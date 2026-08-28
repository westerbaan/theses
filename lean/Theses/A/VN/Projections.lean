/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 2: Von Neumann Algebras — vn.tex, lines 2183–3780.

  §Projections
    parsec 550: projections in a C*-algebra
    Ceiling and Floor       (parsecs 560–580)
    Range and Support       (parsecs 590–620)
    Carrier and Commutant   (parsecs 630–660)
    Central Support and Central Carrier  (parsecs 670–700)

This module contains **no `sorry`**.  See CONVENTIONS.md for the numbering
and naming conventions, and `Theses/A/VN/Basic.lean` for the encoding of the
ultraweak/ultrastrong topologies.

The ceiling `⌈b⌉`, floor `⌊b⌋`, suprema/infima of projections, carriers and
central supports are actual (noncomputable) definitions, obtained by choice
from proved existence-and-uniqueness lemmas.
-/
import Theses.A.VN.Basic

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra ENNReal
open Filter Topology Theses Theses.A.CStar

namespace Theses.A.VN

universe u v w

variable {A : Type u} {B : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
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
/-- **55II** (vn.tex:2204, Definition): an element `p` of a C*-algebra is a
**projection** when `p* p = p`.  The tree renders this by Mathlib's
`IsStarProjection` (idempotent *and* self-adjoint); this is the one place
where the two are shown to agree, so that the rendering is verified rather
than asserted.  (`p* p = p` forces `p* = p`: starring it gives
`p* p = p*`.) -/
theorem isStarProjection_iff_star_mul_self (p : A) :
    IsStarProjection p ↔ star p * p = p := by
  constructor
  · intro hp
    calc star p * p = p * p := by rw [hp.isSelfAdjoint.star_eq]
      _ = p := hp.isIdempotentElem
  · intro h
    have hsa : IsSelfAdjoint p := by
      have h2 := congrArg star h
      rw [star_mul, star_star, h] at h2
      exact h2.symm
    refine ⟨?_, hsa⟩
    calc p * p = star p * p := by rw [hsa.star_eq]
      _ = p := h

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

/-- **56VI**.70–90 (`vna-floor`, vn.tex:2419), the thesis's construction: the
chain `1 ≥ b ≥ b² ≥ b⁴ ≥ ⋯ ≥ 0` has an infimum `q = ⋀ₙ b^{2ⁿ}`
(`infima_in_vna`, **43Ia**), `q` is a projection (**56VI**.90, two
applications of `ad_normal_inf`), and whatever commutes with `b` commutes
with `q` (**56VI**.80, a variation on **44XIII**).

Everything about `⌊b⌋` below — its existence, its being the greatest
projection below `b`, the formula `⌊b⌋ = ⋀ₙ b^{2ⁿ}` and the commutation
clause — is read off this one lemma, which is how vn.tex:2419 proceeds. -/
private theorem exists_floor_inf (b : A) (hb : b ∈ effects A) :
    ∃ q : A, IsStarProjection q ∧ IsGLB (Set.range fun n : ℕ => b ^ (2 ^ n)) q ∧
      ∀ a : A, a * b = b * a → a * q = q * a := by
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
  -- **56VI**.80: whatever commutes with `b` commutes with `b^{2ⁿ}` for every
  -- `n`, hence with `q ≡ ⋀ₙ b^{2ⁿ}` (a variation on **44XIII**)
  have hcomm' : ∀ a : A, a * b = b * a → a * q = q * a := fun a hab =>
    vna_infimum_commutes hne hdir hglbSA a (by
      rintro _ ⟨n, rfl⟩
      exact ((show Commute a b from hab).pow_right (2 ^ n)).eq)
  have hcomm : b * q = q * b := hcomm' b rfl
  -- and therefore `√q` commutes with `b` too (`sqrt`, cstar.tex **23VII**)
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
  exact ⟨q, hqproj, hglb, hcomm'⟩

/-- **56VI** (`vna-floor`, vn.tex:2419, Proposition), well-definedness:
every effect `b` of a von Neumann algebra has a greatest projection `p` with
`p·b = p`.

This is the thesis's own route: `p := ⋀ₙ b^{2ⁿ}` by `exists_floor_inf`
(**56VI**.70–90), and **56VI**.100 for the leastness — a projection `q ≤ b`
satisfies `q ≤ b²` by **55IX** `projection-below-effect`, hence `q ≤ b^{2ⁿ}`
for every `n` by induction, hence `q ≤ ⋀ₙ b^{2ⁿ}`. -/
theorem exists_floor (b : A) (hb : b ∈ effects A) :
    ∃! p : A, IsStarProjection p ∧ p * b = p ∧
      ∀ q : A, IsStarProjection q → q * b = q → q ≤ p := by
  obtain ⟨p, hpproj, hglb, -⟩ := exists_floor_inf b hb
  have hpb : p ≤ b := by simpa using hglb.1 ⟨0, rfl⟩
  have hpmem : p * b = p := ((projection_below_effect b p hb hpproj).out 0 7).mp hpb
  -- **56VI**.100
  have hgreat : ∀ q : A, IsStarProjection q → q * b = q → q ≤ p := by
    intro q hq hqb
    have hq0 : q ≤ b := ((projection_below_effect b q hb hq).out 0 7).mpr hqb
    have hpow : ∀ n : ℕ, q ≤ b ^ 2 ^ n := by
      intro n
      induction n with
      | zero => simpa using hq0
      | succ m ih =>
        have hmul : q * b ^ 2 ^ m = q :=
          ((projection_below_effect (b ^ 2 ^ m) q (pow_mem_effects hb (2 ^ m)) hq).out
            0 7).mp ih
        have hsplit : b ^ 2 ^ (m + 1) = b ^ 2 ^ m * b ^ 2 ^ m := by
          rw [← pow_add]; congr 1; rw [pow_succ]; ring
        refine ((projection_below_effect (b ^ 2 ^ (m + 1)) q
          (pow_mem_effects hb (2 ^ (m + 1))) hq).out 0 7).mpr ?_
        rw [hsplit, ← mul_assoc, hmul, hmul]
    exact hglb.2 (by rintro _ ⟨n, rfl⟩; exact hpow n)
  exact ⟨p, ⟨hpproj, hpmem, hgreat⟩,
    fun q hq => le_antisymm (hgreat q hq.1 hq.2.1) (hq.2.2 _ hpproj hpmem)⟩

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

/-- **56VI**: `⌊b⌋` is the greatest projection below the effect `b`. -/
theorem floor_isGreatest {b : A} (hb : b ∈ effects A) :
    IsGreatest {p : A | IsStarProjection p ∧ p ≤ b} (floor b) := by
  obtain ⟨h1, -, h3⟩ := floor_spec hb
  refine ⟨⟨h1, floor_le hb⟩, ?_⟩
  rintro q ⟨hq, hqb⟩
  exact h3 q hq (((projection_below_effect b q hb hq).out 0 7).mp hqb)

/-- **56XIII**.1 for the floor: `⌊b⌋ = ⌈b^⊥⌉^⊥`.  Now a corollary of
**56VI**, as in the thesis, and no longer a step towards it: `⌈b^⊥⌉^⊥` is a
projection below `b`, hence `≤ ⌊b⌋`, while `b^⊥ ≤ ⌊b⌋^⊥` gives
`⌈b^⊥⌉ ≤ ⌊b⌋^⊥` by leastness of the ceiling (**56I**). -/
theorem floor_eq_one_sub_ceil {b : A} (hb : b ∈ effects A) :
    floor b = 1 - ceil (1 - b) := by
  obtain ⟨⟨hcproj, hbc⟩, hcleast⟩ := vna_ceil (1 - b) (effect_orthosupplement b hb)
  have h1 : (1 : A) - ceil (1 - b) ≤ b := by
    have h := sub_le_sub_left hbc 1
    rwa [sub_sub_cancel] at h
  have h2 : ceil (1 - b) ≤ 1 - floor b :=
    hcleast ⟨(floor_spec hb).1.one_sub, sub_le_sub_left (floor_le hb) 1⟩
  exact le_antisymm (le_sub_comm.mp h2) ((floor_isGreatest hb).2 ⟨hcproj.one_sub, h1⟩)

/-- **56VI** (`vna-floor`, vn.tex:2419, Proposition): `⌊b⌋` is the greatest
projection below the effect `b`, and equals `⋀ₙ b^{2ⁿ}`. -/
theorem vna_floor (b : A) (hb : b ∈ effects A) :
    IsGreatest {p : A | IsStarProjection p ∧ p ≤ b} (floor b) ∧
      IsGLB (Set.range fun n : ℕ => b ^ (2 ^ n)) (floor b) := by
  refine ⟨floor_isGreatest hb, ?_⟩
  obtain ⟨q, hqproj, hglb, -⟩ := exists_floor_inf b hb
  have hqb : q ≤ b := by simpa using hglb.1 ⟨0, rfl⟩
  -- `⌊b⌋ ≤ b^{2ⁿ}` for every `n`, so `⌊b⌋ ≤ q`; and `q ≤ ⌊b⌋` by **56VI**.100
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
commutes with `b` commutes with `⌊b⌋`.  This is **56VI**.80 of the printed
proof, read off `exists_floor_inf` through `⌊b⌋ = ⋀ₙ b^{2ⁿ}`.

(vn.tex:2419 prints "if `a ∈ 𝒜` commutes with `b`, then `b` commutes with
`⌊b⌋`"; the conclusion must be about `a`, and **56VI**.80 proves exactly
that.) -/
theorem vna_floor_comm (b : A) (hb : b ∈ effects A) (a : A)
    (h : a * b = b * a) : a * floor b = floor b * a := by
  obtain ⟨q, -, hglb, hcomm⟩ := exists_floor_inf b hb
  rw [← hglb.unique (vna_floor b hb).2]
  exact hcomm a h

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
`⌈λa⌉ = ⌈a⌉` for **every** `λ ∈ (0,1]` — the exercise's hypothesis is
`λ ∈ [0,1]` with `λ ≠ 0`, so `λ = 1` is included — and, for `λ ∈ (0,1)`, the
projection `⌈λa + λ^⊥b⌉` is the least projection above both `⌈a⌉` and `⌈b⌉`
(the supremum in the poset of projections).

The two clauses carry *separate* scalars: only the second needs `λ ≠ 1`, and
bundling them would silently drop `λ = 1` from the first. -/
theorem ceil_floor_basic_2 (a b : A) (ha : a ∈ effects A)
    (hb : b ∈ effects A) (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1) :
    (∀ m : ℝ, 0 < m → m ≤ 1 → ceil ((m : ℂ) • a) = ceil a) ∧
      IsLeast {p : A | IsStarProjection p ∧ ceil a ≤ p ∧ ceil b ≤ p}
        (ceil ((l : ℂ) • a + ((1 - l : ℝ) : ℂ) • b)) := by
  have hm0 : (0 : ℝ) < 1 - l := by linarith
  have hsmul : ∀ {x : A} {r : ℝ}, x ∈ effects A → 0 ≤ r → r ≤ 1 → r • x ∈ effects A := by
    intro x r hx hr0 hr1
    refine ⟨smul_nonneg hr0 hx.1, ?_⟩
    have h1 : r • x ≤ x := by
      have h := smul_nonneg (by linarith : (0 : ℝ) ≤ 1 - r) hx.1
      rw [sub_smul, one_smul, sub_nonneg] at h
      exact h
    exact h1.trans hx.2
  -- for a projection `p`, `r·x ≤ p ↔ x ≤ p` when `r > 0`
  have hscale : ∀ {x : A} {r : ℝ} {p : A}, x ∈ effects A → 0 < r → r ≤ 1 →
      IsStarProjection p → (r • x ≤ p ↔ x ≤ p) := by
    intro x r p hx hr0 hr1 hp
    rw [le_proj_iff (hsmul hx hr0.le hr1) hp, le_proj_iff hx hp, smul_mul_assoc]
    refine ⟨fun h => ?_, fun h => by rw [h, smul_zero]⟩
    have h2 := congrArg (fun z : A => (r⁻¹ : ℝ) • z) h
    simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt hr0)] using h2
  constructor
  · -- the first clause, for every `m ∈ (0,1]` (`m = 1` included)
    intro m hm0 hm1
    rw [Complex.coe_smul]
    refine (vna_ceil _ (hsmul ha hm0.le hm1)).unique ?_
    have hset : {p : A | IsStarProjection p ∧ (m : ℝ) • a ≤ p}
        = {p : A | IsStarProjection p ∧ a ≤ p} :=
      Set.ext fun p => and_congr_right fun hp => hscale ha hm0 hm1 hp
    rw [hset]
    exact vna_ceil a ha
  -- the convex combination
  rw [Complex.coe_smul, Complex.coe_smul]
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
theorem isLeast_ceil_add {p q : A} (hp : IsStarProjection p)
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

/-- Auxiliary: for a directed set of projections, `projSup` is the supremum
in `A` itself. -/
theorem isLUB_projSup_of_directed (D : Set A) (hD : ∀ p ∈ D, IsStarProjection p)
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) : IsLUB D (projSup D) := by
  classical
  obtain ⟨d₀, hd₀⟩ := hne
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
  have hbdd' : BddAbove D' := ⟨1, fun d hd => (hD _ hd).le_one⟩
  have h3 : D'.Nonempty ∧ DirectedOn (· ≤ ·) D' ∧ BddAbove D' := ⟨hne', hdir', hbdd'⟩
  have hlub : IsLUB D ((dirSup D' h3 : selfAdjoint A) : A) := by
    rw [← hval]; exact isLUB_coe_of_isLUB hne' (isLUB_dirSup D' h3)
  have hproj : IsStarProjection ((dirSup D' h3 : selfAdjoint A) : A) :=
    vna_directed_supremum_projections D _ hD ⟨d₀, hd₀⟩ hdir hlub
  have hEq : projSup D = ((dirSup D' h3 : selfAdjoint A) : A) :=
    projSup_eq hD hproj (fun p hp => hlub.1 hp) fun q _ hub => hlub.2 hub
  rwa [hEq]

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

/-! ### The witness of **56XVII**.3: `1, ½, ⅓, …`

The exercise's hint is a single sequence of scalars, and it settles all four
of its claims: `aₙ = (n+1)⁻¹·1` is a filtered set of effects with infimum
`0` on which `⌈·⌉` is constantly `1`, and `aₙ^⊥ = (1 − (n+1)⁻¹)·1` is a
directed set with supremum `1` on which `⌊·⌋` is constantly `0`.  The same
sequence converges to its limit in the norm, ultraweak *and* ultrastrong
topologies (a direct computation of `ω(aₙ)` and `‖aₙ‖_ω`), which is why the
one witness refutes all three continuities: passing to a coarser topology on
source *and* target changes continuity in both directions, so the norm case
does not by itself give the other two. -/

section CeilSupremumWitness

private theorem npFunctional_smul_real (ω : NPFunctional A) (r : ℝ) (x : A) :
    ω (r • x) = (r : ℂ) * ω x := by
  rw [← Complex.coe_smul]
  exact map_smul ω.toPositiveLinearMap _ _

/-- The generic discontinuity argument, for an arbitrary Hausdorff topology
`t` on `A`: a sequence of effects `aₙ → x` on which `f` is constantly `v ≠
f x` witnesses that `f` is not `t`-continuous on `[0,1]_A`. -/
private theorem not_continuousOn_aux (t : TopologicalSpace A) (ht : @T2Space A t)
    (f : A → A) (a : ℕ → A) (x v : A)
    (hmem : ∀ n, a n ∈ effects A) (hx : x ∈ effects A)
    (ha : @Tendsto ℕ A a atTop (@nhds A t x))
    (hfa : ∀ n, f (a n) = v) (hne : v ≠ f x) :
    ¬ @ContinuousOn A A t t f (effects A) := by
  let _ : TopologicalSpace A := t
  have : T2Space A := ht
  intro h
  have h0 : Tendsto f (𝓝[effects A] x) (𝓝 (f x)) := h x hx
  have hnw : Tendsto a atTop (𝓝[effects A] x) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within a ha
      (Filter.Eventually.of_forall hmem)
  have hcomp : Tendsto (fun n => f (a n)) atTop (𝓝 (f x)) := h0.comp hnw
  have hconst : Tendsto (fun _ : ℕ => v) atTop (𝓝 (f x)) := by
    simpa only [hfa] using hcomp
  exact hne (tendsto_nhds_unique tendsto_const_nhds hconst)

/-- The scalars `1, ½, ⅓, …` of the exercise's hint. -/
private noncomputable def wc (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

private theorem wc_pos (n : ℕ) : 0 < wc n := by unfold wc; positivity

private theorem wc_le_one (n : ℕ) : wc n ≤ 1 := by
  unfold wc; rw [inv_le_one_iff₀]; right; simp

private theorem wc_antitone : Antitone wc := by
  intro m n hmn
  unfold wc
  have hle : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
  exact inv_anti₀ (by positivity) this

private theorem wc_tendsto : Tendsto wc atTop (𝓝 (0 : ℝ)) := by
  unfold wc
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

private theorem ofReal_tendsto {f : ℕ → ℝ} {l : ℝ} (h : Tendsto f atTop (𝓝 l)) :
    Tendsto (fun n => ((f n : ℝ) : ℂ)) atTop (𝓝 ((l : ℝ) : ℂ)) := by
  have := (Complex.continuous_ofReal.tendsto l).comp h
  simpa [Function.comp_def] using this

/-- `r·1` is an effect for `r ∈ [0,1]`. -/
private theorem smul_one_mem_effects {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (r • (1 : A)) ∈ effects A := by
  refine ⟨smul_nonneg hr0 zero_le_one, ?_⟩
  have h : (0 : A) ≤ (1 - r) • (1 : A) := smul_nonneg (by linarith) zero_le_one
  rw [sub_smul, one_smul, sub_nonneg] at h
  exact h

private theorem ceil_one_eq : ceil (1 : A) = 1 :=
  ceil_eq_of_isLeast zero_le_one (IsStarProjection.one A) (mul_one 1)
    fun q _ hq => by rw [← hq, one_mul]

private theorem floor_one_eq : floor (1 : A) = 1 := by
  have h1 : (1 : A) ∈ effects A := ⟨zero_le_one, le_rfl⟩
  exact le_antisymm (floor_le h1)
    ((floor_isGreatest h1).2 ⟨IsStarProjection.one A, le_rfl⟩)

/-- `⌈r·1⌉ = 1` for `r > 0`. -/
private theorem ceil_smul_one {r : ℝ} (hr : 0 < r) : ceil (r • (1 : A)) = 1 := by
  rw [ceil_smul zero_le_one hr, ceil_one_eq]

/-- `⌊r·1⌋ = 0` for `0 ≤ r < 1`: a projection `p ≤ r·1` satisfies
`p = p p p ≤ p (r·1) p = r·p`, so `(1−r)·p ≤ 0`, so `p = 0`. -/
private theorem floor_smul_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    floor (r • (1 : A)) = 0 := by
  obtain ⟨⟨hp, hple⟩, -⟩ := floor_isGreatest (smul_one_mem_effects (A := A) hr0 hr1.le)
  set p : A := floor (r • (1 : A)) with hpdef
  have hcj := IsSelfAdjoint.conjugate_le_conjugate hple hp.isSelfAdjoint
  have h1 : p * p * p = p := by
    rw [hp.isIdempotentElem.eq, hp.isIdempotentElem.eq]
  have h2 : p * (r • (1 : A)) * p = r • p := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, hp.isIdempotentElem.eq]
  rw [h1, h2] at hcj
  have h5 : (1 - r) • p ≤ 0 := by
    rw [sub_smul, one_smul]; exact sub_nonpos.mpr hcj
  have h4 : (0 : A) ≤ (1 - r) • p := smul_nonneg (by linarith) hp.nonneg
  have h7 : (1 - r) • p = 0 := le_antisymm h5 h4
  have h8 := congrArg (fun z : A => ((1 - r)⁻¹ : ℝ) • z) h7
  simpa [smul_smul, inv_mul_cancel₀ (by linarith : (1 : ℝ) - r ≠ 0)] using h8

/-- `aₙ = (n+1)⁻¹·1`, the hint's sequence. -/
private noncomputable def wu (n : ℕ) : A := wc n • (1 : A)

/-- `aₙ^⊥ = (1 − (n+1)⁻¹)·1`. -/
private noncomputable def wv (n : ℕ) : A := (1 - wc n) • (1 : A)

private theorem wu_mem (n : ℕ) : wu (A := A) n ∈ effects A :=
  smul_one_mem_effects (wc_pos n).le (wc_le_one n)

private theorem wv_mem (n : ℕ) : wv (A := A) n ∈ effects A :=
  smul_one_mem_effects (by linarith [wc_le_one n]) (by linarith [(wc_pos n).le])

private theorem wu_ceil (n : ℕ) : ceil (wu (A := A) n) = 1 := ceil_smul_one (wc_pos n)

private theorem wv_floor (n : ℕ) : floor (wv (A := A) n) = 0 :=
  floor_smul_one (by linarith [wc_le_one n]) (by linarith [wc_pos n])

private theorem wu_norm_tendsto : Tendsto (wu (A := A)) atTop (𝓝 (0 : A)) := by
  have h := wc_tendsto.smul_const (1 : A)
  rw [zero_smul] at h
  exact h

private theorem wv_norm_tendsto : Tendsto (wv (A := A)) atTop (𝓝 (1 : A)) := by
  have h : Tendsto (fun n => 1 - wc n) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub wc_tendsto
  have h2 := h.smul_const (1 : A)
  rw [one_smul] at h2
  exact h2

private theorem wu_uw : @Tendsto ℕ A (wu (A := A)) atTop (@nhds A (ultraweak A) 0) := by
  have h : UWTendsto (wu (A := A)) atTop 0 := by
    rw [uwTendsto_iff]
    intro ω
    have hval : ∀ n, (ω (wu (A := A) n) : ℂ) = ((wc n : ℝ) : ℂ) * ω 1 := by
      intro n
      show (ω ((wc n : ℝ) • (1 : A)) : ℂ) = _
      rw [npFunctional_smul_real]
    have hc : Tendsto (fun n => ((wc n : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
      simpa using ofReal_tendsto wc_tendsto
    simpa [hval] using hc.mul_const (ω 1 : ℂ)
  exact h

private theorem wv_uw : @Tendsto ℕ A (wv (A := A)) atTop (@nhds A (ultraweak A) 1) := by
  have h : UWTendsto (wv (A := A)) atTop 1 := by
    rw [uwTendsto_iff]
    intro ω
    have hval : ∀ n, (ω (wv (A := A) n) : ℂ) = ((1 - wc n : ℝ) : ℂ) * ω 1 := by
      intro n
      show (ω ((1 - wc n : ℝ) • (1 : A)) : ℂ) = _
      rw [npFunctional_smul_real]
    have hc : Tendsto (fun n => ((1 - wc n : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
      have h1 : Tendsto (fun n => 1 - wc n) atTop (𝓝 (1 : ℝ)) := by
        simpa using tendsto_const_nhds.sub wc_tendsto
      simpa using ofReal_tendsto h1
    simpa [hval] using hc.mul_const (ω 1 : ℂ)
  exact h

private theorem wu_us : @Tendsto ℕ A (wu (A := A)) atTop (@nhds A (ultrastrong A) 0) := by
  have h : USTendsto (wu (A := A)) atTop 0 := by
    rw [usTendsto_iff]
    intro ω
    have hval : ∀ n, omegaNorm A ω (wu (A := A) n - 0) = wc n * Real.sqrt (ω 1).re := by
      intro n
      rw [sub_zero]
      show omegaNorm A ω ((wc n : ℝ) • (1 : A)) = _
      rw [← Complex.coe_smul, omegaNorm_smul, omegaNorm_one]
      simp [abs_of_nonneg (wc_pos n).le]
    have h1 := wc_tendsto.mul_const (Real.sqrt (ω 1).re)
    rw [zero_mul] at h1
    simp only [hval]
    exact h1
  exact h

private theorem wv_us : @Tendsto ℕ A (wv (A := A)) atTop (@nhds A (ultrastrong A) 1) := by
  have h : USTendsto (wv (A := A)) atTop 1 := by
    rw [usTendsto_iff]
    intro ω
    have hval : ∀ n, omegaNorm A ω (wv (A := A) n - 1) = wc n * Real.sqrt (ω 1).re := by
      intro n
      have he : wv (A := A) n - 1 = (-(wc n) : ℝ) • (1 : A) := by
        show (1 - wc n : ℝ) • (1 : A) - 1 = _
        rw [sub_smul, one_smul, neg_smul]
        abel
      rw [he, ← Complex.coe_smul, omegaNorm_smul, omegaNorm_one]
      simp [abs_of_nonneg (wc_pos n).le]
    have h1 := wc_tendsto.mul_const (Real.sqrt (ω 1).re)
    rw [zero_mul] at h1
    simp only [hval]
    exact h1
  exact h

end CeilSupremumWitness

/-- **56XVII** (`ceil-supremum`, vn.tex:2554, Exercise), part 3, in full:

> Show that `⌈·⌉` does not preserve filtered infima, and `⌊·⌋` does not
> preserve directed suprema.  (Hint: `1, ½, ⅓, …`.)  Conclude that `⌈·⌉` and
> `⌊·⌋` are neither ultraweakly, ultrastrongly nor norm continuous as maps
> from `[0,1]_𝒜` to `[0,1]_𝒜`.

All six claims, on the hint's witness: `D = {(n+1)⁻¹·1}` is filtered with
`⋀D = 0`, yet `⋂_{d∈D}⌈d⌉ = 1 ≠ 0 = ⌈⋀D⌉`; `D^⊥ = {(1−(n+1)⁻¹)·1}` is
directed with `⋁D^⊥ = 1`, yet `⋃_{d∈D^⊥}⌊d⌋ = 0 ≠ 1 = ⌊⋁D^⊥⌋`; and the same
sequences converge in all three topologies, so neither map is continuous on
`[0,1]_A` for any of them.  `[Nontrivial A]` is what the thesis leaves
implicit (in `A = 0` every claim fails). -/
theorem ceil_supremum_3 [Nontrivial A] :
    (∃ (D : Set A) (s : A), (∀ d ∈ D, d ∈ effects A) ∧ D.Nonempty ∧
        DirectedOn (· ≥ ·) D ∧ IsGLB D s ∧ ceil s ≠ projInf (ceil '' D)) ∧
      (∃ (D : Set A) (s : A), (∀ d ∈ D, d ∈ effects A) ∧ D.Nonempty ∧
        DirectedOn (· ≤ ·) D ∧ IsLUB D s ∧ floor s ≠ projSup (floor '' D)) ∧
      ¬ContinuousOn (fun a : A => ceil a) (effects A) ∧
      ¬ContinuousOn (fun a : A => floor a) (effects A) ∧
      ¬@ContinuousOn A A (ultraweak A) (ultraweak A) (fun a : A => ceil a) (effects A) ∧
      ¬@ContinuousOn A A (ultraweak A) (ultraweak A) (fun a : A => floor a) (effects A) ∧
      ¬@ContinuousOn A A (ultrastrong A) (ultrastrong A)
        (fun a : A => ceil a) (effects A) ∧
      ¬@ContinuousOn A A (ultrastrong A) (ultrastrong A)
        (fun a : A => floor a) (effects A) := by
  have hsm : ∀ {r s : ℝ}, r ≤ s → (r • (1 : A)) ≤ s • (1 : A) := by
    intro r s h
    have h0 : (0 : A) ≤ (s - r) • (1 : A) := smul_nonneg (by linarith) zero_le_one
    rw [sub_smul, sub_nonneg] at h0
    exact h0
  have h0 : (0 : A) ∈ effects A := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : A) ∈ effects A := ⟨zero_le_one, le_rfl⟩
  have hc0 : (1 : A) ≠ ceil (0 : A) := by rw [ceil_zero]; exact one_ne_zero
  have hf1 : (0 : A) ≠ floor (1 : A) := by rw [floor_one_eq]; exact zero_ne_one
  refine ⟨⟨Set.range (wu (A := A)), 0, ?_, ⟨wu 0, ⟨0, rfl⟩⟩, ?_, ?_, ?_⟩,
    ⟨Set.range (wv (A := A)), 1, ?_, ⟨wv 0, ⟨0, rfl⟩⟩, ?_, ?_, ?_⟩,
    not_continuousOn_aux _ inferInstance _ wu 0 1 wu_mem h0 wu_norm_tendsto wu_ceil hc0,
    not_continuousOn_aux _ inferInstance _ wv 1 0 wv_mem h1 wv_norm_tendsto wv_floor hf1,
    not_continuousOn_aux _ (vn_positive_basic_1 (A := A)).1 _ wu 0 1 wu_mem h0 wu_uw
      wu_ceil hc0,
    not_continuousOn_aux _ (vn_positive_basic_1 (A := A)).1 _ wv 1 0 wv_mem h1 wv_uw
      wv_floor hf1,
    not_continuousOn_aux _ (vn_positive_basic_1 (A := A)).2 _ wu 0 1 wu_mem h0 wu_us
      wu_ceil hc0,
    not_continuousOn_aux _ (vn_positive_basic_1 (A := A)).2 _ wv 1 0 wv_mem h1 wv_us
      wv_floor hf1⟩
  · rintro _ ⟨n, rfl⟩; exact wu_mem n
  · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ⟨wu (max m n), ⟨max m n, rfl⟩,
      hsm (wc_antitone (le_max_left m n)), hsm (wc_antitone (le_max_right m n))⟩
  · constructor
    · rintro _ ⟨n, rfl⟩; exact (wu_mem (A := A) n).1
    · intro b hb
      exact ge_of_tendsto wu_norm_tendsto
        (Filter.Eventually.of_forall fun n => hb ⟨n, rfl⟩)
  · have himg : ∀ p ∈ ceil '' Set.range (wu (A := A)), p = 1 := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩; exact wu_ceil n
    have hproj : ∀ p ∈ ceil '' Set.range (wu (A := A)), IsStarProjection p := by
      intro p hp; rw [himg p hp]; exact IsStarProjection.one A
    have hpi : projInf (ceil '' Set.range (wu (A := A))) = 1 :=
      projInf_eq hproj (IsStarProjection.one A)
        (fun p hp => by rw [himg p hp]) (fun q hq _ => hq.le_one)
    rw [hpi, ceil_zero]
    exact zero_ne_one
  · rintro _ ⟨n, rfl⟩; exact wv_mem n
  · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    refine ⟨wv (max m n), ⟨max m n, rfl⟩, hsm ?_, hsm ?_⟩
    · have := wc_antitone (le_max_left m n); linarith
    · have := wc_antitone (le_max_right m n); linarith
  · constructor
    · rintro _ ⟨n, rfl⟩; exact (wv_mem (A := A) n).2
    · intro b hb
      exact le_of_tendsto wv_norm_tendsto
        (Filter.Eventually.of_forall fun n => hb ⟨n, rfl⟩)
  · have himg : ∀ p ∈ floor '' Set.range (wv (A := A)), p = 0 := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩; exact wv_floor n
    have hproj : ∀ p ∈ floor '' Set.range (wv (A := A)), IsStarProjection p := by
      intro p hp; rw [himg p hp]; exact IsStarProjection.zero A
    have hps : projSup (floor '' Set.range (wv (A := A))) = 0 :=
      projSup_eq hproj (IsStarProjection.zero A)
        (fun p hp => by rw [himg p hp]) (fun q hq _ => hq.nonneg)
    rw [hps, floor_one_eq]
    exact one_ne_zero

/-- **56XVIII** (`sum-of-orthogonal-projections`, vn.tex:2577, Exercise):
for a family `(pᵢ)_{i∈I}` of pairwise orthogonal projections, the net of
partial sums `∑_{i∈F} pᵢ` (over finite `F ⊆ I`) converges ultrastrongly to
`⋃ᵢ pᵢ`. -/
theorem sum_of_orthogonal_projections {ι : Type*} (p : ι → A)
    (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise fun i j => p i * p j = 0) :
    USTendsto (fun F : Finset ι => ∑ i ∈ F, p i) atTop
      (projSup (Set.range p)) := by
  classical
  have hmulL : ∀ {e q : A}, IsStarProjection e → IsStarProjection q → e ≤ q →
      q * e = e := fun he hq h =>
    ((projection_below_effect _ _ ⟨hq.nonneg, hq.le_one⟩ he).out 0 6).mp h
  have hmulR : ∀ {e q : A}, IsStarProjection e → IsStarProjection q → e ≤ q →
      e * q = e := fun he hq h =>
    ((projection_below_effect _ _ ⟨hq.nonneg, hq.le_one⟩ he).out 0 7).mp h
  set s : Finset ι → A := fun F => ∑ i ∈ F, p i with hsdef
  have hsproj : ∀ F, IsStarProjection (s F) := fun F =>
    isStarProjection_sum F p hp fun i _ j _ hij => horth hij
  have hprange : ∀ r ∈ Set.range p, IsStarProjection r := by
    rintro _ ⟨i, rfl⟩; exact hp i
  have hsrange : ∀ r ∈ Set.range s, IsStarProjection r := by
    rintro _ ⟨F, rfl⟩; exact hsproj F
  set q : A := projSup (Set.range p) with hqdef
  obtain ⟨hqproj, hqub, hqleast⟩ := projSup_spec hprange
  -- every partial sum is below `q`
  have hsq : ∀ F : Finset ι, s F ≤ q := by
    intro F
    have hqs : q * s F = s F := by
      rw [hsdef]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hmulL (hp i) hqproj (hqub _ ⟨i, rfl⟩)
    have hsq' : s F * q = s F := by
      rw [hsdef]
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => hmulR (hp i) hqproj (hqub _ ⟨i, rfl⟩)
    have hdiff : IsStarProjection (q - s F) := by
      constructor
      · change (q - s F) * (q - s F) = q - s F
        rw [sub_mul, mul_sub, mul_sub, hqproj.isIdempotentElem.eq, hqs, hsq',
          (hsproj F).isIdempotentElem.eq]
        abel
      · exact (hqproj.isSelfAdjoint.sub (hsproj F).isSelfAdjoint)
    exact sub_nonneg.mp hdiff.nonneg
  -- the two suprema agree
  have hqeq : projSup (Set.range s) = q := by
    refine projSup_eq hsrange hqproj (fun r hr => by obtain ⟨F, rfl⟩ := hr; exact hsq F) ?_
    intro r hr hub
    refine hqleast r hr ?_
    rintro _ ⟨i, rfl⟩
    have : p i = s {i} := by simp [hsdef]
    rw [this]
    exact hub _ ⟨{i}, rfl⟩
  -- directedness
  have hdir : DirectedOn (· ≤ ·) (Set.range s) := by
    rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
    refine ⟨s (F ∪ G), ⟨F ∪ G, rfl⟩, ?_, ?_⟩
    · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        fun i _ _ => (hp i).nonneg
    · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
        fun i _ _ => (hp i).nonneg
  have hlub : IsLUB (Set.range s) q := by
    have := isLUB_projSup_of_directed (Set.range s) hsrange ⟨s ∅, ⟨∅, rfl⟩⟩ hdir
    rwa [hqeq] at this
  -- ultrastrong convergence
  rw [usTendsto_iff]
  intro ω
  have hsa : ∀ F : Finset ι, IsSelfAdjoint (s F) := fun F => (hsproj F).isSelfAdjoint
  set D : Set (selfAdjoint A) := {d : selfAdjoint A | (d : A) ∈ Set.range s} with hD
  have hDval : Subtype.val '' D = Set.range s := by
    ext x
    exact ⟨by rintro ⟨d, hd, rfl⟩; exact hd,
      fun hx => ⟨⟨x, by obtain ⟨F, rfl⟩ := hx; exact hsa F⟩, hx, rfl⟩⟩
  have hDne : D.Nonempty := ⟨⟨s ∅, hsa ∅⟩, ⟨∅, rfl⟩⟩
  have hDdir : DirectedOn (· ≤ ·) D := by
    intro x hx y hy
    obtain ⟨c, hc, hxc, hyc⟩ := hdir _ hx _ hy
    exact ⟨⟨c, by obtain ⟨F, rfl⟩ := hc; exact hsa F⟩, hc, hxc, hyc⟩
  have hDlub : IsLUB D (⟨q, hqproj.isSelfAdjoint⟩ : selfAdjoint A) := by
    refine isLUB_sa_of_isLUB ?_
    rw [hDval]; exact hlub
  have hωlub := ω.preservesDirSups' D _ hDne hDdir hDlub
  have hreal : ∀ w ∈ ((fun d : selfAdjoint A => (ω (d : A) : ℂ)) '' D), w.im = 0 := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨F, hF⟩ := hd
    have h0 : (0 : ℂ) ≤ ω (d : A) := by
      rw [← hF] at *
      exact npFunctional_nonneg ω (hsproj F).nonneg
    exact ((Complex.le_def.mp h0).2).symm
  have hrelub := isLUB_re_of_isLUB hreal hωlub
  have hrange : Complex.re '' ((fun d : selfAdjoint A => (ω (d : A) : ℂ)) '' D)
      = Set.range (fun F : Finset ι => (ω (s F) : ℂ).re) := by
    ext r
    constructor
    · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
      obtain ⟨F, hF⟩ := hd
      refine ⟨F, ?_⟩
      change (ω (s F) : ℂ).re = ((ω (d : A) : ℂ)).re
      rw [hF]
    · rintro ⟨F, rfl⟩
      exact ⟨ω (s F), ⟨⟨s F, hsa F⟩, ⟨F, rfl⟩, rfl⟩, rfl⟩
  rw [hrange] at hrelub
  have hmono : Monotone (fun F : Finset ι => (ω (s F) : ℂ).re) := by
    intro F G hFG
    have h := npFunctional_mono ω (Finset.sum_le_sum_of_subset_of_nonneg hFG
      fun i _ _ => (hp i).nonneg)
    exact (Complex.le_def.mp h).1
  have htend := tendsto_atTop_isLUB hmono hrelub
  have hfun : ∀ F : Finset ι, omegaNorm A ω (s F - q)
      = Real.sqrt ((ω q : ℂ).re - (ω (s F) : ℂ).re) := by
    intro F
    have hdiff : IsStarProjection (q - s F) := by
      have hqs : q * s F = s F := hmulL (hsproj F) hqproj (hsq F)
      have hsq' : s F * q = s F := hmulR (hsproj F) hqproj (hsq F)
      constructor
      · change (q - s F) * (q - s F) = q - s F
        rw [sub_mul, mul_sub, mul_sub, hqproj.isIdempotentElem.eq, hqs, hsq',
          (hsproj F).isIdempotentElem.eq]
        abel
      · exact (hqproj.isSelfAdjoint.sub (hsproj F).isSelfAdjoint)
    have hstar : star (s F - q) * (s F - q) = q - s F := by
      have : star (s F - q) = -(q - s F) := by
        rw [star_sub, (hsproj F).isSelfAdjoint.star_eq, hqproj.isSelfAdjoint.star_eq]
        abel
      rw [this, show s F - q = -(q - s F) by abel, neg_mul_neg]
      exact hdiff.isIdempotentElem.eq
    rw [omegaNorm, hstar, npFunctional_sub]
    simp
  simp only [hfun]
  have htend' : Tendsto (fun F : Finset ι => (ω (s F) : ℂ).re) atTop
      (𝓝 ((ω q : ℂ).re)) := htend
  have hlim : Tendsto (fun F : Finset ι => (ω q : ℂ).re - (ω (s F) : ℂ).re)
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds
      (x := (ω q : ℂ).re) (f := (atTop : Filter (Finset ι)))).sub htend'
    simpa using h
  have hc := (Real.continuous_sqrt.tendsto 0).comp hlim
  simpa [Function.comp_def] using hc

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
    ceil (p * q * p) = projInf {p, projSup {1 - p, q}} := by
  have hpe : p ∈ effects A := (projection_basic_2 p hp).2
  have hqe : q ∈ effects A := (projection_basic_2 q hq).2
  have hsqrtp : CFC.sqrt p = p :=
    (CFC.sqrt_eq_iff p p hp.nonneg hp.nonneg).mpr hp.isIdempotentElem.eq
  have hfloor_proj : ∀ t : A, IsStarProjection t → floor t = t := fun t ht =>
    le_antisymm (floor_le (projection_basic_2 t ht).2)
      ((floor_isGreatest (projection_basic_2 t ht).2).2 ⟨ht, le_rfl⟩)
  -- `p ∩ b = ⌊p b p⌋` for an effect `b`, since `√p = p` and `⌊p⌋ = p`
  have hpbp : ∀ b : A, b ∈ effects A → floor (p * b * p) = projInf {p, floor b} := by
    intro b hb
    have h := floor_sequential_product p b hpe hb
    rwa [hsqrtp, hfloor_proj p hp] at h
  -- for a projection `r ≤ p`: `p ∩ r^⊥ = p - r`
  have hinf : ∀ r : A, IsStarProjection r → r ≤ p → projInf {p, 1 - r} = p - r := by
    intro r hr hrp
    have hre : r ∈ effects A := (projection_basic_2 r hr).2
    have hpr : p * r = r := ((projection_below_effect p r hpe hr).out 0 6).mp hrp
    have hrp' : r * p = r := ((projection_below_effect p r hpe hr).out 0 7).mp hrp
    have hcalc : p * (1 - r) * p = p - r := by
      rw [mul_sub, mul_one, sub_mul, hp.isIdempotentElem.eq, hpr, hrp']
    have h := hpbp (1 - r) (effect_orthosupplement r hre)
    rw [hcalc, hfloor_proj (p - r) (projection_below_projection _ _ hr hp hrp),
      hfloor_proj (1 - r) hr.one_sub] at h
    exact h.symm
  -- `m = p ∩ q^⊥`
  have hPq : ∀ x ∈ ({p, 1 - q} : Set A), IsStarProjection x := by
    rintro x hx
    rcases hx with rfl | rfl
    · exact hp
    · exact hq.one_sub
  obtain ⟨hmproj, hmlb, hmgreat⟩ := projInf_spec hPq
  set m : A := projInf {p, 1 - q} with hm
  have hmp : m ≤ p := hmlb p (Set.mem_insert _ _)
  have hmq : m ≤ 1 - q := hmlb _ (Set.mem_insert_of_mem _ rfl)
  -- De Morgan: `p^⊥ ∪ q = (p ∩ q^⊥)^⊥`
  have hsup : projSup {1 - p, q} = 1 - m := by
    refine projSup_eq ?_ hmproj.one_sub ?_ ?_
    · rintro x hx
      rcases hx with rfl | rfl
      · exact hp.one_sub
      · exact hq
    · rintro x hx
      rcases hx with rfl | rfl
      · exact sub_le_sub_left hmp 1
      · exact le_sub_comm.mp hmq
    · intro u hu hub
      have h1 : (1 : A) - u ≤ p := sub_le_comm.mp (hub _ (Set.mem_insert _ _))
      have h2 : (1 : A) - u ≤ 1 - q := sub_le_sub_left (hub _ (Set.mem_insert_of_mem _ rfl)) 1
      have := hmgreat (1 - u) hu.one_sub (by
        rintro x hx
        rcases hx with rfl | rfl
        · exact h1
        · exact h2)
      exact sub_le_comm.mp this
  rw [hsup, hinf m hmproj hmp]
  -- `p - ⌈pqp⌉ = ⌊p - pqp⌋ = ⌊p q^⊥ p⌋ = p ∩ q^⊥ = m`
  have hpqp_nonneg : (0 : A) ≤ p * q * p := by
    have := star_left_conjugate_nonneg hq.nonneg p
    rwa [hp.isSelfAdjoint.star_eq] at this
  have hpqp_le : p * q * p ≤ p := by
    have := star_left_conjugate_le_conjugate hq.le_one p
    rwa [hp.isSelfAdjoint.star_eq, mul_one, hp.isIdempotentElem.eq] at this
  have hpqpe : p * q * p ∈ effects A := ⟨hpqp_nonneg, hpqp_le.trans hp.le_one⟩
  have hdiff := floor_difference p (p * q * p) hp hpqpe hpqp_le
  have hcalc2 : p - p * q * p = p * (1 - q) * p := by
    rw [mul_sub, mul_one, sub_mul, hp.isIdempotentElem.eq]
  rw [hcalc2, hpbp (1 - q) (effect_orthosupplement q hqe),
    hfloor_proj (1 - q) hq.one_sub, ← hm] at hdiff
  rw [← hdiff]
  abel

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
      {x : H | suppProj T x = x} = ((LinearMap.ker (T : H →ₗ[ℂ] H))ᗮ : Set H) := by
  classical
  constructor
  · -- `⌊T⌉` is the projection onto `closure (range T)`
    set M : Submodule ℂ H := (LinearMap.range (T : H →ₗ[ℂ] H)).topologicalClosure with hMdef
    have hOP : M.HasOrthogonalProjection := inferInstance
    set p : H →L[ℂ] H := M.starProjection with hpdef
    have hproj : IsStarProjection p := isStarProjection_starProjection
    have hpT : ∀ x : H, p (T x) = T x := fun x =>
      Submodule.starProjection_eq_self_iff.mpr (Submodule.le_topologicalClosure _ ⟨x, rfl⟩)
    have hmem : IsStarProjection p ∧ p * T = T := by
      refine ⟨hproj, ?_⟩
      ext x
      exact hpT x
    have hleast : ∀ q : H →L[ℂ] H, IsStarProjection q ∧ q * T = T → p ≤ q := by
      rintro q ⟨hq, hqT⟩
      set e : H →L[ℂ] H := 1 - q with hedef
      have heproj : IsStarProjection e := hq.one_sub
      have hE : ∀ x : H, e (T x) = 0 := by
        intro x
        have : q (T x) = T x := congrArg (fun S : H →L[ℂ] H => S x) hqT
        simp [hedef, this]
      have hker : M ≤ LinearMap.ker (e : H →ₗ[ℂ] H) := by
        rw [hMdef]
        refine Submodule.topologicalClosure_minimal _ ?_ e.isClosed_ker
        rintro _ ⟨x, rfl⟩
        exact hE x
      have hpe : p * e = 0 := by
        have h1 : e * p = 0 := by
          ext y
          show e (p y) = 0
          exact hker (M.starProjection_apply_mem y)
        have h2 := congrArg star h1
        rwa [star_mul, heproj.isSelfAdjoint.star_eq, hproj.isSelfAdjoint.star_eq,
          star_zero] at h2
      exact (proj_le_iff (projection_basic_2 q hq).2 hproj).mpr hpe
    have hrp : rangeProj T = p := ((ceill_basic_2 T).unique ⟨hmem, hleast⟩)
    have hset : ((LinearMap.range (T : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H)
        = Set.range T := by
      ext z; simp [LinearMap.mem_range]
    rw [hrp]
    ext y
    simp only [Set.mem_ofPred_eq, hpdef, Submodule.starProjection_eq_self_iff]
    rw [hMdef, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, hset]
  · -- `⌈T⌋` is the projection onto `(ker T)^⊥`
    set K : Submodule ℂ H := (LinearMap.ker (T : H →ₗ[ℂ] H))ᗮ with hKdef
    have hOP : K.HasOrthogonalProjection := inferInstance
    set p : H →L[ℂ] H := K.starProjection with hpdef
    have hproj : IsStarProjection p := isStarProjection_starProjection
    have hKperp : Kᗮ = LinearMap.ker (T : H →ₗ[ℂ] H) := by
      rw [hKdef]
      exact Submodule.orthogonal_orthogonal _
    have hmem : IsStarProjection p ∧ T * p = T := by
      refine ⟨hproj, ?_⟩
      ext x
      show T (p x) = T x
      have hsub : x - p x ∈ Kᗮ := K.sub_starProjection_mem_orthogonal x
      rw [hKperp] at hsub
      have h0 : T (x - p x) = 0 := by simpa using LinearMap.mem_ker.mp hsub
      rw [map_sub, sub_eq_zero] at h0
      exact h0.symm
    have hleast : ∀ q : H →L[ℂ] H, IsStarProjection q ∧ T * q = T → p ≤ q := by
      rintro q ⟨hq, hqT⟩
      have hpe : p * (1 - q) = 0 := by
        ext y
        show p (y - q y) = 0
        refine (Submodule.starProjection_apply_eq_zero_iff K).mpr ?_
        rw [hKperp]
        refine LinearMap.mem_ker.mpr ?_
        have hyq : T (q y) = T y := congrArg (fun S : H →L[ℂ] H => S y) hqT
        simp [map_sub, hyq]
      exact (proj_le_iff (projection_basic_2 q hq).2 hproj).mpr hpe
    have hsp : suppProj T = p := ((ceill_basic_1 T).unique ⟨hmem, hleast⟩)
    rw [hsp]
    ext y
    simp only [Set.mem_ofPred_eq, hpdef, Submodule.starProjection_eq_self_iff]
    rfl

/-- **59VII** (`hilb-ceil`, vn.tex:2796, Exercise), part 3: for an effect
`T` on a Hilbert space, `⌊T⌋` is the projection onto
`{x | Tx = x}`. -/
theorem hilb_ceil_2 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : T ∈ effects (H →L[ℂ] H)) :
    {x : H | floor T x = x} = {x : H | T x = x} := by
  classical
  have hTsa : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg hT.1
  set V : Submodule ℂ H := LinearMap.ker (((T - 1 : H →L[ℂ] H) : H →ₗ[ℂ] H)) with hVdef
  have hVmem : ∀ x : H, x ∈ V ↔ T x = x := by
    intro x
    rw [hVdef]
    simp [LinearMap.mem_ker, sub_eq_zero]
  have : CompleteSpace V := (ContinuousLinearMap.isClosed_ker (T - 1)).completeSpace_coe
  have hOP : V.HasOrthogonalProjection := inferInstance
  set p : H →L[ℂ] H := V.starProjection with hpdef
  have hproj : IsStarProjection p := isStarProjection_starProjection
  have hTp : T * p = p := by
    ext x
    show T (p x) = p x
    exact (hVmem _).mp (V.starProjection_apply_mem x)
  have hpT : p * T = p := by
    have h2 := congrArg star hTp
    rwa [star_mul, hTsa.star_eq, hproj.isSelfAdjoint.star_eq] at h2
  have hgreat : ∀ q : H →L[ℂ] H, IsStarProjection q → q * T = q → q ≤ p := by
    intro q hq hqT
    have hTq : T * q = q := by
      have h2 := congrArg star hqT
      rwa [star_mul, hTsa.star_eq, hq.isSelfAdjoint.star_eq] at h2
    have hone : (1 - p) * q = 0 := by
      ext y
      show q y - p (q y) = 0
      have : T (q y) = q y := congrArg (fun S : H →L[ℂ] H => S y) hTq
      rw [Submodule.starProjection_eq_self_iff.mpr ((hVmem _).mpr this), sub_self]
    have hqe : q * (1 - p) = 0 := by
      have h2 := congrArg star hone
      rwa [star_mul, hproj.one_sub.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
        star_zero] at h2
    exact (proj_le_iff (projection_basic_2 p hproj).2 hq).mpr hqe
  obtain ⟨hf1, hf2, hf3⟩ := floor_spec hT
  have hfl : floor T = p := le_antisymm (hgreat _ hf1 hf2) (hf3 p hproj hpT)
  rw [hfl]
  ext y
  simp only [Set.mem_ofPred_eq, hpdef, Submodule.starProjection_eq_self_iff]
  exact hVmem y

/-! ## Parsec 600 -/

section Functionals

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B]

/-- Kadison's inequality (`omega-norm-basic`, cstar.tex **30IV**.1) for an
np-functional: `|ω(a* b)|² ≤ ω(a* a)·ω(b* b)`. -/
private theorem npFunctional_cauchy_schwarz (ω : NPFunctional A) (a b : A) :
    ((‖ω (star a * b)‖ : ℂ)) ^ 2 ≤ ω (star a * a) * ω (star b * b) :=
  omega_norm_basic_1 ω.toPositiveLinearMap.toLinearMap
    (fun _ hx => npFunctional_nonneg ω hx) a b

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
    -- The exercise's hint (vn.tex:2929): if `cb = 0` then
    -- `⌈b* c* c b⌉ ≡ ⌈b* ⌈c* c⌉ b⌉ = 0` by **60VII** `ceil-fundamental`.
    -- The left-hand side is `⌈(cb)*(cb)⌉ = ⌈0⌉ = 0` and the right-hand side
    -- is `⌈(⌈c⌋b)*(⌈c⌋b)⌉`, so `⌈c⌋b = 0`; then `(bb*)⌈c⌋ = 0`, so
    -- `⌊b⌉⌈c⌋ = 0`.
    have hL : star b * (star c * c) * b = 0 := by
      have e : star b * (star c * c) * b = star (c * b) * (c * b) := by
        rw [star_mul]; noncomm_ring
      rw [e, h, mul_zero]
    have hR : star b * suppProj c * b = star (suppProj c * b) * (suppProj c * b) := by
      rw [star_mul, hsc.isSelfAdjoint.star_eq]
      calc star b * suppProj c * b
          = star b * (suppProj c * suppProj c) * b := by rw [hsc.isIdempotentElem.eq]
        _ = star b * suppProj c * (suppProj c * b) := by noncomm_ring
    have hfund : ceil (star b * (star c * c) * b) = ceil (star b * suppProj c * b) :=
      ceil_fundamental_1 b (star c * c) (star_mul_self_nonneg c)
    have h2 : suppProj c * b = 0 := by
      have h0 : ceil (star (suppProj c * b) * (suppProj c * b)) = 0 := by
        rw [← hR, ← hfund, hL, ceil_zero]
      exact (CStarRing.star_mul_self_eq_zero_iff _).mp
        ((ceil_basic_3 _ (star_mul_self_nonneg _)).mpr h0)
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

/-- **60IX**.2 specialised to conjugation, the form in which it is used
repeatedly: `⌈b*(⋃P)b⌉ = ⋃_{p∈P} ⌈b* p b⌉` for a set `P` of projections. -/
theorem ceil_conj_projSup (b : A) (P : Set A) (hP : ∀ p ∈ P, IsStarProjection p) :
    ceil (star b * projSup P * b)
      = projSup ((fun p => ceil (star b * p * b)) '' P) :=
  ncp_union_2 (conjPMap b) (conjPMap_preservesDirSups b) P hP

/-! ## Parsec 610

**61I** (vn.tex:2967): the equation `⌈f(⌈a⌋)⌉ = ⌈f(a)⌋` fails for np-maps —
nothing to formalize. -/

/-- **61II** (`ncp-ceill`, vn.tex:2983, Proposition): for an *ncp*-map
`f : A → B` and any `a`: `⌈f(a)⌋ ≤ ⌈f(⌈a⌋)⌉` and `⌊f(a)⌉ ≤ ⌈f(⌊a⌉)⌉`.

(Erratum `parsec-610.20` — the reversal of these two inequalities — **has
been incorporated into vn.tex**: 61II now displays them in the direction
stated here, which is also the direction its proof, via
`f(a)* f(a) ≤ ‖f(1)‖² f(a* a)`, establishes.  The displayed-in-reverse form
was false, e.g. for the trace on `M₂` at `a = e₁₂`.) -/
theorem ncp_ceill (f : NCPMap A B) (a : A) :
    suppProj (f a) ≤ ceil (f (suppProj a)) ∧
      rangeProj (f a) ≤ ceil (f (rangeProj a)) := by
  -- The thesis's chain, with `‖f(1)‖ + 1` in place of `‖f(1)‖²` so that the
  -- constant is positive without a case split:
  --   `⌈f(a)⌋ = ⌈f(a)* f(a)⌉ ≤ ⌈(‖f(1)‖+1)·f(a* a)⌉ = ⌈f(a* a)⌉`
  --          `= ⌈f(⌈a* a⌉)⌉ = ⌈f(⌈a⌋)⌉`,
  -- using **34XIV** `cp-cs` (as `ncp_cp_cs`), **59III**.4 (`ceil_smul`) and
  -- **60VI** (`ncp_ceil`).  The second inequality is the first one at `a*`.
  have key : ∀ x : A, suppProj (f x) ≤ ceil (f (suppProj x)) := by
    intro x
    have hxx : (0 : A) ≤ star x * x := star_mul_self_nonneg x
    have hfxx : (0 : B) ≤ f (star x * x) := by
      have h0 : ((ncpPositive f) (0 : A) : B) ≤ (ncpPositive f) (star x * x) :=
        (ncpPositive f).monotone hxx
      rwa [map_zero] at h0
    have h1 : star (f x : B) * f x
        ≤ ((‖(f 1 : B)‖ + 1 : ℝ)) • f (star x * x) :=
      (ncp_cp_cs f x).trans (smul_le_smul_of_nonneg_right (by linarith) hfxx)
    have h2 := ceil_mono (star_mul_self_nonneg (f x : B)) h1
    rw [ceil_smul hfxx (by positivity : (0:ℝ) < ‖(f 1 : B)‖ + 1)] at h2
    have h3 : ceil ((ncpPositive f) (star x * x) : B)
        = ceil ((ncpPositive f) (ceil (star x * x)) : B) :=
      ncp_ceil (ncpPositive f) f.preservesDirSups' _ hxx
    simp only [ncpPositive_apply] at h3
    rw [suppProj, suppProj, ← h3]
    exact h2
  refine ⟨key a, ?_⟩
  have h1 : rangeProj (f a : B) = suppProj (f (star a)) := by
    rw [rangeProj, suppProj, ncp_star f a, star_star]
  have h2 : suppProj (star a) = rangeProj a := by
    rw [suppProj, rangeProj, star_star]
  rw [h1, ← h2]
  exact key (star a)

/-! ## Parsec 620 -/

omit [VonNeumannAlgebra A] [VonNeumannAlgebra B] in
/-- A normal positive map preserves the infima of filtered sets of
self-adjoint elements: apply normality to `-D`. -/
private theorem preservesDirInfs (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f)
    (D : Set (selfAdjoint A)) (s : selfAdjoint A) (hne : D.Nonempty)
    (hdir : DirectedOn (· ≥ ·) D) (hglb : IsGLB D s) :
    IsGLB ((fun d : selfAdjoint A => f (d : A)) '' D) (f (s : A)) := by
  have hnegle : ∀ x y : selfAdjoint A, x ≤ y ↔ -y ≤ -x := by
    intro x y
    constructor <;> intro h <;>
      exact Subtype.coe_le_coe.mp (by
        simpa using neg_le_neg (Subtype.coe_le_coe.mpr h))
  set E : Set (selfAdjoint A) := (fun d : selfAdjoint A => -d) '' D with hE
  have hEne : E.Nonempty := hne.image _
  have hEdir : DirectedOn (· ≤ ·) E := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzx, hzy⟩ := hdir x hx y hy
    exact ⟨-z, ⟨z, hz, rfl⟩, (hnegle z x).mp hzx, (hnegle z y).mp hzy⟩
  have hElub : IsLUB E (-s) := by
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      exact (hnegle s d).mp (hglb.1 hd)
    · intro u hu
      have h1 : ∀ d ∈ D, -u ≤ d := by
        intro d hd
        exact (hnegle (-u) d).mpr (by simpa using hu ⟨d, hd, rfl⟩)
      simpa using (hnegle (-u) s).mp (hglb.2 h1)
  have hkey := hf E (-s) hEne hEdir hElub
  have himg : (fun d : selfAdjoint A => f (d : A)) '' E
      = (fun z : B => -z) '' ((fun d : selfAdjoint A => f (d : A)) '' D) := by
    rw [hE, ← Set.image_comp, ← Set.image_comp]
    refine Set.image_congr fun d _ => ?_
    show f ((-d : selfAdjoint A) : A) = -f (d : A)
    rw [show ((-d : selfAdjoint A) : A) = -(d : A) from rfl, map_neg]
  have hfs : f ((-s : selfAdjoint A) : A) = -f (s : A) := by
    rw [show ((-s : selfAdjoint A) : A) = -(s : A) from rfl, map_neg]
  rw [himg, hfs] at hkey
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    have := hkey.1 ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    simpa using neg_le_neg this
  · intro u hu
    have h1 : ∀ z ∈ (fun z : B => -z) '' ((fun d : selfAdjoint A => f (d : A)) '' D), z ≤ -u := by
      rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
      exact neg_le_neg (hu ⟨d, hd, rfl⟩)
    have := hkey.2 h1
    simpa using neg_le_neg this

/-- floor is monotone on effects -/
private theorem floor_mono' {u v : A} (hu : u ∈ effects A) (hv : v ∈ effects A)
    (huv : u ≤ v) : floor u ≤ floor v :=
  (floor_isGreatest hv).2 ⟨(floor_spec hu).1, (floor_le hu).trans huv⟩


/-- **62I** (vn.tex:3010, Proposition): for an ncpsu-map `f : A → B` and an
effect `a`: `⌊f(a)⌋ = ⌊f(⌊a⌋)⌋`. -/
theorem ncpsu_floor (f : NCPSUMap A B) (a : A) (ha : a ∈ effects A) :
    floor (f.toNCPMap a) = floor (f.toNCPMap (floor a)) := by
  set g : NCPMap A B := f.toNCPMap with hg
  have hmono : ∀ x y : A, x ≤ y → (g x : B) ≤ g y := fun x y h =>
    (ncpPositive g).monotone h
  have hnn : ∀ x : A, 0 ≤ x → (0 : B) ≤ g x := by
    intro x hx
    have h0 : ((ncpPositive g) (0 : A) : B) ≤ (ncpPositive g) x :=
      (ncpPositive g).monotone hx
    rwa [map_zero] at h0
  have heff : ∀ x : A, x ∈ effects A → (g x : B) ∈ effects B := by
    intro x hx
    exact ⟨hnn x hx.1, (hmono x 1 hx.2).trans f.subunital'⟩
  have hone : ‖(1 : B)‖ ≤ 1 := by
    have h : ‖(1 : B)‖ = ‖(1 : B)‖ * ‖(1 : B)‖ := by
      have := CStarRing.norm_star_mul_self (x := (1 : B))
      rwa [star_one, one_mul] at this
    nlinarith [norm_nonneg (1 : B)]
  have hf1 : ‖(g 1 : B)‖ ≤ 1 :=
    (CStarAlgebra.norm_le_norm_of_nonneg_of_le (hnn 1 zero_le_one) f.subunital').trans hone
  -- `⌊f(x)⌋ = ⌊f(x²)⌋` for an effect `x`
  have hstep : ∀ x : A, x ∈ effects A → floor (g x : B) = floor (g (x ^ 2) : B) := by
    intro x hx
    have hx2 : x ^ 2 ∈ effects A := sq_mem_effects hx
    have hsq : (g x : B) ^ 2 ≤ g (x ^ 2) := by
      have h := ncp_cp_cs g x
      have hxsa : star x = x := (IsSelfAdjoint.of_nonneg hx.1).star_eq
      have hgsa : star (g x : B) = g x := (IsSelfAdjoint.of_nonneg (hnn x hx.1)).star_eq
      rw [hxsa, hgsa, ← sq, ← sq] at h
      refine h.trans ?_
      have hnn2 : (0 : B) ≤ g (x ^ 2) := hnn _ hx2.1
      have : (0 : B) ≤ (1 - ‖(g 1 : B)‖) • g (x ^ 2) :=
        smul_nonneg (by linarith) hnn2
      rw [sub_smul, one_smul, sub_nonneg] at this
      exact this
    have h1 : floor (g x : B) ≤ floor (g (x ^ 2) : B) := by
      rw [(ceil_floor_basic_3 (g x : B) (heff x hx)).1]
      exact floor_mono' (sq_mem_effects (heff x hx)) (heff _ hx2) hsq
    have h2 : floor (g (x ^ 2) : B) ≤ floor (g x : B) :=
      floor_mono' (heff _ hx2) (heff x hx)
        (hmono _ _ (by
          have := pow_antitone_of_mem_effects hx (by norm_num : 1 ≤ 2)
          simpa using this))
    exact le_antisymm h1 h2
  -- `⌊f(a)⌋ = ⌊f(a^{2ⁿ})⌋`
  have hiter : ∀ n : ℕ, floor (g a : B) = floor (g (a ^ 2 ^ n) : B) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [ih, hstep _ (pow_mem_effects ha (2 ^ k)), ← pow_mul, pow_succ]
  -- `⌊f(a)⌋ ≤ f(a^{2ⁿ})` for every `n`
  have hle : ∀ n : ℕ, floor (g a : B) ≤ (g (a ^ 2 ^ n) : B) := by
    intro n
    rw [hiter n]
    exact floor_le (heff _ (pow_mem_effects ha (2 ^ n)))
  -- the infimum `⌊a⌋ = ⋀ₙ a^{2ⁿ}` is preserved by normality
  obtain ⟨-, hglbA⟩ := vna_floor a ha
  set E : Set (selfAdjoint A) :=
    Set.range fun n : ℕ =>
      (⟨a ^ 2 ^ n, IsSelfAdjoint.of_nonneg (pow_mem_effects ha (2 ^ n)).1⟩ :
        selfAdjoint A) with hEdef
  have hEne : E.Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hanti : ∀ m n : ℕ, m ≤ n → a ^ 2 ^ n ≤ a ^ 2 ^ m := fun m n hmn =>
    pow_antitone_of_mem_effects ha (Nat.pow_le_pow_right (by norm_num) hmn)
  have hEdir : DirectedOn (· ≥ ·) E := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ⟨_, ⟨max m n, rfl⟩,
      Subtype.coe_le_coe.mp (hanti m _ (le_max_left m n)),
      Subtype.coe_le_coe.mp (hanti n _ (le_max_right m n))⟩
  set sfl : selfAdjoint A :=
    ⟨floor a, (floor_spec ha).1.isSelfAdjoint⟩ with hsfl
  have hEglb : IsGLB E sfl := by
    constructor
    · rintro _ ⟨n, rfl⟩
      exact Subtype.coe_le_coe.mp (hglbA.1 ⟨n, rfl⟩)
    · intro u hu
      refine Subtype.coe_le_coe.mp (hglbA.2 ?_)
      rintro _ ⟨n, rfl⟩
      exact Subtype.coe_le_coe.mpr (hu ⟨n, rfl⟩)
  have hglbB := preservesDirInfs (ncpPositive g) g.preservesDirSups' E sfl hEne hEdir hEglb
  have hlow : floor (g a : B) ≤ (g (floor a) : B) := by
    refine hglbB.2 ?_
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact hle n
  -- assemble
  have hfa : floor a ∈ effects A := ⟨(floor_spec ha).1.nonneg, floor_le ha |>.trans ha.2⟩
  refine le_antisymm ?_ ?_
  · exact (floor_isGreatest (heff _ hfa)).2 ⟨(floor_spec (heff a ha)).1, hlow⟩
  · exact floor_mono' (heff _ hfa) (heff a ha) (hmono _ _ (floor_le ha))

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
    {y : K | carrier g hg y = y} = closure (Set.range T) := by
  -- The thesis's argument for `carrier_ad`, transported: take `p` the
  -- orthogonal projection onto `closure (range T)`.  Then `T* p^⊥ T = 0`
  -- because `p^⊥ T = 0`, and for any projection `q` with `T* q^⊥ T = 0` one
  -- has `‖q^⊥ T x‖² = ⟪Tx, q^⊥ T x⟫ = ⟪x, T* q^⊥ T x⟫ = 0`, so `q^⊥` kills
  -- `range T`, hence (its kernel being closed) all of `closure (range T)`,
  -- i.e. `q^⊥ p = 0` and so `p ≤ q` by **55X** `proj_le_iff`.
  classical
  set M : Submodule ℂ K := (LinearMap.range (T : H →ₗ[ℂ] K)).topologicalClosure
    with hMdef
  have hOP : M.HasOrthogonalProjection := inferInstance
  set p : K →L[ℂ] K := M.starProjection with hpdef
  have hproj : IsStarProjection p := isStarProjection_starProjection
  have hmemM : ∀ x : H, T x ∈ M := fun x =>
    Submodule.le_topologicalClosure _ ⟨x, rfl⟩
  have hpT : ∀ x : H, p (T x) = T x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (hmemM x)
  have h0 : g (1 - p) = 0 := by
    rw [h]
    ext x
    simp [hpT x]
  have hleast : ∀ q : (K →L[ℂ] K), IsStarProjection q → g (1 - q) = 0 → p ≤ q := by
    intro q hq hq0
    rw [h] at hq0
    set e : K →L[ℂ] K := 1 - q with hedef
    have heproj : IsStarProjection e := hq.one_sub
    have hself : ContinuousLinearMap.adjoint e = e := by
      rw [← ContinuousLinearMap.star_eq_adjoint]; exact heproj.isSelfAdjoint.star_eq
    have hidem : ∀ y : K, e (e y) = e y := by
      intro y
      have := congrArg (fun S : K →L[ℂ] K => S y) heproj.isIdempotentElem.eq
      simpa using this
    have hE : ∀ x : H, e (T x) = 0 := by
      intro x
      have h1 : (ContinuousLinearMap.adjoint T ∘L e ∘L T) x = 0 := by
        rw [hq0]; rfl
      have h2 : (⟪T x, e (T x)⟫ : ℂ) = 0 := by
        have := congrArg (fun z => (⟪x, z⟫ : ℂ)) h1
        simpa [ContinuousLinearMap.adjoint_inner_right] using this
      have h3 : (⟪e (T x), e (T x)⟫ : ℂ) = (⟪T x, e (T x)⟫ : ℂ) := by
        conv_lhs => rw [← hself]
        rw [ContinuousLinearMap.adjoint_inner_left, hself, hidem]
      rw [h2] at h3
      exact inner_self_eq_zero.mp h3
    have hker : M ≤ LinearMap.ker (e : K →ₗ[ℂ] K) := by
      rw [hMdef]
      refine Submodule.topologicalClosure_minimal _ ?_ e.isClosed_ker
      rintro _ ⟨x, rfl⟩
      exact hE x
    have hpe : p * e = 0 := by
      have h1 : e * p = 0 := by
        ext y
        show e (p y) = 0
        exact hker (M.starProjection_apply_mem y)
      have h2 := congrArg star h1
      rwa [star_mul, heproj.isSelfAdjoint.star_eq, hproj.isSelfAdjoint.star_eq,
        star_zero] at h2
    exact (proj_le_iff (projection_basic_2 q hq).2 hproj).mpr hpe
  have hcar : carrier g hg = p := carrier_eq g hg hproj h0 hleast
  have hset : ((LinearMap.range (T : H →ₗ[ℂ] K) : Submodule ℂ K) : Set K)
      = Set.range T := by
    ext z; simp [LinearMap.mem_range]
  rw [hcar]
  ext y
  simp only [Set.mem_ofPred_eq, hpdef, Submodule.starProjection_eq_self_iff]
  rw [hMdef, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, hset]

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
    f a = f (p * a) ∧ f a = f (a * p) ∧ f a = f (p * a * p) := by
  -- the thesis's first paragraph: the case `B = ℂ`
  have hscalar : ∀ ω : A →ₗ[ℂ] ℂ, IsPositiveMap ω → ω (1 - p) = 0 → ∀ x : A,
      ω x = ω (p * x) ∧ ω x = ω (x * p) ∧ ω x = ω (p * x * p) := by
    intro ω hω h0
    have hq : (1 - p) ∈ effects A := effect_orthosupplement p hp
    have hqsa : star (1 - p) = 1 - p := (IsSelfAdjoint.of_nonneg hq.1).star_eq
    have hnn : (0 : ℂ) ≤ ω ((1 - p) * (1 - p)) := by
      refine hω _ ?_
      simpa [hqsa] using star_mul_self_nonneg (1 - p)
    have hle : ω ((1 - p) * (1 - p)) ≤ ω (1 - p) := by
      have hs := hω ((1 - p) - (1 - p) * (1 - p)) (sub_nonneg.mpr (mul_self_le_self hq))
      rw [map_sub, sub_nonneg] at hs
      exact hs
    have hzero : ω ((1 - p) * (1 - p)) = 0 := le_antisymm (h0 ▸ hle) hnn
    -- Kadison's inequality (**30IV**.1) kills `ω(p^⊥ x)`
    have hkad : ∀ x : A, ω ((1 - p) * x) = 0 := by
      intro x
      have hk := omega_norm_basic_1 ω hω (1 - p) x
      rw [hqsa, hzero, zero_mul, ← Complex.ofReal_pow, ← Complex.ofReal_zero,
        Complex.real_le_real] at hk
      have h3 : ‖ω ((1 - p) * x)‖ = 0 := by
        have := le_antisymm hk (by positivity : (0:ℝ) ≤ ‖ω ((1 - p) * x)‖ ^ 2)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      exact norm_eq_zero.mp h3
    have hleft : ∀ x : A, ω x = ω (p * x) := by
      intro x
      have hx := hkad x
      rw [sub_mul, one_mul, map_sub, sub_eq_zero] at hx
      exact hx
    have hinv := cstar_p_implies_i ω hω
    have hright : ∀ x : A, ω x = ω (x * p) := by
      intro x
      have h1 : ω (star (x * p)) = ω (star x) := by
        rw [star_mul, (IsSelfAdjoint.of_nonneg hp.1).star_eq]
        exact (hleft (star x)).symm
      rw [hinv (x * p), hinv x] at h1
      exact (star_injective h1).symm
    exact fun x => ⟨hleft x, hright x, (hleft x).trans (hright (p * x))⟩
  -- the thesis's second paragraph: the states of `B` are separating
  have hsep : ∀ y z : B, (∀ ω : B →ₗ[ℂ] ℂ, IsState ω → ω y = ω z) → y = z := by
    intro y z hyz
    have key : ∀ w : B, (∀ ω : B →ₗ[ℂ] ℂ, IsState ω → ω w = 0) → (0 : B) ≤ w := by
      intro w hw
      refine (states_order_separating_2 w).mpr fun ω => ?_
      rw [hw ω.1 ω.2]
    have h1 : (0 : B) ≤ z - y := key _ fun ω hω => by rw [map_sub, hyz ω hω, sub_self]
    have h2 : (0 : B) ≤ y - z := key _ fun ω hω => by rw [map_sub, hyz ω hω, sub_self]
    exact le_antisymm (sub_nonneg.mp h1) (sub_nonneg.mp h2)
  have hcomp : ∀ ω : B →ₗ[ℂ] ℂ, IsState ω →
      IsPositiveMap (ω.comp (f.toLinearMap)) ∧ (ω.comp (f.toLinearMap)) (1 - p) = 0 := by
    intro ω hω
    refine ⟨fun x hx => hω.1 _ ?_, ?_⟩
    · have hm : (f (0 : A) : B) ≤ f x := f.monotone hx
      rwa [show (f (0 : A) : B) = 0 from map_zero f] at hm
    · simp only [LinearMap.comp_apply]
      change ω (f (1 - p)) = 0
      rw [h, map_zero]
  refine ⟨hsep _ _ fun ω hω => ?_, hsep _ _ fun ω hω => ?_, hsep _ _ fun ω hω => ?_⟩
  · exact (hscalar _ (hcomp ω hω).1 (hcomp ω hω).2 a).1
  · exact (hscalar _ (hcomp ω hω).1 (hcomp ω hω).2 a).2.1
  · exact (hscalar _ (hcomp ω hω).1 (hcomp ω hω).2 a).2.2

section Commutant

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B]

/-- **63VI** (`carrier-fundamental`, vn.tex:3145, Corollary): an np-map
`f : A → B` satisfies `f(a) = f(⌈f⌉a) = f(a⌈f⌉) = f(⌈f⌉a⌈f⌉)`.

The thesis gives no proof: 63VI is stated as an immediate Corollary of
**63IV** (`cp_comprehension`), and that is what the term below is.  The
carrier `⌈f⌉` is a projection, hence an effect, and `f(⌈f⌉^⊥) = 0` is the
defining property of `carrier` — which is exactly 63IV's hypothesis. -/
theorem carrier_fundamental (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f)
    (a : A) :
    f a = f (carrier f hf * a) ∧ f a = f (a * carrier f hf) ∧
      f a = f (carrier f hf * a * carrier f hf) :=
  cp_comprehension f (carrier f hf)
    ⟨(carrier_spec f hf).1.nonneg, (carrier_spec f hf).1.le_one⟩
    (carrier_spec f hf).2.1 a

/-! ## Parsec 640 -/

/-! ### A von Neumann subalgebra is closed under `⌈·⌉`

`ceil_mem` below is the missing ingredient for the *relativised* form of
**65IV** (`projections_norm_dense_subalgebra`): the linear span of the
projections *of a von Neumann subalgebra* `S` is norm-dense in `S`.  The
thesis never states this separately; it is its own construction
`⌈b⌉ = ⋁ₙ b^{1/2ⁿ}` (**56I**.20) read inside `S` — every iterated square
root of an element of `S` lies in `S` (a norm-closed star subalgebra is
closed under the continuous functional calculus), and `S` contains the
suprema of its bounded directed sets by definition. -/

omit [VonNeumannAlgebra A] in
/-- `√x = cfc √ x` for positive `x`.  Mathlib's `CFC.sqrt` is defined by the
*non-unital* `ℝ≥0`-valued calculus; `cfc_mem` needs the unital `ℝ`-valued
one. -/
private theorem sqrt_eq_cfc_real {x : A} (hx : 0 ≤ x) :
    CFC.sqrt x = cfc Real.sqrt x := by
  refine CFC.sqrt_unique ?_ (cfc_nonneg fun r _ => Real.sqrt_nonneg r)
  rw [← cfc_mul _ _ x (by fun_prop) (by fun_prop)]
  nth_rewrite 2 [← cfc_id ℝ x]
  refine cfc_congr fun r hr => ?_
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hx hr)

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
/-- A norm-closed `ℂ`-star-subalgebra is closed under the (`ℝ`-valued,
unital) continuous functional calculus. -/
private theorem cfc_mem_of_isClosed {S : StarSubalgebra ℂ A}
    (hcl : IsClosed (S : Set A)) (f : ℝ → ℝ) {x : A} (hx : x ∈ S) :
    cfc f x ∈ S := by
  have : IsClosed ((S : StarSubalgebra ℂ A) : Set A) := hcl
  exact cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) f hx

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
/-- A `ℂ`-star-subalgebra is closed under real scalar multiples. -/
private theorem real_smul_mem {S : StarSubalgebra ℂ A} (r : ℝ) {y : A}
    (hy : y ∈ S) : r • y ∈ S := by
  have hsm : r • y = ((r : ℝ) : ℂ) • y := by
    rw [← algebraMap_smul ℂ r y]
    simp
  rw [hsm]
  exact SMulMemClass.smul_mem _ hy

/-- **56I**/**65IV**, relativised: a von Neumann subalgebra `S` of `A` is
closed under the ceiling — `⌈x⌉ ∈ S` for every positive `x ∈ S`.

This is **56I**.20's formula `⌈b⌉ = ⋁ₙ b^{1/2ⁿ}` (`vna_ceil_sup`) read
inside `S`: the iterated square roots of `b = ‖x‖⁻¹x` stay in `S` because a
norm-closed star subalgebra is closed under the continuous functional
calculus, they form a chain, and `S` contains the suprema of its bounded
directed sets. -/
theorem ceil_mem {S : StarSubalgebra ℂ A} (hS : IsVNSubalgebra A S)
    {x : A} (hx : 0 ≤ x) (hxS : x ∈ S) : ceil x ∈ S := by
  classical
  rcases eq_or_ne x 0 with rfl | hne
  · rw [ceil_zero]; exact zero_mem _
  have hn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hne
  set b : A := (‖x‖⁻¹ : ℝ) • x with hbdef
  have hbnn : (0 : A) ≤ b := smul_nonneg (by positivity) hx
  have hbeff : b ∈ effects A := by
    refine ⟨hbnn, ?_⟩
    refine (CStarAlgebra.norm_le_one_iff_of_nonneg _ hbnn).mp ?_
    rw [hbdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      inv_mul_cancel₀ (ne_of_gt hn)]
  have hbS : b ∈ S := by
    rw [hbdef]
    exact real_smul_mem _ hxS
  -- every iterated square root of `b` lies in `S`
  have hmem : ∀ n : ℕ, sqrtIter b n ∈ S := by
    intro n
    induction n with
    | zero => exact hbS
    | succ n ih =>
        rw [sqrtIter_succ, sqrt_eq_cfc_real (sqrtIter_mem_effects hbeff n).1]
        exact cfc_mem_of_isClosed hS.isClosed _ ih
  -- ... and they form a chain with supremum `⌈b⌉`
  set E : ℕ → selfAdjoint A := fun n =>
    ⟨sqrtIter b n, IsSelfAdjoint.of_nonneg (sqrtIter_mem_effects hbeff n).1⟩ with hE
  have hEmono : Monotone E := fun m n hmn =>
    Subtype.coe_le_coe.mp (sqrtIter_monotone hbeff hmn)
  set D : Set (selfAdjoint A) := Set.range E with hD
  have hDne : D.Nonempty := ⟨E 0, 0, rfl⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ⟨E (max m n), ⟨max m n, rfl⟩, hEmono (le_max_left _ _),
      hEmono (le_max_right _ _)⟩
  have hcsa : IsSelfAdjoint (ceil b) := (ceil_spec hbnn).1.isSelfAdjoint
  have hlubA : IsLUB (Set.range (sqrtIter b)) (ceil b) := vna_ceil_sup b hbeff
  have hlubSA : IsLUB D (⟨ceil b, hcsa⟩ : selfAdjoint A) := by
    constructor
    · rintro _ ⟨n, rfl⟩
      exact Subtype.coe_le_coe.mp (hlubA.1 ⟨n, rfl⟩)
    · intro y hy
      refine Subtype.coe_le_coe.mp (hlubA.2 ?_)
      rintro _ ⟨n, rfl⟩
      exact Subtype.coe_le_coe.mpr (hy ⟨n, rfl⟩)
  have hcx : ceil b = ceil x := by
    rw [hbdef]; exact ceil_smul hx (by positivity : (0:ℝ) < ‖x‖⁻¹)
  have hres : ceil b ∈ S := hS.dirSup_mem D ⟨ceil b, hcsa⟩
    (by rintro _ ⟨n, rfl⟩; exact hmem n) hDne hdir hlubSA
  rwa [hcx] at hres


/-- The real spectrum of a self-adjoint element lies in `[-‖a‖, ‖a‖]`.  (Made
public for the clamping functions of **74IV** in `Completeness.lean`.) -/
theorem spectrum_abs_le {a : A} (ha : IsSelfAdjoint a) {r : ℝ}
    (hr : r ∈ spectrum ℝ a) : |r| ≤ ‖a‖ := by
  rcases subsingleton_or_nontrivial A with _ | _
  · exact absurd (isUnit_of_subsingleton _) (spectrum.mem_iff.mp hr)
  · have h : ((r : ℂ)) ∈ spectrum ℂ a := (IsSelfAdjoint.coe_mem_spectrum_complex ha).mpr hr
    simpa using spectrum.norm_le_norm_of_mem h

private theorem ramp_cont (t : ℝ) (s : Set ℝ) :
    ContinuousOn (fun r : ℝ => max (r - t) 0) s :=
  ((continuous_id.sub continuous_const).max continuous_const).continuousOn

private theorem smul_one_eq (r : ℝ) : (r • (1 : A)) = algebraMap ℂ A ((r : ℝ) : ℂ) := by
  rw [Algebra.algebraMap_eq_smul_one, ← algebraMap_smul ℂ r (1 : A)]
  simp

/-- The spectral (Riemann-sum) approximation behind the *relativised*
**65IV**: a
self-adjoint element of a von Neumann algebra is, up to `ε` in norm, a real
linear combination of the spectral projections `⌈(a - t)⁺⌉`, each of which
commutes with everything that commutes with `a` — and, since a von Neumann
subalgebra is closed under `cfc` and under `⌈·⌉` (`ceil_mem`), lies in every
von Neumann subalgebra containing `a`.  The last clause is what makes the
*relativised* **65IV** (`projections_norm_dense_subalgebra`) come out of the
same Riemann sum. -/
private theorem exists_spectral_approx (a : A) (ha : IsSelfAdjoint a) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ s : A, s ∈ Submodule.span ℂ
        {p : A | IsStarProjection p ∧ (∀ x : A, a * x = x * a → x * p = p * x) ∧
          ∀ T : StarSubalgebra ℂ A, IsVNSubalgebra A T → a ∈ T → p ∈ T} ∧
      ‖a - s‖ ≤ ε := by
  classical
  set S : Set A := {p : A | IsStarProjection p ∧ (∀ x : A, a * x = x * a → x * p = p * x) ∧
      ∀ T : StarSubalgebra ℂ A, IsVNSubalgebra A T → a ∈ T → p ∈ T}
    with hSdef
  have hone : (1 : A) ∈ S :=
    ⟨IsStarProjection.one A, fun x _ => by rw [mul_one, one_mul], fun T _ _ => one_mem T⟩
  rcases eq_or_lt_of_le (norm_nonneg a) with hM | hM
  · -- `a = 0`
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [sub_zero, ← hM]
    exact le_of_lt hε
  -- choose a mesh `h = 2‖a‖/n < ε`
  set M : ℝ := ‖a‖ with hMdef
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * M / ε)
  set n : ℕ := m + 1 with hndef
  have hn0 : (0 : ℝ) < n := by positivity
  set hh : ℝ := 2 * M / n with hhdef
  have hh0 : 0 < hh := by positivity
  have hhε : hh ≤ ε := by
    rw [hhdef, div_le_iff₀ hn0]
    have : 2 * M / ε < (n : ℝ) := lt_of_lt_of_le hm (by exact_mod_cast Nat.le_succ m)
    rw [div_lt_iff₀ hε] at this
    linarith
  set t : ℕ → ℝ := fun k => -M + k * hh with htdef
  set g : ℕ → A := fun k => cfc (fun r : ℝ => max (r - t k) 0) a with hgdef
  -- basic facts about `g`
  have hgnn : ∀ k, (0 : A) ≤ g k := fun k => cfc_nonneg fun x _ => le_max_right _ _
  have hgsa : ∀ k, IsSelfAdjoint (g k) := fun k => IsSelfAdjoint.of_nonneg (hgnn k)
  have hgmono : ∀ k, g (k + 1) ≤ g k := by
    intro k
    refine (cfc_le_iff _ _ a (ramp_cont _ _) (ramp_cont _ _) ha).mpr fun r _ => ?_
    have : t k ≤ t (k + 1) := by
      simp only [htdef]; push_cast; nlinarith
    exact max_le_max (by linarith) le_rfl
  have hgle : ∀ k, g k - g (k + 1) ≤ hh • (1 : A) := by
    intro k
    have ht : t (k + 1) - t k = hh := by simp only [htdef]; push_cast; ring
    rw [← cfc_sub _ _ a (ramp_cont _ _) (ramp_cont _ _),
      show (hh • (1 : A)) = cfc (fun _ : ℝ => hh) a by
        rw [cfc_const _ _ ha]; simp [Algebra.algebraMap_eq_smul_one]]
    refine (cfc_le_iff _ _ a (by fun_prop) (by fun_prop) ha).mpr fun r _ => ?_
    rcases le_total r (t k) with hr | hr
    · rw [max_eq_right (by linarith : r - t k ≤ 0),
        max_eq_right (by linarith [ht, hh0.le] : r - t (k + 1) ≤ 0)]
      linarith
    · rcases le_total r (t (k + 1)) with hr' | hr'
      · rw [max_eq_left (by linarith : (0 : ℝ) ≤ r - t k),
          max_eq_right (by linarith : r - t (k + 1) ≤ 0)]
        linarith
      · rw [max_eq_left (by linarith : (0 : ℝ) ≤ r - t k),
          max_eq_left (by linarith : (0 : ℝ) ≤ r - t (k + 1))]
        linarith
  have hgprod : ∀ k, (hh • (1 : A) - (g k - g (k + 1))) * g (k + 1) = 0 := by
    intro k
    have ht : t (k + 1) - t k = hh := by simp only [htdef]; push_cast; ring
    rw [show (hh • (1 : A)) = cfc (fun _ : ℝ => hh) a by
        rw [cfc_const _ _ ha]; simp [Algebra.algebraMap_eq_smul_one],
      ← cfc_sub _ _ a (ramp_cont _ _) (ramp_cont _ _),
      ← cfc_sub _ _ a (by fun_prop) (by fun_prop),
      ← cfc_mul _ _ a (by fun_prop) (ramp_cont _ _),
      show (0 : A) = cfc (fun _ : ℝ => (0 : ℝ)) a by simp]
    refine cfc_congr fun r _ => ?_
    rcases le_total r (t (k + 1)) with hr | hr
    · rw [max_eq_right (by linarith : r - t (k + 1) ≤ 0)]; ring
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ r - t (k + 1)),
        max_eq_left (by linarith [ht, hh0.le] : (0 : ℝ) ≤ r - t k),
        show hh - (r - t k - (r - t (k + 1))) = 0 by linarith, zero_mul]
  have hg0 : g 0 = a + M • (1 : A) := by
    have h1 : cfc (fun r : ℝ => r + M) a = a + M • (1 : A) := by
      rw [cfc_add a (fun r : ℝ => r) (fun _ : ℝ => M) (by fun_prop) (by fun_prop),
        show (fun r : ℝ => r) = (id : ℝ → ℝ) from rfl, cfc_id ℝ a, cfc_const _ _ ha]
      simp [Algebra.algebraMap_eq_smul_one]
    rw [← h1]
    refine cfc_congr fun r hr => ?_
    have hb := spectrum_abs_le ha hr
    rw [abs_le] at hb
    have ht0 : t 0 = -M := by simp [htdef]
    rw [ht0, max_eq_left (by linarith : (0 : ℝ) ≤ r - -M)]
    ring
  have hgn : g n = 0 := by
    rw [show (0 : A) = cfc (fun _ : ℝ => (0 : ℝ)) a by simp]
    refine cfc_congr fun r hr => ?_
    have hb := spectrum_abs_le ha hr
    rw [abs_le] at hb
    have htn : t n = M := by
      have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
      simp only [htdef, hhdef]
      field_simp
      ring
    rw [htn]
    exact max_eq_right (by linarith)
  -- the spectral projections
  set e : ℕ → A := fun k => ceil (g k) with hedef
  have heproj : ∀ k, IsStarProjection (e k) := fun k => (ceil_spec (hgnn k)).1
  have hege : ∀ k, g k * e k = g k := fun k => (ceil_spec (hgnn k)).2.1
  have hemono : ∀ k, e (k + 1) ≤ e k := fun k => ceil_mono (hgnn (k + 1)) (hgmono k)
  have hgek : ∀ k, g (k + 1) * e k = g (k + 1) := fun k =>
    (ceil_le_iff (hgnn (k + 1)) (heproj k)).mp (hemono k)
  have hecomm : ∀ (k) (x : A), a * x = x * a → x * e k = e k * x := by
    intro k x hx
    refine vna_ceil_comm (g k) (hgnn k) x ?_
    exact (Commute.cfc_real hx _).symm
  have hgmem : ∀ T : StarSubalgebra ℂ A, IsVNSubalgebra A T → a ∈ T → ∀ k, g k ∈ T := by
    intro T hT haT k
    simp only [hgdef]
    exact cfc_mem_of_isClosed hT.isClosed _ haT
  have hemem : ∀ k, e k ∈ S := fun k =>
    ⟨heproj k, hecomm k, fun T hT haT => ceil_mem hT (hgnn k) (hgmem T hT haT k)⟩
  -- `e k` commutes with `g j`
  have hegcomm : ∀ j k, g j * e k = e k * g j := fun j k =>
    hecomm k (g j) ((Commute.cfc_real (Commute.refl a) _).symm)
  -- I1
  have hI1 : ∀ k, g k - g (k + 1) ≤ hh • e k := by
    intro k
    set x : A := g k - g (k + 1) with hxdef
    have hxe : x * e k = x := by rw [hxdef, sub_mul, hege k, hgek k]
    have hex : e k * x = x := by
      rw [hxdef, mul_sub, ← hegcomm k k, ← hegcomm (k + 1) k, hege k, hgek k]
    have hconj : e k * x * e k = x := by rw [hex, hxe]
    have hsa : star (e k) = e k := (heproj k).isSelfAdjoint.star_eq
    have h1 : e k * x * e k ≤ e k * (hh • (1 : A)) * e k := by
      have := star_left_conjugate_le_conjugate (hgle k) (e k)
      rwa [hsa] at this
    rw [hconj] at h1
    refine h1.trans_eq ?_
    rw [mul_smul_comm, smul_mul_assoc, mul_one, (heproj k).isIdempotentElem.eq]
  -- I2
  have hI2 : ∀ k, hh • e (k + 1) ≤ g k - g (k + 1) := by
    intro k
    set y : A := g k - g (k + 1) with hydef
    have hynn : (0 : A) ≤ y := sub_nonneg.mpr (hgmono k)
    set z : A := hh • (1 : A) - y with hzdef
    have hzsa : IsSelfAdjoint z := by
      refine IsSelfAdjoint.sub ?_ ((hgsa k).sub (hgsa (k + 1)))
      rw [smul_one_eq]
      exact isSelfAdjoint_algebraMap_ofReal hh
    have hzg : g (k + 1) * z = 0 := by
      have h := congrArg star (hgprod k)
      rw [star_mul, hzsa.star_eq, (hgsa (k + 1)).star_eq, star_zero] at h
      exact h
    have hez : e (k + 1) * z = 0 := ceil_mul_eq_zero (hgnn (k + 1)) hzg
    have hey : e (k + 1) * y = hh • e (k + 1) := by
      have := hez
      rw [hzdef, mul_sub, sub_eq_zero] at this
      rw [← this, mul_smul_comm, mul_one]
    have hycomm : y * e (k + 1) = e (k + 1) * y := by
      rw [hydef, sub_mul, mul_sub, hegcomm k (k + 1), hegcomm (k + 1) (k + 1)]
    have hq : (1 - e (k + 1)) * y * (1 - e (k + 1)) = y - hh • e (k + 1) := by
      have hidem := (heproj (k + 1)).isIdempotentElem.eq
      calc (1 - e (k + 1)) * y * (1 - e (k + 1))
          = y - y * e (k + 1) - e (k + 1) * y + e (k + 1) * y * e (k + 1) := by
            noncomm_ring
        _ = y - hh • e (k + 1) := by
            rw [hycomm, hey, smul_mul_assoc, hidem]
            module
    have hnn : (0 : A) ≤ (1 - e (k + 1)) * y * (1 - e (k + 1)) := by
      have := star_left_conjugate_nonneg hynn (1 - e (k + 1))
      rwa [(heproj (k + 1)).one_sub.isSelfAdjoint.star_eq] at this
    rw [hq] at hnn
    exact sub_nonneg.mp hnn
  -- assemble the Riemann sum
  set E : A := ∑ k ∈ Finset.range n, e k with hEdef
  have hsum1 : ∑ k ∈ Finset.range n, (g k - g (k + 1)) = a + M • (1 : A) := by
    rw [Finset.sum_range_sub' g n, hg0, hgn, sub_zero]
  have hlow : a + M • (1 : A) ≤ hh • E := by
    rw [← hsum1, hEdef, Finset.smul_sum]
    exact Finset.sum_le_sum fun k _ => hI1 k
  have hhigh : hh • E ≤ hh • (1 : A) + (a + M • (1 : A)) := by
    have h1 : ∑ k ∈ Finset.range m, hh • e (k + 1)
        ≤ ∑ k ∈ Finset.range m, (g k - g (k + 1)) :=
      Finset.sum_le_sum fun k _ => hI2 k
    have h2 : ∑ k ∈ Finset.range m, (g k - g (k + 1)) = g 0 - g m :=
      Finset.sum_range_sub' g m
    have h3 : g 0 - g m ≤ a + M • (1 : A) := by
      rw [← hg0]; exact sub_le_self _ (hgnn m)
    have h4 : hh • e 0 ≤ hh • (1 : A) :=
      smul_le_smul_of_nonneg_left (heproj 0).le_one hh0.le
    have h5 : hh • E = ∑ k ∈ Finset.range m, hh • e (k + 1) + hh • e 0 := by
      rw [hEdef, Finset.smul_sum, hndef, Finset.sum_range_succ' (fun k => hh • e k) m]
    rw [h5, add_comm (hh • (1 : A))]
    exact add_le_add (le_trans (h1.trans_eq h2) h3) h4
  have hrsmul : ∀ (r : ℝ) (x : A), r • x = ((r : ℂ)) • x := by
    intro r x
    rw [← algebraMap_smul ℂ r x]
    simp
  refine ⟨(-M) • (1 : A) + hh • E, ?_, ?_⟩
  · refine Submodule.add_mem _ ?_ ?_
    · rw [hrsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hone)
    · rw [hrsmul]
      refine Submodule.smul_mem _ _ ?_
      exact Submodule.sum_mem _ fun k _ => Submodule.subset_span (hemem k)
  · have hd : a - ((-M) • (1 : A) + hh • E) = a + M • (1 : A) - hh • E := by
      rw [neg_smul]; abel
    have hsa : IsSelfAdjoint (a - ((-M) • (1 : A) + hh • E)) := by
      rw [hd]
      refine (ha.add ?_).sub ?_
      · rw [smul_one_eq]; exact isSelfAdjoint_algebraMap_ofReal M
      · have hEsa : IsSelfAdjoint E := by
          show star E = E
          rw [hEdef, star_sum]
          exact Finset.sum_congr rfl fun k _ => (heproj k).isSelfAdjoint.star_eq
        show star (hh • E) = hh • E
        rw [hrsmul, star_smul, hEsa.star_eq, Complex.star_def, Complex.conj_ofReal]
    have hup : a - ((-M) • (1 : A) + hh • E) ≤ algebraMap ℂ A ((hh : ℝ) : ℂ) := by
      rw [hd, ← smul_one_eq]
      exact le_trans (sub_nonpos.mpr hlow) (smul_nonneg hh0.le zero_le_one)
    have hlo : -(algebraMap ℂ A ((hh : ℝ) : ℂ)) ≤ a - ((-M) • (1 : A) + hh • E) := by
      rw [hd, ← smul_one_eq, neg_le_sub_iff_le_add]
      exact hhigh.trans_eq (add_comm _ _)
    exact le_trans ((positive_basic_2_3a _ hsa hh hh0.le).mp ⟨hlo, hup⟩) hhε

/-- **64II**/**65IV**, self-adjoint case: `a` is a norm limit of linear
combinations of the spectral projections `⌈(a - t)⁺⌉`, all of which lie in
`{a}^□□`. -/
private theorem mem_closure_span_spectral (a : A) (ha : IsSelfAdjoint a) :
    a ∈ closure (Submodule.span ℂ
      {p : A | IsStarProjection p ∧ (∀ x : A, a * x = x * a → x * p = p * x) ∧
        ∀ T : StarSubalgebra ℂ A, IsVNSubalgebra A T → a ∈ T → p ∈ T} : Set A) := by
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  obtain ⟨s, hs, hnorm⟩ := exists_spectral_approx a ha (half_pos hε)
  refine ⟨s, hs, ?_⟩
  rw [dist_eq_norm]
  linarith

section AbelianStone

open WeakDual

/-- The linear span of the projections of a *commutative* ∗-algebra is a
∗-subalgebra: a product of commuting projections is a projection, `1` is a
projection, and projections are self-adjoint.  (Needed to run Stone–
Weierstraß against the projections of `C(spec 𝒜)` in **64II** below.) -/
private def projStarSubalgebra (R : Type*) [CommRing R] [Algebra ℂ R] [StarRing R]
    [StarModule ℂ R] : StarSubalgebra ℂ R where
  toSubalgebra :=
    Submodule.toSubalgebra (Submodule.span ℂ {p : R | IsStarProjection p})
      (Submodule.subset_span (IsStarProjection.one R))
      (fun x y hx hy => by
        have hle : Submodule.span ℂ {p : R | IsStarProjection p}
            * Submodule.span ℂ {p : R | IsStarProjection p}
            ≤ Submodule.span ℂ {p : R | IsStarProjection p} := by
          rw [Submodule.span_mul_span]
          refine Submodule.span_le.mpr ?_
          rintro _ ⟨p, hp, q, hq, rfl⟩
          exact Submodule.subset_span (hp.mul hq (Commute.all _ _))
        exact hle (Submodule.mul_mem_mul hx hy))
  star_mem' := by
    intro x hx
    show star x ∈ Submodule.span ℂ {p : R | IsStarProjection p}
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (show x ∈ Submodule.span ℂ _ from hx)
    · intro p hp
      exact Submodule.subset_span
        (by rw [(hp : IsStarProjection p).isSelfAdjoint.star_eq]; exact hp)
    · simp
    · intro a b _ _ ha hb
      rw [star_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha
      rw [star_smul]; exact Submodule.smul_mem _ _ ha

/-- The Stone–Weierstraß step of **64II**: on a compact Hausdorff
*extremally disconnected* space the linear span of the projections of
`C(X, ℂ)` — the indicators of the clopen sets — is norm dense.

The projections separate the points because such an `X` is totally
separated (Mathlib's instance for an extremally disconnected Hausdorff
space); that is what the thesis's **53III**
`vn_spectrum_extremally_disconnected` is for.  Stone–Weierstraß then applies
to the ∗-subalgebra `projStarSubalgebra` above. -/
private theorem mem_closure_span_projections_continuousMap {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [ExtremallyDisconnected X]
    (f : C(X, ℂ)) :
    f ∈ closure (Submodule.span ℂ {p : C(X, ℂ) | IsStarProjection p} : Set C(X, ℂ)) := by
  have hsep : (projStarSubalgebra C(X, ℂ)).SeparatesPoints := by
    rintro x y hxy
    obtain ⟨U, hU, hxU, hyU⟩ := exists_isClopen_of_totally_separated hxy
    refine ⟨(chi U : X → ℂ), ⟨chi U, ?_, rfl⟩, ?_⟩
    · refine Submodule.subset_span ?_
      refine ⟨?_, chi_isSelfAdjoint U⟩
      show chi U * chi U = chi U
      ext z
      by_cases hz : z ∈ U
      · simp [chi_of_mem hU hz]
      · simp [chi_of_notMem hU hz]
    · rw [chi_of_mem hU hxU, chi_of_notMem hU hyU]
      exact one_ne_zero
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (projStarSubalgebra C(X, ℂ)) hsep
  have hmem : f ∈ (projStarSubalgebra C(X, ℂ)).topologicalClosure := by
    rw [htop]; trivial
  exact hmem

/-- **64II** (`abelian-projections-norm-dense`, vn.tex:3162, Proposition):
every element of a *commutative* von Neumann algebra is the norm limit of
linear combinations of projections.

This is the thesis's own proof (vn.tex:3165): by **53II** `ngelfand_vna` it
suffices to show that the span of the projections is norm dense in
`C(spec 𝒜)`, and for that it suffices by Stone–Weierstraß that the
projections of `C(spec 𝒜)` — the indicators of its clopen sets — separate
the points of `spec 𝒜`, which they do because `spec 𝒜` is extremally
disconnected (**53III**).  The transport back along `γ_𝒜⁻¹` is by continuity:
an injective ∗-homomorphism between C*-algebras is isometric, and `γ_𝒜⁻¹`
carries projections to projections.

(The spectral Riemann sum `mem_closure_span_spectral` above proves the same
conclusion for an *arbitrary* von Neumann algebra, with no appeal to
commutativity; that is what the *relativised* **65IV** below is read off,
since a von Neumann subalgebra need not be commutative.  **65IV** itself is
read off this Proposition, as vn.tex:3285 does.) -/
theorem abelian_projections_norm_dense {C : Type*} [CommCStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] [VonNeumannAlgebra C] (a : C) :
    a ∈ closure (Submodule.span ℂ {p : C | IsStarProjection p} : Set C) := by
  have : ExtremallyDisconnected (characterSpace ℂ C) :=
    vn_spectrum_extremally_disconnected C
  set γ : C ≃⋆ₐ[ℂ] C(characterSpace ℂ C, ℂ) := gelfandStarTransform C with hγ
  have hcont : Continuous (γ.symm : C(characterSpace ℂ C, ℂ) → C) :=
    (NonUnitalStarAlgHom.isometry γ.symm γ.symm.injective).continuous
  set L : C(characterSpace ℂ C, ℂ) →ₗ[ℂ] C :=
    { toFun := γ.symm, map_add' := map_add γ.symm, map_smul' := map_smul γ.symm } with hL
  have hproj : ∀ p : C(characterSpace ℂ C, ℂ), IsStarProjection p →
      IsStarProjection (γ.symm p) := by
    intro p hp
    refine ⟨?_, ?_⟩
    · show γ.symm p * γ.symm p = γ.symm p
      rw [← map_mul, hp.isIdempotentElem.eq]
    · show star (γ.symm p) = γ.symm p
      rw [← map_star, hp.isSelfAdjoint.star_eq]
  have hmap : ∀ x ∈ (Submodule.span ℂ {p : C(characterSpace ℂ C, ℂ) | IsStarProjection p} :
      Set C(characterSpace ℂ C, ℂ)), γ.symm x ∈
        (Submodule.span ℂ {p : C | IsStarProjection p} : Set C) := by
    have hle : Submodule.map L
        (Submodule.span ℂ {p : C(characterSpace ℂ C, ℂ) | IsStarProjection p})
        ≤ Submodule.span ℂ {p : C | IsStarProjection p} := by
      rw [Submodule.map_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨p, hp, rfl⟩
      exact Submodule.subset_span (hproj p hp)
    exact fun x hx => hle ⟨x, hx, rfl⟩
  have h1 := mem_closure_span_projections_continuousMap (γ a)
  have h3 : a ∈ closure ((fun f => (γ.symm f : C)) ''
      (Submodule.span ℂ {p : C(characterSpace ℂ C, ℂ) | IsStarProjection p} :
        Set C(characterSpace ℂ C, ℂ))) := by
    have hgg : (γ.symm (γ a) : C) = a := γ.symm_apply_apply a
    exact hgg ▸ image_closure_subset_closure_image hcont ⟨γ a, h1, rfl⟩
  refine closure_mono ?_ h3
  rintro _ ⟨x, hx, rfl⟩
  exact hmap x hx

end AbelianStone

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

/-! `continuous_ultraweak_conj` — the polarisation lemma that used to be
proved privately here — now lives in `Theses/A/VN/Basic.lean`, where **45IV**
`mult_uws_cont` needs it too; it is stated there in exactly this form
(`a ↦ ω(u a v)` is ultraweakly continuous) and proved from **44II**
`mult_polarization`. -/

/-- **65III** (`commutant-basic`, vn.tex:3222, Exercise), part 2: `S^□` is
closed under addition and (scalar) multiplication, contains `1`, and is
ultraweakly closed. -/
theorem commutant_basic_2 (S : Set A) :
    (1 : A) ∈ commutant A S ∧
      (∀ a ∈ commutant A S, ∀ b ∈ commutant A S, a + b ∈ commutant A S) ∧
      (∀ a ∈ commutant A S, ∀ b ∈ commutant A S, a * b ∈ commutant A S) ∧
      (∀ (z : ℂ), ∀ a ∈ commutant A S, z • a ∈ commutant A S) ∧
      @IsClosed A (ultraweak A) (commutant A S) := by
  refine ⟨fun s _ => by rw [mul_one, one_mul], fun a ha b hb s hs => by
      rw [mul_add, add_mul, ha s hs, hb s hs],
    fun a ha b hb s hs => by
      rw [← mul_assoc, ha s hs, mul_assoc, hb s hs, mul_assoc],
    fun z a ha s hs => by rw [mul_smul_comm, smul_mul_assoc, ha s hs], ?_⟩
  -- `S□ = ⋂_{s∈S} ⋂_ω {a | ω(sa − as) = 0}` (the np-functionals are
  -- separating), and each `a ↦ ω(sa − as)` is ultraweakly continuous by
  -- polarisation
  letI : TopologicalSpace A := ultraweak A
  have hrepr : commutant A S = ⋂ s : S, ⋂ ω : NPFunctional A,
      (fun a : A => (ω ((s : A) * a - a * (s : A)) : ℂ)) ⁻¹' {0} := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun ha s ω => by rw [ha (s : A) s.2, sub_self, npFunctional_zero],
      fun h s hs => sub_eq_zero.mp
        (np_separating ((s : A) * a - a * (s : A)) fun ω => h ⟨s, hs⟩ ω)⟩
  rw [hrepr]
  refine isClosed_iInter fun s => isClosed_iInter fun ω => ?_
  refine IsClosed.preimage ?_ isClosed_singleton
  have h1 := continuous_ultraweak_conj ω (s : A) 1
  have h2 := continuous_ultraweak_conj ω 1 (s : A)
  simp only [mul_one, one_mul] at h1 h2
  have heq : (fun a : A => (ω ((s : A) * a - a * (s : A)) : ℂ))
      = fun a : A => (ω ((s : A) * a) : ℂ) - (ω (a * (s : A)) : ℂ) := by
    funext a; rw [npFunctional_sub]
  rw [heq]
  exact h1.sub h2

/-- **65III** (`commutant-basic`, vn.tex:3222, Exercise), part 3
(counterexample): the commutant need not be closed under the involution
(witness `{[[0,1],[0,0]]}^□` in `M₂`). -/
theorem commutant_basic_3 :
    ∃ S : Set (CStarMatrix (Fin 2) (Fin 2) ℂ),
      ¬∀ a ∈ commutant _ S, star a ∈ commutant _ S := by
  -- the thesis's own witness: `S = {e₁₂}`.  `e₁₂` commutes with itself, but
  -- `e₁₂ e₁₂* = diag(1,0) ≠ diag(0,1) = e₁₂* e₁₂`.
  classical
  set e : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix !![0, 1; 0, 0] with he
  refine ⟨{e}, fun h => ?_⟩
  have hmem : e ∈ commutant (CStarMatrix (Fin 2) (Fin 2) ℂ) {e} := by
    intro m hm
    rw [Set.mem_singleton_iff] at hm
    subst hm; rfl
  have h2 := h e hmem e (Set.mem_singleton e)
  have h3 : (e * star e) 0 0 = (star e * e) 0 0 := by rw [h2]
  rw [CStarMatrix.mul_apply, CStarMatrix.mul_apply] at h3
  simp [he, CStarMatrix.star_apply, Fin.sum_univ_two] at h3

/-- **65III** (`commutant-basic`, vn.tex:3222, Exercise), part 3 (main): if
`S` is closed under the involution, then `S^□` is a von Neumann subalgebra
of `A`; in particular so are `Z(A)` and `S^□□` (which contains `S`), and
`S^□□` is commutative when `S` is. -/
theorem commutant_basic_3' (S : Set A) (hS : ∀ s ∈ S, star s ∈ S) :
    (∃ T : StarSubalgebra ℂ A, IsVNSubalgebra A T ∧
        (T : Set A) = commutant A S) ∧
      (S ⊆ commutant A S →
        ∀ a ∈ commutant A (commutant A S), ∀ b ∈ commutant A (commutant A S),
          a * b = b * a) := by
  -- `S□` is a star-subalgebra because `S` is star-closed; it is *norm* closed
  -- because `a ↦ sa − as` is norm continuous, and it contains the suprema of
  -- its bounded directed sets by **44XIII** (`vna-supremum-commutes`).
  have hstar : ∀ {a : A}, a ∈ Subalgebra.centralizer ℂ S →
      star a ∈ Subalgebra.centralizer ℂ S := by
    intro a ha m hm
    have h1 := congrArg star (ha (star m) (hS m hm))
    rw [star_mul, star_mul, star_star] at h1
    exact h1.symm
  refine ⟨⟨⟨Subalgebra.centralizer ℂ S, hstar⟩, ⟨?_, ?_⟩, rfl⟩, ?_⟩
  · show IsClosed (Set.centralizer S : Set A)
    have hrepr : (Set.centralizer S : Set A)
        = ⋂ m : S, {a : A | (m : A) * a = a * (m : A)} := by
      ext a
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      exact ⟨fun ha m => ha m m.2, fun h m hm => h ⟨m, hm⟩⟩
    rw [hrepr]
    exact isClosed_iInter fun m =>
      isClosed_eq (continuous_const.mul continuous_id)
        (continuous_id.mul continuous_const)
  · intro D t hDT hne hdir hlub m hm
    have h3 : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, ⟨t, hlub.1⟩⟩
    have ht : dirSup D h3 = t := (isLUB_dirSup D h3).unique hlub
    have hcomm := vna_supremum_commutes D h3 m fun d hd => hDT d hd m hm
    rwa [ht] at hcomm
  · exact fun hSS a ha b hb => (ha b (Set.centralizer_subset hSS hb)).symm

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

section CommutativeSubalgebra

/-! ### A von Neumann subalgebra bundled as a von Neumann algebra

The thesis proves **65IV** by applying **64II**
`abelian-projections-norm-dense` to the commutative von Neumann subalgebra
`{a}^□□` of **65III** (`commutant-basic`, vn.tex:3221), which vn.tex:3285
invokes.  64II is stated for a commutative von
Neumann algebra as a *type*, so the subalgebra has to be bundled as one.
Mathlib supplies the C\*-structure of a closed `StarSubalgebra`
(`StarSubalgebra.cstarAlgebra`); what is added here is the spectral order
and the two clauses of **42I** `vna`.  The witness `IsVNSubalgebra A S` is
carried as a `Fact` so that the pieces can be `local instance`s.  (The same
bundling as a structure, `VNSub`, is built in `A/VN/Division` for the
*relative* comparison theory — three files downstream of this one, which is
why it is not reused here.) -/


variable {S : StarSubalgebra ℂ A} [hSf : Fact (IsVNSubalgebra A S)]

local instance instIsClosedSub : IsClosed (S : Set A) := hSf.out.isClosed

omit [VonNeumannAlgebra A] in
/-- The square root of a positive element of a closed star subalgebra again
lies in it (Mathlib's `cfcₙ_mem`). -/
private theorem sqrtSub_mem {a : A} (ha : 0 ≤ a) (hmem : a ∈ S) : CFC.sqrt a ∈ S := by
  rw [CFC.sqrt_eq_real_sqrt a ha]
  exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ) Real.sqrt hmem

/-- The order of `S` is that of `A`, and it is the C\*-order: the positives
are the `s* s` for `s ∈ S` (take `s = √x`, which stays in `S`). -/
noncomputable local instance instStarOrderedSub : StarOrderedRing ↥S := by
  refine StarOrderedRing.of_nonneg_iff' (fun {x y} hxy z => ?_) (fun x => ?_)
  · exact show ((z : A) + (x : A)) ≤ ((z : A) + (y : A)) from
      add_le_add le_rfl (show (x : A) ≤ (y : A) from hxy)
  · constructor
    · intro hx
      have hx' : (0 : A) ≤ (x : A) := hx
      refine ⟨⟨CFC.sqrt (x : A), sqrtSub_mem hx' x.2⟩, ?_⟩
      refine Subtype.ext ?_
      have hsa : IsSelfAdjoint (CFC.sqrt (x : A)) :=
        IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (x : A))
      show (x : A) = star (CFC.sqrt (x : A)) * CFC.sqrt (x : A)
      rw [hsa.star_eq, CFC.sqrt_mul_sqrt_self (x : A) hx']
    · rintro ⟨s, rfl⟩
      exact show (0 : A) ≤ star (s : A) * (s : A) from star_mul_self_nonneg (s : A)

/-- A self-adjoint element of `S`, viewed in `A`. -/
private def saValSub (d : selfAdjoint ↥S) : selfAdjoint A :=
  ⟨(d.1 : A), Subtype.ext_iff.mp d.2⟩

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] hSf in
@[simp] private theorem saValSub_coe (d : selfAdjoint ↥S) :
    ((saValSub d : selfAdjoint A) : A) = (d.1 : A) := rfl

omit [StarOrderedRing A] in
private theorem isLUB_saValSub {D : Set (selfAdjoint ↥S)} {s : selfAdjoint ↥S}
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hlub : IsLUB D s) :
    IsLUB (saValSub '' D) (saValSub s) := by
  have hne' : (saValSub '' D).Nonempty := hne.image _
  have hdir' : DirectedOn (· ≤ ·) (saValSub (S := S) '' D) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    obtain ⟨u, hu, hxu, hzu⟩ := hdir x hx z hz
    exact ⟨saValSub u, ⟨u, hu, rfl⟩, hxu, hzu⟩
  have hbdd' : BddAbove (saValSub (S := S) '' D) := by
    refine ⟨saValSub s, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hlub.1 hx
  obtain ⟨s₀, hs₀⟩ :=
    VonNeumannAlgebra.isLUB_of_bddAbove_directed _ hne' hdir' hbdd'
  have hmem : (s₀ : A) ∈ S :=
    hSf.out.dirSup_mem _ s₀ (by rintro _ ⟨x, hx, rfl⟩; exact x.1.2) hne' hdir' hs₀
  have htsa : IsSelfAdjoint (⟨(s₀ : A), hmem⟩ : ↥S) := Subtype.ext s₀.2
  have hlubt : IsLUB D ⟨⟨(s₀ : A), hmem⟩, htsa⟩ := by
    refine ⟨fun d hd => hs₀.1 ⟨d, hd, rfl⟩, fun u hu => ?_⟩
    have hub : saValSub u ∈ upperBounds (saValSub (S := S) '' D) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hu hx
    exact hs₀.2 hub
  have hst : s = ⟨⟨(s₀ : A), hmem⟩, htsa⟩ := hlub.unique hlubt
  rw [hst]
  exact hs₀

/-- Restriction of an np-functional to `S`. -/
private noncomputable def restrictNPSub (ω : NPFunctional A) : NPFunctional ↥S where
  toPositiveLinearMap :=
    { toFun := fun a => ω (a : A)
      map_add' := fun x y => map_add ω.toPositiveLinearMap _ _
      map_smul' := fun c x => map_smul ω.toPositiveLinearMap _ _
      monotone' := fun x y hxy => ω.toPositiveLinearMap.monotone hxy }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hkey := ω.preservesDirSups' (saValSub '' D) (saValSub s) (hne.image _)
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
        obtain ⟨u, hu, hxu, hzu⟩ := hdir x hx z hz
        exact ⟨saValSub u, ⟨u, hu, rfl⟩, hxu, hzu⟩)
      (isLUB_saValSub hne hdir hlub)
    rw [← Set.image_comp] at hkey
    exact hkey

omit [StarOrderedRing A] in
@[simp] private theorem restrictNPSub_apply (ω : NPFunctional A) (a : ↥S) :
    (restrictNPSub ω : NPFunctional ↥S) a = ω (a : A) := rfl

/-- **42V** part 4: a von Neumann subalgebra is a von Neumann algebra —
directed suprema are computed in `A` and stay in `S`, and the restrictions
of the np-functionals of `A` are still faithful. -/
local instance instVNSubtype : VonNeumannAlgebra ↥S where
  isLUB_of_bddAbove_directed := by
    intro D hne hdir hbdd
    obtain ⟨u, hu⟩ := hbdd
    have hne' : (saValSub (S := S) '' D).Nonempty := hne.image _
    have hdir' : DirectedOn (· ≤ ·) (saValSub (S := S) '' D) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
      obtain ⟨v, hv, hxv, hzv⟩ := hdir x hx z hz
      exact ⟨saValSub v, ⟨v, hv, rfl⟩, hxv, hzv⟩
    have hbdd' : BddAbove (saValSub (S := S) '' D) := by
      refine ⟨saValSub u, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hu hx
    obtain ⟨s₀, hs₀⟩ :=
      VonNeumannAlgebra.isLUB_of_bddAbove_directed _ hne' hdir' hbdd'
    have hmem : (s₀ : A) ∈ S :=
      hSf.out.dirSup_mem _ s₀ (by rintro _ ⟨x, hx, rfl⟩; exact x.1.2) hne' hdir' hs₀
    refine ⟨⟨⟨(s₀ : A), hmem⟩, Subtype.ext s₀.2⟩, fun d hd => hs₀.1 ⟨d, hd, rfl⟩,
      fun v hv => ?_⟩
    have hub : saValSub v ∈ upperBounds (saValSub (S := S) '' D) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hv hx
    exact hs₀.2 hub
  np_faithful := by
    intro a ha hω
    refine Subtype.ext ?_
    exact VonNeumannAlgebra.np_faithful (a : A) ha
      (fun ω => by simpa using hω (restrictNPSub ω))

/-- **64II** `abelian-projections-norm-dense` transported to a *commutative*
von Neumann subalgebra `S` of `A`. -/
private theorem abelian_projections_norm_dense_sub
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {a : A} (haS : a ∈ S) :
    a ∈ closure (Submodule.span ℂ {p : A | IsStarProjection p ∧ p ∈ S} : Set A) := by
  letI : CommCStarAlgebra ↥S :=
    { (inferInstance : CStarAlgebra ↥S) with
      mul_comm := fun x y => Subtype.ext (hcomm (x : A) x.2 (y : A) y.2) }
  have h64 := abelian_projections_norm_dense (⟨a, haS⟩ : ↥S)
  set L : ↥S →ₗ[ℂ] A :=
    { toFun := fun x => (x : A), map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl } with hL
  have hmap : ∀ x ∈ (Submodule.span ℂ {p : ↥S | IsStarProjection p} : Set ↥S),
      (x : A) ∈ (Submodule.span ℂ {p : A | IsStarProjection p ∧ p ∈ S} : Set A) := by
    have hle : Submodule.map L (Submodule.span ℂ {p : ↥S | IsStarProjection p})
        ≤ Submodule.span ℂ {p : A | IsStarProjection p ∧ p ∈ S} := by
      rw [Submodule.map_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨p, hp, rfl⟩
      exact Submodule.subset_span
        ⟨⟨congrArg Subtype.val hp.isIdempotentElem,
          congrArg Subtype.val hp.isSelfAdjoint⟩, p.2⟩
    exact fun x hx => hle ⟨x, hx, rfl⟩
  have h3 : a ∈ closure ((fun x : ↥S => (x : A)) ''
      (Submodule.span ℂ {p : ↥S | IsStarProjection p} : Set ↥S)) :=
    image_closure_subset_closure_image continuous_subtype_val ⟨⟨a, haS⟩, h64, rfl⟩
  refine closure_mono ?_ h3
  rintro _ ⟨x, hx, rfl⟩
  exact hmap x hx

end CommutativeSubalgebra

/-- **65IV** (`projections-norm-dense`, vn.tex:3279, Proposition): every
self-adjoint element `a` of a von Neumann algebra is the norm limit of
linear combinations of projections from `{a}^□□`.

This is the thesis's own proof (vn.tex:3285): `{a}^□□` is by **65III**
`commutant-basic` a *commutative* von Neumann subalgebra of `A` containing
`a`, so **64II** `abelian_projections_norm_dense` — applied to it through
the bundling above — puts `a` in the closed span of its projections. -/
theorem projections_norm_dense (a : A) (ha : IsSelfAdjoint a) :
    a ∈ closure (Submodule.span ℂ
      {p : A | IsStarProjection p ∧ p ∈ commutant A (commutant A {a})} :
        Set A) := by
  have hstar1 : ∀ s ∈ ({a} : Set A), star s ∈ ({a} : Set A) := by
    rintro s rfl
    exact ha.star_eq
  obtain ⟨⟨T₁, hT₁vn, hT₁⟩, hcomm⟩ := commutant_basic_3' ({a} : Set A) hstar1
  have hstar2 : ∀ s ∈ commutant A ({a} : Set A), star s ∈ commutant A ({a} : Set A) := by
    intro s hs
    rw [← hT₁] at hs ⊢
    exact star_mem hs
  obtain ⟨⟨T₂, hT₂vn, hT₂⟩, -⟩ := commutant_basic_3' (commutant A ({a} : Set A)) hstar2
  haveI : Fact (IsVNSubalgebra A T₂) := ⟨hT₂vn⟩
  have hself : ({a} : Set A) ⊆ commutant A ({a} : Set A) := by
    rintro s rfl t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
  have haT₂ : a ∈ T₂ := by
    rw [← SetLike.mem_coe, hT₂]
    exact (commutant_basic_1 ({a} : Set A) (∅ : Set A)).2.2.1 rfl
  have hcomm₂ : ∀ x ∈ T₂, ∀ y ∈ T₂, x * y = y * x := by
    intro x hx y hy
    rw [← SetLike.mem_coe, hT₂] at hx hy
    exact hcomm hself x hx y hy
  have hres := abelian_projections_norm_dense_sub (S := T₂) hcomm₂ haT₂
  have hset : {p : A | IsStarProjection p ∧ p ∈ T₂}
      = {p : A | IsStarProjection p ∧ p ∈ commutant A (commutant A {a})} := by
    ext p
    simp only [Set.mem_setOf_eq, ← SetLike.mem_coe, hT₂]
  rwa [hset] at hres

/-- **65IV** relativised to a von Neumann *subalgebra*, self-adjoint case:
every self-adjoint element of a von Neumann subalgebra `S` of `A` is the
norm limit of linear combinations of projections **of `S`**.

The thesis states 65IV only for a von Neumann algebra, and the relative form
does not follow from it in our setting: 65IV places the projections in
`{a}^□□`, and `{a}^□□ ⊆ S` is the double commutant theorem **88VI**, which is
proved (`A/VN/NormalFunctionals`'s `double_commutant`) but only for `B(H)`,
not for a von Neumann subalgebra of an abstract `A`.  (The earlier note that
88VI was "still `sorry`" was stale.)  It does, however, come out of the same
spectral Riemann sum, because a von Neumann subalgebra is closed under `cfc`
and under `⌈·⌉` (`ceil_mem`). -/
theorem projections_norm_dense_subalgebra_selfAdjoint {S : StarSubalgebra ℂ A}
    (hS : IsVNSubalgebra A S) (a : A) (ha : IsSelfAdjoint a) (haS : a ∈ S) :
    a ∈ closure (Submodule.span ℂ {p : A | IsStarProjection p ∧ p ∈ S} : Set A) := by
  refine closure_mono (SetLike.coe_subset_coe.mpr (Submodule.span_mono ?_))
    (mem_closure_span_spectral a ha)
  rintro p ⟨h1, -, h3⟩
  exact ⟨h1, h3 S hS haS⟩

/-- **65IV** relativised to a von Neumann *subalgebra*: **the linear span of
the projections of `S` is norm-dense in `S`** (`a = ℜa + i·ℑa`). -/
theorem projections_norm_dense_subalgebra {S : StarSubalgebra ℂ A}
    (hS : IsVNSubalgebra A S) (a : A) (haS : a ∈ S) :
    a ∈ closure (Submodule.span ℂ {p : A | IsStarProjection p ∧ p ∈ S} : Set A) := by
  have hre : (realPart a : A) ∈ S := by
    rw [realPart_apply_coe]
    exact real_smul_mem _ (add_mem haS (star_mem haS))
  have him : (imaginaryPart a : A) ∈ S := by
    rw [imaginaryPart_apply_coe]
    exact SMulMemClass.smul_mem _ (real_smul_mem _ (sub_mem haS (star_mem haS)))
  have hx : (realPart a : A) + Complex.I • (imaginaryPart a : A) = a :=
    realPart_add_I_smul_imaginaryPart a
  have hmem : a ∈ Submodule.topologicalClosure
      (Submodule.span ℂ {p : A | IsStarProjection p ∧ p ∈ S}) := by
    rw [← hx]
    exact Submodule.add_mem _
      (projections_norm_dense_subalgebra_selfAdjoint hS _ (realPart a).2 hre)
      (Submodule.smul_mem _ _
        (projections_norm_dense_subalgebra_selfAdjoint hS _ (imaginaryPart a).2 him))
  exact hmem

/-- **65IV** relativised, in the form its consumers use: a norm-closed
`ℂ`-subspace of `A` containing every projection of a von Neumann subalgebra
`S` contains all of `S`. -/
theorem mem_of_isClosed_of_projections_subalgebra {S : StarSubalgebra ℂ A}
    (hS : IsVNSubalgebra A S) (V : Submodule ℂ A) (hV : IsClosed (V : Set A))
    (hp : ∀ p : A, IsStarProjection p → p ∈ S → p ∈ V) {a : A} (haS : a ∈ S) :
    a ∈ V := by
  have hspan : Submodule.span ℂ {p : A | IsStarProjection p ∧ p ∈ S} ≤ V :=
    Submodule.span_le.mpr fun p hpp => hp p hpp.1 hpp.2
  have hmem : a ∈ closure (V : Set A) :=
    closure_mono (SetLike.coe_subset_coe.mpr hspan)
      (projections_norm_dense_subalgebra hS a haS)
  rwa [hV.closure_eq] at hmem

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
    (hq : Ultracyclic A q) : Ultracyclic A (projSup {p, q}) := by
  -- `⌈ω⌉ ∪ ⌈τ⌉ = ⌈ω + τ⌉` is **63II**.2 `carrier_basic_2`.
  obtain ⟨ω, rfl⟩ := hp
  obtain ⟨τ, rfl⟩ := hq
  exact ⟨addNP ω τ, (carrier_basic_2 _ _ _ ω.preservesDirSups' τ.preservesDirSups'
    (addNP ω τ).preservesDirSups' fun _ => rfl).symm⟩

/-- **66IV** (`ultracyclic-basic`, vn.tex:3334, Exercise), part 2: a
projection below an ultracyclic projection is ultracyclic. -/
theorem ultracyclic_basic_2 (p q : A) (hp : IsStarProjection p)
    (hq : Ultracyclic A q) (hpq : p ≤ q) : Ultracyclic A p := by
  -- `p = ⌈ω(p(·)p)⌉` for `q = ⌈ω⌉`: the compression kills `p^⊥`, and if
  -- `ω(p r^⊥ p) = 0` for a projection `r` then `ω(⌈p r^⊥ p⌉) = 0` (**60I**),
  -- so `⌈ω⌉ ≤ ⌈p r^⊥ p⌉^⊥`; as `⌈p r^⊥ p⌉ ≤ p ≤ ⌈ω⌉` this forces
  -- `⌈p r^⊥ p⌉ ≤ its own complement`, i.e. `p r^⊥ p = 0`, i.e. `p ≤ r`.
  obtain ⟨ω, rfl⟩ := hq
  refine ⟨conjNP p ω, ?_⟩
  refine (carrier_eq _ _ hp ?_ ?_).symm
  · -- `ω(p p^⊥ p) = ω 0 = 0`
    show ((conjNP p ω) (1 - p) : ℂ) = 0
    rw [conjNP_apply, hp.isSelfAdjoint.star_eq,
      show p * (1 - p) * p = 0 from by
        rw [mul_sub, mul_one, hp.isIdempotentElem.eq, sub_self, zero_mul]]
    exact npFunctional_zero _
  · intro r hr hr0
    -- `ω(p r^⊥ p) = 0`, so `ω(⌈p r^⊥ p⌉) = 0`
    replace hr0 : ((conjNP p ω) (1 - r) : ℂ) = 0 := hr0
    rw [conjNP_apply, hp.isSelfAdjoint.star_eq] at hr0
    have hnn : (0 : A) ≤ p * (1 - r) * p :=
      IsSelfAdjoint.conjugate_nonneg hr.one_sub.nonneg hp.isSelfAdjoint
    set c : A := ceil (p * (1 - r) * p) with hc
    have hcproj : IsStarProjection c := (ceil_spec hnn).1
    have hcω : ω c = 0 := (ceil_functionals_lemma _ hnn ω).mp hr0
    -- hence `⌈ω⌉ ≤ 1 - c`
    have hle1c : npCarrier ω ≤ 1 - c := by
      refine (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').2.2 _
        hcproj.one_sub ?_
      show (ω.toPositiveLinearMap (1 - (1 - c)) : ℂ) = 0
      rw [sub_sub_cancel]
      exact hcω
    -- but `c ≤ p ≤ ⌈ω⌉`, so `c ≤ 1 - c`, forcing `c = 0`
    have hcp : c ≤ p := (ceil_le_iff hnn hp).mpr (by
      rw [mul_assoc, hp.isIdempotentElem.eq])
    have hc0 : c = 0 := by
      have h0 : c ≤ 1 - c := le_trans hcp (le_trans hpq hle1c)
      have h1 : c * c * c ≤ c * (1 - c) * c :=
        IsSelfAdjoint.conjugate_le_conjugate h0 hcproj.isSelfAdjoint
      rw [hcproj.isIdempotentElem.eq, hcproj.isIdempotentElem.eq,
        show c * (1 - c) * c = 0 from by
          rw [mul_sub, mul_one, hcproj.isIdempotentElem.eq, sub_self, zero_mul]] at h1
      exact le_antisymm h1 hcproj.nonneg
    have hzero0 : p * (1 - r) * p = 0 := (ceil_basic_3 _ hnn).mpr hc0
    -- `p r^⊥ = 0`, i.e. `p ≤ r`
    have hzero : ((1 : A) - r) * p = 0 := by
      refine (CStarRing.star_mul_self_eq_zero_iff _).mp ?_
      rw [star_mul, hp.isSelfAdjoint.star_eq, hr.one_sub.isSelfAdjoint.star_eq]
      calc p * (1 - r) * ((1 - r) * p) = p * ((1 - r) * (1 - r)) * p := by noncomm_ring
        _ = p * (1 - r) * p := by rw [hr.one_sub.isIdempotentElem.eq]
        _ = 0 := hzero0
    have hrp : r * p = p := by
      rw [sub_mul, one_mul] at hzero
      exact (sub_eq_zero.mp hzero).symm
    have hpr : p * r = p := by
      have h := congrArg star hrp
      rwa [star_mul, hr.isSelfAdjoint.star_eq, hp.isSelfAdjoint.star_eq] at h
    calc p = r * p * r := by rw [hrp, hpr]
      _ ≤ r * 1 * r := IsSelfAdjoint.conjugate_le_conjugate hp.le_one hr.isSelfAdjoint
      _ = r := by rw [mul_one, hr.isIdempotentElem.eq]

/-- **66IV** (`ultracyclic-basic`, vn.tex:3334, Exercise), part 3, the "in
fact" equation: `p = ⋁_ω ⌈ω⌉` over the np-functionals `ω` with `ω(p^⊥) = 0`,
with the supremum read as the join in the poset of projections.  That this
join is a *directed* supremum — the point's first claim — is
`ultracyclic_basic_3_directed` below.

*Class 2 — different route.*  The thesis's hint is "first consider `p = 1`";
we do not need the reduction.  That `p` is an upper bound is the defining
leastness of `⌈ω⌉`.  For leastness, let `r` be a projection above every such
`⌈ω⌉`.  For an arbitrary np-functional `τ`, the compression
`ω = τ(p(·)p) = conjNP p τ` satisfies `ω(p^⊥) = 0`, so `⌈ω⌉ ≤ r` and hence
`ω(r^⊥) = 0`, i.e. `τ(p r^⊥ p) = 0`.  As `τ` was arbitrary and `p r^⊥ p ≥ 0`,
faithfulness of the np-functionals (**42I**.2) gives `p r^⊥ p = 0`, whence
`r^⊥ p = 0` by the C\*-identity and `p = r p r ≤ r`.

The `p = 1` case of the thesis's hint is the special case `p = 1`, where the
compression is the identity. -/
theorem ultracyclic_basic_3 (p : A) (hp : IsStarProjection p) :
    p = projSup {q : A | ∃ ω : NPFunctional A, ω (1 - p) = 0 ∧
      q = npCarrier ω} := by
  set P : Set A := {q : A | ∃ ω : NPFunctional A, ω (1 - p) = 0 ∧
    q = npCarrier ω} with hPdef
  have hPproj : ∀ q ∈ P, IsStarProjection q := by
    rintro q ⟨ω, -, rfl⟩
    exact (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').1
  refine (projSup_eq hPproj hp ?_ ?_).symm
  · rintro q ⟨ω, hω, rfl⟩
    exact (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').2.2 p hp hω
  · intro r hr hub
    have hkey : p * (1 - r) * p = 0 := by
      refine VonNeumannAlgebra.np_faithful _
        (IsSelfAdjoint.conjugate_nonneg hr.one_sub.nonneg hp.isSelfAdjoint) fun τ => ?_
      have hω0 : conjNP p τ (1 - p) = 0 := by
        rw [conjNP_apply, hp.isSelfAdjoint.star_eq,
          show p * (1 - p) * p = 0 from by
            rw [mul_sub, mul_one, hp.isIdempotentElem.eq, sub_self, zero_mul]]
        exact npFunctional_zero _
      have hle : npCarrier (conjNP p τ) ≤ r := hub _ ⟨conjNP p τ, hω0, rfl⟩
      have h1 : (conjNP p τ (1 - r) : ℂ) ≤ conjNP p τ (1 - npCarrier (conjNP p τ)) :=
        npFunctional_mono _ (sub_le_sub_left hle 1)
      have hc : conjNP p τ (1 - npCarrier (conjNP p τ)) = 0 :=
        (carrier_spec (conjNP p τ).toPositiveLinearMap
          (conjNP p τ).preservesDirSups').2.1
      rw [hc] at h1
      have h2 : (0 : ℂ) ≤ conjNP p τ (1 - r) :=
        npFunctional_nonneg _ hr.one_sub.nonneg
      have h3 : conjNP p τ (1 - r) = 0 := le_antisymm h1 h2
      rwa [conjNP_apply, hp.isSelfAdjoint.star_eq] at h3
    have hzero : (1 - r) * p = 0 := by
      refine (CStarRing.star_mul_self_eq_zero_iff _).mp ?_
      rw [star_mul, hp.isSelfAdjoint.star_eq, hr.one_sub.isSelfAdjoint.star_eq]
      calc p * (1 - r) * ((1 - r) * p) = p * ((1 - r) * (1 - r)) * p := by noncomm_ring
        _ = p * (1 - r) * p := by rw [hr.one_sub.isIdempotentElem.eq]
        _ = 0 := hkey
    have hrp : r * p = p := by
      rw [sub_mul, one_mul] at hzero
      exact (sub_eq_zero.mp hzero).symm
    have hpr : p * r = p := by
      have h := congrArg star hrp
      rwa [star_mul, hr.isSelfAdjoint.star_eq, hp.isSelfAdjoint.star_eq] at h
    calc p = r * p * r := by rw [hrp, hpr]
      _ ≤ r * 1 * r := IsSelfAdjoint.conjugate_le_conjugate hp.le_one hr.isSelfAdjoint
      _ = r := by rw [mul_one, hr.isIdempotentElem.eq]

/-- **66IV** (`ultracyclic-basic`, vn.tex:3334, Exercise), part 3, **first
claim**: every projection `p` is a *directed* supremum of ultracyclic
projections.

`ultracyclic_basic_3` gives the point's "in fact" equation, with the
supremum read as the join in the poset of projections; this is what makes
that join a genuine supremum *in `A`*.  The family
`P = {⌈ω⌉ : ω(p^⊥) = 0}` consists of ultracyclic projections below `p`, is
nonempty (`ω = 0`), and is directed: for `ω, τ ∈ P` the sum `ω + τ` again
kills `p^⊥`, and `⌈ω + τ⌉ = ⌈ω⌉ ∪ ⌈τ⌉` by **63II**.2 (`carrier_basic_2`) —
which is exactly the ingredient part 1 uses.  Being directed, `P` has by
**56XIV** the same supremum in `A` as in the poset of projections, so
`IsLUB P p`. -/
theorem ultracyclic_basic_3_directed (p : A) (hp : IsStarProjection p) :
    (∀ q ∈ {q : A | ∃ ω : NPFunctional A, ω (1 - p) = 0 ∧ q = npCarrier ω},
        Ultracyclic A q ∧ q ≤ p) ∧
      {q : A | ∃ ω : NPFunctional A, ω (1 - p) = 0 ∧ q = npCarrier ω}.Nonempty ∧
      DirectedOn (· ≤ ·)
        {q : A | ∃ ω : NPFunctional A, ω (1 - p) = 0 ∧ q = npCarrier ω} ∧
      IsLUB {q : A | ∃ ω : NPFunctional A, ω (1 - p) = 0 ∧ q = npCarrier ω} p := by
  set P : Set A := {q : A | ∃ ω : NPFunctional A, ω (1 - p) = 0 ∧ q = npCarrier ω}
    with hPdef
  have hPproj : ∀ q ∈ P, IsStarProjection q := by
    rintro q ⟨ω, -, rfl⟩
    exact (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').1
  have hmem : ∀ q ∈ P, Ultracyclic A q ∧ q ≤ p := by
    rintro q ⟨ω, hω, rfl⟩
    exact ⟨⟨ω, rfl⟩,
      (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').2.2 p hp hω⟩
  have hne : P.Nonempty :=
    ⟨npCarrier (zeroNP : NPFunctional A), ⟨zeroNP, rfl, rfl⟩⟩
  have hdir : DirectedOn (· ≤ ·) P := by
    rintro _ ⟨ω, hω, rfl⟩ _ ⟨τ, hτ, rfl⟩
    have hzero : (addNP ω τ) (1 - p) = 0 := by
      show (ω (1 - p) : ℂ) + τ (1 - p) = 0
      rw [hω, hτ, add_zero]
    have hjoin : npCarrier (addNP ω τ) = projSup {npCarrier ω, npCarrier τ} :=
      carrier_basic_2 _ _ _ ω.preservesDirSups' τ.preservesDirSups'
        (addNP ω τ).preservesDirSups' fun _ => rfl
    have hP2 : ∀ r ∈ ({npCarrier ω, npCarrier τ} : Set A), IsStarProjection r := by
      rintro r (rfl | rfl)
      exacts [(carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').1,
        (carrier_spec τ.toPositiveLinearMap τ.preservesDirSups').1]
    obtain ⟨-, hub, -⟩ := projSup_spec hP2
    exact ⟨npCarrier (addNP ω τ), ⟨addNP ω τ, hzero, rfl⟩,
      hjoin ▸ hub _ (by left; rfl), hjoin ▸ hub _ (by right; rfl)⟩
  refine ⟨hmem, hne, hdir, ?_⟩
  have hlub := isLUB_projSup_of_directed P hPproj hne hdir
  rwa [← ultracyclic_basic_3 p hp] at hlub

/-- **66IV** (`ultracyclic-basic`, vn.tex:3334, Exercise), part 4: every
projection is the sum of a family of pairwise orthogonal ultracyclic
projections.

The argument is Zorn's lemma over the sets of np-functionals whose carriers
lie below `p` and are pairwise orthogonal (the same shape as **83V**
`cceil_sum`).  For a maximal such set `S` put `q = ⋁_{ω ∈ S} ⌈ω⌉ ≤ p`; if
`q ≠ p` then `r = p - q` is a non-zero projection, so by faithfulness of the
np-functionals (**42I**.2) some `τ` has `τ(r) ≠ 0`, and `ω = τ(r(·)r)`
satisfies `0 ≠ ⌈ω⌉ ≤ r`, which is orthogonal to `q` — contradicting
maximality. -/
theorem ultracyclic_basic_4 (p : A) (hp : IsStarProjection p) :
    ∃ (ι : Type u) (ω : ι → NPFunctional A),
      (Pairwise fun i j => npCarrier (ω i) * npCarrier (ω j) = 0) ∧
        p = projSup (Set.range fun i => npCarrier (ω i)) := by
  classical
  set T : Set (Set (NPFunctional A)) :=
    {S | (∀ ω ∈ S, npCarrier ω ≤ p) ∧
      ∀ ω ∈ S, ∀ τ ∈ S, ω ≠ τ → npCarrier ω * npCarrier τ = 0} with hT
  obtain ⟨S, hSmax⟩ : ∃ S, Maximal (· ∈ T) S := by
    refine zorn_subset T fun c hc hchain =>
      ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro ω ⟨s, hs, hωs⟩
      exact (hc hs).1 ω hωs
    · rintro ω ⟨s, hs, hωs⟩ τ ⟨s', hs', hτs'⟩ hne
      rcases hchain.total hs hs' with hsub | hsub
      · exact (hc hs').2 ω (hsub hωs) τ hτs' hne
      · exact (hc hs).2 ω hωs τ (hsub hτs') hne
  refine ⟨↥S, Subtype.val,
    fun i j hij => hSmax.1.2 i.1 i.2 j.1 j.2 fun h => hij (Subtype.ext h), ?_⟩
  set Q : Set A := Set.range fun i : ↥S => npCarrier (i : NPFunctional A) with hQ
  have hcarrierproj : ∀ ω : NPFunctional A, IsStarProjection (npCarrier ω) :=
    fun ω => (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').1
  have hQproj : ∀ x ∈ Q, IsStarProjection x := by
    rintro _ ⟨i, rfl⟩; exact hcarrierproj _
  obtain ⟨hqproj, hqub, hqleast⟩ := projSup_spec hQproj
  have hqle : projSup Q ≤ p := by
    refine hqleast p hp ?_
    rintro _ ⟨i, rfl⟩
    exact hSmax.1.1 i.1 i.2
  refine le_antisymm ?_ hqle
  by_contra hlt
  obtain ⟨r, hrdef⟩ : ∃ r : A, r = p - projSup Q := ⟨_, rfl⟩
  have hrproj : IsStarProjection r := by
    rw [hrdef]; exact projection_below_projection _ _ hqproj hp hqle
  have hrne : r ≠ 0 := by
    intro h
    rw [hrdef, sub_eq_zero] at h
    exact hlt h.le
  have hrp : r ≤ p := by
    rw [hrdef, sub_le_self_iff]
    exact hqproj.nonneg
  have hpq : p * projSup Q = projSup Q :=
    ((projection_below_effect p (projSup Q) ⟨hp.nonneg, hp.le_one⟩ hqproj).out 0 6).mp hqle
  have hrq : r * projSup Q = 0 := by
    rw [hrdef, sub_mul, hpq, hqproj.isIdempotentElem.eq, sub_self]
  -- some np-functional does not kill `r`
  obtain ⟨τ, hτ⟩ : ∃ τ : NPFunctional A, τ r ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hrne (VonNeumannAlgebra.np_faithful r hrproj.nonneg hcon)
  obtain ⟨ω, hωdef⟩ : ∃ ω : NPFunctional A, ω = conjNP r τ := ⟨_, rfl⟩
  have hrort : r * ((1 : A) - r) * r = 0 := by
    rw [mul_sub, mul_one, hrproj.isIdempotentElem.eq, sub_self, zero_mul]
  have hω1 : (ω 1 : ℂ) = τ r := by
    rw [hωdef, conjNP_apply, hrproj.isSelfAdjoint.star_eq, mul_one,
      hrproj.isIdempotentElem.eq]
  have hcle : npCarrier ω ≤ r := by
    refine (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').2.2 r hrproj ?_
    show ((ω : A → ℂ) (1 - r)) = 0
    rw [hωdef, conjNP_apply, hrproj.isSelfAdjoint.star_eq, hrort]
    exact npFunctional_zero _
  have hcne : npCarrier ω ≠ 0 := by
    intro h
    have h0 := (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').2.1
    change ((ω : A → ℂ) (1 - npCarrier ω)) = 0 at h0
    rw [h, sub_zero, hω1] at h0
    exact hτ h0
  have hcr : npCarrier ω * r = npCarrier ω :=
    ((projection_below_effect r (npCarrier ω) ⟨hrproj.nonneg, hrproj.le_one⟩
      (hcarrierproj ω)).out 0 7).mp hcle
  -- `⌈ω⌉` is orthogonal to every `⌈τ'⌉`, `τ' ∈ S`
  have horth : ∀ τ' ∈ S, npCarrier ω * npCarrier τ' = 0 := by
    intro τ' hτ'
    have hle : npCarrier τ' ≤ projSup Q := hqub _ ⟨⟨τ', hτ'⟩, rfl⟩
    have hmul : projSup Q * npCarrier τ' = npCarrier τ' :=
      ((projection_below_effect (projSup Q) (npCarrier τ')
        ⟨hqproj.nonneg, hqproj.le_one⟩ (hcarrierproj τ')).out 0 6).mp hle
    calc npCarrier ω * npCarrier τ'
        = (npCarrier ω * r) * (projSup Q * npCarrier τ') := by rw [hcr, hmul]
      _ = npCarrier ω * (r * projSup Q) * npCarrier τ' := by noncomm_ring
      _ = 0 := by rw [hrq, mul_zero, zero_mul]
  have hins : insert ω S ∈ T := by
    constructor
    · intro ν hν
      rcases Set.mem_insert_iff.mp hν with hν | hν
      · rw [hν]; exact hcle.trans hrp
      · exact hSmax.1.1 ν hν
    · intro ν hν μ hμ hne
      rcases Set.mem_insert_iff.mp hν with hν | hν <;>
        rcases Set.mem_insert_iff.mp hμ with hμ | hμ
      · exact absurd (hν.trans hμ.symm) hne
      · rw [hν]; exact horth μ hμ
      · rw [hμ]
        have h' := congrArg star (horth ν hν)
        rwa [star_mul, (hcarrierproj ν).isSelfAdjoint.star_eq,
          (hcarrierproj ω).isSelfAdjoint.star_eq, star_zero] at h'
      · exact hSmax.1.2 ν hν μ hμ hne
  have hωS : ω ∈ S := hSmax.2 hins (Set.subset_insert _ _) (Set.mem_insert _ _)
  have hcq : npCarrier ω * projSup Q = npCarrier ω :=
    ((projection_below_effect (projSup Q) (npCarrier ω)
      ⟨hqproj.nonneg, hqproj.le_one⟩ (hcarrierproj ω)).out 0 7).mp
      (hqub _ ⟨⟨ω, hωS⟩, rfl⟩)
  refine hcne ?_
  calc npCarrier ω = npCarrier ω * projSup Q := hcq.symm
    _ = (npCarrier ω * r) * projSup Q := by rw [hcr]
    _ = npCarrier ω * (r * projSup Q) := by noncomm_ring
    _ = 0 := by rw [hrq, mul_zero]

/-! ## Parsec 670: central elements -/

variable (A) in
/-- **67I** (vn.tex:3363, Definition): an element `a` of a von Neumann
algebra is **central** when it commutes with every element (i.e.
`a ∈ Z(A)`). -/
def IsCentral (a : A) : Prop := ∀ b : A, a * b = b * a

/-- **67II** (`central-examples`, vn.tex:3370, Examples), part 3: in `B(H)`
only the scalars are central.  (Parts 1–2 — commutative algebras and direct
sums — are immediate from the definitions and not converted.  **67III**,
Remark: such von Neumann algebras are called *factors*.)

This is the thesis's own computation (vn.tex:3383–3392).  Write `|x⟩⟨y|`
for the rank-one operator `z ↦ ⟪y,z⟫·x`.  If `T` is central then
`T|x⟩⟨y| = |x⟩⟨y|T`, and evaluating both sides at `y` gives the printed
display

    ‖y‖²·T x  =  (T |x⟩⟨y|) y  =  (|x⟩⟨y| T) y  =  ⟪y, T y⟫·x ,

so that dividing by `‖y‖² ≠ 0` for one fixed `y ≠ 0` exhibits `T` as the
scalar `⟪y,Ty⟫/‖y‖²`.

Two notes on the rendering.  The thesis runs the display for a *positive*
central `A` and writes the right-hand scalar as `‖√A y‖²`; that is only an
identification of `⟪y, A y⟫` (`√A` is self-adjoint and `√A√A = A`), and
positivity enters the argument nowhere else, so the computation is given
here for an arbitrary central `T`, which is what the statement asks for.
And the thesis pairs the display against `x`, reading it as an equality of
quadratic forms; the unpaired form above is that same equality one step
earlier, so no polarisation is needed to undo the pairing. -/
theorem central_examples_3 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) :
    IsCentral (H →L[ℂ] H) T ↔ ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
  constructor
  · intro hT
    rcases subsingleton_or_nontrivial H with hsub | hnt
    · refine ⟨0, ?_⟩
      ext y
      simp [Subsingleton.elim y 0]
    obtain ⟨y, hy⟩ := exists_ne (0 : H)
    have hyy : (⟪y, y⟫ : ℂ) ≠ 0 := by
      simpa [inner_self_eq_zero] using hy
    refine ⟨(⟪y, T y⟫ : ℂ) / ⟪y, y⟫, ?_⟩
    ext x
    -- `T |x⟩⟨y| = |x⟩⟨y| T`, evaluated at `y`
    have h := hT ((innerSL ℂ y).smulRight x)
    have h0 := congrArg (fun S : H →L[ℂ] H => S y) h
    simp only [mul_apply_eq_comp, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, map_smul] at h0
    have h1 : (⟪y, y⟫ : ℂ) • T x = (⟪y, T y⟫ : ℂ) • x := h0
    show T x = ((⟪y, T y⟫ : ℂ) / ⟪y, y⟫) • x
    rw [div_eq_inv_mul, ← smul_smul, ← h1, smul_smul, inv_mul_cancel₀ hyy, one_smul]
  · rintro ⟨z, rfl⟩ b
    simp [smul_mul_assoc, mul_smul_comm]

/-! ### The corner `c𝒜` as a von Neumann algebra in its own right

**67IV**.1's demands (ii) and (iii) — "`c𝒜` is a von Neumann algebra with `c`
as unit", and "`a ↦ (ca, c^⊥a)` is an nmiu-isomorphism `𝒜 → c𝒜 ⊕ c^⊥𝒜`" —
are statements *about a carrier type* for the corner, which this section
builds.  `c𝒜` is the non-unital `*`-subalgebra `{b : cb = b}` of `𝒜`
(part 1's demand (i)) with `c` adjoined as unit; the resulting
`CStarAlgebra`, order and `VonNeumannAlgebra` instances are all inherited
from `𝒜`, and the two facts that make the inheritance work are

* `corner_ub` — an upper bound `u ∈ 𝒜` of a nonempty set of corner elements
  dominates `cu`, because `c^⊥ u c^⊥ = c^⊥ u ≥ c^⊥ d c^⊥ = 0`; hence
  suprema computed in `𝒜` land in the corner and agree with suprema computed
  there (`mul_eq_of_isLUB`, `inclP_preservesDirSups`), and
* `restrictNP` — every np-functional of `𝒜` restricts to one of `c𝒜`, which
  is what carries faithfulness across.

The same section supplies the compression `a ↦ ca` as an nmiu-map
(`compress`) — used again for **69IVa**. -/

section Corner

/-- A **central projection** of `A`, bundled, so that the corner it cuts out
can carry instances. -/
structure CentralProj (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] where
  /-- the underlying element -/
  val : A
  /-- it is a projection -/
  isProj : IsStarProjection val
  /-- it is central -/
  isCentral : IsCentral A val

namespace CentralProj

variable (c : CentralProj A)

theorem mul_self : c.val * c.val = c.val := c.isProj.isIdempotentElem.eq

theorem star_val : star c.val = c.val := c.isProj.isSelfAdjoint.star_eq

/-- Conjugation by a central projection collapses: `c x c = c x`. -/
theorem conj_eq (x : A) : c.val * x * c.val = c.val * x := by
  rw [mul_assoc, ← c.isCentral x, ← mul_assoc, c.mul_self]

/-- The complement `c^⊥` of a central projection is a central projection. -/
def compl : CentralProj A where
  val := 1 - c.val
  isProj := c.isProj.one_sub
  isCentral := fun b => by
    rw [sub_mul, mul_sub, one_mul, mul_one, c.isCentral b]

@[simp] theorem compl_val : (c.compl).val = 1 - c.val := rfl

/-- **67IV**.1, demand (i): the corner `cA = {b : cb = b}` as a non-unital
`*`-subalgebra of `A` — closed under addition, multiplication, scalar
multiplication and involution (`central_projections_sums_1`), and norm
closed. -/
def sub : NonUnitalStarSubalgebra ℂ A where
  carrier := {a : A | c.val * a = a}
  add_mem' := by
    intro x y hx hy
    show c.val * (x + y) = x + y
    rw [mul_add, hx, hy]
  zero_mem' := by show c.val * (0 : A) = 0; rw [mul_zero]
  mul_mem' := by
    intro x y hx hy
    show c.val * (x * y) = x * y
    rw [← mul_assoc, (hx : c.val * x = x)]
  smul_mem' := by
    intro z x hx
    show c.val * (z • x) = z • x
    rw [mul_smul_comm, (hx : c.val * x = x)]
  star_mem' := by
    intro x hx
    show c.val * star x = star x
    have h := congrArg star (hx : c.val * x = x)
    rwa [star_mul, c.star_val, ← c.isCentral (star x)] at h

theorem mem_sub_iff (a : A) : a ∈ c.sub ↔ c.val * a = a := Iff.rfl

instance : IsClosed (c.sub : Set A) :=
  isClosed_eq (continuous_const.mul continuous_id) continuous_id

/-- `c` itself is the unit of the corner. -/
noncomputable instance : One c.sub := ⟨⟨c.val, c.mul_self⟩⟩

@[simp] theorem one_coe : ((1 : c.sub) : A) = c.val := rfl

noncomputable instance : Ring c.sub :=
  { (inferInstance : NonUnitalRing c.sub), (inferInstance : One c.sub) with
    one_mul := by
      rintro ⟨x, hx⟩
      exact Subtype.ext (hx : c.val * x = x)
    mul_one := by
      rintro ⟨x, hx⟩
      refine Subtype.ext ?_
      show x * c.val = x
      rw [← c.isCentral x]
      exact hx }

noncomputable instance : NormedRing c.sub where
  dist_eq := fun x y => NonUnitalNormedRing.dist_eq x y
  norm_mul_le := fun x y => norm_mul_le x y

noncomputable instance : Algebra ℂ c.sub :=
  Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)

noncomputable instance : NormedAlgebra ℂ c.sub where
  norm_smul_le := fun r x => norm_smul_le r x

/-- **67IV**.1, demand (ii), first half: the corner is a C\*-algebra with
`c` as unit. -/
noncomputable instance : CStarAlgebra c.sub where

theorem algebraMap_coe (r : ℂ) : ((algebraMap ℂ c.sub r : c.sub) : A) = r • c.val := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

theorem coe_le_coe {x y : c.sub} : x ≤ y ↔ (x : A) ≤ (y : A) := Iff.rfl

/-- The order of the corner is that of `A`, and it is the C\*-order: the
positives are the `star s * s` for `s` in the corner (take `s = c √x`). -/
noncomputable instance : StarOrderedRing c.sub := by
  refine StarOrderedRing.of_nonneg_iff' (fun {x y} h z => ?_) (fun x => ?_)
  · refine Subtype.coe_le_coe.mp ?_
    show ((z : A) + (x : A)) ≤ ((z : A) + (y : A))
    exact add_le_add le_rfl (Subtype.coe_le_coe.mpr h)
  · constructor
    · intro hx
      have hxA : (0 : A) ≤ (x : A) := hx
      set s : A := CFC.sqrt (x : A) with hs
      have hsa : star s = s := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (x : A))).star_eq
      have hss : s * s = (x : A) := CFC.sqrt_mul_sqrt_self (x : A) hxA
      refine ⟨⟨c.val * s, ?_⟩, ?_⟩
      · show c.val * (c.val * s) = c.val * s
        rw [← mul_assoc, c.mul_self]
      · refine Subtype.ext ?_
        show (x : A) = star (c.val * s) * (c.val * s)
        have hcc : star (c.val * s) * (c.val * s) = c.val * (s * s) := by
          rw [star_mul, hsa, c.star_val]
          calc s * c.val * (c.val * s) = s * (c.val * c.val) * s := by noncomm_ring
            _ = s * c.val * s := by rw [c.mul_self]
            _ = c.val * s * s := by rw [← c.isCentral s]
            _ = c.val * (s * s) := by noncomm_ring
        rw [hcc, hss]
        exact (x.2 : c.val * (x : A) = (x : A)).symm
    · rintro ⟨t, rfl⟩
      show (0 : A) ≤ star (t : A) * (t : A)
      exact star_mul_self_nonneg (t : A)

theorem isSelfAdjoint_iff {x : c.sub} : IsSelfAdjoint x ↔ IsSelfAdjoint (x : A) :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- A self-adjoint element of the corner, read in `A`. -/
noncomputable def saIncl (x : selfAdjoint c.sub) : selfAdjoint A :=
  ⟨((x : c.sub) : A), (isSelfAdjoint_iff c).mp x.2⟩

@[simp] theorem saIncl_coe (x : selfAdjoint c.sub) :
    ((saIncl c x : selfAdjoint A) : A) = ((x : c.sub) : A) := rfl

/-- An upper bound `u ∈ A` of a nonempty set of corner elements dominates
`cu`, which is itself an upper bound and lies in the corner: the `c^⊥`-part
of `u` is positive because it dominates `c^⊥ d c^⊥ = 0`. -/
theorem corner_ub {D : Set A} (hD : ∀ d ∈ D, c.val * d = d) (hne : D.Nonempty)
    {u : A} (hu : ∀ d ∈ D, d ≤ u) :
    c.val * u ≤ u ∧ ∀ d ∈ D, d ≤ c.val * u := by
  obtain ⟨d₀, hd₀⟩ := hne
  have hq : IsSelfAdjoint (1 - c.val) := c.isProj.one_sub.isSelfAdjoint
  have hqc : ∀ x : A, x * (1 - c.val) = (1 - c.val) * x := by
    intro x
    rw [sub_mul, mul_sub, one_mul, mul_one, c.isCentral x]
  have hconj : ∀ x : A, (1 - c.val) * x * (1 - c.val) = x - c.val * x := by
    intro x
    rw [mul_assoc, hqc x, ← mul_assoc, c.isProj.one_sub.isIdempotentElem.eq,
      sub_mul, one_mul]
  constructor
  · have hd0 : (1 - c.val) * d₀ * (1 - c.val) = 0 := by
      rw [hconj d₀, hD d₀ hd₀, sub_self]
    have h := IsSelfAdjoint.conjugate_le_conjugate (hu d₀ hd₀) hq
    rw [hd0, hconj u] at h
    exact sub_nonneg.mp h
  · intro d hd
    have h := IsSelfAdjoint.conjugate_le_conjugate (hu d hd) c.isProj.isSelfAdjoint
    rwa [c.conj_eq d, c.conj_eq u, hD d hd] at h

/-- `c s = s` for the supremum in `A` of a nonempty set of corner elements:
`c s` is a self-adjoint upper bound sitting below `s`. -/
theorem mul_eq_of_isLUB {D : Set (selfAdjoint A)}
    (hD : ∀ d ∈ D, c.val * (d : A) = (d : A)) (hne : D.Nonempty)
    {s : selfAdjoint A} (hlub : IsLUB D s) : c.val * (s : A) = (s : A) := by
  have hsa : IsSelfAdjoint (c.val * (s : A)) := by
    show star (c.val * (s : A)) = c.val * (s : A)
    rw [star_mul, s.2.star_eq, c.star_val, ← c.isCentral (s : A)]
  obtain ⟨hle, hub⟩ := c.corner_ub (D := (fun d : selfAdjoint A => (d : A)) '' D)
    (by rintro _ ⟨d, hd, rfl⟩; exact hD d hd) (hne.image _)
    (u := (s : A)) (by rintro _ ⟨d, hd, rfl⟩; exact Subtype.coe_le_coe.mpr (hlub.1 hd))
  have h2 : s ≤ (⟨c.val * (s : A), hsa⟩ : selfAdjoint A) :=
    hlub.2 (fun d hd => Subtype.coe_le_coe.mp (hub _ ⟨d, hd, rfl⟩))
  exact le_antisymm hle (Subtype.coe_le_coe.mpr h2)

/-- The inclusion `cA ↪ A` as a positive linear map. -/
noncomputable def inclP : c.sub →ₚ[ℂ] A where
  toFun := fun x => (x : A)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  monotone' := fun _ _ h => h

@[simp] theorem inclP_apply (x : c.sub) : c.inclP x = (x : A) := rfl

/-- The inclusion `cA ↪ A` is normal: a supremum computed in the corner is
the supremum in `A` (leastness is `corner_ub`). -/
theorem inclP_preservesDirSups : PreservesDirSups ⇑c.inclP := by
  intro D s hne hdir hlub
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact Subtype.coe_le_coe.mp (hlub.1 hd)
  · intro u hu
    obtain ⟨d₀, hd₀⟩ := hne
    have husa : IsSelfAdjoint u :=
      IsSelfAdjoint.of_ge (hu ⟨d₀, hd₀, rfl⟩) ((isSelfAdjoint_iff c).mp d₀.2)
    have hmem : c.val * (c.val * u) = c.val * u := by rw [← mul_assoc, c.mul_self]
    have hsa : IsSelfAdjoint ((⟨c.val * u, hmem⟩ : c.sub)) := by
      refine Subtype.ext ?_
      show star (c.val * u) = c.val * u
      rw [star_mul, husa.star_eq, c.star_val, ← c.isCentral u]
    obtain ⟨hle, hub⟩ := c.corner_ub
      (D := (fun d : selfAdjoint c.sub => ((d : c.sub) : A)) '' D)
      (by rintro _ ⟨d, hd, rfl⟩; exact (d : c.sub).2) ⟨_, ⟨d₀, hd₀, rfl⟩⟩
      (u := u) hu
    have h2 : s ≤ (⟨⟨c.val * u, hmem⟩, hsa⟩ : selfAdjoint c.sub) :=
      hlub.2 (fun d hd => hub _ ⟨d, hd, rfl⟩)
    exact le_trans (Subtype.coe_le_coe.mp h2) hle

/-- A supremum in the corner is a supremum among the self-adjoints of `A`. -/
theorem saIncl_isLUB {D : Set (selfAdjoint c.sub)} {s : selfAdjoint c.sub}
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hlub : IsLUB D s) :
    IsLUB (saIncl c '' D) (saIncl c s) := by
  have h := c.inclP_preservesDirSups D s hne hdir hlub
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact Subtype.coe_le_coe.mp (h.1 ⟨d, hd, rfl⟩)
  · intro u hu
    refine Subtype.coe_le_coe.mp (h.2 ?_)
    rintro _ ⟨d, hd, rfl⟩
    exact Subtype.coe_le_coe.mpr (hu ⟨d, hd, rfl⟩)

/-- Every np-functional of `A` restricts to an np-functional of the corner. -/
noncomputable def restrictNP (ω : NPFunctional A) : NPFunctional c.sub :=
  compNP c.inclP c.inclP_preservesDirSups ω

@[simp] theorem restrictNP_apply (ω : NPFunctional A) (x : c.sub) :
    c.restrictNP ω x = ω (x : A) := rfl

/-- **67IV**.1, demand (ii): the corner `cA` is a **von Neumann algebra**
with `c` as unit.  Bounded directed suprema are computed in `A` and land in
`cA` (`mul_eq_of_isLUB`); the np-functionals of `cA` are faithful because
those of `A` are and every one of them restricts (`restrictNP`). -/
noncomputable instance : VonNeumannAlgebra c.sub where
  isLUB_of_bddAbove_directed := by
    intro D hne hdir hbdd
    obtain ⟨b, hb⟩ := hbdd
    set D' : Set (selfAdjoint A) := saIncl c '' D with hD'
    have hD'mem : ∀ d ∈ D', c.val * (d : A) = (d : A) := by
      rintro _ ⟨d, hd, rfl⟩; exact (d : c.sub).2
    have hD'ne : D'.Nonempty := hne.image _
    have hD'dir : DirectedOn (· ≤ ·) D' := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
      exact ⟨saIncl c z, ⟨z, hz, rfl⟩, hxz, hyz⟩
    have hD'bdd : BddAbove D' := by
      refine ⟨saIncl c b, ?_⟩
      rintro _ ⟨d, hd, rfl⟩
      exact hb hd
    obtain ⟨t, ht⟩ :=
      VonNeumannAlgebra.isLUB_of_bddAbove_directed D' hD'ne hD'dir hD'bdd
    have hmem : c.val * (t : A) = (t : A) := c.mul_eq_of_isLUB hD'mem hD'ne ht
    have hsa : IsSelfAdjoint ((⟨(t : A), hmem⟩ : c.sub)) := Subtype.ext t.2
    refine ⟨⟨⟨(t : A), hmem⟩, hsa⟩, ?_, ?_⟩
    · intro d hd
      exact ht.1 ⟨d, hd, rfl⟩
    · intro u hu
      have hub : saIncl c u ∈ upperBounds D' := by
        rintro _ ⟨d, hd, rfl⟩
        exact hu hd
      exact ht.2 hub
  np_faithful := by
    intro a ha hzero
    refine Subtype.ext (VonNeumannAlgebra.np_faithful (a : A) ha fun ω => ?_)
    exact hzero (c.restrictNP ω)

/-- The compression `a ↦ ca : A → cA`, an nmiu-map.  Normality is the
computation `c(⋁D) = ⋁(cD)`: leastness holds because for an upper bound `u`
of `cD` in the corner the element `u + c^⊥(⋁D)` is a self-adjoint upper
bound of `D` itself. -/
noncomputable def compress : NMIUMap A c.sub where
  toStarAlgHom :=
    { toFun := fun a => ⟨c.val * a, by
        show c.val * (c.val * a) = c.val * a
        rw [← mul_assoc, c.mul_self]⟩
      map_one' := Subtype.ext (by show c.val * 1 = c.val; rw [mul_one])
      map_mul' := fun a b => Subtype.ext (by
        show c.val * (a * b) = c.val * a * (c.val * b)
        symm
        calc c.val * a * (c.val * b) = c.val * (a * c.val) * b := by noncomm_ring
          _ = c.val * (c.val * a) * b := by rw [← c.isCentral a]
          _ = c.val * c.val * (a * b) := by noncomm_ring
          _ = c.val * (a * b) := by rw [c.mul_self])
      map_zero' := Subtype.ext (by show c.val * 0 = 0; rw [mul_zero])
      map_add' := fun a b => Subtype.ext (by
        show c.val * (a + b) = c.val * a + c.val * b
        rw [mul_add])
      commutes' := fun r => Subtype.ext (by
        rw [algebraMap_coe]
        show c.val * (algebraMap ℂ A r) = r • c.val
        rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one])
      map_star' := fun a => Subtype.ext (by
        show c.val * star a = star (c.val * a)
        rw [star_mul, c.star_val, ← c.isCentral (star a)]) }
  preservesDirSups' := by
    intro D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      show c.val * ((d : selfAdjoint A) : A) ≤ c.val * ((s : selfAdjoint A) : A)
      have h := IsSelfAdjoint.conjugate_le_conjugate
        (Subtype.coe_le_coe.mpr (hlub.1 hd)) c.isProj.isSelfAdjoint
      rwa [c.conj_eq, c.conj_eq] at h
    · intro u hu
      obtain ⟨d₀, hd₀⟩ := hne
      have hd0sa : IsSelfAdjoint (c.val * ((d₀ : selfAdjoint A) : A)) := by
        show star _ = _
        rw [star_mul, d₀.2.star_eq, c.star_val, ← c.isCentral _]
      have husa : IsSelfAdjoint ((u : A)) :=
        IsSelfAdjoint.of_ge
          (show c.val * ((d₀ : selfAdjoint A) : A) ≤ (u : A) from hu ⟨d₀, hd₀, rfl⟩) hd0sa
      set q : A := 1 - c.val with hq
      have hqsa : IsSelfAdjoint q := c.isProj.one_sub.isSelfAdjoint
      have hqc : ∀ x : A, q * x = x * q := fun x => by
        rw [hq, sub_mul, mul_sub, one_mul, mul_one, c.isCentral x]
      have hqq : ∀ x : A, q * x * q = q * x := by
        intro x
        rw [mul_assoc, ← hqc x, ← mul_assoc, hq,
          c.isProj.one_sub.isIdempotentElem.eq]
      have hbnd : IsSelfAdjoint ((u : A) + q * ((s : selfAdjoint A) : A)) := by
        show star _ = _
        rw [star_add, husa.star_eq, star_mul, s.2.star_eq, hqsa.star_eq, ← hqc]
      have hub : ∀ d ∈ D, d ≤ (⟨(u : A) + q * ((s : selfAdjoint A) : A), hbnd⟩ :
          selfAdjoint A) := by
        intro d hd
        refine Subtype.coe_le_coe.mp ?_
        show ((d : selfAdjoint A) : A) ≤ (u : A) + q * ((s : selfAdjoint A) : A)
        have h1 : c.val * ((d : selfAdjoint A) : A) ≤ (u : A) := hu ⟨d, hd, rfl⟩
        have h2 : q * ((d : selfAdjoint A) : A) ≤ q * ((s : selfAdjoint A) : A) := by
          have h := IsSelfAdjoint.conjugate_le_conjugate
            (Subtype.coe_le_coe.mpr (hlub.1 hd)) hqsa
          rwa [hqq, hqq] at h
        have h3 := add_le_add h1 h2
        have h4 : c.val * ((d : selfAdjoint A) : A) + q * ((d : selfAdjoint A) : A)
            = ((d : selfAdjoint A) : A) := by
          rw [hq, sub_mul, one_mul]; abel
        rwa [h4] at h3
      have h5 := hlub.2 hub
      have h6 := IsSelfAdjoint.conjugate_le_conjugate
        (Subtype.coe_le_coe.mpr h5) c.isProj.isSelfAdjoint
      rw [c.conj_eq] at h6
      show c.val * ((s : selfAdjoint A) : A) ≤ (u : A)
      have hcq : c.val * q = 0 := by
        rw [hq, mul_sub, mul_one, c.mul_self, sub_self]
      have h7 : c.val * ((u : A) + q * ((s : selfAdjoint A) : A)) * c.val = (u : A) := by
        rw [c.conj_eq, mul_add, ← mul_assoc, hcq, zero_mul, add_zero]
        exact u.2
      rwa [h7] at h6

@[simp] theorem compress_coe (a : A) : ((c.compress a : c.sub) : A) = c.val * a := rfl

theorem compress_surjective : Function.Surjective ⇑c.compress := by
  intro x
  refine ⟨(x : A), Subtype.ext ?_⟩
  show c.val * (x : A) = (x : A)
  exact x.2

/-- `a ↦ (ca, c^⊥a) : A → cA ⊕ c^⊥A`, an nmiu-map. -/
noncomputable def split : NMIUMap A (c.sub × (c.compl).sub) where
  toStarAlgHom :=
    { toFun := fun a => (c.compress a, (c.compl).compress a)
      map_one' := Prod.ext (map_one c.compress.toStarAlgHom)
        (map_one (c.compl).compress.toStarAlgHom)
      map_mul' := fun a b => Prod.ext (map_mul c.compress.toStarAlgHom a b)
        (map_mul (c.compl).compress.toStarAlgHom a b)
      map_zero' := Prod.ext (map_zero c.compress.toStarAlgHom)
        (map_zero (c.compl).compress.toStarAlgHom)
      map_add' := fun a b => Prod.ext (map_add c.compress.toStarAlgHom a b)
        (map_add (c.compl).compress.toStarAlgHom a b)
      commutes' := fun r => Prod.ext (c.compress.toStarAlgHom.commutes r)
        ((c.compl).compress.toStarAlgHom.commutes r)
      map_star' := fun a => Prod.ext (map_star c.compress.toStarAlgHom a)
        (map_star (c.compl).compress.toStarAlgHom a) }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have h1 := c.compress.preservesDirSups' D s hne hdir hlub
    have h2 := (c.compl).compress.preservesDirSups' D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      exact ⟨h1.1 ⟨d, hd, rfl⟩, h2.1 ⟨d, hd, rfl⟩⟩
    · rintro ⟨u, v⟩ huv
      exact ⟨h1.2 (by rintro _ ⟨d, hd, rfl⟩; exact (huv ⟨d, hd, rfl⟩).1),
        h2.2 (by rintro _ ⟨d, hd, rfl⟩; exact (huv ⟨d, hd, rfl⟩).2)⟩

@[simp] theorem split_fst (a : A) : ((c.split a).1 : A) = c.val * a := rfl

@[simp] theorem split_snd (a : A) : ((c.split a).2 : A) = (1 - c.val) * a := rfl

theorem split_bijective : Function.Bijective ⇑c.split := by
  constructor
  · intro a b hab
    have h1 : c.val * a = c.val * b := congrArg (fun z => ((z.1 : c.sub) : A)) hab
    have h2 : (1 - c.val) * a = (1 - c.val) * b := congrArg (fun z => ((z.2 : _) : A)) hab
    have h3 : c.val * a + (1 - c.val) * a = c.val * b + (1 - c.val) * b := by rw [h1, h2]
    simpa [sub_mul] using h3
  · rintro ⟨x, y⟩
    refine ⟨(x : A) + (y : A), Prod.ext ?_ ?_⟩
    · refine Subtype.ext ?_
      show c.val * ((x : A) + (y : A)) = (x : A)
      have hy : (1 - c.val) * (y : A) = (y : A) := y.2
      have hcy : c.val * (y : A) = 0 := by
        rw [← hy, ← mul_assoc, mul_sub, mul_one, c.mul_self, sub_self, zero_mul]
      rw [mul_add, hcy, add_zero]
      exact x.2
    · refine Subtype.ext ?_
      show (1 - c.val) * ((x : A) + (y : A)) = (y : A)
      have hx : c.val * (x : A) = (x : A) := x.2
      have hcx : (1 - c.val) * (x : A) = 0 := by
        rw [← hx, ← mul_assoc]
        show (1 - c.val) * c.val * (x : A) = 0
        rw [sub_mul, one_mul, c.mul_self, sub_self, zero_mul]
      rw [mul_add, hcx, zero_add]
      exact y.2

end CentralProj

end Corner

/-- **67IV** (`central-projections-sums`, vn.tex:3408, Exercise), part 1,
demand (i): for a central projection `c` of a von Neumann algebra `A` the
corner `cA = {ca : a ∈ A} = {b : cb = b}` is a von Neumann subalgebra of `A`
"for all but the fact that `1` need not be in `cA`" — it is closed under
addition, multiplication, involution and **scalar multiplication**, is
**norm-closed**, has `c` as a unit, and is closed under bounded directed
suprema of self-adjoint elements.  (The scalar and norm clauses are the two
remaining fields of `IsVNSubalgebra`; the missing one is exactly `1 ∈ cA`.)

Demands (ii) and (iii) are `central_projections_sums_1_algebra` below, on
the carrier `CentralProj.sub` built in the preceding section. -/
theorem central_projections_sums_1 (c : A) (hc : IsStarProjection c)
    (hcentral : IsCentral A c) :
    (∀ x ∈ {b : A | c * b = b}, ∀ y ∈ {b : A | c * b = b},
        x + y ∈ {b : A | c * b = b} ∧ x * y ∈ {b : A | c * b = b} ∧
          star x ∈ {b : A | c * b = b}) ∧
      (∀ (z : ℂ), ∀ x ∈ {b : A | c * b = b}, z • x ∈ {b : A | c * b = b}) ∧
      IsClosed {b : A | c * b = b} ∧
      c * c = c ∧  -- `c` is the unit of the corner `cA`
      (∀ x ∈ {b : A | c * b = b}, c * x = x ∧ x * c = x) ∧
      (∀ (D : Set (selfAdjoint A)) (s : selfAdjoint A),
        (∀ d ∈ D, c * (d : A) = (d : A)) → D.Nonempty →
          DirectedOn (· ≤ ·) D → IsLUB D s → c * (s : A) = (s : A)) := by
  have hcs : star c = c := hc.isSelfAdjoint.star_eq
  refine ⟨?_, ?_, isClosed_eq (continuous_const.mul continuous_id) continuous_id,
    hc.isIdempotentElem.eq, ?_, ?_⟩
  · intro x hx y hy
    have hx' : c * x = x := hx
    have hy' : c * y = y := hy
    refine ⟨?_, ?_, ?_⟩
    · show c * (x + y) = x + y
      rw [mul_add, hx', hy']
    · show c * (x * y) = x * y
      rw [← mul_assoc, hx']
    · show c * star x = star x
      have h := congrArg star hx'
      rwa [star_mul, hcs, ← hcentral (star x)] at h
  · intro z x hx
    show c * (z • x) = z • x
    rw [mul_smul_comm, (hx : c * x = x)]
  · intro x hx
    exact ⟨hx, by rw [← hcentral x]; exact hx⟩
  · intro D s hD hne hdir hlub
    have hfix : ∀ d ∈ D, c * (d : A) * c = (d : A) := by
      intro d hd
      rw [hD d hd, ← hcentral (d : A), hD d hd]
    -- `csc` is an upper bound of `D`, so `s ≤ csc`
    have hsacsc : IsSelfAdjoint (c * (s : A) * c) := by
      have : star (c * (s : A) * c) = c * (s : A) * c := by
        rw [star_mul, star_mul, hcs, s.2.star_eq, mul_assoc]
      exact this
    have hub : ∀ d ∈ D, d ≤ (⟨c * (s : A) * c, hsacsc⟩ : selfAdjoint A) := by
      intro d hd
      refine Subtype.coe_le_coe.mp ?_
      show (d : A) ≤ c * (s : A) * c
      rw [← hfix d hd]
      exact IsSelfAdjoint.conjugate_le_conjugate
        (Subtype.coe_le_coe.mpr (hlub.1 hd)) hc.isSelfAdjoint
    have hle : (s : A) ≤ c * (s : A) * c :=
      Subtype.coe_le_coe.mpr (hlub.2 hub)
    -- conjugate by `c^⊥`
    set q : A := 1 - c with hq
    have hqc : q * c = 0 := by rw [hq, sub_mul, one_mul, hc.isIdempotentElem.eq, sub_self]
    have hqsa : IsSelfAdjoint q := hc.one_sub.isSelfAdjoint
    have hqcentral : IsCentral A q := fun b => by
      rw [hq, sub_mul, mul_sub, one_mul, mul_one, hcentral b]
    have hupper : q * (s : A) * q ≤ 0 := by
      have h := IsSelfAdjoint.conjugate_le_conjugate hle hqsa
      have hz : q * (c * (s : A) * c) * q = 0 := by
        rw [show q * (c * (s : A) * c) * q = (q * c) * (s : A) * (c * q) by noncomm_ring,
          hqc, zero_mul, zero_mul]
      rwa [hz] at h
    have hlower : (0 : A) ≤ q * (s : A) * q := by
      obtain ⟨d, hd⟩ := hne
      have h := IsSelfAdjoint.conjugate_le_conjugate
        (Subtype.coe_le_coe.mpr (hlub.1 hd)) hqsa
      have hz : q * ((d : selfAdjoint A) : A) * q = 0 := by
        rw [← hfix d hd,
          show q * (c * ((d : selfAdjoint A) : A) * c) * q
            = (q * c) * ((d : selfAdjoint A) : A) * (c * q) by noncomm_ring,
          hqc, zero_mul, zero_mul]
      rwa [hz] at h
    have hzero : q * (s : A) * q = 0 := le_antisymm hupper hlower
    have hqq : q * q = q := hc.one_sub.isIdempotentElem.eq
    have heq : q * (s : A) * q = q * (s : A) := by
      calc q * (s : A) * q = q * ((s : A) * q) := by noncomm_ring
        _ = q * (q * (s : A)) := by rw [← hqcentral (s : A)]
        _ = q * q * (s : A) := by noncomm_ring
        _ = q * (s : A) := by rw [hqq]
    have hqs : q * (s : A) = 0 := by rw [← heq]; exact hzero
    rw [hq, sub_mul, one_mul, sub_eq_zero] at hqs
    exact hqs.symm

/-- **67IV** (`central-projections-sums`, vn.tex:3408, Exercise), part 1,
demands (ii) and (iii): the corner `cA` **is a von Neumann algebra with `c`
as unit**, and `a ↦ (ca, c^⊥a)` is an **nmiu-isomorphism**
`A → cA ⊕ c^⊥A`.

Demand (ii) is carried by the instances of the preceding section — the
`VonNeumannAlgebra (CentralProj.sub c)` instance, whose `1` is `c` — and
recorded here by the first conjunct.  Demand (iii) is `CentralProj.split`:
an nmiu-map (multiplicative, involutive, unital, `ℂ`-linear and normal, all
four being fields of `NMIUMap`) which is bijective, hence an isomorphism.
The binary direct sum `cA ⊕ c^⊥A` is rendered as the product, which is
Mathlib's C\*-algebra direct sum of two summands. -/
theorem central_projections_sums_1_algebra (c : CentralProj A) :
    ((1 : c.sub) : A) = c.val ∧
      ∃ Φ : NMIUMap A (c.sub × (c.compl).sub),
        Function.Bijective ⇑Φ ∧
          ∀ a : A, ((Φ a).1 : A) = c.val * a ∧ ((Φ a).2 : A) = (1 - c.val) * a :=
  ⟨rfl, c.split, c.split_bijective, fun _ => ⟨rfl, rfl⟩⟩

/-- Auxiliary for **67IV**.2: a family of central projections whose
supremum is `1` is separating — if `cᵢa = 0` for every `i`, then `a = 0`.
(Take `⌈aa*⌉`: `aa*cᵢ = 0` gives `⌈aa*⌉cᵢ = 0` by `ceil_mul_eq_zero`, so
every `cᵢ` lies below `1 − ⌈aa*⌉`, whence `1 ≤ 1 − ⌈aa*⌉`.) -/
theorem central_family_separating {ι : Type*} (c : ι → A)
    (hc : ∀ i, IsStarProjection (c i))
    (hsum : projSup (Set.range c) = 1)
    {a : A} (ha : ∀ i, c i * a = 0) : a = 0 := by
  have hnn : (0 : A) ≤ a * star a := mul_star_self_nonneg a
  have hkey : ∀ i, ceil (a * star a) * c i = 0 := by
    intro i
    refine ceil_mul_eq_zero hnn ?_
    have h : star a * c i = 0 := by
      have := congrArg star (ha i)
      rwa [star_mul, (hc i).isSelfAdjoint.star_eq, star_zero] at this
    calc a * star a * c i = a * (star a * c i) := by noncomm_ring
      _ = 0 := by rw [h, mul_zero]
  have hle : projSup (Set.range c) ≤ 1 - ceil (a * star a) := by
    refine (projSup_spec ?_).2.2 _ ((ceil_spec hnn).1).one_sub ?_
    · rintro _ ⟨i, rfl⟩; exact hc i
    · rintro _ ⟨i, rfl⟩
      exact ((orthogonal_tuple_of_projections_1 (c i) (ceil (a * star a))
        (hc i) ((ceil_spec hnn).1)).out 0 4).mp
        (by
          have := congrArg star (hkey i)
          rwa [star_mul, (hc i).isSelfAdjoint.star_eq,
            ((ceil_spec hnn).1).isSelfAdjoint.star_eq, star_zero] at this)
  rw [hsum] at hle
  have hz : ceil (a * star a) = 0 := by
    have : (0 : A) ≤ -ceil (a * star a) := by
      have := sub_nonneg.mpr hle
      simpa using this
    have h2 := ((ceil_spec hnn).1).nonneg
    have : ceil (a * star a) ≤ 0 := by
      have := neg_nonneg.mp this
      exact this
    exact le_antisymm this h2
  have : a * star a = 0 := by
    have := (ceil_spec hnn).2.1
    rw [hz, mul_zero] at this
    exact this.symm
  exact (CStarRing.mul_star_self_eq_zero_iff a).mp this

/-- Auxiliary for **67IV**.2, the heart of the existence half: a *positive*
family `(bᵢ)` in the corners `cᵢA` of an orthogonal family of central
projections, bounded above by `M·1`, is `(cᵢa)ᵢ` for the supremum `a` of the
finite partial sums `∑_{i∈F} bᵢ`.  The partial sums are directed and bounded
by `M·1` (a finite sum of orthogonal projections is a projection), so `a`
exists by von Neumann-ness alone — no ultraweak compactness is needed.  That
`cⱼa = bⱼ` comes from `bⱼ + cⱼ^⊥ a cⱼ^⊥` being an upper bound of the partial
sums as well. -/
private theorem exists_corner_lift_nonneg {ι : Type*} (c : ι → A)
    (hc : ∀ i, IsStarProjection (c i)) (hcen : ∀ i, IsCentral A (c i))
    (horth : Pairwise fun i j => c i * c j = 0)
    (b : ι → A) (hbnn : ∀ i, 0 ≤ b i) (hb : ∀ i, c i * b i = b i)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, b i ≤ M • (1 : A)) :
    ∃ a : A, ∀ i, c i * a = b i := by
  classical
  -- partial sums
  have hSsa : ∀ F : Finset ι, IsSelfAdjoint (∑ i ∈ F, b i) := by
    intro F
    change star (∑ i ∈ F, b i) = _
    rw [star_sum]
    exact Finset.sum_congr rfl fun i _ => (IsSelfAdjoint.of_nonneg (hbnn i)).star_eq
  set D : Set (selfAdjoint A) :=
    Set.range (fun F : Finset ι => (⟨∑ i ∈ F, b i, hSsa F⟩ : selfAdjoint A)) with hDdef
  have hmono : ∀ F G : Finset ι, F ⊆ G → (∑ i ∈ F, b i) ≤ ∑ i ∈ G, b i := by
    intro F G h
    exact Finset.sum_le_sum_of_subset_of_nonneg h fun i _ _ => hbnn i
  have hne : D.Nonempty := ⟨_, ⟨∅, rfl⟩⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
    exact ⟨_, ⟨F ∪ G, rfl⟩,
      Subtype.coe_le_coe.mp (hmono _ _ Finset.subset_union_left),
      Subtype.coe_le_coe.mp (hmono _ _ Finset.subset_union_right)⟩
  -- `b i ≤ M • c i`
  have hbMc : ∀ i, b i ≤ M • c i := by
    intro i
    have h2 := star_left_conjugate_le_conjugate (hM i) (c i)
    rw [(hc i).isSelfAdjoint.star_eq] at h2
    have hcbc : c i * b i * c i = b i := by
      rw [hb i, ← hcen i (b i)]; exact hb i
    have hrhs : c i * (M • (1 : A)) * c i = M • c i := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, (hc i).isIdempotentElem.eq]
    rwa [hcbc, hrhs] at h2
  have hMone : IsSelfAdjoint (M • (1 : A)) := by
    change star (M • (1 : A)) = M • (1 : A)
    rw [star_smul, star_one, star_trivial]
  have hbdd : BddAbove D := by
    refine ⟨⟨M • (1 : A), hMone⟩, ?_⟩
    rintro _ ⟨F, rfl⟩
    refine Subtype.coe_le_coe.mp ?_
    change (∑ i ∈ F, b i) ≤ M • (1 : A)
    calc (∑ i ∈ F, b i) ≤ ∑ i ∈ F, M • c i := Finset.sum_le_sum fun i _ => hbMc i
      _ = M • ∑ i ∈ F, c i := (Finset.smul_sum).symm
      _ ≤ M • (1 : A) := by
          have hp : IsStarProjection (∑ i ∈ F, c i) :=
            isStarProjection_sum F c (fun i => hc i) fun i _ j _ hij => horth hij
          exact smul_le_smul_of_nonneg_left hp.le_one hM0
  set s : selfAdjoint A := dirSup D ⟨hne, hdir, hbdd⟩ with hsdef
  have hlub : IsLUB D s := isLUB_dirSup D ⟨hne, hdir, hbdd⟩
  set a : A := (s : A) with hadef
  refine ⟨a, fun j => ?_⟩
  set q : A := 1 - c j with hqdef
  have hqproj : IsStarProjection q := (hc j).one_sub
  have hqcen : IsCentral A q := fun x => by
    rw [hqdef, sub_mul, mul_sub, one_mul, mul_one, hcen j x]
  have hqb : ∀ i, i ≠ j → q * b i = b i := by
    intro i hij
    have : c j * b i = 0 := by
      rw [← hb i, ← mul_assoc, horth (Ne.symm hij), zero_mul]
    rw [hqdef, sub_mul, one_mul, this, sub_zero]
  have hUB : ∀ F : Finset ι, (∑ i ∈ F, b i) ≤ b j + q * a * q := by
    intro F
    have hF' : (∑ i ∈ F.erase j, b i) ≤ q * a * q := by
      have hle : (∑ i ∈ F.erase j, b i) ≤ a :=
        Subtype.coe_le_coe.mpr (hlub.1 ⟨F.erase j, rfl⟩)
      have h2 := star_left_conjugate_le_conjugate hle q
      rw [hqproj.isSelfAdjoint.star_eq] at h2
      have hfix : q * (∑ i ∈ F.erase j, b i) * q = ∑ i ∈ F.erase j, b i := by
        have h3 : q * (∑ i ∈ F.erase j, b i) = ∑ i ∈ F.erase j, b i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i hi =>
            hqb i (Finset.ne_of_mem_erase hi)
        rw [← hqcen _, ← mul_assoc, hqproj.isIdempotentElem.eq, h3]
      rwa [hfix] at h2
    by_cases hj : j ∈ F
    · rw [← Finset.add_sum_erase F b hj]
      exact add_le_add le_rfl hF'
    · rw [Finset.erase_eq_of_notMem hj] at hF'
      calc (∑ i ∈ F, b i) ≤ q * a * q := hF'
        _ ≤ b j + q * a * q := le_add_of_nonneg_left (hbnn j)
  have hsale : IsSelfAdjoint (b j + q * a * q) := by
    refine (IsSelfAdjoint.of_nonneg (hbnn j)).add ?_
    have : star (q * a * q) = q * a * q := by
      rw [star_mul, star_mul, hqproj.isSelfAdjoint.star_eq, s.2.star_eq, mul_assoc]
    exact this
  have hub : (⟨b j + q * a * q, hsale⟩ : selfAdjoint A) ∈ upperBounds D := by
    intro x hx
    obtain ⟨F, rfl⟩ := hx
    exact Subtype.coe_le_coe.mp (hUB F)
  have hale : a ≤ b j + q * a * q := Subtype.coe_le_coe.mpr (hlub.2 hub)
  have hcq : c j * q = 0 := by
    rw [hqdef, mul_sub, mul_one, (hc j).isIdempotentElem.eq, sub_self]
  have hcbc : c j * b j * c j = b j := by
    rw [hb j, ← hcen j (b j)]; exact hb j
  have hupper : c j * a * c j ≤ b j := by
    have h := star_left_conjugate_le_conjugate hale (c j)
    rw [(hc j).isSelfAdjoint.star_eq] at h
    have hz : c j * (b j + q * a * q) * c j = b j := by
      rw [mul_add, add_mul, hcbc,
        show c j * (q * a * q) * c j = (c j * q) * a * (q * c j) by noncomm_ring,
        hcq, zero_mul, zero_mul, add_zero]
    rwa [hz] at h
  have hlower : b j ≤ c j * a * c j := by
    have hbjmem : (⟨∑ i ∈ ({j} : Finset ι), b i, hSsa _⟩ : selfAdjoint A) ∈ D := ⟨{j}, rfl⟩
    have hbjle : b j ≤ a := by
      have h0 := Subtype.coe_le_coe.mpr (hlub.1 hbjmem)
      simpa using h0
    have h := star_left_conjugate_le_conjugate hbjle (c j)
    rw [(hc j).isSelfAdjoint.star_eq, hcbc] at h
    exact h
  have heq : c j * a * c j = b j := le_antisymm hupper hlower
  rw [← heq, mul_assoc, ← hcen j a, ← mul_assoc, (hc j).isIdempotentElem.eq]

/-- Auxiliary for **67IV**.2: the self-adjoint case, by shifting.  A
self-adjoint family with `‖bᵢ‖ ≤ M` satisfies `−M·cᵢ ≤ bᵢ`, so `bᵢ + M·cᵢ`
is positive and bounded by `2M·1`; subtract `M·1` from the lift. -/
private theorem exists_corner_lift_selfAdjoint {ι : Type*} (c : ι → A)
    (hc : ∀ i, IsStarProjection (c i)) (hcen : ∀ i, IsCentral A (c i))
    (horth : Pairwise fun i j => c i * c j = 0)
    (d : ι → A) (hdsa : ∀ i, IsSelfAdjoint (d i)) (hdc : ∀ i, c i * d i = d i)
    {M : ℝ} (hM0 : 0 ≤ M) (hdM : ∀ i, ‖d i‖ ≤ M) :
    ∃ a : A, ∀ i, c i * a = d i := by
  have hcoe : algebraMap ℂ A ((M : ℝ) : ℂ) = M • (1 : A) := by
    rw [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
  have hord : ∀ i, -(M • (1 : A)) ≤ d i ∧ d i ≤ M • (1 : A) := by
    intro i
    have h := (Theses.A.CStar.norm_le_iff_neg_algebraMap_le (hdsa i) hM0).mp (hdM i)
    rwa [hcoe] at h
  have hcm : ∀ i, c i * (M • (1 : A)) = M • c i := by
    intro i; rw [mul_smul_comm, mul_one]
  have hcdc : ∀ i, c i * d i * c i = d i := by
    intro i; rw [hdc i, ← hcen i (d i)]; exact hdc i
  set d' : ι → A := fun i => d i + M • c i with hd'def
  have hd'nn : ∀ i, 0 ≤ d' i := by
    intro i
    have h2 := star_left_conjugate_le_conjugate (hord i).1 (c i)
    rw [(hc i).isSelfAdjoint.star_eq, hcdc i,
      show c i * -(M • (1 : A)) * c i = -(M • c i) by
        rw [mul_neg, neg_mul, hcm i, smul_mul_assoc, (hc i).isIdempotentElem.eq]] at h2
    have := neg_le_iff_add_nonneg.mp h2
    simpa [hd'def, add_comm] using this
  have hd'c : ∀ i, c i * d' i = d' i := by
    intro i
    change c i * (d i + M • c i) = d i + M • c i
    rw [mul_add, hdc i, mul_smul_comm, (hc i).isIdempotentElem.eq]
  have hd'M : ∀ i, d' i ≤ (2 * M) • (1 : A) := by
    intro i
    have h1 : M • c i ≤ M • (1 : A) := smul_le_smul_of_nonneg_left (hc i).le_one hM0
    have h2 := add_le_add (hord i).2 h1
    rwa [show M • (1 : A) + M • (1 : A) = (2 * M) • (1 : A) by
      rw [← add_smul]; ring_nf] at h2
  obtain ⟨a', ha'⟩ := exists_corner_lift_nonneg c hc hcen horth d' hd'nn hd'c
    (by linarith : (0 : ℝ) ≤ 2 * M) hd'M
  refine ⟨a' - M • (1 : A), fun i => ?_⟩
  rw [mul_sub, ha' i, hcm i]
  change d i + M • c i - M • c i = d i
  abel

/-- **67IV** (`central-projections-sums`, vn.tex:3408, Exercise), part 2:
given a family of central projections `(cᵢ)` with `∑ᵢ cᵢ = 1` (pairwise
orthogonal, supremum `1`), `a ↦ (cᵢa)ᵢ` is an nmiu-isomorphism
`A ≅ ⊕ᵢ cᵢA` — here in the concrete form that carries the bijectivity:
every norm-bounded choice of elements of the corners is uniquely of the form
`(cᵢa)ᵢ`.  The nmiu-isomorphism itself is `central_projections_sums_2_iso`
below, which is this statement plus `famCompress`. -/
theorem central_projections_sums_2 {ι : Type*} (c : ι → A)
    (hc : ∀ i, IsStarProjection (c i) ∧ IsCentral A (c i))
    (horth : Pairwise fun i j => c i * c j = 0)
    (hsum : projSup (Set.range c) = 1)
    (b : ι → A) (hb : ∀ i, c i * b i = b i)
    (hbdd : BddAbove (Set.range fun i => ‖b i‖)) :
    ∃! a : A, ∀ i, c i * a = b i := by
  obtain ⟨M₀, hM₀⟩ := hbdd
  have hM : ∀ i, ‖b i‖ ≤ max M₀ 0 := fun i =>
    le_trans (hM₀ ⟨i, rfl⟩) (le_max_left _ _)
  have hM0 : (0 : ℝ) ≤ max M₀ 0 := le_max_right _ _
  set M : ℝ := max M₀ 0 with hMdef
  have hcp : ∀ i, IsStarProjection (c i) := fun i => (hc i).1
  have hcc : ∀ i, IsCentral A (c i) := fun i => (hc i).2
  have hbs : ∀ i, c i * star (b i) = star (b i) := by
    intro i
    have h := congrArg star (hb i)
    rw [star_mul, (hcp i).isSelfAdjoint.star_eq] at h
    rw [hcc i (star (b i))]; exact h
  -- real and imaginary parts
  set h : ι → A := fun i => ((2 : ℂ)⁻¹) • (b i + star (b i)) with hhdef
  set k : ι → A := fun i => (Complex.I / 2) • (star (b i) - b i) with hkdef
  have hhsa : ∀ i, IsSelfAdjoint (h i) := by
    intro i
    change star (((2 : ℂ)⁻¹) • (b i + star (b i))) = _
    rw [star_smul, star_add, star_star]
    simp [hhdef, add_comm]
  have hksa : ∀ i, IsSelfAdjoint (k i) := by
    intro i
    change star ((Complex.I / 2) • (star (b i) - b i)) = _
    rw [star_smul, star_sub, star_star]
    rw [show star (Complex.I / 2) = -(Complex.I / 2) by
      simp [Complex.ext_iff]; norm_num]
    rw [hkdef]
    change (-(Complex.I / 2)) • (b i - star (b i)) = (Complex.I / 2) • (star (b i) - b i)
    rw [neg_smul, ← smul_neg]
    congr 1
    abel
  have hhc : ∀ i, c i * h i = h i := by
    intro i; change c i * (((2 : ℂ)⁻¹) • (b i + star (b i))) = _
    rw [mul_smul_comm, mul_add, hb i, hbs i]
  have hkc : ∀ i, c i * k i = k i := by
    intro i; change c i * ((Complex.I / 2) • (star (b i) - b i)) = _
    rw [mul_smul_comm, mul_sub, hb i, hbs i]
  have hhM : ∀ i, ‖h i‖ ≤ M := by
    intro i
    change ‖((2 : ℂ)⁻¹) • (b i + star (b i))‖ ≤ M
    rw [norm_smul]
    have := norm_add_le (b i) (star (b i))
    rw [norm_star] at this
    have h2 : ‖((2 : ℂ)⁻¹)‖ = 2⁻¹ := by norm_num
    rw [h2]
    have := hM i
    nlinarith [norm_nonneg (b i), norm_add_le (b i) (star (b i))]
  have hkM : ∀ i, ‖k i‖ ≤ M := by
    intro i
    change ‖(Complex.I / 2) • (star (b i) - b i)‖ ≤ M
    rw [norm_smul]
    have h2 : ‖Complex.I / 2‖ = 2⁻¹ := by
      rw [norm_div, Complex.norm_I]; norm_num
    rw [h2]
    have h3 := norm_sub_le (star (b i)) (b i)
    rw [norm_star] at h3
    have := hM i
    nlinarith [norm_nonneg (b i)]
  have hdec : ∀ i, h i + Complex.I • k i = b i := by
    intro i
    change ((2 : ℂ)⁻¹) • (b i + star (b i)) +
      Complex.I • ((Complex.I / 2) • (star (b i) - b i)) = b i
    rw [smul_smul, show Complex.I * (Complex.I / 2) = -(2 : ℂ)⁻¹ by
      rw [div_eq_mul_inv, ← mul_assoc, Complex.I_mul_I]; ring]
    rw [neg_smul, ← smul_neg, ← smul_add]
    rw [show (b i + star (b i)) + -(star (b i) - b i) = (2 : ℂ) • b i by
      rw [two_smul]; abel]
    rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
  obtain ⟨ah, hah⟩ := exists_corner_lift_selfAdjoint c hcp hcc horth h hhsa hhc hM0 hhM
  obtain ⟨ak, hak⟩ := exists_corner_lift_selfAdjoint c hcp hcc horth k hksa hkc hM0 hkM
  refine ⟨ah + Complex.I • ak, fun i => ?_, ?_⟩
  · rw [mul_add, mul_smul_comm, hah i, hak i]
    exact hdec i
  · intro y hy
    have hzero : ∀ i, c i * (y - (ah + Complex.I • ak)) = 0 := by
      intro i
      rw [mul_sub, hy i, mul_add, mul_smul_comm, hah i, hak i, hdec i, sub_self]
    exact sub_eq_zero.mp (central_family_separating c hcp hsum hzero)

/-! ### **67IV**.2's nmiu-isomorphism `𝒜 ≅ ⊕ᵢ cᵢ𝒜` -/

section FamilyCorner

variable {ι : Type*} (c : ι → CentralProj A) [∀ i, Nontrivial ((c i).sub)]

/-- `a ↦ (cᵢa)ᵢ : A → ⊕ᵢ cᵢA`, an nmiu-map.  The family `(cᵢa)ᵢ` is
norm-bounded by `‖a‖` (each `cᵢ` is a projection, so `‖cᵢ‖ ≤ 1`), hence lies
in `lp _ ∞`; the algebra operations, the unit and the order of `lp _ ∞` are
all pointwise, so each field reduces to the corresponding field of
`CentralProj.compress`. -/
noncomputable def famCompress : NMIUMap A (lp (fun i => (c i).sub) ∞) where
  toStarAlgHom :=
    { toFun := fun a => ⟨fun i => (c i).compress a, by
        refine memℓp_infty ⟨‖a‖, ?_⟩
        rintro _ ⟨i, rfl⟩
        show ‖((c i).val * a : A)‖ ≤ ‖a‖
        calc ‖((c i).val * a : A)‖ ≤ ‖((c i).val : A)‖ * ‖a‖ := norm_mul_le _ _
          _ ≤ 1 * ‖a‖ := by
              gcongr
              exact norm_le_one_of_mem_effects ⟨(c i).isProj.nonneg, (c i).isProj.le_one⟩
          _ = ‖a‖ := one_mul _⟩
      map_one' := by
        refine lp.ext (funext fun i => ?_)
        show (c i).compress 1 = (1 : lp (fun i => (c i).sub) ∞) i
        rw [lp.infty_coeFn_one]
        exact map_one (c i).compress.toStarAlgHom
      map_mul' := fun a b => by
        refine lp.ext (funext fun i => ?_)
        show (c i).compress (a * b) = ((_ : lp (fun i => (c i).sub) ∞) * _) i
        rw [lp.infty_coeFn_mul]
        exact map_mul (c i).compress.toStarAlgHom a b
      map_zero' := by
        refine lp.ext (funext fun i => ?_)
        show (c i).compress 0 = (0 : lp (fun i => (c i).sub) ∞) i
        rw [lp.coeFn_zero]
        exact map_zero (c i).compress.toStarAlgHom
      map_add' := fun a b => by
        refine lp.ext (funext fun i => ?_)
        show (c i).compress (a + b) = ((_ : lp (fun i => (c i).sub) ∞) + _) i
        rw [lp.coeFn_add]
        exact map_add (c i).compress.toStarAlgHom a b
      commutes' := fun r => by
        refine lp.ext (funext fun i => ?_)
        show (c i).compress (algebraMap ℂ A r) = algebraMap ℂ ((c i).sub) r
        exact (c i).compress.toStarAlgHom.commutes r
      map_star' := fun a => by
        refine lp.ext (funext fun i => ?_)
        show (c i).compress (star a) = (star (_ : lp (fun i => (c i).sub) ∞)) i
        rw [lp.coeFn_star]
        exact map_star (c i).compress.toStarAlgHom a }
  preservesDirSups' := by
    intro D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      rw [lp_infty_le_iff]
      intro i
      exact ((c i).compress.preservesDirSups' D s hne hdir hlub).1 ⟨d, hd, rfl⟩
    · intro u hu
      rw [lp_infty_le_iff]
      intro i
      refine ((c i).compress.preservesDirSups' D s hne hdir hlub).2 ?_
      rintro _ ⟨d, hd, rfl⟩
      exact (lp_infty_le_iff _ _).mp (hu ⟨d, hd, rfl⟩) i

@[simp] theorem famCompress_coe (a : A) (i : ι) :
    (((famCompress c a : lp (fun i => (c i).sub) ∞) : ∀ i, (c i).sub) i : A)
      = (c i).val * a := rfl

/-- **67IV** (`central-projections-sums`, vn.tex:3408, Exercise), part 2, in
the shape the point asks for: given a family of central projections `(cᵢ)`
with `∑ᵢcᵢ = 1` (pairwise orthogonal with join `1`, equivalent by
**56XVIII**), `a ↦ (cᵢa)ᵢ` is an **nmiu-isomorphism** `A → ⊕ᵢ cᵢA`.

`famCompress` supplies the nmiu-map — multiplicativity, involutivity,
unitality, `ℂ`-linearity and normality are its `NMIUMap` fields — and
bijectivity is `central_projections_sums_2`: surjectivity is the existence
half applied to `bᵢ = (yᵢ : A)`, which is norm-bounded by `‖y‖`, and
injectivity is `central_family_separating`.

The `[∀ i, Nontrivial ((c i).sub)]` binder (i.e. `cᵢ ≠ 0`) is **Mathlib's,
not the thesis's**: it is what Mathlib's unital normed-ring instance on
`lp _ ∞` requires — see the note at the head of `A/VN/Basic`'s `DirectSum`
section, where the same binder is discussed and left. -/
theorem central_projections_sums_2_iso
    (horth : Pairwise fun i j => (c i).val * (c j).val = 0)
    (hsum : projSup (Set.range fun i => (c i).val) = 1) :
    ∃ Φ : NMIUMap A (lp (fun i => (c i).sub) ∞),
      Function.Bijective ⇑Φ ∧
        ∀ (a : A) (i : ι),
          (((Φ a : lp (fun i => (c i).sub) ∞) : ∀ i, (c i).sub) i : A)
            = (c i).val * a := by
  refine ⟨famCompress c, ⟨?_, ?_⟩, fun _ _ => rfl⟩
  · intro a b hab
    have h : ∀ i, (c i).val * (a - b) = 0 := by
      intro i
      have h1 : (c i).val * a = (c i).val * b :=
        congrArg (fun z : lp (fun i => (c i).sub) ∞ =>
          (((z : ∀ i, (c i).sub) i : (c i).sub) : A)) hab
      rw [mul_sub, h1, sub_self]
    exact sub_eq_zero.mp
      (central_family_separating (fun i => (c i).val) (fun i => (c i).isProj) hsum h)
  · intro y
    set b : ι → A := fun i => (((y : ∀ i, (c i).sub) i : (c i).sub) : A) with hb
    have hbc : ∀ i, (c i).val * b i = b i := fun i => ((y : ∀ i, (c i).sub) i).2
    have hbdd : BddAbove (Set.range fun i => ‖b i‖) := by
      refine ⟨‖y‖, ?_⟩
      rintro _ ⟨i, rfl⟩
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero y i
    obtain ⟨a, ha, -⟩ := central_projections_sums_2 (fun i => (c i).val)
      (fun i => ⟨(c i).isProj, (c i).isCentral⟩) horth hsum b hbc hbdd
    exact ⟨a, lp.ext (funext fun i => Subtype.ext (ha i))⟩

end FamilyCorner

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

/-- Auxiliary: the supremum of a set of *central* projections is again
central.  The argument is the one of **68I**: `⌈b*cb⌉ = ⋃_{p∈S} ⌈b*pb⌉ ≤ c`
by **60IX**.2 (each `⌈b*pb⌉ ≤ p` because `p` is central), so `cbc = cb`; and
`bc = cbc` follows by taking adjoints. -/
theorem projSup_isCentral {S : Set A} (hSproj : ∀ p ∈ S, IsStarProjection p)
    (hScentral : ∀ p ∈ S, IsCentral A p) : IsCentral A (projSup S) := by
  obtain ⟨hcproj, hcub, -⟩ := projSup_spec hSproj
  set c : A := projSup S with hcdef
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
    have h3 : suppProj (c * b) ≤ c := by
      rw [suppProj, e1]
      refine le_of_eq_of_le (?_ : ceil (star b * c * b) = _)
        ((projSup_spec himgproj).2.2 c hcproj ?_)
      · exact h2
      · rintro _ ⟨p, hp, rfl⟩
        refine le_trans ?_ (hcub p hp)
        show ceil (star b * p * b) ≤ p
        refine (ceil_le_iff (star_left_conjugate_nonneg (hSproj p hp).nonneg b)
          (hSproj p hp)).mpr ?_
        calc star b * p * b * p = star b * p * (b * p) := by noncomm_ring
          _ = star b * p * (p * b) := by rw [← hScentral p hp b]
          _ = star b * (p * p) * b := by noncomm_ring
          _ = star b * p * b := by rw [(hSproj p hp).isIdempotentElem.eq]
    exact mul_eq_of_suppProj_le hcproj h3
  intro b
  have h4 : c * b * c = b * c := by
    have h := congrArg star (hkey (star b))
    simp only [star_mul, star_star, hcproj.isSelfAdjoint.star_eq] at h
    rw [← mul_assoc] at h
    exact h
  rw [← hkey b, h4]

/-- Auxiliary: `⌈⌈x⌉⌉ ≤ r` with `r` a projection gives `rx = x`. -/
private theorem mul_eq_of_cceil_le {x r : A} (hr : IsStarProjection r)
    (h : cceil x ≤ r) : r * x = x := by
  obtain ⟨⟨h1, -, h3⟩, -⟩ := cceil_isLeast x
  calc r * x = r * (cceil x * x) := by rw [h3]
    _ = r * cceil x * x := by noncomm_ring
    _ = cceil x * x := by rw [(proj_le_iff_mul_left h1 hr).mp h]
    _ = x := h3

/-- Auxiliary: for a *central* projection `p`, conjugation by `p` is
multiplication by `p`. -/
private theorem conj_central_proj {p : A} (hp : IsStarProjection p)
    (hpc : IsCentral A p) (x : A) : star p * x * p = p * x := by
  rw [hp.isSelfAdjoint.star_eq]
  calc p * x * p = p * (p * x) := by rw [mul_assoc, ← hpc x]
    _ = p * p * x := by noncomm_ring
    _ = p * x := by rw [hp.isIdempotentElem.eq]

/-- Auxiliary: the complement of a central projection is central. -/
private theorem isCentral_one_sub {p : A} (hpc : IsCentral A p) :
    IsCentral A (1 - p) := fun x => by
  rw [sub_mul, mul_sub, one_mul, mul_one, hpc x]

/-- Auxiliary: `⌈⌈·⌉⌉` is monotone on the positive cone.  If `0 ≤ a ≤ b` then
`(1−⌈⌈b⌉⌉)a(1−⌈⌈b⌉⌉) = 0`, whence `⌈⌈b⌉⌉a = a`. -/
private theorem cceil_mono {a b : A} (ha : 0 ≤ a) (hab : a ≤ b) :
    cceil a ≤ cceil b := by
  obtain ⟨⟨hp, hpc, hpb⟩, -⟩ := cceil_isLeast b
  set p : A := cceil b with hpdef
  have hq : IsStarProjection (1 - p) := hp.one_sub
  have hqc : IsCentral A (1 - p) := isCentral_one_sub hpc
  have hb0 : (1 - p) * b = 0 := by rw [sub_mul, one_mul, hpb, sub_self]
  have hle : star (1 - p) * a * (1 - p) ≤ star (1 - p) * b * (1 - p) :=
    star_left_conjugate_le_conjugate hab (1 - p)
  rw [conj_central_proj hq hqc a, conj_central_proj hq hqc b, hb0] at hle
  have ha0 : (1 - p) * a = 0 :=
    le_antisymm hle
      (by rw [← conj_central_proj hq hqc a]; exact star_left_conjugate_nonneg ha (1 - p))
  refine (cceil_isLeast a).2 ⟨hp, hpc, ?_⟩
  rw [sub_mul, one_mul] at ha0
  exact (sub_eq_zero.mp ha0).symm

/-- Auxiliary: `⌈⌈a⌉⌉ = ⌈⌈⌈a⌉⌉⌉` for positive `a` — a central projection
absorbs `a` iff it absorbs `⌈a⌉`. -/
private theorem cceil_ceil {a : A} (ha : 0 ≤ a) : cceil a = cceil (ceil a) := by
  refine cceil_congr fun p hp hpc => ?_
  constructor
  · intro h
    exact (proj_le_iff_mul_left (ceil_spec ha).1 hp).mp
      ((ceil_le_iff ha hp).mpr (by rw [← hpc a]; exact h))
  · intro h
    rw [hpc a]
    exact (ceil_le_iff ha hp).mp ((proj_le_iff_mul_left (ceil_spec ha).1 hp).mpr h)

/-- **68IV** (`cceil-basic`, vn.tex:3490, Exercise), part 2:
`⌈⌈⋁D⌉⌉ = ⋃_{d∈D} ⌈⌈d⌉⌉` for bounded directed `D` of *positive* elements;
`⌈⌈⋃E⌉⌉ = ⋃_{e∈E} ⌈⌈e⌉⌉` for sets of projections `E`; and
`⌈⌈a+b⌉⌉ = ⌈⌈⌈a⌉ ∪ ⌈b⌉⌉⌉ = ⌈⌈a⌉⌉ ∪ ⌈⌈b⌉⌉` for positive `a`, `b`.

(Erratum `parsec-680.40` — positivity in the first and third clauses — **has
been incorporated into vn.tex**: 68IV.2 now reads "for any bounded directed
subset of positive elements of `𝒜`" and "for all positive `a,b ∈ 𝒜`", which
is what is assumed here.  Without positivity both clauses were false, central
support being monotone on positive elements only: `D = {−1, 0}` is directed
and bounded with `⋁D = 0`, so `⌈⌈⋁D⌉⌉ = 0` while `⌈⌈−1⌉⌉ ∪ ⌈⌈0⌉⌉ = 1`; and
`a = 1`, `b = −1` gives `⌈⌈0⌉⌉ = 0` against `1`.) -/
theorem cceil_basic_2 (D : Set (selfAdjoint A)) (s : selfAdjoint A)
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hs : IsLUB D s)
    (hDpos : ∀ d ∈ D, 0 ≤ (d : A))
    (E : Set A) (hE : ∀ e ∈ E, IsStarProjection e) (a b : A) (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    cceil (s : A) = projSup ((fun d : selfAdjoint A => cceil (d : A)) '' D) ∧
      cceil (projSup E) = projSup (cceil '' E) ∧
      cceil (a + b) = cceil (projSup {ceil a, ceil b}) ∧
      cceil (projSup {ceil a, ceil b}) = projSup {cceil a, cceil b} := by
  have hcp : ∀ x : A, IsStarProjection (cceil x) := fun x => (cceil_isLeast x).1.1
  have hcc : ∀ x : A, IsCentral A (cceil x) := fun x => (cceil_isLeast x).1.2.1
  -- the second clause, for an arbitrary set of projections; used again below
  have key2 : ∀ F : Set A, (∀ e ∈ F, IsStarProjection e) →
      cceil (projSup F) = projSup (cceil '' F) := by
    intro F hF
    have hFcp : ∀ x ∈ cceil '' F, IsStarProjection x := by
      rintro _ ⟨e, -, rfl⟩; exact hcp e
    have hFcc : ∀ x ∈ cceil '' F, IsCentral A x := by
      rintro _ ⟨e, -, rfl⟩; exact hcc e
    obtain ⟨hrproj, hrub, hrleast⟩ := projSup_spec hFcp
    have hrc : IsCentral A (projSup (cceil '' F)) := projSup_isCentral hFcp hFcc
    obtain ⟨hsproj, hsub, hsleast⟩ := projSup_spec hF
    refine le_antisymm ((cceil_isLeast (projSup F)).2 ⟨hrproj, hrc, ?_⟩) ?_
    · exact (proj_le_iff_mul_left hsproj hrproj).mp
        (hsleast _ hrproj fun e he => (proj_le_iff_mul_left (hF e he) hrproj).mpr
          (mul_eq_of_cceil_le hrproj (hrub _ ⟨e, he, rfl⟩)))
    · refine hrleast _ (hcp _) ?_
      rintro _ ⟨e, he, rfl⟩
      exact cceil_mono (hF e he).nonneg (hsub e he)
  -- clause 1: `⌈⌈⋁D⌉⌉ = ⋃_{d∈D}⌈⌈d⌉⌉`
  have hDcp : ∀ x ∈ (fun d : selfAdjoint A => cceil (d : A)) '' D,
      IsStarProjection x := by rintro _ ⟨d, -, rfl⟩; exact hcp _
  have hDcc : ∀ x ∈ (fun d : selfAdjoint A => cceil (d : A)) '' D,
      IsCentral A x := by rintro _ ⟨d, -, rfl⟩; exact hcc _
  obtain ⟨hrproj, hrub, hrleast⟩ := projSup_spec hDcp
  set r : A := projSup ((fun d : selfAdjoint A => cceil (d : A)) '' D) with hrdef
  have hrc : IsCentral A r := projSup_isCentral hDcp hDcc
  have hq : IsStarProjection (1 - r) := hrproj.one_sub
  have hqc : IsCentral A (1 - r) := isCentral_one_sub hrc
  have hzero : ∀ d ∈ D, (conjPMap (1 - r)) (d : A) = 0 := by
    intro d hd
    show star (1 - r) * (d : A) * (1 - r) = 0
    rw [conj_central_proj hq hqc, sub_mul, one_mul,
      mul_eq_of_cceil_le hrproj (hrub _ ⟨d, hd, rfl⟩), sub_self]
  have hlub := conjPMap_preservesDirSups (1 - r) D s hne hdir hs
  have himg : ((fun d : selfAdjoint A => (conjPMap (1 - r)) (d : A)) '' D)
      = ({0} : Set A) := by
    obtain ⟨d0, hd0⟩ := hne
    exact Set.eq_singleton_iff_unique_mem.mpr
      ⟨⟨d0, hd0, hzero d0 hd0⟩, by rintro _ ⟨d, hd, rfl⟩; exact hzero d hd⟩
  rw [himg] at hlub
  have hs0 : star (1 - r) * (s : A) * (1 - r) = 0 := hlub.unique isLUB_singleton
  have hrs : r * (s : A) = (s : A) := by
    rw [conj_central_proj hq hqc, sub_mul, one_mul] at hs0
    exact (sub_eq_zero.mp hs0).symm
  have h1 : cceil (s : A) = r :=
    le_antisymm ((cceil_isLeast (s : A)).2 ⟨hrproj, hrc, hrs⟩)
      (hrleast _ (hcp _) (by
        rintro _ ⟨d, hd, rfl⟩
        exact cceil_mono (hDpos d hd) (Subtype.coe_le_coe.mpr (hs.1 hd))))
  -- clauses 3 and 4
  have hFproj : ∀ e ∈ ({ceil a, ceil b} : Set A), IsStarProjection e := by
    rintro e (rfl | rfl)
    · exact (ceil_spec ha).1
    · exact (ceil_spec hb).1
  have h4 : cceil (projSup ({ceil a, ceil b} : Set A))
      = projSup ({cceil a, cceil b} : Set A) := by
    rw [key2 _ hFproj, Set.image_pair, ← cceil_ceil ha, ← cceil_ceil hb]
  have hPcp : ∀ x ∈ ({cceil a, cceil b} : Set A), IsStarProjection x := by
    rintro x (rfl | rfl) <;> exact hcp _
  have hPcc : ∀ x ∈ ({cceil a, cceil b} : Set A), IsCentral A x := by
    rintro x (rfl | rfl) <;> exact hcc _
  obtain ⟨hr'proj, hr'ub, hr'least⟩ := projSup_spec hPcp
  have hr'c : IsCentral A (projSup ({cceil a, cceil b} : Set A)) :=
    projSup_isCentral hPcp hPcc
  have h3 : cceil (a + b) = projSup ({cceil a, cceil b} : Set A) := by
    refine le_antisymm ((cceil_isLeast (a + b)).2 ⟨hr'proj, hr'c, ?_⟩) ?_
    · rw [mul_add, mul_eq_of_cceil_le hr'proj (hr'ub _ (Set.mem_insert _ _)),
        mul_eq_of_cceil_le hr'proj (hr'ub _ (Set.mem_insert_of_mem _ rfl))]
    · refine hr'least _ (hcp _) ?_
      rintro x (rfl | rfl)
      · exact cceil_mono ha (le_add_of_nonneg_right hb)
      · exact cceil_mono hb (le_add_of_nonneg_left ha)
  exact ⟨h1, key2 E hE, h3.trans h4.symm, h4⟩

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

/-- **56I** (`vna-ceil`, vn.tex:2362) in the *powers* form: for an effect
`a`, `1 - (1-a)^{2ⁿ} ↗ ⌈a⌉`.

This is the ERRATA 69III repair of the proof of **69II**: vn.tex 69III
obtains `⌈a⌉ ∈ 𝒟` from the *roots* formula `⌈a⌉ = ⋁ₙ a^{1/2ⁿ}`
(`vna_ceil_sup`), which needs every `a^{1/2ⁿ} ∈ 𝒟` — not an ideal-theoretic
fact (in `C[0,1]`, `x·C[0,1]` contains `x` but not `√x`).  Powers work
instead, and the argument is elementary: with `p = ⌈a⌉` and `x = p - a` one
has `(1-p)x = x(1-p) = 0`, hence `(1-a)^{n+1} = (1-p) + x^{n+1}` and so
`1 - (1-a)ⁿ = p - xⁿ`; and `⌊x⌋ = 0` (a projection `q ≤ p - a` would give
`a ≤ p - q`, a projection strictly below `⌈a⌉`), so `xⁿ ↘ 0` by **56VI**
`vna_floor`. -/
theorem ceil_isLUB_one_sub_pow {a : A} (ha : a ∈ effects A) :
    IsLUB (Set.range fun n : ℕ => 1 - (1 - a) ^ (2 ^ n)) (ceil a) := by
  have hpproj : IsStarProjection (ceil a) := (ceil_spec ha.1).1
  have hap : a ≤ ceil a := (vna_ceil a ha).1.2
  have hpa : ceil a * a = a := ((ceil_basic_1 a (ceil a) ha.1 hpproj).out 2 0).mp le_rfl
  have hap' : a * ceil a = a := ((ceil_basic_1 a (ceil a) ha.1 hpproj).out 2 1).mp le_rfl
  set p : A := ceil a with hpdef
  set x : A := p - a with hxdef
  have hx0 : (0 : A) ≤ x := sub_nonneg.mpr hap
  have hxp : x ≤ p := sub_le_self p ha.1
  have hxeff : x ∈ effects A := ⟨hx0, hxp.trans hpproj.le_one⟩
  -- `(1-p)x = x(1-p) = 0`
  have hlx : (1 - p) * x = 0 := by
    rw [hxdef, mul_sub, sub_mul, one_mul, hpproj.isIdempotentElem.eq, sub_mul,
      one_mul, hpa]
    abel
  have hxl : x * (1 - p) = 0 := by
    rw [hxdef, sub_mul, mul_sub, mul_one, hpproj.isIdempotentElem.eq, mul_sub,
      mul_one, hap']
    abel
  -- `(1-a)^(n+1) = (1-p) + x^(n+1)`
  have hkey : ∀ n : ℕ, (1 - a) ^ (n + 1) = (1 - p) + x ^ (n + 1) := by
    intro n
    induction n with
    | zero => rw [pow_one, pow_one, hxdef]; abel
    | succ m ih =>
        have hxm : x ^ (m + 1) * (1 - p) = 0 := by
          rw [pow_succ, mul_assoc, hxl, mul_zero]
        calc (1 - a) ^ (m + 1 + 1) = (1 - a) ^ (m + 1) * (1 - a) := by rw [pow_succ]
          _ = ((1 - p) + x ^ (m + 1)) * ((1 - p) + x) := by
              rw [ih]; congr 1; rw [hxdef]; abel
          _ = (1 - p) * (1 - p) + (1 - p) * x + x ^ (m + 1) * (1 - p)
                + x ^ (m + 1) * x := by noncomm_ring
          _ = (1 - p) + x ^ (m + 1 + 1) := by
              rw [hpproj.one_sub.isIdempotentElem.eq, hlx, hxm, ← pow_succ]; abel
  -- `⌊x⌋ = 0`
  have hfl : floor x = 0 := by
    obtain ⟨⟨hqproj, hqle⟩, -⟩ := floor_isGreatest hxeff
    have hqp : floor x ≤ p := hqle.trans hxp
    have hpq : IsStarProjection (p - floor x) :=
      projection_below_projection _ p hqproj hpproj hqp
    have haq : a ≤ p - floor x := le_sub_comm.mp (hxdef ▸ hqle)
    have hle := (vna_ceil a ha).2 ⟨hpq, haq⟩
    have hq0 : floor x ≤ 0 := by
      have h2 : p + floor x ≤ p + 0 := by rw [add_zero]; exact le_sub_iff_add_le.mp hle
      exact (add_le_add_iff_left p).mp h2
    exact le_antisymm hq0 hqproj.nonneg
  have hglb : IsGLB (Set.range fun n : ℕ => x ^ 2 ^ n) 0 := by
    have h := (vna_floor x hxeff).2
    rwa [hfl] at h
  -- rewrite the family
  have hrw : ∀ n : ℕ, 1 - (1 - a) ^ 2 ^ n = p - x ^ 2 ^ n := by
    intro n
    obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 ^ n = m + 1 :=
      ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
    rw [hm, hkey m]
    abel
  have hrange : (Set.range fun n : ℕ => 1 - (1 - a) ^ 2 ^ n)
      = Set.range fun n : ℕ => p - x ^ 2 ^ n := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩; exact ⟨n, (hrw n).symm⟩
    · rintro ⟨n, rfl⟩; exact ⟨n, hrw n⟩
  rw [hrange]
  constructor
  · rintro _ ⟨n, rfl⟩
    exact sub_le_self p (pow_mem_effects hxeff (2 ^ n)).1
  · intro u hu
    have h1 : ∀ n : ℕ, p - u ≤ x ^ 2 ^ n := fun n => sub_le_comm.mp (hu ⟨n, rfl⟩)
    have h2 : p - u ≤ 0 := hglb.2 (by rintro _ ⟨n, rfl⟩; exact h1 n)
    exact sub_nonpos.mp h2

/-- **69III** (the proof of **69II**), first paragraph, repaired: `⌈a⌉ ∈ 𝒟`
for an effect `a` of a two-sided ideal `𝒟` closed under bounded directed
suprema.  Each `1 - (1-a)^{2ⁿ} = (∑_{i<2ⁿ}(1-a)^i)·a` lies in `𝒟` because
`a` does, and these increase to `⌈a⌉` by `ceil_isLUB_one_sub_pow`. -/
private theorem ceil_mem_ideal_of_effect (D : TwoSidedIdeal A)
    (hD : ∀ (S : Set (selfAdjoint A)) (s : selfAdjoint A),
      (∀ y ∈ S, (y : A) ∈ D) → S.Nonempty → DirectedOn (· ≤ ·) S →
        IsLUB S s → (s : A) ∈ D)
    {a : A} (ha : a ∈ effects A) (haD : a ∈ D) : ceil a ∈ D := by
  have hasa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha.1
  have h1a : (1 : A) - a ∈ effects A := effect_orthosupplement a ha
  have hsa : ∀ n : ℕ, IsSelfAdjoint ((1 : A) - (1 - a) ^ n) := fun n =>
    (IsSelfAdjoint.one A).sub (((IsSelfAdjoint.one A).sub hasa).pow n)
  have hmono : Monotone (fun n : ℕ => (⟨1 - (1 - a) ^ 2 ^ n, hsa _⟩ : selfAdjoint A)) := by
    intro m n hmn
    refine Subtype.coe_le_coe.mp ?_
    exact sub_le_sub_left
      (pow_antitone_of_mem_effects h1a (Nat.pow_le_pow_right (by norm_num) hmn)) 1
  refine hD (Set.range fun n : ℕ => (⟨1 - (1 - a) ^ 2 ^ n, hsa _⟩ : selfAdjoint A))
    ⟨ceil a, ((ceil_spec ha.1).1).isSelfAdjoint⟩ ?_ ⟨_, 0, rfl⟩ ?_ ?_
  · rintro _ ⟨n, rfl⟩
    show (1 : A) - (1 - a) ^ 2 ^ n ∈ D
    have h := geom_sum_mul_neg ((1 : A) - a) (2 ^ n)
    rw [sub_sub_cancel] at h
    rw [← h]
    exact D.mul_mem_left _ _ haD
  · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ⟨_, ⟨max m n, rfl⟩, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩
  · refine isLUB_sa_of_isLUB ?_
    have himg : Subtype.val '' (Set.range fun n : ℕ =>
        (⟨1 - (1 - a) ^ 2 ^ n, hsa _⟩ : selfAdjoint A))
        = Set.range fun n : ℕ => (1 : A) - (1 - a) ^ 2 ^ n := by
      rw [← Set.range_comp]; rfl
    rw [himg]
    exact ceil_isLUB_one_sub_pow ha

/-- `ceil_mem_ideal_of_effect` for an arbitrary positive element of `𝒟`,
by rescaling (**59I**). -/
private theorem ceil_mem_ideal (D : TwoSidedIdeal A)
    (hD : ∀ (S : Set (selfAdjoint A)) (s : selfAdjoint A),
      (∀ y ∈ S, (y : A) ∈ D) → S.Nonempty → DirectedOn (· ≤ ·) S →
        IsLUB S s → (s : A) ∈ D)
    {b : A} (hb : 0 ≤ b) (hbD : b ∈ D) : ceil b ∈ D := by
  rcases eq_or_ne b 0 with rfl | hne
  · rw [ceil_zero]; exact D.zero_mem
  have hn : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hne
  have heff : (‖b‖⁻¹ : ℝ) • b ∈ effects A := by
    refine ⟨smul_nonneg (by positivity) hb, ?_⟩
    refine (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (smul_nonneg (by positivity) hb)).mp ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      inv_mul_cancel₀ (ne_of_gt hn)]
  have hmemD : (‖b‖⁻¹ : ℝ) • b ∈ D := by
    have : (‖b‖⁻¹ : ℝ) • b = ((‖b‖⁻¹ : ℂ) • (1 : A)) * b := by
      rw [smul_mul_assoc, one_mul, ← Complex.ofReal_inv, Complex.coe_smul]
    rw [this]
    exact D.mul_mem_left _ _ hbD
  have := ceil_mem_ideal_of_effect D hD heff hmemD
  rwa [ceil_smul hb (inv_pos.mpr hn)] at this

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
        IsGreatest {p : A | IsStarProjection p ∧ p ∈ D} c := by
  -- the second clause holds of *any* `c` with the stated property
  have hgreat : ∀ c : A, IsStarProjection c → IsCentral A c →
      (∀ a : A, a ∈ D ↔ c * a = a) →
      IsGreatest {p : A | IsStarProjection p ∧ p ∈ D} c := by
    intro c hc _ hchar
    refine ⟨⟨hc, (hchar c).mpr hc.isIdempotentElem.eq⟩, ?_⟩
    rintro p ⟨hp, hpD⟩
    exact (proj_le_iff_mul_left hp hc).mpr ((hchar p).mp hpD)
  refine ⟨?_, hgreat⟩
  -- `𝒟 ∩ [0,1]` is nonempty, bounded and — by the repair above — directed
  have hzero : (⟨0, IsSelfAdjoint.zero A⟩ : selfAdjoint A) ∈
      {y : selfAdjoint A | (y : A) ∈ D ∧ (y : A) ∈ effects A} :=
    ⟨D.zero_mem, le_rfl, zero_le_one⟩
  have hEne : ({y : selfAdjoint A | (y : A) ∈ D ∧ (y : A) ∈ effects A}).Nonempty :=
    ⟨_, hzero⟩
  have hEbdd : BddAbove {y : selfAdjoint A | (y : A) ∈ D ∧ (y : A) ∈ effects A} := by
    refine ⟨⟨1, IsSelfAdjoint.one A⟩, fun y hy => ?_⟩
    exact hy.2.2
  have hEdir : DirectedOn (· ≤ ·)
      {y : selfAdjoint A | (y : A) ∈ D ∧ (y : A) ∈ effects A} := by
    rintro y ⟨hy1, hy2⟩ z ⟨hz1, hz2⟩
    have hsum : (0 : A) ≤ (y : A) + z := add_nonneg hy2.1 hz2.1
    have hsumD : ((y : A) + z) ∈ D := D.add_mem hy1 hz1
    have hcm : ceil ((y : A) + z) ∈ D := ceil_mem_ideal D hD hsum hsumD
    have hcp : IsStarProjection (ceil ((y : A) + z)) := (ceil_spec hsum).1
    refine ⟨⟨ceil ((y : A) + z), hcp.isSelfAdjoint⟩,
      ⟨hcm, hcp.nonneg, hcp.le_one⟩, Subtype.coe_le_coe.mp ?_, Subtype.coe_le_coe.mp ?_⟩
    · exact (vna_ceil _ hy2).1.2.trans
        (ceil_mono hy2.1 (le_add_of_nonneg_right hz2.1))
    · exact (vna_ceil _ hz2).1.2.trans
        (ceil_mono hz2.1 (le_add_of_nonneg_left hy2.1))
  obtain ⟨s, hs⟩ := VonNeumannAlgebra.isLUB_of_bddAbove_directed
    {y : selfAdjoint A | (y : A) ∈ D ∧ (y : A) ∈ effects A} hEne hEdir hEbdd
  have hcD : (s : A) ∈ D := hD _ s (fun y hy => hy.1) hEne hEdir hs
  have hc0 : (0 : A) ≤ (s : A) := by
    have := Subtype.coe_le_coe.mpr (hs.1 hzero)
    simpa using this
  have hc1 : (s : A) ≤ 1 := by
    have hub : (⟨1, IsSelfAdjoint.one A⟩ : selfAdjoint A) ∈ upperBounds
        {y : selfAdjoint A | (y : A) ∈ D ∧ (y : A) ∈ effects A} := by
      intro y hy; exact hy.2.2
    have := Subtype.coe_le_coe.mpr (hs.2 hub)
    simpa using this
  have hceff : (s : A) ∈ effects A := ⟨hc0, hc1⟩
  -- `c` is the greatest effect of `𝒟`
  have hgreatest : ∀ y : A, y ∈ D → y ∈ effects A → y ≤ (s : A) := by
    intro y hy1 hy2
    exact Subtype.coe_le_coe.mpr
      (hs.1 (show (⟨y, IsSelfAdjoint.of_nonneg hy2.1⟩ : selfAdjoint A) ∈ _ from ⟨hy1, hy2⟩))
  -- hence a projection, since `⌈c⌉ ∈ 𝒟 ∩ [0,1]` too
  have hcproj : IsStarProjection (s : A) := by
    have h1 : ceil (s : A) ∈ D := ceil_mem_ideal_of_effect D hD hceff hcD
    have hpp : IsStarProjection (ceil (s : A)) := (ceil_spec hc0).1
    have h3 : ceil (s : A) ≤ (s : A) := hgreatest _ h1 ⟨hpp.nonneg, hpp.le_one⟩
    have h4 : (s : A) ≤ ceil (s : A) := (vna_ceil _ hceff).1.2
    exact (le_antisymm h3 h4) ▸ hpp
  -- the claim: `a ∈ 𝒟` implies `ca = a` and `ac = a`
  have hclaim : ∀ a : A, a ∈ D → (s : A) * a = a ∧ a * (s : A) = a := by
    intro a haD
    have h1 : star a * a ∈ D := D.mul_mem_left _ _ haD
    have h2 : a * star a ∈ D := D.mul_mem_right _ _ haD
    have hq : suppProj a ∈ D := ceil_mem_ideal D hD (star_mul_self_nonneg a) h1
    have hr : rangeProj a ∈ D := ceil_mem_ideal D hD (mul_star_self_nonneg a) h2
    have hqproj : IsStarProjection (suppProj a) := (ceill_basic_1 a).1.1
    have hrproj : IsStarProjection (rangeProj a) := (ceill_basic_2 a).1.1
    have hqc : suppProj a ≤ (s : A) := hgreatest _ hq ⟨hqproj.nonneg, hqproj.le_one⟩
    have hrc : rangeProj a ≤ (s : A) := hgreatest _ hr ⟨hrproj.nonneg, hrproj.le_one⟩
    constructor
    · have hcr : (s : A) * rangeProj a = rangeProj a := (proj_le_iff_mul_left hrproj hcproj).mp hrc
      calc (s : A) * a = (s : A) * (rangeProj a * a) := by rw [(ceill_basic_2 a).1.2]
        _ = ((s : A) * rangeProj a) * a := by rw [mul_assoc]
        _ = rangeProj a * a := by rw [hcr]
        _ = a := (ceill_basic_2 a).1.2
    · have hqc' : suppProj a * (s : A) = suppProj a := (proj_le_iff_mul_right hqproj hcproj).mp hqc
      calc a * (s : A) = (a * suppProj a) * (s : A) := by rw [(ceill_basic_1 a).1.2]
        _ = a * (suppProj a * (s : A)) := by rw [mul_assoc]
        _ = a * suppProj a := by rw [hqc']
        _ = a := (ceill_basic_1 a).1.2
  have hchar : ∀ a : A, a ∈ D ↔ (s : A) * a = a := by
    intro a
    refine ⟨fun h => (hclaim a h).1, fun h => ?_⟩
    exact h ▸ D.mul_mem_right _ a hcD
  have hcentral : IsCentral A (s : A) := by
    intro b
    have h1 : (s : A) * (b * (s : A)) = b * (s : A) :=
      (hclaim (b * (s : A)) (D.mul_mem_left b _ hcD)).1
    have h2 : ((s : A) * b) * (s : A) = (s : A) * b :=
      (hclaim ((s : A) * b) (D.mul_mem_right _ b hcD)).2
    rw [← h2, mul_assoc, h1]
  refine ⟨(s : A), ⟨hcproj, hcentral, hchar⟩, ?_⟩
  rintro c' ⟨hc'proj, -, hc'char⟩
  have h1 : c' ∈ D := (hc'char c').mpr hc'proj.isIdempotentElem.eq
  have e1 : (s : A) * c' = c' := (hclaim c' h1).1
  have e2 : c' * (s : A) = (s : A) := (hc'char (s : A)).mp hcD
  have e3 : c' * (s : A) = c' := by
    have h := congrArg star e1
    rwa [star_mul, hc'proj.isSelfAdjoint.star_eq, hcproj.isSelfAdjoint.star_eq] at h
  rw [← e3, e2]

/-- **69IV** (`carrier-miu`, vn.tex:3611, Corollary): the carrier of an
nmiu-map `f : A → B` is central (`⌈f⌉ = ⌈⌈f⌉⌉`), and
`ker f = ⌈⌈f⌉⌉^⊥ A` (i.e. `f(a) = 0` iff `⌈f⌉·a = 0`).  (The carrier is
taken through any positive-map avatar `g` of `f`.)

The thesis gives no proof text: 69IV is a Corollary of **69II**
(`weakly_closed_ideal`), and that is the route taken here.  `ker f` is a
two-sided ideal closed under bounded directed suprema (`f` being
multiplicative, linear and normal), so 69II hands us a central projection
`c` with `ker f = c𝒜`, and `c` is the *greatest* projection of `ker f`.
That makes `c^⊥` the least projection `p` with `f(p^⊥) = 0`, i.e. `⌈f⌉`;
centrality and `ker f = ⌈f⌉^⊥𝒜` are then read off `c`. -/
theorem carrier_miu (f : NMIUMap A B) (g : A →ₚ[ℂ] B)
    (hg : PreservesDirSups ⇑g) (heq : ∀ a, g a = f a) :
    IsCentral A (carrier g hg) ∧
      ∀ a : A, f a = 0 ↔ carrier g hg * a = 0 := by
  -- `𝒟 = ker f`, a two-sided ideal
  set D : TwoSidedIdeal A := TwoSidedIdeal.ker f.toStarAlgHom with hDdef
  have hmemD : ∀ a : A, a ∈ D ↔ (f a : B) = 0 := fun a => TwoSidedIdeal.mem_ker _
  -- closed under bounded directed suprema, because `f` is normal and the
  -- image of `S` is `{0}`
  have hDsup : ∀ (S : Set (selfAdjoint A)) (s : selfAdjoint A),
      (∀ x ∈ S, (x : A) ∈ D) → S.Nonempty → DirectedOn (· ≤ ·) S →
        IsLUB S s → (s : A) ∈ D := by
    intro S s hS hne hdir hlub
    have h := f.preservesDirSups' S s hne hdir hlub
    have himg : (fun d : selfAdjoint A => (f.toStarAlgHom (d : A) : B)) '' S = {(0 : B)} := by
      refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨?_, ?_⟩
      · obtain ⟨x, hx⟩ := hne
        exact ⟨_, ⟨x, hx, rfl⟩⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact (hmemD _).mp (hS x hx)
    rw [himg] at h
    exact (hmemD _).mpr (le_antisymm (h.2 fun b hb => le_of_eq hb) (h.1 rfl))
  -- **69II**: `𝒟 = c𝒜` for a central projection `c`, the greatest in `𝒟`
  obtain ⟨⟨c, ⟨hcproj, hccentral, hcchar⟩, -⟩, hgreat⟩ := weakly_closed_ideal D hDsup
  have hcD : c ∈ D := (hcchar c).mpr hcproj.isIdempotentElem.eq
  -- `⌈f⌉ ≤ c^⊥`, since `f(c) = 0`
  have hle₁ : carrier g hg ≤ 1 - c := by
    refine (carrier_spec g hg).2.2 _ hcproj.one_sub ?_
    rw [sub_sub_cancel, heq]
    exact (hmemD c).mp hcD
  have hf0 : (f ((1 : A) - carrier g hg) : B) = 0 := by
    rw [← heq]; exact (carrier_spec g hg).2.1
  -- and `c^⊥ ≤ ⌈f⌉`, since `⌈f⌉^⊥` is a projection of `𝒟` and `c` is the
  -- greatest such
  have hle₂ : (1 : A) - c ≤ carrier g hg :=
    sub_le_comm.mp ((hgreat c hcproj hccentral hcchar).2
      ⟨(carrier_spec g hg).1.one_sub, (hmemD _).mpr hf0⟩)
  have hceq : carrier g hg = 1 - c := le_antisymm hle₁ hle₂
  refine ⟨?_, ?_⟩
  · rw [hceq]
    intro b
    rw [sub_mul, mul_sub, one_mul, mul_one, hccentral b]
  · intro a
    rw [hceq, ← hmemD a, hcchar a, sub_mul, one_mul, sub_eq_zero, eq_comm]

/-- **69IV** (`carrier-miu`, vn.tex:3611, Corollary), the point's other half:
`⌈f⌉ = ⌈⌈f⌉⌉` for an nmiu-map `f`.  It is immediate from the centrality that
`carrier_miu` establishes — a central projection is its own central support,
by the leastness of `⌈⌈·⌉⌉` in one direction and `⌈⌈p⌉⌉p = p` in the other —
but the equation itself had no declaration. -/
theorem carrier_eq_cceilMap (f : NMIUMap A B) (g : A →ₚ[ℂ] B)
    (hg : PreservesDirSups ⇑g) (heq : ∀ a, g a = f a) :
    carrier g hg = cceilMap g hg := by
  have hproj : IsStarProjection (carrier g hg) := (carrier_spec g hg).1
  have hcent : IsCentral A (carrier g hg) := (carrier_miu f g hg heq).1
  refine le_antisymm ?_ ((cceil_isLeast (carrier g hg)).2
    ⟨hproj, hcent, hproj.isIdempotentElem.eq⟩)
  exact (proj_le_iff_mul_left hproj (cceil_isLeast _).1.1).mpr
    (cceil_isLeast (carrier g hg)).1.2.2

/-- **69IVa** (`nmiu-factors`, vn.tex:3619, Exercise): an nmiu-map
`f : A → B` factors through the corner `⌈⌈f⌉⌉A` as an nmiu-surjection
`a ↦ ⌈⌈f⌉⌉a` followed by an nmiu-injection — here in the two elementwise
forms the factorisation amounts to: `f(a) = f(⌈f⌉a)` for all `a`, and
`f(a) = f(b)` iff `⌈f⌉a = ⌈f⌉b`.  The factorisation itself, with both maps
constructed as `NMIUMap`s, is `nmiu_factors_maps` below. -/
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

omit [VonNeumannAlgebra A] [VonNeumannAlgebra B] in
/-- Auxiliary: an nmiu-map is positive.  (`starAlgHom_nonneg` of `Basic.lean`
says the same, but is stated for two algebras in a *common* universe.) -/
theorem nmiu_nonneg (f : NMIUMap A B) {x : A} (hx : 0 ≤ x) : (0 : B) ≤ f x := by
  have hs : CFC.sqrt x * CFC.sqrt x = x := CFC.sqrt_mul_sqrt_self x hx
  have hsa : IsSelfAdjoint (CFC.sqrt x) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x)
  have hstar : ∀ y : A, (f (star y) : B) = star (f y) := fun y => map_star f.toStarAlgHom y
  have h : (f x : B) = star (f (CFC.sqrt x)) * f (CFC.sqrt x) :=
    calc (f x : B) = f (CFC.sqrt x * CFC.sqrt x) := by rw [hs]
      _ = f (CFC.sqrt x) * f (CFC.sqrt x) := map_mul f.toStarAlgHom _ _
      _ = star (f (CFC.sqrt x)) * f (CFC.sqrt x) := by
          rw [← hstar, hsa.star_eq]
  rw [h]
  exact star_mul_self_nonneg _

/-- Auxiliary: an nmiu-map as a positive linear map, so that `carrier` applies. -/
noncomputable def nmiuP (f : NMIUMap A B) : A →ₚ[ℂ] B where
  toFun := f
  map_add' := map_add f.toStarAlgHom
  map_smul' := map_smul f.toStarAlgHom
  monotone' := fun x y h => by
    have hsub : ∀ u v : A, (f (u - v) : B) = f u - f v := fun u v =>
      map_sub f.toStarAlgHom u v
    have h0 : (0 : B) ≤ f (y - x) := nmiu_nonneg f (sub_nonneg.mpr h)
    rw [hsub] at h0
    exact sub_nonneg.mp h0

omit [VonNeumannAlgebra A] [VonNeumannAlgebra B] in
@[simp] theorem nmiuP_apply (f : NMIUMap A B) (x : A) : nmiuP f x = f x := rfl

/-! ### **69IVa**'s factorisation, with its two maps

The corner `⌈⌈f⌉⌉A` of the preceding section, the compression
`g : a ↦ ⌈⌈f⌉⌉a` (`CentralProj.compress`) and the restriction
`h : x ↦ f(x)` (`CentralProj.restrictNMIU`) are exactly the exercise's
triangle. -/

namespace CentralProj

variable (c : CentralProj A)

/-- An nmiu-map `f : A → B` with `f(c) = 1` restricts to an nmiu-map
`cA → B`.  (Normality is `f`'s own normality precomposed with
`saIncl_isLUB`, i.e. with the fact that suprema of the corner are suprema of
`A`.) -/
noncomputable def restrictNMIU (f : NMIUMap A B) (hf1 : (f c.val : B) = 1) :
    NMIUMap c.sub B where
  toStarAlgHom :=
    { toFun := fun x => f (x : A)
      map_one' := hf1
      map_mul' := fun x y => map_mul f.toStarAlgHom _ _
      map_zero' := map_zero f.toStarAlgHom
      map_add' := fun x y => map_add f.toStarAlgHom _ _
      commutes' := fun r => by
        show (f (((algebraMap ℂ c.sub r : c.sub)) : A) : B) = algebraMap ℂ B r
        rw [algebraMap_coe]
        show (f.toStarAlgHom (r • c.val) : B) = algebraMap ℂ B r
        rw [map_smul f.toStarAlgHom]
        show r • (f c.val : B) = _
        rw [hf1, Algebra.algebraMap_eq_smul_one]
      map_star' := fun x => map_star f.toStarAlgHom _ }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hdir' : DirectedOn (· ≤ ·) (saIncl c '' D) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
      exact ⟨saIncl c z, ⟨z, hz, rfl⟩, hxz, hyz⟩
    have h := f.preservesDirSups' (saIncl c '' D) (saIncl c s) (hne.image _) hdir'
      (c.saIncl_isLUB hne hdir hlub)
    have himg : (fun d : selfAdjoint A => (f.toStarAlgHom (d : A) : B)) '' (saIncl c '' D)
        = (fun d : selfAdjoint c.sub => (f.toStarAlgHom ((d : c.sub) : A) : B)) '' D := by
      rw [← Set.image_comp]; rfl
    rw [himg] at h
    exact h

@[simp] theorem restrictNMIU_apply (f : NMIUMap A B) (hf1 : (f c.val : B) = 1)
    (x : c.sub) : c.restrictNMIU f hf1 x = f (x : A) := rfl

end CentralProj

/-- **69IVa** (`nmiu-factors`, vn.tex:3619, Exercise), the factorisation
itself: an nmiu-map `f : A → B` factors as an nmiu-**surjection**
`g : A → ⌈⌈f⌉⌉A`, `a ↦ ⌈⌈f⌉⌉a`, followed by an nmiu-**injection**
`h : ⌈⌈f⌉⌉A → B`, `a ↦ f(a)`.

Both maps are `NMIUMap`s, so multiplicativity, involutivity, unitality,
`ℂ`-linearity and normality are all claimed; the corner is the von Neumann
algebra `CentralProj.sub` of the preceding section, `⌈⌈f⌉⌉ = ⌈f⌉` being
central by **69IV** (`carrier_miu`).  Unitality of `h` is `f(⌈f⌉) = 1`, which
is `f(1) = 1` minus `f(⌈f⌉^⊥) = 0`; surjectivity of `g` is `⌈f⌉x = x` on the
corner; injectivity of `h` is the second clause of `nmiu_factors`. -/
theorem nmiu_factors_maps (f : NMIUMap A B) (g : A →ₚ[ℂ] B)
    (hg : PreservesDirSups ⇑g) (heq : ∀ a, g a = f a) :
    ∃ (c : CentralProj A) (G : NMIUMap A c.sub) (H : NMIUMap c.sub B),
      c.val = carrier g hg ∧
        (∀ a : A, ((G a : c.sub) : A) = carrier g hg * a) ∧
        (∀ x : c.sub, (H x : B) = f (x : A)) ∧
        Function.Surjective ⇑G ∧ Function.Injective ⇑H ∧
        ∀ a : A, (f a : B) = H (G a) := by
  have hcp : IsStarProjection (carrier g hg) := (carrier_spec g hg).1
  have hcc : IsCentral A (carrier g hg) := (carrier_miu f g hg heq).1
  set c : CentralProj A := ⟨carrier g hg, hcp, hcc⟩ with hcdef
  have hf1 : (f c.val : B) = 1 := by
    have h1 : (f ((1 : A) - carrier g hg) : B) = 0 := by
      have h := (carrier_spec g hg).2.1
      rw [heq] at h
      exact h
    have h3 : (f ((1 : A) - carrier g hg) : B) = f 1 - f (carrier g hg) :=
      map_sub f.toStarAlgHom _ _
    have hone : (f (1 : A) : B) = 1 := map_one f.toStarAlgHom
    rw [h1, hone] at h3
    exact (sub_eq_zero.mp h3.symm).symm
  refine ⟨c, c.compress, c.restrictNMIU f hf1, rfl, fun _ => rfl, fun _ => rfl,
    c.compress_surjective, ?_, ?_⟩
  · intro x y hxy
    have h : carrier g hg * (x : A) = carrier g hg * (y : A) :=
      (nmiu_factors f g hg heq (x : A) (y : A)).2.mp hxy
    refine Subtype.ext ?_
    rw [← (show carrier g hg * (x : A) = (x : A) from x.2),
      ← (show carrier g hg * (y : A) = (y : A) from y.2)]
    exact h
  · intro a
    exact (nmiu_factors f g hg heq a a).1

/-- **69IVb** (`nmiu-image`, vn.tex:3637): the image of an nmiu-map
`f : A → B` between von Neumann algebras is a von Neumann subalgebra of
`B`.

This is the route vn.tex:3637 prints — "use this, and
`injective-nmiu-iso-on-image`, to show that `f(𝒜)` is a von Neumann
subalgebra of `ℬ`": **69IVa**'s factorisation `f = H ∘ G` with `G` onto the
corner `⌈⌈f⌉⌉A` and `H` injective gives `f(𝒜) = H(⌈⌈f⌉⌉𝒜)`, and **48VI**.1
(`isVNSubalgebra_range`) applies to the injective normal `H`.  (The corner
lives in `A`'s universe and `B` in its own, so the form of 48VI.1 used here
is `isVNSubalgebra_range_general`, which is `isVNSubalgebra_range` with the
common-universe constraint dropped.) -/
theorem nmiu_image (f : NMIUMap A B) :
    IsVNSubalgebra B f.toStarAlgHom.range := by
  obtain ⟨c, G, H, -, -, -, hGs, hHi, hfa⟩ :=
    nmiu_factors_maps f (nmiuP f) f.preservesDirSups' (fun _ => rfl)
  -- `f(𝒜) = H(⌈⌈f⌉⌉𝒜)`, because `G` is onto the corner and `f = H ∘ G`
  have hr : f.toStarAlgHom.range = H.toStarAlgHom.range := by
    ext b
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨G a, (hfa a).symm⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := hGs x
      exact ⟨a, hfa a⟩
  rw [hr]
  exact isVNSubalgebra_range_general H.toStarAlgHom hHi H.preservesDirSups'

/-- `a* e a` is positive for a projection `e`. -/
private theorem conj_proj_nonneg {e : A} (he : IsStarProjection e) (a : A) :
    (0 : A) ≤ star a * e * a := by
  have h : star a * e * a = star (e * a) * (e * a) := by
    calc star a * e * a = star a * (e * e) * a := by rw [he.isIdempotentElem.eq]
      _ = star (e * a) * (e * a) := by
          rw [star_mul, he.isSelfAdjoint.star_eq]; noncomm_ring
  rw [h]
  exact star_mul_self_nonneg _

/-- The GNS identity behind **69V** and **69VII**: for a vector `ξ` implementing
`ω` in a ∗-representation `ρ`, and a projection `e`, the vector
`ρ(e)ρ(a)ξ` vanishes exactly when `ω(a* e a)` does, because its squared norm
*is* `ω(a* e a)`. -/
private theorem gns_zero_iff {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (ω : NPFunctional A)
    (ρ : MIUMap A (H →L[ℂ] H)) (ξ : H) (hξ : ∀ a : A, ω a = ⟪ξ, ρ a ξ⟫)
    {e : A} (he : IsStarProjection e) (a : A) :
    ρ e (ρ a ξ) = 0 ↔ (ω (star a * e * a) : ℂ) = 0 := by
  have hinner : ∀ b : A, ⟪ρ a ξ, ρ b (ρ a ξ)⟫ = (ω (star a * b * a) : ℂ) := by
    intro b
    rw [hξ (star a * b * a), map_mul, map_mul, map_star]
    rw [← ContinuousLinearMap.adjoint_inner_right (ρ a) ξ (ρ b (ρ a ξ))]
    simp [ContinuousLinearMap.star_eq_adjoint]
  have hself : ⟪ρ e (ρ a ξ), ρ e (ρ a ξ)⟫ = (ω (star a * e * a) : ℂ) := by
    rw [← hinner e, ← ContinuousLinearMap.adjoint_inner_right (ρ e) (ρ a ξ) (ρ e (ρ a ξ))]
    have hst : ContinuousLinearMap.adjoint (ρ e) = ρ e := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, he.isSelfAdjoint.star_eq]
    rw [hst]
    have hee : (ρ e) (ρ e (ρ a ξ)) = ρ (e * e) (ρ a ξ) := by rw [map_mul]; rfl
    rw [hee, he.isIdempotentElem.eq]
  rw [← hself]
  exact (inner_self_eq_zero (𝕜 := ℂ) (x := ρ e (ρ a ξ))).symm

/-- Half of **69V**: `ω(a* ⌈⌈⌈ω⌉⌉⌉^⊥ a) = 0`.  (`⌈⌈⌈ω⌉⌉⌉^⊥` is central and
killed by `ω`, and `⌈a* q a⌉ ≤ q` for central `q`.) -/
private theorem omega_conj_cceil_compl (ω : NPFunctional A) (a : A) :
    (ω (star a * (1 - cceil (npCarrier ω)) * a) : ℂ) = 0 := by
  set c : A := npCarrier ω with hcdef
  have hspec := carrier_spec ω.toPositiveLinearMap ω.preservesDirSups'
  have hcproj : IsStarProjection c := hspec.1
  have hc0 : (ω (1 - c) : ℂ) = 0 := hspec.2.1
  have hcc := (cceil_fundamental c hcproj).1
  set q : A := 1 - cceil c with hqdef
  have hqproj : IsStarProjection q := hcc.1.1.one_sub
  have hqcentral : IsCentral A q := by
    intro b
    rw [hqdef, sub_mul, mul_sub, one_mul, mul_one, hcc.1.2.1 b]
  have hqω : (ω q : ℂ) = 0 := by
    have hle : q ≤ 1 - c := by rw [hqdef]; exact sub_le_sub_left hcc.1.2.2 1
    have h1 : (0 : ℂ) ≤ ω q := npFunctional_nonneg ω hqproj.nonneg
    have h2 : (ω q : ℂ) ≤ ω (1 - c) := npFunctional_mono ω hle
    rw [hc0] at h2
    exact le_antisymm h2 h1
  have hx0 : (0 : A) ≤ star a * q * a := conj_proj_nonneg hqproj a
  refine (ceil_functionals_lemma _ hx0 ω).mpr ?_
  have hceilq : ceil (star a * q * a) ≤ q := by
    refine (ceil_le_iff hx0 hqproj).mpr ?_
    calc star a * q * a * q = star a * q * (q * a) := by rw [hqcentral a]; noncomm_ring
      _ = star a * (q * q) * a := by noncomm_ring
      _ = star a * q * a := by rw [hqproj.isIdempotentElem.eq]
  have h1 : (0 : ℂ) ≤ ω (ceil (star a * q * a)) :=
    npFunctional_nonneg ω (ceil_spec hx0).1.nonneg
  have h2 : (ω (ceil (star a * q * a)) : ℂ) ≤ ω q := npFunctional_mono ω hceilq
  rw [hqω] at h2
  exact le_antisymm h2 h1

/-- The other half of **69V**: if `ω(a* e a) = 0` for every `a` then
`⌈⌈⌈ω⌉⌉⌉ ≤ e^⊥`.  (By **68I** `cceil-fundamental`, `⌈⌈e⌉⌉ = ⋃_a ⌈a* e a⌉`
lies below `⌈ω⌉^⊥`, and `1 - ⌈⌈e⌉⌉` is then a central projection above
`⌈ω⌉`.) -/
private theorem cceil_npCarrier_le (ω : NPFunctional A) {e : A} (he : IsStarProjection e)
    (hvan : ∀ a : A, (ω (star a * e * a) : ℂ) = 0) :
    cceil (npCarrier ω) ≤ 1 - e := by
  set c : A := npCarrier ω with hcdef
  have hspec := carrier_spec ω.toPositiveLinearMap ω.preservesDirSups'
  have hcproj : IsStarProjection c := hspec.1
  have hcleast : ∀ p : A, IsStarProjection p → (ω (1 - p) : ℂ) = 0 → c ≤ p := hspec.2.2
  have hcc := (cceil_fundamental c hcproj).1
  have hbelow : ∀ x ∈ {x : A | ∃ a : A, x = ceil (star a * e * a)}, x ≤ 1 - c := by
    rintro _ ⟨a, rfl⟩
    have hx0 : (0 : A) ≤ star a * e * a := conj_proj_nonneg he a
    have hceilproj : IsStarProjection (ceil (star a * e * a)) := (ceil_spec hx0).1
    have h0 : (ω (ceil (star a * e * a)) : ℂ) = 0 :=
      (ceil_functionals_lemma _ hx0 ω).mp (hvan a)
    exact le_sub_comm.mp
      (hcleast (1 - ceil (star a * e * a)) hceilproj.one_sub (by simpa using h0))
  have hccele : cceil e ≤ 1 - c := by
    rw [(cceil_fundamental e he).2]
    refine (projSup_spec ?_).2.2 _ hcproj.one_sub hbelow
    rintro _ ⟨a, rfl⟩
    exact (ceil_spec (conj_proj_nonneg he a)).1
  have hce := (cceil_fundamental e he).1
  have hsub : cceil c ≤ 1 - cceil e := by
    refine hcc.2 ⟨hce.1.1.one_sub, ?_, le_sub_comm.mp hccele⟩
    intro b
    rw [sub_mul, mul_sub, one_mul, mul_one, hce.1.2.1 b]
  exact hsub.trans (sub_le_sub_left hce.1.2.2 1)

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
    carrier g hg = cceil (npCarrier ω) := by
  have hcproj : IsStarProjection (npCarrier ω) :=
    (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').1
  have hccproj : IsStarProjection (cceil (npCarrier ω)) :=
    ((cceil_fundamental _ hcproj).1).1.1
  refine carrier_eq g hg hccproj ?_ ?_
  · -- `ρ(⌈⌈⌈ω⌉⌉⌉^⊥)` kills the dense set of `ρ(a)ξ`, hence vanishes
    rw [heq]
    have hzero : ∀ a : A, (ρ (1 - cceil (npCarrier ω))) (ρ a ξ) = 0 := fun a =>
      (gns_zero_iff ω ρ ξ hξ hccproj.one_sub a).mpr (omega_conj_cceil_compl ω a)
    have hfun : ⇑(ρ (1 - cceil (npCarrier ω))) = fun _ => (0 : H) := by
      refine Continuous.ext_on hcyc (ρ _).continuous continuous_const ?_
      rintro _ ⟨a, rfl⟩
      exact hzero a
    exact ContinuousLinearMap.ext fun y => by simpa using congrFun hfun y
  · intro r hr hgr
    have hkey := cceil_npCarrier_le ω hr.one_sub fun a =>
      (gns_zero_iff ω ρ ξ hξ hr.one_sub a).mp (by rw [← heq, hgr]; rfl)
    rwa [sub_sub_cancel] at hkey

/-- **69V** (`proto-gns-ceil`) at the thesis's own `ϱ_ω`.  `proto_gns_ceil`
above is stated for an *arbitrary* normal cyclic representation implementing
`ω`, which is more general than the point; this instantiates it at the GNS
representation of **48I**, in the form in which **48III** (`gns_normal`,
`A/VN/Basic`) makes that representation available — so the printed statement
`⌈⌈ω⌉⌉ = ⌈ϱ_ω⌉` is on record. -/
theorem proto_gns_ceil_gnsRep (ω : NPFunctional A) :
    ∃ (ι : Type u) (ρ : MIUMap A
        (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2))
      (ξ : lp (fun _ : ι => ℂ) 2) (hn : PreservesDirSups ⇑ρ),
      (∀ a : A, ω a = ⟪ξ, ρ a ξ⟫) ∧
        Dense (Set.range fun a : A => ρ a ξ) ∧
        carrier (starAlgHomP ρ) hn = cceil (npCarrier ω) := by
  obtain ⟨ι, ρ, ξ, hξ, hdense, hn⟩ := gns_normal ω
  exact ⟨ι, ρ, ξ, hn, hξ, hdense,
    proto_gns_ceil ω ρ (starAlgHomP ρ) hn (fun _ => rfl) ξ hξ hdense⟩

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
      projSup {p : A | ∃ ω ∈ Ω, p = cceil (npCarrier ω)} := by
  set S : Set A := {p : A | ∃ ω ∈ Ω, p = cceil (npCarrier ω)} with hSdef
  have hSproj : ∀ p ∈ S, IsStarProjection p := by
    rintro _ ⟨ν, -, rfl⟩
    exact ((cceil_fundamental _ (carrier_spec ν.toPositiveLinearMap ν.preservesDirSups').1).1).1.1
  obtain ⟨hPproj, hPub, hPleast⟩ := projSup_spec hSproj
  -- a continuous map killing every `ρ(a)x_ω` is zero
  have hdense_zero : ∀ T : H →L[ℂ] H, (∀ (ν : Ω) (a : A), T (ρ a (x ν)) = 0) → T = 0 := by
    intro T hT
    have hsub : (Set.range fun p : Ω × A => ρ p.2 (x p.1)) ⊆ (T : H →ₗ[ℂ] H).ker := by
      rintro _ ⟨p, rfl⟩
      exact hT p.1 p.2
    have hspan : (Submodule.span ℂ (Set.range fun p : Ω × A => ρ p.2 (x p.1)) : Set H)
        ⊆ ((T : H →ₗ[ℂ] H).ker : Set H) := by
      simpa using (Submodule.span_le.mpr hsub)
    have hclosed : IsClosed ((T : H →ₗ[ℂ] H).ker : Set H) := T.isClosed_ker
    have huniv : (Set.univ : Set H) ⊆ ((T : H →ₗ[ℂ] H).ker : Set H) := by
      rw [← hcyc.closure_eq]
      exact hclosed.closure_subset_iff.mpr hspan
    exact ContinuousLinearMap.ext fun y => huniv (Set.mem_univ y)
  refine carrier_eq g hg hPproj ?_ ?_
  · rw [heq]
    refine hdense_zero _ fun ν a => ?_
    refine (gns_zero_iff (ν : NPFunctional A) ρ (x ν) (hx ν) hPproj.one_sub a).mpr ?_
    -- `1 - ⋃ ≤ 1 - ⌈⌈⌈ν⌉⌉⌉`, so `ν(a* (1-⋃) a) ≤ ν(a* ⌈⌈⌈ν⌉⌉⌉^⊥ a) = 0`
    have hle : (1 : A) - projSup S ≤ 1 - cceil (npCarrier (ν : NPFunctional A)) :=
      sub_le_sub_left (hPub _ ⟨ν, ν.2, rfl⟩) 1
    have h1 : (0 : ℂ) ≤ (ν : NPFunctional A) (star a * (1 - projSup S) * a) :=
      npFunctional_nonneg _ (conj_proj_nonneg hPproj.one_sub a)
    have h2 : ((ν : NPFunctional A) (star a * (1 - projSup S) * a) : ℂ)
        ≤ (ν : NPFunctional A) (star a * (1 - cceil (npCarrier (ν : NPFunctional A))) * a) :=
      npFunctional_mono _ (star_left_conjugate_le_conjugate hle a)
    rw [omega_conj_cceil_compl (ν : NPFunctional A) a] at h2
    exact le_antisymm h2 h1
  · intro r hr hgr
    refine hPleast r hr ?_
    rintro _ ⟨ν, hν, rfl⟩
    have hkey := cceil_npCarrier_le (((⟨ν, hν⟩ : Ω) : NPFunctional A)) hr.one_sub fun a =>
      (gns_zero_iff ((⟨ν, hν⟩ : Ω) : NPFunctional A) ρ (x ⟨ν, hν⟩)
        (hx ⟨ν, hν⟩) hr.one_sub a).mp (by rw [← heq, hgr]; rfl)
    rwa [sub_sub_cancel] at hkey

variable (A) in
/-- **Auxiliary — not a transcription, and carrying no DISP number**: a
collection `Ω` of np-functionals kills no nonzero *central positive*
element — `a` central, `0 ≤ a` and `ω(a) = 0` for all `ω ∈ Ω` force `a = 0`.

It is *neither* item of **69IX**, and is deliberately no longer named as if
it were: it is not cstar.tex **21II**.4 (which conjugates — 69IX item 1,
here `CentreSeparatingConj`) and not 69IX item 2 (which speaks of central
*projections*, here `CentreSeparatingCentralProj`).  It sits strictly between
the two — `CentrePositiveSeparating → CentreSeparatingCentralProj`
(`CentrePositiveSeparating.centralProj`, projections are positive) — and the
three are all equivalent once the missing lemma "`⌈a⌉` is central for central
positive `a`" is available (see PROVING-LOG, "Divergences").

The earlier note that it was "kept because `A/Proc/Tensor.lean` states eight
results with it" is **stale**: `Tensor.lean` uses `CentreSeparatingConj`
throughout, and this notion is used nowhere outside this file.  It is kept
only as the intermediate step of the two implications below. -/
def CentrePositiveSeparating (Ω : Set (NPFunctional A)) : Prop :=
  ∀ a : A, IsCentral A a → 0 ≤ a → (∀ ω ∈ Ω, ω a = 0) → a = 0

variable (A) in
/-- **21II**.4 (`separating`, cstar.tex:3113, Definition), which is **69IX**
item **1** — the thesis's *centre separating*.  Quoting cstar.tex:

> A collection `Ω` of linear maps on a C\*-algebra `𝒜` will be called […]
> **centre separating** if `a ∈ 𝒜₊` is zero iff `ω(b*ab) = 0` for all
> `ω ∈ Ω` and `b ∈ 𝒜`.

This is *literally* `Theses.A.CStar.CentreSeparating` — the 21II.4 rendering
already in `A/CStar/Positive.lean` — applied to `Ω` read as an indexed family
of positive linear functionals; it is not a second definition of the notion.
See `centreSeparatingConj_iff` for the unfolded form. -/
def CentreSeparatingConj (Ω : Set (NPFunctional A)) : Prop :=
  Theses.A.CStar.CentreSeparating
    (fun ω : Ω => ((ω : NPFunctional A).toPositiveLinearMap.toLinearMap : A →ₗ[ℂ] ℂ))

/-- `CentreSeparatingConj` unfolded: `a ∈ A₊` is zero iff `ω(b*ab) = 0` for
all `ω ∈ Ω` and all `b ∈ A`. -/
theorem centreSeparatingConj_iff (Ω : Set (NPFunctional A)) :
    CentreSeparatingConj A Ω ↔
      ∀ a : A, 0 ≤ a → (a = 0 ↔ ∀ ω ∈ Ω, ∀ b : A, (ω (star b * a * b) : ℂ) = 0) :=
  ⟨fun h a ha => (h a ha).trans ⟨fun H ω hω b => H ⟨ω, hω⟩ b, fun H ω b => H ω ω.2 b⟩,
   fun h a ha => (h a ha).trans ⟨fun H ω b => H ω ω.2 b, fun H ω hω b => H ⟨ω, hω⟩ b⟩⟩

variable (A) in
/-- **69IX** item **2** (`vn-center-separating`, vn.tex:3693, Corollary),
quoting vn.tex:

> A central projection `z` of `𝒜` is zero when `ω(z) = 0` for all `ω ∈ Ω`. -/
def CentreSeparatingCentralProj (Ω : Set (NPFunctional A)) : Prop :=
  ∀ z : A, IsStarProjection z → IsCentral A z → (∀ ω ∈ Ω, ω z = 0) → z = 0

/-- The auxiliary central-positive notion implies **69IX** item 2: a central
projection is a central positive. -/
theorem CentrePositiveSeparating.centralProj {Ω : Set (NPFunctional A)}
    (h : CentrePositiveSeparating A Ω) : CentreSeparatingCentralProj A Ω :=
  fun z hz hzc hzero => h z hzc hz.nonneg hzero

/-- **69IX**, the implication (2) ⇒ (1) — the one its consumers actually
need: 69IX item **2** ("a central *projection* killed by all of `Ω` is
zero") gives cstar.tex **21II**.4, thesis item **1**.

Proof: `⌈⌈a⌉⌉ = ⋃_b ⌈b* ⌊a⌉ b⌉` by **68I**, every `ω ∈ Ω` kills `b* ⌊a⌉ b`
(because it kills `b* a b`, hence `b* a a* b`, hence `b* ⌈aa*⌉ b` by **60I**),
so every `ω` kills `⌈b* ⌊a⌉ b⌉` — again by **60I** — hence kills their
supremum, which is the central projection `⌈⌈a⌉⌉`.  (This is a shortcut: the
thesis derives (2) ⇒ (1) through (3) and `gns_ceil`.) -/
theorem eq_zero_of_centreSeparating_conj (Ω : Set (NPFunctional A))
    (hΩ : CentreSeparatingCentralProj A Ω) {a : A} (ha : 0 ≤ a)
    (h : ∀ ω ∈ Ω, ∀ b : A, ω (star b * a * b) = 0) : a = 0 := by
  have hasa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha
  obtain ⟨herproj, hera⟩ := (ceill_basic_2 a).1
  set e : A := rangeProj a with hedef
  have hstar : a * star a = a * a := by rw [hasa.star_eq]
  have hea : ∀ ω ∈ Ω, ∀ b : A, ω (star b * e * b) = 0 := by
    intro ω hω b
    have h1 : conjNP b ω a = 0 := by rw [conjNP_apply]; exact h ω hω b
    have h2 : conjNP b ω (a * star a) = 0 := by
      have hle : a * a ≤ (‖a‖ : ℝ) • a := mul_self_le_norm_smul ha
      have hmono : conjNP b ω (a * a) ≤ conjNP b ω ((‖a‖ : ℝ) • a) :=
        (conjNP b ω).monotone hle
      have hrhs : conjNP b ω ((‖a‖ : ℝ) • a) = 0 := by
        have hcx : ((‖a‖ : ℝ) • a : A) = (((‖a‖ : ℝ) : ℂ)) • a := by
          rw [← algebraMap_smul ℂ (‖a‖ : ℝ) a]; simp
        rw [hcx]
        show (conjNP b ω).toPositiveLinearMap _ = 0
        rw [map_smul (conjNP b ω).toPositiveLinearMap]
        show (((‖a‖ : ℝ) : ℂ)) • (conjNP b ω) a = 0
        rw [h1, smul_zero]
      have hnn : (0 : ℂ) ≤ conjNP b ω (a * a) :=
        npFunctional_nonneg _ (by rw [← hstar]; exact mul_star_self_nonneg a)
      rw [hstar]
      rw [hrhs] at hmono
      exact le_antisymm hmono hnn
    have h3 : conjNP b ω (ceil (a * star a)) = 0 :=
      (ceil_functionals_lemma (a * star a) (mul_star_self_nonneg a) (conjNP b ω)).mp h2
    rw [conjNP_apply] at h3
    exact h3
  set P : Set A := {x : A | ∃ b : A, x = ceil (star b * e * b)} with hPdef
  have hPproj : ∀ p ∈ P, IsStarProjection p := by
    rintro p ⟨b, rfl⟩
    exact (ceil_spec (star_left_conjugate_nonneg herproj.nonneg b)).1
  have hcc : cceil a = projSup P := by
    rw [(cceil_eq_cceil_supp a).2.1, ← hedef, (cceil_fundamental e herproj).2]
  have hzero : ∀ ω ∈ Ω, ω (cceil a) = 0 := by
    intro ω hω
    set r : A := npCarrier ω with hrdef
    obtain ⟨hrproj, hr0, -⟩ := carrier_spec ω.toPositiveLinearMap ω.preservesDirSups'
    have hle : projSup P ≤ 1 - r := by
      refine (projSup_spec hPproj).2.2 _ hrproj.one_sub ?_
      rintro p ⟨b, rfl⟩
      have hnn : (0 : A) ≤ star b * e * b := star_left_conjugate_nonneg herproj.nonneg b
      have hp0 : ω (ceil (star b * e * b)) = 0 :=
        (ceil_functionals_lemma _ hnn ω).mp (hea ω hω b)
      have hcp : IsStarProjection (ceil (star b * e * b)) := (ceil_spec hnn).1
      have hcar := (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').2.2
        (1 - ceil (star b * e * b)) hcp.one_sub (by rw [sub_sub_cancel]; exact hp0)
      exact le_sub_comm.mp hcar
    have hmono : ω (cceil a) ≤ ω (1 - r) := by
      rw [hcc]; exact (ω.monotone hle : ω (projSup P) ≤ ω (1 - r))
    have hr0' : ω (1 - r) = 0 := hr0
    rw [hr0'] at hmono
    refine le_antisymm hmono ?_
    exact npFunctional_nonneg ω (by rw [hcc]; exact (projSup_spec hPproj).1.nonneg)
  obtain ⟨⟨hzproj, hzcentral, hza⟩, -⟩ := cceil_isLeast a
  have hz0 : cceil a = 0 := hΩ (cceil a) hzproj hzcentral hzero
  rw [← hza, hz0, zero_mul]

/-- **69IX**, (2) ⇒ (1) packaged: `eq_zero_of_centreSeparating_conj` read as
cstar.tex **21II**.4 for the family `Ω`. -/
theorem CentreSeparatingCentralProj.conj {Ω : Set (NPFunctional A)}
    (hΩ : CentreSeparatingCentralProj A Ω) : CentreSeparatingConj A Ω := by
  intro x hx
  refine ⟨fun hx0 ω b => by rw [hx0]; simp, fun H => ?_⟩
  exact eq_zero_of_centreSeparating_conj Ω hΩ hx fun ω hω b => H ⟨ω, hω⟩ b

/-- The auxiliary central-positive notion implies the thesis's, through
**69IX** item 2. -/
theorem CentrePositiveSeparating.conj {Ω : Set (NPFunctional A)}
    (hΩ : CentrePositiveSeparating A Ω) : CentreSeparatingConj A Ω :=
  hΩ.centralProj.conj

/-- The `Ω`-version of **44XI**'s `nonneg_of_conjNP`: for a centre separating
collection `Ω` (cstar.tex **21II**.4), positivity of all `ω(c* a c)`
(`ω ∈ Ω`, `c ∈ A`) already gives `0 ≤ a`.  This is `CentreSeparatingConj` fed
to **30X** (`proto_gelfand_naimark_1`). -/
theorem nonneg_of_conjNP_of_centreSeparating (Ω : Set (NPFunctional A))
    (hΩ : CentreSeparatingConj A Ω) {a : A}
    (h : ∀ ω ∈ Ω, ∀ c : A, (0 : ℂ) ≤ ω (star c * a * c)) : 0 ≤ a := by
  have hpos : ∀ ω : Ω,
      IsPositiveMap ((ω : NPFunctional A).toPositiveLinearMap.toLinearMap : A →ₗ[ℂ] ℂ) :=
    fun ω x hx => npFunctional_nonneg (ω : NPFunctional A) hx
  refine ((proto_gelfand_naimark_1 _ hpos).mp hΩ a).mpr fun p => ?_
  show (0 : ℂ) ≤ (p.1 : NPFunctional A) (star p.2 * (a * p.2))
  rw [← mul_assoc]
  exact h _ p.1.2 p.2

/-! ### **69VII** at the thesis's own `ϱ_Ω`

`gns_ceil` above is stated for an arbitrary normal cyclic representation.
Here it is *instantiated* at the direct-sum GNS representation
`ϱ_Ω : 𝒜 → 𝔅(ℋ_Ω)` of **48I**/**48V** (`gnsRepFam` of `A/VN/Basic`), with
the cyclic vectors `η_ω(1)` — which is what **69IX** item 3 speaks about, and
what turns `⌈ϱ_Ω⌉ = ⋃_{ω∈Ω}⌈⌈ω⌉⌉` into a statement about `ϱ_Ω` being
injective (**63II**.4). -/

section GNSOmega

variable (Ω : Set (NPFunctional A))

/-- The collection `Ω`, read as a family indexed by itself, so that
`gnsHilbFam`/`gnsRepFam` apply. -/
private noncomputable def famOfSet : Ω → NPFunctional A := fun ω => (ω : NPFunctional A)

open scoped Classical in
/-- The cyclic vector `η_ω(1)` of `ℋ_Ω = ⊕_{ω∈Ω} ℋ_ω`, sitting in the
`ω`-summand. -/
private noncomputable def gnsCycVec (ν : Ω) : gnsHilbFam (famOfSet Ω) :=
  lp.single 2 ν (gnsVec (famOfSet Ω ν) 1)

set_option maxHeartbeats 1000000 in
/-- `ω(a) = ⟪η_ω(1), ϱ_Ω(a) η_ω(1)⟫`: each `ω ∈ Ω` is the vector functional
of its own cyclic vector. -/
private theorem gnsCycVec_implements (ν : Ω) (a : A) :
    ((ν : NPFunctional A) a : ℂ)
      = ⟪gnsCycVec Ω ν, gnsRepFam (famOfSet Ω) a (gnsCycVec Ω ν)⟫ := by
  classical
  rw [gnsCycVec, lp.inner_single_left]
  show _ = (⟪gnsVec (famOfSet Ω ν) 1,
    ((gnsRepFam (famOfSet Ω) a (lp.single 2 ν (gnsVec (famOfSet Ω ν) 1)) :
        gnsHilbFam (famOfSet Ω)) : ∀ _ : Ω, _) ν⟫)
  rw [gnsRepFam_apply_coe, lp.single_apply_self, gnsRep_gnsVec, gnsVec_inner]
  simp [famOfSet]

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- `ϱ_Ω(a) η_ω(1) = η_ω(a)`. -/
private theorem gnsRepFam_gnsCycVec (ν : Ω) (a : A) :
    gnsRepFam (famOfSet Ω) a (gnsCycVec Ω ν)
      = lp.single 2 ν (gnsVec (famOfSet Ω ν) a) := by
  classical
  refine Subtype.ext (funext fun i => ?_)
  rw [gnsRepFam_apply_coe, gnsCycVec]
  by_cases h : i = ν
  · subst h
    rw [lp.single_apply_self, lp.single_apply_self, gnsRep_gnsVec, mul_one]
  · rw [lp.single_apply_ne _ _ _ h, lp.single_apply_ne _ _ _ h, map_zero]

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- The vectors `ϱ_Ω(a) η_ω(1) = η_ω(a)` span a dense subspace of `ℋ_Ω`:
they exhaust each summand's dense set `η_ω(𝒜)`, and the summands add up to
`ℋ_Ω` by `lp.hasSum_single`. -/
private theorem gnsCycVec_dense :
    Dense (Submodule.span ℂ (Set.range fun q : Ω × A =>
      gnsRepFam (famOfSet Ω) q.2 (gnsCycVec Ω q.1)) :
        Set (gnsHilbFam (famOfSet Ω))) := by
  classical
  set V : Submodule ℂ (gnsHilbFam (famOfSet Ω)) :=
    Submodule.span ℂ (Set.range fun q : Ω × A =>
      gnsRepFam (famOfSet Ω) q.2 (gnsCycVec Ω q.1)) with hV
  have hWclosed : IsClosed ((V.topologicalClosure : Submodule ℂ _) :
      Set (gnsHilbFam (famOfSet Ω))) := V.isClosed_topologicalClosure
  have hsingle : ∀ (ν : Ω) (z : (famOfSet Ω ν).toPositiveLinearMap.GNS),
      (lp.single 2 ν z : gnsHilbFam (famOfSet Ω)) ∈ V.topologicalClosure := by
    intro ν
    have hclosed : IsClosed {z : (famOfSet Ω ν).toPositiveLinearMap.GNS |
        (lp.single 2 ν z : gnsHilbFam (famOfSet Ω)) ∈ V.topologicalClosure} :=
      hWclosed.preimage (lp.singleContinuousLinearMap ℂ
        (fun i : Ω => (famOfSet Ω i).toPositiveLinearMap.GNS) 2 ν).continuous
    have hsub : Set.range (gnsVec (famOfSet Ω ν)) ⊆
        {z | (lp.single 2 ν z : gnsHilbFam (famOfSet Ω)) ∈ V.topologicalClosure} := by
      rintro _ ⟨b, rfl⟩
      refine V.le_topologicalClosure ?_
      exact Submodule.subset_span ⟨(ν, b), gnsRepFam_gnsCycVec Ω ν b⟩
    have huniv : (Set.univ : Set (famOfSet Ω ν).toPositiveLinearMap.GNS) ⊆
        {z | (lp.single 2 ν z : gnsHilbFam (famOfSet Ω)) ∈ V.topologicalClosure} := by
      rw [← (gnsVec_denseRange (famOfSet Ω ν)).closure_eq]
      exact hclosed.closure_subset_iff.mpr hsub
    exact fun z => huniv (Set.mem_univ z)
  have hall : ∀ y : gnsHilbFam (famOfSet Ω), y ∈ V.topologicalClosure := by
    intro y
    have hs : HasSum (fun ν : Ω =>
        (lp.single 2 ν ((y : ∀ _ : Ω, _) ν) : gnsHilbFam (famOfSet Ω))) y :=
      lp.hasSum_single (by norm_num) y
    refine hWclosed.mem_of_tendsto hs ?_
    filter_upwards with t
    exact Submodule.sum_mem _ fun ν _ => hsingle ν _
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_forall fun y => ?_
  rw [← Submodule.topologicalClosure_coe]
  exact hall y

set_option maxHeartbeats 1000000 in
/-- **69VII** (`gns-ceil`) at the thesis's own `ϱ_Ω`:
`⌈ϱ_Ω⌉ = ⋃_{ω∈Ω} ⌈⌈ω⌉⌉`. -/
theorem gns_ceil_gnsRepFam :
    carrier (starAlgHomP (gnsRepFam (famOfSet Ω))) (gnsRepFam_normal (famOfSet Ω))
      = projSup {p : A | ∃ ω ∈ Ω, p = cceil (npCarrier ω)} :=
  gns_ceil Ω (gnsRepFam (famOfSet Ω)) (starAlgHomP (gnsRepFam (famOfSet Ω)))
    (gnsRepFam_normal (famOfSet Ω)) (fun _ => rfl) (gnsCycVec Ω)
    (gnsCycVec_implements Ω) (gnsCycVec_dense Ω)

set_option maxHeartbeats 1000000 in
/-- **69IX** items 2/3 joined: `⋃_{ω∈Ω}⌈⌈ω⌉⌉ = 1` iff `ϱ_Ω` is injective.
This is `gns_ceil_gnsRepFam` followed by **63II**.4 (`carrier_basic_4`,
`⌈f⌉ = 1` iff `f` injective, for multiplicative `f`). -/
theorem gnsRepFam_injective_iff :
    projSup {p : A | ∃ ω ∈ Ω, p = cceil (npCarrier ω)} = 1 ↔
      Function.Injective ⇑(gnsRepFam (famOfSet Ω)) := by
  rw [← gns_ceil_gnsRepFam Ω]
  exact carrier_basic_4 _ _ (fun a b => map_mul (gnsRepFam (famOfSet Ω)) a b)

end GNSOmega

/-- **69IX** (`vn-center-separating`, vn.tex:3693, Corollary): for a
collection `Ω` of np-functionals on a von Neumann algebra the following are
equivalent.

> 1. `Ω` is centre separating (see 21II).
> 2. A central projection `z` of `𝒜` is zero when `ω(z) = 0` for all `ω ∈ Ω`.
> 3. The map `ϱ_Ω : 𝒜 → 𝔅(ℋ_Ω)` from 48I is injective.

Item 3 appears **twice**: as entry 4, verbatim — `ϱ_Ω` being `gnsRepFam` of
`A/VN/Basic`, the direct-sum GNS representation of **48I**/**48V** — and, as
entry 3, in the equivalent form `⌈ϱ_Ω⌉ = ⋃_{ω∈Ω}⌈⌈ω⌉⌉ = 1` which the two
implications below are proved against.  Entries 3 and 4 are joined by
`gnsRepFam_injective_iff`, i.e. by **69VII** (`gns_ceil`) instantiated at
`ϱ_Ω` followed by **63II**.4.

Our route differs from the thesis's.  The thesis gets (1) ⟺ (3) from **30X**
and proves (2) ⇒ (3); we prove (1) ⇒ (3) ⇒ (2) ⇒ (1), where (2) ⇒ (1) is
`eq_zero_of_centreSeparating_conj` (**68I** plus **60I**, a shortcut round
`gns_ceil`) and (3) ⇒ (2) is the leastness of `⌈⌈·⌉⌉`.  The thesis's
(2) ⇒ (3) step — `⌈ϱ_Ω⌉^⊥ ≤ ⌈⌈ω⌉⌉^⊥ ≤ ⌈ω⌉^⊥`, so `ω(⌈ϱ_Ω⌉^⊥) = 0` — is our
(1) ⇒ (3) with the conjugating `b` carried along. -/
theorem vn_center_separating (Ω : Set (NPFunctional A)) :
    List.TFAE
      [CentreSeparatingConj A Ω,
       CentreSeparatingCentralProj A Ω,
       projSup {p : A | ∃ ω ∈ Ω, p = cceil (npCarrier ω)} = 1,
       Function.Injective ⇑(gnsRepFam (famOfSet Ω))] := by
  have hSproj : ∀ p ∈ {p : A | ∃ ω ∈ Ω, p = cceil (npCarrier ω)}, IsStarProjection p := by
    rintro _ ⟨ν, -, rfl⟩
    exact (cceil_isLeast _).1.1
  have hSmem : ∀ ω ∈ Ω, cceil (npCarrier ω)
      ∈ {p : A | ∃ ω ∈ Ω, p = cceil (npCarrier ω)} := fun ω hω => ⟨ω, hω, rfl⟩
  obtain ⟨huproj, hub, hleast⟩ := projSup_spec hSproj
  set u : A := projSup {p : A | ∃ ω ∈ Ω, p = cceil (npCarrier ω)} with hudef
  tfae_have 1 → 3 := by
    intro h
    -- `z := (⋃_ω ⌈⌈ω⌉⌉)^⊥` is a central projection, and `ω(b* z b) = 0`
    -- because `z ≤ ⌈⌈ω⌉⌉^⊥` and `ω(b* ⌈⌈ω⌉⌉^⊥ b) = 0` (half of **69V**).
    have hzproj : IsStarProjection (1 - u) := huproj.one_sub
    have hz0 : (1 : A) - u = 0 := by
      refine (h (1 - u) hzproj.nonneg).mpr fun ω b => ?_
      have hle : (1 : A) - u ≤ 1 - cceil (npCarrier (ω : NPFunctional A)) :=
        sub_le_sub_left (hub _ (hSmem _ ω.2)) 1
      have h2 : ((ω : NPFunctional A) (star b * (1 - u) * b) : ℂ)
          ≤ (ω : NPFunctional A)
            (star b * (1 - cceil (npCarrier (ω : NPFunctional A))) * b) :=
        npFunctional_mono _ (star_left_conjugate_le_conjugate hle b)
      rw [omega_conj_cceil_compl (ω : NPFunctional A) b] at h2
      exact le_antisymm h2 (npFunctional_nonneg _ (conj_proj_nonneg hzproj b))
    exact (sub_eq_zero.mp hz0).symm
  tfae_have 3 → 2 := by
    intro hu z hzproj hzc hzero
    -- `1 - z` is a central projection above every `⌈ω⌉`, hence above every
    -- `⌈⌈ω⌉⌉`, hence above their supremum `1`.
    have hle : u ≤ 1 - z := by
      refine hleast _ hzproj.one_sub ?_
      rintro _ ⟨ν, hν, rfl⟩
      obtain ⟨hcproj, -, hcleast⟩ := carrier_spec ν.toPositiveLinearMap ν.preservesDirSups'
      refine (cceil_fundamental (npCarrier ν) hcproj).1.2
        ⟨hzproj.one_sub, isCentral_one_sub hzc, ?_⟩
      exact hcleast (1 - z) hzproj.one_sub (by rw [sub_sub_cancel]; exact hzero ν hν)
    rw [hu] at hle
    have hz : z ≤ 0 := by
      have h0 : (0 : A) ≤ -z := by
        have h1 := sub_nonneg.mpr hle
        rwa [sub_sub_cancel_left] at h1
      exact neg_nonneg.mp h0
    exact le_antisymm hz hzproj.nonneg
  tfae_have 2 → 1 := fun h => h.conj
  tfae_have 3 ↔ 4 := gnsRepFam_injective_iff Ω
  tfae_finish

/-! ## Parsec 700: the classification of commutative von Neumann algebras

**70I** (vn.tex:3743): introduction — nothing to formalize. -/

/-- **70II** (`central-projection-central-carrier`, vn.tex:3749, Exercise):
every central projection `c` of a von Neumann algebra is of the form
`c = ∑ᵢ ⌈⌈ωᵢ⌉⌉` for a family of np-functionals with pairwise orthogonal
central carriers.

This is the thesis's own hint — "take `(ωᵢ)ᵢ` to be a maximal set of
np-functionals for which the `⌈⌈ωᵢ⌉⌉` are orthogonal" — and it does **not**
go through **66IV**.4: the Zorn argument is run directly on the central
carriers.  If `q = ⋁ᵢ ⌈⌈ωᵢ⌉⌉ ≠ c` then `r = c - q` is a non-zero *central*
projection, so some np-functional `τ` has `τ(r) ≠ 0`, and `ω = τ(r(·)r)`
satisfies `0 ≠ ⌈ω⌉ ≤ r`, whence `⌈⌈ω⌉⌉ ≤ r` (`r` being central), which is
orthogonal to `q` — contradicting maximality. -/
theorem central_projection_central_carrier (c : A)
    (hc : IsStarProjection c) (hcentral : IsCentral A c) :
    ∃ (ι : Type u) (ω : ι → NPFunctional A),
      (Pairwise fun i j =>
        cceil (npCarrier (ω i)) * cceil (npCarrier (ω j)) = 0) ∧
      c = projSup (Set.range fun i => cceil (npCarrier (ω i))) := by
  classical
  set T : Set (Set (NPFunctional A)) :=
    {S | (∀ ω ∈ S, cceil (npCarrier ω) ≤ c) ∧
      ∀ ω ∈ S, ∀ τ ∈ S, ω ≠ τ →
        cceil (npCarrier ω) * cceil (npCarrier τ) = 0} with hT
  obtain ⟨S, hSmax⟩ : ∃ S, Maximal (· ∈ T) S := by
    refine zorn_subset T fun cc hcc hchain =>
      ⟨⋃₀ cc, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro ω ⟨s, hs, hωs⟩
      exact (hcc hs).1 ω hωs
    · rintro ω ⟨s, hs, hωs⟩ τ ⟨s', hs', hτs'⟩ hne
      rcases hchain.total hs hs' with hsub | hsub
      · exact (hcc hs').2 ω (hsub hωs) τ hτs' hne
      · exact (hcc hs).2 ω hωs τ (hsub hτs') hne
  refine ⟨↥S, Subtype.val,
    fun i j hij => hSmax.1.2 i.1 i.2 j.1 j.2 fun h => hij (Subtype.ext h), ?_⟩
  set Q : Set A :=
    Set.range fun i : ↥S => cceil (npCarrier (i : NPFunctional A)) with hQ
  have hcarrierproj : ∀ ω : NPFunctional A, IsStarProjection (npCarrier ω) :=
    fun ω => (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').1
  have hQproj : ∀ x ∈ Q, IsStarProjection x := by
    rintro _ ⟨i, rfl⟩; exact (cceil_isLeast _).1.1
  have hQcen : ∀ x ∈ Q, IsCentral A x := by
    rintro _ ⟨i, rfl⟩; exact (cceil_isLeast _).1.2.1
  obtain ⟨hqproj, hqub, hqleast⟩ := projSup_spec hQproj
  have hqcen : IsCentral A (projSup Q) := projSup_isCentral hQproj hQcen
  have hqle : projSup Q ≤ c := by
    refine hqleast c hc ?_
    rintro _ ⟨i, rfl⟩
    exact hSmax.1.1 i.1 i.2
  refine le_antisymm ?_ hqle
  by_contra hlt
  obtain ⟨r, hrdef⟩ : ∃ r : A, r = c - projSup Q := ⟨_, rfl⟩
  have hrproj : IsStarProjection r := by
    rw [hrdef]; exact projection_below_projection _ _ hqproj hc hqle
  have hrcen : IsCentral A r := by
    rw [hrdef]; intro x; rw [sub_mul, mul_sub, hcentral x, hqcen x]
  have hrne : r ≠ 0 := by
    intro h
    rw [hrdef, sub_eq_zero] at h
    exact hlt h.le
  have hrc : r ≤ c := by
    rw [hrdef, sub_le_self_iff]
    exact hqproj.nonneg
  have hcq : c * projSup Q = projSup Q :=
    ((projection_below_effect c (projSup Q) ⟨hc.nonneg, hc.le_one⟩ hqproj).out 0 6).mp hqle
  have hrq : r * projSup Q = 0 := by
    rw [hrdef, sub_mul, hcq, hqproj.isIdempotentElem.eq, sub_self]
  obtain ⟨τ, hτ⟩ : ∃ τ : NPFunctional A, τ r ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hrne (VonNeumannAlgebra.np_faithful r hrproj.nonneg hcon)
  obtain ⟨ω, hωdef⟩ : ∃ ω : NPFunctional A, ω = conjNP r τ := ⟨_, rfl⟩
  have hrort : r * ((1 : A) - r) * r = 0 := by
    rw [mul_sub, mul_one, hrproj.isIdempotentElem.eq, sub_self, zero_mul]
  have hω1 : (ω 1 : ℂ) = τ r := by
    rw [hωdef, conjNP_apply, hrproj.isSelfAdjoint.star_eq, mul_one,
      hrproj.isIdempotentElem.eq]
  have hcle : npCarrier ω ≤ r := by
    refine (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').2.2 r hrproj ?_
    show ((ω : A → ℂ) (1 - r)) = 0
    rw [hωdef, conjNP_apply, hrproj.isSelfAdjoint.star_eq, hrort]
    exact npFunctional_zero _
  have hcne : npCarrier ω ≠ 0 := by
    intro h
    have h0 := (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').2.1
    change ((ω : A → ℂ) (1 - npCarrier ω)) = 0 at h0
    rw [h, sub_zero, hω1] at h0
    exact hτ h0
  -- `r` is central, so it dominates the *central* carrier of `ω` too
  have hccle : cceil (npCarrier ω) ≤ r :=
    (cceil_isLeast _).2
      ⟨hrproj, hrcen, (proj_le_iff_mul_left (hcarrierproj ω) hrproj).mp hcle⟩
  have hccne : cceil (npCarrier ω) ≠ 0 := by
    intro h
    have habs := (cceil_isLeast (npCarrier ω)).1.2.2
    rw [h, zero_mul] at habs
    exact hcne habs.symm
  have hccproj : ∀ ν : NPFunctional A, IsStarProjection (cceil (npCarrier ν)) :=
    fun ν => (cceil_isLeast _).1.1
  have hccr : cceil (npCarrier ω) * r = cceil (npCarrier ω) :=
    (proj_le_iff_mul_right (hccproj ω) hrproj).mp hccle
  have horth : ∀ τ' ∈ S, cceil (npCarrier ω) * cceil (npCarrier τ') = 0 := by
    intro τ' hτ'
    have hle : cceil (npCarrier τ') ≤ projSup Q := hqub _ ⟨⟨τ', hτ'⟩, rfl⟩
    have hmul : projSup Q * cceil (npCarrier τ') = cceil (npCarrier τ') :=
      (proj_le_iff_mul_left (hccproj τ') hqproj).mp hle
    calc cceil (npCarrier ω) * cceil (npCarrier τ')
        = (cceil (npCarrier ω) * r) * (projSup Q * cceil (npCarrier τ')) := by
          rw [hccr, hmul]
      _ = cceil (npCarrier ω) * (r * projSup Q) * cceil (npCarrier τ') := by
          noncomm_ring
      _ = 0 := by rw [hrq, mul_zero, zero_mul]
  have hins : insert ω S ∈ T := by
    constructor
    · intro ν hν
      rcases Set.mem_insert_iff.mp hν with hν | hν
      · rw [hν]; exact hccle.trans hrc
      · exact hSmax.1.1 ν hν
    · intro ν hν μ hμ hne
      rcases Set.mem_insert_iff.mp hν with hν | hν <;>
        rcases Set.mem_insert_iff.mp hμ with hμ | hμ
      · exact absurd (hν.trans hμ.symm) hne
      · rw [hν]; exact horth μ hμ
      · rw [hμ]
        have h' := congrArg star (horth ν hν)
        rwa [star_mul, (hccproj ν).isSelfAdjoint.star_eq,
          (hccproj ω).isSelfAdjoint.star_eq, star_zero] at h'
      · exact hSmax.1.2 ν hν μ hμ hne
  have hωS : ω ∈ S := hSmax.2 hins (Set.subset_insert _ _) (Set.mem_insert _ _)
  have hccq : cceil (npCarrier ω) * projSup Q = cceil (npCarrier ω) :=
    (proj_le_iff_mul_right (hccproj ω) hqproj).mp (hqub _ ⟨⟨ω, hωS⟩, rfl⟩)
  refine hccne ?_
  calc cceil (npCarrier ω) = cceil (npCarrier ω) * projSup Q := hccq.symm
    _ = (cceil (npCarrier ω) * r) * projSup Q := by rw [hccr]
    _ = cceil (npCarrier ω) * (r * projSup Q) := by noncomm_ring
    _ = 0 := by rw [hrq, mul_zero]


end Commutant

/-- **70III** (`cvn`, vn.tex:3758, Theorem): every commutative von Neumann
algebra is nmiu-isomorphic to a direct sum `⊕ᵢ L^∞(Xᵢ)` of `L^∞`s of finite
complete measure spaces.

This declaration carries the **first step** of the printed proof — 70II at
`c = 1`, giving `1 = ∑ᵢ ⌈⌈ωᵢ⌉⌉` with each `ωᵢ` faithful on its corner, by
the thesis's observation that `⌈⌈ωᵢ⌉⌉ = ⌈ωᵢ⌉` in a commutative algebra.  The
*second* step, `𝒜 ≅ ⊕ᵢ ⌈⌈ωᵢ⌉⌉𝒜` by 67IV.2, is `cvn_direct_sum` below, which
also records that each summand is a commutative von Neumann algebra carrying
a faithful np-functional.  The **third** step — identifying each summand
with an `L^∞(Xᵢ)` by 54XI — is `cvn_linfty` at the end of this file, which is
the theorem in full.

(This statement is destructured at `A/Proc/Duplicators.lean:4038`, which is
why the two later steps go in beside it rather than into it.) -/
theorem cvn {C : Type w} [CommCStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] [VonNeumannAlgebra C] :
    ∃ (ι : Type w) (ω : ι → NPFunctional C),
      (Pairwise fun i j =>
        cceil (npCarrier (ω i)) * cceil (npCarrier (ω j)) = 0) ∧
      projSup (Set.range fun i => cceil (npCarrier (ω i))) = 1 ∧
      ∀ i, ∀ a : C, 0 ≤ a → cceil (npCarrier (ω i)) * a = a →
        (ω i) a = 0 → a = 0 := by
  -- **70II** applied to `c = 1` gives the orthogonal decomposition; the
  -- faithfulness of `ωᵢ` on its corner is the thesis's observation that in a
  -- commutative algebra `⌈⌈ωᵢ⌉⌉ = ⌈ωᵢ⌉`, so `⌈ωᵢ⌉a = a` and `ωᵢ(a) = 0`
  -- together force `⌈a⌉ ≤ ⌈ωᵢ⌉ ≤ ⌈a⌉^⊥`, i.e. `⌈a⌉ = 0`.
  obtain ⟨ι, ω, hpair, hsum⟩ :=
    central_projection_central_carrier (1 : C) projection_basic_1.2
      (fun b => by rw [one_mul, mul_one])
  refine ⟨ι, ω, hpair, hsum.symm, fun i a ha hmul h0 => ?_⟩
  have hcarrproj : IsStarProjection (npCarrier (ω i)) :=
    (carrier_spec (ω i).toPositiveLinearMap (ω i).preservesDirSups').1
  -- in a commutative algebra the central carrier is the carrier
  have hcc : cceil (npCarrier (ω i)) = npCarrier (ω i) := by
    refine le_antisymm ((cceil_isLeast _).2
      ⟨hcarrproj, fun b => mul_comm _ b, hcarrproj.isIdempotentElem.eq⟩) ?_
    exact (proj_le_iff_mul_left hcarrproj (cceil_isLeast _).1.1).mpr
      (cceil_isLeast _).1.2.2
  rw [hcc] at hmul
  -- `⌈a⌉ ≤ ⌈ωᵢ⌉`
  have hceille : ceil a ≤ npCarrier (ω i) :=
    ((ceil_basic_1 a _ ha hcarrproj).out 0 2).mp hmul
  -- and `⌈ωᵢ⌉ ≤ ⌈a⌉^⊥`, because `ωᵢ(⌈a⌉) = 0`
  have hceil0 : (ω i) (ceil a) = 0 := (ceil_functionals_lemma a ha (ω i)).mp h0
  have hcarrle : npCarrier (ω i) ≤ 1 - ceil a := by
    refine (carrier_spec (ω i).toPositiveLinearMap (ω i).preservesDirSups').2.2
      _ (ceil_spec ha).1.one_sub ?_
    show ((ω i : C → ℂ) (1 - (1 - ceil a))) = 0
    rw [sub_sub_cancel]
    exact hceil0
  have hself : ceil a * ceil a = 0 :=
    ((orthogonal_tuple_of_projections_1 (ceil a) (ceil a) (ceil_spec ha).1
      (ceil_spec ha).1).out 4 0).mp (hceille.trans hcarrle)
  refine (ceil_basic_3 a ha).mpr ?_
  rw [← (ceil_spec ha).1.isIdempotentElem.eq, hself]

/-- **70III** (`cvn`, vn.tex:3758, Theorem), the printed proof carried as far
as the tree allows: a commutative von Neumann algebra `C` is **nmiu-
isomorphic to the direct sum `⊕ᵢ cᵢC` of its corners**, for an orthogonal
family of *nonzero* central projections `cᵢ = ⌈⌈ωᵢ⌉⌉` with join `1`, each
corner being a **commutative von Neumann algebra** on which `ωᵢ` restricts to
a **faithful** np-functional.

This is 70IV's first two sentences verbatim: 70II at `c = 1` (`cvn`) followed
by 67IV.2 (`central_projections_sums_2_iso`).  The zero carriers of `cvn`'s
family are dropped — they contribute nothing to the join and would make the
corresponding summand the zero algebra, which Mathlib's `lp _ ∞` does not
admit (see `central_projections_sums_2_iso`).

The theorem's last sentence — "which is therefore by `cvn-faithful`
nmiu-isomorphic to `L^∞(Xᵢ)`" — is taken in `cvn_linfty` below, by
`A/VN/Basic`'s `cvn_faithful_4` (the isomorphism clause of 54XI.3, which used
to be missing there).  This declaration is kept as the intermediate step, and
because the *corners* are what the rest of the tree consumes. -/
theorem cvn_direct_sum {C : Type w} [CommCStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] [VonNeumannAlgebra C] :
    ∃ (ι : Type w) (ω : ι → NPFunctional C) (c : ι → CentralProj C)
      (_ : ∀ i, Nontrivial ((c i).sub)),
      (∀ i, (c i).val = cceil (npCarrier (ω i))) ∧
      (Pairwise fun i j => (c i).val * (c j).val = 0) ∧
      projSup (Set.range fun i => (c i).val) = 1 ∧
      (∀ (i : ι) (x y : (c i).sub), x * y = y * x) ∧
      (∀ (i : ι) (x : (c i).sub), 0 ≤ x → (c i).restrictNP (ω i) x = 0 → x = 0) ∧
      ∃ Φ : NMIUMap C (lp (fun i => (c i).sub) ∞),
        Function.Bijective ⇑Φ ∧
          ∀ (a : C) (i : ι),
            (((Φ a : lp (fun i => (c i).sub) ∞) : ∀ i, (c i).sub) i : C)
              = (c i).val * a := by
  classical
  obtain ⟨ι₀, ω₀, hpair₀, hsum₀, hfaith₀⟩ := cvn (C := C)
  -- discard the summands with `⌈⌈ωᵢ⌉⌉ = 0`
  set ι : Type w := {i : ι₀ // cceil (npCarrier (ω₀ i)) ≠ 0} with hι
  set ω : ι → NPFunctional C := fun i => ω₀ (i : ι₀) with hω
  have hcproj : ∀ i : ι, IsStarProjection (cceil (npCarrier (ω i))) :=
    fun i => (cceil_isLeast _).1.1
  have hccent : ∀ i : ι, IsCentral C (cceil (npCarrier (ω i))) :=
    fun i => (cceil_isLeast _).1.2.1
  set c : ι → CentralProj C := fun i => ⟨cceil (npCarrier (ω i)), hcproj i, hccent i⟩
    with hc
  have hntriv : ∀ i : ι, Nontrivial ((c i).sub) := by
    intro i
    refine ⟨⟨0, 1, ?_⟩⟩
    intro h
    exact i.2 (by
      have h2 := congrArg (fun z : (c i).sub => (z : C)) h
      exact h2.symm)
  have horth : Pairwise fun i j : ι => (c i).val * (c j).val = 0 := by
    intro i j hij
    exact hpair₀ (fun h => hij (Subtype.ext h))
  have hjoin : projSup (Set.range fun i : ι => (c i).val) = 1 := by
    have hPproj : ∀ p ∈ Set.range (fun i : ι => (c i).val), IsStarProjection p := by
      rintro _ ⟨i, rfl⟩; exact hcproj i
    refine projSup_eq hPproj (IsStarProjection.one C)
      (fun p hp => (hPproj p hp).le_one) ?_
    intro q hq hle
    rw [← hsum₀]
    refine (projSup_spec (fun p hp => by
      obtain ⟨i, rfl⟩ := hp; exact (cceil_isLeast _).1.1)).2.2 q hq ?_
    rintro _ ⟨i, rfl⟩
    show cceil (npCarrier (ω₀ i)) ≤ q
    by_cases h0 : cceil (npCarrier (ω₀ i)) = 0
    · rw [h0]; exact hq.nonneg
    · exact hle _ ⟨⟨i, h0⟩, rfl⟩
  refine ⟨ι, ω, c, hntriv, fun _ => rfl, horth, hjoin, ?_, ?_, ?_⟩
  · intro i x y
    exact Subtype.ext (mul_comm (x : C) (y : C))
  · intro i x hx h0
    exact Subtype.ext (hfaith₀ (i : ι₀) (x : C) hx x.2 h0)
  · obtain ⟨Φ, hbij, hval⟩ := central_projections_sums_2_iso c horth hjoin
    exact ⟨Φ, hbij, hval⟩


section Classification

open MeasureTheory WeakDual

/-- Auxiliary for **70III**: **54XI** at a single summand.  A *commutative*
von Neumann algebra `A` carrying a faithful np-functional `ω` **is** an
`L^∞(X)` for a finite complete measure space `X`.  `cvn_faithful_1` builds
the measure on the σ-algebra of almost clopen subsets of `spec A` (which is a
σ-algebra by 53V, `almostClopen_sigmaAlgebra`), and `cvn_faithful_4` — the
isomorphism clause of 54XI.3 — builds the presentation
`q : 𝓛^∞(spec A) → A`.

Commutativity is a *hypothesis* rather than an instance because the summands
of `cvn_direct_sum` are corners `cᵢ𝒜`, whose ambient `CStarAlgebra` instance
is the one `lp _ ∞` consumes; the `CommCStarAlgebra` structure is put on
inside the proof, as `A/Proc/Duplicators`'s `duplicable_forward` does at the
same point. -/
private theorem exists_linftyPresentation (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]
    (hcomm : ∀ x y : A, x * y = y * x) (ω : NPFunctional A)
    (hω : ∀ a : A, 0 ≤ a → ω a = 0 → a = 0) :
    ∃ (X : Type u) (_ : MeasurableSpace X) (μ : Measure X),
      IsFiniteMeasure μ ∧ μ.IsComplete ∧
      ∃ q : (X → ℂ) → A,
        (∀ y : A, ∃ f, IsBoundedMeasurable X f ∧ q f = y) ∧
        (∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
          q (f + g) = q f + q g) ∧
        (∀ (z : ℂ) f, IsBoundedMeasurable X f → q (z • f) = z • q f) ∧
        (∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
          q (f * g) = q f * q g) ∧
        (∀ f, IsBoundedMeasurable X f → q (star f) = star (q f)) ∧
        q 1 = 1 ∧
        (∀ f, IsBoundedMeasurable X f → (q f = 0 ↔ f =ᵐ[μ] 0)) := by
  letI : CommCStarAlgebra A := { ‹CStarAlgebra A› with mul_comm := hcomm }
  haveI : ExtremallyDisconnected (characterSpace ℂ A) :=
    vn_spectrum_extremally_disconnected (A := A)
  obtain ⟨μ, ⟨hnull, -, hfin, hcomp⟩, -⟩ := cvn_faithful_1 ω hω
  obtain ⟨q, hq⟩ := @cvn_faithful_4 A _ _ _ _ (almostClopenMS _)
    (almostClopen_sigmaAlgebra _) μ hnull
  exact ⟨characterSpace ℂ A, almostClopenMS _, μ, hfin, hcomp, q, hq.1, hq.2.1,
    hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2.1, hq.2.2.2.2.2.2.1⟩

/-- **70III** (`cvn`, vn.tex:3758, Theorem), in full: **every commutative von
Neumann algebra `C` is nmiu-isomorphic to a direct sum `⊕ᵢ L^∞(Xᵢ)`, where
the `Xᵢ` are finite complete measure spaces.**

The printed proof, in its three steps:

* 70II at `c = 1` gives `1 = ∑ᵢ ⌈⌈ωᵢ⌉⌉` with each `ωᵢ` faithful on its
  corner, by the thesis's observation that `⌈⌈ωᵢ⌉⌉ = ⌈ωᵢ⌉` in a commutative
  algebra (`cvn`);
* 67IV.2 gives the nmiu-isomorphism `C ≅ ⊕ᵢ ⌈⌈ωᵢ⌉⌉C` onto the corners
  (`cvn_direct_sum`);
* 54XI identifies each corner with an `L^∞(Xᵢ)` (`cvn_faithful_1` and
  `cvn_faithful_4`, packaged as `exists_linftyPresentation`).

`L^∞(Xᵢ)` is rendered exactly as 51IX `Linfty_vn` renders it — there is no
`L^∞` carrier in the tree — namely as an algebra `𝒜ᵢ` together with a
surjective map `qᵢ : 𝓛^∞(Xᵢ) → 𝒜ᵢ` that is additive, `ℂ`-homogeneous,
multiplicative, `∗`-preserving and unital and whose kernel is exactly the
`μᵢ`-a.e.-zero functions, i.e. that descends to a miu-isomorphism
`L^∞(Xᵢ) ≅ 𝒜ᵢ`.  Each `Xᵢ` is `spec(cᵢC)` with the almost clopen σ-algebra
and the measure of 54XI, and is finite and complete as 54XI says.

The direct sum is Mathlib's `lp 𝒜 ∞`, as everywhere else in the tree; the
`Nontrivial` binder on the summands is Mathlib's, not the thesis's (see
`central_projections_sums_2_iso`), and is why the zero corners are dropped.

`cvn` above is left as it stands — it is destructured at
`A/Proc/Duplicators.lean:4038`. -/
theorem cvn_linfty {C : Type w} [CommCStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] [VonNeumannAlgebra C] :
    ∃ (ι : Type w) (𝒜 : ι → Type w) (_ : ∀ i, CStarAlgebra (𝒜 i))
      (_ : ∀ i, Nontrivial (𝒜 i)) (_ : ∀ i, PartialOrder (𝒜 i))
      (_ : ∀ i, StarOrderedRing (𝒜 i)) (_ : ∀ i, VonNeumannAlgebra (𝒜 i))
      (X : ι → Type w) (_ : ∀ i, MeasurableSpace (X i))
      (μ : ∀ i, Measure (X i)),
      (∀ i, IsFiniteMeasure (μ i)) ∧
      (∀ i, (μ i).IsComplete) ∧
      (∀ (i : ι) (x y : 𝒜 i), x * y = y * x) ∧
      (∀ i, ∃ q : (X i → ℂ) → 𝒜 i,
        (∀ y : 𝒜 i, ∃ f, IsBoundedMeasurable (X i) f ∧ q f = y) ∧
        (∀ f g, IsBoundedMeasurable (X i) f → IsBoundedMeasurable (X i) g →
          q (f + g) = q f + q g) ∧
        (∀ (z : ℂ) f, IsBoundedMeasurable (X i) f → q (z • f) = z • q f) ∧
        (∀ f g, IsBoundedMeasurable (X i) f → IsBoundedMeasurable (X i) g →
          q (f * g) = q f * q g) ∧
        (∀ f, IsBoundedMeasurable (X i) f → q (star f) = star (q f)) ∧
        q 1 = 1 ∧
        (∀ f, IsBoundedMeasurable (X i) f → (q f = 0 ↔ f =ᵐ[μ i] 0))) ∧
      ∃ Φ : NMIUMap C (lp 𝒜 ∞), Function.Bijective ⇑Φ := by
  classical
  obtain ⟨ι, ω, c, hntriv, -, -, -, hcomm, hfaith, Φ, hbij, -⟩ :=
    cvn_direct_sum (C := C)
  choose X mX μ hfin hcomp q hq using fun i : ι =>
    exists_linftyPresentation ((c i).sub) (hcomm i) ((c i).restrictNP (ω i))
      (hfaith i)
  exact ⟨ι, fun i => (c i).sub, inferInstance, hntriv, inferInstance,
    inferInstance, inferInstance, X, mX, μ, hfin, hcomp, hcomm,
    fun i => ⟨q i, hq i⟩, Φ, hbij⟩

end Classification

end Theses.A.VN
