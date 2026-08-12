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

variable [VonNeumannAlgebra A]

/-- **56I** (`vna-ceil`, vn.tex:2362, Proposition), well-definedness (in the
uniform formulation of 59III `ceil-basic`): every positive `b` in a von
Neumann algebra has a least projection `p` with `b·p = b`. -/
theorem exists_ceil (b : A) (hb : 0 ≤ b) :
    ∃! p : A, IsStarProjection p ∧ b * p = b ∧
      ∀ q : A, IsStarProjection q → b * q = b → p ≤ q :=
  sorry

open scoped Classical in
/-- **56I**/**59I** (`vna-ceil`/`ceill`, vn.tex:2362/2684): the **ceiling**
`⌈b⌉` of a positive element `b` of a von Neumann algebra: the least
projection `p` with `b·p = b`.  For an effect `b` this is the least
projection above `b` (56I); for general positive `b` it agrees with the
extension `⌈b⌉ = ⌈‖b‖⁻¹·b⌉` of 59I.  (Junk value `0` off the positive
cone.) -/
noncomputable def ceil (b : A) : A :=
  if hb : 0 ≤ b then (exists_ceil b hb).choose else 0

/-- **56I** (`vna-ceil`, vn.tex:2362, Proposition): for an *effect* `b`,
`⌈b⌉` is the least projection above `b`. -/
theorem vna_ceil (b : A) (hb : b ∈ effects A) :
    IsLeast {p : A | IsStarProjection p ∧ b ≤ p} (ceil b) :=
  sorry

/-- **56I** (`vna-ceil`, vn.tex:2362, Proposition), formula:
`⌈b⌉ = ⋁ₙ b^{1/2ⁿ}` for an effect `b` (the iterated square roots). -/
theorem vna_ceil_sup (b : A) (hb : b ∈ effects A) :
    IsLUB (Set.range fun n : ℕ => (fun x : A => CFC.sqrt x)^[n] b) (ceil b) :=
  sorry

/-- **56I** (`vna-ceil`, vn.tex:2362, Proposition), moreover: whatever
commutes with `b` commutes with `⌈b⌉`. -/
theorem vna_ceil_comm (b : A) (hb : 0 ≤ b) (a : A) (h : a * b = b * a) :
    a * ceil b = ceil b * a :=
  sorry

/-- **56VI** (`vna-floor`, vn.tex:2419, Proposition), well-definedness:
every effect `b` of a von Neumann algebra has a greatest projection `p` with
`p·b = p`. -/
theorem exists_floor (b : A) (hb : b ∈ effects A) :
    ∃! p : A, IsStarProjection p ∧ p * b = p ∧
      ∀ q : A, IsStarProjection q → q * b = q → q ≤ p :=
  sorry

open scoped Classical in
/-- **56VI** (`vna-floor`, vn.tex:2419, Proposition): the **floor** `⌊b⌋` of
an effect `b` of a von Neumann algebra: the greatest projection below `b`
(characterized as the greatest projection `p` with `p·b = p`, cf. 56XI).
(Junk value `0` off the effects.) -/
noncomputable def floor (b : A) : A :=
  if hb : b ∈ effects A then (exists_floor b hb).choose else 0

/-- **56VI** (`vna-floor`, vn.tex:2419, Proposition): `⌊b⌋` is the greatest
projection below the effect `b`, and equals `⋀ₙ b^{2ⁿ}`. -/
theorem vna_floor (b : A) (hb : b ∈ effects A) :
    IsGreatest {p : A | IsStarProjection p ∧ p ≤ b} (floor b) ∧
      IsGLB (Set.range fun n : ℕ => b ^ (2 ^ n)) (floor b) :=
  sorry

/-- **56VI** (`vna-floor`, vn.tex:2419, Proposition), moreover: whatever
commutes with `b` commutes with `⌊b⌋`. -/
theorem vna_floor_comm (b : A) (hb : b ∈ effects A) (a : A)
    (h : a * b = b * a) : a * floor b = floor b * a :=
  sorry

/-- **56XI** (`ceil-floor-second-property`, vn.tex:2471, Exercise), part 1:
for an effect `a` and a projection `p`: `pa = a` iff `ap = a` iff
`⌈a⌉ ≤ p`.  In particular `⌈a⌉` is the least projection `p` with `a = ap`,
and `a = a⌈a⌉ = ⌈a⌉a`. -/
theorem ceil_floor_second_property_1 (a p : A) (ha : a ∈ effects A)
    (hp : IsStarProjection p) :
    List.TFAE [p * a = a, a * p = a, ceil a ≤ p] :=
  sorry

/-- **56XI** (`ceil-floor-second-property`, vn.tex:2471, Exercise), part 2:
for an effect `a` and a projection `p`: `pa = p` iff `ap = p` iff
`p ≤ ⌊a⌋`.  In particular `⌊a⌋` is the greatest projection `p` with
`p = ap`, and `⌊a⌋ = a⌊a⌋ = ⌊a⌋a`. -/
theorem ceil_floor_second_property_2 (a p : A) (ha : a ∈ effects A)
    (hp : IsStarProjection p) :
    List.TFAE [p * a = p, a * p = p, p ≤ floor a] :=
  sorry

/-! **56XII** (vn.tex:2491, Example): ceiling and floor in `L^∞(X)` —
descriptive example, not converted (cf. 51IX on `L^∞`). -/

/-- **56XIII** (`ceil-floor-basic`, vn.tex:2505, Exercise), part 1:
`⌈a⌉^⊥ = ⌊a^⊥⌋` and `⌊a⌋^⊥ = ⌈a^⊥⌉` for an effect `a`. -/
theorem ceil_floor_basic_1 (a : A) (ha : a ∈ effects A) :
    1 - ceil a = floor (1 - a) ∧ 1 - floor a = ceil (1 - a) :=
  sorry

/-- **56XIII** (`ceil-floor-basic`, vn.tex:2505, Exercise), part 2:
`⌈λa⌉ = ⌈a⌉` for `λ ∈ (0,1]`, and for `λ ∈ (0,1)` the projection
`⌈λa + λ^⊥b⌉` is the least projection above both `⌈a⌉` and `⌈b⌉` (the
supremum in the poset of projections). -/
theorem ceil_floor_basic_2 (a b : A) (ha : a ∈ effects A)
    (hb : b ∈ effects A) (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1) :
    ceil ((l : ℂ) • a) = ceil a ∧
      IsLeast {p : A | IsStarProjection p ∧ ceil a ≤ p ∧ ceil b ≤ p}
        (ceil ((l : ℂ) • a + ((1 - l : ℝ) : ℂ) • b)) :=
  sorry

/-- **56XIII** (`ceil-floor-basic`, vn.tex:2505, Exercise), part 3:
`⌊a⌋ = ⌊a²⌋` and `⌈a⌉ = ⌈a²⌉` for an effect `a`. -/
theorem ceil_floor_basic_3 (a : A) (ha : a ∈ effects A) :
    floor a = floor (a ^ 2) ∧ ceil a = ceil (a ^ 2) :=
  sorry

/-- **56XIV** (`vna-directed-supremum-projections`, vn.tex:2526, Lemma): the
supremum of a directed set of projections of a von Neumann algebra is a
projection. -/
theorem vna_directed_supremum_projections (D : Set A) (s : A)
    (hD : ∀ p ∈ D, IsStarProjection p) (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hs : IsLUB D s) :
    IsStarProjection s :=
  sorry

/-- **56XVI** (vn.tex:2542, Exercise), suprema: every set of projections of
a von Neumann algebra has a supremum `⋃A` *in the poset of projections*. -/
theorem exists_projSup (P : Set A) (hP : ∀ p ∈ P, IsStarProjection p) :
    ∃! s : A, IsStarProjection s ∧ (∀ p ∈ P, p ≤ s) ∧
      ∀ q : A, IsStarProjection q → (∀ p ∈ P, p ≤ q) → s ≤ q :=
  sorry

open scoped Classical in
/-- **56XVI** (vn.tex:2542, Exercise): the supremum `⋃P` of a set of
projections in the poset of projections (junk value `0` if `P` contains a
non-projection). -/
noncomputable def projSup (P : Set A) : A :=
  if hP : ∀ p ∈ P, IsStarProjection p then (exists_projSup P hP).choose else 0

/-- **56XVI** (vn.tex:2542, Exercise), infima: every set of projections of a
von Neumann algebra has an infimum `⋂A` in the poset of projections. -/
theorem exists_projInf (P : Set A) (hP : ∀ p ∈ P, IsStarProjection p) :
    ∃! s : A, IsStarProjection s ∧ (∀ p ∈ P, s ≤ p) ∧
      ∀ q : A, IsStarProjection q → (∀ p ∈ P, q ≤ p) → q ≤ s :=
  sorry

open scoped Classical in
/-- **56XVI** (vn.tex:2542, Exercise): the infimum `⋂P` of a set of
projections in the poset of projections (junk value `0`). -/
noncomputable def projInf (P : Set A) : A :=
  if hP : ∀ p ∈ P, IsStarProjection p then (exists_projInf P hP).choose else 0

/-- **56XVII** (`ceil-supremum`, vn.tex:2554, Exercise), part 1:
`⌈⋁D⌉ = ⋃_{d∈D} ⌈d⌉` for a directed set `D` of effects. -/
theorem ceil_supremum_1 (D : Set A) (s : A) (hD : ∀ d ∈ D, d ∈ effects A)
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hs : IsLUB D s) :
    ceil s = projSup (ceil '' D) :=
  sorry

/-- **56XVII** (`ceil-supremum`, vn.tex:2554, Exercise), part 2:
`⌊⋀D⌋ = ⋂_{d∈D} ⌊d⌋` for a filtered set `D` of effects. -/
theorem ceil_supremum_2 (D : Set A) (s : A) (hD : ∀ d ∈ D, d ∈ effects A)
    (hne : D.Nonempty) (hdir : DirectedOn (· ≥ ·) D) (hs : IsGLB D s) :
    floor s = projInf (floor '' D) :=
  sorry

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
    floor (CFC.sqrt a * b * CFC.sqrt a) = projInf {floor a, floor b} :=
  sorry

/-! ## Parsec 580

**58I** (vn.tex:2628): discussion — nothing to formalize. -/

/-- **58II** (`floor-difference`, vn.tex:2641, Lemma): for a projection `p`
and an effect `a ≤ p`: `p - ⌈a⌉ = ⌊p - a⌋`. -/
theorem floor_difference (p a : A) (hp : IsStarProjection p)
    (ha : a ∈ effects A) (hap : a ≤ p) :
    p - ceil a = floor (p - a) :=
  sorry

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
    ceil b = ceil ((‖b‖⁻¹ : ℂ) • b) :=
  sorry

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
    List.TFAE [p * a = a, a * p = a, ceil a ≤ p] :=
  sorry

/-- **59III** (`ceil-basic`, vn.tex:2728, Exercise), part 2:
`⌈a⌉a = a⌈a⌉`, and in fact whatever commutes with positive `a` commutes
with `⌈a⌉`. -/
theorem ceil_basic_2 (a b : A) (ha : 0 ≤ a) (h : b * a = a * b) :
    b * ceil a = ceil a * b :=
  sorry

/-- **59III** (`ceil-basic`, vn.tex:2728, Exercise), part 3: `a = 0` iff
`⌈a⌉ = 0` for positive `a`. -/
theorem ceil_basic_3 (a : A) (ha : 0 ≤ a) : a = 0 ↔ ceil a = 0 :=
  sorry

/-- **59III** (`ceil-basic`, vn.tex:2728, Exercise), part 4:
`⌈a⌉ = ⌈λa⌉` for `λ > 0`, and `⌈a + b⌉ = ⌈a⌉ ∪ ⌈b⌉` for positive `a`,
`b`. -/
theorem ceil_basic_4 (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) (l : ℝ)
    (hl : 0 < l) :
    ceil ((l : ℂ) • a) = ceil a ∧ ceil (a + b) = projSup {ceil a, ceil b} :=
  sorry

/-- **59III** (`ceil-basic`, vn.tex:2728, Exercise), part 5: `⌈a²⌉ = ⌈a⌉`
for positive `a`. -/
theorem ceil_basic_5 (a : A) (ha : 0 ≤ a) : ceil (a ^ 2) = ceil a :=
  sorry

/-- **59IV** (`ceil-pos-part`, vn.tex:2756, Exercise), part 1:
`⌈a₊⌉⌈a₋⌉ = 0` for self-adjoint `a`. -/
theorem ceil_pos_part_1 (a : A) (ha : IsSelfAdjoint a) :
    ceil (posPart a) * ceil (negPart a) = 0 :=
  sorry

/-- **59IV** (`ceil-pos-part`, vn.tex:2756, Exercise), part 2:
`⌈a₊⌉a = a⌈a₊⌉ = a₊` and `⌈a₋⌉a = a⌈a₋⌉ = -a₋` for self-adjoint `a`. -/
theorem ceil_pos_part_2 (a : A) (ha : IsSelfAdjoint a) :
    ceil (posPart a) * a = posPart a ∧
      a * ceil (posPart a) = posPart a ∧
      ceil (negPart a) * a = -negPart a ∧
      a * ceil (negPart a) = -negPart a :=
  sorry

/-- **59V** (`ceil-suprema`, vn.tex:2768, Exercise):
`⌈⋁D⌉ = ⋃_{d∈D} ⌈d⌉` for a bounded directed set `D` of *positive*
elements. -/
theorem ceil_suprema (D : Set A) (s : A) (hD : ∀ d ∈ D, 0 ≤ d)
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hs : IsLUB D s) :
    ceil s = projSup (ceil '' D) :=
  sorry

/-- **59VI** (`ceill-basic`, vn.tex:2773, Exercise), part 1: the support
`⌈a⌋ = ⌈a* a⌉` is the least projection `p` with `ap = a`. -/
theorem ceill_basic_1 (a : A) :
    IsLeast {p : A | IsStarProjection p ∧ a * p = a} (suppProj a) :=
  sorry

/-- **59VI** (`ceill-basic`, vn.tex:2773, Exercise), part 2: the range
`⌊a⌉ = ⌈a a*⌉` is the least projection `p` with `pa = a`. -/
theorem ceill_basic_2 (a : A) :
    IsLeast {p : A | IsStarProjection p ∧ p * a = a} (rangeProj a) :=
  sorry

/-- **59VI** (`ceill-basic`, vn.tex:2773, Exercise), part 3:
`⌈a*⌋ = ⌊a⌉` and `⌊a*⌉ = ⌈a⌋`. -/
theorem ceill_basic_3 (a : A) :
    suppProj (star a) = rangeProj a ∧ rangeProj (star a) = suppProj a :=
  sorry

/-- **59VI** (`ceill-basic`, vn.tex:2773, Exercise), part 4:
`⌈ab⌋ ≤ ⌈b⌋` and `⌊ab⌉ ≤ ⌊a⌉`. -/
theorem ceill_basic_4 (a b : A) :
    suppProj (a * b) ≤ suppProj b ∧ rangeProj (a * b) ≤ rangeProj a :=
  sorry

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

/-- **60I** (`ceil-functionals-lemma`, vn.tex:2817, Lemma): for positive `a`
and an np-functional `ω`: `ω(a) = 0` iff `ω(⌈a⌉) = 0`. -/
theorem ceil_functionals_lemma (a : A) (ha : 0 ≤ a) (ω : NPFunctional A) :
    ω a = 0 ↔ ω (ceil a) = 0 :=
  sorry

/-- **60III** (`ceil-functionals`, vn.tex:2855, Proposition): for positive
`a`, `b`: `⌈a⌉ ≤ ⌈b⌉` iff every np-functional vanishing on `b` vanishes on
`a`. -/
theorem ceil_functionals (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ceil a ≤ ceil b ↔
      ∀ ω : NPFunctional A, ω b = 0 → ω a = 0 :=
  sorry

/-- **60V** (`ncp-ceil`, vn.tex:2893, Proposition): for an np-map
`f : A → B` between von Neumann algebras and positive `a`:
`⌈f(a)⌉ = ⌈f(⌈a⌉)⌉`. -/
theorem ncp_ceil (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) (a : A)
    (ha : 0 ≤ a) : ceil (f a) = ceil (f (ceil a)) :=
  sorry

/-- **60VII** (`ceil-fundamental`, vn.tex:2906, Exercise), part 1:
`⌈a* b a⌉ = ⌈a* ⌈b⌉ a⌉` for `b ≥ 0`. -/
theorem ceil_fundamental_1 (a b : A) (hb : 0 ≤ b) :
    ceil (star a * b * a) = ceil (star a * ceil b * a) :=
  sorry

/-- **60VII** (`ceil-fundamental`, vn.tex:2906, Exercise), part 2:
`⌈ab⌋ = ⌈⌈a⌋b⌋` and `⌊ab⌉ = ⌊a⌊b⌉⌉`. -/
theorem ceil_fundamental_2 (a b : A) :
    suppProj (a * b) = suppProj (suppProj a * b) ∧
      rangeProj (a * b) = rangeProj (a * rangeProj b) :=
  sorry

/-- **60VIII** (`mult-cancellation`, vn.tex:2921, Exercise), part 1:
`cb = 0` iff `⌈c⌋⌊b⌉ = 0` iff `⌈c⌋ ≤ ⌊b⌉^⊥`. -/
theorem mult_cancellation_1 (b c : A) :
    List.TFAE
      [c * b = 0,
       suppProj c * rangeProj b = 0,
       suppProj c ≤ 1 - rangeProj b] :=
  sorry

/-- **60VIII** (`mult-cancellation`, vn.tex:2921, Exercise), part 2:
`c₁b = c₂b → c₁ = c₂` when `⌈cᵢ⌋ ≤ ⌊b⌉`. -/
theorem mult_cancellation_2 (b c₁ c₂ : A)
    (h₁ : suppProj c₁ ≤ rangeProj b) (h₂ : suppProj c₂ ≤ rangeProj b)
    (h : c₁ * b = c₂ * b) : c₁ = c₂ :=
  sorry

/-- **60VIII** (`mult-cancellation`, vn.tex:2921, Exercise), part 3:
`b* c₁ b = b* c₂ b → c₁ = c₂` for `c₁, c₂ ∈ ⌊b⌉A⌊b⌉`. -/
theorem mult_cancellation_3 (b c₁ c₂ : A)
    (h₁ : rangeProj b * c₁ * rangeProj b = c₁)
    (h₂ : rangeProj b * c₂ * rangeProj b = c₂)
    (h : star b * c₁ * b = star b * c₂ * b) : c₁ = c₂ :=
  sorry

/-- **60IX** (`ncp-union`, vn.tex:2942, Exercise), part 1:
`⌈f(p ∪ q)⌉ = ⌈f(p)⌉ ∪ ⌈f(q)⌉` for an np-map `f` and projections `p`,
`q`. -/
theorem ncp_union_1 (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) (p q : A)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ceil (f (projSup {p, q})) = projSup {ceil (f p), ceil (f q)} :=
  sorry

/-- **60IX** (`ncp-union`, vn.tex:2942, Exercise), part 2:
`⌈f(⋃P)⌉ = ⋃_{p∈P} ⌈f(p)⌉` for every set `P` of projections. -/
theorem ncp_union_2 (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) (P : Set A)
    (hP : ∀ p ∈ P, IsStarProjection p) :
    ceil (f (projSup P)) = projSup ((fun p => ceil (f p)) '' P) :=
  sorry

/-- **60IX** (`ncp-union`, vn.tex:2942, Exercise), part 3: there is a
greatest projection `e` with `f(e) = 0`. -/
theorem ncp_union_3 (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) :
    ∃ e : A, IsGreatest {p : A | IsStarProjection p ∧ f p = 0} e :=
  sorry

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
      ∀ q : A, IsStarProjection q → f (1 - q) = 0 → p ≤ q :=
  sorry

/-- **63I** (`carrier`, vn.tex:3043, Definition): the **carrier** `⌈f⌉` of
an np-map `f : A → B` between von Neumann algebras: the least projection
`p` with `f(p^⊥) = 0`. -/
noncomputable def carrier (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) : A :=
  (exists_carrier f hf).choose

/-- **63I** (`carrier`, vn.tex:3043, Definition), specialized to
np-functionals: the carrier `⌈ω⌉` of `ω : A → ℂ`. -/
noncomputable def npCarrier (ω : NPFunctional A) : A :=
  carrier ω.toPositiveLinearMap ω.preservesDirSups'

/-- **63II** (`carrier-basic`, vn.tex:3054, Exercise), part 1:
`⌈λf⌉ = ⌈f⌉` for `λ > 0` (the scaled map given pointwise). -/
theorem carrier_basic_1 (f g : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f)
    (hg : PreservesDirSups ⇑g) (l : ℝ) (hl : 0 < l)
    (h : ∀ a, g a = (l : ℂ) • f a) :
    carrier g hg = carrier f hf :=
  sorry

/-- **63II** (`carrier-basic`, vn.tex:3054, Exercise), part 2:
`⌈f + g⌉ = ⌈f⌉ ∪ ⌈g⌉` (the sum given pointwise). -/
theorem carrier_basic_2 (f g h : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f)
    (hg : PreservesDirSups ⇑g) (hh : PreservesDirSups ⇑h)
    (hsum : ∀ a, h a = f a + g a) :
    carrier h hh = projSup {carrier f hf, carrier g hg} :=
  sorry

/-- **63II** (`carrier-basic`, vn.tex:3054, Exercise), part 3: `⌈f⌉ = 1` iff
`f` is faithful. -/
theorem carrier_basic_3 (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) :
    carrier f hf = 1 ↔ ∀ a : A, 0 ≤ a → f a = 0 → a = 0 :=
  sorry

/-- **63II** (`carrier-basic`, vn.tex:3054, Exercise), part 4: for
multiplicative `f`: `⌈f⌉ = 1` iff `f` is injective. -/
theorem carrier_basic_4 (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f)
    (hmul : ∀ a b : A, f (a * b) = f a * f b) :
    carrier f hf = 1 ↔ Function.Injective ⇑f :=
  sorry

/-- **63III** (vn.tex:3074, Exercise), part 1: `⌈a*(·)a⌉ = ⌈aa*⌉ = ⌊a⌉` for
the np-map `a*(·)a : A → A`. -/
theorem carrier_ad (a : A) (g : A →ₚ[ℂ] A) (hg : PreservesDirSups ⇑g)
    (h : ∀ b, g b = star a * b * a) :
    carrier g hg = rangeProj a :=
  sorry

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
    npCarrier ω = ketbra x x :=
  sorry

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
      f a = f (carrier f hf * a * carrier f hf) :=
  sorry

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

/-- **68III** (`central support`, vn.tex:3472, Definition),
well-definedness: every element `a` of a von Neumann algebra has a least
central projection `p` with `pa = a`. -/
theorem exists_cceil (a : A) :
    ∃! p : A, IsStarProjection p ∧ IsCentral A p ∧ p * a = a ∧
      ∀ q : A, IsStarProjection q → IsCentral A q → q * a = a → p ≤ q :=
  sorry

/-- **68III** (`central support`, vn.tex:3472, Definition): the **central
support** `⌈⌈a⌉⌉` of `a`: the least central projection `p` with
`pa = a`. -/
noncomputable def cceil (a : A) : A := (exists_cceil a).choose

/-- **68I** (`cceil-fundamental`, vn.tex:3437, Proposition): for a
projection `e`, `⌈⌈e⌉⌉ = ⋃_{a∈A} ⌈a* e a⌉` is the least central projection
above `e`. -/
theorem cceil_fundamental (e : A) (he : IsStarProjection e) :
    IsLeast {p : A | IsStarProjection p ∧ IsCentral A p ∧ e ≤ p} (cceil e) ∧
      cceil e = projSup {x : A | ∃ a : A, x = ceil (star a * e * a)} :=
  sorry

/-- **68III** (`central support`, vn.tex:3472, Definition), embedded claims:
`⌈⌈a⌉⌉ = ⌈⌈⌈a⌋⌉⌉ = ⌈⌈⌊a⌉⌉⌉`, and for a central projection `c`:
`⌈⌈a⌉⌉ ≤ c` iff `ac = a` iff `ca = a`. -/
theorem cceil_eq_cceil_supp (a : A) :
    cceil a = cceil (suppProj a) ∧ cceil a = cceil (rangeProj a) ∧
      ∀ c : A, IsStarProjection c → IsCentral A c →
        ((cceil a ≤ c ↔ a * c = a) ∧ (cceil a ≤ c ↔ c * a = a)) :=
  sorry

/-- **68IV** (`cceil-basic`, vn.tex:3490, Exercise), part 1:
`⌈⌈a⌉⌉ = ⌈⌈a*⌉⌉ = ⌈⌈a*a⌉⌉ = ⌈⌈aa*⌉⌉`. -/
theorem cceil_basic_1 (a : A) :
    cceil a = cceil (star a) ∧ cceil a = cceil (star a * a) ∧
      cceil a = cceil (a * star a) :=
  sorry

/-- **68IV** (`cceil-basic`, vn.tex:3490, Exercise), part 2:
`⌈⌈⋁D⌉⌉ = ⋃_{d∈D} ⌈⌈d⌉⌉` for bounded directed `D`;
`⌈⌈⋃E⌉⌉ = ⋃_{e∈E} ⌈⌈e⌉⌉` for sets of projections `E`; and
`⌈⌈a+b⌉⌉ = ⌈⌈a⌉⌉ ∪ ⌈⌈b⌉⌉` for positive `a`, `b`. -/
theorem cceil_basic_2 (D : Set (selfAdjoint A)) (s : selfAdjoint A)
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hs : IsLUB D s)
    (E : Set A) (hE : ∀ e ∈ E, IsStarProjection e) (a b : A) (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    cceil (s : A) = projSup ((fun d : selfAdjoint A => cceil (d : A)) '' D) ∧
      cceil (projSup E) = projSup (cceil '' E) ∧
      cceil (a + b) = projSup {cceil a, cceil b} :=
  sorry

/-- **68IV** (`cceil-basic`, vn.tex:3490, Exercise), part 3:
`⌈⌈a⌉⌉c = ⌈⌈ac⌉⌉` for central projections `c`; consequently
`⌈⌈a⌉⌉⌈⌈b⌉⌉ = ⌈⌈a⌈⌈b⌉⌉⌉⌉ = ⌈⌈⌈⌈a⌉⌉b⌉⌉ = ⌈⌈a⌉⌉ ∩ ⌈⌈b⌉⌉`. -/
theorem cceil_basic_3 (a b c : A) (hc : IsStarProjection c)
    (hcentral : IsCentral A c) :
    cceil a * c = cceil (a * c) ∧
      cceil a * cceil b = cceil (a * cceil b) ∧
      cceil a * cceil b = projInf {cceil a, cceil b} :=
  sorry

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
      (carrier f hf ≤ c ↔ cceilMap f hf ≤ c) :=
  sorry

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
      ∀ a : A, f a = 0 ↔ carrier g hg * a = 0 :=
  sorry

/-- **69IVa** (`nmiu-factors`, vn.tex:3619, Exercise): an nmiu-map
`f : A → B` factors through the corner `⌈⌈f⌉⌉A` as an nmiu-surjection
`a ↦ ⌈⌈f⌉⌉a` followed by an nmiu-injection — rendered concretely:
`f(a) = f(⌈f⌉a)` for all `a`, and `f(a) = f(b)` iff `⌈f⌉a = ⌈f⌉b`. -/
theorem nmiu_factors (f : NMIUMap A B) (g : A →ₚ[ℂ] B)
    (hg : PreservesDirSups ⇑g) (heq : ∀ a, g a = f a) (a b : A) :
    f a = f (carrier g hg * a) ∧
      (f a = f b ↔ carrier g hg * a = carrier g hg * b) :=
  sorry

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
