/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 2: Von Neumann Algebras — vn.tex, lines
5000–6230.

  §Division
    (Approximate) Pseudoinverses  (parsecs 790–800)
    Division                      (parsec 810: Douglas' lemma, quotients)
    Polar Decomposition           (parsecs 820–830: polar decomposition,
                                   the Murray–von Neumann preorder,
                                   finite-dimensional C*-algebras)
    No Equalisers in CStar_pu     (parsec 841)
    Hereditarily Atomic Von Neumann Algebras  (parsec 842)

See `Theses/A/VN/Basic.lean` for the topologies and
`Theses/A/VN/Projections.lean` for `ceil`, `suppProj` (`⌈a⌋`), `rangeProj`
(`⌊a⌉`), `projSup`, `cceil`.
-/
import Theses.A.VN.Completeness
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Analysis.Matrix.Spectrum

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra ENNReal
open Filter Topology Theses Theses.A.CStar

universe u

namespace Theses.A.VN

variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-! ## Parsec 790: pseudoinverses

**78I** (vn.tex:5003): overview of the division problem — nothing to
formalize. -/

section Pseudoinverse

variable [VonNeumannAlgebra A]

variable (A) in
/-- **79I** (`dfn-pseudoinverse`, vn.tex:5090, Definition): `t` is a
**pseudoinverse** of `a` when `ta = ⌈a⌋ = ⌊t⌉` and `at = ⌈t⌋ = ⌊a⌉`. -/
def IsPseudoinverse (a t : A) : Prop :=
  t * a = suppProj a ∧ t * a = rangeProj t ∧
    a * t = suppProj t ∧ a * t = rangeProj a

variable (A) in
/-- **79I** (`dfn-pseudoinverse`, vn.tex:5090, Definition): `a` is
**pseudoinvertible** when it has a pseudoinverse. -/
def Pseudoinvertible (a : A) : Prop := ∃ t : A, IsPseudoinverse A a t

/-- **79I** (`dfn-pseudoinverse`, vn.tex:5090, Definition), embedded claim:
the pseudoinverse is unique when it exists (by **60VIII**,
`mult_cancellation`). -/
theorem isPseudoinverse_unique (a t t' : A) (h : IsPseudoinverse A a t)
    (h' : IsPseudoinverse A a t') : t = t' :=
  -- `ta = ⌈a⌋ = t'a` and `⌈t⌋ = ⌊a⌉ = ⌈t'⌋`, so **60VIII** applies
  mult_cancellation_2 a t t' (le_of_eq (h.2.2.1.symm.trans h.2.2.2))
    (le_of_eq (h'.2.2.1.symm.trans h'.2.2.2)) (h.1.trans h'.1.symm)

open scoped Classical in
/-- **79I** (`dfn-pseudoinverse`, vn.tex:5090, Definition): the
pseudoinverse `a^{∼1}` of `a` (junk value `0` when `a` is not
pseudoinvertible). -/
noncomputable def pinv (a : A) : A :=
  if h : Pseudoinvertible A a then h.choose else 0

/-- The defining property of `a^{∼1}` (for pseudoinvertible `a`). -/
theorem pinv_spec {a : A} (h : Pseudoinvertible A a) :
    IsPseudoinverse A a (pinv a) := by
  rw [pinv, dif_pos h]
  exact h.choose_spec

/-- Auxiliary: `⌊a*⌉ = ⌈a⌋`. -/
theorem rangeProj_star (a : A) : rangeProj (star a) = suppProj a := by
  rw [rangeProj, suppProj, star_star]

/-- Auxiliary: `⌈a*⌋ = ⌊a⌉`. -/
theorem suppProj_star (a : A) : suppProj (star a) = rangeProj a := by
  rw [rangeProj, suppProj, star_star]

/-- Auxiliary: `⌈p⌋ = p` for a projection `p`. -/
theorem suppProj_of_isStarProjection {p : A} (hp : IsStarProjection p) :
    suppProj p = p := by
  rw [suppProj, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq,
    ceil_of_isStarProjection hp]

/-- Auxiliary: `⌊p⌉ = p` for a projection `p`. -/
theorem rangeProj_of_isStarProjection {p : A} (hp : IsStarProjection p) :
    rangeProj p = p := by
  rw [rangeProj, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq,
    ceil_of_isStarProjection hp]

/-- Auxiliary: `⌈x⌋ = ⌈x⌉` for positive `x` — both are the least projection
`q` with `xq = x`. -/
theorem suppProj_of_nonneg {x : A} (hx : 0 ≤ x) : suppProj x = ceil x := by
  obtain ⟨h1, h2, h3⟩ := ceil_spec hx
  exact (ceill_basic_1 x).unique ⟨⟨h1, h2⟩, fun q hq => h3 q hq.1 hq.2⟩

/-- Auxiliary: `⌈xy⌋ ≤ ⌈y⌋`. -/
theorem suppProj_mul_le (x y : A) : suppProj (x * y) ≤ suppProj y :=
  (ceill_basic_1 (x * y)).2
    ⟨(ceill_basic_1 y).1.1, by rw [mul_assoc, (ceill_basic_1 y).1.2]⟩

/-- Auxiliary: `⌊xy⌉ ≤ ⌊x⌉`. -/
theorem rangeProj_mul_le (x y : A) : rangeProj (x * y) ≤ rangeProj x :=
  (ceill_basic_2 (x * y)).2
    ⟨(ceill_basic_2 x).1.1, by rw [← mul_assoc, (ceill_basic_2 x).1.2]⟩

/-- **60VIII** (`mult-cancellation`), left-handed version: `bc₁ = bc₂` with
`⌊c₁⌉, ⌊c₂⌉ ≤ ⌈b⌋` forces `c₁ = c₂`. -/
theorem mult_cancellation_left (b c₁ c₂ : A)
    (h₁ : rangeProj c₁ ≤ suppProj b) (h₂ : rangeProj c₂ ≤ suppProj b)
    (h : b * c₁ = b * c₂) : c₁ = c₂ := by
  have hs : star c₁ = star c₂ :=
    mult_cancellation_2 (star b) (star c₁) (star c₂)
      (by rw [suppProj_star, rangeProj_star]; exact h₁)
      (by rw [suppProj_star, rangeProj_star]; exact h₂)
      (by rw [← star_mul, ← star_mul, h])
  have hst := congrArg star hs
  rwa [star_star, star_star] at hst

variable (A) in
/-- **79I** (`dfn-pseudoinverse`, vn.tex:5090, Definition): `u` is a
**partial isometry** when `u*` is its pseudoinverse. -/
def IsPartialIsometry (u : A) : Prop := IsPseudoinverse A u (star u)

/-- **79II** (`pseudoinverse-equivalents`, vn.tex:5109, Lemma): for
elements `a`, `t` of a von Neumann algebra the following are equivalent:
(1) `ta` is a projection and `⌈t⌋ = ⌊a⌉`; (2) `ata = a`, `⌈t⌋ ≤ ⌊a⌉` and
`⌊t⌉ ≤ ⌈a⌋`; (3) `at` is a projection and `⌈a⌋ = ⌊t⌉`; (4) `tat = t`,
`⌈a⌋ ≤ ⌊t⌉` and `⌊a⌉ ≤ ⌈t⌋`; (5) `t` is a pseudoinverse of `a`; (6) `a`
is a pseudoinverse of `t`. -/
theorem pseudoinverse_equivalents (a t : A) :
    List.TFAE
      [IsStarProjection (t * a) ∧ suppProj t = rangeProj a,
       a * t * a = a ∧ suppProj t ≤ rangeProj a ∧
         rangeProj t ≤ suppProj a,
       IsStarProjection (a * t) ∧ suppProj a = rangeProj t,
       t * a * t = t ∧ suppProj a ≤ rangeProj t ∧
         rangeProj a ≤ suppProj t,
       IsPseudoinverse A a t,
       IsPseudoinverse A t a] := by
  -- (3), (4), (6) are (1), (2), (5) with `a` and `t` interchanged, so it is
  -- enough to prove (1)→(2)→(5)→(1) for all `x`, `y` — which is the author's
  -- argument, `mult-cancellation` (**60VIII**) throughout.
  have L1 : ∀ x y : A, IsStarProjection (y * x) → suppProj y = rangeProj x →
      x * y * x = x ∧ suppProj y ≤ rangeProj x ∧ rangeProj y ≤ suppProj x := by
    intro x y hp hq
    have hsy := (ceill_basic_1 y).1
    -- `⌊y⌉ = ⌊y⌈y⌋⌉ = ⌊y⌊x⌉⌉ = ⌊yx⌉ = yx = ⌈yx⌋ ≤ ⌈x⌋`
    have h3 : rangeProj y ≤ suppProj x := by
      have e1 : rangeProj y = y * x := by
        conv_lhs => rw [← hsy.2]
        rw [hq, ← (ceil_fundamental_2 y x).2, rangeProj_of_isStarProjection hp]
      rw [e1, ← suppProj_of_isStarProjection hp]
      exact suppProj_mul_le y x
    refine ⟨?_, le_of_eq hq, h3⟩
    -- `y(xyx) = (yx)(yx) = yx = yx`, and cancel `y` on the left
    refine mult_cancellation_left y (x * y * x) x
      (le_trans (le_trans (rangeProj_mul_le (x * y) x) (rangeProj_mul_le x y))
        (le_of_eq hq.symm))
      (le_of_eq hq.symm) ?_
    calc y * (x * y * x) = y * x * (y * x) := by noncomm_ring
      _ = y * x := hp.isIdempotentElem.eq
  have L2 : ∀ x y : A, x * y * x = x → suppProj y ≤ rangeProj x →
      rangeProj y ≤ suppProj x → IsPseudoinverse A x y := by
    intro x y h1 h2 h3
    have hsx := (ceill_basic_1 x).1
    have hrx := (ceill_basic_2 x).1
    -- `yx = ⌈x⌋`: cancel `x` on the left in `x(yx) = x = x⌈x⌋`
    have e1 : y * x = suppProj x := by
      refine mult_cancellation_left x (y * x) (suppProj x)
        (le_trans (rangeProj_mul_le y x) h3)
        (le_of_eq (rangeProj_of_isStarProjection hsx.1)) ?_
      rw [← mul_assoc, h1, hsx.2]
    -- `xy = ⌊x⌉`: cancel `x` on the right in `(xy)x = x = ⌊x⌉x`
    have e2 : x * y = rangeProj x := by
      refine mult_cancellation_2 x (x * y) (rangeProj x)
        (le_trans (suppProj_mul_le x y) h2)
        (le_of_eq (suppProj_of_isStarProjection hrx.1)) ?_
      rw [h1, hrx.2]
    have e3 : suppProj y = rangeProj x := by
      refine le_antisymm h2 ?_
      have hle : suppProj (x * y) ≤ suppProj y := suppProj_mul_le x y
      rwa [e2, suppProj_of_isStarProjection hrx.1] at hle
    have e4 : rangeProj y = suppProj x := by
      refine le_antisymm h3 ?_
      have hle : rangeProj (y * x) ≤ rangeProj y := rangeProj_mul_le y x
      rwa [e1, rangeProj_of_isStarProjection hsx.1] at hle
    exact ⟨e1, by rw [e1, ← e4], by rw [e2, ← e3], e2⟩
  have L3 : ∀ x y : A, IsPseudoinverse A x y →
      IsStarProjection (y * x) ∧ suppProj y = rangeProj x := fun x y h =>
    ⟨by rw [h.1]; exact (ceill_basic_1 x).1.1, h.2.2.1.symm.trans h.2.2.2⟩
  tfae_have 1 → 2 := fun h => L1 a t h.1 h.2
  tfae_have 2 → 5 := fun h => L2 a t h.1 h.2.1 h.2.2
  tfae_have 5 → 1 := fun h => L3 a t h
  tfae_have 3 → 4 := fun h => L1 t a h.1 h.2
  tfae_have 4 → 6 := fun h => L2 t a h.1 h.2.1 h.2.2
  tfae_have 6 → 3 := fun h => L3 t a h
  tfae_have 5 → 6 := fun h => ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩
  tfae_have 6 → 5 := fun h => ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩
  tfae_finish

/-- **79IV** (`partial-isometry-equivalents`, vn.tex:5172, Exercise): `u`
is a partial isometry iff `u*u` is a projection iff `uu*u = u` iff `uu*`
is a projection iff `u*uu* = u*`. -/
theorem partial_isometry_equivalents (u : A) :
    List.TFAE
      [IsPartialIsometry A u,
       IsStarProjection (star u * u),
       u * star u * u = u,
       IsStarProjection (u * star u),
       star u * u * star u = star u] := by
  -- the crux is `⟹`: if `p = v*v` is a projection then `(v − vp)*(v − vp) = 0`
  have key : ∀ v : A, IsStarProjection (star v * v) → v * star v * v = v := by
    intro v hp
    have hz : star (v - v * (star v * v)) * (v - v * (star v * v)) = 0 := by
      have hps : star (star v * v) = star v * v := hp.isSelfAdjoint.star_eq
      have hpp : (star v * v) * (star v * v) = star v * v := hp.isIdempotentElem.eq
      calc star (v - v * (star v * v)) * (v - v * (star v * v))
          = (star v - (star v * v) * star v) * (v - v * (star v * v)) := by
            rw [star_sub, star_mul, hps]
        _ = (star v * v) - (star v * v) * (star v * v)
              - ((star v * v) * (star v * v)
                - ((star v * v) * (star v * v)) * (star v * v)) := by noncomm_ring
        _ = 0 := by simp only [hpp]; abel
    have hv := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
    rw [sub_eq_zero] at hv
    conv_rhs => rw [hv]
    noncomm_ring
  have hproj : ∀ v : A, v * star v * v = v → IsStarProjection (star v * v) := by
    intro v h
    refine ⟨?_, ?_⟩
    · show star v * v * (star v * v) = star v * v
      calc star v * v * (star v * v) = star v * (v * star v * v) := by noncomm_ring
        _ = star v * v := by rw [h]
    · show star (star v * v) = star v * v
      rw [star_mul, star_star]
  have hproj2 : ∀ v : A, v * star v * v = v → IsStarProjection (v * star v) := by
    intro v h
    refine ⟨?_, ?_⟩
    · show v * star v * (v * star v) = v * star v
      calc v * star v * (v * star v) = v * star v * v * star v := by noncomm_ring
        _ = v * star v := by rw [h]
    · show star (v * star v) = v * star v
      rw [star_mul, star_star]
  have hflip : ∀ v : A, v * star v * v = v → star v * v * star v = star v := by
    intro v h
    have hs := congrArg star h
    simp only [star_mul, star_star] at hs
    first
      | exact hs
      | (rw [← mul_assoc] at hs; exact hs)
  tfae_have 1 → 2 := fun h => h.1 ▸ (ceill_basic_1 u).1.1
  tfae_have 2 → 3 := key u
  tfae_have 3 → 4 := hproj2 u
  tfae_have 4 → 5 := by
    intro h
    have h' : IsStarProjection (star (star u) * star u) := by rwa [star_star]
    have hk := key (star u) h'
    rwa [star_star] at hk
  tfae_have 5 → 3 := by
    intro h
    have hs := hflip (star u) (by rwa [star_star])
    rwa [star_star] at hs
  tfae_have 3 → 1 := by
    intro h
    have h2 : IsStarProjection (star u * u) := hproj u h
    have h4 : IsStarProjection (u * star u) := hproj2 u h
    have hs : suppProj u = star u * u := by
      rw [suppProj, ceil_of_isStarProjection h2]
    have hr : rangeProj u = u * star u := by
      rw [rangeProj, ceil_of_isStarProjection h4]
    exact ⟨hs.symm, by rw [rangeProj_star, hs], by rw [suppProj_star, hr],
      hr.symm⟩
  tfae_finish

/-- **79V** (`pseudoinverse-basic`, vn.tex:5183, Exercise), part 1: `a` is
pseudoinvertible iff `a*` is, and then `(a*)^{∼1} = (a^{∼1})*`. -/
theorem pseudoinverse_basic_1 (a : A) :
    (Pseudoinvertible A a ↔ Pseudoinvertible A (star a)) ∧
      (Pseudoinvertible A a → pinv (star a) = star (pinv a)) := by
  -- the four defining equations of `IsPseudoinverse` are permuted by `(·)*`
  have hstar : ∀ x y : A, IsPseudoinverse A x y →
      IsPseudoinverse A (star x) (star y) := by
    intro x y h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← star_mul, h4, suppProj_star]
      exact (ceill_basic_2 x).1.1.isSelfAdjoint.star_eq
    · rw [← star_mul, h3, rangeProj_star]
      exact (ceill_basic_1 y).1.1.isSelfAdjoint.star_eq
    · rw [← star_mul, h2, suppProj_star]
      exact (ceill_basic_2 y).1.1.isSelfAdjoint.star_eq
    · rw [← star_mul, h1, rangeProj_star]
      exact (ceill_basic_1 x).1.1.isSelfAdjoint.star_eq
  have hiff : Pseudoinvertible A a ↔ Pseudoinvertible A (star a) := by
    constructor
    · rintro ⟨t, ht⟩; exact ⟨star t, hstar a t ht⟩
    · rintro ⟨t, ht⟩
      refine ⟨star t, ?_⟩
      have := hstar (star a) t ht
      rwa [star_star] at this
  refine ⟨hiff, fun h => ?_⟩
  exact isPseudoinverse_unique (star a) _ _ (pinv_spec (hiff.mp h))
    (hstar a (pinv a) (pinv_spec h))

/-- **79V** (`pseudoinverse-basic`, vn.tex:5183, Exercise), part 2: if `a`,
`b` are pseudoinvertible and `⌊b⌉ = ⌈a⌋`, then `ab` is pseudoinvertible
with `(ab)^{∼1} = b^{∼1}a^{∼1}`. -/
theorem pseudoinverse_basic_2 (a b : A) (ha : Pseudoinvertible A a)
    (hb : Pseudoinvertible A b) (hab : rangeProj b = suppProj a) :
    Pseudoinvertible A (a * b) ∧ pinv (a * b) = pinv b * pinv a := by
  obtain ⟨hs1, hs2, hs3, hs4⟩ := pinv_spec ha
  obtain ⟨ht1, ht2, ht3, ht4⟩ := pinv_spec hb
  set s : A := pinv a with hsdef
  set t : A := pinv b with htdef
  have hsa := (ceill_basic_1 a).1
  have hrb := (ceill_basic_2 b).1
  -- `⌊ab⌉ = ⌊a⌊b⌉⌉ = ⌊a⌈a⌋⌉ = ⌊a⌉` and dually `⌈ab⌋ = ⌈b⌋`
  have hrab : rangeProj (a * b) = rangeProj a := by
    rw [(ceil_fundamental_2 a b).2, hab, hsa.2]
  have hsab : suppProj (a * b) = suppProj b := by
    rw [(ceil_fundamental_2 a b).1, ← hab, hrb.2]
  -- `(ab)(ts)(ab) = a⌊b⌉⌈a⌋b = a⌈a⌋b = ab`
  have hmain : a * b * (t * s) * (a * b) = a * b := by
    calc a * b * (t * s) * (a * b) = a * (b * t) * (s * a) * b := by noncomm_ring
      _ = a * suppProj a * suppProj a * b := by rw [ht4, hs1, hab]
      _ = a * b := by rw [hsa.2, hsa.2]
  have hpseudo : IsPseudoinverse A (a * b) (t * s) := by
    have hcond : a * b * (t * s) * (a * b) = a * b ∧
        suppProj (t * s) ≤ rangeProj (a * b) ∧
        rangeProj (t * s) ≤ suppProj (a * b) := by
      refine ⟨hmain, ?_, ?_⟩
      · rw [hrab]
        exact le_trans (suppProj_mul_le t s) (le_of_eq (hs3.symm.trans hs4))
      · rw [hsab]
        exact le_trans (rangeProj_mul_le t s) (le_of_eq (ht2.symm.trans ht1))
    exact ((pseudoinverse_equivalents (a * b) (t * s)).out 1 4).mp hcond
  exact ⟨⟨t * s, hpseudo⟩,
    isPseudoinverse_unique (a * b) _ _ (pinv_spec ⟨t * s, hpseudo⟩) hpseudo⟩

/-- **79V** (`pseudoinverse-basic`, vn.tex:5183, Exercise), part 3: `a` is
pseudoinvertible iff `a*a` is, and then `a^{∼1} = (a*a)^{∼1}a*` and
`(a*a)^{∼1} = a^{∼1}(a^{∼1})*`. -/
theorem pseudoinverse_basic_3 (a : A) :
    (Pseudoinvertible A a ↔ Pseudoinvertible A (star a * a)) ∧
      (Pseudoinvertible A a →
        pinv a = pinv (star a * a) * star a ∧
          pinv (star a * a) = pinv a * star (pinv a)) := by
  -- `⟹` is **79V**.1 + **79V**.2 applied to `a* · a`; `⟸` is the explicit
  -- candidate `u a*` for `u` a pseudoinverse of `a*a`
  have hsupp : suppProj (star a * a) = suppProj a :=
    suppProj_of_nonneg (star_mul_self_nonneg a)
  have hback : ∀ u : A, IsPseudoinverse A (star a * a) u →
      IsPseudoinverse A a (u * star a) := by
    intro u hu
    obtain ⟨hu1, hu2, -, -⟩ := hu
    have hcond : a * (u * star a) * a = a ∧
        suppProj (u * star a) ≤ rangeProj a ∧
        rangeProj (u * star a) ≤ suppProj a := by
      refine ⟨?_, ?_, ?_⟩
      · calc a * (u * star a) * a = a * (u * (star a * a)) := by noncomm_ring
          _ = a * suppProj a := by rw [hu1, hsupp]
          _ = a := (ceill_basic_1 a).1.2
      · calc suppProj (u * star a) ≤ suppProj (star a) := suppProj_mul_le u (star a)
          _ = rangeProj a := suppProj_star a
      · calc rangeProj (u * star a) ≤ rangeProj u := rangeProj_mul_le u (star a)
          _ = suppProj (star a * a) := hu2.symm.trans hu1
          _ = suppProj a := hsupp
    exact ((pseudoinverse_equivalents a (u * star a)).out 1 4).mp hcond
  have hfwd : Pseudoinvertible A a → Pseudoinvertible A (star a * a) ∧
      pinv (star a * a) = pinv a * pinv (star a) := fun h =>
    pseudoinverse_basic_2 (star a) a ((pseudoinverse_basic_1 a).1.mp h) h
      (suppProj_star a).symm
  have hiff : Pseudoinvertible A a ↔ Pseudoinvertible A (star a * a) := by
    refine ⟨fun h => (hfwd h).1, ?_⟩
    rintro ⟨u, hu⟩
    exact ⟨u * star a, hback u hu⟩
  refine ⟨hiff, fun h => ⟨?_, ?_⟩⟩
  · exact isPseudoinverse_unique a _ _ (pinv_spec h)
      (hback (pinv (star a * a)) (pinv_spec (hiff.mp h)))
  · rw [(hfwd h).2, (pseudoinverse_basic_1 a).2 h]

/-- Auxiliary: `⌊a⌉ = ⌈a⌋` for self-adjoint `a` (both are `⌈a²⌉`). -/
theorem rangeProj_eq_suppProj_of_isSelfAdjoint {a : A} (ha : IsSelfAdjoint a) :
    rangeProj a = suppProj a := by
  rw [rangeProj, suppProj, ha.star_eq]

/-- Auxiliary: the pseudoinverse of a self-adjoint element is self-adjoint. -/
theorem pinv_isSelfAdjoint {a : A} (ha : IsSelfAdjoint a)
    (h : Pseudoinvertible A a) : IsSelfAdjoint (pinv a) := by
  set t := pinv a with htdef
  obtain ⟨e1, e2, e3, e4⟩ := pinv_spec h
  have hsa : star (suppProj a) = suppProj a :=
    (ceill_basic_1 a).1.1.isSelfAdjoint.star_eq
  have hra : star (rangeProj a) = rangeProj a :=
    (ceill_basic_2 a).1.1.isSelfAdjoint.star_eq
  have hst : star (suppProj t) = suppProj t :=
    (ceill_basic_1 t).1.1.isSelfAdjoint.star_eq
  have hrt : star (rangeProj t) = rangeProj t :=
    (ceill_basic_2 t).1.1.isSelfAdjoint.star_eq
  have s1 : star t * a = suppProj a := by
    have := congrArg star e4
    rwa [star_mul, ha.star_eq, hra, rangeProj_eq_suppProj_of_isSelfAdjoint ha] at this
  have s2 : star t * a = rangeProj (star t) := by
    have := congrArg star e3
    rw [star_mul, ha.star_eq, hst] at this
    rw [this, rangeProj_star]
  have s3 : a * star t = suppProj (star t) := by
    have := congrArg star e2
    rw [star_mul, ha.star_eq, hrt] at this
    rw [this, suppProj_star]
  have s4 : a * star t = rangeProj a := by
    have := congrArg star e1
    rwa [star_mul, ha.star_eq, hsa, ← rangeProj_eq_suppProj_of_isSelfAdjoint ha] at this
  exact (isPseudoinverse_unique a t (star t) ⟨e1, e2, e3, e4⟩ ⟨s1, s2, s3, s4⟩).symm

/-- Auxiliary: the pseudoinverse of a *positive* element is positive —
`a^{∼1} = (a^{∼1})* a a^{∼1}` by **79II**.(4). -/
theorem pinv_nonneg {a : A} (ha : 0 ≤ a) (h : Pseudoinvertible A a) :
    (0 : A) ≤ pinv a := by
  have hsa := pinv_isSelfAdjoint (IsSelfAdjoint.of_nonneg ha) h
  have h4 : pinv a * a * pinv a = pinv a ∧ suppProj a ≤ rangeProj (pinv a) ∧
      rangeProj a ≤ suppProj (pinv a) :=
    ((pseudoinverse_equivalents a (pinv a)).out 4 3).mp (pinv_spec h)
  have hrw : pinv a = star (pinv a) * a * pinv a := by
    rw [hsa.star_eq]; exact h4.1.symm
  rw [hrw]
  exact star_left_conjugate_nonneg ha _

/-- Auxiliary: whatever commutes with a positive `a` commutes with `⌈a⌉`:
`a b (1−⌈a⌉) = b a (1−⌈a⌉) = 0` gives `⌈a⌉ b = ⌈a⌉ b ⌈a⌉`, and the same for
`b*`, conjugated, gives `b ⌈a⌉ = ⌈a⌉ b ⌈a⌉`. -/
theorem commute_ceil_of_commute {a b : A} (ha : 0 ≤ a) (hab : b * a = a * b) :
    b * ceil a = ceil a * b := by
  have hproj : IsStarProjection (ceil a) := (ceil_spec ha).1
  have hac : a * ceil a = a := (ceil_spec ha).2.1
  set p := ceil a with hpdef
  have key : ∀ c : A, c * a = a * c → p * c = p * c * p := by
    intro c hc
    have e1 : a * (c * (1 - p)) = 0 := by
      calc a * (c * (1 - p)) = a * c * (1 - p) := by rw [mul_assoc]
        _ = c * (a * (1 - p)) := by rw [← hc, mul_assoc]
        _ = 0 := by rw [mul_sub, mul_one, hac, sub_self, mul_zero]
    have f1 := ceil_mul_eq_zero ha e1
    rw [mul_sub, mul_one, mul_sub, sub_eq_zero, ← mul_assoc] at f1
    exact f1
  have hstar : star b * a = a * star b := by
    have := congrArg star hab
    rw [star_mul, star_mul, (IsSelfAdjoint.of_nonneg ha).star_eq] at this
    exact this.symm
  have k1 := key b hab
  have k2 := key (star b) hstar
  have k2' : b * p = p * b * p := by
    have h := congrArg star k2
    simp only [star_mul, star_star, hproj.isSelfAdjoint.star_eq] at h
    rw [mul_assoc]
    exact h
  rw [k2', ← k1]

/-- **79VI** (`pseudoinverse-basic-2`, vn.tex:5203, Exercise), part 1, the
**three-way** equivalence: for positive `a` the following are the same.

> 1. `a` is pseudoinvertible;
> 2. `a` is invertible in the corner `⌈a⌉𝒜⌈a⌉`;
> 3. `at = ⌈a⌉` for some `t ∈ 𝒜₊`.

Moreover `at = ta` for such `t`.

The corner `⌈a⌉𝒜⌈a⌉` is not built as a type (cf. **67IV**.1, where the
corner of a central projection is likewise handled as a set): membership is
`⌈a⌉t⌈a⌉ = t` and the unit of the corner is `⌈a⌉`, so invertibility of `a`
there is `at = ⌈a⌉ = ta` for some `t` in the corner — which is what clause 2
says below. -/
theorem pseudoinverse_basic_2'_1 (a : A) (ha : 0 ≤ a) :
    (Pseudoinvertible A a ↔
        ∃ t : A, ceil a * t * ceil a = t ∧ a * t = ceil a ∧ t * a = ceil a) ∧
      (Pseudoinvertible A a ↔ ∃ t : A, 0 ≤ t ∧ a * t = ceil a) ∧
      ∀ t : A, 0 ≤ t → a * t = ceil a → a * t = t * a := by
  have hasa : IsSelfAdjoint a := .of_nonneg ha
  have hproj : IsStarProjection (ceil a) := (ceil_spec ha).1
  have hsupp : suppProj a = ceil a := suppProj_of_nonneg ha
  have hrange : rangeProj a = ceil a := by
    rw [rangeProj_eq_suppProj_of_isSelfAdjoint hasa, hsupp]
  have hac : a * ceil a = a := (ceil_spec ha).2.1
  have hca : ceil a * a = a := by
    have := congrArg star hac
    rwa [star_mul, hproj.isSelfAdjoint.star_eq, hasa.star_eq] at this
  set p := ceil a with hpdef
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · -- (1) ⟹ (2): the pseudoinverse `a^{∼1}` already lies in the corner,
    -- because `⌈a⌉ = ta` and `⌈a⌉ = at` give `pt = tat = t = tp`
    intro h
    set t := pinv a with htdef
    have hspec := pinv_spec h
    have hta : t * a = p := by rw [hspec.1, hsupp]
    have hat : a * t = p := by rw [hspec.2.2.2, hrange]
    have h4 := ((pseudoinverse_equivalents a t).out 4 3).mp hspec
    have htat : t * a * t = t := h4.1
    refine ⟨t, ?_, hat, hta⟩
    have hpt : p * t = t := by rw [← hta]; exact htat
    have htp : t * p = t := by rw [← hat, ← mul_assoc]; exact htat
    rw [hpt, htp]
  · -- (2) ⟹ (1): a corner inverse is a pseudoinverse, by **79II**.2 ⇒ .5
    rintro ⟨t, htcorner, hat, hta⟩
    have hcond : a * t * a = a ∧ suppProj t ≤ rangeProj a ∧
        rangeProj t ≤ suppProj a := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hat, hca]
      · calc suppProj t = suppProj (p * t * p) := by rw [htcorner]
          _ ≤ suppProj p := suppProj_mul_le (p * t) p
          _ = p := suppProj_of_isStarProjection hproj
          _ = rangeProj a := hrange.symm
      · calc rangeProj t = rangeProj (p * (t * p)) := by
              rw [show p * (t * p) = p * t * p by noncomm_ring, htcorner]
          _ ≤ rangeProj p := rangeProj_mul_le p (t * p)
          _ = p := rangeProj_of_isStarProjection hproj
          _ = suppProj a := hsupp.symm
    exact ⟨t, ((pseudoinverse_equivalents a t).out 1 4).mp hcond⟩
  · -- (1) ⟹ (3): the pseudoinverse is positive
    intro h
    refine ⟨pinv a, pinv_nonneg ha h, ?_⟩
    rw [(pinv_spec h).2.2.2, hrange]
  · -- (3) ⟹ (1): cut `t` down to the corner `⌈a⌉A⌈a⌉`
    rintro ⟨t, -, hat⟩
    have hcond : a * (p * t * p) * a = a ∧
        suppProj (p * t * p) ≤ rangeProj a ∧
        rangeProj (p * t * p) ≤ suppProj a := by
     refine ⟨?_, ?_, ?_⟩
     · calc a * (p * t * p) * a = (a * p) * t * (p * a) := by noncomm_ring
        _ = a * t * a := by rw [hac, hca]
        _ = a := by rw [hat, hca]
     · calc suppProj (p * t * p) ≤ suppProj p := suppProj_mul_le (p * t) p
        _ = p := suppProj_of_isStarProjection hproj
        _ = rangeProj a := hrange.symm
     · have hassoc : p * t * p = p * (t * p) := by noncomm_ring
       calc rangeProj (p * t * p) = rangeProj (p * (t * p)) := by rw [hassoc]
        _ ≤ rangeProj p := rangeProj_mul_le p (t * p)
        _ = p := rangeProj_of_isStarProjection hproj
        _ = suppProj a := hsupp.symm
    exact ⟨p * t * p, ((pseudoinverse_equivalents a (p * t * p)).out 1 4).mp hcond⟩
  · -- such `t` commutes with `a`
    intro t ht hat
    have := congrArg star hat
    rw [star_mul, hasa.star_eq, (IsSelfAdjoint.of_nonneg ht).star_eq,
      hproj.isSelfAdjoint.star_eq] at this
    rw [hat, this]


/-- **79VI** (`pseudoinverse-basic-2`, vn.tex:5203, Exercise), part 2: a
positive `a` is pseudoinvertible iff `λ⌈a⌉ ≤ a` for some `λ > 0`. -/
theorem pseudoinverse_basic_2'_2 (a : A) (ha : 0 ≤ a) :
    Pseudoinvertible A a ↔ ∃ l : ℝ, 0 < l ∧ (l : ℂ) • ceil a ≤ a := by
  have hasa : IsSelfAdjoint a := .of_nonneg ha
  have hproj : IsStarProjection (ceil a) := (ceil_spec ha).1
  have hsupp : suppProj a = ceil a := suppProj_of_nonneg ha
  have hrange : rangeProj a = ceil a := by
    rw [rangeProj_eq_suppProj_of_isSelfAdjoint hasa, hsupp]
  have hac : a * ceil a = a := (ceil_spec ha).2.1
  have hca : ceil a * a = a := by
    have := congrArg star hac
    rwa [star_mul, hproj.isSelfAdjoint.star_eq, hasa.star_eq] at this
  set p := ceil a with hpdef
  constructor
  · -- `⟹`
    intro h
    set t := pinv a with htdef
    have hspec := pinv_spec h
    have hta : t * a = p := by rw [hspec.1, hsupp]
    have hat : a * t = p := by rw [hspec.2.2.2, hrange]
    have hsa := pinv_isSelfAdjoint hasa h
    have h4 := ((pseudoinverse_equivalents a t).out 4 3).mp hspec
    have htat : t * a * t = t := h4.1
    have htnn : (0 : A) ≤ t := by
      have : t = star t * a * t := by rw [hsa.star_eq]; exact htat.symm
      rw [this]; exact star_left_conjugate_nonneg ha _
    have hpt : p * t = t := by rw [← hta, mul_assoc, ← mul_assoc]; exact htat
    have htp : t * p = t := by rw [← hat, ← mul_assoc]; exact htat
    -- `t ≤ ‖t‖ p`
    have hnorm : t ≤ ‖t‖ • p := by
      have h1 : t ≤ algebraMap ℝ A ‖t‖ := hsa.le_algebraMap_norm_self
      have h2 : p * t * p ≤ p * algebraMap ℝ A ‖t‖ * p :=
        hproj.isSelfAdjoint.conjugate_le_conjugate h1
      have h3 : p * t * p = t := by rw [hpt, htp]
      have h4' : p * algebraMap ℝ A ‖t‖ * p = ‖t‖ • p := by
        rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
          hproj.isIdempotentElem.eq]
      rwa [h3, h4'] at h2
    -- transport along `√a`
    set s : A := CFC.sqrt a with hsdef
    have hss : s * s = a := CFC.sqrt_mul_sqrt_self a ha
    have hsnn : (0 : A) ≤ s := CFC.sqrt_nonneg a
    have hcomm_at : Commute a t := by
      have h : a * t = t * a := by rw [hat, hta]
      exact h
    have hcomm_ap : Commute a p := by
      have h : a * p = p * a := by rw [hac, hca]
      exact h
    have hst : Commute s t := by
      rw [hsdef, CFC.sqrt_eq_cfc]; exact hcomm_at.cfc_nnreal _
    have hsp : Commute s p := by
      rw [hsdef, CFC.sqrt_eq_cfc]; exact hcomm_ap.cfc_nnreal _
    have hkey : p = s * t * s := by
      calc p = a * t := hat.symm
        _ = s * s * t := by rw [hss]
        _ = s * (s * t) := by rw [mul_assoc]
        _ = s * (t * s) := by rw [hst.eq]
        _ = s * t * s := by rw [mul_assoc]
    have hspa : s * p * s = a := by
      rw [hsp.eq, mul_assoc, hss, hca]
    have hple : p ≤ ‖t‖ • a := by
      have := hsnn.isSelfAdjoint.conjugate_le_conjugate hnorm
      rw [← hkey] at this
      have hr : s * (‖t‖ • p) * s = ‖t‖ • a := by
        rw [mul_smul_comm, smul_mul_assoc, hspa]
      rwa [hr] at this
    rcases eq_or_lt_of_le (norm_nonneg t) with h0 | h0
    · refine ⟨1, one_pos, ?_⟩
      have ht0 : t = 0 := by
        have := norm_eq_zero.mp h0.symm; exact this
      have hp0 : p = 0 := by rw [← hat, ht0, mul_zero]
      rw [hp0, smul_zero]; exact ha
    · refine ⟨‖t‖⁻¹, inv_pos.mpr h0, ?_⟩
      rw [Complex.coe_smul]
      have hsub : (0 : A) ≤ ‖t‖⁻¹ • (‖t‖ • a - p) :=
        smul_nonneg (inv_nonneg.mpr h0.le) (sub_nonneg.mpr hple)
      have hcalc : ‖t‖⁻¹ • (‖t‖ • a - p) = a - ‖t‖⁻¹ • p := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ h0.ne', one_smul]
      rw [hcalc] at hsub
      exact sub_nonneg.mp hsub
  · -- `⟸`
    rintro ⟨l, hl, hle⟩
    set b : A := a + (l : ℂ) • (1 - p) with hbdef
    have hpnn : (0 : A) ≤ p := hproj.nonneg
    have hlone : (l : ℂ) • (1 : A) ≤ b := by
      have : b - (l : ℂ) • (1 : A) = a - (l : ℂ) • p := by
        rw [hbdef, smul_sub]; abel
      rw [← sub_nonneg, this, sub_nonneg]; exact hle
    have hbsa : IsSelfAdjoint b := by
      have h1 : IsSelfAdjoint ((l : ℂ) • (1 - p : A)) := by
        rw [IsSelfAdjoint, star_smul, star_sub, star_one,
          hproj.isSelfAdjoint.star_eq, Complex.star_def, Complex.conj_ofReal]
      exact hasa.add h1
    have hbnn : (0 : A) ≤ b := by
      refine le_trans ?_ hlone
      rw [Complex.coe_smul]
      exact smul_nonneg hl.le zero_le_one
    have hamap : algebraMap ℝ A l ≤ b := by
      rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]; exact hlone
    have hspec : ∀ x ∈ spectrum ℝ b, l ≤ x :=
      (algebraMap_le_iff_le_spectrum hbsa).mp hamap
    have hunit : IsUnit b := by
      refine spectrum.isUnit_of_zero_notMem (R := ℝ) fun hmem => ?_
      exact absurd (hspec 0 hmem) (by linarith)
    set c : A := Ring.inverse b with hcdef
    have hcb : c * b = 1 := Ring.inverse_mul_cancel b hunit
    have hbc : b * c = 1 := Ring.mul_inverse_cancel b hunit
    have hbp : b * p = a := by
      rw [hbdef, add_mul, smul_mul_assoc, sub_mul, one_mul,
        hproj.isIdempotentElem.eq, sub_self, smul_zero, add_zero, hac]
    have hpb : p * b = a := by
      rw [hbdef, mul_add, mul_smul_comm, mul_sub, mul_one,
        hproj.isIdempotentElem.eq, sub_self, smul_zero, add_zero, hca]
    have hcp : c * p = p * c := by
      calc c * p = c * p * (b * c) := by rw [hbc, mul_one]
        _ = c * (p * b) * c := by noncomm_ring
        _ = c * (b * p) * c := by rw [hpb, hbp]
        _ = (c * b) * p * c := by noncomm_ring
        _ = p * c := by rw [hcb, one_mul]
    have hcsa : star c = c := by
      have h1 : b * star c = 1 := by
        have := congrArg star hcb
        rwa [star_mul, star_one, hbsa.star_eq] at this
      exact (left_inv_eq_right_inv hcb h1).symm
    have hcnn : (0 : A) ≤ c := by
      have : c = star c * b * c := by
        rw [hcsa, mul_assoc, hbc, mul_one]
      rw [this]; exact star_left_conjugate_nonneg hbnn _
    refine (pseudoinverse_basic_2'_1 a ha).2.1.mpr ⟨c * p, ?_, ?_⟩
    · have : c * p = p * c * p := by rw [← hcp, mul_assoc, hproj.isIdempotentElem.eq]
      rw [this]
      exact hproj.isSelfAdjoint.conjugate_nonneg hcnn
    · calc a * (c * p) = (b * p) * (c * p) := by rw [hbp]
        _ = b * (p * c) * p := by noncomm_ring
        _ = b * (c * p) * p := by rw [hcp]
        _ = (b * c) * (p * p) := by noncomm_ring
        _ = p := by rw [hbc, one_mul, hproj.isIdempotentElem.eq]


/-- **79VI** (`pseudoinverse-basic-2`, vn.tex:5203, Exercise), part 3: for
pseudoinvertible positive `a`: `⌈a^{∼1}⌉ = ⌈a⌉`, and whatever commutes
with `a` commutes with `a^{∼1}` (i.e. `a^{∼1} ∈ {a}^□□`). -/
theorem pseudoinverse_basic_2'_3 (a : A) (ha : 0 ≤ a)
    (hp : Pseudoinvertible A a) :
    ceil (pinv a) = ceil a ∧
      ∀ b : A, b * a = a * b → b * pinv a = pinv a * b := by
  have hasa : IsSelfAdjoint a := .of_nonneg ha
  have hrange : rangeProj a = ceil a := by
    rw [rangeProj_eq_suppProj_of_isSelfAdjoint hasa, suppProj_of_nonneg ha]
  set t := pinv a with htdef
  have hspec := pinv_spec hp
  have htnn : (0 : A) ≤ t := pinv_nonneg ha hp
  have hceq : ceil t = ceil a := by
    have h1 : suppProj t = ceil a := by
      rw [← hspec.2.2.1, hspec.2.2.2, hrange]
    rw [← suppProj_of_nonneg htnn, h1]
  refine ⟨hceq, fun b hb => ?_⟩
  have hat : a * t = ceil a := by rw [hspec.2.2.2, hrange]
  have h43 : t * a * t = t ∧ suppProj a ≤ rangeProj t ∧ rangeProj a ≤ suppProj t :=
    ((pseudoinverse_equivalents a t).out 4 3).mp hspec
  have htat : t * a * t = t := h43.1
  have htp : t * ceil a = t := by rw [← hat, ← mul_assoc]; exact htat
  have hbp : b * ceil a = ceil a * b := commute_ceil_of_commute ha hb
  refine mult_cancellation_2 a (b * t) (t * b) ?_ ?_ ?_
  · refine le_trans ((ceill_basic_1 (b * t)).2 ⟨(ceil_spec ha).1, ?_⟩) (le_of_eq hrange.symm)
    rw [mul_assoc, htp]
  · refine le_trans ((ceill_basic_1 (t * b)).2 ⟨(ceil_spec ha).1, ?_⟩) (le_of_eq hrange.symm)
    rw [mul_assoc, hbp, ← mul_assoc, htp]
  · calc b * t * a = b * (t * a) := by rw [mul_assoc]
      _ = b * ceil a := by rw [hspec.1, suppProj_of_nonneg ha]
      _ = ceil a * b := hbp
      _ = t * a * b := by rw [hspec.1, suppProj_of_nonneg ha]
      _ = t * b * a := by rw [mul_assoc, ← hb, ← mul_assoc]


/-- Auxiliary: a projection is its own pseudoinverse. -/
theorem isPseudoinverse_self_of_isStarProjection {p : A} (hp : IsStarProjection p) :
    IsPseudoinverse A p p := by
  have h1 : suppProj p = p := suppProj_of_isStarProjection hp
  have h2 : rangeProj p = p := rangeProj_of_isStarProjection hp
  exact ⟨by rw [hp.isIdempotentElem.eq, h1], by rw [hp.isIdempotentElem.eq, h2],
    by rw [hp.isIdempotentElem.eq, h1], by rw [hp.isIdempotentElem.eq, h2]⟩

/-- Auxiliary: a projection is pseudoinvertible. -/
theorem pseudoinvertible_of_isStarProjection {p : A} (hp : IsStarProjection p) :
    Pseudoinvertible A p :=
  ⟨p, isPseudoinverse_self_of_isStarProjection hp⟩

/-- Auxiliary: `p^{∼1} = p` for a projection `p`. -/
theorem pinv_of_isStarProjection {p : A} (hp : IsStarProjection p) : pinv p = p :=
  isPseudoinverse_unique p _ _ (pinv_spec (pseudoinvertible_of_isStarProjection hp))
    (isPseudoinverse_self_of_isStarProjection hp)

/-- The **printed** conclusion of **79VI**.4 applied to `b = p` (a projection)
and `c = 1` would force `p = 1`: both are positive, commuting and
pseudoinvertible with `p ≤ 1`, and `p^{∼1} = p`, `1^{∼1} = 1`.  (The
*corrected* conclusion — see `pseudoinverse_basic_2'_4` below — reads
`⌈b⌉c^{∼1}⌈b⌉ ≤ b^{∼1}`, which here is the true `p·1·p = p ≤ p`.) -/
theorem pseudoinverse_basic_2'_4_forces_eq_one {p : A} (hp : IsStarProjection p)
    (h : pinv (1 : A) ≤ pinv p) : p = 1 := by
  rw [pinv_of_isStarProjection hp, pinv_of_isStarProjection (IsStarProjection.one _)] at h
  exact le_antisymm hp.le_one h

/-- A nontrivial projection in `ℓ^∞({0,1}) = ℂ ⊕ ℂ`: the witness for
`pseudoinverse_basic_2'_4_is_false`. -/
noncomputable def pbFourWitness : lp (fun _ : Fin 2 => ℂ) ∞ :=
  ⟨fun i => if i = 0 then 1 else 0, (Set.finite_range _).bddAbove⟩

theorem pbFourWitness_apply (i : Fin 2) :
    (pbFourWitness : ∀ _ : Fin 2, ℂ) i = if i = 0 then 1 else 0 := rfl

theorem pbFourWitness_isStarProjection : IsStarProjection pbFourWitness := by
  constructor
  · show pbFourWitness * pbFourWitness = pbFourWitness
    refine lp.ext ?_
    funext i
    rw [lp.infty_coeFn_mul]
    fin_cases i <;> simp [pbFourWitness_apply]
  · show star pbFourWitness = pbFourWitness
    refine lp.ext ?_
    funext i
    rw [lp.coeFn_star]
    fin_cases i <;> simp [pbFourWitness_apply]

theorem pbFourWitness_ne_one :
    pbFourWitness ≠ (1 : lp (fun _ : Fin 2 => ℂ) ∞) := by
  intro h
  have hco := congrArg
    (fun x : lp (fun _ : Fin 2 => ℂ) ∞ => (x : ∀ _ : Fin 2, ℂ) 1) h
  simp only [pbFourWitness_apply, lp.infty_coeFn_one, Pi.one_apply] at hco
  exact absurd hco (by norm_num)

/-- The **printed** conclusion of **79VI**.4 (vn.tex:5222), `c^{∼1} ≤ b^{∼1}`,
is **false** — erratum `parsec-790.60`.  Take `b = (1,0)` and `c = (1,1)` in
`ℓ^∞({0,1})`: both are positive, commuting and pseudoinvertible (projections
are their own pseudoinverses) with `b ≤ c`, `b^{∼1} = b` and `c^{∼1} = c`, and
`c ≰ b`.  The pseudoinverse *grows* where the carrier of `c` exceeds that of
`b`.

This lemma is kept as the record of what the printed statement claimed; the
author's repair (2026-08-17) **compresses the conclusion** to
`⌈b⌉c^{∼1}⌈b⌉ ≤ b^{∼1}`, which is `pseudoinverse_basic_2'_4` below and is
proved there.  In particular the printed parenthetical about dropping the
commutation hypothesis is *correct* for the repaired statement. -/
theorem pseudoinverse_basic_2'_4_is_false :
    ¬ ∀ b c : lp (fun _ : Fin 2 => ℂ) ∞, 0 ≤ b → Pseudoinvertible _ b →
      Pseudoinvertible _ c → b ≤ c → b * c = c * b → pinv c ≤ pinv b := by
  intro h
  exact pbFourWitness_ne_one (pseudoinverse_basic_2'_4_forces_eq_one
    pbFourWitness_isStarProjection
    (h pbFourWitness 1 pbFourWitness_isStarProjection.nonneg
      (pseudoinvertible_of_isStarProjection pbFourWitness_isStarProjection)
      (pseudoinvertible_of_isStarProjection (IsStarProjection.one _))
      pbFourWitness_isStarProjection.le_one (by rw [mul_one, one_mul])))

omit [VonNeumannAlgebra A] in
/-- Auxiliary: the positive square root of a positive element, packaged with
the two properties the estimates below need — it squares to `a`, and it
commutes with everything `a` commutes with. -/
private theorem exists_sqrt_commuting {a : A} (ha : 0 ≤ a) :
    ∃ x : A, 0 ≤ x ∧ x * x = a ∧ ∀ y : A, Commute a y → Commute x y :=
  ⟨CFC.sqrt a, CFC.sqrt_nonneg a, CFC.sqrt_mul_sqrt_self a ha, fun y hy => by
    rw [CFC.sqrt_eq_cfc]
    exact hy.cfc_nnreal _⟩

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
/-- Auxiliary: a projection `q` that absorbs `x²` on both sides absorbs the
self-adjoint `x` itself, since `(xq − x)*(xq − x) = qx²q − qx² − x²q + x² = 0`. -/
private theorem isStarProjection_absorb {q x : A} (hq : IsStarProjection q)
    (hx : IsSelfAdjoint x) (h : q * (x * x) = x * x) (h' : x * x * q = x * x) :
    x * q = x ∧ q * x = x := by
  have hz : star (x * q - x) * (x * q - x) = 0 := by
    have hs : star (x * q - x) = q * x - x := by
      rw [star_sub, star_mul, hq.isSelfAdjoint.star_eq, hx.star_eq]
    rw [hs]
    calc (q * x - x) * (x * q - x)
        = q * (x * x) * q - q * (x * x) - x * x * q + x * x := by noncomm_ring
      _ = 0 := by rw [h, h']; abel
  have h1 : x * q = x := by
    have hd := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
    rwa [sub_eq_zero] at hd
  refine ⟨h1, ?_⟩
  have hs := congrArg star h1
  rwa [star_mul, hq.isSelfAdjoint.star_eq, hx.star_eq] at hs

-- `hcomm` is deliberately unused: see the doc comment.
set_option linter.unusedVariables false in
/-- **79VI** (`pseudoinverse-basic-2`, vn.tex:5203, Exercise), part 4:
`⌈b⌉c^{∼1}⌈b⌉ ≤ b^{∼1}` for pseudoinvertible positive `b ≤ c`.

**Corrected statement**, erratum `parsec-790.60` (author's ruling of
2026-08-17).  The *printed* conclusion `c^{∼1} ≤ b^{∼1}` is false — see
`pseudoinverse_basic_2'_4_is_false` just above — and the repair **compresses
the conclusion** rather than strengthening the hypotheses.  The printed
parenthetical therefore stands: `hcomm` is used **nowhere** in the proof, and
is kept only to match the printed statement.

The argument is the standard C*-one.  Writing `b^{½}`, `b^{∼½} = (b^{∼1})^{½}`,
`c^{∼½} = (c^{∼1})^{½}` and `p = ⌈b⌉`: from `b ≤ c`,
`‖c^{∼½}b^{½}‖² = ‖c^{∼½}bc^{∼½}‖ ≤ ‖c^{∼½}cc^{∼½}‖ = ‖⌈c⌉‖ ≤ 1`, so
`b^{½}c^{∼1}b^{½} = (c^{∼½}b^{½})*(c^{∼½}b^{½})` is positive of norm `≤ 1`,
hence `≤ 1`, hence `≤ p` after compressing by `p` (which it absorbs).
Conjugating by `b^{∼½}` — using `b^{∼½}b^{½} = p` and `b^{∼½}b^{∼½} = b^{∼1}`,
both from **79VI**.1 — gives the claim. -/
theorem pseudoinverse_basic_2'_4 (b c : A) (hb : 0 ≤ b)
    (hbp : Pseudoinvertible A b) (hcp : Pseudoinvertible A c) (hbc : b ≤ c)
    (hcomm : b * c = c * b) : ceil b * pinv c * ceil b ≤ pinv b := by
  have hc : (0 : A) ≤ c := hb.trans hbc
  have hbsa : IsSelfAdjoint b := .of_nonneg hb
  have hcsa : IsSelfAdjoint c := .of_nonneg hc
  have hpbnn : (0 : A) ≤ pinv b := pinv_nonneg hb hbp
  have hpcnn : (0 : A) ≤ pinv c := pinv_nonneg hc hcp
  have hpproj : IsStarProjection (ceil b) := (ceil_spec hb).1
  have hqproj : IsStarProjection (ceil c) := (ceil_spec hc).1
  -- the defining products of the two pseudoinverses
  have e_pbb : pinv b * b = ceil b := by
    rw [(pinv_spec hbp).1, suppProj_of_nonneg hb]
  have e_bpb : b * pinv b = ceil b := by
    rw [(pinv_spec hbp).2.2.2, rangeProj_eq_suppProj_of_isSelfAdjoint hbsa,
      suppProj_of_nonneg hb]
  have e_pcc : pinv c * c = ceil c := by
    rw [(pinv_spec hcp).1, suppProj_of_nonneg hc]
  have e_cpc : c * pinv c = ceil c := by
    rw [(pinv_spec hcp).2.2.2, rangeProj_eq_suppProj_of_isSelfAdjoint hcsa,
      suppProj_of_nonneg hc]
  have hcomm_b : Commute b (pinv b) := show b * pinv b = pinv b * b by
    rw [e_bpb, e_pbb]
  have hcomm_c : Commute c (pinv c) := show c * pinv c = pinv c * c by
    rw [e_cpc, e_pcc]
  -- the three square roots
  obtain ⟨bh, hbh0, hbh2, hbhC⟩ := exists_sqrt_commuting hb
  obtain ⟨bph, hbph0, hbph2, hbphC⟩ := exists_sqrt_commuting hpbnn
  obtain ⟨cph, hcph0, hcph2, hcphC⟩ := exists_sqrt_commuting hpcnn
  have hbhsa : IsSelfAdjoint bh := .of_nonneg hbh0
  have hbphsa : IsSelfAdjoint bph := .of_nonneg hbph0
  have hcphsa : IsSelfAdjoint cph := .of_nonneg hcph0
  -- `c^{∼½} c c^{∼½} = ⌈c⌉`
  have hcphc : Commute cph c := hcphC c hcomm_c.symm
  have hconj_c : cph * c * cph = ceil c := by
    rw [mul_assoc, ← hcphc.eq, ← mul_assoc, hcph2, e_pcc]
  -- `b^{½}c^{∼1}b^{½} = x*x` and `c^{∼½}bc^{∼½} = xx*` for `x = c^{∼½}b^{½}`
  have hx : cph * bh * star (cph * bh) = cph * b * cph := by
    rw [star_mul, hbhsa.star_eq, hcphsa.star_eq]
    calc cph * bh * (bh * cph) = cph * (bh * bh) * cph := by noncomm_ring
      _ = cph * b * cph := by rw [hbh2]
  have hx' : star (cph * bh) * (cph * bh) = bh * pinv c * bh := by
    rw [star_mul, hbhsa.star_eq, hcphsa.star_eq]
    calc bh * cph * (cph * bh) = bh * (cph * cph) * bh := by noncomm_ring
      _ = bh * pinv c * bh := by rw [hcph2]
  have hle1 : cph * bh * star (cph * bh) ≤ 1 := by
    rw [hx]
    calc cph * b * cph ≤ cph * c * cph := hcphsa.conjugate_le_conjugate hbc
      _ = ceil c := hconj_c
      _ ≤ 1 := hqproj.le_one
  have hnorm : ‖star (cph * bh) * (cph * bh)‖ ≤ 1 := by
    rw [CStarRing.norm_star_mul_self, ← CStarRing.norm_self_mul_star]
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (mul_star_self_nonneg _)).mpr hle1
  have hy1 : bh * pinv c * bh ≤ 1 := by
    rw [← hx']
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg _)).mp hnorm
  -- `⌈b⌉` absorbs `b^{½}` and `b^{∼½}`
  have hbceil : b * ceil b = b := (ceil_spec hb).2.1
  have hbceil' : ceil b * b = b := by
    have hs := congrArg star hbceil
    rwa [star_mul, hpproj.isSelfAdjoint.star_eq, hbsa.star_eq] at hs
  obtain ⟨hbhp, hpbh⟩ := isStarProjection_absorb hpproj hbhsa
    (by rw [hbh2]; exact hbceil') (by rw [hbh2]; exact hbceil)
  have hceilpb : ceil (pinv b) = ceil b := (pseudoinverse_basic_2'_3 b hb hbp).1
  have hpbc : pinv b * ceil b = pinv b := by
    have hh := (ceil_spec hpbnn).2.1
    rwa [hceilpb] at hh
  have hpbc' : ceil b * pinv b = pinv b := by
    have hs := congrArg star hpbc
    rwa [star_mul, hpproj.isSelfAdjoint.star_eq,
      (IsSelfAdjoint.of_nonneg hpbnn).star_eq] at hs
  obtain ⟨hbphp, hpbph⟩ := isStarProjection_absorb hpproj hbphsa
    (by rw [hbph2]; exact hpbc') (by rw [hbph2]; exact hpbc)
  -- compress `b^{½}c^{∼1}b^{½} ≤ 1` by `⌈b⌉`
  have hconj_p : ceil b * (bh * pinv c * bh) * ceil b = bh * pinv c * bh := by
    calc ceil b * (bh * pinv c * bh) * ceil b
        = ceil b * bh * pinv c * (bh * ceil b) := by noncomm_ring
      _ = bh * pinv c * bh := by rw [hpbh, hbhp]
  have hy2 : bh * pinv c * bh ≤ ceil b := by
    have hh := hpproj.isSelfAdjoint.conjugate_le_conjugate hy1
    rwa [hconj_p, mul_one, hpproj.isIdempotentElem.eq] at hh
  -- `b^{∼½}b^{½} = ⌈b⌉`
  have hcomm_bh_pb : Commute bh (pinv b) := hbhC (pinv b) hcomm_b
  have hcomm_bph_bh : Commute bph bh := hbphC bh hcomm_bh_pb.symm
  have hz2 : bph * bh * (bph * bh) = ceil b := by
    calc bph * bh * (bph * bh) = bph * (bh * bph) * bh := by noncomm_ring
      _ = bph * (bph * bh) * bh := by rw [hcomm_bph_bh.eq]
      _ = bph * bph * (bh * bh) := by noncomm_ring
      _ = ceil b := by rw [hbph2, hbh2, e_pbb]
  have hz0 : (0 : A) ≤ bph * bh := by
    obtain ⟨u, hu0, hu2, huC⟩ := exists_sqrt_commuting hbph0
    have hub : Commute u bh := huC bh hcomm_bph_bh
    have hrw : bph * bh = star u * bh * u := by
      rw [(IsSelfAdjoint.of_nonneg hu0).star_eq]
      calc bph * bh = u * u * bh := by rw [hu2]
        _ = u * (u * bh) := by noncomm_ring
        _ = u * (bh * u) := by rw [hub.eq]
        _ = u * bh * u := by noncomm_ring
    rw [hrw]
    exact star_left_conjugate_nonneg hbh0 u
  have hzp : bph * bh = ceil b := by
    have h1 : CFC.sqrt (ceil b) = bph * bh := CFC.sqrt_unique hz2 hz0
    have h2 : CFC.sqrt (ceil b) = ceil b :=
      CFC.sqrt_unique hpproj.isIdempotentElem.eq hpproj.nonneg
    rw [← h1, h2]
  -- conjugate by `b^{∼½}`
  have hbphp' : bph * ceil b * bph = pinv b := by rw [hbphp, hbph2]
  have hlhs : bph * (bh * pinv c * bh) * bph = ceil b * pinv c * ceil b := by
    calc bph * (bh * pinv c * bh) * bph
        = bph * bh * pinv c * (bh * bph) := by noncomm_ring
      _ = ceil b * pinv c * ceil b := by rw [hzp, ← hcomm_bph_bh.eq, hzp]
  have hh := hbphsa.conjugate_le_conjugate hy2
  rwa [hlhs, hbphp'] at hh

/-! **79VI** (`pseudoinverse-basic-2`, vn.tex:5203, Exercise), part 5: the
element `(0, 0, 1, ½, ⅓, …)` of `ℓ^∞(ℕ)` is not pseudoinvertible.
**80I** (vn.tex:5239, Remark): its obvious pseudoinverse-candidate
`(0, 0, 1, 2, 3, …)` is unbounded, but can be approximated — motivating
the approximate pseudoinverses below. -/

/-- **79VI** (`pseudoinverse-basic-2`, vn.tex:5203, Exercise), part 5:
`(0, 0, 1, ½, ⅓, …)` is not pseudoinvertible in `ℓ^∞(ℕ)`. -/
theorem pseudoinverse_basic_2'_5 :
    ∃ x : lp (fun _ : ℕ => ℂ) ∞,
      (∀ n : ℕ, (x : ∀ _ : ℕ, ℂ) n =
        if n < 2 then 0 else ((n : ℂ) - 1)⁻¹) ∧
      ¬Pseudoinvertible (lp (fun _ : ℕ => ℂ) ∞) x := by
  classical
  set g : ∀ _ : ℕ, ℂ := fun n => if n < 2 then 0 else ((n : ℂ) - 1)⁻¹ with hg
  have hcast : ∀ n : ℕ, 2 ≤ n → ((n : ℂ) - 1) = (((n : ℝ) - 1 : ℝ) : ℂ) := by
    intro n _; push_cast; ring
  have hnorm : ∀ n : ℕ, 2 ≤ n → ‖(n : ℂ) - 1‖ = (n : ℝ) - 1 := by
    intro n hn
    have h1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [hcast n hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hgval : ∀ n : ℕ, g n = if n < 2 then (0 : ℂ) else ((n : ℂ) - 1)⁻¹ :=
    fun _ => rfl
  have hbd : ∀ n : ℕ, ‖g n‖ ≤ 1 := by
    intro n
    rw [hgval n]
    by_cases h : n < 2
    · simp [h]
    · push_neg at h
      rw [if_neg (Nat.not_lt.mpr h), norm_inv, hnorm n h]
      refine inv_le_one_of_one_le₀ ?_
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      linarith
  have hmem : Memℓp g ∞ := memℓp_infty ⟨1, by rintro _ ⟨n, rfl⟩; exact hbd n⟩
  refine ⟨⟨g, hmem⟩, fun n => rfl, ?_⟩
  rintro ⟨t, -, -, -, h4⟩
  set x : lp (fun _ : ℕ => ℂ) ∞ := ⟨g, hmem⟩ with hx
  -- `⌊x⌉x = x` (**59VI**.2), so `x t x = x` pointwise
  have hkey : x * t * x = x := by
    rw [h4]; exact (ceill_basic_2 x).1.2
  have hcoord : ∀ n : ℕ, g n * (t : ∀ _ : ℕ, ℂ) n * g n = g n := by
    intro n
    have h := congrArg (fun y : lp (fun _ : ℕ => ℂ) ∞ => (y : ∀ _ : ℕ, ℂ) n) hkey
    simpa only [lp.infty_coeFn_mul, Pi.mul_apply] using h
  -- for `n ≥ 2` this forces `tₙ = n − 1`, which is unbounded
  have hval : ∀ n : ℕ, 2 ≤ n → (t : ∀ _ : ℕ, ℂ) n = (n : ℂ) - 1 := by
    intro n hn
    have hgn : g n = ((n : ℂ) - 1)⁻¹ := by
      rw [hgval n, if_neg (Nat.not_lt.mpr hn)]
    have hne : ((n : ℂ) - 1) ≠ 0 := by
      intro h0
      have h1 := hnorm n hn
      rw [h0, norm_zero] at h1
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have h := hcoord n
    rw [hgn] at h
    field_simp at h
    exact h
  obtain ⟨N, hN⟩ := exists_nat_gt (‖t‖ + 2)
  have hN2 : 2 ≤ N := by
    have : (0 : ℝ) ≤ ‖t‖ := norm_nonneg _
    have h2 : (2 : ℝ) < (N : ℝ) := by linarith
    exact_mod_cast h2.le
  have hle : ‖(t : ∀ _ : ℕ, ℂ) N‖ ≤ ‖t‖ := lp.norm_apply_le_norm (by simp) t N
  rw [hval N hN2, hnorm N hN2] at hle
  linarith

/-! ## Parsec 800: approximate pseudoinverses -/

variable (A) in
/-- **80II** (`approximate-pseudoinverse-def`, vn.tex:5259, Definition): an
**approximate pseudoinverse** of `a` is a sequence `t₁, t₂, …` such that
all `tₙa` and `atₙ` are projections with `∑ₙ tₙa = ⌈a⌋ = ∑ₙ ⌊tₙ⌉` and
`∑ₙ atₙ = ⌊a⌉ = ∑ₙ ⌈tₙ⌋` (the sums rendered as suprema of the partial
sums, which are increasing since the summands are pairwise orthogonal
projections). -/
structure IsApproxPseudoinverse (a : A) (t : ℕ → A) : Prop where
  proj_left : ∀ n, IsStarProjection (t n * a)
  proj_right : ∀ n, IsStarProjection (a * t n)
  sum_left : IsLUB
    {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, t n * a} (suppProj a)
  sum_range : IsLUB
    {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, rangeProj (t n)}
    (suppProj a)
  sum_right : IsLUB
    {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, a * t n} (rangeProj a)
  sum_supp : IsLUB
    {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, suppProj (t n)}
    (rangeProj a)

omit [VonNeumannAlgebra A] in
/-- Auxiliary (the order-limit lemma behind **80III**): if `pₙ ≤ rₙ` and the
partial sums `∑_{n<N} pₙ` and `∑_{n<N} rₙ` have the *same* supremum, then
`pₙ = rₙ` for every `n`.  (Take `d = r_m - p_m ≥ 0`; for `N > m` one has
`∑_{n<N} pₙ + d ≤ ∑_{n<N} rₙ ≤ q`, so `q ≤ q - d`.) -/
theorem eq_of_le_of_isLUB_partialSums {p r : ℕ → A} (hp0 : ∀ n, 0 ≤ p n)
    (hle : ∀ n, p n ≤ r n) {q : A}
    (hpq : IsLUB {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, p n} q)
    (hrq : IsLUB {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, r n} q) (m : ℕ) :
    p m = r m := by
  classical
  have hd0 : 0 ≤ r m - p m := sub_nonneg.mpr (hle m)
  have key : ∀ N : ℕ, ∑ n ∈ Finset.range N, p n ≤ q - (r m - p m) := by
    intro N
    set M := max N (m + 1) with hM
    have hsubset : Finset.range N ⊆ Finset.range M :=
      fun i hi => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hi) (le_max_left N (m + 1)))
    have hsub : ∑ n ∈ Finset.range N, p n ≤ ∑ n ∈ Finset.range M, p n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset fun i _ _ => hp0 i
    have hmM : m ∈ Finset.range M :=
      Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_right _ _))
    have h1 : ∑ n ∈ Finset.range M, p n - p m ≤ ∑ n ∈ Finset.range M, r n - r m := by
      rw [← Finset.sum_erase_eq_sub (f := p) hmM, ← Finset.sum_erase_eq_sub (f := r) hmM]
      exact Finset.sum_le_sum fun i _ => hle i
    have h2 : ∑ n ∈ Finset.range M, p n + (r m - p m)
        ≤ ∑ n ∈ Finset.range M, r n := by
      calc ∑ n ∈ Finset.range M, p n + (r m - p m)
          = (∑ n ∈ Finset.range M, p n - p m) + r m := by abel
        _ ≤ (∑ n ∈ Finset.range M, r n - r m) + r m := by gcongr
        _ = ∑ n ∈ Finset.range M, r n := by abel
    have h3 : ∑ n ∈ Finset.range M, r n ≤ q := hrq.1 ⟨M, rfl⟩
    calc ∑ n ∈ Finset.range N, p n
        ≤ ∑ n ∈ Finset.range M, p n := hsub
      _ ≤ q - (r m - p m) := by rw [le_sub_iff_add_le]; exact h2.trans h3
  have hq : q ≤ q - (r m - p m) := hpq.2 (by rintro _ ⟨N, rfl⟩; exact key N)
  have hle0 : r m - p m ≤ 0 := by
    have := sub_le_sub_right hq q
    simpa using this
  exact (sub_eq_zero.mp (le_antisymm hle0 hd0)).symm

namespace IsApproxPseudoinverse

variable {a : A} {t : ℕ → A}

/-- **80III**, first structural fact: `tₙ a = ⌊tₙ⌉`.  The two sequences of
projections `tₙ a` and `⌊tₙ⌉` satisfy `tₙ a ≤ ⌊tₙ⌉` and have the same
supremum `⌈a⌋`, so they agree termwise. -/
theorem mul_eq_rangeProj (h : IsApproxPseudoinverse A a t) (n : ℕ) :
    t n * a = rangeProj (t n) :=
  eq_of_le_of_isLUB_partialSums (fun k => (h.proj_left k).nonneg)
    (fun k => by
      conv_lhs => rw [← rangeProj_of_isStarProjection (h.proj_left k)]
      exact rangeProj_mul_le _ _)
    h.sum_left h.sum_range n

/-- **80III**, dually: `a tₙ = ⌈tₙ⌋`. -/
theorem mul_eq_suppProj (h : IsApproxPseudoinverse A a t) (n : ℕ) :
    a * t n = suppProj (t n) :=
  eq_of_le_of_isLUB_partialSums (fun k => (h.proj_right k).nonneg)
    (fun k => by
      conv_lhs => rw [← suppProj_of_isStarProjection (h.proj_right k)]
      exact suppProj_mul_le _ _)
    h.sum_right h.sum_supp n

/-- **80III**: `tₙ a tₙ = tₙ`, i.e. `tₙ` is a generalised inverse of `a`. -/
theorem mul_mul_self (h : IsApproxPseudoinverse A a t) (n : ℕ) :
    t n * a * t n = t n := by
  rw [h.mul_eq_rangeProj n]
  exact (ceill_basic_2 (t n)).1.2

/-- **80III**: every member of an approximate pseudoinverse of a *positive*
element is self-adjoint.  With `w = tₙ*tₙ - tₙtₙ*` one has `tₙ - tₙ* = a w`
and `tₙ - tₙ* = -(w a)`, whence `a² w = w a²`; as `a = √(a²)` this gives
`a w = w a`, so `a w = 0` and `tₙ = tₙ*`. -/
theorem isSelfAdjoint_of_nonneg (h : IsApproxPseudoinverse A a t) (ha : 0 ≤ a)
    (n : ℕ) : IsSelfAdjoint (t n) := by
  set u : A := t n with hu
  have hasa : star a = a := (IsSelfAdjoint.of_nonneg ha).star_eq
  have h1 : a * star u = u * a := by
    have hx := (h.proj_left n).isSelfAdjoint.star_eq
    rwa [star_mul, hasa] at hx
  have h2 : star u * a = a * u := by
    have hx := (h.proj_right n).isSelfAdjoint.star_eq
    rwa [star_mul, hasa] at hx
  have hucu : u * a * u = u := h.mul_mul_self n
  have hucu' : star u * a * star u = star u := by
    have := congrArg star hucu
    rwa [star_mul, star_mul, hasa, ← mul_assoc] at this
  have e1 : a * (star u * u) = u := by rw [← mul_assoc, h1, hucu]
  have e2 : a * (u * star u) = star u := by rw [← mul_assoc, ← h2, hucu']
  have e3 : (u * star u) * a = u := by rw [mul_assoc, h2, ← mul_assoc, hucu]
  have e4 : (star u * u) * a = star u := by rw [mul_assoc, ← h1, ← mul_assoc, hucu']
  set w : A := star u * u - u * star u with hw
  have haw : a * w = u - star u := by rw [hw, mul_sub, e1, e2]
  have hwa : w * a = star u - u := by rw [hw, sub_mul, e4, e3]
  have hanti : a * w = -(w * a) := by rw [haw, hwa]; abel
  have hcomm2 : Commute (a * a) w := by
    change a * a * w = w * (a * a)
    calc a * a * w = a * (a * w) := by rw [mul_assoc]
      _ = a * -(w * a) := by rw [hanti]
      _ = -(a * w * a) := by rw [mul_neg, mul_assoc]
      _ = -(-(w * a) * a) := by rw [hanti]
      _ = w * (a * a) := by rw [neg_mul, neg_neg, mul_assoc]
  have hcomm : Commute a w := by
    have hsq : CFC.sqrt (a * a) = a := CFC.sqrt_mul_self a ha
    have := hcomm2.cfc_nnreal NNReal.sqrt
    rwa [← CFC.sqrt_eq_cfc, hsq] at this
  have hzero : a * w = 0 := by
    have hsum : a * w + a * w = 0 := by
      calc a * w + a * w = -(w * a) + w * a := by rw [← hanti, ← hcomm.eq]
        _ = 0 := by abel
    have h2s : (2 : ℂ) • (a * w) = 0 := by rw [two_smul]; exact hsum
    rcases smul_eq_zero.mp h2s with h' | h'
    · exact absurd h' (by norm_num)
    · exact h'
  have : u - star u = 0 := by rw [← haw, hzero]
  exact (sub_eq_zero.mp this).symm

/-- **80III**: for positive `a`, each `tₙ` commutes with `a`. -/
theorem commute_of_nonneg (h : IsApproxPseudoinverse A a t) (ha : 0 ≤ a)
    (n : ℕ) : a * t n = t n * a := by
  have hsa := h.isSelfAdjoint_of_nonneg ha n
  have h1 : a * star (t n) = t n * a := by
    have hx := (h.proj_left n).isSelfAdjoint.star_eq
    rwa [star_mul, (IsSelfAdjoint.of_nonneg ha).star_eq] at hx
  rwa [hsa.star_eq] at h1

end IsApproxPseudoinverse

/-- Auxiliary for **80III**: if `tₙ (b*b) tₙ = tₙ` and `b tₙ b*` is a
projection, then `⌊b tₙ⌉ = b tₙ b*`. -/
theorem apinv_rangeProj_mul {b c : A} {t : ℕ → A} (hc : c = star b * b)
    (htct : ∀ n, t n * c * t n = t n)
    (hfproj : ∀ n, IsStarProjection (b * (t n * star b))) (n : ℕ) :
    rangeProj (b * t n) = b * (t n * star b) := by
  refine (ceill_basic_2 (b * t n)).unique ⟨⟨hfproj n, ?_⟩, ?_⟩
  · calc b * (t n * star b) * (b * t n)
        = b * (t n * (star b * b) * t n) := by noncomm_ring
      _ = b * t n := by rw [← hc, htct n]
  · rintro p ⟨hp, hpm⟩
    have hpf : p * (b * (t n * star b)) = b * (t n * star b) := by
      calc p * (b * (t n * star b)) = (p * (b * t n)) * star b := by noncomm_ring
        _ = b * (t n * star b) := by rw [hpm]; noncomm_ring
    calc b * (t n * star b) = rangeProj (b * (t n * star b)) :=
          (rangeProj_of_isStarProjection (hfproj n)).symm
      _ ≤ p := (ceill_basic_2 _).2 ⟨hp, hpf⟩

/-- Auxiliary for **80III**: `⌊b (∑_{k<N} t_k c)⌉ = ∑_{k<N} b t_k b*`. -/
theorem apinv_rangeProj_mul_sum {b c : A} {t : ℕ → A} (hc : c = star b * b)
    (hprojE : ∀ n, IsStarProjection (t n * c))
    (horth : ∀ m n : ℕ, m ≠ n → (t m * c) * (t n * c) = 0)
    (het : ∀ n, (t n * c) * t n = t n)
    (hfproj : ∀ n, IsStarProjection (b * (t n * star b)))
    (hforth : ∀ m n : ℕ, m ≠ n →
      (b * (t m * star b)) * (b * (t n * star b)) = 0) (N : ℕ) :
    rangeProj (b * ∑ k ∈ Finset.range N, t k * c)
      = ∑ k ∈ Finset.range N, b * (t k * star b) := by
  classical
  have hEproj : IsStarProjection (∑ k ∈ Finset.range N, t k * c) :=
    isStarProjection_sum _ _ hprojE fun i _ j _ hij => horth i j hij
  have hFproj : IsStarProjection (∑ k ∈ Finset.range N, b * (t k * star b)) :=
    isStarProjection_sum _ _ hfproj fun i _ j _ hij => hforth i j hij
  -- `eₙ Eₙ = eₙ` and `Eₙ tₙ = tₙ` for `n < N`
  have hEe : ∀ n ∈ Finset.range N,
      (t n * c) * (∑ k ∈ Finset.range N, t k * c) = t n * c := by
    intro n hn
    rw [Finset.mul_sum, Finset.sum_eq_single n]
    · exact hprojE n |>.isIdempotentElem.eq
    · intro i _ hin; exact horth n i (Ne.symm hin)
    · intro hcon; exact absurd hn hcon
  have hEt : ∀ n ∈ Finset.range N,
      (∑ k ∈ Finset.range N, t k * c) * t n = t n := by
    intro n hn
    rw [Finset.sum_mul, Finset.sum_eq_single n]
    · exact het n
    · intro i _ hin
      calc t i * c * t n = (t i * c) * ((t n * c) * t n) := by rw [het n]
        _ = ((t i * c) * (t n * c)) * t n := by noncomm_ring
        _ = 0 := by rw [horth i n hin, zero_mul]
    · intro hcon; exact absurd hn hcon
  refine (ceill_basic_2 _).unique ⟨⟨hFproj, ?_⟩, ?_⟩
  · rw [Finset.sum_mul]
    calc ∑ i ∈ Finset.range N,
          b * (t i * star b) * (b * ∑ k ∈ Finset.range N, t k * c)
        = ∑ i ∈ Finset.range N, b * (t i * c) :=
          Finset.sum_congr rfl fun i hi => by
            calc b * (t i * star b) * (b * ∑ k ∈ Finset.range N, t k * c)
                = b * ((t i * (star b * b)) * ∑ k ∈ Finset.range N, t k * c) := by
                  noncomm_ring
              _ = b * ((t i * c) * ∑ k ∈ Finset.range N, t k * c) := by rw [← hc]
              _ = b * (t i * c) := by rw [hEe i hi]
      _ = b * ∑ k ∈ Finset.range N, t k * c := (Finset.mul_sum _ _ _).symm
  · rintro p ⟨hp, hpm⟩
    have hpf : p * (∑ k ∈ Finset.range N, b * (t k * star b))
        = ∑ k ∈ Finset.range N, b * (t k * star b) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hEti : (∑ k ∈ Finset.range N, t k * c) * t i = t i := hEt i hi
      calc p * (b * (t i * star b))
          = p * (b * (((∑ k ∈ Finset.range N, t k * c) * t i) * star b)) := by
            rw [hEti]
        _ = (p * (b * ∑ k ∈ Finset.range N, t k * c)) * (t i * star b) := by
            noncomm_ring
        _ = (b * ∑ k ∈ Finset.range N, t k * c) * (t i * star b) := by rw [hpm]
        _ = b * (((∑ k ∈ Finset.range N, t k * c) * t i) * star b) := by
            noncomm_ring
        _ = b * (t i * star b) := by rw [hEti]
    calc ∑ k ∈ Finset.range N, b * (t k * star b)
        = rangeProj (∑ k ∈ Finset.range N, b * (t k * star b)) :=
          (rangeProj_of_isStarProjection hFproj).symm
      _ ≤ p := (ceill_basic_2 _).2 ⟨hp, hpf⟩


/-- **80III** (`approximate-pseudoinverse-reduction`, vn.tex:5270,
Exercise): if `t₁, t₂, …` is an approximate pseudoinverse of `b*b`, then
`t₁b*, t₂b*, …` is one of `b`.

The exercise has no author argument.  Writing `c = b*b`, the four sums that
do not involve `b` on the left transfer by associativity once one knows
`tₙ c tₙ = tₙ` — which is *not* a field of the definition, but follows from
`eq_of_le_of_isLUB_partialSums` — and `tₙ = tₙ*`.  The remaining two sums
`∑ₙ b tₙ b* = ⌊b⌉ = ∑ₙ ⌈tₙb*⌋` are the substance: `∑_{k<N} b t_k b*` is the
range projection `⌊b(∑_{k<N} t_k c)⌉`, and **60IX**.2 in the form
`ceil_conj_projSup` turns `⋃_N ⌊b Eₙ⌉` into `⌈b ⌈b⌋ b*⌉ = ⌊b⌉`. -/
theorem approximate_pseudoinverse_reduction (b : A) (t : ℕ → A)
    (h : IsApproxPseudoinverse A (star b * b) t) :
    IsApproxPseudoinverse A b (fun n => t n * star b) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : A, c = star b * b := ⟨_, rfl⟩
  rw [← hc] at h
  have hcnn : (0 : A) ≤ c := hc ▸ star_mul_self_nonneg b
  have hcsa : star c = c := (IsSelfAdjoint.of_nonneg hcnn).star_eq
  have hsuppb : suppProj b = ceil c := by rw [hc]; rfl
  have hsupp : suppProj c = suppProj b := by
    change ceil (star c * c) = suppProj b
    rw [hcsa, ← sq, ceil_basic_5 c hcnn, hsuppb]
  -- the basic structure of an approximate pseudoinverse of a *positive* element
  have hprojE : ∀ n, IsStarProjection (t n * c) := h.proj_left
  have htct : ∀ n, t n * c * t n = t n := h.mul_mul_self
  have hstar : ∀ n, star (t n) = t n := fun n =>
    (h.isSelfAdjoint_of_nonneg hcnn n).star_eq
  have het : ∀ n, (t n * c) * t n = t n := htct
  -- pairwise orthogonality of the projections `tₙc`
  have hsupp_le_one : suppProj c ≤ 1 := (ceill_basic_1 c).1.1.le_one
  have horth : ∀ m n : ℕ, m ≠ n → (t m * c) * (t n * c) = 0 := by
    intro m n hmn
    refine ((orthogonal_tuple_of_projections_1 _ _ (hprojE m) (hprojE n)).out 3 0).mp ?_
    have hsubset : ({m, n} : Finset ℕ) ⊆ Finset.range (max m n + 1) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
    have h1 : t m * c + t n * c ≤ ∑ k ∈ Finset.range (max m n + 1), t k * c := by
      have hpair : ∑ k ∈ ({m, n} : Finset ℕ), t k * c = t m * c + t n * c :=
        Finset.sum_pair hmn
      rw [← hpair]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun i _ _ => (hprojE i).nonneg
    exact h1.trans ((h.sum_left.1 ⟨_, rfl⟩).trans hsupp_le_one)
  -- the projections `b tₙ b*`
  have hfsa : ∀ n, star (b * (t n * star b)) = b * (t n * star b) := by
    intro n
    rw [star_mul, star_mul, star_star, hstar n, mul_assoc]
  have hfproj : ∀ n, IsStarProjection (b * (t n * star b)) := by
    intro n
    refine ⟨?_, hfsa n⟩
    change b * (t n * star b) * (b * (t n * star b)) = b * (t n * star b)
    calc b * (t n * star b) * (b * (t n * star b))
        = b * (t n * (star b * b) * t n) * star b := by noncomm_ring
      _ = b * t n * star b := by rw [← hc, htct n]
      _ = b * (t n * star b) := by rw [mul_assoc]
  have hforth : ∀ m n : ℕ, m ≠ n →
      (b * (t m * star b)) * (b * (t n * star b)) = 0 := by
    intro m n hmn
    have h0 : t m * (star b * b) * t n = 0 := by
      rw [← hc]
      calc t m * c * t n = (t m * c) * ((t n * c) * t n) := by rw [het n]
        _ = ((t m * c) * (t n * c)) * t n := by noncomm_ring
        _ = 0 := by rw [horth m n hmn, zero_mul]
    calc b * (t m * star b) * (b * (t n * star b))
        = b * (t m * (star b * b) * t n) * star b := by noncomm_ring
      _ = 0 := by rw [h0]; simp
  -- ranges and supports of `tₙ b*`
  have hrp : ∀ n, rangeProj (t n * star b) = rangeProj (t n) := by
    intro n
    refine le_antisymm (rangeProj_mul_le _ _) ?_
    have hsplit : t n = (t n * star b) * (b * t n) := by
      calc t n = t n * c * t n := (htct n).symm
        _ = (t n * star b) * (b * t n) := by rw [hc]; noncomm_ring
    calc rangeProj (t n) = rangeProj ((t n * star b) * (b * t n)) := by rw [← hsplit]
      _ ≤ rangeProj (t n * star b) := rangeProj_mul_le _ _
  have hsp : ∀ n, suppProj (t n * star b) = b * (t n * star b) := by
    intro n
    have hst : star (t n * star b) = b * t n := by
      rw [star_mul, star_star, hstar n]
    rw [← rangeProj_star (t n * star b), hst]
    exact apinv_rangeProj_mul hc htct hfproj n
  -- the supremum of the `b tₙ b*`
  have hEproj : ∀ N : ℕ, IsStarProjection (∑ k ∈ Finset.range N, t k * c) := fun N =>
    isStarProjection_sum _ _ hprojE fun i _ j _ hij => horth i j hij
  have hFproj : ∀ N : ℕ,
      IsStarProjection (∑ k ∈ Finset.range N, b * (t k * star b)) := fun N =>
    isStarProjection_sum _ _ hfproj fun i _ j _ hij => hforth i j hij
  have hPproj : ∀ p ∈ Set.range (fun N : ℕ => ∑ k ∈ Finset.range N, t k * c),
      IsStarProjection p := by rintro _ ⟨N, rfl⟩; exact hEproj N
  have hprojSupE :
      projSup (Set.range (fun N : ℕ => ∑ k ∈ Finset.range N, t k * c))
        = suppProj b := by
    refine projSup_eq hPproj (ceill_basic_1 b).1.1 ?_ ?_
    · rintro _ ⟨N, rfl⟩
      exact (h.sum_left.1 ⟨N, rfl⟩).trans (le_of_eq hsupp)
    · intro q _ hub
      rw [← hsupp]
      exact h.sum_left.2 (by rintro _ ⟨N, rfl⟩; exact hub _ ⟨N, rfl⟩)
  have hkey := ceil_conj_projSup (star b)
    (Set.range (fun N : ℕ => ∑ k ∈ Finset.range N, t k * c)) hPproj
  rw [star_star, hprojSupE, (ceill_basic_1 b).1.2] at hkey
  have himg : ∀ N : ℕ, ceil (b * (∑ k ∈ Finset.range N, t k * c) * star b)
      = ∑ k ∈ Finset.range N, b * (t k * star b) := by
    intro N
    have harg : (b * ∑ k ∈ Finset.range N, t k * c)
        * star (b * ∑ k ∈ Finset.range N, t k * c)
        = b * (∑ k ∈ Finset.range N, t k * c) * star b := by
      rw [star_mul, (hEproj N).isSelfAdjoint.star_eq]
      calc (b * ∑ k ∈ Finset.range N, t k * c)
            * ((∑ k ∈ Finset.range N, t k * c) * star b)
          = b * ((∑ k ∈ Finset.range N, t k * c)
              * (∑ k ∈ Finset.range N, t k * c)) * star b := by noncomm_ring
        _ = b * (∑ k ∈ Finset.range N, t k * c) * star b := by
            rw [(hEproj N).isIdempotentElem.eq]
    calc ceil (b * (∑ k ∈ Finset.range N, t k * c) * star b)
        = rangeProj (b * ∑ k ∈ Finset.range N, t k * c) := (congrArg ceil harg).symm
      _ = ∑ k ∈ Finset.range N, b * (t k * star b) :=
          apinv_rangeProj_mul_sum hc hprojE horth het hfproj hforth N
  have himgset : (fun p => ceil (b * p * star b)) ''
      Set.range (fun N : ℕ => ∑ k ∈ Finset.range N, t k * c)
      = Set.range (fun N : ℕ => ∑ k ∈ Finset.range N, b * (t k * star b)) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext himg)
  rw [himgset] at hkey
  have hFdir : DirectedOn (· ≤ ·)
      (Set.range (fun N : ℕ => ∑ k ∈ Finset.range N, b * (t k * star b))) := by
    rintro _ ⟨N, rfl⟩ _ ⟨M, rfl⟩
    refine ⟨_, ⟨max N M, rfl⟩, ?_, ?_⟩
    · exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hi) (le_max_left N M)))
        fun i _ _ => (hfproj i).nonneg
    · exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hi) (le_max_right N M)))
        fun i _ _ => (hfproj i).nonneg
  have hFlub := isLUB_projSup_of_directed
    (Set.range (fun N : ℕ => ∑ k ∈ Finset.range N, b * (t k * star b)))
    (by rintro _ ⟨N, rfl⟩; exact hFproj N) (Set.range_nonempty _) hFdir
  rw [← hkey] at hFlub
  have hFset : {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, b * (t n * star b)}
      = Set.range (fun N : ℕ => ∑ k ∈ Finset.range N, b * (t k * star b)) := by
    ext x; simp [eq_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    show IsStarProjection (t n * star b * b)
    rw [mul_assoc, ← hc]
    exact hprojE n
  · intro n
    show IsStarProjection (b * (t n * star b))
    exact hfproj n
  · show IsLUB {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, t n * star b * b}
      (suppProj b)
    have hset : {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, t n * star b * b}
        = {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, t n * c} := by
      simp only [mul_assoc, ← hc]
    rw [hset, ← hsupp]
    exact h.sum_left
  · show IsLUB {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, rangeProj (t n * star b)}
      (suppProj b)
    have hset : {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, rangeProj (t n * star b)}
        = {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, rangeProj (t n)} := by
      simp only [hrp]
    rw [hset, ← hsupp]
    exact h.sum_range
  · show IsLUB {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, b * (t n * star b)}
      (rangeProj b)
    rw [hFset]
    exact hFlub
  · show IsLUB {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, suppProj (t n * star b)}
      (rangeProj b)
    have hset : {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, suppProj (t n * star b)}
        = {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, b * (t n * star b)} := by
      simp only [hsp]
    rw [hset, hFset]
    exact hFlub

omit [VonNeumannAlgebra A] in
/-- Auxiliary for **80IV**: `(a - l)₊ = f(a)` for `f r = (r - l) ⊔ 0`. -/
theorem posPart_sub_algebraMap {a : A} (ha : 0 ≤ a) (l : ℝ) :
    posPart (a - algebraMap ℝ A l) = cfc (fun r : ℝ => (r - l) ⊔ 0) a := by
  have hsa : IsSelfAdjoint a := .of_nonneg ha
  have hx : a - algebraMap ℝ A l = cfc (fun r : ℝ => r - l) a := by
    rw [cfc_sub _ _ a, cfc_id' ℝ a, cfc_const l a]
  rw [CFC.posPart_def, cfcₙ_eq_cfc, hx]
  exact (cfc_comp (fun s : ℝ => s ⊔ 0) (fun r : ℝ => r - l) a hsa).symm

omit [VonNeumannAlgebra A] in
/-- Auxiliary for **80IV**: `(a - l)₊ ≤ a` for positive `a` and `0 ≤ l`. -/
theorem posPart_sub_le {a : A} (ha : 0 ≤ a) {l : ℝ} (hl : 0 ≤ l) :
    posPart (a - algebraMap ℝ A l) ≤ a := by
  rw [posPart_sub_algebraMap ha l]
  nth_rewrite 2 [← cfc_id' ℝ a]
  refine cfc_mono fun r hr => ?_
  have h0 : (0 : ℝ) ≤ r := spectrum_nonneg_of_nonneg ha hr
  simp only [sup_le_iff]
  exact ⟨by linarith, h0⟩

omit [VonNeumannAlgebra A] in
/-- Auxiliary for **80IV**: `(a - l)₊ ≤ (a - l')₊` for `l' ≤ l`. -/
theorem posPart_sub_mono {a : A} (ha : 0 ≤ a) {l l' : ℝ} (hll : l' ≤ l) :
    posPart (a - algebraMap ℝ A l) ≤ posPart (a - algebraMap ℝ A l') := by
  rw [posPart_sub_algebraMap ha l, posPart_sub_algebraMap ha l']
  exact cfc_mono fun r _ => by
    simp only [sup_le_iff, le_sup_right, and_true]
    exact le_sup_of_le_left (by linarith)

omit [VonNeumannAlgebra A] in
/-- Auxiliary for **80IV**: `‖a - (a - l)₊‖ ≤ l` for positive `a`, `0 ≤ l`. -/
theorem norm_sub_posPart_le {a : A} (ha : 0 ≤ a) {l : ℝ} (hl : 0 ≤ l) :
    ‖a - posPart (a - algebraMap ℝ A l)‖ ≤ l := by
  have hsa : IsSelfAdjoint a := .of_nonneg ha
  rw [posPart_sub_algebraMap ha l]
  nth_rewrite 1 [← cfc_id' ℝ a]
  rw [← cfc_sub (fun r : ℝ => r) (fun r : ℝ => (r - l) ⊔ 0) a]
  refine norm_cfc_le hl fun r hr => ?_
  have h0 : (0 : ℝ) ≤ r := spectrum_nonneg_of_nonneg ha hr
  rw [Real.norm_eq_abs, abs_le]
  rcases le_total l r with h | h
  · rw [sup_eq_left.mpr (by linarith)]; constructor <;> linarith
  · rw [sup_eq_right.mpr (by linarith)]; constructor <;> linarith

/-- **80IV** (`approximate-pseudoinverse`, vn.tex:5278, Theorem), the
positive case, which is the thesis's proof: with `qₙ = ⌈(a − 1/n)₊⌉` and
`eₙ = qₙ₊₁ − qₙ` one has `1/(n+1) eₙ ≤ a eₙ ≤ ‖a‖ eₙ`, hence
`⌈a eₙ⌉ = eₙ` and `a eₙ` pseudoinvertible by **79VI**.2; `tₙ = (a eₙ)^{∼1}`
satisfies `tₙa = a tₙ = ⌊tₙ⌉ = ⌈tₙ⌋ = eₙ`, and the partial sums `∑_{n<N} eₙ`
telescope to `q_N`, whose supremum is `⌈a⌉ = ⌈a⌋ = ⌊a⌉`. -/
theorem approximate_pseudoinverse_of_nonneg (a : A) (ha : 0 ≤ a) :
    ∃ t : ℕ → A, IsApproxPseudoinverse A a t := by
  classical
  have hasa : IsSelfAdjoint a := .of_nonneg ha
  have hsuppa : suppProj a = ceil a := suppProj_of_nonneg ha
  have hrangea : rangeProj a = ceil a := by
    rw [rangeProj_eq_suppProj_of_isSelfAdjoint hasa, hsuppa]
  have halg : ∀ (x : A) (r : ℝ), algebraMap ℝ A r * x = r • x := fun x r => by
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have halg' : ∀ (x : A) (r : ℝ), x * algebraMap ℝ A r = r • x := fun x r => by
    rw [← Algebra.commutes, halg]
  rcases eq_or_ne a 0 with rfl | hane
  · have hz : IsLUB {x : A | ∃ N : ℕ, x = ∑ _n ∈ Finset.range N, (0 : A)} (0 : A) := by
      have hset : {x : A | ∃ N : ℕ, x = ∑ _n ∈ Finset.range N, (0 : A)} = {(0 : A)} := by
        ext x; simp
      rw [hset]; exact isLUB_singleton
    have hz0 : suppProj (0 : A) = 0 := by rw [hsuppa, ceil_zero]
    have hr0 : rangeProj (0 : A) = 0 := by rw [hrangea, ceil_zero]
    refine ⟨fun _ => 0, fun n => by simp, fun n => by simp, ?_, ?_, ?_, ?_⟩
    · simp only [mul_zero, hz0]; exact hz
    · simp only [hr0, hz0]; exact hz
    · simp only [zero_mul, hr0]; exact hz
    · simp only [hz0, hr0]; exact hz
  -- `a ≠ 0`
  have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr hane
  obtain ⟨lam, hlam⟩ : ∃ lam : ℕ → ℝ, ∀ n, lam n = 1 / ((n : ℝ) + 1) :=
    ⟨_, fun _ => rfl⟩
  have hlampos : ∀ n, 0 < lam n := fun n => by
    rw [hlam n]; positivity
  obtain ⟨u, hu⟩ : ∃ u : ℕ → A, ∀ n, u n = posPart (a - algebraMap ℝ A (lam n)) :=
    ⟨_, fun _ => rfl⟩
  have hunn : ∀ n, (0 : A) ≤ u n := fun n => by rw [hu n]; exact CFC.posPart_nonneg _
  obtain ⟨Q, hQ0, hQs⟩ : ∃ Q : ℕ → A, Q 0 = 0 ∧ ∀ n, Q (n + 1) = ceil (u n) :=
    ⟨fun N => match N with | 0 => 0 | n + 1 => ceil (u n), rfl, fun _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → A, ∀ n, e n = Q (n + 1) - Q n := ⟨_, fun _ => rfl⟩
  -- the projections `Qₙ`
  have hQproj : ∀ N, IsStarProjection (Q N) := by
    intro N
    cases N with
    | zero => rw [hQ0]; exact IsStarProjection.zero A
    | succ n => rw [hQs n]; exact (ceil_spec (hunn n)).1
  have hQmono : ∀ N, Q N ≤ Q (N + 1) := by
    intro N
    cases N with
    | zero => rw [hQ0]; exact (hQproj 1).nonneg
    | succ n =>
        rw [hQs n, hQs (n + 1), hu n, hu (n + 1)]
        refine ceil_mono (CFC.posPart_nonneg _) (posPart_sub_mono ha ?_)
        rw [hlam n, hlam (n + 1)]
        exact one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
  have hQle : ∀ N, Q N ≤ ceil a := by
    intro N
    cases N with
    | zero => rw [hQ0]; exact (ceil_spec ha).1.nonneg
    | succ n =>
        rw [hQs n, hu n]
        exact ceil_mono (CFC.posPart_nonneg _) (posPart_sub_le ha (hlampos n).le)
  have heproj : ∀ n, IsStarProjection (e n) := fun n => by
    rw [he n]
    exact projection_below_projection _ _ (hQproj n) (hQproj (n + 1)) (hQmono n)
  have hQe : ∀ n, Q (n + 1) * e n = e n := by
    intro n
    have h1 : Q (n + 1) * Q n = Q n :=
      ((hQproj n).le_iff_mul_eq_right (hQproj (n + 1))).mp (hQmono n)
    rw [he n, mul_sub, h1, (hQproj (n + 1)).isIdempotentElem.eq]
  -- commutation with `a`
  have hua : ∀ n, a * u n = u n * a := by
    intro n
    rw [hu n, posPart_sub_algebraMap ha]
    have h1 : a * cfc (fun r : ℝ => (r - lam n) ⊔ 0) a
        = cfc (fun r : ℝ => r * ((r - lam n) ⊔ 0)) a := by
      rw [cfc_mul (fun r : ℝ => r) (fun r : ℝ => (r - lam n) ⊔ 0) a, cfc_id' ℝ a]
    have h2 : cfc (fun r : ℝ => (r - lam n) ⊔ 0) a * a
        = cfc (fun r : ℝ => ((r - lam n) ⊔ 0) * r) a := by
      rw [cfc_mul (fun r : ℝ => (r - lam n) ⊔ 0) (fun r : ℝ => r) a, cfc_id' ℝ a]
    rw [h1, h2]
    exact cfc_congr fun r _ => mul_comm _ _
  have hcommQ : ∀ N, a * Q N = Q N * a := by
    intro N
    cases N with
    | zero => rw [hQ0, mul_zero, zero_mul]
    | succ n => rw [hQs n]; exact vna_ceil_comm (u n) (hunn n) a (hua n)
  have hcomme : ∀ n, a * e n = e n * a := by
    intro n
    rw [he n, mul_sub, sub_mul, hcommQ n, hcommQ (n + 1)]
  -- the two-sided estimate `λₙ eₙ ≤ a eₙ ≤ ‖a‖ eₙ`
  have haen : ∀ n, (0 : A) ≤ a * e n := by
    intro n
    have : a * e n = e n * a * e n := by
      rw [← hcomme n, mul_assoc, (heproj n).isIdempotentElem.eq]
    rw [this]
    have := star_left_conjugate_nonneg ha (e n)
    rwa [(heproj n).isSelfAdjoint.star_eq] at this
  have hxQ : ∀ n, (a - algebraMap ℝ A (lam n)) * Q (n + 1) = u n := by
    intro n
    have hxsa : IsSelfAdjoint (a - algebraMap ℝ A (lam n)) := by
      refine hasa.sub ?_
      exact IsSelfAdjoint.of_nonneg (by
        simpa using (algebraMap_nonneg A (hlampos n).le))
    rw [hQs n, hu n]
    exact (ceil_pos_part_2 _ hxsa).2.1
  have hlow : ∀ n, lam n • e n ≤ a * e n := by
    intro n
    have hpos : (0 : A) ≤ e n * u n * e n := by
      have := star_left_conjugate_nonneg (hunn n) (e n)
      rwa [(heproj n).isSelfAdjoint.star_eq] at this
    have hcalc : e n * u n * e n = a * e n - lam n • e n := by
      rw [← hxQ n]
      calc e n * ((a - algebraMap ℝ A (lam n)) * Q (n + 1)) * e n
          = e n * (a - algebraMap ℝ A (lam n)) * (Q (n + 1) * e n) := by noncomm_ring
        _ = e n * (a - algebraMap ℝ A (lam n)) * e n := by rw [hQe n]
        _ = (e n * a) * e n - (algebraMap ℝ A (lam n) * e n) * e n := by
            rw [Algebra.commutes]; noncomm_ring
        _ = a * e n - lam n • e n := by
            rw [← hcomme n, mul_assoc, (heproj n).isIdempotentElem.eq, halg,
              smul_mul_assoc, (heproj n).isIdempotentElem.eq]
    rw [hcalc] at hpos
    exact sub_nonneg.mp hpos
  have hupp : ∀ n, a * e n ≤ ‖a‖ • e n := by
    intro n
    have h1 : a ≤ algebraMap ℝ A ‖a‖ := hasa.le_algebraMap_norm_self
    have h2 := (heproj n).isSelfAdjoint.conjugate_le_conjugate h1
    have h3 : e n * a * e n = a * e n := by
      rw [← hcomme n, mul_assoc, (heproj n).isIdempotentElem.eq]
    have h4 : e n * algebraMap ℝ A ‖a‖ * e n = ‖a‖ • e n := by
      rw [halg', smul_mul_assoc, (heproj n).isIdempotentElem.eq]
    rwa [h3, h4] at h2
  have hceil_ae : ∀ n, ceil (a * e n) = e n := by
    intro n
    refine le_antisymm ?_ ?_
    · calc ceil (a * e n) ≤ ceil (‖a‖ • e n) := ceil_mono (haen n) (hupp n)
        _ = ceil (e n) := ceil_smul (heproj n).nonneg hanorm
        _ = e n := ceil_of_isStarProjection (heproj n)
    · calc e n = ceil (e n) := (ceil_of_isStarProjection (heproj n)).symm
        _ = ceil (lam n • e n) := (ceil_smul (heproj n).nonneg (hlampos n)).symm
        _ ≤ ceil (a * e n) :=
            ceil_mono (smul_nonneg (hlampos n).le (heproj n).nonneg) (hlow n)
  -- the pseudoinverses `tₙ = (a eₙ)^{∼1}`
  have hpinv : ∀ n, Pseudoinvertible A (a * e n) := by
    intro n
    refine (pseudoinverse_basic_2'_2 (a * e n) (haen n)).mpr ⟨lam n, hlampos n, ?_⟩
    rw [hceil_ae n, Complex.coe_smul]
    exact hlow n
  obtain ⟨t, ht⟩ : ∃ t : ℕ → A, ∀ n, t n = pinv (a * e n) := ⟨_, fun _ => rfl⟩
  have hspec : ∀ n, IsPseudoinverse A (a * e n) (t n) := fun n => by
    rw [ht n]; exact pinv_spec (hpinv n)
  have hsuppae : ∀ n, suppProj (a * e n) = e n := fun n => by
    rw [suppProj_of_nonneg (haen n), hceil_ae n]
  have hrangeae : ∀ n, rangeProj (a * e n) = e n := fun n => by
    rw [rangeProj_eq_suppProj_of_isSelfAdjoint (IsSelfAdjoint.of_nonneg (haen n)),
      hsuppae n]
  have hrt : ∀ n, rangeProj (t n) = e n := fun n => by
    rw [← (hspec n).2.1, (hspec n).1, hsuppae n]
  have hst : ∀ n, suppProj (t n) = e n := fun n => by
    rw [← (hspec n).2.2.1, (hspec n).2.2.2, hrangeae n]
  have hta : ∀ n, t n * a = e n := by
    intro n
    calc t n * a = t n * suppProj (t n) * a := by rw [(ceill_basic_1 (t n)).1.2]
      _ = t n * (e n * a) := by rw [hst n, mul_assoc]
      _ = t n * (a * e n) := by rw [← hcomme n]
      _ = e n := by rw [(hspec n).1, hsuppae n]
  have hat : ∀ n, a * t n = e n := by
    intro n
    calc a * t n = a * (rangeProj (t n) * t n) := by rw [(ceill_basic_2 (t n)).1.2]
      _ = a * e n * t n := by rw [hrt n, mul_assoc]
      _ = e n := by rw [(hspec n).2.2.2, hrangeae n]
  -- the partial sums telescope to `Qₙ`, whose supremum is `⌈a⌉`
  have hsum : ∀ N, ∑ n ∈ Finset.range N, e n = Q N := by
    intro N
    simp only [he]
    rw [Finset.sum_range_sub Q N, hQ0, sub_zero]
  have hQlub : IsLUB (Set.range Q) (ceil a) := by
    have hdir : DirectedOn (· ≤ ·) (Set.range Q) := by
      have hmono : Monotone Q := monotone_nat_of_le_succ hQmono
      rintro _ ⟨N, rfl⟩ _ ⟨M, rfl⟩
      exact ⟨Q (max N M), ⟨max N M, rfl⟩, hmono (le_max_left N M),
        hmono (le_max_right N M)⟩
    have hlub := isLUB_projSup_of_directed (Set.range Q)
      (by rintro _ ⟨N, rfl⟩; exact hQproj N) (Set.range_nonempty _) hdir
    have hEq : projSup (Set.range Q) = ceil a := by
      refine projSup_eq (by rintro _ ⟨N, rfl⟩; exact hQproj N) (ceil_spec ha).1
        (by rintro _ ⟨N, rfl⟩; exact hQle N) ?_
      intro p hp hub
      refine (ceil_le_iff ha hp).mpr ?_
      have hup : ∀ n, u n * p = u n := by
        intro n
        refine (ceil_le_iff (hunn n) hp).mp ?_
        rw [← hQs n]
        exact hub _ ⟨n + 1, rfl⟩
      have hbound : ∀ n : ℕ, ‖a * p - a‖ ≤ 2 * (1 / ((n : ℝ) + 1)) := by
        intro n
        have hnp : ‖p‖ ≤ 1 := norm_le_one_of_mem_effects ⟨hp.nonneg, hp.le_one⟩
        have hrw : a * p - a = (a - u n) * p - (a - u n) := by
          rw [sub_mul, hup n]; abel
        have hun : ‖a - u n‖ ≤ lam n := by
          rw [hu n]; exact norm_sub_posPart_le ha (hlampos n).le
        calc ‖a * p - a‖ = ‖(a - u n) * p - (a - u n)‖ := by rw [hrw]
          _ ≤ ‖(a - u n) * p‖ + ‖a - u n‖ := norm_sub_le _ _
          _ ≤ ‖a - u n‖ * ‖p‖ + ‖a - u n‖ := by gcongr; exact norm_mul_le _ _
          _ ≤ ‖a - u n‖ * 1 + ‖a - u n‖ := by gcongr
          _ = 2 * ‖a - u n‖ := by ring
          _ ≤ 2 * (1 / ((n : ℝ) + 1)) := by
              rw [← hlam n]; linarith [hun]
      have htend : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
      have hzero : ‖a * p - a‖ ≤ 0 :=
        ge_of_tendsto htend (Filter.Eventually.of_forall hbound)
      exact sub_eq_zero.mp (norm_le_zero_iff.mp hzero)
    rwa [hEq] at hlub
  have hsetQ : ∀ f : ℕ → A, (∀ n, f n = e n) →
      {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, f n} = Set.range Q := by
    intro f hf
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨N, rfl⟩
      exact ⟨N, by simp only [hf]; rw [hsum N]⟩
    · rintro ⟨N, rfl⟩
      exact ⟨N, by simp only [hf]; rw [hsum N]⟩
  refine ⟨t, fun n => by rw [hta n]; exact heproj n,
    fun n => by rw [hat n]; exact heproj n, ?_, ?_, ?_, ?_⟩
  · rw [hsetQ _ hta, hsuppa]; exact hQlub
  · rw [hsetQ _ hrt, hsuppa]; exact hQlub
  · rw [hsetQ _ hat, hrangea]; exact hQlub
  · rw [hsetQ _ hst, hrangea]; exact hQlub

/-- **80IV** (`approximate-pseudoinverse`, vn.tex:5278, Theorem): every
element of a von Neumann algebra has an approximate pseudoinverse.  By
**80III** it suffices to treat the positive element `a*a`. -/
theorem approximate_pseudoinverse (a : A) :
    ∃ t : ℕ → A, IsApproxPseudoinverse A a t := by
  obtain ⟨t, ht⟩ :=
    approximate_pseudoinverse_of_nonneg (star a * a) (star_mul_self_nonneg a)
  exact ⟨fun n => t n * star a, approximate_pseudoinverse_reduction a t ht⟩

/-! ## Parsec 810: division -/

/-- **81I** (`division`, vn.tex:5342, Definition), well-definedness (via
**60VIII**): for `a ∈ Ab` there is a unique `c ∈ A⌊b⌉` with `a = cb`. -/
theorem exists_div (a b : A) (h : ∃ c : A, a = c * b) :
    ∃! c : A, a = c * b ∧ c * rangeProj b = c := by
  -- existence: replace a witness `c₀` by `c₀⌊b⌉`; uniqueness is **60VIII**,
  -- since `c⌊b⌉ = c` forces `⌈c⌋ ≤ ⌊b⌉`
  obtain ⟨c₀, hc₀⟩ := h
  obtain ⟨hrb, hrba⟩ := (ceill_basic_2 b).1
  refine ⟨c₀ * rangeProj b, ⟨by rw [mul_assoc, hrba, hc₀],
    by rw [mul_assoc, hrb.isIdempotentElem.eq]⟩, ?_⟩
  rintro c ⟨hcb, hcr⟩
  refine mult_cancellation_2 b c (c₀ * rangeProj b)
    ((ceill_basic_1 c).2 ⟨hrb, hcr⟩)
    ((ceill_basic_1 _).2 ⟨hrb, by rw [mul_assoc, hrb.isIdempotentElem.eq]⟩) ?_
  rw [mul_assoc, hrba, ← hc₀, ← hcb]

open scoped Classical in
/-- **81I** (`division`, vn.tex:5342, Definition): the quotient `a/b`: the
unique `c ∈ A⌊b⌉` with `a = cb`, for `a ∈ Ab` (junk value `0`
otherwise). -/
noncomputable def div (a b : A) : A :=
  if h : ∃ c : A, a = c * b then (exists_div a b h).choose else 0

/-- **81I** (`division`, vn.tex:5342, Definition), dually: `b∖a`: the
unique `c ∈ ⌈b⌋A` with `a = bc`, for `a ∈ bA` (junk value `0`
otherwise). -/
noncomputable def ldiv (b a : A) : A := star (div (star a) (star b))

/-- The defining property of `a/b` (for `a ∈ Ab`). -/
theorem div_spec (a b : A) (h : ∃ c : A, a = c * b) :
    a = div a b * b ∧ div a b * rangeProj b = div a b := by
  rw [div, dif_pos h]
  exact (exists_div a b h).choose_spec.1

/-- `a/b` is characterised by its defining property. -/
theorem div_eq {a b c : A} (h1 : a = c * b) (h2 : c * rangeProj b = c) :
    div a b = c :=
  (exists_div a b ⟨c, h1⟩).unique (div_spec a b ⟨c, h1⟩) ⟨h1, h2⟩

/-- The defining property of `b∖a` (for `a ∈ bA`). -/
theorem ldiv_spec (b a : A) (h : ∃ c : A, a = b * c) :
    a = b * ldiv b a ∧ suppProj b * ldiv b a = ldiv b a := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨h1, h2⟩ := div_spec (star a) (star b) ⟨star c, by rw [hc, star_mul]⟩
  have hsb : star (suppProj b) = suppProj b :=
    (ceill_basic_1 b).1.1.isSelfAdjoint.star_eq
  constructor
  · have hst := congrArg star h1
    rw [star_star, star_mul, star_star] at hst
    exact hst
  · have hst := congrArg star h2
    rw [star_mul, rangeProj_star, hsb] at hst
    exact hst

/-- `b∖a` is characterised by its defining property. -/
theorem ldiv_eq {a b c : A} (h1 : a = b * c) (h2 : suppProj b * c = c) :
    ldiv b a = c := by
  have hsb : star (suppProj b) = suppProj b :=
    (ceill_basic_1 b).1.1.isSelfAdjoint.star_eq
  have h1' : star a = star c * star b := by rw [h1, star_mul]
  have h2' : star c * rangeProj (star b) = star c := by
    rw [rangeProj_star, ← hsb, ← star_mul, h2]
  show star (div (star a) (star b)) = c
  rw [div_eq h1' h2', star_star]

/-- **81II** (vn.tex:5358, Exercise), part 1: `c/b ∈ ⌊c⌉A⌊b⌉` for
`c ∈ Ab`.

**Thesis defect (recorded, not repaired).**  vn.tex:5361 prints "for every
element `c` of `b𝒜`", which cannot be meant: `c/b` is defined (**81I**) only
for `c ∈ 𝒜b`, and the conclusion `c/b ∈ ⌊c⌉𝒜⌊b⌉` is about that quotient.  Our
hypothesis `∃ d, c = d * b` is the correct `𝒜b`, so this statement silently
carries the repair. -/
theorem division_basic_1 (b c : A) (h : ∃ d : A, c = d * b) :
    rangeProj c * div c b = div c b ∧ div c b * rangeProj b = div c b := by
  -- `⌊c⌉ = ⌊(c/b)b⌉ = ⌊(c/b)⌊b⌉⌉ = ⌊c/b⌉` by **60VII**.2, and `⌊d⌉d = d`
  obtain ⟨hcb, hcr⟩ := div_spec c b h
  refine ⟨?_, hcr⟩
  have hrc : rangeProj c = rangeProj (div c b) := by
    conv_lhs => rw [hcb]
    rw [(ceil_fundamental_2 (div c b) b).2, hcr]
  rw [hrc]
  exact (ceill_basic_2 (div c b)).1.2

/-- **81II** (vn.tex:5358, Exercise), part 2: `(ab)/b = a⌊b⌉` and
`b∖(ba) = ⌈b⌋a`. -/
theorem division_basic_2 (a b : A) :
    div (a * b) b = a * rangeProj b ∧ ldiv b (b * a) = suppProj b * a := by
  obtain ⟨hrb, hrba⟩ := (ceill_basic_2 b).1
  have hmain : ∀ x y : A, div (x * y) y = x * rangeProj y := by
    intro x y
    obtain ⟨hry, hrya⟩ := (ceill_basic_2 y).1
    exact div_eq (by rw [mul_assoc, hrya])
      (by rw [mul_assoc, hry.isIdempotentElem.eq])
  refine ⟨hmain a b, ?_⟩
  have hsb : star (suppProj b) = suppProj b :=
    (ceill_basic_1 b).1.1.isSelfAdjoint.star_eq
  show star (div (star (b * a)) (star b)) = suppProj b * a
  rw [star_mul, hmain (star a) (star b), rangeProj_star, star_mul, hsb, star_star]

/-- **81II** (vn.tex:5358, Exercise), part 3: for `c ∈ aAb`:
`a∖c ∈ Ab`, `c/b ∈ aA`, and `(a∖c)/b = a∖(c/b) =: a∖c/b` is the unique
`d ∈ ⌈a⌋A⌊b⌉` with `c = adb`.

The fourth clause **names** that unique element: `d` satisfies the three
conditions *iff* `d = a∖c/b`.  (A bare `∃!` would deliver uniqueness without
connecting it to `a∖c/b`, which is what the point is about.) -/
theorem division_basic_3 (a b c : A) (h : ∃ d : A, c = a * d * b) :
    (∃ d : A, ldiv a c = d * b) ∧ (∃ d : A, div c b = a * d) ∧
      div (ldiv a c) b = ldiv a (div c b) ∧
      (∀ e : A, (c = a * e * b ∧ suppProj a * e = e ∧ e * rangeProj b = e)
        ↔ e = ldiv a (div c b)) := by
  -- everything is read off from the two explicit descriptions
  -- `a∖c = (⌈a⌋d)b` and `c/b = a(d⌊b⌉)`
  obtain ⟨d, hd⟩ := h
  obtain ⟨hsa, hsaa⟩ := (ceill_basic_1 a).1
  obtain ⟨hrb, hrbb⟩ := (ceill_basic_2 b).1
  have hl : ldiv a c = suppProj a * d * b := by
    refine ldiv_eq (by rw [hd, ← mul_assoc, ← mul_assoc, hsaa]) ?_
    rw [← mul_assoc, ← mul_assoc, hsa.isIdempotentElem.eq]
  have habs : a * (suppProj a * d * rangeProj b) * b = a * d * b := by
    calc a * (suppProj a * d * rangeProj b) * b
        = a * suppProj a * d * (rangeProj b * b) := by noncomm_ring
      _ = a * d * b := by rw [hsaa, hrbb]
  have hidem : suppProj a * d * rangeProj b * rangeProj b
      = suppProj a * d * rangeProj b := by
    calc suppProj a * d * rangeProj b * rangeProj b
        = suppProj a * d * (rangeProj b * rangeProj b) := by noncomm_ring
      _ = suppProj a * d * rangeProj b := by rw [hrb.isIdempotentElem.eq]
  have hr : div c b = a * (d * rangeProj b) := by
    refine div_eq ?_ ?_
    · rw [hd]
      calc a * d * b = a * d * (rangeProj b * b) := by rw [hrbb]
        _ = a * (d * rangeProj b) * b := by noncomm_ring
    · calc a * (d * rangeProj b) * rangeProj b
          = a * (d * (rangeProj b * rangeProj b)) := by noncomm_ring
        _ = a * (d * rangeProj b) := by rw [hrb.isIdempotentElem.eq]
  -- the explicit value of `a∖c/b`
  have hval : ldiv a (div c b) = suppProj a * d * rangeProj b := by
    rw [hr, (division_basic_2 (d * rangeProj b) a).2, mul_assoc]
  refine ⟨⟨suppProj a * d, hl⟩, ⟨d * rangeProj b, hr⟩, ?_, ?_⟩
  · rw [hl, hr, (division_basic_2 (suppProj a * d) b).1,
      (division_basic_2 (d * rangeProj b) a).2, mul_assoc]
  · intro e
    refine ⟨?_, ?_⟩
    · rw [hval]
      rintro ⟨he, hea, heb⟩
      -- uniqueness: cancel `b` on the right (**60VIII**), then `a` on the left
      have hcancelb : a * e = a * (suppProj a * d * rangeProj b) := by
        refine mult_cancellation_2 b (a * e) (a * (suppProj a * d * rangeProj b))
          ((ceill_basic_1 _).2 ⟨hrb, by rw [mul_assoc, heb]⟩)
          ((ceill_basic_1 _).2 ⟨hrb, by rw [mul_assoc, hidem]⟩) ?_
        rw [← he, hd, habs]
      have hstar := congrArg star hcancelb
      rw [star_mul, star_mul] at hstar
      have hkey : star e = star (suppProj a * d * rangeProj b) := by
        refine mult_cancellation_2 (star a) (star e)
          (star (suppProj a * d * rangeProj b)) ?_ ?_ hstar
        · rw [suppProj_star, rangeProj_star]
          exact (ceill_basic_2 e).2 ⟨hsa, hea⟩
        · rw [suppProj_star, rangeProj_star]
          refine (ceill_basic_2 _).2 ⟨hsa, ?_⟩
          rw [← mul_assoc, ← mul_assoc, hsa.isIdempotentElem.eq]
      have := congrArg star hkey
      rwa [star_star, star_star] at this
    · rintro rfl
      rw [hval]
      exact ⟨by rw [hd, habs], by rw [← mul_assoc, ← mul_assoc,
        hsa.isIdempotentElem.eq], hidem⟩

/-- **81II** (vn.tex:5358, Exercise), part 4: for `c ∈ Ab` and `d ∈ aA`:
`dc ∈ aAb` and `a∖(dc)/b = (a∖d)(c/b)`. -/
theorem division_basic_4 (a b c d : A) (hc : ∃ x : A, c = x * b)
    (hd : ∃ x : A, d = a * x) :
    (∃ x : A, d * c = a * x * b) ∧
      ldiv a (div (d * c) b) = ldiv a d * div c b := by
  obtain ⟨hc1, hc2⟩ := div_spec c b hc
  obtain ⟨hd1, hd2⟩ := ldiv_spec a d hd
  obtain ⟨x, hx⟩ := hc
  obtain ⟨y, hy⟩ := hd
  refine ⟨⟨y * x, by rw [hx, hy]; noncomm_ring⟩, ?_⟩
  -- `(dc)/b = d(c/b)`, and then `a∖(d(c/b)) = (a∖d)(c/b)`
  have h1 : div (d * c) b = d * div c b :=
    div_eq (by conv_lhs => rw [hc1]
               noncomm_ring)
      (by rw [mul_assoc, hc2])
  rw [h1]
  refine ldiv_eq ?_ ?_
  · conv_lhs => rw [hd1]
    noncomm_ring
  · rw [← mul_assoc, hd2]

/-- **81II** (vn.tex:5358, Exercise), part 5: for `c ∈ Ab`: `c* ∈ b*A` and
`b*∖c* = (c/b)*`. -/
theorem division_basic_5 (b c : A) (h : ∃ x : A, c = x * b) :
    (∃ x : A, star c = star b * x) ∧
      ldiv (star b) (star c) = star (div c b) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨⟨star x, by rw [hx, star_mul]⟩, ?_⟩
  show star (div (star (star c)) (star (star b))) = star (div c b)
  rw [star_star, star_star]

/-- Auxiliary: an increasing sequence of projections converges ultrastrongly
to its supremum. -/
theorem usTendsto_of_monotone_isStarProjection {P : ℕ → A}
    (hproj : ∀ N, IsStarProjection (P N)) (hmono : Monotone P) {q : A}
    (hq : IsLUB (Set.range P) q) : USTendsto P atTop q := by
  have hPrange : ∀ r ∈ Set.range P, IsStarProjection r := by
    rintro _ ⟨N, rfl⟩; exact hproj N
  have hdir : DirectedOn (· ≤ ·) (Set.range P) := by
    rintro _ ⟨N, rfl⟩ _ ⟨M, rfl⟩
    exact ⟨P (max N M), ⟨max N M, rfl⟩, hmono (le_max_left N M),
      hmono (le_max_right N M)⟩
  have hlub' :=
    isLUB_projSup_of_directed (Set.range P) hPrange (Set.range_nonempty _) hdir
  have hqeq : q = projSup (Set.range P) := hq.unique hlub'
  have hqproj : IsStarProjection q := by rw [hqeq]; exact (projSup_spec hPrange).1
  have hle : ∀ N, P N ≤ q := fun N => hq.1 ⟨N, rfl⟩
  have hsa : ∀ N, IsSelfAdjoint (P N) := fun N => (hproj N).isSelfAdjoint
  rw [usTendsto_iff]
  intro ω
  have hfun : ∀ N, omegaNorm A ω (P N - q)
      = Real.sqrt ((ω q : ℂ).re - (ω (P N) : ℂ).re) := by
    intro N
    have hdiff : IsStarProjection (q - P N) :=
      projection_below_projection _ _ (hproj N) hqproj (hle N)
    have hstar : star (P N - q) * (P N - q) = q - P N := by
      have hs : star (P N - q) = -(q - P N) := by
        rw [star_sub, (hsa N).star_eq, hqproj.isSelfAdjoint.star_eq]; abel
      rw [hs, show P N - q = -(q - P N) by abel, neg_mul_neg]
      exact hdiff.isIdempotentElem.eq
    rw [omegaNorm, hstar, npFunctional_sub]
    simp
  simp only [hfun]
  set D : Set (selfAdjoint A) := {d : selfAdjoint A | (d : A) ∈ Set.range P} with hD
  have hDval : Subtype.val '' D = Set.range P := by
    ext x
    exact ⟨by rintro ⟨d, hd, rfl⟩; exact hd,
      fun hx => ⟨⟨x, by obtain ⟨N, rfl⟩ := hx; exact hsa N⟩, hx, rfl⟩⟩
  have hDne : D.Nonempty := ⟨⟨P 0, hsa 0⟩, ⟨0, rfl⟩⟩
  have hDdir : DirectedOn (· ≤ ·) D := by
    intro x hx y hy
    obtain ⟨c, hc, hxc, hyc⟩ := hdir _ hx _ hy
    exact ⟨⟨c, by obtain ⟨N, rfl⟩ := hc; exact hsa N⟩, hc, hxc, hyc⟩
  have hDlub : IsLUB D (⟨q, hqproj.isSelfAdjoint⟩ : selfAdjoint A) := by
    refine isLUB_sa_of_isLUB ?_
    rw [hDval]; exact hq
  have hωlub := ω.preservesDirSups' D _ hDne hDdir hDlub
  have hreal : ∀ w ∈ ((fun d : selfAdjoint A => (ω (d : A) : ℂ)) '' D), w.im = 0 := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨N, hN⟩ := hd
    have h0 : (0 : ℂ) ≤ ω (d : A) := by
      rw [← hN] at *
      exact npFunctional_nonneg ω (hproj N).nonneg
    exact ((Complex.le_def.mp h0).2).symm
  have hrelub := isLUB_re_of_isLUB hreal hωlub
  have hrange : Complex.re '' ((fun d : selfAdjoint A => (ω (d : A) : ℂ)) '' D)
      = Set.range (fun N : ℕ => (ω (P N) : ℂ).re) := by
    ext r
    constructor
    · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
      obtain ⟨N, hN⟩ := hd
      exact ⟨N, by change (ω (P N) : ℂ).re = ((ω (d : A) : ℂ)).re; rw [hN]⟩
    · rintro ⟨N, rfl⟩
      exact ⟨ω (P N), ⟨⟨P N, hsa N⟩, ⟨N, rfl⟩, rfl⟩, rfl⟩
  rw [hrange] at hrelub
  have hmono' : Monotone (fun N : ℕ => (ω (P N) : ℂ).re) := fun M N h =>
    (Complex.le_def.mp (npFunctional_mono ω (hmono h))).1
  have htend := tendsto_atTop_isLUB hmono' hrelub
  have hlim : Tendsto (fun N : ℕ => (ω q : ℂ).re - (ω (P N) : ℂ).re) atTop (𝓝 0) := by
    have htend' : Tendsto (fun N : ℕ => (ω (P N) : ℂ).re) atTop (𝓝 ((ω q : ℂ).re)) :=
      htend
    have h := (tendsto_const_nhds
      (x := (ω q : ℂ).re) (f := (atTop : Filter ℕ))).sub htend'
    simpa using h
  have hc := (Real.continuous_sqrt.tendsto 0).comp hlim
  simpa [Function.comp_def] using hc

/-- Auxiliary for **81III**: given a sequence of projections whose partial
sums have a least upper bound `q ≤ 1`, the partial sums are themselves
projections, increase to `q`, and converge ultrastrongly to it. -/
theorem partialSums_of_isLUB {p : ℕ → A} (hp : ∀ n, IsStarProjection (p n))
    {q : A} (hq : IsLUB {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, p n} q)
    (hq1 : q ≤ 1) :
    (∀ N : ℕ, IsStarProjection (∑ n ∈ Finset.range N, p n)) ∧
      Monotone (fun N : ℕ => ∑ n ∈ Finset.range N, p n) ∧
      USTendsto (fun N : ℕ => ∑ n ∈ Finset.range N, p n) atTop q := by
  classical
  have hmono : Monotone (fun N : ℕ => ∑ n ∈ Finset.range N, p n) := by
    intro M N h
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono h)
      fun i _ _ => (hp i).nonneg
  have hub : ∀ N : ℕ, ∑ n ∈ Finset.range N, p n ≤ q := fun N => hq.1 ⟨N, rfl⟩
  have horth : ∀ n m : ℕ, n ≠ m → p n * p m = 0 := by
    intro n m hnm
    have hsub : p n + p m ≤ ∑ k ∈ Finset.range (max n m + 1), p k := by
      have hsubset : ({n, m} : Finset ℕ) ⊆ Finset.range (max n m + 1) := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl <;>
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega))
      have := Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun k _ _ => (hp k).nonneg)
      rwa [Finset.sum_pair hnm] at this
    exact ((orthogonal_tuple_of_projections_1 (p n) (p m) (hp n) (hp m)).out 3 0).mp
      (hsub.trans ((hub _).trans hq1))
  have hproj : ∀ N : ℕ, IsStarProjection (∑ n ∈ Finset.range N, p n) := fun N =>
    isStarProjection_sum _ p hp fun i _ j _ hij => horth i j hij
  refine ⟨hproj, hmono, ?_⟩
  refine usTendsto_of_monotone_isStarProjection hproj hmono ?_
  have hset : Set.range (fun N : ℕ => ∑ n ∈ Finset.range N, p n)
      = {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, p n} := by
    ext x
    exact ⟨fun ⟨N, hN⟩ => ⟨N, hN.symm⟩, fun ⟨N, hN⟩ => ⟨N, hN.symm⟩⟩
  rw [hset]; exact hq


/-- Auxiliary for **81III**, the thesis's block estimate (vn.tex:5411): for
`a*a ≤ b*b` and an approximate pseudoinverse `t` of `b`,
`(∑_{n=M}^{N} a tₙ)* (∑_{n=M}^{N} a tₙ) ≤ ∑_{n=M}^{N} b tₙ`, whence
`‖∑_{n=M}^{N} a tₙ‖_ω ≤ (ω(∑_{n<N} b tₙ) − ω(∑_{n<M} b tₙ))^½`.  The bound
does not mention `a`, which is what makes the convergence uniform in `a`
(**81III**, second half). -/
theorem apinv_block_est {a b : A} (h : star a * a ≤ star b * b) {t : ℕ → A}
    (ht : IsApproxPseudoinverse A b t) (ω : NPFunctional A) {M N : ℕ}
    (hMN : M ≤ N) :
    omegaNorm A ω (∑ n ∈ Finset.range N, a * t n - ∑ n ∈ Finset.range M, a * t n)
      ≤ Real.sqrt ((ω (∑ n ∈ Finset.range N, b * t n) : ℂ).re
          - (ω (∑ n ∈ Finset.range M, b * t n) : ℂ).re) := by
  classical
  obtain ⟨hPproj, hPmono, _⟩ :=
    partialSums_of_isLUB (p := fun n => b * t n) ht.proj_right ht.sum_right
      (ceill_basic_2 b).1.1.le_one
  have hIco : ∀ (f : ℕ → A) (M N : ℕ), M ≤ N →
      ∑ n ∈ Finset.range N, f n - ∑ n ∈ Finset.range M, f n
        = ∑ n ∈ Finset.Ico M N, f n := by
    intro f M N hMN
    have hcons := Finset.sum_Ico_consecutive f (Nat.zero_le M) hMN
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (eq_sub_of_add_eq' hcons).symm
  have hproj : IsStarProjection (∑ n ∈ Finset.range N, b * t n
      - ∑ n ∈ Finset.range M, b * t n) :=
    projection_below_projection _ _ (hPproj M) (hPproj N) (hPmono hMN)
  have hsq : star (∑ n ∈ Finset.range N, b * t n - ∑ n ∈ Finset.range M, b * t n) *
      (∑ n ∈ Finset.range N, b * t n - ∑ n ∈ Finset.range M, b * t n)
      = ∑ n ∈ Finset.range N, b * t n - ∑ n ∈ Finset.range M, b * t n := by
    rw [hproj.isSelfAdjoint.star_eq]; exact hproj.isIdempotentElem.eq
  have hest : star (∑ n ∈ Finset.range N, a * t n - ∑ n ∈ Finset.range M, a * t n) *
      (∑ n ∈ Finset.range N, a * t n - ∑ n ∈ Finset.range M, a * t n)
      ≤ star (∑ n ∈ Finset.range N, b * t n - ∑ n ∈ Finset.range M, b * t n) *
        (∑ n ∈ Finset.range N, b * t n - ∑ n ∈ Finset.range M, b * t n) := by
    rw [hIco (fun n => a * t n) M N hMN, hIco (fun n => b * t n) M N hMN,
      ← Finset.mul_sum, ← Finset.mul_sum]
    calc star (a * ∑ n ∈ Finset.Ico M N, t n) * (a * ∑ n ∈ Finset.Ico M N, t n)
        = star (∑ n ∈ Finset.Ico M N, t n) * (star a * a) *
            (∑ n ∈ Finset.Ico M N, t n) := by rw [star_mul]; noncomm_ring
      _ ≤ star (∑ n ∈ Finset.Ico M N, t n) * (star b * b) *
            (∑ n ∈ Finset.Ico M N, t n) :=
          star_left_conjugate_le_conjugate h _
      _ = star (b * ∑ n ∈ Finset.Ico M N, t n) *
            (b * ∑ n ∈ Finset.Ico M N, t n) := by rw [star_mul]; noncomm_ring
  refine (omegaNorm_le_omegaNorm ω hest).trans (le_of_eq ?_)
  rw [omegaNorm, hsq, npFunctional_sub]
  simp

/-- **81III** (`proto-douglas`, vn.tex:5395, Lemma), part 1: if
`a*a ≤ b*b` then `a ∈ Ab`, and the series `∑ₙ atₙ` (for an approximate
pseudoinverse `t` of `b`) converges ultrastrongly to `a/b`. -/
theorem proto_douglas_1 (a b : A) (h : star a * a ≤ star b * b)
    (t : ℕ → A) (ht : IsApproxPseudoinverse A b t) :
    (∃ c : A, a = c * b) ∧
      USTendsto (fun N : ℕ => ∑ n ∈ Finset.range N, a * t n) atTop
        (div a b) := by
  classical
  obtain ⟨hPproj, hPmono, _hPtend⟩ :=
    partialSums_of_isLUB (p := fun n => b * t n) ht.proj_right ht.sum_right
      (ceill_basic_2 b).1.1.le_one
  obtain ⟨_hQproj, _hQmono, hQtend⟩ :=
    partialSums_of_isLUB (p := fun n => t n * b) ht.proj_left ht.sum_left
      (ceill_basic_1 b).1.1.le_one
  set S : ℕ → A := fun N => ∑ n ∈ Finset.range N, a * t n with hSdef
  set P : ℕ → A := fun N => ∑ n ∈ Finset.range N, b * t n with hPdef
  set Q : ℕ → A := fun N => ∑ n ∈ Finset.range N, t n * b with hQdef
  have hnormbd : ∀ (ω : NPFunctional A) (M N : ℕ), M ≤ N →
      omegaNorm A ω (S N - S M)
        ≤ Real.sqrt ((ω (P N) : ℂ).re - (ω (P M) : ℂ).re) :=
    fun ω M N hMN => apinv_block_est h ht ω hMN
  -- `PN ≤ ⌊b⌉`, so `ω(PN).re` increases to a finite limit
  have hPub : ∀ N : ℕ, P N ≤ rangeProj b := fun N => ht.sum_right.1 ⟨N, rfl⟩
  have hcauchy : ∀ ω : NPFunctional A,
      Tendsto (fun p : ℕ × ℕ => omegaNorm A ω (S p.1 - S p.2)) (atTop ×ˢ atTop)
        (𝓝 0) := by
    intro ω
    set g : ℕ → ℝ := fun N => (ω (P N) : ℂ).re with hgdef
    have hgmono : Monotone g := fun M N hMN =>
      (Complex.le_def.mp (npFunctional_mono ω (hPmono hMN))).1
    have hgbdd : BddAbove (Set.range g) := by
      refine ⟨(ω (rangeProj b) : ℂ).re, ?_⟩
      rintro _ ⟨N, rfl⟩
      exact (Complex.le_def.mp (npFunctional_mono ω (hPub N))).1
    have hgtend : Tendsto g atTop (𝓝 (⨆ N, g N)) := tendsto_atTop_ciSup hgmono hgbdd
    have hbound : ∀ p : ℕ × ℕ,
        omegaNorm A ω (S p.1 - S p.2) ≤ Real.sqrt |g p.1 - g p.2| := by
      intro p
      rcases le_total p.2 p.1 with hle | hle
      · exact (hnormbd ω p.2 p.1 hle).trans (Real.sqrt_le_sqrt (le_abs_self _))
      · have heq : omegaNorm A ω (S p.1 - S p.2) = omegaNorm A ω (S p.2 - S p.1) := by
          rw [← omegaNorm_neg ω (S p.2 - S p.1)]; congr 1; abel
        rw [heq]
        refine (hnormbd ω p.1 p.2 hle).trans (Real.sqrt_le_sqrt ?_)
        rw [abs_sub_comm]; exact le_abs_self _
    have hlim : Tendsto (fun p : ℕ × ℕ => Real.sqrt |g p.1 - g p.2|)
        (atTop ×ˢ atTop) (𝓝 0) := by
      have h1 : Tendsto (fun p : ℕ × ℕ => g p.1) (atTop ×ˢ atTop) (𝓝 (⨆ N, g N)) :=
        hgtend.comp tendsto_fst
      have h2 : Tendsto (fun p : ℕ × ℕ => g p.2) (atTop ×ˢ atTop) (𝓝 (⨆ N, g N)) :=
        hgtend.comp tendsto_snd
      have h3 : Tendsto (fun p : ℕ × ℕ => g p.1 - g p.2) (atTop ×ˢ atTop) (𝓝 0) := by
        simpa using h1.sub h2
      have hcont : Continuous fun x : ℝ => Real.sqrt |x| :=
        Real.continuous_sqrt.comp continuous_abs
      have := (hcont.tendsto 0).comp h3
      simpa [Function.comp_def] using this
    exact squeeze_zero (fun p => omegaNorm_nonneg _ _) hbound hlim
  obtain ⟨c, hc⟩ := vn_complete_1 (atTop : Filter ℕ) S hcauchy
  -- `a = c b`
  have hsupp : a * suppProj b = a := by
    have hle : suppProj a ≤ suppProj b := ceil_mono (star_mul_self_nonneg a) h
    have hmul : suppProj a * suppProj b = suppProj a :=
      ((projection_below_effect (suppProj b) (suppProj a)
        ⟨(ceill_basic_1 b).1.1.nonneg, (ceill_basic_1 b).1.1.le_one⟩
        (ceill_basic_1 a).1.1).out 0 7).mp hle
    calc a * suppProj b = a * suppProj a * suppProj b := by rw [(ceill_basic_1 a).1.2]
      _ = a * (suppProj a * suppProj b) := by noncomm_ring
      _ = a * suppProj a := by rw [hmul]
      _ = a := (ceill_basic_1 a).1.2
  have hSQ : ∀ N : ℕ, S N * b = a * Q N := by
    intro N
    rw [hSdef, hQdef]
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  let _ : TopologicalSpace A := ultrastrong A
  have _ : T2Space A := (vn_positive_basic_1 (A := A)).2
  have hlim1 : USTendsto (fun N : ℕ => a * Q N) atTop (c * b) := by
    have h1 : USTendsto (fun N : ℕ => (1 : A) * S N * b) atTop ((1 : A) * c * b) :=
      usTendsto_mul_left_right (1 : A) b hc
    simp only [one_mul] at h1
    simpa only [hSQ] using h1
  have hlim2 : USTendsto (fun N : ℕ => a * Q N) atTop a := by
    have h2 : USTendsto (fun N : ℕ => a * Q N * (1 : A)) atTop (a * suppProj b * (1 : A)) :=
      usTendsto_mul_left_right a (1 : A) hQtend
    simp only [mul_one, hsupp] at h2
    exact h2
  have hcb : c * b = a := tendsto_nhds_unique hlim1 hlim2
  -- `c ⌊b⌉ = c`
  have htr : ∀ n : ℕ, t n * rangeProj b = t n := by
    intro n
    have hle : suppProj (t n) ≤ rangeProj b := by
      refine le_trans ?_ (ht.sum_supp.1 ⟨n + 1, rfl⟩)
      exact Finset.single_le_sum (f := fun k => suppProj (t k))
        (fun k _ => (ceill_basic_1 (t k)).1.1.nonneg) (Finset.self_mem_range_succ n)
    have hmul : suppProj (t n) * rangeProj b = suppProj (t n) :=
      ((projection_below_effect (rangeProj b) (suppProj (t n))
        ⟨(ceill_basic_2 b).1.1.nonneg, (ceill_basic_2 b).1.1.le_one⟩
        (ceill_basic_1 (t n)).1.1).out 0 7).mp hle
    calc t n * rangeProj b = t n * suppProj (t n) * rangeProj b := by
          rw [(ceill_basic_1 (t n)).1.2]
      _ = t n * (suppProj (t n) * rangeProj b) := by noncomm_ring
      _ = t n * suppProj (t n) := by rw [hmul]
      _ = t n := (ceill_basic_1 (t n)).1.2
  have hSr : ∀ N : ℕ, S N * rangeProj b = S N := by
    intro N
    rw [hSdef]
    simp only [Finset.sum_mul, mul_assoc, htr]
  have hlim3 : USTendsto S atTop (c * rangeProj b) := by
    have h3 : USTendsto (fun N : ℕ => (1 : A) * S N * rangeProj b) atTop
        ((1 : A) * c * rangeProj b) := usTendsto_mul_left_right (1 : A) (rangeProj b) hc
    simp only [one_mul, hSr] at h3
    exact h3
  have hcr : c * rangeProj b = c := tendsto_nhds_unique hlim3 hc
  exact ⟨⟨c, hcb.symm⟩, by rw [div_eq hcb.symm hcr]; exact hc⟩

/-- **81III** (`proto-douglas`, vn.tex:5395, Lemma), part 2: the
convergence of `∑ₙ atₙ` to `a/b` is uniform in `a` (over
`{a | a*a ≤ b*b}`). -/
theorem proto_douglas_2 (b : A) (t : ℕ → A)
    (ht : IsApproxPseudoinverse A b t) (ω : NPFunctional A) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ a : A, star a * a ≤ star b * b → ∀ M ≥ N,
      omegaNorm A ω (div a b - ∑ n ∈ Finset.range M, a * t n) ≤ ε := by
  classical
  obtain ⟨_, hPmono, _⟩ :=
    partialSums_of_isLUB (p := fun n => b * t n) ht.proj_right ht.sum_right
      (ceill_basic_2 b).1.1.le_one
  set g : ℕ → ℝ := fun N => (ω (∑ n ∈ Finset.range N, b * t n) : ℂ).re with hgdef
  have hgmono : Monotone g := fun M N hMN =>
    (Complex.le_def.mp (npFunctional_mono ω (hPmono hMN))).1
  have hgbdd : BddAbove (Set.range g) := by
    refine ⟨(ω (rangeProj b) : ℂ).re, ?_⟩
    rintro _ ⟨N, rfl⟩
    exact (Complex.le_def.mp (npFunctional_mono ω (ht.sum_right.1 ⟨N, rfl⟩))).1
  have hgL : ∀ N : ℕ, g N ≤ ⨆ K, g K := fun N => le_ciSup hgbdd N
  have hgtend : Tendsto g atTop (𝓝 (⨆ K, g K)) := tendsto_atTop_ciSup hgmono hgbdd
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (⨆ K, g K) - g N ≤ ε ^ 2 := by
    have hpos : (0 : ℝ) < ε ^ 2 := by positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hgtend (ε ^ 2) hpos
    have h1 := hN N le_rfl
    rw [Real.dist_eq] at h1
    exact ⟨N, by linarith [(abs_lt.mp h1).1]⟩
  refine ⟨N, fun a ha M hM => ?_⟩
  have hconv : USTendsto (fun K : ℕ => ∑ n ∈ Finset.range K, a * t n) atTop (div a b) :=
    (proto_douglas_1 a b ha t ht).2
  have hzero : Tendsto
      (fun K : ℕ => omegaNorm A ω (div a b - ∑ n ∈ Finset.range K, a * t n))
      atTop (𝓝 0) := by
    refine ((usTendsto_iff _ atTop (div a b)).mp hconv ω).congr fun K => ?_
    rw [← omegaNorm_neg ω (∑ n ∈ Finset.range K, a * t n - div a b)]
    congr 1
    abel
  have hbd : ∀ K : ℕ, M ≤ K →
      omegaNorm A ω (div a b - ∑ n ∈ Finset.range M, a * t n)
        ≤ omegaNorm A ω (div a b - ∑ n ∈ Finset.range K, a * t n)
          + Real.sqrt ((⨆ K, g K) - g M) := by
    intro K hK
    have h1 : omegaNorm A ω (div a b - ∑ n ∈ Finset.range M, a * t n)
        ≤ omegaNorm A ω (div a b - ∑ n ∈ Finset.range K, a * t n)
          + omegaNorm A ω (∑ n ∈ Finset.range K, a * t n
              - ∑ n ∈ Finset.range M, a * t n) := omegaNorm_sub_le ω _ _ _
    have h2 : omegaNorm A ω (∑ n ∈ Finset.range K, a * t n
        - ∑ n ∈ Finset.range M, a * t n) ≤ Real.sqrt (g K - g M) :=
      apinv_block_est ha ht ω hK
    have h3 : Real.sqrt (g K - g M) ≤ Real.sqrt ((⨆ K, g K) - g M) :=
      Real.sqrt_le_sqrt (by linarith [hgL K])
    linarith
  have hfin : omegaNorm A ω (div a b - ∑ n ∈ Finset.range M, a * t n)
      ≤ 0 + Real.sqrt ((⨆ K, g K) - g M) := by
    refine ge_of_tendsto (hzero.add tendsto_const_nhds) ?_
    filter_upwards [eventually_ge_atTop M] with K hK using hbd K hK
  have hsq : Real.sqrt ((⨆ K, g K) - g M) ≤ ε := by
    have hle : (⨆ K, g K) - g M ≤ ε ^ 2 := by linarith [hgmono hM]
    calc Real.sqrt ((⨆ K, g K) - g M) ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hle
      _ = ε := by rw [Real.sqrt_sq hε.le]
  linarith

/-- Auxiliary for **81V** and **81IX**: *an ultrastrong limit of a
norm-bounded net is norm-bounded*.  The closed unit ball is ultrastrongly
closed (**44XI**.3, `vn_positive_basic_3`); rescaling by `(C+ε)⁻¹` — which is
an ultrastrong homeomorphism because `‖λ·x‖_ω = |λ|‖x‖_ω` — transports that to
every radius, and `ε ↓ 0` gives the bound. -/
theorem norm_le_of_usTendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {x : ι → A} {y : A} {C : ℝ} (hconv : USTendsto x l y)
    (hbdd : ∀ᶠ i in l, ‖x i‖ ≤ C) : ‖y‖ ≤ C := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hbdd.exists.choose_spec
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hr0 : (0 : ℝ) < C + ε := by linarith
  set r : ℂ := (((C + ε)⁻¹ : ℝ) : ℂ) with hrdef
  have hrn : ‖r‖ = (C + ε)⁻¹ := by
    rw [hrdef, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hr0.le)]
  -- the rescaled net still converges ultrastrongly
  have hsc : USTendsto (fun i => r • x i) l (r • y) := by
    rw [usTendsto_iff]
    intro ω
    have h0 := (usTendsto_iff x l y).mp hconv ω
    have h1 : Tendsto (fun i => ‖r‖ * omegaNorm A ω (x i - y)) l (𝓝 (‖r‖ * 0)) :=
      h0.const_mul ‖r‖
    rw [mul_zero] at h1
    exact h1.congr fun i => by rw [← smul_sub, omegaNorm_smul]
  -- and it lands in the closed unit ball
  have hmem : ∀ᶠ i in l, r • x i ∈ Metric.closedBall (0 : A) 1 := by
    filter_upwards [hbdd] with i hi
    rw [mem_closedBall_zero_iff, norm_smul, hrn]
    have h2 : (C + ε)⁻¹ * ‖x i‖ ≤ (C + ε)⁻¹ * (C + ε) :=
      mul_le_mul_of_nonneg_left (hi.trans (by linarith)) (inv_nonneg.mpr hr0.le)
    rwa [inv_mul_cancel₀ hr0.ne'] at h2
  let _ : TopologicalSpace A := ultrastrong A
  have hsc' : Tendsto (fun i => r • x i) l
      (@nhds A (ultrastrong A) (r • y)) := hsc
  have hy := vn_positive_basic_3.mem_of_tendsto hsc' hmem
  rw [mem_closedBall_zero_iff, norm_smul, hrn] at hy
  have h3 := mul_le_mul_of_nonneg_left hy hr0.le
  rw [← mul_assoc, mul_inv_cancel₀ hr0.ne', one_mul, mul_one] at h3
  exact h3

/-- Auxiliary for **81V**: the partial sums `∑_{n<N} a tₙ` of **81III** are
contractions when `a*a ≤ b*b`.  Writing `d = ∑_{n<N} tₙ`, one has
`(ad)*(ad) = d*(a*a)d ≤ d*(b*b)d = (bd)*(bd) = ∑_{n<N} b tₙ ≤ 1`, the last
step because that partial sum is a projection. -/
theorem apinv_partialSum_norm_le {a b : A} (h : star a * a ≤ star b * b)
    {t : ℕ → A} (ht : IsApproxPseudoinverse A b t) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, a * t n‖ ≤ 1 := by
  classical
  obtain ⟨hPproj, _, _⟩ :=
    partialSums_of_isLUB (p := fun n => b * t n) ht.proj_right ht.sum_right
      (ceill_basic_2 b).1.1.le_one
  have hsum : ∀ c : A, ∑ n ∈ Finset.range N, c * t n
      = c * ∑ n ∈ Finset.range N, t n := fun c => (Finset.mul_sum _ _ _).symm
  have hest : star (∑ n ∈ Finset.range N, a * t n) * (∑ n ∈ Finset.range N, a * t n)
      ≤ ∑ n ∈ Finset.range N, b * t n := by
    rw [hsum a]
    calc star (a * ∑ n ∈ Finset.range N, t n) * (a * ∑ n ∈ Finset.range N, t n)
        = star (∑ n ∈ Finset.range N, t n) * (star a * a) *
            (∑ n ∈ Finset.range N, t n) := by rw [star_mul]; noncomm_ring
      _ ≤ star (∑ n ∈ Finset.range N, t n) * (star b * b) *
            (∑ n ∈ Finset.range N, t n) := star_left_conjugate_le_conjugate h _
      _ = star (b * ∑ n ∈ Finset.range N, t n) *
            (b * ∑ n ∈ Finset.range N, t n) := by rw [star_mul]; noncomm_ring
      _ = star (∑ n ∈ Finset.range N, b * t n) *
            (∑ n ∈ Finset.range N, b * t n) := by rw [hsum b]
      _ = ∑ n ∈ Finset.range N, b * t n := by
          rw [(hPproj N).isSelfAdjoint.star_eq]; exact (hPproj N).isIdempotentElem.eq
  have hle1 : star (∑ n ∈ Finset.range N, a * t n) * (∑ n ∈ Finset.range N, a * t n)
      ≤ 1 := hest.trans (hPproj N).le_one
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (star_mul_self_nonneg (∑ n ∈ Finset.range N, a * t n))).mpr hle1
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (∑ n ∈ Finset.range N, a * t n)]

/-- Auxiliary for **81V**: `(λ·a)/b = λ·(a/b)` for `a ∈ Ab`. -/
theorem div_smul_left (a b : A) (z : ℂ) (h : ∃ c : A, a = c * b) :
    div (z • a) b = z • div a b := by
  obtain ⟨h1, h2⟩ := div_spec a b h
  exact div_eq (by rw [smul_mul_assoc, ← h1]) (by rw [smul_mul_assoc, h2])

/-- **81V** (`douglas`, vn.tex:5461, Exercise), part 1 (Douglas' lemma):
`a ∈ (A)_λ·b` iff `a*a ≤ λ²b*b`, and then `‖a/b‖ ≤ λ`. -/
theorem douglas_1 (a b : A) (l : ℝ) (hl : 0 ≤ l) :
    ((∃ c : A, ‖c‖ ≤ l ∧ a = c * b) ↔
        star a * a ≤ ((l : ℂ) ^ 2) • (star b * b)) ∧
      (star a * a ≤ ((l : ℂ) ^ 2) • (star b * b) → ‖div a b‖ ≤ l) := by
  classical
  -- bookkeeping for real scalars acting through `ℂ`
  have hRC : ∀ (r : ℝ) (x : A), (r : ℝ) • x = ((r : ℂ)) • x := fun r x => by
    rw [← IsScalarTower.algebraMap_smul ℂ r x, Complex.coe_algebraMap]
  have hmono : ∀ {x y : A}, x ≤ y → ∀ {r : ℝ}, 0 ≤ r →
      ((r : ℂ)) • x ≤ ((r : ℂ)) • y := by
    intro x y h r hr
    rw [← sub_nonneg, ← smul_sub]
    exact ofReal_smul_nonneg (sub_nonneg.mpr h) hr
  have hone : ∀ {r s : ℝ}, r ≤ s → ((r : ℂ)) • (1 : A) ≤ ((s : ℂ)) • (1 : A) := by
    intro r s h
    have h2 := algebraMap_ofReal_mono (𝒜 := A) h
    rwa [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at h2
  have hsq : ∀ (r : ℝ) (x : A), star (((r : ℝ) : ℂ) • x) * (((r : ℝ) : ℂ) • x)
      = ((r * r : ℝ) : ℂ) • (star x * x) := by
    intro r x
    rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
      show star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) from by simp, ← Complex.ofReal_mul]
  have hcast : ((l : ℂ) ^ 2) • (star b * b) = ((l * l : ℝ) : ℂ) • (star b * b) := by
    rw [Complex.ofReal_mul, sq]
  -- (⇒) conjugate `c*c ≤ λ²·1` by `b`
  have hfwd : ∀ c : A, ‖c‖ ≤ l → a = c * b →
      star a * a ≤ ((l : ℂ) ^ 2) • (star b * b) := by
    intro c hc hac
    have h1 : star c * c ≤ ((l * l : ℝ) : ℂ) • (1 : A) := by
      have h2 : star c * c ≤ (‖star c * c‖ : ℝ) • (1 : A) :=
        le_norm_smul_one (star_mul_self_nonneg c)
      rw [hRC, CStarRing.norm_star_mul_self] at h2
      exact h2.trans (hone (by nlinarith [norm_nonneg c]))
    have h3 := star_left_conjugate_le_conjugate h1 b
    rw [hcast]
    calc star a * a = star b * (star c * c) * b := by
          rw [hac, star_mul]; noncomm_ring
      _ ≤ star b * (((l * l : ℝ) : ℂ) • (1 : A)) * b := h3
      _ = ((l * l : ℝ) : ℂ) • (star b * b) := by
          rw [mul_smul_comm, smul_mul_assoc, mul_one]
  -- (⇐) and the norm bound, together
  have hmain : star a * a ≤ ((l : ℂ) ^ 2) • (star b * b) →
      (∃ c : A, a = c * b) ∧ ‖div a b‖ ≤ l := by
    intro hle
    rcases eq_or_lt_of_le hl with hl0 | hl0
    · -- `λ = 0`: then `a*a ≤ 0`, so `a = 0` and `a/b = 0`
      have hz : star a * a ≤ 0 := by
        rw [hcast, ← hl0] at hle
        simpa using hle
      have ha0 : a = 0 := by
        have heq := le_antisymm hz (star_mul_self_nonneg a)
        have hnn : ‖a‖ * ‖a‖ = 0 := by
          rw [← CStarRing.norm_star_mul_self, heq, norm_zero]
        exact norm_eq_zero.mp (by nlinarith [norm_nonneg a])
      refine ⟨⟨0, by rw [ha0, zero_mul]⟩, ?_⟩
      rw [ha0, div_eq (c := 0) (by rw [zero_mul]) (by rw [zero_mul]), norm_zero, ← hl0]
    · -- `λ > 0`: rescale to `a' = λ⁻¹a`, which satisfies `a'*a' ≤ b*b`
      have hlne : (l : ℝ) ≠ 0 := ne_of_gt hl0
      set a' : A := ((l⁻¹ : ℝ) : ℂ) • a with ha'def
      have hle2 : star a * a ≤ ((l * l : ℝ) : ℂ) • (star b * b) := by
        rw [← hcast]; exact hle
      have hle' : star a' * a' ≤ star b * b := by
        rw [ha'def, hsq]
        refine (hmono hle2 (by positivity : (0:ℝ) ≤ l⁻¹ * l⁻¹)).trans (le_of_eq ?_)
        rw [smul_smul, ← Complex.ofReal_mul,
          show (l⁻¹ * l⁻¹) * (l * l) = 1 by field_simp]
        simp
      obtain ⟨t, ht⟩ := approximate_pseudoinverse b
      obtain ⟨⟨c', hc'⟩, hconv⟩ := proto_douglas_1 a' b hle' t ht
      have hex : ∃ c : A, a = c * b := by
        refine ⟨((l : ℝ) : ℂ) • c', ?_⟩
        rw [smul_mul_assoc, ← hc', ha'def, smul_smul, ← Complex.ofReal_mul,
          mul_inv_cancel₀ hlne]
        simp
      refine ⟨hex, ?_⟩
      have hbd : ‖div a' b‖ ≤ 1 :=
        norm_le_of_usTendsto hconv
          (Filter.Eventually.of_forall fun N => apinv_partialSum_norm_le hle' ht N)
      have hda : div a b = ((l : ℝ) : ℂ) • div a' b := by
        rw [ha'def, div_smul_left a b _ hex, smul_smul, ← Complex.ofReal_mul,
          mul_inv_cancel₀ hlne]
        simp
      rw [hda, norm_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
      nlinarith [norm_nonneg (div a' b)]
  refine ⟨⟨fun ⟨c, hc, hac⟩ => hfwd c hc hac, fun hle => ?_⟩, fun hle => (hmain hle).2⟩
  exact ⟨div a b, (hmain hle).2, (div_spec a b (hmain hle).1).1⟩

/-- **81V** (`douglas`, vn.tex:5461, Exercise), part 2: `a ∈ A⌊b⌉` need
not entail `a ∈ Ab` (a counterexample exists, e.g. in `ℓ^∞(ℕ)`). -/
theorem douglas_2 :
    ∃ a b : lp (fun _ : ℕ => ℂ) ∞,
      a * rangeProj b = a ∧ ¬∃ c, a = c * b := by
  -- `b = (1, ½, ⅓, …)` has all coordinates nonzero, so `⌊b⌉ = 1`; but
  -- `⌊b⌉ = cb` would force the unbounded `c = (1, 2, 3, …)`
  have hmem : Memℓp (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ)⁻¹) ∞ := by
    refine memℓp_infty ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    show ‖(((n : ℝ) + 1 : ℝ) : ℂ)⁻¹‖ ≤ 1
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) + 1),
      inv_le_one₀ (by positivity)]
    simp
  set b : lp (fun _ : ℕ => ℂ) ∞ := ⟨fun n => (((n : ℝ) + 1 : ℝ) : ℂ)⁻¹, hmem⟩
    with hbdef
  have hbn : ∀ n : ℕ, b n = (((n : ℝ) + 1 : ℝ) : ℂ)⁻¹ := fun _ => rfl
  have hne : ∀ n : ℕ, (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := fun n =>
    Complex.ofReal_ne_zero.mpr (by positivity : (0:ℝ) < (n : ℝ) + 1).ne'
  refine ⟨rangeProj b, b, (ceill_basic_2 b).1.1.isIdempotentElem.eq, ?_⟩
  rintro ⟨c, hc⟩
  -- `⌊b⌉` is a projection with `⌊b⌉b = b`, so every coordinate of `⌊b⌉` is `1`
  have hp : rangeProj b * b = b := (ceill_basic_2 b).1.2
  have hp1 : ∀ n : ℕ, rangeProj b n = 1 := by
    intro n
    have h : (rangeProj b * b) n = b n := by rw [hp]
    rw [lp.infty_coeFn_mul, Pi.mul_apply, hbn n] at h
    field_simp at h
    exact h
  -- hence `c n = n+1` for every `n`, which is unbounded
  have hcn : ∀ n : ℕ, c n = (((n : ℝ) + 1 : ℝ) : ℂ) := by
    intro n
    have h : rangeProj b n = (c * b) n := by rw [hc]
    rw [lp.infty_coeFn_mul, Pi.mul_apply, hp1 n, hbn n] at h
    field_simp at h
    exact h.symm
  obtain ⟨N, hN⟩ := exists_nat_gt ‖c‖
  have hle := lp.norm_apply_le_norm ENNReal.top_ne_zero c N
  rw [hcn N, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (N : ℝ) + 1)] at hle
  linarith

/-- Auxiliary for **81VI**, the common core of `sequential-douglas`: from
`0 ≤ a ≤ λ·b*b`, Douglas' lemma (**81V**) applied to `√a` — which satisfies
`(√a)*√a = a ≤ (√λ)²·b*b` — produces `c` with `‖c‖ ≤ √λ` and `√a = cb`;
then `a = b*(c*c)b` and `b*∖a/b = ⌊b⌉(c*c)⌊b⌉ = (c⌊b⌉)*(c⌊b⌉)`, which
gives at once the norm bound of part 1 and the positivity of part 2. -/
theorem sequential_douglas_core {a b : A} (ha : 0 ≤ a) {l : ℝ} (hl : 0 ≤ l)
    (hle : a ≤ (l : ℂ) • (star b * b)) :
    ∃ c : A, ‖c‖ ≤ Real.sqrt l ∧ a = star b * (star c * c) * b ∧
      ldiv (star b) (div a b)
        = star (c * rangeProj b) * (c * rangeProj b) := by
  classical
  have hsa : star (CFC.sqrt a) = CFC.sqrt a :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq
  have hq : star (CFC.sqrt a) * CFC.sqrt a = a := by
    rw [hsa, CFC.sqrt_mul_sqrt_self a ha]
  have hm0 : (0 : ℝ) ≤ Real.sqrt l := Real.sqrt_nonneg l
  have hdoug : star (CFC.sqrt a) * CFC.sqrt a
      ≤ (((Real.sqrt l : ℝ) : ℂ) ^ 2) • (star b * b) := by
    rw [hq, ← Complex.ofReal_pow, Real.sq_sqrt hl]
    exact hle
  obtain ⟨c, hc, hcb⟩ := (douglas_1 (CFC.sqrt a) b (Real.sqrt l) hm0).1.2 hdoug
  have he : a = star b * (star c * c) * b := by
    rw [← hq, hcb, star_mul]; noncomm_ring
  refine ⟨c, hc, he, ?_⟩
  -- `b*∖a = ⌈b*⌋(c*c)b`, and dividing that by `b` on the right gives
  -- `⌈b*⌋(c*c)⌊b⌉`; finally `⌈b*⌋ = ⌊b⌉`
  have hsp : IsStarProjection (suppProj (star b)) := (ceill_basic_1 (star b)).1.1
  have hsb : star b * suppProj (star b) = star b := (ceill_basic_1 (star b)).1.2
  have hl1 : ldiv (star b) a = suppProj (star b) * (star c * c) * b := by
    refine ldiv_eq ?_ ?_
    · rw [← mul_assoc, ← mul_assoc, hsb]; exact he
    · rw [← mul_assoc, ← mul_assoc, hsp.isIdempotentElem.eq]
  have hcomm := (division_basic_3 (star b) b a ⟨star c * c, he⟩).2.2.1
  rw [← hcomm, hl1, (division_basic_2 (suppProj (star b) * (star c * c)) b).1,
    suppProj_star, star_mul, (ceill_basic_2 b).1.1.isSelfAdjoint.star_eq]
  noncomm_ring

/-- **81VI** (`sequential-douglas`, vn.tex:5480, Exercise), part 1: for
positive `a` and `λ ≥ 0`: `a ∈ b*(A)_λ b` iff `a ≤ λb*b`, and then
`‖b*∖a/b‖ ≤ λ`. -/
theorem sequential_douglas_1 (a b : A) (ha : 0 ≤ a) (l : ℝ) (hl : 0 ≤ l) :
    ((∃ c : A, ‖c‖ ≤ l ∧ a = star b * c * b) ↔
        a ≤ (l : ℂ) • (star b * b)) ∧
      (a ≤ (l : ℂ) • (star b * b) →
        ‖ldiv (star b) (div a b)‖ ≤ l) := by
  classical
  have hsl : Real.sqrt l * Real.sqrt l = l := Real.mul_self_sqrt hl
  have hrp : ‖rangeProj b‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (ceill_basic_2 b).1.1.nonneg).mpr
      (ceill_basic_2 b).1.1.le_one
  -- (⇒) `a = b*cb = b*sb` with `s = ½(c + c*)` self-adjoint of norm `≤ λ`,
  -- and `s ≤ λ·1`, which conjugates to `a ≤ λ·b*b`
  have hfwd : ∀ c : A, ‖c‖ ≤ l → a = star b * c * b →
      a ≤ (l : ℂ) • (star b * b) := by
    intro c hc hac
    set s : A := ((2⁻¹ : ℝ) : ℂ) • (c + star c) with hsdef
    have hss : IsSelfAdjoint s := by
      rw [hsdef, IsSelfAdjoint, star_smul, star_add, star_star,
        show star (((2⁻¹ : ℝ) : ℂ)) = ((2⁻¹ : ℝ) : ℂ) from by simp, add_comm]
    have hastar : star b * star c * b = a := by
      have h1 : star a = star (star b * c * b) := by rw [hac]
      rw [(IsSelfAdjoint.of_nonneg ha).star_eq, star_mul, star_mul, star_star] at h1
      rw [h1]
      noncomm_ring
    have hsa : star b * s * b = a := by
      rw [hsdef, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, hastar,
        show star b * c * b = a from hac.symm, smul_add, ← add_smul,
        ← Complex.ofReal_add]
      norm_num
    have hns : ‖s‖ ≤ l := by
      rw [hsdef, norm_smul]
      have h2 : ‖c + star c‖ ≤ ‖c‖ + ‖c‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_star]
      have h3 : ‖(((2⁻¹ : ℝ) : ℂ))‖ = 2⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs]; norm_num
      rw [h3]
      nlinarith [norm_nonneg c]
    have hsle : s ≤ ((l : ℂ)) • (1 : A) := by
      have h4 := ((norm_le_iff_neg_algebraMap_le hss hl).mp hns).2
      rwa [Algebra.algebraMap_eq_smul_one] at h4
    have h5 := star_left_conjugate_le_conjugate hsle b
    rw [hsa, mul_smul_comm, smul_mul_assoc, mul_one] at h5
    exact h5
  refine ⟨⟨fun ⟨c, hc, hac⟩ => hfwd c hc hac, fun hle => ?_⟩, fun hle => ?_⟩
  · obtain ⟨c, hc, he, _⟩ := sequential_douglas_core ha hl hle
    refine ⟨star c * c, ?_, he⟩
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg c]
  · obtain ⟨c, hc, _, hd⟩ := sequential_douglas_core ha hl hle
    rw [hd, CStarRing.norm_star_mul_self]
    have h6 : ‖c * rangeProj b‖ ≤ Real.sqrt l :=
      (norm_mul_le _ _).trans (by nlinarith [norm_nonneg c, Real.sqrt_nonneg l])
    nlinarith [norm_nonneg (c * rangeProj b), Real.sqrt_nonneg l]

/-- **81VI** (`sequential-douglas`, vn.tex:5480, Exercise), part 2:
`b*∖a/b` is positive for positive `a ∈ b*Ab`. -/
theorem sequential_douglas_2 (a b : A) (ha : 0 ≤ a)
    (h : ∃ c : A, a = star b * c * b) :
    0 ≤ ldiv (star b) (div a b) := by
  obtain ⟨c, hac⟩ := h
  -- part 1 turns `a ∈ b*Ab` into `a ≤ ‖c‖·b*b`, and the core writes
  -- `b*∖a/b` as `x*x`
  have hle : a ≤ ((‖c‖ : ℝ) : ℂ) • (star b * b) :=
    (sequential_douglas_1 a b ha ‖c‖ (norm_nonneg c)).1.1 ⟨c, le_rfl, hac⟩
  obtain ⟨d, _, _, hd⟩ := sequential_douglas_core ha (norm_nonneg c) hle
  rw [hd]
  exact star_mul_self_nonneg _

/-- **81VII** (`div-approx`, vn.tex:5500, Exercise): for approximate
pseudoinverses `t` of `b` and `s` of `c`, the net
`(∑_{n<N} sₙ) a (∑_{m<N} tₘ)` converges ultrastrongly to `c∖a/b` for
`a ∈ c(A)₁b`. -/
theorem div_approx (a b c : A) (t s : ℕ → A)
    (ht : IsApproxPseudoinverse A b t) (hs : IsApproxPseudoinverse A c s)
    (ha : ∃ d : A, ‖d‖ ≤ 1 ∧ a = c * d * b) :
    USTendsto
      (fun N : ℕ => (∑ n ∈ Finset.range N, s n) * a *
        (∑ m ∈ Finset.range N, t m))
      atTop (ldiv c (div a b)) := by
  classical
  obtain ⟨d, hd, rfl⟩ := ha
  obtain ⟨hQproj, _, hQtend⟩ :=
    partialSums_of_isLUB (p := fun n => s n * c) hs.proj_left hs.sum_left
      (ceill_basic_1 c).1.1.le_one
  obtain ⟨hPproj, _, hPtend⟩ :=
    partialSums_of_isLUB (p := fun n => b * t n) ht.proj_right ht.sum_right
      (ceill_basic_2 b).1.1.le_one
  -- `c∖(cdb)/b = ⌈c⌋d⌊b⌉`, by the explicit formulas of **81II**
  have hsp : IsStarProjection (suppProj c) := (ceill_basic_1 c).1.1
  have hsc : c * suppProj c = c := (ceill_basic_1 c).1.2
  have hl1 : ldiv c (c * d * b) = suppProj c * d * b :=
    ldiv_eq (by rw [← mul_assoc, ← mul_assoc, hsc])
      (by rw [← mul_assoc, ← mul_assoc, hsp.isIdempotentElem.eq])
  have hlim : ldiv c (div (c * d * b) b) = suppProj c * d * rangeProj b := by
    rw [← (division_basic_3 c b (c * d * b) ⟨d, rfl⟩).2.2.1, hl1,
      (division_basic_2 (suppProj c * d) b).1]
  rw [hlim]
  -- the net *is* `Q_N d P_N`
  have hnet : ∀ N : ℕ, (∑ n ∈ Finset.range N, s n) * (c * d * b) *
      (∑ m ∈ Finset.range N, t m)
      = (∑ n ∈ Finset.range N, s n * c) * d * (∑ n ∈ Finset.range N, b * t n) := by
    intro N
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    noncomm_ring
  -- the two "one-sided" limits, which are ultrastrongly continuous
  have hy : USTendsto
      (fun N : ℕ => (∑ n ∈ Finset.range N, s n * c) * (d * rangeProj b))
      atTop (suppProj c * (d * rangeProj b)) := by
    simpa using usTendsto_mul_left_right (1 : A) (d * rangeProj b) hQtend
  have hz : USTendsto
      (fun N : ℕ => suppProj c * d * (∑ n ∈ Finset.range N, b * t n))
      atTop (suppProj c * d * rangeProj b) := by
    simpa using usTendsto_mul_left_right (suppProj c * d) (1 : A) hPtend
  rw [usTendsto_iff]
  intro ω
  have hP0 := (usTendsto_iff _ atTop (rangeProj b)).mp hPtend ω
  have hy0 := (usTendsto_iff _ atTop (suppProj c * (d * rangeProj b))).mp hy ω
  have hz0 := (usTendsto_iff _ atTop (suppProj c * d * rangeProj b)).mp hz ω
  -- the three-term decomposition
  have hdecomp : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, s n) * (c * d * b) * (∑ m ∈ Finset.range N, t m)
        - suppProj c * d * rangeProj b
      = (((∑ n ∈ Finset.range N, s n * c) - suppProj c) * d) *
          ((∑ n ∈ Finset.range N, b * t n) - rangeProj b)
        + ((∑ n ∈ Finset.range N, s n * c) * (d * rangeProj b)
            - suppProj c * (d * rangeProj b))
        + (suppProj c * d * (∑ n ∈ Finset.range N, b * t n)
            - suppProj c * d * rangeProj b) := by
    intro N
    rw [hnet N]
    noncomm_ring
  -- bound the first term by `2‖P_N − ⌊b⌉‖_ω`
  have hbd : ∀ N : ℕ, ‖((∑ n ∈ Finset.range N, s n * c) - suppProj c) * d‖ ≤ 2 := by
    intro N
    have h1 : ‖∑ n ∈ Finset.range N, s n * c‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hQproj N).nonneg).mpr
        (hQproj N).le_one
    have h2 : ‖suppProj c‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ hsp.nonneg).mpr hsp.le_one
    calc ‖((∑ n ∈ Finset.range N, s n * c) - suppProj c) * d‖
        ≤ ‖(∑ n ∈ Finset.range N, s n * c) - suppProj c‖ * ‖d‖ := norm_mul_le _ _
      _ ≤ 2 * 1 := by
          have := norm_sub_le (∑ n ∈ Finset.range N, s n * c) (suppProj c)
          have h3 : (0:ℝ) ≤ ‖(∑ n ∈ Finset.range N, s n * c) - suppProj c‖ :=
            norm_nonneg _
          nlinarith [norm_nonneg d]
      _ = 2 := by ring
  refine squeeze_zero (g := fun N : ℕ =>
      2 * omegaNorm A ω ((∑ n ∈ Finset.range N, b * t n) - rangeProj b)
        + omegaNorm A ω ((∑ n ∈ Finset.range N, s n * c) * (d * rangeProj b)
            - suppProj c * (d * rangeProj b))
        + omegaNorm A ω (suppProj c * d * (∑ n ∈ Finset.range N, b * t n)
            - suppProj c * d * rangeProj b))
    (fun N => omegaNorm_nonneg _ _) (fun N => ?_) ?_
  · rw [hdecomp N]
    refine (omegaNorm_add_le ω _ _).trans (add_le_add ((omegaNorm_add_le ω _ _).trans
      (add_le_add ?_ le_rfl)) le_rfl)
    exact (omegaNorm_mul_le ω _ _).trans
      (mul_le_mul_of_nonneg_right (hbd N) (omegaNorm_nonneg _ _))
  · have h1 : Tendsto (fun N : ℕ =>
        2 * omegaNorm A ω ((∑ n ∈ Finset.range N, b * t n) - rangeProj b)
          + omegaNorm A ω ((∑ n ∈ Finset.range N, s n * c) * (d * rangeProj b)
              - suppProj c * (d * rangeProj b))
          + omegaNorm A ω (suppProj c * d * (∑ n ∈ Finset.range N, b * t n)
              - suppProj c * d * rangeProj b)) atTop (𝓝 (2 * 0 + 0 + 0)) :=
      ((hP0.const_mul 2).add hy0).add hz0
    simpa using h1

/-- Auxiliary for **81VI**/**81VIII**: `b*∖a/b` really is a witness, i.e.
`a = b*(b*∖a/b)b` for `a ∈ b*Ab`.  (The explicit description
`b*∖a/b = ⌈b*⌋d⌊b⌉` of **81II**.3, with `⌈b*⌋` absorbed by `b*` on the left
and `⌊b⌉` by `b` on the right.) -/
theorem ldiv_div_recover {a b : A} (h : ∃ d : A, a = star b * d * b) :
    a = star b * ldiv (star b) (div a b) * b := by
  obtain ⟨d, hd⟩ := h
  have hsp : IsStarProjection (suppProj (star b)) := (ceill_basic_1 (star b)).1.1
  have hsb : star b * suppProj (star b) = star b := (ceill_basic_1 (star b)).1.2
  have hrb : rangeProj b * b = b := (ceill_basic_2 b).1.2
  have hl1 : ldiv (star b) a = suppProj (star b) * d * b :=
    ldiv_eq (by rw [← mul_assoc, ← mul_assoc, hsb]; exact hd)
      (by rw [← mul_assoc, ← mul_assoc, hsp.isIdempotentElem.eq])
  rw [← (division_basic_3 (star b) b a ⟨d, hd⟩).2.2.1, hl1,
    (division_basic_2 (suppProj (star b) * d) b).1]
  calc a = star b * d * b := hd
    _ = (star b * suppProj (star b)) * d * (rangeProj b * b) := by rw [hsb, hrb]
    _ = star b * (suppProj (star b) * d * rangeProj b) * b := by noncomm_ring

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
/-- Auxiliary: membership of the corner `pAq` splits into its two halves. -/
private theorem corner_two_sided {p q x : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : p * x * q = x) :
    p * x = x ∧ x * q = x := by
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have hqq : q * q = q := hq.isIdempotentElem.eq
  constructor
  · calc p * x = p * (p * x * q) := by rw [h]
      _ = (p * p) * x * q := by noncomm_ring
      _ = p * x * q := by rw [hpp]
      _ = x := h
  · calc x * q = (p * x * q) * q := by rw [h]
      _ = p * x * (q * q) := by noncomm_ring
      _ = p * x * q := by rw [hqq]
      _ = x := h

/-- **81II** (`division-basic`) in the form used for 81IX: for `x` in the
corner `⌈c⌋A⌊b⌉` one has `c∖(cxb)/b = x`.  Both steps are the explicit
characterisations of division: `(cxb)/b = cx` because `x⌊b⌉ = x`, and
`c∖(cx) = x` because `⌈c⌋x = x`. -/
theorem ldiv_div_corner {b c x : A} (h : suppProj c * x * rangeProj b = x) :
    ldiv c (div (c * x * b) b) = x := by
  obtain ⟨h1, h2⟩ := corner_two_sided (ceill_basic_1 c).1.1 (ceill_basic_2 b).1.1 h
  have hd : div (c * x * b) b = c * x := div_eq rfl (by rw [mul_assoc, h2])
  rw [hd]
  exact ldiv_eq rfl h1

/-- The explicit value of `c∖a/b` on `c(A)b`: for `a = cdb` it is
`⌈c⌋d⌊b⌉`.  In particular `‖c∖a/b‖ ≤ ‖d‖`, which is the norm bound
**81VI**.1 supplies in general — here it is immediate, because the corner
projections are contractions. -/
theorem ldiv_div_ball (b c d : A) :
    ldiv c (div (c * d * b) b) = suppProj c * d * rangeProj b := by
  have hp : IsStarProjection (suppProj c) := (ceill_basic_1 c).1.1
  have hq : IsStarProjection (rangeProj b) := (ceill_basic_2 b).1.1
  have hc : c * suppProj c = c := (ceill_basic_1 c).1.2
  have hb : rangeProj b * b = b := (ceill_basic_2 b).1.2
  have key : c * (suppProj c * d * rangeProj b) * b = c * d * b := by
    calc c * (suppProj c * d * rangeProj b) * b
        = (c * suppProj c) * d * (rangeProj b * b) := by noncomm_ring
      _ = c * d * b := by rw [hc, hb]
  rw [← key]
  refine ldiv_div_corner ?_
  calc suppProj c * (suppProj c * d * rangeProj b) * rangeProj b
      = (suppProj c * suppProj c) * d * (rangeProj b * rangeProj b) := by noncomm_ring
    _ = suppProj c * d * rangeProj b := by
        rw [hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]

/-- **81VIII** (`sequential-quotient`, vn.tex:5513, Exercise), part 1: for
positive `a`, `b`: `a ≤ λb` for some `λ ≥ 0` iff `a = √b c √b` for some
positive `c`. -/
theorem sequential_quotient_1 (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∃ l : ℝ, 0 ≤ l ∧ a ≤ (l : ℂ) • b) ↔
      ∃ c : A, 0 ≤ c ∧ a = CFC.sqrt b * c * CFC.sqrt b := by
  have hsq : star (CFC.sqrt b) = CFC.sqrt b :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq
  have hbb : star (CFC.sqrt b) * CFC.sqrt b = b := by
    rw [hsq, CFC.sqrt_mul_sqrt_self b hb]
  constructor
  · rintro ⟨l, hl, hle⟩
    -- **81VI** applied to `√b`: the witness is `√b∖a/√b`, positive by 81VI.2
    rw [← hbb] at hle
    obtain ⟨c, _, he, _⟩ := sequential_douglas_core ha hl hle
    refine ⟨ldiv (star (CFC.sqrt b)) (div a (CFC.sqrt b)), ?_, ?_⟩
    · exact sequential_douglas_2 a (CFC.sqrt b) ha ⟨star c * c, he⟩
    · conv_lhs => rw [ldiv_div_recover ⟨star c * c, he⟩]
      rw [hsq]
  · rintro ⟨c, hc, hac⟩
    -- conversely `√b c √b ≤ ‖c‖·√b√b = ‖c‖·b`
    refine ⟨‖c‖, norm_nonneg c, ?_⟩
    have h1 : c ≤ ((‖c‖ : ℝ) : ℂ) • (1 : A) := by
      have h2 : c ≤ (‖c‖ : ℝ) • (1 : A) := le_norm_smul_one hc
      rwa [← IsScalarTower.algebraMap_smul ℂ (‖c‖ : ℝ) (1 : A),
        Complex.coe_algebraMap] at h2
    have h3 := star_left_conjugate_le_conjugate h1 (CFC.sqrt b)
    rw [hsq, mul_smul_comm, smul_mul_assoc, mul_one,
      CFC.sqrt_mul_sqrt_self b hb] at h3
    rw [hac]
    exact h3

/-- **81VIII** (`sequential-quotient`, vn.tex:5513, Exercise), part 2: in
that case there is a *unique* positive `c` with `a = √b c √b` and
`⌈c⌉ ≤ ⌈b⌉`; and for an approximate pseudoinverse `t` of `√b` the double
series `∑_{m,n} tₘ a tₙ` converges ultraweakly to this `c`.

The two claims are stated **separately**, as the thesis makes them.  Folding
the convergence into the `∃!` would make the uniqueness *vacuous* — an
ultraweak limit is unique anyway (the
ultraweak topology is Hausdorff), so the `∃!` would say nothing about the
three properties, which is precisely what the point asserts.

The witness is `c = √b∖a/√b`, positive by **81VI**.2 and a genuine witness
by `ldiv_div_recover`; it lies in the corner `⌈b⌉A⌈b⌉` (because
`⌈(√b)*⌋ = ⌊√b⌉ = ⌈b⌉`), which is exactly `⌈c⌉ ≤ ⌈b⌉` by **59III**.1, and
that same corner condition makes the *uniqueness* an instance of
`ldiv_div_corner`.

**Divergence (a strengthening).**  The double series is
`(∑_{m<N}tₘ√b) c (∑_{n<N}√b tₙ) = Q_N c P_N` with `Q_N, P_N` projections
increasing to `⌈b⌉` (**80III**), and
`Q_N c P_N − c = (Q_N c)(P_N − ⌈b⌉) + (Q_N − ⌈b⌉)(c⌈b⌉)`; the first term is
`‖·‖_ω`-bounded by `‖c‖‖P_N − ⌈b⌉‖_ω` and the second is
`‖Q_N − ⌈b⌉‖_{(c⌈b⌉)*ω(c⌈b⌉)}`, so both vanish.  That proves convergence in
the *ultrastrong* topology, which is strictly finer; the thesis's ultraweak
claim follows by **43I**.2.  (This does not conflict with the falsity of the
second half of **81IX**: here `a` is fixed, and it is only uniformity in `a`
that fails — cf. `div_approx`.) -/
theorem sequential_quotient_2 (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (l : ℝ) (hl : 0 ≤ l) (hab : a ≤ (l : ℂ) • b) (t : ℕ → A)
    (ht : IsApproxPseudoinverse A (CFC.sqrt b) t) :
    (∃! c : A, 0 ≤ c ∧ a = CFC.sqrt b * c * CFC.sqrt b ∧ ceil c ≤ ceil b) ∧
      ∀ c : A, (0 ≤ c ∧ a = CFC.sqrt b * c * CFC.sqrt b ∧ ceil c ≤ ceil b) →
        UWTendsto
          (fun N : ℕ => ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
            t m * a * t n) atTop c := by
  classical
  set s : A := CFC.sqrt b with hsdef
  have hsnn : (0 : A) ≤ s := CFC.sqrt_nonneg b
  have hs : star s = s := (IsSelfAdjoint.of_nonneg hsnn).star_eq
  have hss : s * s = b := CFC.sqrt_mul_sqrt_self b hb
  have hqb : IsStarProjection (ceil b) := (ceil_spec hb).1
  have hsupp : suppProj s = ceil b := by rw [suppProj, hs, hss]
  have hrange : rangeProj s = ceil b := by rw [rangeProj, hs, hss]
  -- `a ∈ s A s`
  have hex : ∃ d : A, a = star s * d * s := by
    obtain ⟨d₀, _, had₀⟩ := (sequential_quotient_1 a b ha hb).mp ⟨l, hl, hab⟩
    exact ⟨d₀, by rw [hs]; exact had₀⟩
  set c₀ : A := ldiv (star s) (div a s) with hcdef
  have hcpos : (0 : A) ≤ c₀ := sequential_douglas_2 a s ha hex
  have hrec : a = s * c₀ * s := by
    have h : a = star s * c₀ * s := ldiv_div_recover hex
    rwa [hs] at h
  -- `c₀` lies in the corner `⌈b⌉A⌈b⌉`
  have hcorner : ceil b * c₀ * ceil b = c₀ := by
    obtain ⟨d, hd⟩ := hex
    have h := ldiv_div_ball s (star s) d
    rw [← hd] at h
    rw [hcdef, h, suppProj_star, hrange]
    calc ceil b * (ceil b * d * ceil b) * ceil b
        = (ceil b * ceil b) * d * (ceil b * ceil b) := by noncomm_ring
      _ = ceil b * d * ceil b := by rw [hqb.isIdempotentElem.eq]
  have hqc : ceil b * c₀ = c₀ := by
    calc ceil b * c₀ = ceil b * (ceil b * c₀ * ceil b) := by rw [hcorner]
      _ = (ceil b * ceil b) * c₀ * ceil b := by noncomm_ring
      _ = ceil b * c₀ * ceil b := by rw [hqb.isIdempotentElem.eq]
      _ = c₀ := hcorner
  have hceil : ceil c₀ ≤ ceil b := ((ceil_basic_1 c₀ (ceil b) hcpos hqb).out 0 2).mp hqc
  -- the partial sums
  obtain ⟨hQproj, _, hQtend⟩ :=
    partialSums_of_isLUB (p := fun n => t n * s) ht.proj_left ht.sum_left
      (ceill_basic_1 s).1.1.le_one
  obtain ⟨_, _, hPtend⟩ :=
    partialSums_of_isLUB (p := fun n => s * t n) ht.proj_right ht.sum_right
      (ceill_basic_2 s).1.1.le_one
  rw [hsupp] at hQtend
  rw [hrange] at hPtend
  -- the double series *is* `Q_N c₀ P_N`
  have hnet : ∀ N : ℕ, (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, t m * a * t n)
      = (∑ n ∈ Finset.range N, t n * s) * c₀ * (∑ n ∈ Finset.range N, s * t n) := by
    intro N
    have hQ : (∑ n ∈ Finset.range N, t n) * s = ∑ n ∈ Finset.range N, t n * s :=
      Finset.sum_mul _ _ _
    have hP : s * (∑ n ∈ Finset.range N, t n) = ∑ n ∈ Finset.range N, s * t n :=
      Finset.mul_sum _ _ _
    calc (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, t m * a * t n)
        = (∑ m ∈ Finset.range N, t m) * a * (∑ n ∈ Finset.range N, t n) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_comm
      _ = ((∑ n ∈ Finset.range N, t n) * s) * c₀ * (s * (∑ n ∈ Finset.range N, t n)) := by
          rw [hrec]; noncomm_ring
      _ = _ := by rw [hQ, hP]
  -- ultrastrong (hence ultraweak) convergence
  have hUS : USTendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, t n * s) * c₀ * (∑ n ∈ Finset.range N, s * t n))
      atTop c₀ := by
    rw [usTendsto_iff]
    intro ω
    have hdecomp : ∀ N : ℕ,
        (∑ n ∈ Finset.range N, t n * s) * c₀ * (∑ n ∈ Finset.range N, s * t n) - c₀
        = ((∑ n ∈ Finset.range N, t n * s) * c₀) *
            ((∑ n ∈ Finset.range N, s * t n) - ceil b)
          + ((∑ n ∈ Finset.range N, t n * s) - ceil b) * (c₀ * ceil b) := by
      intro N
      have hr : ((∑ n ∈ Finset.range N, t n * s) * c₀) *
            ((∑ n ∈ Finset.range N, s * t n) - ceil b)
          + ((∑ n ∈ Finset.range N, t n * s) - ceil b) * (c₀ * ceil b)
          = (∑ n ∈ Finset.range N, t n * s) * c₀ * (∑ n ∈ Finset.range N, s * t n)
            - ceil b * c₀ * ceil b := by noncomm_ring
      rw [hr, hcorner]
    have hbound : ∀ N : ℕ, omegaNorm A ω
        ((∑ n ∈ Finset.range N, t n * s) * c₀ * (∑ n ∈ Finset.range N, s * t n) - c₀)
        ≤ ‖c₀‖ * omegaNorm A ω ((∑ n ∈ Finset.range N, s * t n) - ceil b)
          + omegaNorm A (conjNP (c₀ * ceil b) ω)
              ((∑ n ∈ Finset.range N, t n * s) - ceil b) := by
      intro N
      rw [hdecomp N]
      refine (omegaNorm_add_le ω _ _).trans (add_le_add ?_ ?_)
      · refine (omegaNorm_mul_le ω _ _).trans
          (mul_le_mul_of_nonneg_right ?_ (omegaNorm_nonneg _ _))
        calc ‖(∑ n ∈ Finset.range N, t n * s) * c₀‖
            ≤ ‖∑ n ∈ Finset.range N, t n * s‖ * ‖c₀‖ := norm_mul_le _ _
          _ ≤ 1 * ‖c₀‖ := by
              gcongr
              exact IsStarProjection.norm_le _ (hQproj N)
          _ = ‖c₀‖ := one_mul _
      · rw [omegaNorm_mul_right]
    refine squeeze_zero (fun N => omegaNorm_nonneg _ _) hbound ?_
    have h1 := (usTendsto_iff _ atTop (ceil b)).mp hPtend ω
    have h2 := (usTendsto_iff _ atTop (ceil b)).mp hQtend (conjNP (c₀ * ceil b) ω)
    simpa using (h1.const_mul ‖c₀‖).add h2
  have hUW : UWTendsto (fun N : ℕ => ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      t m * a * t n) atTop c₀ := by
    have := uwweaker_2 _ atTop c₀ hUS
    simpa only [hnet] using this
  -- uniqueness among the three properties alone
  have huniq : ∀ y : A, (0 ≤ y ∧ a = CFC.sqrt b * y * CFC.sqrt b ∧
      ceil y ≤ ceil b) → y = c₀ := by
    rintro y ⟨hy0, hys, hyc⟩
    have hqy : ceil b * y = y := ((ceil_basic_1 y (ceil b) hy0 hqb).out 2 0).mp hyc
    have hyq : y * ceil b = y := ((ceil_basic_1 y (ceil b) hy0 hqb).out 2 1).mp hyc
    have hcor : suppProj (star s) * y * rangeProj s = y := by
      rw [suppProj_star, hrange, hqy, hyq]
    have h : ldiv (star s) (div (star s * y * s) s) = y := ldiv_div_corner hcor
    have hsy : star s * y * s = a := by rw [hs, ← hys]
    rw [hsy] at h
    rw [hcdef]
    exact h.symm
  exact ⟨⟨c₀, ⟨hcpos, hrec, hceil⟩, huniq⟩, fun y hy => by rw [huniq y hy]; exact hUW⟩


/-- **81IX** (`div-usc`, vn.tex:5533, Lemma), **first half**: `a ↦ a/b` is
ultrastrongly continuous on `(A)₁b`.  This is the thesis's own argument
(vn.tex:5541): by **81III**.2 the partial sums `a ↦ ∑_{n<N} a tₙ` converge to
`a/b` *uniformly* on `(A)₁b` (in each seminorm `‖·‖_ω` separately, which is
all that is needed), and each partial sum is `a ↦ a·(∑_{n<N} tₙ)`, which is
ultrastrongly continuous because `‖yd‖_ω = ‖y‖_{d*ωd}` (**44VIII**).

This is the *first* clause of 81IX as corrected; the clause's
companion, ultraweak continuity of the same map, is the first conjunct of
`div_uwc` below.  The printed *second* half — ultrastrong continuity of
`a ↦ c∖a/b` on `c(A)₁b` — is **false**; see the note below. -/
theorem div_usc_ball (b : A) :
    @ContinuousOn A A (ultrastrong A) (ultrastrong A) (fun a => div a b)
      {a : A | ∃ d : A, ‖d‖ ≤ 1 ∧ a = d * b} := by
  classical
  set S : Set A := {a : A | ∃ d : A, ‖d‖ ≤ 1 ∧ a = d * b} with hSdef
  obtain ⟨t, ht⟩ := approximate_pseudoinverse b
  -- membership in `(A)₁b` is exactly Douglas' hypothesis with `λ = 1`
  have hdoug : ∀ a ∈ S, star a * a ≤ star b * b := by
    rintro a ⟨d, hd, rfl⟩
    have h := (douglas_1 (d * b) b 1 zero_le_one).1.1 ⟨d, hd, rfl⟩
    simpa using h
  intro a₀ ha₀
  have hkey : USTendsto (fun a => div a b)
      (@nhdsWithin A (ultrastrong A) a₀ S) (div a₀ b) := by
    rw [usTendsto_iff]
    intro ω
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    have hε3 : (0 : ℝ) < ε / 3 := by linarith
    obtain ⟨N, hN⟩ := proto_douglas_2 b t ht ω (ε / 3) hε3
    set d : A := ∑ n ∈ Finset.range N, t n with hddef
    have hsum : ∀ x : A, ∑ n ∈ Finset.range N, x * t n = x * d :=
      fun x => (Finset.mul_sum _ _ _).symm
    have hball : {a : A | omegaNorm A (conjNP d ω) (a - a₀) < ε / 3}
        ∈ @nhds A (ultrastrong A) a₀ := ultrastrong_ball_mem_nhds _ a₀ hε3
    have hSW : S ∈ @nhdsWithin A (ultrastrong A) a₀ S :=
      @self_mem_nhdsWithin A (ultrastrong A) a₀ S
    have hballW : {a : A | omegaNorm A (conjNP d ω) (a - a₀) < ε / 3}
        ∈ @nhdsWithin A (ultrastrong A) a₀ S :=
      @mem_nhdsWithin_of_mem_nhds A (ultrastrong A) _ _ _ hball
    filter_upwards [hSW, hballW] with a haS haB
    have h1 : omegaNorm A ω (div a b - a * d) ≤ ε / 3 := by
      have := hN a (hdoug a haS) N le_rfl
      rwa [hsum a] at this
    have h3 : omegaNorm A ω (a₀ * d - div a₀ b) ≤ ε / 3 := by
      have := hN a₀ (hdoug a₀ ha₀) N le_rfl
      rwa [hsum a₀, ← omegaNorm_neg ω (div a₀ b - a₀ * d), neg_sub] at this
    have h2 : omegaNorm A ω (a * d - a₀ * d) < ε / 3 := by
      rw [← sub_mul, omegaNorm_mul_right]
      exact haB
    have hstep : omegaNorm A ω (div a b - div a₀ b)
        ≤ omegaNorm A ω (div a b - a * d) + omegaNorm A ω (a * d - div a₀ b) :=
      omegaNorm_sub_le ω _ _ _
    have hstep' : omegaNorm A ω (a * d - div a₀ b)
        ≤ omegaNorm A ω (a * d - a₀ * d) + omegaNorm A ω (a₀ * d - div a₀ b) :=
      omegaNorm_sub_le ω _ _ _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (omegaNorm_nonneg ω _)]
    linarith
  exact hkey

/-! ### The printed 81IX, and why its second half was weakened

The printed **81IX** (`div-usc`, vn.tex:5533) claimed that *both*
`a ↦ a/b : (A)₁b → A` and `a ↦ c∖a/b : c(A)₁b → A` are ultrastrongly
continuous.  The first conjunct is true and is `div_usc_ball` above; the
second is **false**, so the printed statement is not transcribed.  The
author's ruling of 2026-08-17 (see HANDOFF.md) weakens the second map to
ultraweak continuity — that is `div_uwc` below — and leaves the first map
with both continuities; vn.tex carries the counterexample itself, as
sub-point **81XII** (not converted).  (**81XI**, Remark: continuity
also fails on the larger domain `Ab` — not converted.)

Counterexample to the printed second conjunct, with
`b = 1`, so that `a ↦ c∖a/b` is `a ↦ c∖a` on `c(A)₁`: in `A = B(ℓ²)` take
`c = diag(1, ½, ⅓, …)`, which is positive and injective, so `⌈c⌋ = 1` and
`c∖(cd) = d`.  Put `dₙ = |n⟩⟨0|`, so `‖dₙ‖ = 1` and `cdₙ = (n+1)⁻¹|n⟩⟨0| → 0`
*in norm*, hence ultrastrongly; but `c∖(cdₙ) = dₙ` and `‖dₙ‖_ω = ‖dₙ|0⟩‖ = 1`
for the vector state `ω` at `|0⟩`, so `(dₙ)ₙ` does not converge ultrastrongly
to `0 = c∖0`.  Continuity implies sequential continuity, so `c∖(·)` is not
ultrastrongly continuous on `c(A)₁`.  The thesis's proof factors the map as
`c(A)₁b → c(A)₁ → A` and asserts the second factor is ultrastrongly
continuous "as follows"; it is not — left division is ultrastrongly
continuous only in the commutative case (there `‖e‖ ≤ 2` really does bound
`‖e‖_ω` by `c_K⁻¹‖ce‖_ω + 4ε`), and in general only for the ultrastrong-*
topology.  Its repaired proof in vn.tex takes neither route: it uses
`c∖x = (x*/c*)*` (**81II**(5)) together with ultraweak — as against
ultrastrong (**43II**.4) — continuity of the adjoint.
-/

/-! ### 81IX in the ultraweak topology

The counterexample that refutes the second conjunct of **81IX** does not
touch its ultraweak analogue (there `‖dₙ‖_ω = 1` for a *fixed* vector state,
while `ω(dₙ) = ⟨0|ρ|n⟩ → 0` for every trace-class `ρ`), and in fact the
ultraweak statement is **true** for both maps — see `div_uwc`.

This is the thesis's own repaired proof (vn.tex:5546), in both halves.

*First map.*  `div_uwc_ball` runs vn.tex:5547 verbatim in the ultraweak
topology: by **81V**.2 (`proto_douglas_2`) the partial sums `a ↦ ∑_{n<N} a tₙ`
converge to `a/b` uniformly on `(A)₁b` in each `‖·‖_ω`, hence — by
Cauchy–Schwarz `|ω(x)| ≤ ‖x‖_ω ω(1)^½` (**43I**.1
`norm_apply_le_omegaNorm`) — uniformly in each `|ω(·)|`; each partial sum
`a ↦ a·(∑_{n<N} tₙ)` is ultraweakly continuous by **45IV**
(`mult_uws_cont`); and a uniform limit of continuous functions is
continuous.  `div_uwc_ball_of_norm_le` is the same statement on `(A)_λ b`,
which is what the second half needs; it comes out of the same estimate,
rescaled by `λ+1`.

*Second map.*  `div_uwc_corner` is vn.tex:5563 verbatim: `c∖x = (x*/c*)*`
for `x ∈ c(A)₁` — that is **81II**.5 `division_basic_5` — so `c∖(·)` is
ultraweakly continuous, the adjoint being so (`continuous_ultraweak_star`,
the positive half of **43II**.4, whose negative half
`vn_counterexamples_4_star` is exactly why the printed *ultrastrong* claim
cannot be repaired this way); and `(·)/b` maps `c(A)₁b` into `c(A)₁`, so
the composite `c∖·/b` is ultraweakly continuous too. -/

omit [VonNeumannAlgebra A] in
/-- The adjoint is **ultraweakly** continuous: `ω(a*) = conj ω(a)` for every
np-functional, and conjugation is continuous on `ℂ`.  This is the positive
half of **43II**.4, whose negative half — `vn_counterexamples_4_star`, the
adjoint is *not* ultrastrongly continuous — is exactly what stops the
printed ultrastrong form of 81IX's second map from being repairable along
the same lines. -/
theorem continuous_ultraweak_star :
    @Continuous A A (ultraweak A) (ultraweak A) (fun a : A => star a) := by
  refine continuous_ultraweak_of_forall _ fun ω => ?_
  have hform : ∀ a : A, (ω (star a) : ℂ) = star (ω a) := fun a => npFunctional_star ω a
  simp only [hform]
  exact @Continuous.comp A ℂ ℂ (ultraweak A) _ _ _ _ continuous_star
    (continuous_ultraweak_npFunctional ω)

/-- **81IX** (`div-usc`, vn.tex:5533, Lemma), first map, **ultraweakly**, on
the ball of radius `λ`: `a ↦ a/b` is ultraweakly continuous on `(A)_λ b`.

This is the thesis's proof (vn.tex:5547) with `λ` carried along, because the
second half of 81IX applies the first map on `c(A)₁b ⊆ (A)_‖c‖ b`.  The
uniform estimate of **81V**.2 (`proto_douglas_2`) is stated for
`a*a ≤ b*b`; here it is applied to `(λ+1)⁻¹·a`, which lies in `(A)₁b`, and
scaled back by `div_smul_left`. -/
theorem div_uwc_ball_of_norm_le (b : A) (l : ℝ) (hl : 0 ≤ l) :
    @ContinuousOn A A (ultraweak A) (ultraweak A) (fun a => div a b)
      {a : A | ∃ d : A, ‖d‖ ≤ l ∧ a = d * b} := by
  classical
  set S : Set A := {a : A | ∃ d : A, ‖d‖ ≤ l ∧ a = d * b} with hSdef
  obtain ⟨t, ht⟩ := approximate_pseudoinverse b
  set L : ℝ := l + 1 with hLdef
  have hL : 0 < L := by rw [hLdef]; linarith
  -- the partial sums converge to `a/b` uniformly on `(A)_λ b` in each `‖·‖_ω`
  have hunif : ∀ (ω : NPFunctional A) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ a ∈ S,
      omegaNorm A ω (div a b - ∑ n ∈ Finset.range N, a * t n) ≤ ε := by
    intro ω ε hε
    obtain ⟨N, hN⟩ := proto_douglas_2 b t ht ω (ε / L) (by positivity)
    refine ⟨N, ?_⟩
    rintro a ⟨d, hd, rfl⟩
    have hnorm : ‖((L : ℂ))⁻¹ • d‖ ≤ 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
      rw [inv_mul_le_iff₀ hL, hLdef]
      linarith
    have hmem : star (((L : ℂ))⁻¹ • (d * b)) * (((L : ℂ))⁻¹ • (d * b)) ≤ star b * b := by
      have h := (douglas_1 (((L : ℂ))⁻¹ • (d * b)) b 1 zero_le_one).1.1
        ⟨((L : ℂ))⁻¹ • d, hnorm, by rw [smul_mul_assoc]⟩
      simpa using h
    have hsm := hN (((L : ℂ))⁻¹ • (d * b)) hmem N le_rfl
    have hdiv : div (((L : ℂ))⁻¹ • (d * b)) b = ((L : ℂ))⁻¹ • div (d * b) b :=
      div_smul_left (d * b) b _ ⟨d, rfl⟩
    have hsum : (∑ n ∈ Finset.range N, ((L : ℂ))⁻¹ • (d * b) * t n)
        = ((L : ℂ))⁻¹ • ∑ n ∈ Finset.range N, (d * b) * t n := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun n _ => by rw [smul_mul_assoc]
    rw [hdiv, hsum, ← smul_sub, omegaNorm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hL] at hsm
    rw [inv_mul_le_iff₀ hL] at hsm
    calc omegaNorm A ω (div (d * b) b - ∑ n ∈ Finset.range N, (d * b) * t n)
        ≤ L * (ε / L) := hsm
      _ = ε := by field_simp
  intro a₀ ha₀
  have hkey : UWTendsto (fun a => div a b) (@nhdsWithin A (ultraweak A) a₀ S)
      (div a₀ b) := by
    rw [uwTendsto_iff]
    intro ω
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    set K : ℝ := Real.sqrt (ω 1).re + 1 with hKdef
    have hK : 0 < K := by
      have := Real.sqrt_nonneg (ω 1).re
      rw [hKdef]; linarith
    obtain ⟨N, hN⟩ := hunif ω (ε / (3 * K)) (by positivity)
    set d : A := ∑ n ∈ Finset.range N, t n with hddef
    have hsum : ∀ x : A, ∑ n ∈ Finset.range N, x * t n = x * d :=
      fun x => (Finset.mul_sum _ _ _).symm
    -- the uniform bound in the form `|ω(a/b) − ω(a·d)| ≤ ε/3`, by **43I**.1
    have hbnd : ∀ a ∈ S, ‖(ω (div a b) : ℂ) - ω (a * d)‖ ≤ ε / 3 := by
      intro a ha
      have h := hN a ha
      rw [hsum a] at h
      have h2 := norm_apply_le_omegaNorm ω (div a b - a * d)
      rw [npFunctional_sub] at h2
      calc ‖(ω (div a b) : ℂ) - ω (a * d)‖
          ≤ omegaNorm A ω (div a b - a * d) * Real.sqrt (ω 1).re := h2
        _ ≤ (ε / (3 * K)) * Real.sqrt (ω 1).re := by gcongr
        _ ≤ ε / 3 := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            have : Real.sqrt (ω 1).re ≤ K := by rw [hKdef]; linarith
            nlinarith [Real.sqrt_nonneg (ω 1).re, hε.le]
    -- each partial sum `a ↦ a·d` is ultraweakly continuous (**45IV**)
    have hc : @Continuous A A (ultraweak A) (ultraweak A) (fun x : A => x * d) :=
      (mult_uws_cont d).2.1
    have hmid : Tendsto (fun a : A => (ω (a * d) : ℂ))
        (@nhdsWithin A (ultraweak A) a₀ S) (𝓝 (ω (a₀ * d))) := by
      have hcc : @Continuous A ℂ (ultraweak A) _ (fun x : A => (ω (x * d) : ℂ)) := by
        let _ : TopologicalSpace A := ultraweak A
        exact (continuous_ultraweak_npFunctional ω).comp hc
      exact (@Continuous.tendsto A ℂ (ultraweak A) _ _ hcc a₀).mono_left
        (@nhdsWithin_le_nhds A (ultraweak A) a₀ S)
    have hev : ∀ᶠ a in (@nhdsWithin A (ultraweak A) a₀ S),
        ‖(ω (a * d) : ℂ) - ω (a₀ * d)‖ < ε / 3 := by
      have := Metric.tendsto_nhds.mp hmid (ε / 3) (by linarith)
      filter_upwards [this] with a ha
      rwa [Complex.dist_eq] at ha
    filter_upwards [@self_mem_nhdsWithin A (ultraweak A) a₀ S, hev] with a haS haM
    rw [Complex.dist_eq]
    have h1 := hbnd a haS
    have h3 := hbnd a₀ ha₀
    calc ‖(ω (div a b) : ℂ) - ω (div a₀ b)‖
        ≤ ‖(ω (div a b) : ℂ) - ω (a * d)‖ + ‖(ω (a * d) : ℂ) - ω (div a₀ b)‖ := by
          simpa using norm_sub_le_norm_sub_add_norm_sub
            ((ω (div a b) : ℂ)) (ω (a * d)) (ω (div a₀ b))
      _ ≤ ‖(ω (div a b) : ℂ) - ω (a * d)‖ + (‖(ω (a * d) : ℂ) - ω (a₀ * d)‖
            + ‖(ω (a₀ * d) : ℂ) - ω (div a₀ b)‖) := by
          gcongr
          simpa using norm_sub_le_norm_sub_add_norm_sub
            ((ω (a * d) : ℂ)) (ω (a₀ * d)) (ω (div a₀ b))
      _ < ε := by
          rw [← norm_neg ((ω (a₀ * d) : ℂ) - ω (div a₀ b)), neg_sub] at *
          linarith
  exact hkey

/-- **81IX** (`div-usc`, vn.tex:5533, Lemma), **first map, ultraweakly**:
`a ↦ a/b` is ultraweakly continuous on `(A)₁b`.  The `λ = 1` case of
`div_uwc_ball_of_norm_le`; together with `div_usc_ball` this is 81IX's first
clause as corrected ("both ultrastrongly and ultraweakly continuous"). -/
theorem div_uwc_ball (b : A) :
    @ContinuousOn A A (ultraweak A) (ultraweak A) (fun a => div a b)
      {a : A | ∃ d : A, ‖d‖ ≤ 1 ∧ a = d * b} :=
  div_uwc_ball_of_norm_le b 1 zero_le_one

/-- `⌈1⌋ = 1`. -/
theorem suppProj_one : suppProj (1 : A) = 1 := by
  have h := (ceil_spec (b := (1 : A)) zero_le_one).2.1
  rw [suppProj, star_one, one_mul]
  rw [one_mul] at h
  exact h

/-- `1∖a = a`, so the second map of 81IX is the first one at `c = 1`. -/
theorem ldiv_one (y : A) : ldiv 1 y = y :=
  ldiv_eq (one_mul y).symm (by rw [suppProj_one, one_mul])

/-- **81IX** (`div-usc`, vn.tex:5533, Lemma), second map as corrected:
`a ↦ c∖a/b` is **ultraweakly** continuous on `c(A)₁b`.

This is the thesis's repaired proof (vn.tex:5563) verbatim: `c∖x = (x*/c*)*`
for `x ∈ c(A)₁` by **81II**.5 (`division_basic_5`), so `c∖(·)` is ultraweakly
continuous because the adjoint is (`continuous_ultraweak_star`); and `(·)/b`
maps `c(A)₁b` into `c(A)₁` — explicitly, `(cdb)/b = cd⌊b⌉` — so it is
ultraweakly continuous there by `div_uwc_ball_of_norm_le` at `λ = ‖c‖`, and
the composite is ultraweakly continuous.  See the section note above for
why the printed *ultrastrong* claim is false. -/
theorem div_uwc_corner (b c : A) :
    @ContinuousOn A A (ultraweak A) (ultraweak A)
      (fun a => ldiv c (div a b))
      {a : A | ∃ d : A, ‖d‖ ≤ 1 ∧ a = c * d * b} := by
  let _instA : TopologicalSpace A := ultraweak A
  set S : Set A := {a : A | ∃ d : A, ‖d‖ ≤ 1 ∧ a = c * d * b} with hS
  set T : Set A := {y : A | ∃ e : A, ‖e‖ ≤ 1 ∧ y = e * star c} with hT
  have hq : IsStarProjection (rangeProj b) := (ceill_basic_2 b).1.1
  have hb : rangeProj b * b = b := (ceill_basic_2 b).1.2
  -- `(cdb)/b = cd⌊b⌉`, by the explicit characterisation of the quotient
  have hdivval : ∀ d : A, div (c * d * b) b = c * d * rangeProj b := by
    intro d
    refine div_eq ?_ ?_
    · rw [mul_assoc (c * d), hb]
    · rw [mul_assoc (c * d), hq.isIdempotentElem.eq]
  -- `c(A)₁b ⊆ (A)_‖c‖ b`, so `(·)/b` is ultraweakly continuous on it
  have hSsub : S ⊆ {a : A | ∃ d : A, ‖d‖ ≤ ‖c‖ ∧ a = d * b} := by
    rintro a ⟨d, hd, rfl⟩
    refine ⟨c * d, ?_, by noncomm_ring⟩
    calc ‖c * d‖ ≤ ‖c‖ * ‖d‖ := norm_mul_le _ _
      _ ≤ ‖c‖ * 1 := by gcongr
      _ = ‖c‖ := mul_one _
  have hA : ContinuousOn (fun a => div a b) S :=
    (div_uwc_ball_of_norm_le b ‖c‖ (norm_nonneg c)).mono hSsub
  have hB : ContinuousOn (fun a => star (div a b)) S :=
    continuous_ultraweak_star.comp_continuousOn hA
  -- `(·)/b` maps `c(A)₁b` into `c(A)₁`, so its adjoint lands in `(A)₁c*`
  have hmaps : Set.MapsTo (fun a => star (div a b)) S T := by
    rintro a ⟨d, hd, rfl⟩
    refine ⟨rangeProj b * star d, ?_, ?_⟩
    · calc ‖rangeProj b * star d‖ ≤ ‖rangeProj b‖ * ‖star d‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := by rw [norm_star]; gcongr; exact hq.norm_le
        _ = 1 := by norm_num
    · show star (div (c * d * b) b) = rangeProj b * star d * star c
      rw [hdivval d, star_mul, star_mul, hq.isSelfAdjoint.star_eq]
      noncomm_ring
  have hC : ContinuousOn (fun a => div (star (div a b)) (star c)) S :=
    (div_uwc_ball (star c)).comp hB hmaps
  have hD : ContinuousOn (fun a => star (div (star (div a b)) (star c))) S :=
    continuous_ultraweak_star.comp_continuousOn hC
  refine hD.congr ?_
  intro a ha
  have hmem : ∃ x : A, star (div a b) = x * star c := by
    obtain ⟨e, -, he⟩ := hmaps ha
    exact ⟨e, he⟩
  have h := (division_basic_5 (star c) (star (div a b)) hmem).2
  rw [star_star, star_star] at h
  exact h.symm

/-- **81IX** (`div-usc`, vn.tex:5533, Lemma) with "ultrastrongly" replaced
throughout by "ultraweakly": **both** maps `a ↦ a/b : (A)₁b → A` and
`a ↦ c∖a/b : c(A)₁b → A` are ultraweakly continuous.

**This is 81IX as corrected** by the author's ruling: the second map is
weakened to ultraweak continuity, while the first keeps its ultrastrong
continuity (`div_usc_ball`) *and* gains this ultraweak one.  It is also what
the one consumer needs — **96V** `canonical-filter` uses 81IX only for
*normality* of `g = d*∖f(·)/d`, whose proof in vn.tex runs ultraweakly
throughout.  The printed second conjunct is false and is not transcribed; see
the section note above.

Both conjuncts are the thesis's repaired proof: the first is `div_uwc_ball`
(the partial sums of **81V**.2, uniformly on `(A)₁b`), and the second is
`div_uwc_corner`, which reduces to the first through `c∖x = (x*/c*)*`
(**81II**.5) and ultraweak continuity of the adjoint, exactly as
vn.tex:5563 directs. -/
theorem div_uwc (b c : A) :
    @ContinuousOn A A (ultraweak A) (ultraweak A) (fun a => div a b)
        {a : A | ∃ d : A, ‖d‖ ≤ 1 ∧ a = d * b} ∧
      @ContinuousOn A A (ultraweak A) (ultraweak A)
        (fun a => ldiv c (div a b))
        {a : A | ∃ d : A, ‖d‖ ≤ 1 ∧ a = c * d * b} := by
  exact ⟨div_uwc_ball b, div_uwc_corner b c⟩

/-! ## Parsec 820: polar decomposition -/

/-- **82I** (`polar-decomposition`, vn.tex:5607, Proposition (Polar
Decomposition)): the partial isometry `[a] = a/√(a*a)` of the polar
decomposition `a = [a]√(a*a)`. -/
noncomputable def polar (a : A) : A := div a (CFC.sqrt (star a * a))

/-- Auxiliary for **82I**: the elementary facts about `√(a*a)` used
throughout the polar decomposition. -/
theorem sqrt_star_self_spec (a : A) :
    0 ≤ CFC.sqrt (star a * a) ∧ star (CFC.sqrt (star a * a)) = CFC.sqrt (star a * a) ∧
      CFC.sqrt (star a * a) * CFC.sqrt (star a * a) = star a * a ∧
      rangeProj (CFC.sqrt (star a * a)) = suppProj a ∧
      ceil (CFC.sqrt (star a * a)) = suppProj a ∧
      CFC.sqrt (star a * a) * suppProj a = CFC.sqrt (star a * a) := by
  have hspos : (0 : A) ≤ CFC.sqrt (star a * a) := CFC.sqrt_nonneg _
  have hssa : star (CFC.sqrt (star a * a)) = CFC.sqrt (star a * a) :=
    (IsSelfAdjoint.of_nonneg hspos).star_eq
  have hss : CFC.sqrt (star a * a) * CFC.sqrt (star a * a) = star a * a :=
    CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg a)
  have hceil : ceil (CFC.sqrt (star a * a)) = suppProj a := by
    have h := ceil_basic_5 (CFC.sqrt (star a * a)) hspos
    rw [sq, hss] at h
    rw [← h, suppProj]
  refine ⟨hspos, hssa, hss, ?_, hceil, ?_⟩
  · rw [rangeProj, hssa, hss, suppProj]
  · rw [← hceil]; exact (ceil_spec hspos).2.1

/-- **82I** (`polar-decomposition`, vn.tex:5607, Proposition (Polar
Decomposition)), main claim: every `a` can be written *uniquely* as
`a = u√(a*a)` with `u ∈ A⌈a⌋`; namely `u = [a]`. -/
theorem polar_decomposition (a : A) :
    (∃! u : A, a = u * CFC.sqrt (star a * a) ∧ u * suppProj a = u) ∧
      a = polar a * CFC.sqrt (star a * a) ∧
      polar a * suppProj a = polar a := by
  obtain ⟨hspos, hssa, hss, hrs, -, -⟩ := sqrt_star_self_spec a
  have hex : ∃ c : A, a = c * CFC.sqrt (star a * a) := by
    obtain ⟨t, ht⟩ := approximate_pseudoinverse (CFC.sqrt (star a * a))
    exact (proto_douglas_1 a _ (by rw [hssa, hss]) t ht).1
  obtain ⟨h1, h2⟩ := div_spec a (CFC.sqrt (star a * a)) hex
  refine ⟨?_, h1, ?_⟩
  · simpa only [hrs] using exists_div a (CFC.sqrt (star a * a)) hex
  · rw [polar, ← hrs]; exact h2

/-- Auxiliary for **82I**: `⌊a⌉[a] = [a]`, i.e. `⌊[a]⌉ ≤ ⌊a⌉`
(**81II**.1). -/
theorem rangeProj_mul_polar (a : A) : rangeProj a * polar a = polar a := by
  obtain ⟨hspos, hssa, hss, -, -, -⟩ := sqrt_star_self_spec a
  have hex : ∃ c : A, a = c * CFC.sqrt (star a * a) := by
    obtain ⟨t, ht⟩ := approximate_pseudoinverse (CFC.sqrt (star a * a))
    exact (proto_douglas_1 a _ (by rw [hssa, hss]) t ht).1
  exact (division_basic_1 (CFC.sqrt (star a * a)) a hex).1

/-- **82I** (`polar-decomposition`, vn.tex:5607, Proposition), part 1:
`[a]` is a partial isometry with `[a]*[a] = ⌈a*a⌉ = ⌈a⌋` and
`[a][a]* = ⌈aa*⌉ = ⌊a⌉`. -/
theorem polar_decomposition_1 (a : A) :
    IsPartialIsometry A (polar a) ∧
      star (polar a) * polar a = suppProj a ∧
      polar a * star (polar a) = rangeProj a := by
  obtain ⟨hspos, hssa, hss, hrs, hceil, hse⟩ := sqrt_star_self_spec a
  obtain ⟨-, hus, hue⟩ := polar_decomposition a
  set u : A := polar a with hudef
  set s : A := CFC.sqrt (star a * a) with hsdef
  set e : A := suppProj a with hedef
  have heproj : IsStarProjection e := (ceill_basic_1 a).1.1
  have hesa : star e = e := heproj.isSelfAdjoint.star_eq
  have heu : e * star u = star u := by
    have := congrArg star hue
    rwa [star_mul, hesa] at this
  -- `u*u = e` by cancelling `s` on both sides
  have hstaru : star u * u = e := by
    refine mult_cancellation_3 s (star u * u) e ?_ ?_ ?_
    · rw [hrs]
      calc e * (star u * u) * e = (e * star u) * (u * e) := by noncomm_ring
        _ = star u * u := by rw [heu, hue]
    · rw [hrs, heproj.isIdempotentElem.eq, heproj.isIdempotentElem.eq]
    · have hl : star s * (star u * u) * s = star a * a := by
        rw [hssa]
        calc s * (star u * u) * s = star (u * s) * (u * s) := by
              rw [star_mul, hssa]; noncomm_ring
          _ = star a * a := by rw [← hus]
      have hr : star s * e * s = star a * a := by
        rw [hssa]
        calc s * e * s = (s * e) * s := rfl
          _ = s * s := by rw [hse]
          _ = star a * a := hss
      rw [hl, hr]
  have hpi : IsPartialIsometry A u :=
    ((partial_isometry_equivalents u).out 1 0).mp (by rw [hstaru]; exact heproj)
  refine ⟨hpi, hstaru, ?_⟩
  -- `uu* = ⌊u⌉ ≤ ⌊a⌉`
  have huustar : u * star u = rangeProj u := hpi.2.2.2
  have hra : rangeProj a * u = u := rangeProj_mul_polar a
  have hle1 : rangeProj u ≤ rangeProj a :=
    (ceill_basic_2 u).2 ⟨(ceill_basic_2 a).1.1, hra⟩
  rcases eq_or_ne a 0 with rfl | hane
  · -- `a = 0` forces `u = 0`
    have h0 : e = 0 := by
      rw [hedef, suppProj, star_zero, zero_mul, ceil_zero]
    have hu0 : u = 0 := by rw [← hue, h0, mul_zero]
    rw [hu0, star_zero, mul_zero, rangeProj, star_zero, zero_mul, ceil_zero]
  · -- `⌊a⌉ = ⌈aa*⌉ = ⌈u(a*a)u*⌉ ≤ ⌈‖a*a‖ uu*⌉ = ⌈uu*⌉ ≤ uu*`
    refine le_antisymm (by rw [huustar]; exact hle1) ?_
    have hnn : (0 : A) ≤ a * star a := by simp
    have haa : a * star a = u * (star a * a) * star u := by
      calc a * star a = (u * s) * star (u * s) := by rw [← hus]
        _ = u * (s * s) * star u := by rw [star_mul, hssa]; noncomm_ring
        _ = u * (star a * a) * star u := by rw [hss]
    have hbound : u * (star a * a) * star u
        ≤ (‖star a * a‖ : ℝ) • (u * star u) := by
      have h := star_right_conjugate_le_conjugate
        (le_norm_smul_one (star_mul_self_nonneg a)) u
      calc u * (star a * a) * star u
          ≤ u * ((‖star a * a‖ : ℝ) • (1 : A)) * star u := h
        _ = (‖star a * a‖ : ℝ) • (u * star u) := by
            rw [mul_smul_comm, smul_mul_assoc, mul_one]
    have hnorm : 0 < ‖star a * a‖ := by
      rw [norm_pos_iff]
      exact fun h => hane ((CStarRing.star_mul_self_eq_zero_iff a).mp h)
    calc rangeProj a = ceil (a * star a) := rfl
      _ = ceil (u * (star a * a) * star u) := by rw [haa]
      _ ≤ ceil ((‖star a * a‖ : ℝ) • (u * star u)) := ceil_mono (haa ▸ hnn) hbound
      _ = ceil (u * star u) := ceil_smul (by rw [huustar]; exact (ceill_basic_2 u).1.1.nonneg) hnorm
      _ = u * star u := by
          rw [huustar]; exact ceil_of_isStarProjection (ceill_basic_2 u).1.1

/-- **82I** (`polar-decomposition`, vn.tex:5607, Proposition), part 2:
`[a*] = [a]*`, so that `√(aa*)[a] = a = [a]√(a*a)`. -/
theorem polar_decomposition_2 (a : A) :
    polar (star a) = star (polar a) ∧
      CFC.sqrt (a * star a) * polar a = a := by
  obtain ⟨hspos, hssa, hss, hrs, hceil, hse⟩ := sqrt_star_self_spec a
  obtain ⟨-, hus, hue⟩ := polar_decomposition a
  obtain ⟨hpi, hstaru, huu⟩ := polar_decomposition_1 a
  set u : A := polar a with hudef
  set s : A := CFC.sqrt (star a * a) with hsdef
  set e : A := suppProj a with hedef
  have heproj : IsStarProjection e := (ceill_basic_1 a).1.1
  have hesa : star e = e := heproj.isSelfAdjoint.star_eq
  have hes : e * s = s := by
    have := congrArg star hse
    rwa [star_mul, hssa, hesa] at this
  -- `√(aa*) = u √(a*a) u*`
  have hxpos : (0 : A) ≤ u * s * star u := by
    have := star_right_conjugate_nonneg hspos u
    simpa [mul_assoc] using this
  have hxx : (u * s * star u) * (u * s * star u) = a * star a := by
    calc (u * s * star u) * (u * s * star u)
        = u * s * (star u * u) * s * star u := by noncomm_ring
      _ = u * (s * e) * s * star u := by rw [hstaru]; noncomm_ring
      _ = u * (s * s) * star u := by rw [hse]; noncomm_ring
      _ = (u * s) * star (u * s) := by rw [star_mul, hssa]; noncomm_ring
      _ = a * star a := by rw [← hus]
  have hsqrt : CFC.sqrt (a * star a) = u * s * star u := by
    rw [← hxx, CFC.sqrt_mul_self _ hxpos]
  have hmain : CFC.sqrt (a * star a) * u = a := by
    rw [hsqrt]
    calc u * s * star u * u = u * s * (star u * u) := by noncomm_ring
      _ = u * (s * e) := by rw [hstaru]; noncomm_ring
      _ = u * s := by rw [hse]
      _ = a := hus.symm
  refine ⟨?_, hmain⟩
  -- `[a*] = [a]*`
  have hstara : star (star a) * star a = a * star a := by rw [star_star]
  have hrx : rangeProj (CFC.sqrt (star (star a) * star a)) = suppProj (star a) := by
    exact (sqrt_star_self_spec (star a)).2.2.2.1
  refine div_eq ?_ ?_
  · -- `a* = u* √(aa*)`
    rw [hstara, hsqrt]
    calc star a = star (u * s) := by rw [← hus]
      _ = s * star u := by rw [star_mul, hssa]
      _ = (e * s) * star u := by rw [hes]
      _ = star u * (u * s * star u) := by rw [← hstaru]; noncomm_ring
  · rw [hrx, suppProj_star]
    have hra : rangeProj a * u = u := rangeProj_mul_polar a
    have := congrArg star hra
    rwa [star_mul, (ceill_basic_2 a).1.1.isSelfAdjoint.star_eq] at this

/-! ## Parsec 830: the Murray–von Neumann preorder

**83I** (vn.tex:5684): introduction — nothing to formalize. -/

variable (A) in
/-- **83II** (`vmleq`, vn.tex:5694, Proposition): the **Murray–von Neumann
preorder**: `e' ⊴ e` when `e' = u*u` and `uu* ≤ e` for some partial
isometry `u`. -/
def MvNLE (e' e : A) : Prop :=
  ∃ u : A, IsPartialIsometry A u ∧ star u * u = e' ∧ u * star u ≤ e

/-- **83II** (`vmleq`, vn.tex:5694, Proposition): for projections `e'`,
`e` the following are equivalent: (1) `e' = ⌈a*ea⌉` for some `a`;
(2) `e' = ⌈a⌋` and `⌊a⌉ ≤ e` for some `a`; (3) `e' ⊴ e`. -/
theorem vmleq (e' e : A) (he' : IsStarProjection e')
    (he : IsStarProjection e) :
    List.TFAE
      [∃ a : A, e' = ceil (star a * e * a),
       ∃ a : A, e' = suppProj a ∧ rangeProj a ≤ e,
       MvNLE A e' e] := by
  -- `he'` is redundant: each of the three conditions already forces `e'` to
  -- be a projection.
  have _ := he'
  have hemul : ∀ x : A, rangeProj x ≤ e → e * x = x := by
    intro x hx
    have h1 : e * rangeProj x = rangeProj x :=
      ((projection_below_effect e (rangeProj x) ⟨he.nonneg, he.le_one⟩
        (ceill_basic_2 x).1.1).out 0 6).mp hx
    calc e * x = e * (rangeProj x * x) := by rw [(ceill_basic_2 x).1.2]
      _ = (e * rangeProj x) * x := by noncomm_ring
      _ = x := by rw [h1, (ceill_basic_2 x).1.2]
  tfae_have 3 → 2 := by
    rintro ⟨u, hpi, h1, h2⟩
    refine ⟨u, ?_, ?_⟩
    · rw [← h1]; exact hpi.1
    · rw [← hpi.2.2.2]; exact h2
  tfae_have 2 → 1 := by
    rintro ⟨x, hx1, hx2⟩
    refine ⟨x, ?_⟩
    rw [mul_assoc, hemul x hx2, hx1, suppProj]
  tfae_have 1 → 3 := by
    rintro ⟨x, hx⟩
    obtain ⟨hpi, hstar, hrange⟩ := polar_decomposition_1 (e * x)
    refine ⟨polar (e * x), hpi, ?_, ?_⟩
    · rw [hstar, suppProj, hx]
      congr 1
      calc star (e * x) * (e * x) = star x * (star e * e) * x := by
            rw [star_mul]; noncomm_ring
        _ = star x * e * x := by
            rw [he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]
    · rw [hrange]
      calc rangeProj (e * x) ≤ rangeProj e := (ceill_basic_4 e x).2
        _ = e := rangeProj_of_isStarProjection he
  tfae_finish

/-- **83IV** (`mvn-preorders`, vn.tex:5730, Exercise): `⊴` preorders the
projections of a von Neumann algebra. -/
theorem mvn_preorders :
    (∀ p : A, IsStarProjection p → MvNLE A p p) ∧
      ∀ p q r : A, IsStarProjection p → IsStarProjection q →
        IsStarProjection r → MvNLE A p q → MvNLE A q r → MvNLE A p r := by
  constructor
  · intro p hp
    refine ⟨p, ?_, ?_, ?_⟩
    · exact ((partial_isometry_equivalents p).out 1 0).mp
        (by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]; exact hp)
    · rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
    · rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  · rintro p q r hp hq hr ⟨u, hu, hu1, hu2⟩ ⟨v, hv, hv1, hv2⟩
    -- `uu* ≤ q` gives `qu = u`
    have huu : IsStarProjection (u * star u) :=
      ((partial_isometry_equivalents u).out 0 3).mp hu
    have hqu : q * u = u := by
      have h1 : q * (u * star u) = u * star u :=
        ((projection_below_effect q (u * star u) ⟨hq.nonneg, hq.le_one⟩
          huu).out 0 6).mp hu2
      have h2 : u * star u * u = u := ((partial_isometry_equivalents u).out 0 2).mp hu
      calc q * u = q * (u * star u * u) := by rw [h2]
        _ = (q * (u * star u)) * u := by noncomm_ring
        _ = u := by rw [h1, h2]
    have hkey : star (v * u) * (v * u) = p := by
      calc star (v * u) * (v * u) = star u * (star v * v) * u := by
            rw [star_mul]; noncomm_ring
        _ = star u * (q * u) := by rw [hv1]; noncomm_ring
        _ = star u * u := by rw [hqu]
        _ = p := hu1
    refine ⟨v * u, ?_, hkey, ?_⟩
    · exact ((partial_isometry_equivalents (v * u)).out 1 0).mp
        (by rw [hkey]; exact hp)
    · have h3 : v * (u * star u) * star v ≤ v * q * star v :=
        star_right_conjugate_le_conjugate hu2 v
      have h4 : v * q * star v = v * star v := by
        rw [← hv1]
        have h5 : v * star v * v = v := ((partial_isometry_equivalents v).out 0 2).mp hv
        calc v * (star v * v) * star v = (v * star v * v) * star v := by noncomm_ring
          _ = v * star v := by rw [h5]
      calc (v * u) * star (v * u) = v * (u * star u) * star v := by
            rw [star_mul]; noncomm_ring
        _ ≤ v * q * star v := h3
        _ = v * star v := h4
        _ ≤ r := hv2

/-- **83V** (`cceil-sum`, vn.tex:5734, Lemma): for a projection `e` there
is a family `(eᵢ)` of non-zero pairwise orthogonal projections with
`⌈⌈e⌉⌉ = ∑ᵢ eᵢ` and `eᵢ ⊴ e` for all `i`. -/
theorem cceil_sum (e : A) (he : IsStarProjection e) :
    ∃ (ι : Type u) (e' : ι → A),
      (∀ i, IsStarProjection (e' i) ∧ e' i ≠ 0 ∧ MvNLE A (e' i) e) ∧
      (Pairwise fun i j => e' i * e' j = 0) ∧
      cceil e = projSup (Set.range e') := by
  classical
  -- a maximal family of non-zero pairwise orthogonal projections below `e`
  set T : Set (Set A) :=
    {S | (∀ x ∈ S, IsStarProjection x ∧ x ≠ 0 ∧ MvNLE A x e) ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x * y = 0} with hT
  obtain ⟨S, hSmax⟩ : ∃ S, Maximal (· ∈ T) S := by
    refine zorn_subset T fun c hc hchain =>
      ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro x ⟨s, hs, hxs⟩
      exact (hc hs).1 x hxs
    · rintro x ⟨s, hs, hxs⟩ y ⟨s', hs', hys'⟩ hxy
      rcases hchain.total hs hs' with hsub | hsub
      · exact (hc hs').2 x (hsub hxs) y hys' hxy
      · exact (hc hs).2 x hxs y (hsub hys') hxy
  have hSproj : ∀ x ∈ S, IsStarProjection x := fun x hx => (hSmax.1.1 x hx).1
  refine ⟨↥S, Subtype.val, fun i => hSmax.1.1 i.1 i.2,
    fun i j hij => hSmax.1.2 i.1 i.2 j.1 j.2 fun h => hij (Subtype.ext h), ?_⟩
  rw [Subtype.range_coe]
  obtain ⟨hqproj, hqub, hqleast⟩ := projSup_spec hSproj
  have hcproj : IsStarProjection (cceil e) := (cceil_isLeast e).1.1
  have hnn : ∀ a : A, (0 : A) ≤ star a * e * a := fun a =>
    star_left_conjugate_nonneg he.nonneg a
  have hceilproj : ∀ a : A, IsStarProjection (ceil (star a * e * a)) := fun a =>
    (ceil_spec (hnn a)).1
  have hsetproj : ∀ z ∈ {x : A | ∃ a : A, x = ceil (star a * e * a)},
      IsStarProjection z := by
    rintro _ ⟨a, rfl⟩; exact hceilproj a
  -- `x ⊴ e` implies `x ≤ ⌈⌈e⌉⌉`
  have hmvle : ∀ x : A, IsStarProjection x → MvNLE A x e → x ≤ cceil e := by
    rintro x hx ⟨u, hu, hu1, hu2⟩
    have hflip : star u * u * star u = star u :=
      ((partial_isometry_equivalents u).out 0 4).mp hu
    have hstep : x ≤ star u * e * u := by
      rw [← hu1]
      calc star u * u = (star u * u * star u) * u := by rw [hflip]
        _ = star u * (u * star u) * u := by noncomm_ring
        _ ≤ star u * e * u := star_left_conjugate_le_conjugate hu2 u
    calc x = ceil x := (ceil_of_isStarProjection hx).symm
      _ ≤ ceil (star u * e * u) := ceil_mono hx.nonneg hstep
      _ ≤ cceil e := by
          rw [(cceil_fundamental e he).2]
          exact (projSup_spec hsetproj).2.1 _ ⟨u, rfl⟩
  have hqle : projSup S ≤ cceil e :=
    hqleast _ hcproj fun x hx => hmvle x (hSproj x hx) (hSmax.1.1 x hx).2.2
  refine le_antisymm ?_ hqle
  by_contra hlt
  set p : A := cceil e - projSup S with hpdef
  have hpproj : IsStarProjection p :=
    projection_below_projection _ _ hqproj hcproj hqle
  have hpne : p ≠ 0 := by
    intro h
    rw [hpdef, sub_eq_zero] at h
    exact hlt h.le
  have hple : p ≤ cceil e := by
    rw [hpdef, sub_le_self_iff]
    exact hqproj.nonneg
  -- `p = p⌈⌈e⌉⌉p = ⋃ₐ ⌈p⌈a*ea⌉p⌉ = ⋃ₐ ⌈(eap)*eap⌉`, so some `e a p` is non-zero
  have hps : star p = p := hpproj.isSelfAdjoint.star_eq
  have himgproj : ∀ x ∈ ((fun q => ceil (star p * q * p)) ''
      {x : A | ∃ a : A, x = ceil (star a * e * a)}), IsStarProjection x := by
    rintro _ ⟨q, hq, rfl⟩
    exact (ceil_spec (star_left_conjugate_nonneg (hsetproj q hq).nonneg p)).1
  -- `⌈p⌈a*ea⌉p⌉ = ⌈pa*eap⌉ = ⌈(eap)*eap⌉`, by **60VII**.1
  have hconj : ∀ a : A, ceil (star p * ceil (star a * e * a) * p)
      = ceil (star (e * a * p) * (e * a * p)) := by
    intro a
    rw [← ceil_fundamental_1 p (star a * e * a) (hnn a)]
    congr 1
    calc star p * (star a * e * a) * p
        = p * (star a * (e * e) * a) * p := by rw [hps, he.isIdempotentElem.eq]
      _ = star (e * a * p) * (e * a * p) := by
          rw [star_mul, star_mul, he.isSelfAdjoint.star_eq, hps]
          noncomm_ring
  -- `p = ⌈p⌈⌈e⌉⌉p⌉ = ⋃ₐ ⌈p⌈a*ea⌉p⌉`, by **60IX**.2
  have hpeq : p = projSup ((fun q => ceil (star p * q * p)) ''
      {x : A | ∃ a : A, x = ceil (star a * e * a)}) := by
    have hpc : p * cceil e = p :=
      ((projection_below_effect (cceil e) p ⟨hcproj.nonneg, hcproj.le_one⟩
        hpproj).out 0 7).mp hple
    rw [← ceil_conj_projSup p _ hsetproj, ← (cceil_fundamental e he).2, hps]
    calc p = ceil p := (ceil_of_isStarProjection hpproj).symm
      _ = ceil (p * cceil e * p) := by rw [hpc, hpproj.isIdempotentElem.eq]
  have hex : ∃ a : A, e * a * p ≠ 0 := by
    by_contra hcon
    refine hpne (hpeq.trans (projSup_eq himgproj (IsStarProjection.zero A)
      ?_ fun q hq _ => hq.nonneg))
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    have hall : e * a * p = 0 := by by_contra h; exact hcon ⟨a, h⟩
    refine le_of_eq ?_
    show ceil (star p * ceil (star a * e * a) * p) = 0
    rw [hconj a, hall, star_zero, zero_mul, ceil_zero]
  obtain ⟨a, hax⟩ := hex
  obtain ⟨hpi, hstar, hrange⟩ := polar_decomposition_1 (e * a * p)
  set f : A := star (polar (e * a * p)) * polar (e * a * p) with hfdef
  have hfsupp : f = suppProj (e * a * p) := hstar
  have hfproj : IsStarProjection f := by rw [hfsupp]; exact (ceill_basic_1 _).1.1
  have hfne : f ≠ 0 := by
    rw [hfsupp]
    intro h
    exact hax (by rw [← (ceill_basic_1 (e * a * p)).1.2, h, mul_zero])
  have hfmvn : MvNLE A f e := by
    refine ⟨polar (e * a * p), hpi, rfl, ?_⟩
    rw [hrange]
    calc rangeProj (e * a * p) = rangeProj (e * (a * p)) := by rw [mul_assoc]
      _ ≤ rangeProj e := (ceill_basic_4 e (a * p)).2
      _ = e := rangeProj_of_isStarProjection he
  have hfp : f ≤ p := by
    rw [hfsupp]
    calc suppProj (e * a * p) ≤ suppProj p := (ceill_basic_4 (e * a) p).1
      _ = p := suppProj_of_isStarProjection hpproj
  have hfpmul : f * p = f :=
    ((projection_below_effect p f ⟨hpproj.nonneg, hpproj.le_one⟩ hfproj).out 0 7).mp hfp
  have hcq : cceil e * projSup S = projSup S :=
    ((projection_below_effect (cceil e) (projSup S)
      ⟨hcproj.nonneg, hcproj.le_one⟩ hqproj).out 0 6).mp hqle
  have hpq : p * projSup S = 0 := by
    rw [hpdef, sub_mul, hcq, hqproj.isIdempotentElem.eq, sub_self]
  have hforth : ∀ y ∈ S, f * y = 0 := by
    intro y hy
    have hyq : projSup S * y = y :=
      ((projection_below_effect (projSup S) y ⟨hqproj.nonneg, hqproj.le_one⟩
        (hSproj y hy)).out 0 6).mp (hqub y hy)
    calc f * y = (f * p) * (projSup S * y) := by rw [hfpmul, hyq]
      _ = f * (p * projSup S) * y := by noncomm_ring
      _ = 0 := by rw [hpq, mul_zero, zero_mul]
  -- `insert f S` contradicts maximality
  have hins : insert f S ∈ T := by
    constructor
    · rintro x (rfl | hx)
      · exact ⟨hfproj, hfne, hfmvn⟩
      · exact hSmax.1.1 x hx
    · rintro x (rfl | hx) y (rfl | hy) hxy
      · exact absurd rfl hxy
      · exact hforth y hy
      · have h := hforth x hx
        have := congrArg star h
        rwa [star_mul, hfproj.isSelfAdjoint.star_eq,
          (hSproj x hx).isSelfAdjoint.star_eq, star_zero] at this
      · exact hSmax.1.2 x hx y hy hxy
  have hfS : f ∈ S := hSmax.2 hins (Set.subset_insert _ _) (Set.mem_insert _ _)
  have hfq : f * projSup S = f :=
    ((projection_below_effect (projSup S) f ⟨hqproj.nonneg, hqproj.le_one⟩
      hfproj).out 0 7).mp (hqub f hfS)
  exact hfne (by
    calc f = f * projSup S := hfq.symm
      _ = (f * p) * projSup S := by rw [hfpmul]
      _ = f * (p * projSup S) := by noncomm_ring
      _ = 0 := by rw [hpq, mul_zero])

end Pseudoinverse

/-! ## Parsec 840: finite-dimensional C*-algebras

**84I** (vn.tex:5780): introduction — nothing to formalize. -/

/-! ### Ingredients for 84II

The proof below **diverges from the thesis's**: instead of
showing that a finite-dimensional C*-algebra is a von Neumann algebra and
building a system of matrix units by hand (vn.tex:5798–6027), it takes the
*algebra* decomposition from Mathlib's Wedderburn–Artin theorem
(`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`) and upgrades it
to a **∗**-isomorphism.  The upgrade needs Skolem–Noether for matrix algebras,
which Mathlib does not have; it is proved here as
`matrix_exists_intertwiner`. -/

section FDCStar

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A C*-algebra has trivial Jacobson radical (given that it is Artinian, so that
the radical is nilpotent). -/
private theorem cstar_jacobson_eq_bot (R : Type u) [CStarAlgebra R] [IsArtinianRing R] :
    Ring.jacobson R = ⊥ := by
  obtain ⟨n, hn⟩ : IsNilpotent (Ring.jacobson R) := IsSemiprimaryRing.isNilpotent
  refine Submodule.eq_bot_iff _ |>.mpr fun x hx => ?_
  set y : R := star x * x with hy
  have hysa : IsSelfAdjoint y := by simp [hy, IsSelfAdjoint, star_mul]
  have hyJ : y ∈ Ring.jacobson R := Ideal.mul_mem_left _ _ hx
  have hyn : y ^ n = 0 := by
    have : y ^ n ∈ (Ring.jacobson R) ^ n := Ideal.pow_mem_pow hyJ n
    rw [hn] at this
    simpa using this
  have hpow : ∀ m : ℕ, n ≤ m → y ^ m = 0 := by
    intro m hm
    rw [← Nat.sub_add_cancel hm, pow_add, hyn, mul_zero]
  have h2 : y ^ 2 ^ n = 0 := hpow _ (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hnn : ‖y‖ ^ 2 ^ n = 0 := by rw [← hysa.norm_pow_two_pow, h2, norm_zero]
  have hy0 : y = 0 := by
    have : ‖y‖ = 0 := by
      simpa using pow_eq_zero_iff (n := 2 ^ n) (by positivity) |>.mp hnn
    simpa using this
  have hxx : ‖x‖ * ‖x‖ = 0 := by
    rw [← CStarRing.norm_star_mul_self (x := x), ← hy, hy0, norm_zero]
  have : ‖x‖ = 0 := by
    rcases mul_eq_zero.mp hxx with h | h <;> exact h
  simpa using this

private theorem matrix_single_mul_single (p q r s : n) :
    single p q (1 : ℂ) * single r s 1 = if q = r then single p s 1 else 0 := by
  by_cases h : q = r
  · subst h; rw [Matrix.single_mul_single_same]; simp
  · simp only [h, if_false]
    calc single p q (1 : ℂ) * single r s 1 = single p q (1 : ℂ) * 1 * single r s 1 := by
          rw [mul_one]
      _ = single p s (1 * (1 : Matrix n n ℂ) q r * 1) :=
          Matrix.single_mul_mul_single _ _ _ _ _ _ _
      _ = 0 := by simp [h]

/-- **Skolem–Noether for matrix algebras** (absent from Mathlib): every ℂ-algebra
automorphism of `Matrix n n ℂ` is inner. -/
private theorem matrix_exists_intertwiner [Nonempty n]
    (ψ : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) :
    ∃ u : Matrix n n ℂ, IsUnit u ∧ ∀ x, ψ x * u = u * x := by
  classical
  set i₀ := Classical.arbitrary n with hi₀
  set T : Matrix n n ℂ → Matrix n n ℂ :=
    fun X => ∑ j : n, ψ (single j i₀ 1) * X * single i₀ j 1 with hT
  have key : ∀ (X : Matrix n n ℂ) (a b : n), ψ (single a b 1) * T X = T X * single a b 1 := by
    intro X a b
    have hL : ψ (single a b 1) * T X = ψ (single a i₀ 1) * X * single i₀ b 1 := by
      have e1 : ψ (single a b 1) * T X
          = ∑ j : n, ψ (single a b 1 * single j i₀ 1) * X * single i₀ j 1 := by
        rw [hT, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]; noncomm_ring
      rw [e1, Finset.sum_eq_single b]
      · rw [matrix_single_mul_single]; simp
      · intro j _ hj
        rw [matrix_single_mul_single, if_neg (Ne.symm hj), map_zero, zero_mul, zero_mul]
      · intro h; exact absurd (Finset.mem_univ b) h
    have hR : T X * single a b 1 = ψ (single a i₀ 1) * X * single i₀ b 1 := by
      have e1 : T X * single a b 1
          = ∑ j : n, ψ (single j i₀ 1) * X * (single i₀ j 1 * single a b 1) := by
        rw [hT, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        noncomm_ring
      rw [e1, Finset.sum_eq_single a]
      · rw [matrix_single_mul_single]; simp
      · intro j _ hj
        rw [matrix_single_mul_single, if_neg hj, mul_zero]
      · intro h; exact absurd (Finset.mem_univ a) h
    rw [hL, hR]
  have hsingle : ∀ (a b : n) (c : ℂ), single a b c = c • single a b 1 := by
    intro a b c; ext p q; simp [Matrix.single_apply]
  have key' : ∀ (X x : Matrix n n ℂ), ψ x * T X = T X * x := by
    intro X x
    induction x using Matrix.induction_on' with
    | h_zero => simp
    | h_add p q hp hq => rw [map_add, add_mul, hp, hq, mul_add]
    | h_std_basis a b c =>
        rw [hsingle, map_smul, smul_mul_assoc, key, mul_smul_comm]
  have hex : ∃ X, T X ≠ 0 := by
    by_contra hc
    push_neg at hc
    have hF : ∀ q : n, ψ (single i₀ i₀ 1) * single q i₀ (1 : ℂ) = 0 := by
      intro q
      have h1 : ψ (single i₀ i₀ 1) * T (single q i₀ 1) * single i₀ i₀ 1
          = ψ (single i₀ i₀ 1) * single q i₀ (1 : ℂ) := by
        have e1 : ψ (single i₀ i₀ 1) * T (single q i₀ 1) * single i₀ i₀ 1
            = ∑ j : n, ψ (single i₀ i₀ 1 * single j i₀ 1) * (single q i₀ (1:ℂ)) *
                (single i₀ j 1 * single i₀ i₀ 1) := by
          rw [hT, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul]; noncomm_ring
        rw [e1, Finset.sum_eq_single i₀]
        · rw [mul_assoc, matrix_single_mul_single]
          simp
        · intro j _ hj
          rw [matrix_single_mul_single, if_neg (Ne.symm hj), map_zero, zero_mul, zero_mul]
        · intro h; exact absurd (Finset.mem_univ i₀) h
      rw [← h1, hc, mul_zero, zero_mul]
    have hz : ψ (single i₀ i₀ (1 : ℂ)) = 0 := by
      ext a q
      have h2 := congrFun (congrFun (hF q) a) i₀
      simpa using h2
    have h3 := ψ.injective (hz.trans (map_zero ψ).symm)
    have h1 : (single i₀ i₀ (1 : ℂ)) i₀ i₀ = 0 := by rw [h3]; simp
    simp at h1
  obtain ⟨X, hX⟩ := hex
  refine ⟨T X, ?_, fun x => key' X x⟩
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have hker : ∀ v : n → ℂ, T X *ᵥ v = 0 → v = 0 := ?_
  · intro v w hvw
    have h0 : T X *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub, hvw, sub_self]
    exact sub_eq_zero.mp (hker _ h0)
  intro v hv
  by_contra hv0
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push_neg at h; exact hv0 (funext h)
  apply hX
  have hall : ∀ w : n → ℂ, T X *ᵥ w = 0 := by
    intro w
    set x : Matrix n n ℂ := Matrix.of fun a b => if b = i then w a / v i else 0 with hx
    have hxv : x *ᵥ v = w := by
      ext a
      simp only [hx, Matrix.mulVec, Matrix.of_apply, dotProduct]
      rw [Finset.sum_eq_single i]
      · have hii : (if i = i then w a / v i else 0) = w a / v i := by simp
        rw [hii]
        field_simp
      · intro j _ hj; simp [hj]
      · intro h; exact absurd (Finset.mem_univ i) h
    calc T X *ᵥ w = T X *ᵥ (x *ᵥ v) := by rw [hxv]
      _ = (T X * x) *ᵥ v := by rw [Matrix.mulVec_mulVec]
      _ = (ψ x * T X) *ᵥ v := by rw [key' X x]
      _ = ψ x *ᵥ (T X *ᵥ v) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv, Matrix.mulVec_zero]
  ext a b
  have h4 := congrFun (hall (Pi.single b 1)) a
  simpa [Matrix.mulVec_single] using h4

/-- Given a conjugate-linear anti-automorphism `J` of `Matrix n n ℂ` which is
involutive and "definite" (`J x * x = 0 → x = 0`), there is an algebra
automorphism `θ` turning `J` into the conjugate transpose. -/
private theorem matrix_exists_algEquiv_conj [Nonempty n]
    (J : Matrix n n ℂ → Matrix n n ℂ)
    (hadd : ∀ x y, J (x + y) = J x + J y)
    (hsmul : ∀ (c : ℂ) x, J (c • x) = (starRingEnd ℂ) c • J x)
    (hmul : ∀ x y, J (x * y) = J y * J x)
    (hone : J 1 = 1)
    (hinvol : ∀ x, J (J x) = x)
    (hdefinite : ∀ x, J x * x = 0 → x = 0) :
    ∃ θ : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ, ∀ x, θ (J x) = star (θ x) := by
  classical
  -- Step 1: `ψ x = star (J x)` is an algebra automorphism.
  have hψadd : ∀ x y, star (J (x + y)) = star (J x) + star (J y) := by
    intro x y; rw [hadd, star_add]
  have hψsmul : ∀ (c : ℂ) x, star (J (c • x)) = c • star (J x) := by
    intro c x; rw [hsmul, star_smul]; simp
  have hψmul : ∀ x y, star (J (x * y)) = star (J x) * star (J y) := by
    intro x y; rw [hmul, star_mul]
  let ψL : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
    { toFun := fun x => star (J x)
      map_add' := hψadd
      map_smul' := by intro c x; simpa using hψsmul c x }
  let ψA : Matrix n n ℂ →ₐ[ℂ] Matrix n n ℂ :=
    AlgHom.ofLinearMap ψL (by simpa [ψL] using congrArg star hone) (by
      intro x y; simpa [ψL] using hψmul x y)
  have hbij : Function.Bijective (fun x => star (J x) : Matrix n n ℂ → Matrix n n ℂ) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨fun y => J (star y), ?_, ?_⟩
    · intro x; simp [hinvol]
    · intro y; simp [hinvol]
  let ψ : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ := AlgEquiv.ofBijective ψA hbij
  have hψapp : ∀ x, ψ x = star (J x) := fun x => rfl
  -- Step 2: `ψ` is inner, giving `h` with `h * J x = star x * h`.
  obtain ⟨u, hu, hcomm⟩ := matrix_exists_intertwiner ψ
  set h : Matrix n n ℂ := star u with hhdef
  have hh : IsUnit h := hu.star
  have hrel : ∀ x, h * J x = star x * h := by
    intro x
    have h1 : star (J x) * u = u * x := by rw [← hψapp]; exact hcomm x
    have h2 := congrArg star h1
    rw [star_mul, star_mul, star_star] at h2
    exact h2
  have hdet : IsUnit h.det := (Matrix.isUnit_iff_isUnit_det h).mp hh
  have hli : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul h hdet
  have hri : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h hdet
  have hJx : ∀ x, J x = h⁻¹ * (star x * h) := by
    intro x
    rw [← hrel x, ← mul_assoc, hli, one_mul]
  -- Step 3: `star h` is a scalar multiple of `h`.
  have hstarinv : star h⁻¹ * star h = 1 := by rw [← star_mul, hri, star_one]
  have hcentral : ∀ x, (star h⁻¹ * h) * x = x * (star h⁻¹ * h) := by
    intro x
    have e1 : h * x = star h * (x * (star h⁻¹ * h)) := by
      have := hrel (J x)
      rw [hinvol] at this
      rw [this, hJx x]
      rw [star_mul, star_mul, star_star]
      simp only [mul_assoc, star_star]
    calc (star h⁻¹ * h) * x = star h⁻¹ * (h * x) := by noncomm_ring
      _ = star h⁻¹ * (star h * (x * (star h⁻¹ * h))) := by rw [e1]
      _ = (star h⁻¹ * star h) * (x * (star h⁻¹ * h)) := by noncomm_ring
      _ = x * (star h⁻¹ * h) := by rw [hstarinv, one_mul]
  obtain ⟨μ, hμ⟩ : (star h⁻¹ * h) ∈ Set.range (Matrix.scalar n) := by
    refine Matrix.mem_range_scalar_of_commute_single ?_
    intro i j _
    exact (hcentral (Matrix.single i j 1)).symm
  have hscalarone : (Matrix.scalar n μ) = μ • (1 : Matrix n n ℂ) := by
    ext p q; simp [Matrix.scalar, Matrix.one_apply, Matrix.diagonal_apply]
  have hhstar : star h = (starRingEnd ℂ) μ • h := by
    have e1 : h = μ • star h := by
      calc h = star h * (star h⁻¹ * h) := by rw [← mul_assoc, ← star_mul, hli, star_one, one_mul]
        _ = star h * (Matrix.scalar n μ) := by rw [← hμ]
        _ = μ • star h := by rw [hscalarone, mul_smul_comm, mul_one]
    calc star h = star (μ • star h) := by rw [← e1]
      _ = (starRingEnd ℂ) μ • h := by rw [star_smul, star_star]; rfl
  -- Step 4: rescale `h` to a self-adjoint `h'`.
  have hne : h ≠ 0 := by
    intro h0
    have : (1 : Matrix n n ℂ) = 0 := by rw [← hli, h0, mul_zero]
    exact one_ne_zero this
  set lam : ℂ := (starRingEnd ℂ) μ with hlam
  have habs : (starRingEnd ℂ) lam * lam = 1 := by
    have e2 : h = ((starRingEnd ℂ) lam * lam) • h := by
      calc h = star (star h) := (star_star h).symm
        _ = star (lam • h) := by rw [hhstar]
        _ = (starRingEnd ℂ) lam • star h := by rw [star_smul]; rfl
        _ = (starRingEnd ℂ) lam • (lam • h) := by rw [hhstar]
        _ = ((starRingEnd ℂ) lam * lam) • h := by rw [smul_smul]
    have e3 : (((starRingEnd ℂ) lam * lam) - 1) • h = 0 := by
      rw [sub_smul, one_smul, ← e2, sub_self]
    rcases smul_eq_zero.mp e3 with e4 | e4
    · linear_combination (norm := ring_nf) e4
    · exact absurd e4 hne
  obtain ⟨α, hα0, hαlam⟩ : ∃ α : ℂ, α ≠ 0 ∧ (starRingEnd ℂ) α * lam = α := by
    by_cases hc : 1 + lam = 0
    · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
      have hlm : lam = -1 := by linear_combination hc
      rw [hlm]
      simp
    · refine ⟨1 + lam, hc, ?_⟩
      rw [map_add, map_one, add_mul, one_mul, habs]
      ring
  set h' : Matrix n n ℂ := α • h with hh'def
  have hsa : star h' = h' := by
    rw [hh'def, star_smul, hhstar, smul_smul]
    congr 1
  set g : Matrix n n ℂ := α⁻¹ • h⁻¹ with hgdef
  have hg1 : g * h' = 1 := by
    rw [hgdef, hh'def, smul_mul_smul_comm, hli, inv_mul_cancel₀ hα0, one_smul]
  have hg2 : h' * g = 1 := by
    rw [hgdef, hh'def, smul_mul_smul_comm, hri, mul_inv_cancel₀ hα0, one_smul]
  have hrel' : ∀ x, h' * J x = star x * h' := by
    intro x
    rw [hh'def, smul_mul_assoc, hrel, mul_smul_comm]
  -- Step 5: the Hermitian form of `h'` is anisotropic.
  have haniso : ∀ v : n → ℂ, star v ⬝ᵥ (h' *ᵥ v) = 0 → v = 0 := by
    intro v hv
    set i₀ := Classical.arbitrary n with hi₀
    set x : Matrix n n ℂ := Matrix.of (fun a b => if b = i₀ then v a else 0) with hxdef
    have hstarx : ∀ a q, (star x) a q = if a = i₀ then (starRingEnd ℂ) (v q) else 0 := by
      intro a q
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, hxdef]
      simp only [Matrix.of_apply]
      split_ifs with h1 <;> simp
    have hhx : ∀ q b, (h' * x) q b = if b = i₀ then (h' *ᵥ v) q else 0 := by
      intro q b
      rw [Matrix.mul_apply]
      simp only [hxdef, Matrix.of_apply]
      split_ifs with hb
      · simp [Matrix.mulVec, dotProduct]
      · simp
    have hxz : star x * (h' * x) = 0 := by
      ext a b
      rw [Matrix.mul_apply]
      simp only [hstarx, hhx, Matrix.zero_apply]
      by_cases ha : a = i₀ <;> by_cases hb : b = i₀ <;> simp [ha, hb]
      simpa [dotProduct, Matrix.mulVec] using hv
    have hJxx : J x * x = 0 := by
      have e1 : h' * (J x * x) = 0 := by
        rw [← mul_assoc, hrel', mul_assoc, hxz]
      calc J x * x = (g * h') * (J x * x) := by rw [hg1, one_mul]
        _ = g * (h' * (J x * x)) := by rw [mul_assoc]
        _ = 0 := by simp [e1]
    have hx0 := hdefinite x hJxx
    funext a
    have := congrFun (congrFun hx0 a) i₀
    simpa [hxdef] using this
  -- Step 6: `h'` is (positive or negative) definite.
  have hHerm : h'.IsHermitian := by
    rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose]; exact hsa
  set d := hHerm.eigenvalues with hd
  set w : n → (n → ℂ) := fun j => ⇑(hHerm.eigenvectorBasis j) with hw
  have hmv : ∀ j, h' *ᵥ w j = ((d j : ℂ)) • w j := by
    intro j
    rw [hw]
    simp only
    rw [hHerm.mulVec_eigenvectorBasis]
    funext i
    simp [Complex.real_smul]
    left
    rw [hd]
  have hip : ∀ p q, star (w p) ⬝ᵥ w q = if p = q then 1 else 0 := by
    intro p q
    have h1 := orthonormal_iff_ite.mp hHerm.eigenvectorBasis.orthonormal p q
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h1
    rw [dotProduct_comm]
    exact h1
  have hwne : ∀ j, w j ≠ 0 := by
    intro j hj
    have h1 := hip j j
    rw [hj] at h1
    simp at h1
  have hd0 : ∀ j, d j ≠ 0 := by
    intro j hj0
    refine hwne j (haniso _ ?_)
    rw [hmv, dotProduct_smul, hip]
    simp [hj0]
  have hB : ∀ (c₁ c₂ : ℂ) (p q : n), p ≠ q →
      star ((c₁ • w p) + (c₂ • w q)) ⬝ᵥ (h' *ᵥ ((c₁ • w p) + (c₂ • w q)))
        = (starRingEnd ℂ) c₁ * c₁ * (d p : ℂ) + (starRingEnd ℂ) c₂ * c₂ * (d q : ℂ) := by
    intro c₁ c₂ p q hpq
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hmv, star_add, star_smul,
      add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, hip,
      smul_eq_mul, smul_smul]
    simp [hpq, Ne.symm hpq]
    ring
  have hmix : ∀ p q, 0 < d p → d q < 0 → False := by
    intro p q hp hq
    have hpq : p ≠ q := by rintro rfl; linarith
    set a : ℝ := Real.sqrt (-(d q)) with ha
    set b : ℝ := Real.sqrt (d p) with hb
    have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
    have haa : a * a = -(d q) := Real.mul_self_sqrt (by linarith)
    have hbb : b * b = d p := Real.mul_self_sqrt (le_of_lt hp)
    set v : n → ℂ := ((a : ℂ) • w p) + ((b : ℂ) • w q) with hv
    have hz : star v ⬝ᵥ (h' *ᵥ v) = 0 := by
      rw [hv, hB _ _ _ _ hpq]
      simp only [Complex.conj_ofReal]
      have : ((a * a * d p + b * b * d q : ℝ) : ℂ) = 0 := by
        rw [haa, hbb]
        norm_cast
        ring
      push_cast at this
      linear_combination this
    have hv0 := haniso v hz
    have hpv : star (w p) ⬝ᵥ v = (a : ℂ) := by
      rw [hv, dotProduct_add, dotProduct_smul, dotProduct_smul, hip, hip]
      simp [hpq]
    rw [hv0] at hpv
    simp at hpv
    exact absurd hpv (by positivity)
  set j₀ := Classical.arbitrary n with hj₀
  set s : ℝ := if 0 < d j₀ then 1 else -1 with hs
  have hspos : ∀ j, 0 < s * d j := by
    intro j
    by_cases hc : 0 < d j₀
    · rw [hs, if_pos hc, one_mul]
      rcases lt_trichotomy (d j) 0 with hj | hj | hj
      · exact absurd (hmix j₀ j hc hj) (fun h => h)
      · exact absurd hj (hd0 j)
      · exact hj
    · have hj₀neg : d j₀ < 0 := lt_of_le_of_ne (not_lt.mp hc) (hd0 j₀)
      rw [hs, if_neg hc]
      rcases lt_trichotomy (d j) 0 with hj | hj | hj
      · linarith
      · exact absurd hj (hd0 j)
      · exact absurd (hmix j j₀ hj hj₀neg) (fun h => h)
  -- Step 7: the square root `k` and the automorphism `θ`.
  set U : Matrix n n ℂ := (hHerm.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := hHerm.eigenvectorUnitary.2.1
  have hUU' : U * star U = 1 := hHerm.eigenvectorUnitary.2.2
  set D2 : Matrix n n ℂ := Matrix.diagonal (fun j => ((Real.sqrt (s * d j) : ℝ) : ℂ)) with hD2
  set k : Matrix n n ℂ := U * D2 * star U with hk
  have hspec : h' = U * Matrix.diagonal (fun j => ((d j : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hHerm.spectral_theorem]
    rfl
  have hkk : k * k = (s : ℂ) • h' := by
    have e1 : D2 * D2 = Matrix.diagonal (fun j => (((s * d j : ℝ)) : ℂ)) := by
      rw [hD2, Matrix.diagonal_mul_diagonal]
      congr 1
      funext j
      have hj := hspos j
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hj)]
    calc k * k = U * D2 * (star U * U) * D2 * star U := by rw [hk]; noncomm_ring
      _ = U * (D2 * D2) * star U := by rw [hUU]; noncomm_ring
      _ = U * Matrix.diagonal (fun j => (((s * d j : ℝ)) : ℂ)) * star U := by rw [e1]
      _ = (s : ℂ) • (U * Matrix.diagonal (fun j => ((d j : ℝ) : ℂ)) * star U) := by
            rw [show Matrix.diagonal (fun j => (((s * d j : ℝ)) : ℂ))
                  = (s : ℂ) • Matrix.diagonal (fun j => ((d j : ℝ) : ℂ)) by
                rw [← Matrix.diagonal_smul]
                congr 1
                funext j
                simp only [Pi.smul_apply, smul_eq_mul]
                push_cast
                ring]
            rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (s : ℂ) • h' := by rw [← hspec]
  have hsne : (s : ℂ) ≠ 0 := by
    have := hspos j₀
    have hs0 : s ≠ 0 := by intro h0; rw [h0, zero_mul] at this; exact lt_irrefl 0 this
    exact_mod_cast hs0
  have hD2star : star D2 = D2 := by
    rw [hD2, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    simp
  have hkstar : star k = k := by
    rw [hk, star_mul, star_mul, star_star, hD2star]
    noncomm_ring
  have hkunit : IsUnit k := by
    have hh'unit : IsUnit h' := ⟨⟨h', g, hg2, hg1⟩, rfl⟩
    have h1 : IsUnit (k * k) := by
      rw [hkk]
      refine ⟨⟨(s : ℂ) • h', (s : ℂ)⁻¹ • g, ?_, ?_⟩, rfl⟩
      · rw [smul_mul_smul_comm, hg2, mul_inv_cancel₀ hsne, one_smul]
      · rw [smul_mul_smul_comm, hg1, inv_mul_cancel₀ hsne, one_smul]
    rw [Matrix.isUnit_iff_isUnit_det] at h1 ⊢
    rw [Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  have hkdet : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det k).mp hkunit
  have hkl : k⁻¹ * k = 1 := Matrix.nonsing_inv_mul k hkdet
  have hkr : k * k⁻¹ = 1 := Matrix.mul_nonsing_inv k hkdet
  have hkistar : star k⁻¹ = k⁻¹ := by
    have e0 : star k⁻¹ * k = 1 := by
      have e00 : star k⁻¹ * star k = star (k * k⁻¹) := (star_mul _ _).symm
      rw [hkstar] at e00
      rw [e00, hkr, star_one]
    calc star k⁻¹ = star k⁻¹ * (k * k⁻¹) := by rw [hkr, mul_one]
      _ = (star k⁻¹ * k) * k⁻¹ := (mul_assoc _ _ _).symm
      _ = k⁻¹ := by rw [e0, one_mul]
  have hkrel : ∀ x, (k * k) * J x = star x * (k * k) := by
    intro x
    calc (k * k) * J x = ((s : ℂ) • h') * J x := by rw [hkk]
      _ = (s : ℂ) • (h' * J x) := smul_mul_assoc _ _ _
      _ = (s : ℂ) • (star x * h') := by rw [hrel']
      _ = star x * ((s : ℂ) • h') := (mul_smul_comm _ _ _).symm
      _ = star x * (k * k) := by rw [hkk]
  refine ⟨{ toFun := fun x => k * x * k⁻¹
            invFun := fun y => k⁻¹ * y * k
            left_inv := by
              intro x
              show k⁻¹ * (k * x * k⁻¹) * k = x
              calc k⁻¹ * (k * x * k⁻¹) * k = (k⁻¹ * k) * x * (k⁻¹ * k) := by noncomm_ring
                _ = x := by rw [hkl, one_mul, mul_one]
            right_inv := by
              intro y
              show k * (k⁻¹ * y * k) * k⁻¹ = y
              calc k * (k⁻¹ * y * k) * k⁻¹ = (k * k⁻¹) * y * (k * k⁻¹) := by noncomm_ring
                _ = y := by rw [hkr, one_mul, mul_one]
            map_mul' := by
              intro x y
              show k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹)
              calc k * (x * y) * k⁻¹ = k * x * (k⁻¹ * k) * y * k⁻¹ := by
                    rw [hkl]; noncomm_ring
                _ = (k * x * k⁻¹) * (k * y * k⁻¹) := by noncomm_ring
            map_add' := by
              intro x y
              show k * (x + y) * k⁻¹ = k * x * k⁻¹ + k * y * k⁻¹
              noncomm_ring
            commutes' := by
              intro c
              show k * (algebraMap ℂ (Matrix n n ℂ) c) * k⁻¹ = algebraMap ℂ (Matrix n n ℂ) c
              rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, mul_one,
                Matrix.smul_mul, hkr] }, ?_⟩
  intro x
  show k * J x * k⁻¹ = star (k * x * k⁻¹)
  rw [star_mul, star_mul, hkstar, hkistar]
  have e1 : k * J x = k⁻¹ * (star x * (k * k)) := by
    rw [← hkrel, ← mul_assoc, ← mul_assoc, hkl, one_mul]
  calc k * J x * k⁻¹ = (k⁻¹ * (star x * (k * k))) * k⁻¹ := by rw [e1]
    _ = k⁻¹ * star x * k * (k * k⁻¹) := by noncomm_ring
    _ = k⁻¹ * (star x * k) := by rw [hkr, mul_one, mul_assoc]

/-- A central idempotent of a C*-algebra is self-adjoint. -/
private theorem central_idempotent_isSelfAdjoint {R : Type u} [CStarAlgebra R] (z : R)
    (hz : z * z = z) (hcen : ∀ a : R, z * a = a * z) : star z = z := by
  have hidem : IsIdempotentElem z := hz
  have hnormal : IsStarNormal z := ⟨(hcen (star z)).symm⟩
  exact (hidem.isSelfAdjoint_iff_isStarNormal.mpr hnormal).star_eq


/-- Abbreviation for the target of `fdcstar`: a finite product of full matrix
algebras.  Reducible, so that instance search and `simp` see through it. -/
private abbrev MatProd (M : ℕ) (N : Fin M → ℕ) :=
  ∀ m : Fin M, Matrix (Fin (N m)) (Fin (N m)) ℂ

/-- **84II** (`fdcstar`, vn.tex:5784, Theorem): every finite-dimensional
C*-algebra is (miu-isomorphic to) a finite direct sum of full matrix
algebras `⊕ₘ M_{Nₘ}`. -/
theorem fdcstar (A : Type u) [CStarAlgebra A] [FiniteDimensional ℂ A] :
    ∃ (M : ℕ) (N : Fin M → ℕ),
      Nonempty (A ≃⋆ₐ[ℂ] ∀ m : Fin M, Matrix (Fin (N m)) (Fin (N m)) ℂ) := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite ℂ A
  have : IsSemisimpleRing A :=
    IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr (cstar_jacobson_eq_bot A)
  obtain ⟨M, N, hN, ⟨φ⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ A
  refine ⟨M, N, ?_⟩
  set J : (MatProd M N) →
      (MatProd M N) := fun y => φ (star (φ.symm y)) with hJ
  have hJsymm : ∀ y, φ.symm (J y) = star (φ.symm y) := by
    intro y; rw [hJ]; simp
  have hJadd : ∀ x y, J (x + y) = J x + J y := by
    intro x y; rw [hJ]; simp
  have hJsmul : ∀ (c : ℂ) x, J (c • x) = (starRingEnd ℂ) c • J x := by
    intro c x; rw [hJ]; simp
  have hJmul : ∀ x y, J (x * y) = J y * J x := by
    intro x y; rw [hJ]; simp [star_mul]
  have hJone : J 1 = 1 := by rw [hJ]; simp
  have hJinvol : ∀ x, J (J x) = x := by
    intro x; rw [hJ]; simp
  have hJdef : ∀ y, J y * y = 0 → y = 0 := by
    intro y hy
    have h1 : star (φ.symm y) * φ.symm y = 0 := by
      rw [← hJsymm, ← map_mul, hy, map_zero]
    have := (CStarRing.star_mul_self_eq_zero_iff _).mp h1
    simpa using congrArg φ this
  -- `J` fixes each block unit
  have hJe : ∀ m : Fin M, J (Pi.single m 1) = Pi.single m 1 := by
    intro m
    have hsa : star (φ.symm (Pi.single m 1 : MatProd M N))
        = φ.symm (Pi.single m 1 : MatProd M N) := by
      refine central_idempotent_isSelfAdjoint _ ?_ ?_
      · rw [← map_mul]
        congr 1
        funext m'
        rcases eq_or_ne m m' with rfl | h
        · simp [Pi.mul_apply]
        · simp [Pi.mul_apply, Pi.single_eq_of_ne (Ne.symm h)]
      · intro a
        have e0 : (Pi.single m 1 : MatProd M N) * φ a = φ a * Pi.single m 1 := by
          funext m'
          rcases eq_or_ne m m' with rfl | h
          · simp [Pi.mul_apply]
          · simp [Pi.mul_apply, Pi.single_eq_of_ne (Ne.symm h)]
        calc φ.symm (Pi.single m 1 : MatProd M N) * a
            = φ.symm ((Pi.single m 1 : MatProd M N) * φ a) := by simp
          _ = φ.symm (φ a * (Pi.single m 1 : MatProd M N)) := by rw [e0]
          _ = a * φ.symm (Pi.single m 1 : MatProd M N) := by simp
    rw [hJ]
    show φ (star (φ.symm (Pi.single m 1 : MatProd M N))) = Pi.single m 1
    rw [hsa]
    simp
  -- block components of `J`
  set Jm : ∀ m : Fin M, Matrix (Fin (N m)) (Fin (N m)) ℂ → Matrix (Fin (N m)) (Fin (N m)) ℂ :=
    fun m x => (J (Pi.single m x)) m with hJm
  have hJzero : J 0 = 0 := by rw [hJ]; simp
  have hsingle_mul : ∀ (m : Fin M) (y : MatProd M N),
      (Pi.single m 1 : MatProd M N) * y = Pi.single m (y m) := by
    intro m y
    funext m'
    rcases eq_or_ne m m' with rfl | h
    · simp [Pi.mul_apply]
    · simp [Pi.mul_apply, Pi.single_eq_of_ne (Ne.symm h)]
  have hmul_single : ∀ (m : Fin M) (y : MatProd M N),
      y * (Pi.single m 1 : MatProd M N) = Pi.single m (y m) := by
    intro m y
    funext m'
    rcases eq_or_ne m m' with rfl | h
    · simp [Pi.mul_apply]
    · simp [Pi.mul_apply, Pi.single_eq_of_ne (Ne.symm h)]
  have hsingle_mul_single : ∀ (m : Fin M) (x y : Matrix (Fin (N m)) (Fin (N m)) ℂ),
      (Pi.single m x : MatProd M N) * Pi.single m y = Pi.single m (x * y) := by
    intro m x y
    funext m'
    rcases eq_or_ne m m' with rfl | h
    · simp [Pi.mul_apply]
    · simp [Pi.mul_apply, Pi.single_eq_of_ne (Ne.symm h)]
  have hJblock : ∀ (m : Fin M) (y : MatProd M N), (J y) m = Jm m (y m) := by
    intro m y
    have e1 : J (Pi.single m (y m)) = (Pi.single m 1 : MatProd M N) * J y := by
      rw [← hmul_single m y, hJmul, hJe]
    show (J y) m = (J (Pi.single m (y m))) m
    rw [e1, hsingle_mul]
    simp
  have hJmzero : ∀ m : Fin M, Jm m 0 = 0 := by
    intro m
    show (J (Pi.single m (0 : Matrix (Fin (N m)) (Fin (N m)) ℂ))) m = 0
    rw [Pi.single_zero, hJzero]
    rfl
  have hJsingle : ∀ (m : Fin M) (x : Matrix (Fin (N m)) (Fin (N m)) ℂ),
      J (Pi.single m x) = Pi.single m (Jm m x) := by
    intro m x
    funext m'
    rw [hJblock m' (Pi.single m x)]
    rcases eq_or_ne m m' with rfl | h
    · simp
    · rw [Pi.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne (Ne.symm h), hJmzero]
  have hθ : ∀ m : Fin M, ∃ θ : Matrix (Fin (N m)) (Fin (N m)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (N m)) (Fin (N m)) ℂ, ∀ x, θ (Jm m x) = star (θ x) := by
    intro m
    have : Nonempty (Fin (N m)) := ⟨⟨0, Nat.pos_of_ne_zero (hN m).1⟩⟩
    refine matrix_exists_algEquiv_conj (Jm m) ?_ ?_ ?_ ?_ ?_ ?_
    · intro x y
      show (J (Pi.single m (x + y))) m = (J (Pi.single m x)) m + (J (Pi.single m y)) m
      rw [Pi.single_add, hJadd]
      rfl
    · intro c x
      show (J (Pi.single m (c • x))) m = (starRingEnd ℂ) c • (J (Pi.single m x)) m
      rw [Pi.single_smul, hJsmul]
      rfl
    · intro x y
      show (J (Pi.single m (x * y))) m = (J (Pi.single m y)) m * (J (Pi.single m x)) m
      rw [← hsingle_mul_single, hJmul]
      rfl
    · show (J (Pi.single m 1)) m = 1
      rw [hJe]
      simp
    · intro x
      have e2 := hJinvol (Pi.single m x)
      rw [hJsingle, hJsingle] at e2
      have e3 := congrFun e2 m
      simpa using e3
    · intro x hx
      have e1 : J (Pi.single m x) * (Pi.single m x : MatProd M N) = 0 := by
        rw [hJsingle, hsingle_mul_single, hx, Pi.single_zero]
      have e2 := hJdef _ e1
      have e3 := congrFun e2 m
      simpa using e3
  choose θ hθ using hθ
  refine ⟨?_⟩
  refine StarAlgEquiv.ofAlgEquiv (φ.trans
    { toFun := fun y m => θ m (y m)
      invFun := fun y m => (θ m).symm (y m)
      left_inv := fun y => funext fun m => (θ m).symm_apply_apply (y m)
      right_inv := fun y => funext fun m => (θ m).apply_symm_apply (y m)
      map_mul' := fun x y => funext fun m => map_mul (θ m) _ _
      map_add' := fun x y => funext fun m => map_add (θ m) _ _
      commutes' := fun c => funext fun m => by
        simp only [Pi.algebraMap_apply]
        exact (θ m).commutes c }) ?_
  intro a
  have e1 : φ (star a) = J (φ a) := by rw [hJ]; simp
  show (fun m => θ m ((φ (star a)) m)) = star (fun m => θ m ((φ a) m))
  funext m
  rw [e1, hJblock, hθ m]
  rfl

end FDCStar

/-! ## Parsec 841: `CStar_pu` has no equaliser for `f, g : ℂ⁴ → ℂ` -/

section NoPUEqualisers

/-- **84aI** (`cstar-no-pu-equalisers-example`, vn.tex:6034, Example): the
map `f : ℂ⁴ → ℂ`, `f(a,b,c,d) = ½(a+b)`.  Pu-maps are rendered as everywhere
else in the tree (cf. **20aI** `cstar_product_2_pu`): a linear map together
with `IsPositiveMap` and `IsUnitalMap` — see `puEqualiserF_isPositiveMap`
and `puEqualiserF_isUnitalMap`. -/
noncomputable def puEqualiserF : (Fin 4 → ℂ) →ₗ[ℂ] ℂ where
  toFun v := (v 0 + v 1) / 2
  map_add' u v := by simp only [Pi.add_apply]; ring
  map_smul' c v := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- **84aI** (`cstar-no-pu-equalisers-example`, vn.tex:6034, Example): the
map `g : ℂ⁴ → ℂ`, `g(a,b,c,d) = ½(c+d)`. -/
noncomputable def puEqualiserG : (Fin 4 → ℂ) →ₗ[ℂ] ℂ where
  toFun v := (v 2 + v 3) / 2
  map_add' u v := by simp only [Pi.add_apply]; ring
  map_smul' c v := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- **84aI**: `f` is positive, so that it is a pu-map. -/
theorem puEqualiserF_isPositiveMap : IsPositiveMap puEqualiserF := by
  intro v hv
  show (0 : ℂ) ≤ (v 0 + v 1) / 2
  exact div_nonneg (add_nonneg (hv 0) (hv 1)) (by norm_num)

/-- **84aI**: `g` is positive, so that it is a pu-map. -/
theorem puEqualiserG_isPositiveMap : IsPositiveMap puEqualiserG := by
  intro v hv
  show (0 : ℂ) ≤ (v 2 + v 3) / 2
  exact div_nonneg (add_nonneg (hv 2) (hv 3)) (by norm_num)

/-- **84aI**: `f` is unital, so that it is a pu-map. -/
theorem puEqualiserF_isUnitalMap : IsUnitalMap puEqualiserF := by
  show ((1 : Fin 4 → ℂ) 0 + (1 : Fin 4 → ℂ) 1) / 2 = 1
  norm_num

/-- **84aI**: `g` is unital, so that it is a pu-map. -/
theorem puEqualiserG_isUnitalMap : IsUnitalMap puEqualiserG := by
  show ((1 : Fin 4 → ℂ) 2 + (1 : Fin 4 → ℂ) 3) / 2 = 1
  norm_num

/-- Auxiliary for **84aI**, not a transcription: the pu-map `ℂ² → 𝒟`
determined by an effect `a ∈ [0,1]_𝒟`, namely `(z,w) ↦ z a + w a^⊥`.  This
is the correspondence "pu-maps `ℂ² → 𝒟` = effects of `𝒟`" that the Example's
proof uses twice: once to see that the range of a would-be equaliser is the
whole set-theoretic equaliser, and once to see that a would-be equaliser is
injective on effects (the thesis says "equalisers are mono"). -/
private def effectPUMap {D : Type} [CStarAlgebra D] (a : D) : (Fin 2 → ℂ) →ₗ[ℂ] D where
  toFun z := z 0 • a + z 1 • (1 - a)
  map_add' x y := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, smul_add]

/-- Auxiliary for **84aI**. -/
private theorem effectPUMap_apply {D : Type} [CStarAlgebra D] (a : D) (z : Fin 2 → ℂ) :
    effectPUMap a z = z 0 • a + z 1 • (1 - a) := rfl

/-- Auxiliary for **84aI**: `p_a(1,1) = a + a^⊥ = 1`. -/
private theorem effectPUMap_isUnitalMap {D : Type} [CStarAlgebra D] (a : D) :
    IsUnitalMap (effectPUMap a) := by
  show (1 : Fin 2 → ℂ) 0 • a + (1 : Fin 2 → ℂ) 1 • (1 - a) = 1
  simp

/-- Auxiliary for **84aI**: a positive complex multiple of a positive
element is positive (**9X**.1 `cstar_positive_1` for a complex scalar that
happens to be positive, hence real). -/
private theorem nonneg_smul_nonneg {D : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    {z : ℂ} (hz : 0 ≤ z) {a : D} (ha : 0 ≤ a) : 0 ≤ z • a := by
  have h := Complex.le_def.mp hz
  have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simp [← h.2])
  rw [hz']
  exact cstar_positive_1 a ha z.re (by simpa using h.1)

/-- Auxiliary for **84aI**: `p_a` is positive, `a` and `a^⊥` being. -/
private theorem effectPUMap_isPositiveMap {D : Type} [CStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] {a : D} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IsPositiveMap (effectPUMap a) := by
  intro z hz
  show 0 ≤ z 0 • a + z 1 • (1 - a)
  exact add_nonneg (nonneg_smul_nonneg (hz 0) ha0)
    (nonneg_smul_nonneg (hz 1) (sub_nonneg.mpr ha1))

/-- **84aI** (`cstar-no-pu-equalisers-example`, vn.tex:6034, Example): the
pu-maps `f, g : ℂ⁴ → ℂ` of `puEqualiserF`, `puEqualiserG` have **no
equaliser in `CStar_pu`** — which is the claim made at the very start of
thesis A, **20aIII** (`cstar-no-pu-equalisers`, cstar.tex:3073).

`CStar_pu` is not bundled as a category (cf. **47II**), so — exactly as for
**84bV** `ha_equalisers` — the universal property is spelt out: an equaliser
would be a C*-algebra `ℰ` with a pu-map `e : ℰ → ℂ⁴` equalising `f` and `g`
through which every pu-map `h : 𝒟 → ℂ⁴` equalising `f` and `g` factors
uniquely by a pu-map.  The Example says there is no such `ℰ, e`.  The
universe is `Type`, where `ℂ⁴` and the `ℂ²` used in the proof live; nothing
in the argument depends on that choice.

*Class 2 — different route.*  The thesis argues by counting extreme points:
`e(ℰ)` is the set-theoretic equaliser `𝒮`, `e` is a bipositive linear
isomorphism onto it, so `ℰ` is 3-dimensional, hence miu-isomorphic to `ℂ³`
by **84II** `fdcstar`, and then `[0,1]_ℰ` is a cube (8 extreme points) while
`𝒮 ∩ [0,1]` is an octahedron (6).  Formalized here is the same
contradiction, reached without the classification and without extreme
points: keeping the thesis's first two steps in the form they are needed —
every effect of `𝒮` is `e P` for an effect `P` of `ℰ`, and `e` is injective
on the effects, both by the universal property applied to `ℂ²` (injectivity
everywhere then follows by shifting and scaling a self-adjoint element into
`[0,1]`) — take `P, Q ∈ ℰ` over the two octahedron vertices
`r₁ = (1,0,1,0)` and `r₂ = (1,0,0,1)`.  Both are
projections, because `R - R²` is positive for an effect `R` and `e` sends it
into `𝒮` below both `e R` and `1 - e R`, which for `e R = r₁, r₂` leaves
only `0`.  Injectivity of `e` then puts `PQ` in the span of `1, P, Q` — this
is what replaces the dimension count, since `𝒮` is spanned by `1, r₁, r₂` —
say `PQ = α + βP + γQ`; and reading off the second and fourth coordinates of
`0 ≤ PQP ≤ P` gives `γ = 0`, the second and third of `0 ≤ QPQ ≤ Q` give
`β = 0`, and then `α = 0`.  So `PQ = QP = 0`, `1 - P - Q` is a projection
and hence positive, while `e(1 - P - Q) = (-1,1,0,0)` is not. -/
theorem cstar_no_pu_equalisers_example :
    ¬ ∃ (E : Type) (_ : CStarAlgebra E) (_ : PartialOrder E) (_ : StarOrderedRing E)
        (e : E →ₗ[ℂ] (Fin 4 → ℂ)),
      IsPositiveMap e ∧ IsUnitalMap e ∧
      (∀ x : E, puEqualiserF (e x) = puEqualiserG (e x)) ∧
      (∀ (D : Type) (_ : CStarAlgebra D) (_ : PartialOrder D) (_ : StarOrderedRing D)
          (h : D →ₗ[ℂ] (Fin 4 → ℂ)), IsPositiveMap h → IsUnitalMap h →
          (∀ d : D, puEqualiserF (h d) = puEqualiserG (h d)) →
          ∃! m : D →ₗ[ℂ] E, IsPositiveMap m ∧ IsUnitalMap m ∧ ∀ d : D, e (m d) = h d) := by
  rintro ⟨E, _, _, _, e, hep, heu, heq, huniv⟩
  -- `e` is monotone
  have hmono : ∀ x y : E, x ≤ y → e x ≤ e y := by
    intro x y hxy
    have h := hep _ (sub_nonneg.mpr hxy)
    rw [map_sub] at h
    exact sub_nonneg.mp h
  -- the range of `e` lies in the set-theoretic equaliser `𝒮`
  have hS : ∀ x : E, e x 0 + e x 1 = e x 2 + e x 3 := by
    intro x
    have h := heq x
    simp only [puEqualiserF, puEqualiserG, LinearMap.coe_mk, AddHom.coe_mk] at h
    linear_combination 2 * h
  -- every effect of `𝒮` is `e P` for an effect `P` of `E`
  have hsurj : ∀ v : Fin 4 → ℂ, 0 ≤ v → v ≤ 1 → v 0 + v 1 = v 2 + v 3 →
      ∃ P : E, 0 ≤ P ∧ P ≤ 1 ∧ e P = v := by
    intro v hv0 hv1 hvS
    have hpe : ∀ d : Fin 2 → ℂ,
        puEqualiserF (effectPUMap v d) = puEqualiserG (effectPUMap v d) := by
      intro d
      show ((effectPUMap v d) 0 + (effectPUMap v d) 1) / 2
          = ((effectPUMap v d) 2 + (effectPUMap v d) 3) / 2
      simp only [effectPUMap_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply,
        smul_eq_mul]
      linear_combination (d 0 - d 1) / 2 * hvS
    obtain ⟨m, ⟨hmp, hmu, hme⟩, -⟩ :=
      huniv (Fin 2 → ℂ) inferInstance inferInstance inferInstance (effectPUMap v)
        (effectPUMap_isPositiveMap hv0 hv1) (effectPUMap_isUnitalMap v) hpe
    refine ⟨m ![1, 0], hmp _ (by intro i; fin_cases i <;> simp), ?_, ?_⟩
    · have hone : (1 : Fin 2 → ℂ) - ![1, 0] = ![0, 1] := by
        ext i; fin_cases i <;> simp
      have h0 : (0 : E) ≤ m ![0, 1] := hmp _ (by intro i; fin_cases i <;> simp)
      rw [← hone, map_sub, hmu] at h0
      exact sub_nonneg.mp h0
    · rw [hme ![1, 0], effectPUMap_apply]
      simp
  -- `e` is injective on the effects
  have hinj01 : ∀ a b : E, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → e a = e b → a = b := by
    intro a b ha0 ha1 hb0 hb1 hab
    have hpa : IsPositiveMap (e.comp (effectPUMap a)) := fun z hz =>
      hep _ (effectPUMap_isPositiveMap ha0 ha1 z hz)
    have hua : IsUnitalMap (e.comp (effectPUMap a)) := by
      show e (effectPUMap a 1) = 1
      rw [effectPUMap_isUnitalMap a]
      exact heu
    obtain ⟨m, -, hmuniq⟩ := huniv (Fin 2 → ℂ) inferInstance inferInstance inferInstance
      (e.comp (effectPUMap a)) hpa hua (fun d => heq _)
    have h1 : effectPUMap a = m :=
      hmuniq _ ⟨effectPUMap_isPositiveMap ha0 ha1, effectPUMap_isUnitalMap a, fun d => rfl⟩
    have h2 : effectPUMap b = m := by
      refine hmuniq _ ⟨effectPUMap_isPositiveMap hb0 hb1, effectPUMap_isUnitalMap b, fun d => ?_⟩
      show e (d 0 • b + d 1 • (1 - b)) = e (d 0 • a + d 1 • (1 - a))
      rw [map_add, map_add, map_smul, map_smul, map_smul, map_smul, map_sub, map_sub, hab]
    have h3 := h1.trans h2.symm
    have h4 := congrArg (fun φ : (Fin 2 → ℂ) →ₗ[ℂ] E => φ ![1, 0]) h3
    simpa [effectPUMap_apply] using h4
  -- `e` is injective on the self-adjoint elements
  have hinjsa : ∀ x : E, star x = x → e x = 0 → x = 0 := by
    intro x hx hex
    rcases eq_or_lt_of_le (norm_nonneg x) with ht | ht
    · exact norm_eq_zero.mp ht.symm
    obtain ⟨hone, hlo, hhi⟩ := cstar_positive_2 x hx
    have hlo' : (0 : E) ≤ x + ((‖x‖ : ℝ) : ℂ) • 1 := by
      have h := sub_nonneg.mpr hlo
      rwa [sub_neg_eq_add, Algebra.algebraMap_eq_smul_one] at h
    have hhi' : (0 : E) ≤ ((‖x‖ : ℝ) : ℂ) • 1 - x := by
      have h := sub_nonneg.mpr hhi
      rwa [Algebra.algebraMap_eq_smul_one] at h
    have hcpos : (0 : ℝ) < 1 / (2 * ‖x‖) := by positivity
    have hc2 : ((1 / (2 * ‖x‖) : ℝ) : ℂ) * ((‖x‖ : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
      push_cast
      field_simp
    have ha0 : (0 : E) ≤ ((1 / (2 * ‖x‖) : ℝ) : ℂ) • x + ((1 / 2 : ℝ) : ℂ) • (1 : E) := by
      have h := cstar_positive_1 _ hlo' (1 / (2 * ‖x‖)) hcpos.le
      rwa [smul_add, smul_smul, hc2] at h
    have ha1 : ((1 / (2 * ‖x‖) : ℝ) : ℂ) • x + ((1 / 2 : ℝ) : ℂ) • (1 : E) ≤ 1 := by
      have h := cstar_positive_1 _ hhi' (1 / (2 * ‖x‖)) hcpos.le
      rw [smul_sub, smul_smul, hc2] at h
      rw [← sub_nonneg]
      have hrw : (1 : E) - (((1 / (2 * ‖x‖) : ℝ) : ℂ) • x + ((1 / 2 : ℝ) : ℂ) • (1 : E))
          = ((1 / 2 : ℝ) : ℂ) • (1 : E) - ((1 / (2 * ‖x‖) : ℝ) : ℂ) • x := by
        push_cast
        module
      rw [hrw]
      exact h
    have hb0 : (0 : E) ≤ ((1 / 2 : ℝ) : ℂ) • (1 : E) :=
      cstar_positive_1 _ hone (1 / 2) (by norm_num)
    have hb1 : ((1 / 2 : ℝ) : ℂ) • (1 : E) ≤ 1 := by
      rw [← sub_nonneg]
      have hrw : (1 : E) - ((1 / 2 : ℝ) : ℂ) • (1 : E) = ((1 / 2 : ℝ) : ℂ) • (1 : E) := by
        push_cast; module
      rw [hrw]
      exact hb0
    have hee : e (((1 / (2 * ‖x‖) : ℝ) : ℂ) • x + ((1 / 2 : ℝ) : ℂ) • (1 : E))
        = e (((1 / 2 : ℝ) : ℂ) • (1 : E)) := by
      rw [map_add, map_smul, hex, smul_zero, zero_add]
    have hfin := hinj01 _ _ ha0 ha1 hb0 hb1 hee
    have hzero : ((1 / (2 * ‖x‖) : ℝ) : ℂ) • x = 0 := by
      have := sub_eq_zero.mpr hfin
      simpa using this
    rcases smul_eq_zero.mp hzero with h | h
    · exact absurd h (by exact_mod_cast ne_of_gt hcpos)
    · exact h
  -- `e` is injective
  have hstar : ∀ x : E, e (star x) = star (e x) := cstar_p_implies_i e hep
  have hinjf : ∀ x y : E, e x = e y → x = y := by
    intro x y hxy
    have hex : e (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    set z := x - y with hz
    have hu : star ((2 : ℂ)⁻¹ • (z + star z)) = (2 : ℂ)⁻¹ • (z + star z) := by
      rw [star_smul, star_add, star_star]
      simp [add_comm]
    have hv : star ((Complex.I / 2) • (star z - z)) = (Complex.I / 2) • (star z - z) := by
      rw [star_smul, star_sub, star_star]
      simp [sub_eq_add_neg]
      module
    have heu' : e ((2 : ℂ)⁻¹ • (z + star z)) = 0 := by
      rw [map_smul, map_add, hstar, hex, star_zero, add_zero, smul_zero]
    have hev' : e ((Complex.I / 2) • (star z - z)) = 0 := by
      rw [map_smul, map_sub, hstar, hex, star_zero, sub_zero, smul_zero]
    have h1 := hinjsa _ hu heu'
    have h2 := hinjsa _ hv hev'
    have hzz : z = (2 : ℂ)⁻¹ • (z + star z) + Complex.I • ((Complex.I / 2) • (star z - z)) := by
      rw [smul_smul, show Complex.I * (Complex.I / 2) = -(2 : ℂ)⁻¹ by
        rw [mul_div_assoc', Complex.I_mul_I]; ring]
      module
    rw [h1, h2, smul_zero, add_zero] at hzz
    exact sub_eq_zero.mp hzz
  -- coordinates of `1`, `r₁ = (1,0,1,0)` and `r₂ = (1,0,0,1)`
  have hfin4 : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  have hr10 : (![1, 0, 1, 0] : Fin 4 → ℂ) 0 = 1 := by simp
  have hr11 : (![1, 0, 1, 0] : Fin 4 → ℂ) 1 = 0 := by simp
  have hr12 : (![1, 0, 1, 0] : Fin 4 → ℂ) 2 = 1 := by simp
  have hr13 : (![1, 0, 1, 0] : Fin 4 → ℂ) 3 = 0 := by simp
  have hr20 : (![1, 0, 0, 1] : Fin 4 → ℂ) 0 = 1 := by simp
  have hr21 : (![1, 0, 0, 1] : Fin 4 → ℂ) 1 = 0 := by simp
  have hr22 : (![1, 0, 0, 1] : Fin 4 → ℂ) 2 = 0 := by simp
  have hr23 : (![1, 0, 0, 1] : Fin 4 → ℂ) 3 = 1 := by simp
  have hval : ∀ (a b c : ℂ) (i : Fin 4),
      (a • (1 : Fin 4 → ℂ) + b • (![1, 0, 1, 0] : Fin 4 → ℂ)
        + c • (![1, 0, 0, 1] : Fin 4 → ℂ)) i
        = a + b * (![1, 0, 1, 0] : Fin 4 → ℂ) i + c * (![1, 0, 0, 1] : Fin 4 → ℂ) i := by
    intro a b c i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  -- the decomposition of an element of `𝒮` along `1`, `r₁` and `r₂`
  have hdecomp : ∀ v : Fin 4 → ℂ, v 0 + v 1 = v 2 + v 3 →
      v = v 1 • (1 : Fin 4 → ℂ) + (v 2 - v 1) • (![1, 0, 1, 0] : Fin 4 → ℂ)
        + (v 3 - v 1) • (![1, 0, 0, 1] : Fin 4 → ℂ) := by
    intro v hv
    funext i
    rw [hval]
    rcases hfin4 i with rfl | rfl | rfl | rfl
    · rw [hr10, hr20]; linear_combination hv
    · rw [hr11, hr21]; ring
    · rw [hr12, hr22]; ring
    · rw [hr13, hr23]; ring
  have hcomb1 : ∀ a b c : ℂ,
      (a • (1 : Fin 4 → ℂ) + b • (![1, 0, 1, 0] : Fin 4 → ℂ)
        + c • (![1, 0, 0, 1] : Fin 4 → ℂ)) 1 = a := by
    intro a b c; rw [hval, hr11, hr21]; ring
  have hcomb2 : ∀ a b c : ℂ,
      (a • (1 : Fin 4 → ℂ) + b • (![1, 0, 1, 0] : Fin 4 → ℂ)
        + c • (![1, 0, 0, 1] : Fin 4 → ℂ)) 2 = a + b := by
    intro a b c; rw [hval, hr12, hr22]; ring
  have hcomb3 : ∀ a b c : ℂ,
      (a • (1 : Fin 4 → ℂ) + b • (![1, 0, 1, 0] : Fin 4 → ℂ)
        + c • (![1, 0, 0, 1] : Fin 4 → ℂ)) 3 = a + c := by
    intro a b c; rw [hval, hr13, hr23]; ring
  -- effects square to below themselves
  have hsq : ∀ R : E, 0 ≤ R → R ≤ 1 → 0 ≤ R - R * R := by
    intro R h0 h1
    obtain ⟨s, hsa, rfl⟩ : ∃ s : E, star s = s ∧ R = s * s :=
      ⟨CFC.sqrt R, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg R)).star_eq,
        (CFC.sqrt_mul_sqrt_self R h0).symm⟩
    have h := star_left_conjugate_nonneg (sub_nonneg.mpr h1) s
    rw [hsa] at h
    have hrw : s * (1 - s * s) * s = s * s - s * s * (s * s) := by noncomm_ring
    rwa [hrw] at h
  -- an effect whose image is sharp in every coordinate is a projection
  have hidem : ∀ R : E, 0 ≤ R → R ≤ 1 → (∀ i, e R i = 0 ∨ e R i = 1) → R * R = R := by
    intro R h0 h1 hv
    have hRsa : star R = R := (IsSelfAdjoint.of_nonneg h0).star_eq
    have hb0 : (0 : E) ≤ R - R * R := hsq R h0 h1
    have hRR : (0 : E) ≤ R * R := by
      have h := star_mul_self_nonneg R
      rwa [hRsa] at h
    have hb1 : R - R * R ≤ R := sub_le_self R hRR
    have hb2 : R - R * R ≤ 1 - R := by
      have h : (0 : E) ≤ (1 - R) * (1 - R) := by
        have h' := star_mul_self_nonneg (1 - R)
        rwa [star_sub, star_one, hRsa] at h'
      have hrw : (1 - R) - (R - R * R) = (1 - R) * (1 - R) := by noncomm_ring
      exact sub_nonneg.mp (hrw ▸ h)
    have he0 := hep _ hb0
    have he1 := hmono _ _ hb1
    have he2 := hmono _ _ hb2
    have heR : e (1 - R) = 1 - e R := by rw [map_sub, heu]
    rw [heR] at he2
    have hzero : e (R - R * R) = 0 := by
      funext i
      have hl := he0 i
      simp only [Pi.zero_apply] at hl
      rcases hv i with hvi | hvi
      · have hr := he1 i
        rw [hvi] at hr
        exact le_antisymm hr hl
      · have hr := he2 i
        simp only [Pi.sub_apply, Pi.one_apply, hvi, sub_self] at hr
        exact le_antisymm hr hl
    have hb := hinjf _ 0 (by rw [hzero, map_zero])
    exact (sub_eq_zero.mp hb).symm
  -- the two effects `P`, `Q` of `E` over `r₁` and `r₂`
  obtain ⟨P, hP0, hP1, hPe⟩ := hsurj ![1, 0, 1, 0] (by intro i; fin_cases i <;> simp)
    (by intro i; fin_cases i <;> simp) (by simp)
  obtain ⟨Q, hQ0, hQ1, hQe⟩ := hsurj ![1, 0, 0, 1] (by intro i; fin_cases i <;> simp)
    (by intro i; fin_cases i <;> simp) (by simp)
  have hPe1 : e P 1 = 0 := by rw [hPe]; simp
  have hPe3 : e P 3 = 0 := by rw [hPe]; simp
  have hQe1 : e Q 1 = 0 := by rw [hQe]; simp
  have hQe2 : e Q 2 = 0 := by rw [hQe]; simp
  have hPP : P * P = P := hidem P hP0 hP1 (by intro i; rw [hPe]; fin_cases i <;> simp)
  have hQQ : Q * Q = Q := hidem Q hQ0 hQ1 (by intro i; rw [hQe]; fin_cases i <;> simp)
  have hPsa : star P = P := (IsSelfAdjoint.of_nonneg hP0).star_eq
  have hQsa : star Q = Q := (IsSelfAdjoint.of_nonneg hQ0).star_eq
  -- `PQ` is a linear combination of `1`, `P`, `Q`
  obtain ⟨α, β, γ, hPQ⟩ : ∃ α β γ : ℂ, P * Q = α • (1 : E) + β • P + γ • Q := by
    refine ⟨e (P * Q) 1, e (P * Q) 2 - e (P * Q) 1, e (P * Q) 3 - e (P * Q) 1, hinjf _ _ ?_⟩
    rw [map_add, map_add, map_smul, map_smul, map_smul, heu, hPe, hQe]
    exact hdecomp (e (P * Q)) (hS (P * Q))
  have hQP : Q * P = star α • (1 : E) + star β • P + star γ • Q := by
    have h := congrArg star hPQ
    rw [star_mul, hPsa, hQsa] at h
    rw [h]
    simp [star_add, star_smul, hPsa, hQsa]
  -- `PQP` is positive and below `P`, which forces `γ = 0`
  have hPQP : P * Q * P
      = (star γ * α) • (1 : E) + (star α + star β + star γ * β) • P + (star γ * γ) • Q := by
    calc P * Q * P = P * (Q * P) := mul_assoc _ _ _
      _ = P * (star α • (1 : E) + star β • P + star γ • Q) := by rw [hQP]
      _ = star α • P + star β • (P * P) + star γ • (P * Q) := by
            rw [mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm, mul_one]
      _ = star α • P + star β • P + star γ • (α • (1 : E) + β • P + γ • Q) := by
            rw [hPP, hPQ]
      _ = _ := by module
  have hPQPnn : (0 : E) ≤ P * Q * P := by
    have h := star_left_conjugate_nonneg hQ0 P
    rwa [hPsa] at h
  have hPQPle : P * Q * P ≤ P := by
    have h := star_left_conjugate_le_conjugate hQ1 P
    rwa [hPsa, mul_one, hPP] at h
  have hePQP : e (P * Q * P)
      = (star γ * α) • (1 : Fin 4 → ℂ) + (star α + star β + star γ * β) • ![1, 0, 1, 0]
        + (star γ * γ) • ![1, 0, 0, 1] := by
    rw [hPQP, map_add, map_add, map_smul, map_smul, map_smul, heu, hPe, hQe]
  have hga : star γ * α = 0 := by
    have hlo := (hep _ hPQPnn) 1
    have hhi := (hmono _ _ hPQPle) 1
    simp only [Pi.zero_apply] at hlo
    rw [hePQP, hcomb1] at hlo hhi
    rw [hPe1] at hhi
    exact le_antisymm hhi hlo
  have hgam : γ = 0 := by
    have hhi := (hmono _ _ hPQPle) 3
    rw [hePQP, hcomb3, hPe3, hga, zero_add] at hhi
    exact astara_non_negative γ hhi
  -- `QPQ` is positive and below `Q`, which forces `β = 0`
  have hQPQ : Q * P * Q
      = (star β * α) • (1 : E) + (star β * β) • P + (star α + star β * γ + star γ) • Q := by
    calc Q * P * Q = (star α • (1 : E) + star β • P + star γ • Q) * Q := by rw [hQP]
      _ = star α • Q + star β • (P * Q) + star γ • (Q * Q) := by
            rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, one_mul]
      _ = star α • Q + star β • (α • (1 : E) + β • P + γ • Q) + star γ • Q := by
            rw [hPQ, hQQ]
      _ = _ := by module
  have hQPQnn : (0 : E) ≤ Q * P * Q := by
    have h := star_left_conjugate_nonneg hP0 Q
    rwa [hQsa] at h
  have hQPQle : Q * P * Q ≤ Q := by
    have h := star_left_conjugate_le_conjugate hP1 Q
    rwa [hQsa, mul_one, hQQ] at h
  have heQPQ : e (Q * P * Q)
      = (star β * α) • (1 : Fin 4 → ℂ) + (star β * β) • ![1, 0, 1, 0]
        + (star α + star β * γ + star γ) • ![1, 0, 0, 1] := by
    rw [hQPQ, map_add, map_add, map_smul, map_smul, map_smul, heu, hPe, hQe]
  have hba : star β * α = 0 := by
    have hlo := (hep _ hQPQnn) 1
    have hhi := (hmono _ _ hQPQle) 1
    simp only [Pi.zero_apply] at hlo
    rw [heQPQ, hcomb1] at hlo hhi
    rw [hQe1] at hhi
    exact le_antisymm hhi hlo
  have hbet : β = 0 := by
    have hhi := (hmono _ _ hQPQle) 2
    rw [heQPQ, hcomb2, hQe2, hba, zero_add] at hhi
    exact astara_non_negative β hhi
  -- hence `PQ` is a scalar, and in fact `PQ = 0`
  rw [hbet, hgam, zero_smul, zero_smul, add_zero, add_zero] at hPQ
  have halp : α = 0 := by
    have h : P * (P * Q) = P * Q := by rw [← mul_assoc, hPP]
    rw [hPQ, mul_smul_comm, mul_one] at h
    have h2 := congrArg e h
    rw [map_smul, map_smul, heu] at h2
    have h3 := congrFun h2 1
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at h3
    rw [hPe1, mul_zero] at h3
    exact h3.symm
  rw [halp, zero_smul] at hPQ
  have hQP0 : Q * P = 0 := by
    have h := congrArg star hPQ
    rwa [star_mul, hPsa, hQsa, star_zero] at h
  -- so `P + Q` is a projection, whence `P + Q ≤ 1` -- which `e` refutes
  have hnsa : star (1 - P - Q) = 1 - P - Q := by
    rw [star_sub, star_sub, star_one, hPsa, hQsa]
  have hnn : (0 : E) ≤ 1 - P - Q := by
    have h := star_mul_self_nonneg (1 - P - Q)
    rw [hnsa] at h
    have hrw : (1 - P - Q) * (1 - P - Q) = 1 - P - Q := by
      have hexp : (1 - P - Q) * (1 - P - Q)
          = 1 - P - P - Q - Q + P * P + Q * Q + P * Q + Q * P := by noncomm_ring
      rw [hexp, hPP, hQQ, hPQ, hQP0]
      abel
    rwa [hrw] at h
  have hfin := (hep _ hnn) 0
  rw [map_sub, map_sub, heu, hPe, hQe] at hfin
  simp only [Pi.zero_apply, Pi.sub_apply, Pi.one_apply] at hfin
  rw [hr10, hr20] at hfin
  norm_num at hfin

end NoPUEqualisers

/-! ## Parsec 842: hereditarily atomic von Neumann algebras

**84bI** (vn.tex:6129): introduction (Kornell's programme) — nothing to
formalize. -/

variable (A) in
/-- **84bII** (`def:hereditarily-atomic`, vn.tex:6171, Definition): a von
Neumann algebra is **hereditarily atomic** if it is nmiu-isomorphic to a
direct sum `⊕ᵢ M_{Nᵢ}` of (possibly infinitely many) full matrix algebras.
(The summands are rendered as `M_{Nᵢ₊₁}` to keep them nontrivial, which
loses no generality.  The full subcategories `haW*_miu`, `haW*_cpsu` are
not bundled, cf. 47II.) -/
def HereditarilyAtomic : Prop :=
  ∃ (I : Type u) (N : I → ℕ),
    Nonempty (A ≃⋆ₐ[ℂ]
      lp (fun i : I => CStarMatrix (Fin (N i + 1)) (Fin (N i + 1)) ℂ) ∞)

/-! ## Von Neumann subalgebras as bundled algebras

`VNSub A S hS` bundles a von Neumann subalgebra `S ⊆ A` as a von Neumann
algebra in its own right.  It is what makes the *relative* forms of the
comparison theory of parsecs 600–830 available: results such as **83V**
`cceil-sum` are proved for a von Neumann algebra **as a type**, while the
thesis applies them inside `ϱ(𝒜)^□`, which here is a subalgebra-as-a-set
(see `cceil_sum_relative` below, which **89IX** needs).

⚠️ `A/Proc/Tensor.lean` carries a verbatim copy of this block.  It is
*downstream* of this file and can import the definition from here, so its
copy should be deleted by whoever next touches that file; until then a name
in the current namespace takes precedence over one reached through `open`, so
`Theses.A.Proc.VNSub` wins inside `A/Proc` (the same manoeuvre as for
`CU`). -/

noncomputable section VNSubalgebra


variable (A) in
/-- Wrapper: a von Neumann subalgebra `S ⊆ A` bundled as an algebra in its
own right, with proved instances (cf. `Corner` in `Measurement.lean`).
The witness `hS : IsVNSubalgebra A S` (42V, `A/VN/Basic.lean`) is carried
as an index: a bare `StarSubalgebra ℂ A` need not be norm-closed, hence
need not be complete, hence need not be a C*-algebra at all. -/
structure VNSub (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S) :
    Type u where
  val : A
  property : val ∈ S

namespace VNSub

variable {S : StarSubalgebra ℂ A} {hS : IsVNSubalgebra A S}

theorem val_injective :
    Function.Injective (VNSub.val (A := A) (S := S) (hS := hS)) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h
  cases h; rfl

instance : Zero (VNSub A S hS) := ⟨⟨0, zero_mem S⟩⟩
instance : Add (VNSub A S hS) :=
  ⟨fun a b => ⟨a.val + b.val, add_mem a.property b.property⟩⟩
instance : Neg (VNSub A S hS) := ⟨fun a => ⟨-a.val, neg_mem a.property⟩⟩
instance : Sub (VNSub A S hS) :=
  ⟨fun a b => ⟨a.val - b.val, sub_mem a.property b.property⟩⟩
instance : SMul ℕ (VNSub A S hS) := ⟨fun n a => ⟨n • a.val, nsmul_mem a.property n⟩⟩
instance : SMul ℤ (VNSub A S hS) := ⟨fun n a => ⟨n • a.val, zsmul_mem a.property n⟩⟩
instance : SMul ℂ (VNSub A S hS) :=
  ⟨fun z a => ⟨z • a.val, SMulMemClass.smul_mem z a.property⟩⟩
instance : One (VNSub A S hS) := ⟨⟨1, one_mem S⟩⟩
instance : Mul (VNSub A S hS) :=
  ⟨fun a b => ⟨a.val * b.val, mul_mem a.property b.property⟩⟩
instance : Star (VNSub A S hS) := ⟨fun a => ⟨star a.val, star_mem a.property⟩⟩

@[simp] theorem val_zero : (0 : VNSub A S hS).val = 0 := rfl
@[simp] theorem val_add (a b : VNSub A S hS) : (a + b).val = a.val + b.val := rfl
@[simp] theorem val_neg (a : VNSub A S hS) : (-a).val = -a.val := rfl
@[simp] theorem val_sub (a b : VNSub A S hS) : (a - b).val = a.val - b.val := rfl
@[simp] theorem val_one : (1 : VNSub A S hS).val = 1 := rfl
@[simp] theorem val_mul (a b : VNSub A S hS) : (a * b).val = a.val * b.val := rfl
@[simp] theorem val_star (a : VNSub A S hS) : (star a).val = star a.val := rfl
@[simp] theorem val_smul (z : ℂ) (a : VNSub A S hS) : (z • a).val = z • a.val := rfl

instance instAddCommGroup : AddCommGroup (VNSub A S hS) :=
  Function.Injective.addCommGroup VNSub.val val_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance instRing : Ring (VNSub A S hS) where
  __ := instAddCommGroup
  mul_assoc a b c := val_injective (mul_assoc _ _ _)
  one_mul a := val_injective (one_mul _)
  mul_one a := val_injective (mul_one _)
  left_distrib a b c := val_injective (mul_add _ _ _)
  right_distrib a b c := val_injective (add_mul _ _ _)
  zero_mul a := val_injective (zero_mul _)
  mul_zero a := val_injective (mul_zero _)

/-- `VNSub.val` as an additive monoid homomorphism. -/
def valAddHom : VNSub A S hS →+ A where
  toFun := VNSub.val
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModule : Module ℂ (VNSub A S hS) :=
  Function.Injective.module ℂ valAddHom val_injective (fun _ _ => rfl)

instance instAlgebra : Algebra ℂ (VNSub A S hS) :=
  Algebra.ofModule (fun r x y => val_injective (smul_mul_assoc r x.val y.val))
    (fun r x y => val_injective (mul_smul_comm r x.val y.val))

instance instStarRing : StarRing (VNSub A S hS) where
  star_involutive a := val_injective (star_star a.val)
  star_mul a b := val_injective (star_mul a.val b.val)
  star_add a b := val_injective (star_add a.val b.val)

instance instStarModule : StarModule ℂ (VNSub A S hS) where
  star_smul r a := val_injective (star_smul r a.val)

/-- `VNSub.val` as a non-unital ring homomorphism. -/
def valNonUnitalRingHom : VNSub A S hS →ₙ+* A where
  toFun := VNSub.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance instNormedRing : NormedRing (VNSub A S hS) :=
  NormedRing.induced (VNSub A S hS) A valNonUnitalRingHom val_injective

@[simp] theorem norm_def (a : VNSub A S hS) : ‖a‖ = ‖a.val‖ := rfl

instance instNormedAlgebra : NormedAlgebra ℂ (VNSub A S hS) where
  norm_smul_le r a := by simpa [norm_def] using (norm_smul_le r a.val)

theorem isometry_val : Isometry (VNSub.val (A := A) (S := S) (hS := hS)) :=
  AddMonoidHomClass.isometry_of_norm valAddHom (fun _ => rfl)

theorem range_val :
    Set.range (VNSub.val (A := A) (S := S) (hS := hS)) = (S : Set A) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩; exact b.property
  · intro ha; exact ⟨⟨a, ha⟩, rfl⟩

instance instCompleteSpace : CompleteSpace (VNSub A S hS) := by
  refine (isometry_val (S := S) (hS := hS)).isUniformInducing.completeSpace ?_
  rw [range_val]
  exact hS.isClosed.isComplete

instance instCStarRing : CStarRing (VNSub A S hS) where
  norm_mul_self_le a := CStarRing.norm_star_mul_self (x := a.val) |>.symm.le

end VNSub

noncomputable instance (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S) :
    CStarAlgebra (VNSub A S hS) where

noncomputable instance (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S) :
    PartialOrder (VNSub A S hS) :=
  PartialOrder.lift VNSub.val VNSub.val_injective

namespace VNSub

variable {S : StarSubalgebra ℂ A} {hS : IsVNSubalgebra A S}

theorem le_def (a b : VNSub A S hS) : a ≤ b ↔ a.val ≤ b.val := Iff.rfl

/-- The square root of a positive element of a *closed* star subalgebra
again lies in it: `√a = cfcₙ √ a`, and the non-unital continuous functional
calculus of an element stays inside every closed star subalgebra
containing it (Mathlib's `cfcₙ_mem`). -/
theorem sqrt_mem (hcl : IsClosed (S : Set A)) (a : A) (ha : 0 ≤ a)
    (hmem : a ∈ S) : CFC.sqrt a ∈ S := by
  have : IsClosed (S : Set A) := hcl
  rw [CFC.sqrt_eq_real_sqrt a ha]
  exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ) Real.sqrt hmem

end VNSub

instance (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S) :
    StarOrderedRing (VNSub A S hS) := by
  refine StarOrderedRing.of_nonneg_iff' (fun {x y} hxy z => ?_) (fun x => ?_)
  · show z.val + x.val ≤ z.val + y.val
    exact add_le_add le_rfl (show x.val ≤ y.val from hxy)
  · constructor
    · intro hx
      have hx' : (0 : A) ≤ x.val := hx
      refine ⟨⟨CFC.sqrt x.val, VNSub.sqrt_mem hS.isClosed x.val hx' x.property⟩, ?_⟩
      refine VNSub.val_injective ?_
      have hsa : IsSelfAdjoint (CFC.sqrt x.val) :=
        IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x.val)
      show x.val = star (CFC.sqrt x.val) * CFC.sqrt x.val
      rw [hsa.star_eq, CFC.sqrt_mul_sqrt_self x.val hx']
    · rintro ⟨s, rfl⟩
      show (0 : A) ≤ star s.val * s.val
      exact star_mul_self_nonneg s.val

namespace VNSub

variable {S : StarSubalgebra ℂ A} {hS : IsVNSubalgebra A S} [VonNeumannAlgebra A]

/-- A self-adjoint element of `S`, viewed in `A`. -/
def saMap (d : selfAdjoint (VNSub A S hS)) : selfAdjoint A :=
  ⟨d.1.val, congrArg VNSub.val (show star d.1 = d.1 from d.2)⟩

@[simp] theorem saMap_coe (d : selfAdjoint (VNSub A S hS)) :
    ((saMap d : selfAdjoint A) : A) = d.1.val := rfl

/-- Suprema of nonempty directed sets of self-adjoint elements are computed
in a von Neumann subalgebra exactly as they are in `A` (42V part 4). -/
theorem isLUB_saMap_image {D : Set (selfAdjoint (VNSub A S hS))}
    {s : selfAdjoint (VNSub A S hS)} (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hlub : IsLUB D s) :
    IsLUB (saMap '' D) (saMap s) := by
  set D' : Set (selfAdjoint A) := saMap '' D with hD'
  have hne' : D'.Nonempty := hne.image _
  have hdir' : DirectedOn (· ≤ ·) D' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    obtain ⟨u, hu, hxu, hzu⟩ := hdir x hx z hz
    exact ⟨saMap u, ⟨u, hu, rfl⟩, hxu, hzu⟩
  have hbdd' : BddAbove D' := by
    refine ⟨saMap s, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hlub.1 hx
  obtain ⟨s₀, hs₀⟩ :=
    VonNeumannAlgebra.isLUB_of_bddAbove_directed D' hne' hdir' hbdd'
  have hmem : (s₀ : A) ∈ S :=
    hS.dirSup_mem D' s₀ (by rintro _ ⟨x, hx, rfl⟩; exact x.1.property) hne' hdir' hs₀
  set t : VNSub A S hS := ⟨(s₀ : A), hmem⟩ with ht
  have htsa : IsSelfAdjoint t := val_injective s₀.2
  have hlubt : IsLUB D ⟨t, htsa⟩ := by
    constructor
    · intro d hd
      exact hs₀.1 ⟨d, hd, rfl⟩
    · intro u hu
      have hub : saMap u ∈ upperBounds D' := by
        rintro _ ⟨x, hx, rfl⟩
        exact hu hx
      exact hs₀.2 hub
  have hst : s = ⟨t, htsa⟩ := hlub.unique hlubt
  have hsm : saMap (⟨t, htsa⟩ : selfAdjoint (VNSub A S hS)) = s₀ := Subtype.ext rfl
  rw [hst, hsm]
  exact hs₀

/-- Restriction of an np-functional on `A` to a von Neumann subalgebra. -/
def restrictNP (ω : NPFunctional A) : NPFunctional (VNSub A S hS) where
  toPositiveLinearMap :=
    { toFun := fun a => ω a.val
      map_add' := fun x y => map_add ω.toPositiveLinearMap _ _
      map_smul' := fun c x => map_smul ω.toPositiveLinearMap _ _
      monotone' := fun x y hxy => ω.toPositiveLinearMap.monotone hxy }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hkey := ω.preservesDirSups' (saMap '' D) (saMap s) (hne.image _)
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
        obtain ⟨u, hu, hxu, hzu⟩ := hdir x hx z hz
        exact ⟨saMap u, ⟨u, hu, rfl⟩, hxu, hzu⟩)
      (isLUB_saMap_image hne hdir hlub)
    rw [← Set.image_comp] at hkey
    exact hkey

@[simp] theorem restrictNP_apply (ω : NPFunctional A) (a : VNSub A S hS) :
    (restrictNP ω : NPFunctional (VNSub A S hS)) a = ω a.val := rfl

end VNSub

instance (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S)
    [VonNeumannAlgebra A] : VonNeumannAlgebra (VNSub A S hS) where
  isLUB_of_bddAbove_directed := by
    intro D hne hdir hbdd
    obtain ⟨u, hu⟩ := hbdd
    have hne' : (VNSub.saMap '' D).Nonempty := hne.image _
    have hdir' : DirectedOn (· ≤ ·) (VNSub.saMap (S := S) (hS := hS) '' D) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
      obtain ⟨v, hv, hxv, hzv⟩ := hdir x hx z hz
      exact ⟨VNSub.saMap v, ⟨v, hv, rfl⟩, hxv, hzv⟩
    have hbdd' : BddAbove (VNSub.saMap (S := S) (hS := hS) '' D) := by
      refine ⟨VNSub.saMap u, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hu hx
    obtain ⟨s₀, hs₀⟩ :=
      VonNeumannAlgebra.isLUB_of_bddAbove_directed _ hne' hdir' hbdd'
    have hmem : (s₀ : A) ∈ S :=
      hS.dirSup_mem _ s₀ (by rintro _ ⟨x, hx, rfl⟩; exact x.1.property) hne' hdir' hs₀
    refine ⟨⟨⟨(s₀ : A), hmem⟩, VNSub.val_injective s₀.2⟩, ?_, ?_⟩
    · intro d hd
      exact hs₀.1 ⟨d, hd, rfl⟩
    · intro v hv
      have hub : VNSub.saMap v ∈ upperBounds (VNSub.saMap (S := S) (hS := hS) '' D) := by
        rintro _ ⟨x, hx, rfl⟩
        exact hv hx
      exact hs₀.2 hub
  np_faithful := by
    intro a ha hω
    refine VNSub.val_injective ?_
    exact VonNeumannAlgebra.np_faithful a.val ha (fun ω => hω (VNSub.restrictNP ω))


namespace VNSub

variable {S : StarSubalgebra ℂ A} {hS : IsVNSubalgebra A S}

theorem isStarProjection_val {x : VNSub A S hS} (hx : IsStarProjection x) :
    IsStarProjection x.val :=
  ⟨congrArg VNSub.val hx.isIdempotentElem, congrArg VNSub.val hx.isSelfAdjoint⟩

theorem isStarProjection_mk {x : A} (hx : IsStarProjection x) (h : x ∈ S) :
    IsStarProjection (⟨x, h⟩ : VNSub A S hS) :=
  ⟨val_injective hx.isIdempotentElem, val_injective hx.isSelfAdjoint⟩

end VNSub

variable [VonNeumannAlgebra A]

/-- **83V** (`cceil-sum`, vn.tex:5734, Lemma) **relative to a von Neumann
subalgebra** `S`, in the form 89IX needs it: if the least central projection
of `S` above a projection `e ∈ S` is `1`, then there are partial isometries
`(vᵢ)` in `S` with `∑ᵢ vᵢ*vᵢ = 1` (as a supremum of projections) and
`vᵢvᵢ* ≤ e`.

This is `cceil_sum` applied inside the bundled von Neumann algebra `VNSub`;
the thesis simply writes `⌈⌈·⌉⌉_{S}` and uses `cceil-sum` there. -/
theorem cceil_sum_relative (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S)
    (e : A) (heS : e ∈ S) (he : IsStarProjection e)
    (hone : IsLeast {p : A | p ∈ S ∧ IsStarProjection p ∧
      (∀ b ∈ S, p * b = b * p) ∧ e ≤ p} 1) :
    ∃ (ι : Type u) (v : ι → A), (∀ i, v i ∈ S) ∧
      (∀ i, IsStarProjection (star (v i) * v i)) ∧
      (Pairwise fun i j => (star (v i) * v i) * (star (v j) * v j) = 0) ∧
      projSup (Set.range fun i => star (v i) * v i) = 1 ∧
      ∀ i, v i * star (v i) ≤ e := by
  classical
  set E : VNSub A S hS := ⟨e, heS⟩ with hEdef
  have hEproj : IsStarProjection E := VNSub.isStarProjection_mk he heS
  -- the central carrier of `E` inside `S` is `1`
  have hcc : cceil E = 1 := by
    refine le_antisymm ?_ ?_
    · exact (cceil_isLeast E).2 ⟨IsStarProjection.one _, fun b => by
        rw [one_mul, mul_one], one_mul _⟩
    · have hspec := (cceil_isLeast E).1
      have hcproj : IsStarProjection (cceil E).val :=
        VNSub.isStarProjection_val hspec.1
      have hle : E ≤ cceil E :=
        ((projection_below_effect (cceil E) E ⟨hspec.1.nonneg, hspec.1.le_one⟩
          hEproj).out 6 0).mp hspec.2.2
      have hmem : (cceil E).val ∈ {p : A | p ∈ S ∧ IsStarProjection p ∧
          (∀ b ∈ S, p * b = b * p) ∧ e ≤ p} :=
        ⟨(cceil E).property, hcproj,
          fun b hb => congrArg VNSub.val (hspec.2.1 ⟨b, hb⟩), hle⟩
      exact (VNSub.le_def _ _).mpr (hone.2 hmem)
  obtain ⟨ι, f, hf, hforth, hfsup⟩ := cceil_sum E hEproj
  choose u hupi hu1 hu2 using fun i => (hf i).2.2
  refine ⟨ι, fun i => (u i).val, fun i => (u i).property, ?_, ?_, ?_, ?_⟩
  · intro i
    have : star ((u i).val) * (u i).val = (f i).val := congrArg VNSub.val (hu1 i)
    rw [this]
    exact VNSub.isStarProjection_val (hf i).1
  · intro i j hij
    have h1 : star ((u i).val) * (u i).val = (f i).val := congrArg VNSub.val (hu1 i)
    have h2 : star ((u j).val) * (u j).val = (f j).val := congrArg VNSub.val (hu1 j)
    rw [h1, h2]
    exact congrArg VNSub.val (hforth hij)
  · -- the supremum of the `fᵢ`, computed in `A`, is again `1`
    have hval : (fun i => star ((u i).val) * (u i).val) = fun i => (f i).val := by
      funext i; exact congrArg VNSub.val (hu1 i)
    rw [hval]
    set P : Set A := Set.range fun i => (f i).val with hP
    have hPproj : ∀ p ∈ P, IsStarProjection p := by
      rintro _ ⟨i, rfl⟩; exact VNSub.isStarProjection_val (hf i).1
    have hPS : ∀ p ∈ P, p ∈ S := by rintro _ ⟨i, rfl⟩; exact (f i).property
    have hq : projSup P ∈ S :=
      (projSup_mem_of_np hS P hPproj hPS zeroNP (fun _ _ => rfl)).1
    obtain ⟨hqproj, hqub, hqleast⟩ := projSup_spec hPproj
    set Q : VNSub A S hS := ⟨projSup P, hq⟩ with hQdef
    have hQproj : IsStarProjection Q := VNSub.isStarProjection_mk hqproj hq
    have hub : ∀ x ∈ Set.range f, x ≤ Q := by
      rintro _ ⟨i, rfl⟩
      exact (VNSub.le_def _ _).mpr (hqub _ ⟨i, rfl⟩)
    obtain ⟨-, -, hleast⟩ := projSup_spec (P := Set.range f)
      (by rintro _ ⟨i, rfl⟩; exact (hf i).1)
    have h1 : (1 : VNSub A S hS) ≤ Q := by
      rw [← hcc, hfsup]; exact hleast Q hQproj hub
    exact le_antisymm hqproj.le_one ((VNSub.le_def _ _).mp h1)
  · intro i
    exact (VNSub.le_def _ _).mp (hu2 i)

end VNSubalgebra

/-! ### Machinery for **84bIII**

The corner `dⱼℬ` is never constructed as a type.  Instead the *range* of
`πⱼ ∘ e` is used: it is a closed `StarSubalgebra` of a finite-dimensional
C*-algebra, hence a finite-dimensional C*-algebra itself, so **84II**
`fdcstar` applies to it directly, and all the projection algebra stays
inside `ℬ`, where `carrier` (**63I**) and **69IV** `carrier_miu` are
available. -/

section HABlocks

variable [VonNeumannAlgebra B]

-- several of the auxiliaries below use only part of the ambient structure
set_option linter.unusedSectionVars false

/-- A ∗-homomorphism whose kernel is the orthocomplement of a central
projection `c` is contractive, and isometric on the corner `cB`. -/
private theorem starAlgHom_norm_corner {M : Type*} [CStarAlgebra M]
    (ρ : B →⋆ₐ[ℂ] M) {c : B} (hc : IsStarProjection c) (hcen : IsCentral B c)
    (hker : ∀ b : B, ρ b = 0 ↔ c * b = 0) :
    (∀ b : B, ‖ρ b‖ ≤ ‖b‖) ∧ (∀ b : B, c * b = b → ‖ρ b‖ = ‖b‖) := by
  have hcc : c * c = c := hc.isIdempotentElem.eq
  have hone : (1 - c) * ((1 : B) - c) = 1 - c := by
    have h1 : (1 - c) * ((1 : B) - c) = 1 - c - c + c * c := by noncomm_ring
    rw [h1, hcc]; abel
  have hcomm : ∀ x : B, (1 - c) * x = x * (1 - c) := by
    intro x
    have h1 : (1 - c) * x = x - c * x := by noncomm_ring
    have h2 : x * ((1 : B) - c) = x - x * c := by noncomm_ring
    rw [h1, h2, hcen x]
  set φ : B →⋆ₙₐ[ℂ] M × B :=
    { toFun := fun x => (ρ x, (1 - c) * x)
      map_smul' := fun r x => by
        refine Prod.ext (map_smul ρ r x) ?_
        show (1 - c) * (r • x) = r • ((1 - c) * x)
        rw [mul_smul_comm]
      map_zero' := by
        refine Prod.ext (map_zero ρ) ?_
        show (1 - c) * (0 : B) = 0
        rw [mul_zero]
      map_add' := fun x y => by
        refine Prod.ext (map_add ρ x y) ?_
        show (1 - c) * (x + y) = (1 - c) * x + (1 - c) * y
        rw [mul_add]
      map_mul' := fun x y => by
        refine Prod.ext (map_mul ρ x y) ?_
        show (1 - c) * (x * y) = ((1 - c) * x) * ((1 - c) * y)
        calc (1 - c) * (x * y) = ((1 - c) * (1 - c)) * (x * y) := by rw [hone]
          _ = (1 - c) * ((1 - c) * x) * y := by noncomm_ring
          _ = (1 - c) * (x * (1 - c)) * y := by rw [hcomm x]
          _ = ((1 - c) * x) * ((1 - c) * y) := by noncomm_ring
      map_star' := fun x => by
        refine Prod.ext (map_star ρ x) ?_
        show (1 - c) * star x = star ((1 - c) * x)
        rw [star_mul, star_sub, star_one, hc.isSelfAdjoint.star_eq, hcomm (star x)] }
    with hφ
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h1 : ρ x = ρ y := congrArg Prod.fst hxy
    have h2 : (1 - c) * x = (1 - c) * y := congrArg Prod.snd hxy
    have h3 : ρ (x - y) = 0 := by rw [map_sub, h1, sub_self]
    have h4 : c * (x - y) = 0 := (hker _).mp h3
    have h5 : (1 - c) * (x - y) = 0 := by rw [mul_sub, h2, sub_self]
    refine sub_eq_zero.mp ?_
    have h6 : c * (x - y) + (1 - c) * (x - y) = x - y := by noncomm_ring
    rw [h4, h5, add_zero] at h6
    exact h6.symm
  have hn : ∀ b : B, max ‖ρ b‖ ‖(1 - c) * b‖ = ‖b‖ := fun b =>
    NonUnitalStarAlgHom.norm_map φ hinj b
  refine ⟨fun b => ?_, fun b hb => ?_⟩
  · rw [← hn b]; exact le_max_left _ _
  · have hz : (1 - c) * b = 0 := by rw [sub_mul, one_mul, hb, sub_self]
    have h := hn b
    rw [hz, norm_zero, max_eq_left (norm_nonneg _)] at h
    exact h

/-- Auxiliary: a star subalgebra of a finite-dimensional C*-algebra is
finite-dimensional. -/
private theorem finiteDimensional_starSubalgebra {M : Type*} [CStarAlgebra M]
    [FiniteDimensional ℂ M] (S : StarSubalgebra ℂ M) : FiniteDimensional ℂ S :=
  FiniteDimensional.of_injective (S.subtype : S →ₗ[ℂ] M) Subtype.val_injective

attribute [local instance] finiteDimensional_starSubalgebra

/-- Auxiliary: a star subalgebra of a finite-dimensional C*-algebra is a
C*-algebra (it is complete because it is finite-dimensional). -/
@[instance_reducible]
private noncomputable def cstarAlgebra_starSubalgebra {M : Type*} [CStarAlgebra M]
    [FiniteDimensional ℂ M] (S : StarSubalgebra ℂ M) : CStarAlgebra S :=
  { complete := (FiniteDimensional.complete ℂ S).1 }

attribute [local instance] cstarAlgebra_starSubalgebra

/-- Auxiliary: a ∗-homomorphism from `B` into a finite-dimensional C*-algebra
factors as a *surjection* onto a finite product of full matrix algebras with
the same kernel — its range is a star subalgebra of a finite-dimensional
C*-algebra, hence itself a finite-dimensional C*-algebra, so **84II**
`fdcstar` applies to it.  (No corner of `B` is constructed.) -/
private theorem exists_surj_matprod {M : Type*} [CStarAlgebra M]
    [FiniteDimensional ℂ M] (g : B →⋆ₐ[ℂ] M) :
    ∃ (k : ℕ) (n : Fin k → ℕ)
      (Ψ : B →⋆ₐ[ℂ] ∀ m : Fin k, Matrix (Fin (n m)) (Fin (n m)) ℂ),
      Function.Surjective Ψ ∧ ∀ x : B, Ψ x = 0 ↔ g x = 0 := by
  classical
  obtain ⟨k, n, ⟨ψ⟩⟩ := fdcstar (g.range)
  refine ⟨k, n, ψ.toStarAlgHom.comp g.rangeRestrict, ψ.surjective.comp g.rangeRestrict_surjective,
    fun x => ?_⟩
  constructor
  · intro h
    have h1 : g.rangeRestrict x = 0 := by
      have h2 := congrArg ψ.symm h
      simpa using h2
    exact congrArg Subtype.val h1
  · intro h
    have h1 : g.rangeRestrict x = 0 := Subtype.ext h
    show ψ (g.rangeRestrict x) = 0
    rw [h1, map_zero]

/-- The **block decomposition** attached to an nmiu-map `g : B → M` into a
finite-dimensional von Neumann algebra: finitely many *central* projections
`Qₘ` of `B` (the minimal central projections of the corner `⌈g⌉B`, obtained
without ever constructing that corner), each carrying a surjective
∗-homomorphism `ρₘ : B → M_{nₘ}` whose kernel is `Qₘ^⊥B`, and such that
`g b = 0` exactly when every `Qₘ b = 0`. -/
private theorem exists_blocks {M : Type*} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] [VonNeumannAlgebra M] [FiniteDimensional ℂ M]
    (g : NMIUMap B M) :
    ∃ (k : ℕ) (n : Fin k → ℕ) (Q : Fin k → B)
      (ρ : ∀ m : Fin k, B →⋆ₐ[ℂ] CStarMatrix (Fin (n m)) (Fin (n m)) ℂ),
      (∀ m, IsStarProjection (Q m) ∧ IsCentral B (Q m)) ∧
      (∀ (m : Fin k) (b : B), ρ m b = 0 ↔ Q m * b = 0) ∧
      (∀ m, Function.Surjective (ρ m)) ∧
      (∀ m, ρ m (Q m) = 1) ∧
      (∀ b : B, g b = 0 ↔ ∀ m, Q m * b = 0) := by
  classical
  obtain ⟨hdcen, hdker⟩ := carrier_miu g (nmiuP g) g.preservesDirSups' (fun a => rfl)
  set d : B := carrier (nmiuP g) g.preservesDirSups' with hddef
  have hdproj : IsStarProjection d := (carrier_spec (nmiuP g) g.preservesDirSups').1
  have hdd : d * d = d := hdproj.isIdempotentElem.eq
  obtain ⟨k, n, Ψ, hsurj, hker⟩ := exists_surj_matprod (M := M) g.toStarAlgHom
  have hkerg : ∀ x : B, Ψ x = 0 ↔ d * x = 0 := fun x => (hker x).trans (hdker x)
  -- `Ψ d = 1`
  have hd1 : Ψ d = 1 := by
    have h0 : Ψ (1 - d) = 0 := (hkerg _).mpr (by rw [mul_sub, mul_one, hdd, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0.symm
  -- injectivity of `Ψ` on the corner `dB`
  have hinj : ∀ x : B, d * x = x → Ψ x = 0 → x = 0 := by
    intro x hx h0
    rw [← hx]; exact (hkerg x).mp h0
  -- the block projections
  have hQex : ∀ m : Fin k, ∃ q : B, d * q = q ∧ Ψ q = Pi.single m 1 := by
    intro m
    obtain ⟨b, hb⟩ := hsurj (Pi.single m 1)
    refine ⟨d * b, by rw [← mul_assoc, hdd], ?_⟩
    rw [map_mul, hd1, hb, one_mul]
  choose Q hQd hQΨ using hQex
  -- the master identity
  have hmaster : ∀ (m : Fin k) (b : B), Ψ (Q m * b) = Pi.single m (Ψ b m) := by
    intro m b
    rw [map_mul, hQΨ]
    funext m'
    rcases eq_or_ne m' m with rfl | h
    · simp [Pi.mul_apply]
    · simp [Pi.mul_apply, Pi.single_eq_of_ne h]
  have hdQb : ∀ (m : Fin k) (b : B), d * (Q m * b) = Q m * b := by
    intro m b; rw [← mul_assoc, hQd]
  have hQker : ∀ (m : Fin k) (b : B), Q m * b = 0 ↔ Ψ b m = 0 := by
    intro m b
    constructor
    · intro h
      have h1 := hmaster m b
      rw [h, map_zero] at h1
      have h2 := congrFun h1.symm m
      simpa using h2
    · intro h
      refine hinj _ (hdQb m b) ?_
      rw [hmaster, h, Pi.single_zero]
  have hdbQ : ∀ (m : Fin k) (b : B), d * (b * Q m) = b * Q m := by
    intro m b
    calc d * (b * Q m) = (d * b) * Q m := by rw [mul_assoc]
      _ = (b * d) * Q m := by rw [hdcen b]
      _ = b * (d * Q m) := by rw [mul_assoc]
      _ = b * Q m := by rw [hQd]
  have hsinglecen : ∀ (m : Fin k) (y : ∀ m : Fin k, Matrix (Fin (n m)) (Fin (n m)) ℂ),
      Pi.single m 1 * y = y * Pi.single m 1 := by
    intro m y
    funext m'
    rcases eq_or_ne m' m with rfl | h
    · simp [Pi.mul_apply]
    · simp [Pi.mul_apply, Pi.single_eq_of_ne h]
  set ρ : ∀ m : Fin k, B →⋆ₐ[ℂ] CStarMatrix (Fin (n m)) (Fin (n m)) ℂ :=
    fun m => CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
      ((Pi.evalStarAlgHom ℂ _ m).comp Ψ) with hρdef
  have hρapply : ∀ (m : Fin k) (b : B), ρ m b = CStarMatrix.ofMatrixStarAlgEquiv (Ψ b m) :=
    fun _ _ => rfl
  have hρ0 : ∀ (m : Fin k) (b : B), ρ m b = 0 ↔ Ψ b m = 0 := by
    intro m b
    rw [hρapply]
    constructor
    · intro h
      have := congrArg CStarMatrix.ofMatrixStarAlgEquiv.symm h
      simpa using this
    · intro h; rw [h, map_zero]
  refine ⟨k, n, Q, ρ, ?_, ?_, ?_, ?_, ?_⟩
  · -- projections and centrality
    intro m
    have hp : Q m * Q m = Q m := by
      refine sub_eq_zero.mp (hinj _ ?_ ?_)
      · rw [mul_sub, hdQb, hQd]
      · rw [map_sub, map_mul, hQΨ, sub_eq_zero]
        funext m'
        rcases eq_or_ne m' m with rfl | h
        · simp [Pi.mul_apply]
        · simp [Pi.mul_apply, Pi.single_eq_of_ne h]
    have hs : star (Q m) = Q m := by
      have hdstar : d * star (Q m) = star (Q m) := by
        have h := congrArg star (hQd m)
        rw [star_mul, hdproj.isSelfAdjoint.star_eq] at h
        rw [hdcen (star (Q m))]
        exact h
      refine sub_eq_zero.mp (hinj _ ?_ ?_)
      · rw [mul_sub, hdstar, hQd]
      · rw [map_sub, map_star, hQΨ, sub_eq_zero]
        funext m'
        rcases eq_or_ne m' m with rfl | h
        · simp [Pi.star_apply]
        · simp [Pi.star_apply, Pi.single_eq_of_ne h]
    refine ⟨isStarProjection_iff'.mpr ⟨hp, hs⟩, fun b => ?_⟩
    refine sub_eq_zero.mp (hinj _ ?_ ?_)
    · rw [mul_sub, hdQb, hdbQ]
    · rw [map_sub, map_mul, map_mul, hQΨ, sub_eq_zero, hsinglecen]
  · intro m b; rw [hρ0, ← hQker]
  · intro m y
    obtain ⟨b, hb⟩ := hsurj (Pi.single m (CStarMatrix.ofMatrixStarAlgEquiv.symm y))
    refine ⟨b, ?_⟩
    rw [hρapply, hb]
    simp
  · intro m
    rw [hρapply, hQΨ]
    simp
  · intro b
    rw [hdker b, ← hkerg b]
    constructor
    · intro h m
      refine (hQker m b).mpr ?_
      rw [h]; rfl
    · intro h
      funext m
      have := (hQker m b).mp (h m)
      simpa using this

/-- A central idempotent of a full matrix algebra is `0` or `1`
(it is a scalar by `Matrix.mem_range_scalar_of_commute_single`). -/
private theorem central_idem_matrix {p : ℕ} {x : CStarMatrix (Fin p) (Fin p) ℂ}
    (hx : x * x = x) (hcen : ∀ y, x * y = y * x) : x = 0 ∨ x = 1 := by
  classical
  rcases isEmpty_or_nonempty (Fin p) with he | hne
  · left
    have : Subsingleton (CStarMatrix (Fin p) (Fin p) ℂ) := by
      constructor
      intro a b
      funext i
      exact he.elim i
    exact Subsingleton.elim _ _
  · set X : Matrix (Fin p) (Fin p) ℂ := CStarMatrix.ofMatrixStarAlgEquiv.symm x with hX
    have hXcen : ∀ y : Matrix (Fin p) (Fin p) ℂ, X * y = y * X := by
      intro y
      have h := hcen (CStarMatrix.ofMatrixStarAlgEquiv y)
      have h1 := congrArg CStarMatrix.ofMatrixStarAlgEquiv.symm h
      rw [map_mul, map_mul] at h1
      simpa [hX] using h1
    have hXX : X * X = X := by
      have h1 := congrArg CStarMatrix.ofMatrixStarAlgEquiv.symm hx
      rw [map_mul] at h1
      simpa [hX] using h1
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single
      (M := X) (fun i j _ => (hXcen (Matrix.single i j 1)).symm)
    have hcc : (Matrix.scalar (Fin p)) (c * c) = (Matrix.scalar (Fin p)) c := by
      rw [map_mul, hc, hXX]
    have hc2 : c * c = c := by
      obtain ⟨i⟩ := hne
      have h4 := congrFun (congrFun hcc i) i
      simpa [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h4
    have : c = 0 ∨ c = 1 := by
      rcases eq_or_ne c 0 with h | h
      · exact Or.inl h
      · right
        field_simp at hc2
        exact hc2
    rcases this with h | h
    · left
      have : X = 0 := by rw [← hc, h, map_zero]
      rw [hX] at this
      have := congrArg CStarMatrix.ofMatrixStarAlgEquiv this
      simpa using this
    · right
      have : X = 1 := by rw [← hc, h, map_one]
      rw [hX] at this
      have := congrArg CStarMatrix.ofMatrixStarAlgEquiv this
      simpa using this

/-- Each block projection is a *minimal* central projection: a non-zero
central projection below `q` equals `q`. -/
private theorem block_minimal {p : ℕ} (ρ : B →⋆ₐ[ℂ] CStarMatrix (Fin p) (Fin p) ℂ)
    (hsurj : Function.Surjective ρ) {q : B} (hqproj : IsStarProjection q)
    (hker : ∀ b : B, ρ b = 0 ↔ q * b = 0) (hq1 : ρ q = 1)
    {c : B} (hcproj : IsStarProjection c) (hccen : IsCentral B c)
    (hcq : c * q = c) (hc0 : c ≠ 0) : c = q := by
  have hidem : ρ c * ρ c = ρ c := by rw [← map_mul, hcproj.isIdempotentElem.eq]
  have hcenρ : ∀ y, ρ c * y = y * ρ c := by
    intro y
    obtain ⟨b, rfl⟩ := hsurj y
    rw [← map_mul, ← map_mul, hccen b]
  have hne : ρ c ≠ 0 := by
    intro h
    refine hc0 ?_
    calc c = c * q := hcq.symm
      _ = q * c := hccen q
      _ = 0 := (hker c).mp h
  have h1 : ρ c = 1 := (central_idem_matrix hidem hcenρ).resolve_left hne
  have h2 : ρ (c - q) = 0 := by rw [map_sub, h1, hq1, sub_self]
  have h3 : q * (c - q) = 0 := (hker _).mp h2
  rw [mul_sub, hqproj.isIdempotentElem.eq, sub_eq_zero] at h3
  calc c = c * q := hcq.symm
    _ = q * c := hccen q
    _ = q := h3


end HABlocks

section HAMain

/-- The coordinate projection `⊕ᵢ𝒜ᵢ → 𝒜ⱼ` as a ∗-homomorphism. -/
private def lpProj {I : Type*} (𝒜 : I → Type u) [∀ i, CStarAlgebra (𝒜 i)]
    [∀ i, Nontrivial (𝒜 i)] (i : I) :
    lp 𝒜 ∞ →⋆ₐ[ℂ] 𝒜 i where
  toFun a := (a : ∀ i, 𝒜 i) i
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl


/-- Universe-polymorphic form of `starAlgHom_nonneg`. -/
private theorem starAlgHom_nonneg₂ {X Y : Type*} [CStarAlgebra X] [PartialOrder X]
    [StarOrderedRing X] [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y]
    (φ : X →⋆ₐ[ℂ] Y) {a : X} (ha : 0 ≤ a) : 0 ≤ φ a := by
  have hsa : IsSelfAdjoint (CFC.sqrt a) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)
  have h : a = star (CFC.sqrt a) * CFC.sqrt a := by
    rw [hsa.star_eq, CFC.sqrt_mul_sqrt_self a ha]
  rw [h, map_mul, map_star]
  exact star_mul_self_nonneg _

/-- Universe-polymorphic form of `starAlgHom_mono`. -/
private theorem starAlgHom_mono₂ {X Y : Type*} [CStarAlgebra X] [PartialOrder X]
    [StarOrderedRing X] [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y]
    (φ : X →⋆ₐ[ℂ] Y) {x y : X} (h : x ≤ y) : φ x ≤ φ y := by
  have h0 := starAlgHom_nonneg₂ φ (sub_nonneg.mpr h)
  rw [map_sub] at h0
  exact sub_nonneg.mp h0

/-- Universe-polymorphic form of `preservesDirSups_pmap_comp` for
∗-homomorphisms. -/
private theorem preservesDirSups_comp₂ {X Y Z : Type*} [CStarAlgebra X] [PartialOrder X]
    [StarOrderedRing X] [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y]
    [CStarAlgebra Z] [PartialOrder Z] [StarOrderedRing Z]
    (φ : X →⋆ₐ[ℂ] Y) (hφ : PreservesDirSups ⇑φ)
    (ψ : Y →⋆ₐ[ℂ] Z) (hψ : PreservesDirSups ⇑ψ) :
    PreservesDirSups (fun x => ψ (φ x)) := by
  intro D s hne hdir hlub
  have hsa : ∀ d : selfAdjoint X, IsSelfAdjoint (φ (d : X)) := by
    intro d
    show star (φ (d : X)) = φ (d : X)
    rw [← map_star, d.2.star_eq]
  set G : Set (selfAdjoint Y) :=
    (fun d : selfAdjoint X => (⟨φ (d : X), hsa d⟩ : selfAdjoint Y)) '' D with hG
  have hval : Subtype.val '' G = (fun d : selfAdjoint X => φ (d : X)) '' D := by
    rw [hG, ← Set.image_comp]; rfl
  have hlubG : IsLUB G (⟨φ (s : X), hsa s⟩ : selfAdjoint Y) := by
    refine isLUB_sa_of_isLUB ?_
    rw [hval]
    exact hφ D s hne hdir hlub
  have hGne : G.Nonempty := hne.image _
  have hGdir : DirectedOn (· ≤ ·) G := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
    exact ⟨_, ⟨z, hz, rfl⟩,
      Subtype.coe_le_coe.mp (starAlgHom_mono₂ φ (Subtype.coe_le_coe.mpr hxz)),
      Subtype.coe_le_coe.mp (starAlgHom_mono₂ φ (Subtype.coe_le_coe.mpr hyz))⟩
  have hkey := hψ G _ hGne hGdir hlubG
  rw [hG, ← Set.image_comp] at hkey
  exact hkey

/-- `M_n(ℂ)` is finite-dimensional. -/
private theorem finiteDimensional_cstarMatrix (p : ℕ) :
    FiniteDimensional ℂ (CStarMatrix (Fin p) (Fin p) ℂ) :=
  Module.Finite.equiv (CStarMatrix.ofMatrixₗ (R := ℂ) (A := ℂ)
    (m := Fin p) (n := Fin p))

attribute [local instance] finiteDimensional_cstarMatrix

/-- Transporting a matrix algebra along an equality of dimensions. -/
private def cstarMatrixCongr {a b : ℕ} (h : a = b) :
    CStarMatrix (Fin a) (Fin a) ℂ ≃⋆ₐ[ℂ] CStarMatrix (Fin b) (Fin b) ℂ := by
  subst h; exact StarAlgEquiv.refl (R := ℂ) (A := CStarMatrix (Fin a) (Fin a) ℂ)

/-- **84bIII** (vn.tex:6185, Proposition): a von Neumann subalgebra of a
hereditarily atomic von Neumann algebra is hereditarily atomic — rendered:
if `B` embeds into hereditarily atomic `A` by an injective nmiu-map, then
`B` is hereditarily atomic. -/
theorem hereditarilyAtomic_subalgebra [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (hA : HereditarilyAtomic A) (f : NMIUMap B A)
    (hf : Function.Injective f) : HereditarilyAtomic B := by
  classical
  obtain ⟨I, N, ⟨Φ⟩⟩ := hA
  set 𝒜 : I → Type := fun i => CStarMatrix (Fin (N i + 1)) (Fin (N i + 1)) ℂ with h𝒜
  have hgn : ∀ i : I, PreservesDirSups
      (fun b : B => (lpProj 𝒜 i) ((Φ.toStarAlgHom.comp f.toStarAlgHom) b)) := by
    intro i
    have h1 : PreservesDirSups ⇑(Φ.toStarAlgHom.comp f.toStarAlgHom) :=
      preservesDirSups_pmap_comp (nmiuP f) f.preservesDirSups'
        (starAlgHomP Φ.toStarAlgHom) (starAlgEquiv_preservesDirSups Φ)
    exact preservesDirSups_comp₂ (Φ.toStarAlgHom.comp f.toStarAlgHom) h1
      (lpProj 𝒜 i) (vn_products_proj_normal 𝒜 i)
  set g : ∀ i : I, NMIUMap B (𝒜 i) := fun i =>
    ⟨(lpProj 𝒜 i).comp (Φ.toStarAlgHom.comp f.toStarAlgHom), hgn i⟩ with hgdef
  have hgapply : ∀ (i : I) (b : B), g i b = (Φ (f b) : ∀ i, 𝒜 i) i := fun _ _ => rfl
  -- `g i b = 0` for every `i` forces `b = 0`
  have hgsep : ∀ b : B, (∀ i, g i b = 0) → b = 0 := by
    intro b hb
    have hz : (f (0 : B) : A) = 0 := map_zero f.toStarAlgHom
    refine hf ?_
    rw [hz]
    refine Φ.injective ?_
    rw [map_zero]
    exact Subtype.ext (funext fun i => hb i)
  -- the block decomposition of each `g i`
  choose k n Q ρ hQc hQker hρsurj hρ1 hgz using fun i : I => exists_blocks (g i)
  -- the set of non-zero block projections: minimal central projections of `B`
  set S : Set B := {x | x ≠ 0 ∧ ∃ (i : I) (m : Fin (k i)), Q i m = x} with hSdef
  have hSproj : ∀ x ∈ S, IsStarProjection x := by
    rintro _ ⟨-, i, m, rfl⟩; exact (hQc i m).1
  have hScen : ∀ x ∈ S, IsCentral B x := by
    rintro _ ⟨-, i, m, rfl⟩; exact (hQc i m).2
  -- minimality
  have hSmin : ∀ x ∈ S, ∀ c : B, IsStarProjection c → IsCentral B c → c * x = c →
      c ≠ 0 → c = x := by
    rintro _ ⟨-, i, m, rfl⟩ c hcp hcc hcx hc0
    exact block_minimal (ρ i m) (hρsurj i m) (hQc i m).1 (hQker i m) (hρ1 i m) hcp hcc hcx hc0
  -- distinct minimal central projections are orthogonal
  have hSorth : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x * y = 0 := by
    intro x hx y hy hxy
    by_contra h0
    have hxp := hSproj x hx
    have hyp := hSproj y hy
    have hxc := hScen x hx
    have hyc := hScen y hy
    have hprod : IsStarProjection (x * y) := by
      refine isStarProjection_iff'.mpr ⟨?_, ?_⟩
      · calc x * y * (x * y) = x * (y * x) * y := by noncomm_ring
          _ = x * (x * y) * y := by rw [hyc x]
          _ = (x * x) * (y * y) := by noncomm_ring
          _ = x * y := by rw [hxp.isIdempotentElem.eq, hyp.isIdempotentElem.eq]
      · rw [star_mul, hxp.isSelfAdjoint.star_eq, hyp.isSelfAdjoint.star_eq, hyc x]
    have hprodc : IsCentral B (x * y) := by
      intro b
      calc x * y * b = x * (y * b) := by rw [mul_assoc]
        _ = x * (b * y) := by rw [hyc b]
        _ = (x * b) * y := by rw [mul_assoc]
        _ = (b * x) * y := by rw [hxc b]
        _ = b * (x * y) := by rw [mul_assoc]
    have h1 : x * y * x = x * y := by
      calc x * y * x = x * (y * x) := by rw [mul_assoc]
        _ = x * (x * y) := by rw [hyc x]
        _ = (x * x) * y := by rw [← mul_assoc]
        _ = x * y := by rw [hxp.isIdempotentElem.eq]
    have h2 : x * y * y = x * y := by
      rw [mul_assoc, hyp.isIdempotentElem.eq]
    exact hxy ((hSmin x hx _ hprod hprodc h1 h0).symm.trans (hSmin y hy _ hprod hprodc h2 h0))
  -- the supremum of `S` is `1`
  have hSsum : projSup S = 1 := by
    set r : B := projSup S with hr
    have hrp : IsStarProjection r := (projSup_spec hSproj).1
    have hq : ∀ x ∈ S, x * (1 - r) = 0 := by
      intro x hx
      have hle : x ≤ r := (projSup_spec hSproj).2.1 x hx
      have := ((orthogonal_tuple_of_projections_1 x (1 - r) (hSproj x hx) hrp.one_sub).out 4 0).mp
        (by rwa [sub_sub_cancel])
      exact this
    have hQq : ∀ (i : I) (m : Fin (k i)), Q i m * (1 - r) = 0 := by
      intro i m
      rcases eq_or_ne (Q i m) 0 with h | h
      · rw [h, zero_mul]
      · exact hq _ ⟨h, i, m, rfl⟩
    have hz : (1 : B) - r = 0 := hgsep _ fun i => (hgz i (1 - r)).mpr (hQq i)
    rw [sub_eq_zero] at hz
    exact hz.symm
  -- for each `p ∈ S` a surjective ∗-homomorphism onto a full matrix algebra
  have hpack : ∀ p : S, ∃ (m : ℕ) (θ : B →⋆ₐ[ℂ] CStarMatrix (Fin (m + 1)) (Fin (m + 1)) ℂ),
      Function.Surjective θ ∧ (∀ b : B, θ b = 0 ↔ (p : B) * b = 0) ∧ θ (p : B) = 1 := by
    rintro ⟨x, hx0, i, m, rfl⟩
    have hne : n i m ≠ 0 := by
      intro h
      refine hx0 ?_
      have hemp : IsEmpty (Fin (n i m)) := by rw [h]; infer_instance
      have hsub : Subsingleton (CStarMatrix (Fin (n i m)) (Fin (n i m)) ℂ) :=
        ⟨fun a b => funext fun j => (hemp.false j).elim⟩
      have h1 : ρ i m (Q i m) = 0 := by
        rw [hρ1 i m]; exact Subsingleton.elim _ _
      have h2 : Q i m * Q i m = 0 := (hQker i m _).mp h1
      rw [(hQc i m).1.isIdempotentElem.eq] at h2
      exact h2
    obtain ⟨j, hj⟩ : ∃ j, n i m = j + 1 := ⟨n i m - 1, (Nat.succ_pred_eq_of_pos
      (Nat.pos_of_ne_zero hne)).symm⟩
    refine ⟨j, (cstarMatrixCongr hj).toStarAlgHom.comp (ρ i m), ?_, ?_, ?_⟩
    · exact (cstarMatrixCongr hj).surjective.comp (hρsurj i m)
    · intro b
      show (cstarMatrixCongr hj) (ρ i m b) = 0 ↔ _
      rw [← hQker i m b]
      constructor
      · intro h
        have := congrArg (cstarMatrixCongr hj).symm h
        simpa using this
      · intro h; rw [h, map_zero]
    · show (cstarMatrixCongr hj) (ρ i m (Q i m)) = 1
      rw [hρ1 i m, map_one]
  choose NN θ hθsurj hθker hθ1 using hpack
  -- assembling the isomorphism
  have hcen' : ∀ p : S, IsStarProjection ((p : B)) ∧ IsCentral B ((p : B)) :=
    fun p => ⟨hSproj _ p.2, hScen _ p.2⟩
  have hrange : Set.range (fun p : S => (p : B)) = S := Subtype.range_coe
  have hsum' : projSup (Set.range (fun p : S => (p : B))) = 1 := by rw [hrange]; exact hSsum
  have horth' : Pairwise fun p q : S => (p : B) * (q : B) = 0 := by
    intro p q hpq
    exact hSorth _ p.2 _ q.2 (fun h => hpq (Subtype.ext h))
  obtain ⟨Ψ, hΨ, -⟩ := cstar_product_2_miu
    (𝒜 := fun p : S => CStarMatrix (Fin (NN p + 1)) (Fin (NN p + 1)) ℂ) θ
  refine ⟨S, NN, ⟨StarAlgEquiv.ofBijective Ψ ⟨?_, ?_⟩⟩⟩
  · -- injectivity
    intro b b' hbb
    refine sub_eq_zero.mp (central_family_separating (fun p : S => (p : B))
      (fun p => hSproj _ p.2) hsum' (a := b - b') fun p => ?_)
    refine (hθker p _).mp ?_
    rw [map_sub]
    have h1 : θ p b = (Ψ b : ∀ p : S, CStarMatrix (Fin (NN p + 1)) (Fin (NN p + 1)) ℂ) p :=
      (hΨ p b).symm
    have h2 : θ p b' = (Ψ b' : ∀ p : S, CStarMatrix (Fin (NN p + 1)) (Fin (NN p + 1)) ℂ) p :=
      (hΨ p b').symm
    rw [h1, h2, hbb, sub_self]
  · -- surjectivity
    intro x
    have hpre : ∀ p : S, ∃ y : B, (p : B) * y = y ∧ θ p y =
        (x : ∀ p : S, CStarMatrix (Fin (NN p + 1)) (Fin (NN p + 1)) ℂ) p ∧
        ‖y‖ ≤ ‖x‖ := by
      intro p
      obtain ⟨y, hy⟩ := hθsurj p ((x : ∀ p : S, _) p)
      refine ⟨(p : B) * y, ?_, ?_, ?_⟩
      · rw [← mul_assoc, (hSproj _ p.2).isIdempotentElem.eq]
      · rw [map_mul, hθ1 p, one_mul, hy]
      · have hiso := (starAlgHom_norm_corner (θ p) (hSproj _ p.2) (hScen _ p.2)
          (hθker p)).2 ((p : B) * y) (by rw [← mul_assoc, (hSproj _ p.2).isIdempotentElem.eq])
        rw [← hiso, map_mul, hθ1 p, one_mul, hy]
        exact lp.norm_apply_le_norm (by simp) x p
    choose y hy1 hy2 hy3 using hpre
    obtain ⟨a, ha, -⟩ := central_projections_sums_2 (fun p : S => (p : B)) hcen' horth' hsum'
      y hy1 ⟨‖x‖, by rintro _ ⟨p, rfl⟩; exact hy3 p⟩
    refine ⟨a, ?_⟩
    refine Subtype.ext (funext fun p => ?_)
    rw [hΨ p a]
    have h1 : θ p a = θ p ((p : B) * a) := by rw [map_mul, hθ1 p, one_mul]
    rw [h1, ha p, hy2 p]

end HAMain

/-- **84bV** (`ha-equalisers`, vn.tex:6237, Corollary): for nmiu-maps
`f, g : A → B` between hereditarily atomic von Neumann algebras, the
equaliser `E = {a | f(a) = g(a)}` is (the image of) a hereditarily atomic
von Neumann algebra, **and its inclusion `e` is an equaliser of `f` and `g`
both in `haW*_miu` and in `haW*_cpsu`.**

The two categories are not bundled (cf. 47II), so — exactly as for **47V**
`vn_equalisers_miu`/`vn_equalisers_cpsu`, of which these two clauses are the
restrictions to the full subcategories of *hereditarily atomic* algebras —
the universal property is spelt out: every nmiu- (resp. ncpsu-) map `h` out
of a hereditarily atomic `D` that equalises `f` and `g` factors uniquely
through `e`.  Being full subcategories, the mediating map produced by 47V
already lies in `haW*`; nothing beyond hereditary atomicity of `D` is
needed, and that hypothesis is carried only to make the clause the statement
about `haW*` that the Corollary asserts. -/
theorem ha_equalisers [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (hA : HereditarilyAtomic A) (hB : HereditarilyAtomic B)
    (f g : NMIUMap A B) :
    ∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
      (_ : StarOrderedRing C) (_ : VonNeumannAlgebra C),
      ∃ e : NMIUMap C A, HereditarilyAtomic C ∧ Function.Injective e ∧
        Set.range ⇑e = {a : A | f a = g a} ∧
        -- the equaliser property in `haW*_miu`
        (∀ (D : Type u) (_ : CStarAlgebra D) (_ : PartialOrder D)
            (_ : StarOrderedRing D) (_ : VonNeumannAlgebra D),
          HereditarilyAtomic D → ∀ h : NMIUMap D A,
            (∀ d : D, f (h d) = g (h d)) →
              ∃! m : NMIUMap D C, ∀ d : D, e (m d) = h d) ∧
        -- and in `haW*_cpsu`
        (∀ (D : Type u) (_ : CStarAlgebra D) (_ : PartialOrder D)
            (_ : StarOrderedRing D) (_ : VonNeumannAlgebra D),
          HereditarilyAtomic D → ∀ h : NCPSUMap D A,
            (∀ d : D, f (h.toNCPMap d) = g (h.toNCPMap d)) →
              ∃! m : NCPSUMap D C, ∀ d : D,
                e (m.toNCPMap d) = h.toNCPMap d) := by
  classical
  -- **47V**: the equaliser is a von Neumann subalgebra `S ⊆ A`; `VNSub A S hS`
  -- bundles it as a von Neumann algebra, and **84bIII** makes it hereditarily
  -- atomic because its inclusion is an injective nmiu-map into `A`.
  obtain ⟨S, hS, hSet⟩ := vn_equalisers f g
  set e₀ : VNSub A S hS →⋆ₐ[ℂ] A :=
    { toFun := VNSub.val
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun r => by
        show (algebraMap ℂ (VNSub A S hS) r).val = algebraMap ℂ A r
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        rfl
      map_star' := fun _ => rfl } with he₀
  have hnorm : PreservesDirSups ⇑e₀ := by
    intro D s hne hdir hlub
    have h := isLUB_coe_of_isLUB (hne.image _) (VNSub.isLUB_saMap_image hne hdir hlub)
    rw [← Set.image_comp] at h
    exact h
  have hrange : Set.range (⇑(⟨e₀, hnorm⟩ : NMIUMap (VNSub A S hS) A))
      = {a : A | f a = g a} := by
    rw [← hSet]
    exact VNSub.range_val
  refine ⟨VNSub A S hS, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨e₀, hnorm⟩, hereditarilyAtomic_subalgebra hA ⟨e₀, hnorm⟩ VNSub.val_injective,
    VNSub.val_injective, hrange, ?_, ?_⟩
  · -- `haW*_miu` is a full subcategory of `W*_miu`, so this is **47V**
    intro D _ _ _ _ _ h hfg
    exact vn_equalisers_miu f g ⟨e₀, hnorm⟩ VNSub.val_injective hrange h hfg
  · intro D _ _ _ _ _ h hfg
    exact vn_equalisers_cpsu f g ⟨e₀, hnorm⟩ VNSub.val_injective hrange h hfg

/-! **84bVI** (vn.tex:6252, Remark): `haW*_miu` is the least full
subcategory of `W*_miu` closed under limits containing the
finite-dimensional von Neumann algebras — categorical remark, not
converted. -/

end Theses.A.VN
