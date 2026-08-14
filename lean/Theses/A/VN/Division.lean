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
    Hereditarily Atomic Von Neumann Algebras  (parsec 842)

Statements only; every proof is `sorry`.  See `Theses/A/VN/Basic.lean` for
the topologies and `Theses/A/VN/Projections.lean` for `ceil`, `suppProj`
(`⌈a⌋`), `rangeProj` (`⌊a⌉`), `projSup`, `cceil`.
-/
import Theses.A.VN.Completeness

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

/-- **79VI** (`pseudoinverse-basic-2`, vn.tex:5203, Exercise), part 1: a
positive `a` is pseudoinvertible iff `at = ⌈a⌉` for some positive `t`
(equivalently: `a` is invertible in the corner `⌈a⌉A⌈a⌉`); such `t`
commutes with `a`. -/
theorem pseudoinverse_basic_2'_1 (a : A) (ha : 0 ≤ a) :
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
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- `⟹`: the pseudoinverse is positive
    intro h
    refine ⟨pinv a, pinv_nonneg ha h, ?_⟩
    rw [(pinv_spec h).2.2.2, hrange]
  · -- `⟸`: cut `t` down to the corner `⌈a⌉A⌈a⌉`
    rintro ⟨t, -, hat⟩
    set p := ceil a with hpdef
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
    refine (pseudoinverse_basic_2'_1 a ha).1.mpr ⟨c * p, ?_, ?_⟩
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

/-- **79VI**.4 applied to `b = p` (a projection) and `c = 1` would force
`p = 1`: both are positive, commuting and pseudoinvertible with `p ≤ 1`, and
`p^{∼1} = p`, `1^{∼1} = 1`. -/
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

/-- **79VI**.4 (vn.tex:5222) is **false as stated** — ERRATA `79VI.4`.  Take
`b = (1,0)` and `c = (1,1)` in `ℓ^∞({0,1})`: both are positive, commuting and
pseudoinvertible (projections are their own pseudoinverses) with `b ≤ c`,
`b^{∼1} = b` and `c^{∼1} = c`, and `c ≰ b`.  What the exercise needs is the
extra hypothesis `⌈b⌉ = ⌈c⌉`; without it the pseudoinverse *grows* where the
carrier of `c` exceeds that of `b`.  The parenthetical remark that the
statement holds without the commutation hypothesis is false for the same
reason. -/
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

/-- **79VI** (`pseudoinverse-basic-2`, vn.tex:5203, Exercise), part 4:
`c^{∼1} ≤ b^{∼1}` for pseudoinvertible positive *commuting* `b ≤ c`.

**False as stated** — see `pseudoinverse_basic_2'_4_is_false` just above and
`ERRATA.md`.  The statement is kept verbatim (and `sorry`) pending an author
decision; with `⌈b⌉ = ⌈c⌉` added it is true. -/
theorem pseudoinverse_basic_2'_4 (b c : A) (hb : 0 ≤ b)
    (hbp : Pseudoinvertible A b) (hcp : Pseudoinvertible A c) (hbc : b ≤ c)
    (hcomm : b * c = c * b) : pinv c ≤ pinv b :=
  sorry

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
      ¬Pseudoinvertible (lp (fun _ : ℕ => ℂ) ∞) x :=
  sorry

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

/-- **80III** (`approximate-pseudoinverse-reduction`, vn.tex:5270,
Exercise): if `t₁, t₂, …` is an approximate pseudoinverse of `b*b`, then
`t₁b*, t₂b*, …` is one of `b`. -/
theorem approximate_pseudoinverse_reduction (b : A) (t : ℕ → A)
    (h : IsApproxPseudoinverse A (star b * b) t) :
    IsApproxPseudoinverse A b (fun n => t n * star b) :=
  sorry

/-- **80IV** (`approximate-pseudoinverse`, vn.tex:5278, Theorem): every
element of a von Neumann algebra has an approximate pseudoinverse. -/
theorem approximate_pseudoinverse (a : A) :
    ∃ t : ℕ → A, IsApproxPseudoinverse A a t :=
  sorry

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
`c ∈ bA`… (thesis: for every element `c` of `Ab`). -/
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
`d ∈ ⌈a⌋A⌊b⌉` with `c = adb`. -/
theorem division_basic_3 (a b c : A) (h : ∃ d : A, c = a * d * b) :
    (∃ d : A, ldiv a c = d * b) ∧ (∃ d : A, div c b = a * d) ∧
      div (ldiv a c) b = ldiv a (div c b) ∧
      (∃! d : A, c = a * d * b ∧ suppProj a * d = d ∧
        d * rangeProj b = d) :=  by
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
  refine ⟨⟨suppProj a * d, hl⟩, ⟨d * rangeProj b, hr⟩, ?_, ?_⟩
  · rw [hl, hr, (division_basic_2 (suppProj a * d) b).1,
      (division_basic_2 (d * rangeProj b) a).2, mul_assoc]
  · refine ⟨suppProj a * d * rangeProj b, ⟨?_, ?_, hidem⟩, ?_⟩
    · rw [hd, habs]
    · rw [← mul_assoc, ← mul_assoc, hsa.isIdempotentElem.eq]
    · -- uniqueness: cancel `b` on the right (**60VIII**), then `a` on the left
      rintro e ⟨he, hea, heb⟩
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

/-- **81III** (`proto-douglas`, vn.tex:5395, Lemma), part 1: if
`a*a ≤ b*b` then `a ∈ Ab`, and the series `∑ₙ atₙ` (for an approximate
pseudoinverse `t` of `b`) converges ultrastrongly to `a/b`. -/
theorem proto_douglas_1 (a b : A) (h : star a * a ≤ star b * b)
    (t : ℕ → A) (ht : IsApproxPseudoinverse A b t) :
    (∃ c : A, a = c * b) ∧
      USTendsto (fun N : ℕ => ∑ n ∈ Finset.range N, a * t n) atTop
        (div a b) :=
  sorry

/-- **81III** (`proto-douglas`, vn.tex:5395, Lemma), part 2: the
convergence of `∑ₙ atₙ` to `a/b` is uniform in `a` (over
`{a | a*a ≤ b*b}`). -/
theorem proto_douglas_2 (b : A) (t : ℕ → A)
    (ht : IsApproxPseudoinverse A b t) (ω : NPFunctional A) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ a : A, star a * a ≤ star b * b → ∀ M ≥ N,
      omegaNorm A ω (div a b - ∑ n ∈ Finset.range M, a * t n) ≤ ε :=
  sorry

/-- **81V** (`douglas`, vn.tex:5461, Exercise), part 1 (Douglas' lemma):
`a ∈ (A)_λ·b` iff `a*a ≤ λ²b*b`, and then `‖a/b‖ ≤ λ`. -/
theorem douglas_1 (a b : A) (l : ℝ) (hl : 0 ≤ l) :
    ((∃ c : A, ‖c‖ ≤ l ∧ a = c * b) ↔
        star a * a ≤ ((l : ℂ) ^ 2) • (star b * b)) ∧
      (star a * a ≤ ((l : ℂ) ^ 2) • (star b * b) → ‖div a b‖ ≤ l) :=
  sorry

/-- **81V** (`douglas`, vn.tex:5461, Exercise), part 2: `a ∈ A⌊b⌉` need
not entail `a ∈ Ab` (a counterexample exists, e.g. in `ℓ^∞(ℕ)`). -/
theorem douglas_2 :
    ∃ a b : lp (fun _ : ℕ => ℂ) ∞,
      a * rangeProj b = a ∧ ¬∃ c, a = c * b :=
  sorry

/-- **81VI** (`sequential-douglas`, vn.tex:5480, Exercise), part 1: for
positive `a` and `λ ≥ 0`: `a ∈ b*(A)_λ b` iff `a ≤ λb*b`, and then
`‖b*∖a/b‖ ≤ λ`. -/
theorem sequential_douglas_1 (a b : A) (ha : 0 ≤ a) (l : ℝ) (hl : 0 ≤ l) :
    ((∃ c : A, ‖c‖ ≤ l ∧ a = star b * c * b) ↔
        a ≤ (l : ℂ) • (star b * b)) ∧
      (a ≤ (l : ℂ) • (star b * b) →
        ‖ldiv (star b) (div a b)‖ ≤ l) :=
  sorry

/-- **81VI** (`sequential-douglas`, vn.tex:5480, Exercise), part 2:
`b*∖a/b` is positive for positive `a ∈ b*Ab`. -/
theorem sequential_douglas_2 (a b : A) (ha : 0 ≤ a)
    (h : ∃ c : A, a = star b * c * b) :
    0 ≤ ldiv (star b) (div a b) :=
  sorry

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
      atTop (ldiv c (div a b)) :=
  sorry

/-- **81VIII** (`sequential-quotient`, vn.tex:5513, Exercise), part 1: for
positive `a`, `b`: `a ≤ λb` for some `λ ≥ 0` iff `a = √b c √b` for some
positive `c`. -/
theorem sequential_quotient_1 (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∃ l : ℝ, 0 ≤ l ∧ a ≤ (l : ℂ) • b) ↔
      ∃ c : A, 0 ≤ c ∧ a = CFC.sqrt b * c * CFC.sqrt b :=
  sorry

/-- **81VIII** (`sequential-quotient`, vn.tex:5513, Exercise), part 2: in
that case there is a *unique* positive `c` with `a = √b c √b` and
`⌈c⌉ ≤ ⌈b⌉`; and for an approximate pseudoinverse `t` of `√b` the double
series `∑_{m,n} tₘ a tₙ` converges ultraweakly to this `c`. -/
theorem sequential_quotient_2 (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (l : ℝ) (hl : 0 ≤ l) (hab : a ≤ (l : ℂ) • b) (t : ℕ → A)
    (ht : IsApproxPseudoinverse A (CFC.sqrt b) t) :
    ∃! c : A, (0 ≤ c ∧ a = CFC.sqrt b * c * CFC.sqrt b ∧
        ceil c ≤ ceil b) ∧
      UWTendsto
        (fun N : ℕ => ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          t m * a * t n) atTop c :=
  sorry

/-- **81IX** (`div-usc`, vn.tex:5533, Lemma): the maps
`a ↦ a/b : (A)₁b → A` and `a ↦ c∖a/b : c(A)₁b → A` are ultrastrongly
continuous.  (**81XI**, Remark: this fails on the larger domain `Ab` —
not converted.) -/
theorem div_usc (b c : A) :
    @ContinuousOn A A (ultrastrong A) (ultrastrong A) (fun a => div a b)
        {a : A | ∃ d : A, ‖d‖ ≤ 1 ∧ a = d * b} ∧
      @ContinuousOn A A (ultrastrong A) (ultrastrong A)
        (fun a => ldiv c (div a b))
        {a : A | ∃ d : A, ‖d‖ ≤ 1 ∧ a = c * d * b} :=
  sorry

/-! ## Parsec 820: polar decomposition -/

/-- **82I** (`polar-decomposition`, vn.tex:5579, Proposition (Polar
Decomposition)): the partial isometry `[a] = a/√(a*a)` of the polar
decomposition `a = [a]√(a*a)`. -/
noncomputable def polar (a : A) : A := div a (CFC.sqrt (star a * a))

/-- **82I** (`polar-decomposition`, vn.tex:5579, Proposition (Polar
Decomposition)), main claim: every `a` can be written *uniquely* as
`a = u√(a*a)` with `u ∈ A⌈a⌋`; namely `u = [a]`. -/
theorem polar_decomposition (a : A) :
    (∃! u : A, a = u * CFC.sqrt (star a * a) ∧ u * suppProj a = u) ∧
      a = polar a * CFC.sqrt (star a * a) ∧
      polar a * suppProj a = polar a :=
  sorry

/-- **82I** (`polar-decomposition`, vn.tex:5579, Proposition), part 1:
`[a]` is a partial isometry with `[a]*[a] = ⌈a*a⌉ = ⌈a⌋` and
`[a][a]* = ⌈aa*⌉ = ⌊a⌉`. -/
theorem polar_decomposition_1 (a : A) :
    IsPartialIsometry A (polar a) ∧
      star (polar a) * polar a = suppProj a ∧
      polar a * star (polar a) = rangeProj a :=
  sorry

/-- **82I** (`polar-decomposition`, vn.tex:5579, Proposition), part 2:
`[a*] = [a]*`, so that `√(aa*)[a] = a = [a]√(a*a)`. -/
theorem polar_decomposition_2 (a : A) :
    polar (star a) = star (polar a) ∧
      CFC.sqrt (a * star a) * polar a = a :=
  sorry

/-! ## Parsec 830: the Murray–von Neumann preorder

**83I** (vn.tex:5656): introduction — nothing to formalize. -/

variable (A) in
/-- **83II** (`vmleq`, vn.tex:5666, Proposition): the **Murray–von Neumann
preorder**: `e' ⊴ e` when `e' = u*u` and `uu* ≤ e` for some partial
isometry `u`. -/
def MvNLE (e' e : A) : Prop :=
  ∃ u : A, IsPartialIsometry A u ∧ star u * u = e' ∧ u * star u ≤ e

/-- **83II** (`vmleq`, vn.tex:5666, Proposition): for projections `e'`,
`e` the following are equivalent: (1) `e' = ⌈a*ea⌉` for some `a`;
(2) `e' = ⌈a⌋` and `⌊a⌉ ≤ e` for some `a`; (3) `e' ⊴ e`. -/
theorem vmleq (e' e : A) (he' : IsStarProjection e')
    (he : IsStarProjection e) :
    List.TFAE
      [∃ a : A, e' = ceil (star a * e * a),
       ∃ a : A, e' = suppProj a ∧ rangeProj a ≤ e,
       MvNLE A e' e] :=
  sorry

/-- **83IV** (`mvn-preorders`, vn.tex:5702, Exercise): `⊴` preorders the
projections of a von Neumann algebra. -/
theorem mvn_preorders :
    (∀ p : A, IsStarProjection p → MvNLE A p p) ∧
      ∀ p q r : A, IsStarProjection p → IsStarProjection q →
        IsStarProjection r → MvNLE A p q → MvNLE A q r → MvNLE A p r :=
  sorry

/-- **83V** (`cceil-sum`, vn.tex:5706, Lemma): for a projection `e` there
is a family `(eᵢ)` of non-zero pairwise orthogonal projections with
`⌈⌈e⌉⌉ = ∑ᵢ eᵢ` and `eᵢ ⊴ e` for all `i`. -/
theorem cceil_sum (e : A) (he : IsStarProjection e) :
    ∃ (ι : Type u) (e' : ι → A),
      (∀ i, IsStarProjection (e' i) ∧ e' i ≠ 0 ∧ MvNLE A (e' i) e) ∧
      (Pairwise fun i j => e' i * e' j = 0) ∧
      cceil e = projSup (Set.range e') :=
  sorry

end Pseudoinverse

/-! ## Parsec 840: finite-dimensional C*-algebras

**84I** (vn.tex:5752): introduction — nothing to formalize. -/

/-- **84II** (`fdcstar`, vn.tex:5756, Theorem): every finite-dimensional
C*-algebra is (miu-isomorphic to) a finite direct sum of full matrix
algebras `⊕ₘ M_{Nₘ}`. -/
theorem fdcstar (A : Type u) [CStarAlgebra A] [FiniteDimensional ℂ A] :
    ∃ (M : ℕ) (N : Fin M → ℕ),
      Nonempty (A ≃⋆ₐ[ℂ] ∀ m : Fin M, Matrix (Fin (N m)) (Fin (N m)) ℂ) :=
  sorry

/-! **84aI** (`cstar-no-pu-equalisers-example`, vn.tex:6007, Example): the
pu-maps `f, g : ℂ⁴ → ℂ`, `f(a,b,c,d) = ½(a+b)`, `g(a,b,c,d) = ½(c+d)` have
no equaliser in the category `CStar_pu`.
-- FIXME(typecheck): not converted — the category `CStar_pu` is not
formalized (cf. 47II), and the statement is an existence-negation over all
C*-algebras with pu-maps, whose faithful rendering would require the
categorical framework. -/

/-! ## Parsec 842: hereditarily atomic von Neumann algebras

**84bI** (vn.tex:6101): introduction (Kornell's programme) — nothing to
formalize. -/

variable (A) in
/-- **84bII** (`def:hereditarily-atomic`, vn.tex:6143, Definition): a von
Neumann algebra is **hereditarily atomic** if it is nmiu-isomorphic to a
direct sum `⊕ᵢ M_{Nᵢ}` of (possibly infinitely many) full matrix algebras.
(The summands are rendered as `M_{Nᵢ₊₁}` to keep them nontrivial, which
loses no generality.  The full subcategories `haW*_miu`, `haW*_cpsu` are
not bundled, cf. 47II.) -/
def HereditarilyAtomic : Prop :=
  ∃ (I : Type u) (N : I → ℕ),
    Nonempty (A ≃⋆ₐ[ℂ]
      lp (fun i : I => CStarMatrix (Fin (N i + 1)) (Fin (N i + 1)) ℂ) ∞)

/-- **84bIII** (vn.tex:6157, Proposition): a von Neumann subalgebra of a
hereditarily atomic von Neumann algebra is hereditarily atomic — rendered:
if `B` embeds into hereditarily atomic `A` by an injective nmiu-map, then
`B` is hereditarily atomic. -/
theorem hereditarilyAtomic_subalgebra [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (hA : HereditarilyAtomic A) (f : NMIUMap B A)
    (hf : Function.Injective f) : HereditarilyAtomic B :=
  sorry

/-- **84bV** (`ha-equalisers`, vn.tex:6209, Corollary): for nmiu-maps
`f, g : A → B` between hereditarily atomic von Neumann algebras, the
equaliser `E = {a | f(a) = g(a)}` is (the image of) a hereditarily atomic
von Neumann algebra, whose inclusion is the equaliser of `f` and `g` in
`haW*_miu` and `haW*_cpsu`. -/
theorem ha_equalisers [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (hA : HereditarilyAtomic A) (hB : HereditarilyAtomic B)
    (f g : NMIUMap A B) :
    ∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
      (_ : StarOrderedRing C),
      ∃ e : NMIUMap C A, HereditarilyAtomic C ∧ Function.Injective e ∧
        Set.range ⇑e = {a : A | f a = g a} :=
  sorry

/-! **84bVI** (vn.tex:6224, Remark): `haW*_miu` is the least full
subcategory of `W*_miu` closed under limits containing the
finite-dimensional von Neumann algebras — categorical remark, not
converted. -/

end Theses.A.VN
