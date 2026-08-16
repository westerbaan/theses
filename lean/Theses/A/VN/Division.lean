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

/-- **81IX** (`div-usc`, vn.tex:5533, Lemma), **first half**: `a ↦ a/b` is
ultrastrongly continuous on `(A)₁b`.  This is the thesis's own argument
(vn.tex:5541): by **81III**.2 the partial sums `a ↦ ∑_{n<N} a tₙ` converge to
`a/b` *uniformly* on `(A)₁b` (in each seminorm `‖·‖_ω` separately, which is
all that is needed), and each partial sum is `a ↦ a·(∑_{n<N} tₙ)`, which is
ultrastrongly continuous because `‖yd‖_ω = ‖y‖_{d*ωd}` (**44VIII**).

The *second* half of 81IX — ultrastrong continuity of `a ↦ c∖a/b` on
`c(A)₁b` — is **false**; see the note on `div_usc` below. -/
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

/-- **81IX** (`div-usc`, vn.tex:5533, Lemma): the maps
`a ↦ a/b : (A)₁b → A` and `a ↦ c∖a/b : c(A)₁b → A` are ultrastrongly
continuous.  (**81XI**, Remark: this fails on the larger domain `Ab` —
not converted.)

**The second conjunct is false**, so this statement is left `sorry`; the
first conjunct is `div_usc_ball` above.  Counterexample to the second, with
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
topology.  See ERRATA.md. -/
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

/-- **82I** (`polar-decomposition`, vn.tex:5579, Proposition (Polar
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

/-- **82I** (`polar-decomposition`, vn.tex:5579, Proposition), part 1:
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

/-- **82I** (`polar-decomposition`, vn.tex:5579, Proposition), part 2:
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
       MvNLE A e' e] := by
  -- `he'` is redundant: each of the three conditions already forces `e'` to
  -- be a projection (see PROVING-LOG).
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

/-- **83IV** (`mvn-preorders`, vn.tex:5702, Exercise): `⊴` preorders the
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

/-- **83V** (`cceil-sum`, vn.tex:5706, Lemma): for a projection `e` there
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
  -- some `e a p` is non-zero
  have hex : ∃ a : A, e * a * p ≠ 0 := by
    by_contra hcon
    have hall : ∀ a : A, e * a * p = 0 := fun a => by
      by_contra h; exact hcon ⟨a, h⟩
    have hkey : ∀ a : A, ceil (star a * e * a) * p = 0 := by
      intro a
      have hconj : star (e * a * p) * (e * a * p) = p * (star a * e * a) * p := by
        calc star (e * a * p) * (e * a * p)
            = p * (star a * (e * e) * a) * p := by
              rw [star_mul, star_mul, he.isSelfAdjoint.star_eq,
                hpproj.isSelfAdjoint.star_eq]
              noncomm_ring
          _ = p * (star a * e * a) * p := by rw [he.isIdempotentElem.eq]
      have h0 : p * (star a * e * a) * p = 0 := by
        rw [← hconj, hall a, star_zero, zero_mul]
      have hsqrtsa : star (CFC.sqrt (star a * e * a)) = CFC.sqrt (star a * e * a) :=
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
      have hs : CFC.sqrt (star a * e * a) * p = 0 := by
        refine (CStarRing.star_mul_self_eq_zero_iff _).mp ?_
        rw [star_mul, hsqrtsa, hpproj.isSelfAdjoint.star_eq]
        calc p * CFC.sqrt (star a * e * a) *
              (CFC.sqrt (star a * e * a) * p)
            = p * (CFC.sqrt (star a * e * a) * CFC.sqrt (star a * e * a)) * p := by
              noncomm_ring
          _ = p * (star a * e * a) * p := by
              rw [CFC.sqrt_mul_sqrt_self _ (hnn a)]
          _ = 0 := h0
      exact ceil_mul_eq_zero (hnn a) ((sqrt_mul_eq_zero_iff (hnn a) p).mp hs)
    have hle1 : cceil e ≤ 1 - p := by
      rw [(cceil_fundamental e he).2]
      refine (projSup_spec hsetproj).2.2 (1 - p) hpproj.one_sub ?_
      rintro _ ⟨a, rfl⟩
      exact ((orthogonal_tuple_of_projections_1 (ceil (star a * e * a)) p
        (hceilproj a) hpproj).out 0 4).mp (hkey a)
    have hpp : p * p = 0 :=
      ((orthogonal_tuple_of_projections_1 p p hpproj hpproj).out 4 0).mp
        (hple.trans hle1)
    exact hpne (by rw [← hpproj.isIdempotentElem.eq, hpp])
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
