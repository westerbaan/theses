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
          pinv (star a * a) = pinv a * star (pinv a)) :=
  sorry

/-- **79VI** (`pseudoinverse-basic-2`, vn.tex:5203, Exercise), part 1: a
positive `a` is pseudoinvertible iff `at = ⌈a⌉` for some positive `t`
(equivalently: `a` is invertible in the corner `⌈a⌉A⌈a⌉`); such `t`
commutes with `a`. -/
theorem pseudoinverse_basic_2'_1 (a : A) (ha : 0 ≤ a) :
    (Pseudoinvertible A a ↔ ∃ t : A, 0 ≤ t ∧ a * t = ceil a) ∧
      ∀ t : A, 0 ≤ t → a * t = ceil a → a * t = t * a :=
  sorry

/-- **79VI** (`pseudoinverse-basic-2`, vn.tex:5203, Exercise), part 2: a
positive `a` is pseudoinvertible iff `λ⌈a⌉ ≤ a` for some `λ > 0`. -/
theorem pseudoinverse_basic_2'_2 (a : A) (ha : 0 ≤ a) :
    Pseudoinvertible A a ↔ ∃ l : ℝ, 0 < l ∧ (l : ℂ) • ceil a ≤ a :=
  sorry

/-- **79VI** (`pseudoinverse-basic-2`, vn.tex:5203, Exercise), part 3: for
pseudoinvertible positive `a`: `⌈a^{∼1}⌉ = ⌈a⌉`, and whatever commutes
with `a` commutes with `a^{∼1}` (i.e. `a^{∼1} ∈ {a}^□□`). -/
theorem pseudoinverse_basic_2'_3 (a : A) (ha : 0 ≤ a)
    (hp : Pseudoinvertible A a) :
    ceil (pinv a) = ceil a ∧
      ∀ b : A, b * a = a * b → b * pinv a = pinv a * b :=
  sorry

/-- **79VI** (`pseudoinverse-basic-2`, vn.tex:5203, Exercise), part 4:
`c^{∼1} ≤ b^{∼1}` for pseudoinvertible positive *commuting* `b ≤ c`. -/
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
