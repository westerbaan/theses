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
  sorry

open scoped Classical in
/-- **79I** (`dfn-pseudoinverse`, vn.tex:5090, Definition): the
pseudoinverse `a^{∼1}` of `a` (junk value `0` when `a` is not
pseudoinvertible). -/
noncomputable def pinv (a : A) : A :=
  if h : Pseudoinvertible A a then h.choose else 0

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
       IsPseudoinverse A t a] :=
  sorry

/-- **79IV** (`partial-isometry-equivalents`, vn.tex:5172, Exercise): `u`
is a partial isometry iff `u*u` is a projection iff `uu*u = u` iff `uu*`
is a projection iff `u*uu* = u*`. -/
theorem partial_isometry_equivalents (u : A) :
    List.TFAE
      [IsPartialIsometry A u,
       IsStarProjection (star u * u),
       u * star u * u = u,
       IsStarProjection (u * star u),
       star u * u * star u = star u] :=
  sorry

/-- **79V** (`pseudoinverse-basic`, vn.tex:5183, Exercise), part 1: `a` is
pseudoinvertible iff `a*` is, and then `(a*)^{∼1} = (a^{∼1})*`. -/
theorem pseudoinverse_basic_1 (a : A) :
    (Pseudoinvertible A a ↔ Pseudoinvertible A (star a)) ∧
      (Pseudoinvertible A a → pinv (star a) = star (pinv a)) :=
  sorry

/-- **79V** (`pseudoinverse-basic`, vn.tex:5183, Exercise), part 2: if `a`,
`b` are pseudoinvertible and `⌊b⌉ = ⌈a⌋`, then `ab` is pseudoinvertible
with `(ab)^{∼1} = b^{∼1}a^{∼1}`. -/
theorem pseudoinverse_basic_2 (a b : A) (ha : Pseudoinvertible A a)
    (hb : Pseudoinvertible A b) (hab : rangeProj b = suppProj a) :
    Pseudoinvertible A (a * b) ∧ pinv (a * b) = pinv b * pinv a :=
  sorry

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
    ∃! c : A, a = c * b ∧ c * rangeProj b = c :=
  sorry

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

/-- **81II** (vn.tex:5358, Exercise), part 1: `c/b ∈ ⌊c⌉A⌊b⌉` for
`c ∈ bA`… (thesis: for every element `c` of `Ab`). -/
theorem division_basic_1 (b c : A) (h : ∃ d : A, c = d * b) :
    rangeProj c * div c b = div c b ∧ div c b * rangeProj b = div c b :=
  sorry

/-- **81II** (vn.tex:5358, Exercise), part 2: `(ab)/b = a⌊b⌉` and
`b∖(ba) = ⌈b⌋a`. -/
theorem division_basic_2 (a b : A) :
    div (a * b) b = a * rangeProj b ∧ ldiv b (b * a) = suppProj b * a :=
  sorry

/-- **81II** (vn.tex:5358, Exercise), part 3: for `c ∈ aAb`:
`a∖c ∈ Ab`, `c/b ∈ aA`, and `(a∖c)/b = a∖(c/b) =: a∖c/b` is the unique
`d ∈ ⌈a⌋A⌊b⌉` with `c = adb`. -/
theorem division_basic_3 (a b c : A) (h : ∃ d : A, c = a * d * b) :
    (∃ d : A, ldiv a c = d * b) ∧ (∃ d : A, div c b = a * d) ∧
      div (ldiv a c) b = ldiv a (div c b) ∧
      (∃! d : A, c = a * d * b ∧ suppProj a * d = d ∧
        d * rangeProj b = d) :=
  sorry

/-- **81II** (vn.tex:5358, Exercise), part 4: for `c ∈ Ab` and `d ∈ aA`:
`dc ∈ aAb` and `a∖(dc)/b = (a∖d)(c/b)`. -/
theorem division_basic_4 (a b c d : A) (hc : ∃ x : A, c = x * b)
    (hd : ∃ x : A, d = a * x) :
    (∃ x : A, d * c = a * x * b) ∧
      ldiv a (div (d * c) b) = ldiv a d * div c b :=
  sorry

/-- **81II** (vn.tex:5358, Exercise), part 5: for `c ∈ Ab`: `c* ∈ b*A` and
`b*∖c* = (c/b)*`. -/
theorem division_basic_5 (b c : A) (h : ∃ x : A, c = x * b) :
    (∃ x : A, star c = star b * x) ∧
      ldiv (star b) (star c) = star (div c b) :=
  sorry

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
