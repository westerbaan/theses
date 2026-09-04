/-
Theses/B/Eff/OrderUnit.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), lines
2032–2041: the two order-theoretic examples of an effectus in total form
listed in point 189aII — the category `OUSᵒᵖ` of order unit spaces
(189aII.1) and the category `OUGᵒᵖ` of order unit groups (189aII.2).

Design:
* `OrderUnitSpace X` and `OrderUnitGroup G` are *mixins* over Mathlib's
  `AddCommGroup` / `Module ℝ` / `PartialOrder`, in the style of `WStar`
  in `WStarCat.lean`: translation-invariance of `≤`, closure of the
  positive cone under non-negative scalars (spaces only), a distinguished
  `unit`, and the order-unit axiom `∀ x, ∃ n : ℕ, x ≤ n • unit`.  Being a
  mixin, the definition adds no instance of an algebraic class, so the
  products, `ULift`s and one-point spaces below carry exactly Mathlib's
  own algebraic and order structure.
* Archimedeanness is deliberately *not* part of the definition: 190IV.1's
  parenthetical makes it a property of a single space, not an axiom.  It is
  `OUSArchimedean`, in the literature's form (`ousArchimedean_iff_nsmul`),
  with the Minkowski gauge `ouGauge` of the unit and the Hahn–Banach
  separation `ou_exists_state` beside it.
* Positivity of the unit is an axiom for order unit *groups* and a
  *theorem* for order unit *spaces* (`ou_unit_nonneg`): in the real case
  `-u ≤ n • u` gives `0 ≤ (n+1) • u`, and one may divide by `n+1`.  In a
  group one may not — `ℤ` with positive cone `2ℕ` is a partially ordered
  abelian group in which `1` is an order unit that is not positive — so
  there the standard (Goodearl) requirement `0 ≤ unit` is listed.
* Objects are bundled (`OUS`, `OUG` : `Type (u+1)`) and morphisms are
  structures on top of Mathlib's `→ₗ[ℝ]` resp. `→+`, so that identity,
  composition and the three category laws are definitional.
* The effectus proofs are the `vNᵒᵖ` proofs of `VNExamples.lean`
  transcribed: the same concrete presentation of `CoprodPres` (final
  object = the scalars, binary coproducts = products), the same two
  mediating maps `γ(x,y) = β(x,0) + α(0,y)` and `γ(x) = α(x,0)`, and the
  same joint monicity argument on `1+1+1`.  The two places where the
  C\*-argument used the norm are replaced by the order unit: every
  element is a difference of two positive elements
  (`ou_eq_sub_of_nonneg`, `oug_eq_sub_of_nonneg`), and `c ≤ n • 1` for
  `c ≥ 0`, which is the order-unit axiom itself.
* The predicates, states and scalars of `OUSᵒᵖ` and `OUGᵒᵖ` (190IV.1 and
  190IV.2, eff.tex:2148-2166) are computed in the last third of the file,
  in the partial form `Par OUS.{u}ᵒᵖ` / `Par OUG.{u}ᵒᵖ` where `Pred`,
  `Stat`, `Scal`, `SeparatingPredicates` and `SeparatingStates` live
  (190II).  The effectus structure of the two categories is therefore
  promoted from the `have`s inside `effectus_ous` / `effectus_oug` to
  named instances (`effectusTotalForm_ous`, `effectusTotalForm_oug` and
  the `HasTerminal` / `HasFiniteCoproducts` they rest on); the two
  bundled theorems keep their statements and are three lines each.
* ⚠ **190IV.2 is false as printed**: `OUGᵒᵖ` does *not* have separating
  predicates.  `oug_no_separating_predicates` refutes it with the order
  unit group `ℤ²` whose positive cone is `{0} ∪ {(a,b) : a ≥ 1, b ≥ 0}`
  and whose order unit is `(1,1)`: its only effects are `0` and `1`, so
  the predicates see only the diagonal, on which the two distinct
  positive unital maps `(x,n) ↦ x₁` and `(x,n) ↦ x₂` into `ℤ` agree.
  Separating predicates would need the effects `[0,1]` to generate the
  group, which "ordered abelian group with order unit" does not give.
* ⚠ **190IV.1's parenthetical is false as printed** in one direction: the
  states of a single order unit space are separating *if* it is archimedean
  (`ous_separatingStatesAt_of_archimedean`) but not *only if*.  What they
  amount to is *almost* archimedeanness — no non-zero element between
  `-ε · 1` and `ε · 1` for all `ε > 0`, i.e. the order-unit seminorm being a
  norm — which is `ous_separatingStatesAt_iff_almostArchimedean`.  The two
  part at `ousAlm`, `ℝ²` with cone `{0} ∪ {(a,b) : 0 < a, 0 ≤ b}` and unit
  `(1,1)`: it has no non-zero infinitesimal, yet `(0,-1) ≤ ε · (1,1)` for
  every `ε > 0` without being `≤ 0`.  `ous_separating_states_not_archimedean`
  is the refutation.  Archimedeanness *is* equivalent to the states
  determining the *order* (`ous_statesDetermineOrder_iff_archimedean`,
  Kadison), which is presumably what the parenthetical means to say.
* Not separately formalized: the remaining items of 189aII (extensive
  categories with a final object, and the examples `Set`, `CRngᵒᵖ`, `CH`
  of 189aII.3).
-/
import Theses.B.Eff.StatesPredicates

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

namespace Theses.B.Eff

universe u v

noncomputable section

/-! ## Order unit spaces (189aII.1) -/

/-- **189aII.1** (`effexamplesintro`, eff.tex:2032, Examples): an **order
unit space** is an ordered real vector space with a distinguished order
unit.  Stated as a mixin over `AddCommGroup X`, `Module ℝ X` and
`PartialOrder X`: the order is translation-invariant, the positive cone is
closed under multiplication by non-negative reals, and the distinguished
element `unit` is an order unit, i.e. every element is below some natural
multiple of it.

Archimedeanness is *not* required (see 190IV.1), and positivity of `unit`
is not listed because it follows (`ou_unit_nonneg`). -/
class OrderUnitSpace (X : Type u) [AddCommGroup X] [Module ℝ X]
    [PartialOrder X] where
  /-- the order is translation-invariant -/
  protected add_le_add_left (x y : X) : x ≤ y → ∀ z, x + z ≤ y + z
  /-- the positive cone is closed under non-negative scalars -/
  protected smul_nonneg {r : ℝ} {x : X} : 0 ≤ r → 0 ≤ x → 0 ≤ r • x
  /-- the distinguished order unit -/
  unit : X
  /-- ... which is an order unit -/
  protected exists_le_smul_unit (x : X) : ∃ n : ℕ, x ≤ (n : ℝ) • unit

section OUSBasic

variable {X : Type u} [AddCommGroup X] [Module ℝ X] [PartialOrder X]
  [OrderUnitSpace X]

/-- The distinguished order unit of an order unit space, with the space as
an explicit argument. -/
abbrev ouUnit (X : Type u) [AddCommGroup X] [Module ℝ X] [PartialOrder X]
    [OrderUnitSpace X] : X := OrderUnitSpace.unit

/-- An order unit space is an ordered additive monoid; this unlocks
Mathlib's `sub_nonneg`, `add_le_add` and friends. -/
instance OrderUnitSpace.toIsOrderedAddMonoid : IsOrderedAddMonoid X where
  add_le_add_left := OrderUnitSpace.add_le_add_left

/-- Translation-invariance of the order, as a lemma. -/
theorem ou_add_le_add_right {x y : X} (h : x ≤ y) (z : X) : x + z ≤ y + z :=
  OrderUnitSpace.add_le_add_left x y h z

/-- The positive cone is closed under multiplication by a non-negative
real. -/
theorem ou_smul_nonneg {r : ℝ} {x : X} (hr : 0 ≤ r) (hx : 0 ≤ x) :
    0 ≤ r • x := OrderUnitSpace.smul_nonneg hr hx

/-- The order-unit axiom. -/
theorem ou_exists_le_smul_unit (x : X) : ∃ n : ℕ, x ≤ (n : ℝ) • ouUnit X :=
  OrderUnitSpace.exists_le_smul_unit x

/-- Multiplication by a non-negative real is monotone. -/
theorem ou_smul_le_smul {r : ℝ} (hr : 0 ≤ r) {x y : X} (h : x ≤ y) :
    r • x ≤ r • y := by
  have h0 : (0 : X) ≤ y - x := sub_nonneg.mpr h
  have h1 := ou_smul_nonneg hr h0
  rw [smul_sub] at h1
  exact sub_nonneg.mp h1

/-- **The order unit is positive.**  Applying the order-unit axiom to
`-unit` gives `0 ≤ (n+1) • unit`, and the positive cone is closed under
multiplication by `(n+1)⁻¹ ≥ 0`. -/
theorem ou_unit_nonneg : (0 : X) ≤ ouUnit X := by
  obtain ⟨n, hn⟩ := ou_exists_le_smul_unit (-(ouUnit X))
  have h1 : (0 : X) ≤ (n : ℝ) • ouUnit X + ouUnit X := by
    have h := ou_add_le_add_right hn (ouUnit X)
    simpa using h
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : ((n : ℝ) + 1) • ouUnit X = (n : ℝ) • ouUnit X + ouUnit X := by
    rw [add_smul, one_smul]
  rw [← h2] at h1
  have h3 := ou_smul_nonneg (le_of_lt (inv_pos.mpr hpos)) h1
  rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul] at h3

/-- A non-negative multiple of the order unit is positive. -/
theorem ou_smul_unit_nonneg {r : ℝ} (hr : 0 ≤ r) : (0 : X) ≤ r • ouUnit X :=
  ou_smul_nonneg hr ou_unit_nonneg

/-- The multiples of the order unit are monotone in the scalar. -/
theorem ou_smul_unit_mono {r s : ℝ} (h : r ≤ s) :
    r • ouUnit X ≤ s • ouUnit X := by
  have h1 := ou_smul_nonneg (sub_nonneg.mpr h) (ou_unit_nonneg (X := X))
  rw [sub_smul] at h1
  exact sub_nonneg.mp h1

/-- **Every element of an order unit space is a difference of two positive
elements**: from `x ≤ n • 1` one gets `x = n•1 - (n•1 - x)`.  This is the
order-unit substitute for the C\*-algebraic decomposition of an element
into four positive ones used in `linear_eq_zero_of_nonneg`. -/
theorem ou_eq_sub_of_nonneg (x : X) :
    ∃ p q : X, 0 ≤ p ∧ 0 ≤ q ∧ x = p - q := by
  obtain ⟨n, hn⟩ := ou_exists_le_smul_unit x
  refine ⟨(n : ℝ) • ouUnit X, (n : ℝ) • ouUnit X - x,
    ou_smul_unit_nonneg (Nat.cast_nonneg n), sub_nonneg.mpr hn, ?_⟩
  abel

end OUSBasic

/-! ### Archimedeanness, and the gauge of the order unit (190IV.1) -/

/-- **190IV.1** (eff.tex:2151, Examples, item 1, the parenthetical): an order
unit space is **archimedean** if `x ≤ ε · 1` for every `ε > 0` forces
`x ≤ 0`.

This is the definition of the literature the theses cite for order unit
spaces (Alfsen's Definition 1.12, named at cstar.tex:2789 in 30VI); the
equivalent form with natural multiples is `ousArchimedean_iff_nsmul`.  It is
deliberately *not* an axiom of `OrderUnitSpace` — 190IV.1's parenthetical
makes it a property of a single space. -/
def OUSArchimedean (X : Type u) [AddCommGroup X] [Module ℝ X] [PartialOrder X]
    [OrderUnitSpace X] : Prop :=
  ∀ x : X, (∀ ε : ℝ, 0 < ε → x ≤ ε • ouUnit X) → x ≤ 0

/-- An order unit space is **almost archimedean** if the only element caught
between `-ε · 1` and `ε · 1` for every `ε > 0` is `0`; equivalently, the
order unit seminorm is a norm.

This is strictly weaker than `OUSArchimedean` (`ousAlm` below is a
two-dimensional counterexample), and it is what separating states actually
amount to: see `ous_separatingStatesAt_iff_almostArchimedean`, and the
ERRATA row on 190IV.1. -/
def OUSAlmostArchimedean (X : Type u) [AddCommGroup X] [Module ℝ X]
    [PartialOrder X] [OrderUnitSpace X] : Prop :=
  ∀ x : X, (∀ ε : ℝ, 0 < ε → x ≤ ε • ouUnit X ∧ -x ≤ ε • ouUnit X) → x = 0

/-- The set of scalars `r` with `y ≤ r · 1`; the gauge below is its
infimum. -/
def ouGaugeSet (X : Type u) [AddCommGroup X] [Module ℝ X] [PartialOrder X]
    [OrderUnitSpace X] (y : X) : Set ℝ :=
  {r : ℝ | y ≤ r • ouUnit X}

/-- The **Minkowski gauge of the order unit**, `p(y) = inf {r : y ≤ r · 1}`.
It is the sublinear functional that drives the Hahn–Banach separation of
`ou_exists_state`; the order-unit axiom makes `ouGaugeSet` non-empty and (as
long as the unit is not `0`) bounded below. -/
def ouGauge (X : Type u) [AddCommGroup X] [Module ℝ X] [PartialOrder X]
    [OrderUnitSpace X] (y : X) : ℝ :=
  sInf (ouGaugeSet X y)

section OUArch

variable {X : Type u} [AddCommGroup X] [Module ℝ X] [PartialOrder X]
  [OrderUnitSpace X]

/-- Archimedeanness in the form the literature often gives it: `n · x ≤ 1`
for every natural `n` forces `x ≤ 0`.  The two are interchanged by dividing
resp. multiplying by `n`. -/
theorem ousArchimedean_iff_nsmul :
    OUSArchimedean X ↔ ∀ x : X, (∀ n : ℕ, (n : ℝ) • x ≤ ouUnit X) → x ≤ 0 := by
  constructor
  · intro h x hx
    refine h x fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt ε⁻¹
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_of_lt (inv_pos.mpr hε)) hn
    have h1 : (n : ℝ) • x ≤ ouUnit X := hx n
    have h2 : (n : ℝ)⁻¹ • ((n : ℝ) • x) ≤ (n : ℝ)⁻¹ • ouUnit X :=
      ou_smul_le_smul (le_of_lt (inv_pos.mpr hnpos)) h1
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hnpos), one_smul] at h2
    refine h2.trans (ou_smul_unit_mono ?_)
    have h3 : 1 < ε * (n : ℝ) := by
      have h4 := mul_lt_mul_of_pos_left hn hε
      rwa [mul_inv_cancel₀ (ne_of_gt hε)] at h4
    rw [inv_eq_one_div, div_le_iff₀ hnpos]
    linarith
  · intro h x hx
    refine h x fun n => ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn]
      simpa using ou_unit_nonneg (X := X)
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h1 : x ≤ (n : ℝ)⁻¹ • ouUnit X := hx _ (inv_pos.mpr hnpos)
      have h2 := ou_smul_le_smul (le_of_lt hnpos) h1
      rwa [smul_smul, mul_inv_cancel₀ (ne_of_gt hnpos), one_smul] at h2

theorem ou_mem_gaugeSet {y : X} {r : ℝ} (h : y ≤ r • ouUnit X) :
    r ∈ ouGaugeSet X y := h

/-- The order-unit axiom: some natural multiple of the unit dominates `y`. -/
theorem ou_gaugeSet_nonempty (y : X) : (ouGaugeSet X y).Nonempty := by
  obtain ⟨n, hn⟩ := ou_exists_le_smul_unit y
  exact ⟨(n : ℝ), hn⟩

/-- `ouGaugeSet` is upward closed, the unit being positive. -/
theorem ou_gaugeSet_up {y : X} {r s : ℝ} (hr : r ∈ ouGaugeSet X y) (h : r ≤ s) :
    s ∈ ouGaugeSet X y :=
  le_trans hr (ou_smul_unit_mono h)

/-- If the order unit is `0` the space is trivial: `x ≤ 0` and `-x ≤ 0`. -/
theorem ou_eq_zero_of_unit_eq_zero (hu : ouUnit X = 0) (x : X) : x = 0 := by
  obtain ⟨n, hn⟩ := ou_exists_le_smul_unit x
  obtain ⟨m, hm⟩ := ou_exists_le_smul_unit (-x)
  rw [hu, smul_zero] at hn hm
  exact le_antisymm hn (neg_nonpos.mp hm)

/-- A space with a non-zero element has a non-zero order unit. -/
theorem ou_unit_ne_zero_of_ne {x : X} (hx : x ≠ 0) : ouUnit X ≠ 0 :=
  fun hu => hx (ou_eq_zero_of_unit_eq_zero hu x)

/-- A multiple of the order unit is positive only if the scalar is: divide by
`r`, which would otherwise make `-1` a positive multiple of a positive
unit. -/
theorem ou_nonneg_of_smul_unit_nonneg (hu : ouUnit X ≠ 0) {r : ℝ}
    (h : (0 : X) ≤ r • ouUnit X) : 0 ≤ r := by
  by_contra hc
  have hr : r < 0 := not_le.mp hc
  have hc' : (0 : ℝ) ≤ -r⁻¹ := by
    have : r⁻¹ < 0 := inv_neg''.mpr hr
    linarith
  have h1 : (0 : X) ≤ (-r⁻¹) • (r • ouUnit X) := ou_smul_nonneg hc' h
  rw [smul_smul] at h1
  have h2 : -r⁻¹ * r = -1 := by
    rw [neg_mul, inv_mul_cancel₀ (ne_of_lt hr)]
  rw [h2] at h1
  have h3 : ouUnit X ≤ 0 := by simpa using h1
  exact hu (le_antisymm h3 ou_unit_nonneg)

/-- `ouGaugeSet X y` is bounded below by `-m` for any `m` with `-y ≤ m · 1`,
so the gauge is a real number. -/
theorem ou_gaugeSet_bddBelow (hu : ouUnit X ≠ 0) (y : X) :
    BddBelow (ouGaugeSet X y) := by
  obtain ⟨m, hm⟩ := ou_exists_le_smul_unit (-y)
  refine ⟨-(m : ℝ), fun r hr => ?_⟩
  have h1 : -((m : ℝ) • ouUnit X) ≤ y := neg_le.mp hm
  have h2 : -((m : ℝ) • ouUnit X) ≤ r • ouUnit X := le_trans h1 hr
  have h3 : (0 : X) ≤ (m : ℝ) • ouUnit X + r • ouUnit X := by
    have := add_le_add_right h2 ((m : ℝ) • ouUnit X)
    simpa using this
  rw [← add_smul] at h3
  have h4 : (0 : ℝ) ≤ (m : ℝ) + r := ou_nonneg_of_smul_unit_nonneg hu h3
  linarith

theorem ou_gauge_le (hu : ouUnit X ≠ 0) {y : X} {r : ℝ}
    (h : y ≤ r • ouUnit X) : ouGauge X y ≤ r :=
  csInf_le (ou_gaugeSet_bddBelow hu y) h

theorem ou_le_gauge {y : X} {c : ℝ} (h : ∀ r ∈ ouGaugeSet X y, c ≤ r) :
    c ≤ ouGauge X y :=
  le_csInf (ou_gaugeSet_nonempty y) h

theorem ou_gauge_zero (hu : ouUnit X ≠ 0) : ouGauge X (0 : X) = 0 := by
  refine le_antisymm (ou_gauge_le hu (by rw [zero_smul])) (ou_le_gauge ?_)
  intro r hr
  have h : (0 : X) ≤ r • ouUnit X := hr
  exact ou_nonneg_of_smul_unit_nonneg hu h

/-- The gauge is subadditive: `y ≤ r · 1` and `z ≤ s · 1` give
`y + z ≤ (r+s) · 1`. -/
theorem ou_gauge_add_le (hu : ouUnit X ≠ 0) (y z : X) :
    ouGauge X (y + z) ≤ ouGauge X y + ouGauge X z := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨r, hr, hrlt⟩ :=
    Real.lt_sInf_add_pos (ou_gaugeSet_nonempty y) (half_pos hε)
  obtain ⟨s, hs, hslt⟩ :=
    Real.lt_sInf_add_pos (ou_gaugeSet_nonempty z) (half_pos hε)
  have hmem : y + z ≤ (r + s) • ouUnit X := by
    rw [add_smul]
    exact add_le_add hr hs
  have h1 : ouGauge X (y + z) ≤ r + s := ou_gauge_le hu hmem
  have h2 : r + s < ouGauge X y + ouGauge X z + ε := by
    simp only [ouGauge] at *
    linarith
  linarith

theorem ou_gauge_smul_le (hu : ouUnit X ≠ 0) {c : ℝ} (hc : 0 < c) (y : X) :
    ouGauge X (c • y) ≤ c * ouGauge X y := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hεc : 0 < ε / c := div_pos hε hc
  obtain ⟨r, hr, hrlt⟩ := Real.lt_sInf_add_pos (ou_gaugeSet_nonempty y) hεc
  have hmem : c • y ≤ (c * r) • ouUnit X := by
    have h1 : c • y ≤ c • (r • ouUnit X) := ou_smul_le_smul (le_of_lt hc) hr
    rwa [smul_smul] at h1
  have h1 : ouGauge X (c • y) ≤ c * r := ou_gauge_le hu hmem
  have h2 : c * r ≤ c * ouGauge X y + ε := by
    simp only [ouGauge] at *
    have h3 := mul_le_mul_of_nonneg_left (le_of_lt hrlt) (le_of_lt hc)
    calc c * r ≤ c * (sInf (ouGaugeSet X y) + ε / c) := h3
      _ = c * sInf (ouGaugeSet X y) + ε := by field_simp
  linarith

/-- The gauge is positively homogeneous. -/
theorem ou_gauge_smul (hu : ouUnit X ≠ 0) {c : ℝ} (hc : 0 < c) (y : X) :
    ouGauge X (c • y) = c * ouGauge X y := by
  refine le_antisymm (ou_gauge_smul_le hu hc y) ?_
  have h1 : ouGauge X y ≤ c⁻¹ * ouGauge X (c • y) := by
    have h2 := ou_gauge_smul_le hu (inv_pos.mpr hc) (c • y)
    rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul] at h2
  have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt hc)
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul] at h3

/-- `p(1) ≤ 1`, since `1 ≤ 1 · 1`. -/
theorem ou_gauge_unit_le (hu : ouUnit X ≠ 0) : ouGauge X (ouUnit X) ≤ 1 :=
  ou_gauge_le hu (by rw [one_smul])

/-- `p(-1) ≤ -1`, since `-1 ≤ (-1) · 1`.  Together with `ou_gauge_unit_le`
this is what pins a functional below the gauge to be unital. -/
theorem ou_gauge_neg_unit_le (hu : ouUnit X ≠ 0) :
    ouGauge X (-ouUnit X) ≤ -1 :=
  ou_gauge_le hu (by rw [neg_one_smul])

/-- `p(-y) ≤ 0` for `y ≥ 0`: this is what makes a functional below the gauge
positive. -/
theorem ou_gauge_neg_nonpos (hu : ouUnit X ≠ 0) {y : X} (hy : 0 ≤ y) :
    ouGauge X (-y) ≤ 0 :=
  ou_gauge_le hu (by rw [zero_smul]; exact neg_nonpos.mpr hy)

/-- An `ε` that `y` does not reach bounds the gauge from below, the gauge set
being upward closed. -/
theorem ou_gauge_pos_of_not_le {y : X} {ε : ℝ} (hε : 0 < ε)
    (h : ¬ y ≤ ε • ouUnit X) : 0 < ouGauge X y := by
  refine lt_of_lt_of_le hε (ou_le_gauge ?_)
  intro r hr
  by_contra hc
  exact h (ou_gaugeSet_up hr (le_of_lt (not_le.mp hc)))

/-- **The Hahn–Banach separation for order unit spaces** (the substance of
190IV.1's parenthetical): if the gauge of `d` is positive then some state —
a positive unital linear functional — gives `d` a positive value.

Mathlib's `exists_extension_of_le_sublinear` extends a partial linear map
dominated by a sublinear functional; the sublinear functional is the gauge
`p(y) = inf {r : y ≤ r · 1}` of the order unit, and the partial map is
`t · d ↦ t · p(d)` on the line `ℝ · d`, which is dominated because
`p(d) + p(-d) ≥ p(0) = 0`.  The extension `g` is then automatically
positive (`g(-y) ≤ p(-y) ≤ 0` for `y ≥ 0`) and unital (`g(1) ≤ p(1) ≤ 1` and
`-g(1) ≤ p(-1) ≤ -1`). -/
theorem ou_exists_state (hu : ouUnit X ≠ 0) (d : X) (hd : 0 < ouGauge X d) :
    ∃ f : X →ₗ[ℝ] ℝ, (∀ x : X, 0 ≤ x → 0 ≤ f x) ∧ f (ouUnit X) = 1 ∧ 0 < f d := by
  have hdne : d ≠ 0 := by
    intro h
    rw [h, ou_gauge_zero hu] at hd
    exact lt_irrefl _ hd
  have hN_hom : ∀ c : ℝ, 0 < c → ∀ x : X, ouGauge X (c • x) = c * ouGauge X x :=
    fun c hc x => ou_gauge_smul hu hc x
  have hN_add : ∀ x y : X, ouGauge X (x + y) ≤ ouGauge X x + ouGauge X y :=
    ou_gauge_add_le hu
  have hFle : ∀ z : ((LinearPMap.mkSpanSingleton d (ouGauge X d) hdne : X →ₗ.[ℝ] ℝ)).domain,
      ((LinearPMap.mkSpanSingleton d (ouGauge X d) hdne : X →ₗ.[ℝ] ℝ)) z ≤ ouGauge X (z : X) := by
    rintro ⟨z, hz⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hval : ((LinearPMap.mkSpanSingleton d (ouGauge X d) hdne : X →ₗ.[ℝ] ℝ)) ⟨c • d, hz⟩
        = c • ouGauge X d := LinearPMap.mkSpanSingleton'_apply _ _ _ c hz
    rw [hval, smul_eq_mul]
    show c * ouGauge X d ≤ ouGauge X (c • d)
    rcases lt_trichotomy c 0 with hc | hc | hc
    · have hs : 0 < -c := by linarith
      have h1 : ouGauge X (c • d) = (-c) * ouGauge X (-d) := by
        rw [← ou_gauge_smul hu hs (-d)]
        congr 1
        rw [smul_neg, neg_smul, neg_neg]
      have h2 : (0 : ℝ) ≤ ouGauge X d + ouGauge X (-d) := by
        have h3 := ou_gauge_add_le hu d (-d)
        rw [add_neg_cancel, ou_gauge_zero hu] at h3
        linarith
      rw [h1]
      nlinarith
    · rw [hc, zero_smul, zero_mul, ou_gauge_zero hu]
    · rw [ou_gauge_smul hu hc]
  obtain ⟨g, hgF, hgN⟩ :=
    exists_extension_of_le_sublinear ((LinearPMap.mkSpanSingleton d (ouGauge X d) hdne : X →ₗ.[ℝ] ℝ))
      (ouGauge X) hN_hom hN_add hFle
  have hpos : ∀ x : X, 0 ≤ x → 0 ≤ g x := by
    intro x hx
    have h1 : g (-x) ≤ ouGauge X (-x) := hgN (-x)
    have h2 : ouGauge X (-x) ≤ 0 := ou_gauge_neg_nonpos hu hx
    have h3 : g (-x) = -g x := map_neg g x
    linarith
  have hunit : g (ouUnit X) = 1 := by
    have h1 : g (ouUnit X) ≤ 1 :=
      le_trans (hgN (ouUnit X)) (ou_gauge_unit_le hu)
    have h2 : g (-ouUnit X) ≤ -1 :=
      le_trans (hgN (-ouUnit X)) (ou_gauge_neg_unit_le hu)
    have h3 : g (-ouUnit X) = -g (ouUnit X) := map_neg g _
    have h4 : (1 : ℝ) ≤ g (ouUnit X) := by rw [h3] at h2; linarith
    exact le_antisymm h1 h4
  have hd' : g d = ouGauge X d := by
    have hmem : d ∈ ((LinearPMap.mkSpanSingleton d (ouGauge X d) hdne : X →ₗ.[ℝ] ℝ)).domain :=
      Submodule.mem_span_singleton_self d
    have h1 := hgF ⟨d, hmem⟩
    have h2 : ((LinearPMap.mkSpanSingleton d (ouGauge X d) hdne : X →ₗ.[ℝ] ℝ)) ⟨d, hmem⟩
        = ouGauge X d := LinearPMap.mkSpanSingleton'_apply_self _ _ _ hmem
    exact h1.trans h2
  exact ⟨g, hpos, hunit, by rw [hd']; exact hd⟩

end OUArch

/-! ### The basic examples of order unit spaces -/

/-- `ℝ` itself is an order unit space with order unit `1`. -/
instance Real.orderUnitSpace : OrderUnitSpace ℝ where
  add_le_add_left x y h z := by
    rw [add_comm x z, add_comm y z]; exact add_le_add_right h z
  smul_nonneg hr hx := by
    rw [smul_eq_mul]; exact mul_nonneg hr hx
  unit := 1
  exists_le_smul_unit x := ⟨⌈x⌉₊, by simpa using Nat.le_ceil x⟩

/-- An order unit space stays one after `ULift`ing (needed because the
objects of `OUS` live in a single universe, while `ℝ : Type`). -/
instance ULift.orderUnitSpace (X : Type u) [AddCommGroup X] [Module ℝ X]
    [PartialOrder X] [OrderUnitSpace X] :
    OrderUnitSpace (ULift.{v} X) where
  add_le_add_left x y h z := by
    show x.down + z.down ≤ y.down + z.down
    exact ou_add_le_add_right (show x.down ≤ y.down from h) z.down
  smul_nonneg hr hx := by
    show (0 : X) ≤ _
    exact ou_smul_nonneg hr hx
  unit := ULift.up (ouUnit X)
  exists_le_smul_unit x := by
    obtain ⟨n, hn⟩ := ou_exists_le_smul_unit x.down
    exact ⟨n, hn⟩

/-- The one-point space is an order unit space (with unit `0`); it is the
final object of `OUS`, hence the initial object of `OUSᵒᵖ`. -/
instance PUnit.orderUnitSpace : OrderUnitSpace PUnit.{u + 1} where
  add_le_add_left _ _ _ _ := le_of_eq (Subsingleton.elim _ _)
  smul_nonneg _ _ := le_of_eq (Subsingleton.elim _ _)
  unit := PUnit.unit
  exists_le_smul_unit _ := ⟨0, le_of_eq (Subsingleton.elim _ _)⟩

/-- The product of two order unit spaces, with the coordinatewise order
and the unit `(1, 1)`; this is the binary coproduct of `OUSᵒᵖ`. -/
instance Prod.orderUnitSpace (X Y : Type u) [AddCommGroup X] [Module ℝ X]
    [PartialOrder X] [OrderUnitSpace X] [AddCommGroup Y] [Module ℝ Y]
    [PartialOrder Y] [OrderUnitSpace Y] : OrderUnitSpace (X × Y) where
  add_le_add_left _ _ h z :=
    Prod.le_def.mpr ⟨ou_add_le_add_right (Prod.le_def.mp h).1 z.1,
      ou_add_le_add_right (Prod.le_def.mp h).2 z.2⟩
  smul_nonneg hr hx :=
    Prod.le_def.mpr ⟨ou_smul_nonneg hr (Prod.le_def.mp hx).1,
      ou_smul_nonneg hr (Prod.le_def.mp hx).2⟩
  unit := (ouUnit X, ouUnit Y)
  exists_le_smul_unit p := by
    obtain ⟨n, hn⟩ := ou_exists_le_smul_unit p.1
    obtain ⟨m, hm⟩ := ou_exists_le_smul_unit p.2
    refine ⟨max n m, Prod.le_def.mpr ⟨?_, ?_⟩⟩
    · exact hn.trans (ou_smul_unit_mono
        (by exact_mod_cast Nat.le_max_left n m))
    · exact hm.trans (ou_smul_unit_mono
        (by exact_mod_cast Nat.le_max_right n m))

/-! ### The category `OUS` -/

/-- A bundled order unit space: the object type of the category `OUS`. -/
structure OUS : Type (u + 1) where
  /-- the underlying type -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℝ carrier]
  [partialOrder : PartialOrder carrier]
  [orderUnitSpace : OrderUnitSpace carrier]

attribute [instance] OUS.addCommGroup OUS.module OUS.partialOrder
  OUS.orderUnitSpace

/-- An object of `OUS` may be used directly as its carrier type. -/
instance : CoeSort OUS.{u} (Type u) := ⟨OUS.carrier⟩

/-- Bundle an order unit space as an object of `OUS`. -/
abbrev OUS.of (X : Type u) [AddCommGroup X] [Module ℝ X] [PartialOrder X]
    [OrderUnitSpace X] : OUS.{u} := ⟨X⟩

/-- The order unit of a bundled order unit space. -/
abbrev OUS.unit (X : OUS.{u}) : X.carrier := ouUnit X.carrier

/-- The product of two bundled order unit spaces. -/
abbrev OUS.prod (X Y : OUS.{u}) : OUS.{u} := OUS.of (X.carrier × Y.carrier)

/-- The scalars `ℝᵤ`: the initial object of `OUS`, hence the final object
of `OUSᵒᵖ`. -/
abbrev ousScal : OUS.{u} := OUS.of (ULift.{u} ℝ)

/-- The zero space: the final object of `OUS`, hence the initial object of
`OUSᵒᵖ`. -/
abbrev ousTriv : OUS.{u} := OUS.of PUnit.{u + 1}

/-- The order unit of the scalars `ℝᵤ` is `1`. -/
@[simp] theorem ousScal_unit : ousScal.{u}.unit = (1 : ULift.{u} ℝ) := rfl

/-- The order unit of a product is the pair of the order units. -/
@[simp] theorem OUS.prod_unit (X Y : OUS.{u}) :
    (X.prod Y).unit = (X.unit, Y.unit) := rfl

/-- A **positive unit-preserving linear map** between order unit spaces:
the morphisms of `OUS` (and, read backwards, of `OUSᵒᵖ`). -/
structure OUSMap (X Y : OUS.{u}) : Type u where
  /-- the underlying real-linear map -/
  toLinearMap : X.carrier →ₗ[ℝ] Y.carrier
  /-- ... which is positive -/
  map_nonneg' : ∀ x : X.carrier, 0 ≤ x → 0 ≤ toLinearMap x
  /-- ... and unit-preserving -/
  map_unit' : toLinearMap X.unit = Y.unit

/-- Extensionality: a morphism of `OUS` is determined by its underlying
function. -/
theorem OUSMap.ext' {X Y : OUS.{u}} {f g : OUSMap X Y}
    (h : ∀ x, f.toLinearMap x = g.toLinearMap x) : f = g := by
  obtain ⟨f, hf₁, hf₂⟩ := f
  obtain ⟨g, hg₁, hg₂⟩ := g
  have hfg : f = g := LinearMap.ext h
  subst hfg
  rfl

/-- A positive linear map is monotone (apply positivity to `y - x`). -/
theorem OUSMap.mono {X Y : OUS.{u}} (f : OUSMap X Y) {x y : X.carrier}
    (h : x ≤ y) : f.toLinearMap x ≤ f.toLinearMap y := by
  have h1 := f.map_nonneg' (y - x) (sub_nonneg.mpr h)
  rw [map_sub] at h1
  exact sub_nonneg.mp h1

/-- The identity morphism of `OUS`. -/
def OUSMap.id (X : OUS.{u}) : OUSMap X X where
  toLinearMap := LinearMap.id
  map_nonneg' _ h := h
  map_unit' := rfl

/-- Composition in `OUS` (diagrammatic order: first `f`, then `g`). -/
def OUSMap.comp {X Y Z : OUS.{u}} (f : OUSMap X Y) (g : OUSMap Y Z) :
    OUSMap X Z where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_nonneg' x h := g.map_nonneg' _ (f.map_nonneg' x h)
  map_unit' := by
    show g.toLinearMap (f.toLinearMap X.unit) = Z.unit
    rw [f.map_unit', g.map_unit']

/-- **The category `OUS`** of order unit spaces with positive
unit-preserving linear maps.  All three category laws hold definitionally,
since composition is composition of the underlying linear maps. -/
instance : Category.{u} OUS.{u} where
  Hom X Y := OUSMap X Y
  id X := OUSMap.id X
  comp f g := OUSMap.comp f g
  id_comp _ := OUSMap.ext' fun _ => rfl
  comp_id _ := OUSMap.ext' fun _ => rfl
  assoc _ _ _ := OUSMap.ext' fun _ => rfl

/-- Extensionality in `OUS`, for morphisms written with `⟶`. -/
theorem ous_hom_ext {X Y : OUS.{u}} {f g : X ⟶ Y}
    (h : ∀ x, f.toLinearMap x = g.toLinearMap x) : f = g := OUSMap.ext' h

/-- Composition in `OUS` is composition of the underlying functions. -/
theorem ous_comp_apply {X Y Z : OUS.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X.carrier) :
    (f ≫ g).toLinearMap x = g.toLinearMap (f.toLinearMap x) := rfl

/-- The identity of `OUS` is the identity function. -/
theorem ous_id_apply {X : OUS.{u}} (x : X.carrier) :
    (𝟙 X : X ⟶ X).toLinearMap x = x := rfl

/-- Equal morphisms of `OUS` agree pointwise. -/
theorem ous_congr {X Y : OUS.{u}} {f g : X ⟶ Y} (h : f = g) (x : X.carrier) :
    f.toLinearMap x = g.toLinearMap x := by rw [h]

/-- Extensionality in `OUSᵒᵖ`. -/
theorem ousop_hom_ext {X Y : OUS.{u}ᵒᵖ} {f g : X ⟶ Y}
    (h : ∀ x, f.unop.toLinearMap x = g.unop.toLinearMap x) : f = g :=
  Quiver.Hom.unop_inj (ous_hom_ext h)

/-- Composition in `OUSᵒᵖ` applies the two underlying functions in the
opposite order. -/
theorem ousop_comp_apply {X Y Z : OUS.{u}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Z.unop.carrier) :
    (f ≫ g).unop.toLinearMap x
      = f.unop.toLinearMap (g.unop.toLinearMap x) :=
  ous_comp_apply g.unop f.unop x

/-- Equal morphisms of `OUSᵒᵖ` agree pointwise. -/
theorem ousop_congr {X Y : OUS.{u}ᵒᵖ} {f g : X ⟶ Y} (h : f = g)
    (x : Y.unop.carrier) : f.unop.toLinearMap x = g.unop.toLinearMap x := by
  rw [h]

/-- Postcomposition with a fixed map, pointwise. -/
theorem ousop_comp_congr {Z P X : OUS.{u}ᵒᵖ} {F : P ⟶ X} {a b : Z ⟶ P}
    (h : a ≫ F = b ≫ F) (x : X.unop.carrier) :
    a.unop.toLinearMap (F.unop.toLinearMap x)
      = b.unop.toLinearMap (F.unop.toLinearMap x) :=
  ((ousop_comp_apply a F x).symm.trans (ousop_congr h x)).trans
    (ousop_comp_apply b F x)

/-! ### The concrete final, initial and product objects of `OUS` -/

/-- The unique morphism `ℝᵤ ⟶ X` of `OUS`, namely `r ↦ r · 1`. -/
def ousUnitMap (X : OUS.{u}) : ousScal.{u} ⟶ X where
  toLinearMap :=
    { toFun := fun r => r.down • X.unit
      map_add' := fun a b => by
        show (a.down + b.down) • X.unit = a.down • X.unit + b.down • X.unit
        exact add_smul _ _ _
      map_smul' := fun r a => by
        show (r * a.down) • X.unit = r • (a.down • X.unit)
        exact mul_smul _ _ _ }
  map_nonneg' r hr := ou_smul_unit_nonneg hr
  map_unit' := one_smul _ _

/-- The defining equation of `ousUnitMap`. -/
@[simp] theorem ousUnitMap_apply (X : OUS.{u}) (r : ULift.{u} ℝ) :
    (ousUnitMap X).toLinearMap r = r.down • X.unit := rfl

/-- The unique morphism `X ⟶ 0` of `OUS`. -/
def ousTrivMap (X : OUS.{u}) : X ⟶ ousTriv.{u} where
  toLinearMap := 0
  map_nonneg' _ _ := le_of_eq (Subsingleton.elim _ _)
  map_unit' := Subsingleton.elim _ _

/-- The first projection `X × Y ⟶ X`, a coprojection of `OUSᵒᵖ`. -/
def ousFst (X Y : OUS.{u}) : X.prod Y ⟶ X where
  toLinearMap := LinearMap.fst ℝ X.carrier Y.carrier
  map_nonneg' _ h := (Prod.le_def.mp h).1
  map_unit' := rfl

/-- The second projection `X × Y ⟶ Y`. -/
def ousSnd (X Y : OUS.{u}) : X.prod Y ⟶ Y where
  toLinearMap := LinearMap.snd ℝ X.carrier Y.carrier
  map_nonneg' _ h := (Prod.le_def.mp h).2
  map_unit' := rfl

/-- The pairing `⟨f, g⟩ : Z ⟶ X × Y`, the cotupling of `OUSᵒᵖ`. -/
def ousPair {Z X Y : OUS.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) : Z ⟶ X.prod Y where
  toLinearMap := LinearMap.prod f.toLinearMap g.toLinearMap
  map_nonneg' z h := Prod.le_def.mpr ⟨f.map_nonneg' z h, g.map_nonneg' z h⟩
  map_unit' := Prod.ext f.map_unit' g.map_unit'

/-- The defining equation of `ousPair`. -/
@[simp] theorem ousPair_apply {Z X Y : OUS.{u}} (f : Z ⟶ X) (g : Z ⟶ Y)
    (z : Z.carrier) :
    (ousPair f g).toLinearMap z
      = (f.toLinearMap z, g.toLinearMap z) := rfl

/-- The product `f × g : X × Y ⟶ X' × Y'` of two morphisms. -/
def ousProdMap {X X' Y Y' : OUS.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    X.prod Y ⟶ X'.prod Y' where
  toLinearMap := LinearMap.prodMap f.toLinearMap g.toLinearMap
  map_nonneg' _ h :=
    Prod.le_def.mpr ⟨f.map_nonneg' _ (Prod.le_def.mp h).1,
      g.map_nonneg' _ (Prod.le_def.mp h).2⟩
  map_unit' := Prod.ext f.map_unit' g.map_unit'

/-- The defining equation of `ousProdMap`. -/
@[simp] theorem ousProdMap_apply {X X' Y Y' : OUS.{u}} (f : X ⟶ X')
    (g : Y ⟶ Y') (p : X.carrier × Y.carrier) :
    (ousProdMap f g).toLinearMap p
      = (f.toLinearMap p.1, g.toLinearMap p.2) := rfl

/-- Any morphism `ℝᵤ ⟶ X` is `r ↦ r · 1` (linearity and unitality). -/
theorem ousUnitMap_unique {X : OUS.{u}} (f : ousScal.{u} ⟶ X) :
    f = ousUnitMap X := by
  refine ous_hom_ext fun r => ?_
  have hr : r = r.down • (1 : ULift.{u} ℝ) := by
    apply ULift.down_injective
    simp
  rw [ousUnitMap_apply]
  conv_lhs => rw [hr]
  rw [map_smul]
  exact congrArg (fun z => r.down • z) f.map_unit'

/-- **`ℝᵤ` is the initial object of `OUS`**, hence the final object of
`OUSᵒᵖ`. -/
def ousScalIsInitial : IsInitial ousScal.{u} :=
  IsInitial.ofUniqueHom (fun X => ousUnitMap X) (fun _ f => ousUnitMap_unique f)

/-- **The zero space is the final object of `OUS`**, hence the initial
object of `OUSᵒᵖ`. -/
def ousTrivIsTerminal : IsTerminal ousTriv.{u} :=
  IsTerminal.ofUniqueHom (fun X => ousTrivMap X)
    (fun _ _ => ous_hom_ext fun _ =>
      Subsingleton.elim (α := PUnit.{u + 1}) _ _)

/-- The concrete presentation of `OUSᵒᵖ`: the final object is the scalars
`ℝᵤ` (initial in `OUS`), the binary coproducts are the products `X × Y`
with the coordinatewise order and unit `(1,1)`. -/
noncomputable def ousPres : CoprodPres (OUS.{u}ᵒᵖ) where
  T := Opposite.op ousScal.{u}
  hT := IsInitial.op (OUS.{u}) ousScalIsInitial
  P X Y := Opposite.op (X.unop.prod Y.unop)
  pinl X Y := Quiver.Hom.op (ousFst X.unop Y.unop)
  pinr X Y := Quiver.Hom.op (ousSnd X.unop Y.unop)
  hP X Y := BinaryCofan.IsColimit.mk _
    (fun {_} u v => Quiver.Hom.op (ousPair u.unop v.unop))
    (fun {_} _ _ => ousop_hom_ext fun x => ousop_comp_apply _ _ x)
    (fun {_} _ _ => ousop_hom_ext fun x => ousop_comp_apply _ _ x)
    (fun {_} _ _ m h₁ h₂ => ousop_hom_ext fun x => by
      refine Prod.ext ?_ ?_
      · exact (ousop_comp_apply _ m x).symm.trans (ousop_congr h₁ x)
      · exact (ousop_comp_apply _ m x).symm.trans (ousop_congr h₂ x))

/-- The unique morphism into the final object of `OUSᵒᵖ` is `r ↦ r · 1`. -/
theorem ousPres_from_apply (Y : OUS.{u}ᵒᵖ) (r : ULift.{u} ℝ) :
    (ousPres.hT.from Y).unop.toLinearMap r = r.down • Y.unop.unit := by
  have h : ousPres.hT.from Y = Quiver.Hom.op (ousUnitMap Y.unop) :=
    ousPres.hT.hom_ext _ _
  rw [h]
  rfl

/-- The coproduct of two morphisms of `OUSᵒᵖ` acts coordinatewise. -/
theorem ousPres_pmap_apply {X X' Y Y' : OUS.{u}ᵒᵖ} (f : X ⟶ X') (g : Y ⟶ Y')
    (p : (ousPres.P X' Y').unop.carrier) :
    (ousPres.pmap f g).unop.toLinearMap p
      = (f.unop.toLinearMap p.1, g.unop.toLinearMap p.2) := by
  refine Prod.ext ?_ ?_
  · exact ousop_comp_apply f _ p
  · exact ousop_comp_apply g _ p

/-! ### The left pushout square of 180I in `OUS` -/

section OUSMed1

variable {X Y Z : OUS.{u}}

/-- The mediating morphism `γ(x, y) = β(x, 0) + α(0, y)` of the first
pushout square of 180I. -/
def ousMed1 (α : ousScal.{u}.prod Y ⟶ Z) (β : X.prod ousScal.{u} ⟶ Z)
    (hc : ∀ z w : ULift.{u} ℝ,
      α.toLinearMap (z, w.down • Y.unit)
        = β.toLinearMap (z.down • X.unit, w)) :
    X.prod Y ⟶ Z where
  toLinearMap :=
    β.toLinearMap.comp ((LinearMap.inl ℝ X.carrier (ULift.{u} ℝ)).comp
        (LinearMap.fst ℝ X.carrier Y.carrier))
      + α.toLinearMap.comp ((LinearMap.inr ℝ (ULift.{u} ℝ) Y.carrier).comp
        (LinearMap.snd ℝ X.carrier Y.carrier))
  map_nonneg' p hp := by
    show (0 : Z.carrier)
      ≤ β.toLinearMap (p.1, 0) + α.toLinearMap (0, p.2)
    have h1 : (0 : X.carrier × ULift.{u} ℝ) ≤ (p.1, 0) :=
      Prod.le_def.mpr ⟨(Prod.le_def.mp hp).1, le_refl _⟩
    have h2 : (0 : ULift.{u} ℝ × Y.carrier) ≤ (0, p.2) :=
      Prod.le_def.mpr ⟨le_refl _, (Prod.le_def.mp hp).2⟩
    exact add_nonneg (β.map_nonneg' _ h1) (α.map_nonneg' _ h2)
  map_unit' := by
    show β.toLinearMap (X.unit, (0 : ULift.{u} ℝ))
      + α.toLinearMap ((0 : ULift.{u} ℝ), Y.unit) = Z.unit
    have h1 : α.toLinearMap ((1 : ULift.{u} ℝ), (0 : Y.carrier))
        = β.toLinearMap (X.unit, (0 : ULift.{u} ℝ)) := by
      have h := hc 1 0
      simpa using h
    have h2 : ((1 : ULift.{u} ℝ), (0 : Y.carrier))
        + ((0 : ULift.{u} ℝ), Y.unit) = ((1 : ULift.{u} ℝ), Y.unit) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [← h1, ← map_add, h2]
    exact α.map_unit'

/-- The defining equation of `ousMed1`. -/
@[simp] theorem ousMed1_apply (α : ousScal.{u}.prod Y ⟶ Z)
    (β : X.prod ousScal.{u} ⟶ Z) (hc) (p : X.carrier × Y.carrier) :
    (ousMed1 α β hc).toLinearMap p
      = β.toLinearMap (p.1, 0) + α.toLinearMap (0, p.2) := rfl

variable (α : ousScal.{u}.prod Y ⟶ Z) (β : X.prod ousScal.{u} ⟶ Z)
  (hc : ∀ z w : ULift.{u} ℝ,
    α.toLinearMap (z, w.down • Y.unit)
      = β.toLinearMap (z.down • X.unit, w))

/-- `γ ∘ (u × id) = α`. -/
theorem ousMed1_fac_left (y : ULift.{u} ℝ × Y.carrier) :
    (ousMed1 α β hc).toLinearMap (y.1.down • X.unit, y.2)
      = α.toLinearMap y := by
  show β.toLinearMap (y.1.down • X.unit, 0) + α.toLinearMap (0, y.2)
    = α.toLinearMap y
  have h1 : α.toLinearMap (y.1, (0 : Y.carrier))
      = β.toLinearMap (y.1.down • X.unit, (0 : ULift.{u} ℝ)) := by
    have h := hc y.1 0
    simpa using h
  have h3 : ((y.1, (0 : Y.carrier)) : ULift.{u} ℝ × Y.carrier)
      + (((0 : ULift.{u} ℝ), y.2) : ULift.{u} ℝ × Y.carrier) = y := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [← h1, ← map_add, h3]

/-- `γ ∘ (id × u) = β`. -/
theorem ousMed1_fac_right (y : X.carrier × ULift.{u} ℝ) :
    (ousMed1 α β hc).toLinearMap (y.1, y.2.down • Y.unit)
      = β.toLinearMap y := by
  show β.toLinearMap (y.1, 0) + α.toLinearMap (0, y.2.down • Y.unit)
    = β.toLinearMap y
  have h1 : α.toLinearMap ((0 : ULift.{u} ℝ), y.2.down • Y.unit)
      = β.toLinearMap ((0 : X.carrier), y.2) := by
    have h := hc 0 y.2
    simpa using h
  have h3 : ((y.1, (0 : ULift.{u} ℝ)) : X.carrier × ULift.{u} ℝ)
      + (((0 : X.carrier), y.2) : X.carrier × ULift.{u} ℝ) = y := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [h1, ← map_add, h3]

/-- `γ` is the *only* morphism with those two properties. -/
theorem ousMed1_uniq (m : X.prod Y ⟶ Z)
    (h₁ : ∀ y : ULift.{u} ℝ × Y.carrier,
      m.toLinearMap (y.1.down • X.unit, y.2) = α.toLinearMap y)
    (h₂ : ∀ y : X.carrier × ULift.{u} ℝ,
      m.toLinearMap (y.1, y.2.down • Y.unit) = β.toLinearMap y) :
    m = ousMed1 α β hc := by
  refine ous_hom_ext fun p => ?_
  show m.toLinearMap p = β.toLinearMap (p.1, 0) + α.toLinearMap (0, p.2)
  have e₁ : m.toLinearMap ((p.1, (0 : Y.carrier)) : X.carrier × Y.carrier)
      = β.toLinearMap (p.1, 0) := by
    have h := h₂ ((p.1, (0 : ULift.{u} ℝ)) : X.carrier × ULift.{u} ℝ)
    simpa using h
  have e₂ : m.toLinearMap (((0 : X.carrier), p.2) : X.carrier × Y.carrier)
      = α.toLinearMap (0, p.2) := by
    have h := h₁ (((0 : ULift.{u} ℝ), p.2) : ULift.{u} ℝ × Y.carrier)
    simpa using h
  have h3 : ((p.1, (0 : Y.carrier)) : X.carrier × Y.carrier)
      + (((0 : X.carrier), p.2) : X.carrier × Y.carrier) = p := by
    refine Prod.ext ?_ ?_ <;> simp
  have h4 : m.toLinearMap p
      = m.toLinearMap ((p.1, (0 : Y.carrier)) : X.carrier × Y.carrier)
        + m.toLinearMap (((0 : X.carrier), p.2) : X.carrier × Y.carrier) := by
    rw [← map_add, h3]
  rw [h4, e₁, e₂]

end OUSMed1

/-- `id × u : ℝ × ℝ ⟶ ℝ × Y`. -/
def ousSq1f (Y : OUS.{u}) : ousScal.{u}.prod ousScal.{u} ⟶ ousScal.{u}.prod Y :=
  ousProdMap (𝟙 ousScal.{u}) (ousUnitMap Y)

/-- `u × id : ℝ × ℝ ⟶ X × ℝ`. -/
def ousSq1g (X : OUS.{u}) : ousScal.{u}.prod ousScal.{u} ⟶ X.prod ousScal.{u} :=
  ousProdMap (ousUnitMap X) (𝟙 ousScal.{u})

/-- `u × id : ℝ × Y ⟶ X × Y`. -/
def ousSq1h (X Y : OUS.{u}) : ousScal.{u}.prod Y ⟶ X.prod Y :=
  ousProdMap (ousUnitMap X) (𝟙 Y)

/-- `id × u : X × ℝ ⟶ X × Y`. -/
def ousSq1i (X Y : OUS.{u}) : X.prod ousScal.{u} ⟶ X.prod Y :=
  ousProdMap (𝟙 X) (ousUnitMap Y)

/-- The defining equation of `ousSq1f`. -/
@[simp] theorem ousSq1f_apply (Y : OUS.{u}) (p : ULift.{u} ℝ × ULift.{u} ℝ) :
    (ousSq1f Y).toLinearMap p = (p.1, p.2.down • Y.unit) := rfl

/-- The defining equation of `ousSq1g`. -/
@[simp] theorem ousSq1g_apply (X : OUS.{u}) (p : ULift.{u} ℝ × ULift.{u} ℝ) :
    (ousSq1g X).toLinearMap p = (p.1.down • X.unit, p.2) := rfl

/-- The defining equation of `ousSq1h`. -/
@[simp] theorem ousSq1h_apply (X Y : OUS.{u}) (p : ULift.{u} ℝ × Y.carrier) :
    (ousSq1h X Y).toLinearMap p = (p.1.down • X.unit, p.2) := rfl

/-- The defining equation of `ousSq1i`. -/
@[simp] theorem ousSq1i_apply (X Y : OUS.{u}) (p : X.carrier × ULift.{u} ℝ) :
    (ousSq1i X Y).toLinearMap p = (p.1, p.2.down • Y.unit) := rfl

/-- **The left pullback square of 180I in `OUSᵒᵖ`**: the square
```
  ℝ × ℝ --id×u--> ℝ × Y
    |u×id           |u×id
    v               v
  X × ℝ --id×u--> X × Y
```
is a pushout in `OUS` — a positive unit-preserving map out of `X × Y` is
precisely a pair of such maps out of `ℝ × Y` and `X × ℝ` agreeing on
`ℝ × ℝ`, glued by `γ(x, y) = β(x, 0) + α(0, y)`. -/
theorem ous_isPushout1 (X Y : OUS.{u}) :
    IsPushout (ousSq1f Y) (ousSq1g X) (ousSq1h X Y) (ousSq1i X Y) := by
  have w : ousSq1f Y ≫ ousSq1h X Y = ousSq1g X ≫ ousSq1i X Y :=
    ous_hom_ext fun p =>
      (ous_comp_apply _ _ p).trans (ous_comp_apply _ _ p).symm
  have hcond : ∀ s : PushoutCocone (ousSq1f Y) (ousSq1g X),
      ∀ z w : ULift.{u} ℝ,
      s.inl.toLinearMap (z, w.down • Y.unit)
        = s.inr.toLinearMap (z.down • X.unit, w) := by
    intro s z w
    exact ((ous_comp_apply (ousSq1f Y) s.inl (z, w)).symm.trans
      (ous_congr s.condition (z, w))).trans
      (ous_comp_apply (ousSq1g X) s.inr (z, w))
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s => ousMed1 s.inl s.inr (hcond s)) ?_ ?_ ?_)
  · intro s
    exact ous_hom_ext fun y =>
      (ous_comp_apply (ousSq1h X Y) _ y).trans
        (ousMed1_fac_left _ _ (hcond s) y)
  · intro s
    exact ous_hom_ext fun y =>
      (ous_comp_apply (ousSq1i X Y) _ y).trans
        (ousMed1_fac_right _ _ (hcond s) y)
  · intro s m h₁ h₂
    refine ousMed1_uniq _ _ (hcond s) m (fun y => ?_) (fun y => ?_)
    · exact (ous_comp_apply (ousSq1h X Y) m y).symm.trans (ous_congr h₁ y)
    · exact (ous_comp_apply (ousSq1i X Y) m y).symm.trans (ous_congr h₂ y)

/-! ### The right pushout square of 180I in `OUS` -/

/-- **A positive map on a product killing `(0, 1)` kills `0 × Y`.**  For
`0 ≤ c` the order-unit axiom gives `(0, c) ≤ n · (0, 1)`, so `α(0, c)` is
squeezed between `0` and `0`; a general `c` is a difference of two
positive elements (`ou_eq_sub_of_nonneg`).  This is the order-unit
replacement of the norm estimate `c ≤ ‖c‖ · 1` used for von Neumann
algebras. -/
theorem ous_prod_apply_eq_zero {X Y Z : OUS.{u}} (α : X.prod Y ⟶ Z)
    (h1 : α.toLinearMap ((0 : X.carrier), Y.unit) = 0) (b : Y.carrier) :
    α.toLinearMap ((0 : X.carrier), b) = 0 := by
  have hnn : ∀ c : Y.carrier, 0 ≤ c →
      α.toLinearMap ((0 : X.carrier), c) = 0 := by
    intro c hc
    obtain ⟨n, hn⟩ := ou_exists_le_smul_unit c
    have hle : (((0 : X.carrier), c) : X.carrier × Y.carrier)
        ≤ ((0 : X.carrier), (n : ℝ) • Y.unit) :=
      Prod.le_def.mpr ⟨le_refl _, hn⟩
    have h0 : (0 : X.carrier × Y.carrier)
        ≤ (((0 : X.carrier), c) : X.carrier × Y.carrier) :=
      Prod.le_def.mpr ⟨le_refl _, hc⟩
    have hsm : (((0 : X.carrier), (n : ℝ) • Y.unit) : X.carrier × Y.carrier)
        = (n : ℝ) • (((0 : X.carrier), Y.unit) : X.carrier × Y.carrier) := by
      refine Prod.ext ?_ ?_ <;> simp
    have hz : α.toLinearMap ((0 : X.carrier), (n : ℝ) • Y.unit) = 0 := by
      rw [hsm, map_smul, h1, smul_zero]
    refine le_antisymm ?_ ?_
    · rw [← hz]; exact α.mono hle
    · have hp := α.mono h0
      rwa [map_zero] at hp
  obtain ⟨p, q, hp, hq, hb⟩ := ou_eq_sub_of_nonneg b
  have hsplit : (((0 : X.carrier), b) : X.carrier × Y.carrier)
      = (((0 : X.carrier), p) : X.carrier × Y.carrier)
        - (((0 : X.carrier), q) : X.carrier × Y.carrier) := by
    rw [hb]
    refine Prod.ext ?_ ?_ <;> simp
  rw [hsplit, map_sub, hnn p hp, hnn q hq, sub_zero]

section OUSMed2

variable {X Y Z : OUS.{u}}

/-- The mediating morphism `γ(x) = α(x, 0)` of the second pushout
square. -/
def ousMed2 (α : X.prod Y ⟶ Z) (β : ousScal.{u} ⟶ Z)
    (hc : ∀ z w : ULift.{u} ℝ,
      α.toLinearMap (z.down • X.unit, w.down • Y.unit)
        = β.toLinearMap z) : X ⟶ Z where
  toLinearMap := α.toLinearMap.comp (LinearMap.inl ℝ X.carrier Y.carrier)
  map_nonneg' x hx := α.map_nonneg' _ (Prod.le_def.mpr ⟨hx, le_refl _⟩)
  map_unit' := by
    show α.toLinearMap (X.unit, (0 : Y.carrier)) = Z.unit
    have h01 : α.toLinearMap ((0 : X.carrier), Y.unit) = 0 := by
      have h := hc 0 1
      rw [show β.toLinearMap (0 : ULift.{u} ℝ) = 0 from map_zero _] at h
      simpa using h
    have h3 : ((X.unit, (0 : Y.carrier)) : X.carrier × Y.carrier)
        + (((0 : X.carrier), Y.unit) : X.carrier × Y.carrier)
        = (X.prod Y).unit := by
      refine Prod.ext ?_ ?_ <;> simp
    have h4 : α.toLinearMap (X.unit, (0 : Y.carrier))
        + α.toLinearMap ((0 : X.carrier), Y.unit) = Z.unit := by
      rw [← map_add, h3]
      exact α.map_unit'
    rwa [h01, add_zero] at h4

/-- The defining equation of `ousMed2`. -/
@[simp] theorem ousMed2_apply (α : X.prod Y ⟶ Z) (β : ousScal.{u} ⟶ Z) (hc)
    (x : X.carrier) :
    (ousMed2 α β hc).toLinearMap x = α.toLinearMap (x, 0) := rfl

variable (α : X.prod Y ⟶ Z) (β : ousScal.{u} ⟶ Z)
  (hc : ∀ z w : ULift.{u} ℝ,
    α.toLinearMap (z.down • X.unit, w.down • Y.unit) = β.toLinearMap z)

/-- `γ ∘ π₁ = α`. -/
theorem ousMed2_fac_left (p : X.carrier × Y.carrier) :
    (ousMed2 α β hc).toLinearMap p.1 = α.toLinearMap p := by
  show α.toLinearMap (p.1, 0) = α.toLinearMap p
  have h01 : α.toLinearMap ((0 : X.carrier), Y.unit) = 0 := by
    have h := hc 0 1
    rw [show β.toLinearMap (0 : ULift.{u} ℝ) = 0 from map_zero _] at h
    simpa using h
  have h3 : ((p.1, (0 : Y.carrier)) : X.carrier × Y.carrier)
      + (((0 : X.carrier), p.2) : X.carrier × Y.carrier) = p := by
    refine Prod.ext ?_ ?_ <;> simp
  have h4 : α.toLinearMap p
      = α.toLinearMap (p.1, (0 : Y.carrier))
        + α.toLinearMap ((0 : X.carrier), p.2) := by
    rw [← map_add, h3]
  rw [h4, ous_prod_apply_eq_zero α h01 p.2, add_zero]

/-- `γ ∘ u = β`. -/
theorem ousMed2_fac_right (z : ULift.{u} ℝ) :
    (ousMed2 α β hc).toLinearMap (z.down • X.unit) = β.toLinearMap z := by
  show α.toLinearMap (z.down • X.unit, 0) = β.toLinearMap z
  have h := hc z 0
  simpa using h

/-- `γ` is the only morphism with that property. -/
theorem ousMed2_uniq (m : X ⟶ Z)
    (h₁ : ∀ p : X.carrier × Y.carrier,
      m.toLinearMap p.1 = α.toLinearMap p) : m = ousMed2 α β hc := by
  refine ous_hom_ext fun x => ?_
  show m.toLinearMap x = α.toLinearMap (x, 0)
  exact h₁ ((x, (0 : Y.carrier)) : X.carrier × Y.carrier)

end OUSMed2

/-- `u × u : ℝ × ℝ ⟶ X × Y`. -/
def ousSq2f (X Y : OUS.{u}) : ousScal.{u}.prod ousScal.{u} ⟶ X.prod Y :=
  ousProdMap (ousUnitMap X) (ousUnitMap Y)

/-- `π₁ : ℝ × ℝ ⟶ ℝ`. -/
def ousSq2g : ousScal.{u}.prod ousScal.{u} ⟶ ousScal.{u} :=
  ousFst ousScal.{u} ousScal.{u}

/-- `π₁ : X × Y ⟶ X`. -/
def ousSq2h (X Y : OUS.{u}) : X.prod Y ⟶ X := ousFst X Y

/-- `u : ℝ ⟶ X`. -/
def ousSq2i (X : OUS.{u}) : ousScal.{u} ⟶ X := ousUnitMap X

/-- **The right pullback square of 180I in `OUSᵒᵖ`**: the square
```
  ℝ × ℝ --u×u--> X × Y
    |π₁            |π₁
    v              v
    ℝ  ---u----->  X
```
is a pushout in `OUS`.  The mediating map is `γ(x) = α(x, 0)`; that it is
well defined uses `ous_prod_apply_eq_zero`. -/
theorem ous_isPushout2 (X Y : OUS.{u}) :
    IsPushout (ousSq2f X Y) ousSq2g.{u} (ousSq2h X Y) (ousSq2i X) := by
  have w : ousSq2f X Y ≫ ousSq2h X Y = ousSq2g.{u} ≫ ousSq2i X :=
    ous_hom_ext fun p =>
      (ous_comp_apply _ _ p).trans (ous_comp_apply _ _ p).symm
  have hcond : ∀ s : PushoutCocone (ousSq2f X Y) ousSq2g.{u},
      ∀ z w : ULift.{u} ℝ,
      s.inl.toLinearMap (z.down • X.unit, w.down • Y.unit)
        = s.inr.toLinearMap z := by
    intro s z w
    exact ((ous_comp_apply (ousSq2f X Y) s.inl (z, w)).symm.trans
      (ous_congr s.condition (z, w))).trans
      (ous_comp_apply ousSq2g.{u} s.inr (z, w))
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s => ousMed2 s.inl s.inr (hcond s)) ?_ ?_ ?_)
  · intro s
    exact ous_hom_ext fun p =>
      (ous_comp_apply (ousSq2h X Y) _ p).trans
        (ousMed2_fac_left _ _ (hcond s) p)
  · intro s
    exact ous_hom_ext fun z =>
      (ous_comp_apply (ousSq2i X) _ z).trans
        (ousMed2_fac_right _ _ (hcond s) z)
  · intro s m h₁ _
    exact ousMed2_uniq _ _ (hcond s) m
      (fun p => (ous_comp_apply (ousSq2h X Y) m p).symm.trans (ous_congr h₁ p))

/-! ### Joint monicity of the two cotuples in `OUSᵒᵖ` -/

/-- **The third axiom of 180I in `OUSᵒᵖ`**, elementwise: a positive
unit-preserving map out of `ℝ³` is determined by its restrictions along
`(x,y) ↦ (x,y,y)` and `(x,y) ↦ (y,x,y)`, because those recover the images
of the three coordinate units, and `ℝ³` is spanned by them. -/
theorem ous_jointlyMonic_aux {Z : OUS.{u}}
    (a b : (ousScal.{u}.prod ousScal.{u}).prod ousScal.{u} ⟶ Z)
    (h1 : ∀ x : ULift.{u} ℝ × ULift.{u} ℝ,
      a.toLinearMap ((x.1, x.2), x.2) = b.toLinearMap ((x.1, x.2), x.2))
    (h2 : ∀ x : ULift.{u} ℝ × ULift.{u} ℝ,
      a.toLinearMap ((x.2, x.1), x.2) = b.toLinearMap ((x.2, x.1), x.2)) :
    a = b := by
  set e₁ : (ULift.{u} ℝ × ULift.{u} ℝ) × ULift.{u} ℝ := ((1, 0), 0) with he₁
  set e₂ : (ULift.{u} ℝ × ULift.{u} ℝ) × ULift.{u} ℝ := ((0, 1), 0) with he₂
  set e₃ : (ULift.{u} ℝ × ULift.{u} ℝ) × ULift.{u} ℝ := ((0, 0), 1) with he₃
  have ha1 : a.toLinearMap e₁ = b.toLinearMap e₁ := h1 (1, 0)
  have ha2 : a.toLinearMap e₂ = b.toLinearMap e₂ := h2 (1, 0)
  have ha3 : a.toLinearMap e₃ = b.toLinearMap e₃ := by
    have h4 := h1 (0, 1)
    have hsum : (((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)), (1 : ULift.{u} ℝ))
        = e₂ + e₃ := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [he₂, he₃]
    rw [hsum, map_add, map_add, ha2] at h4
    exact add_left_cancel h4
  have key : ∀ (f : (ousScal.{u}.prod ousScal.{u}).prod ousScal.{u} ⟶ Z)
      (y : (ULift.{u} ℝ × ULift.{u} ℝ) × ULift.{u} ℝ),
      f.toLinearMap y = y.1.1.down • f.toLinearMap e₁
        + (y.1.2.down • f.toLinearMap e₂ + y.2.down • f.toLinearMap e₃) := by
    intro f y
    have hdec : y = y.1.1.down • e₁ + (y.1.2.down • e₂ + y.2.down • e₃) := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;>
        · apply ULift.down_injective
          simp [he₁, he₂, he₃]
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, map_add, map_smul, map_smul]
  refine ous_hom_ext fun y => ?_
  rw [key a y, key b y, ha1, ha2, ha3]

/-! ### `OUSᵒᵖ` is an effectus -/

instance ousOpHasTerminal : HasTerminal (OUS.{u}ᵒᵖ) := ousPres.hT.hasTerminal

/-- The zero space is the initial object of `OUSᵒᵖ`. -/
instance ousOpHasInitial : HasInitial (OUS.{u}ᵒᵖ) :=
  (IsTerminal.op (OUS.{u}) ousTrivIsTerminal).hasInitial

/-- Binary coproducts of `OUSᵒᵖ` are the products of `OUS`. -/
instance ousOpHasColimitPair (X Y : OUS.{u}ᵒᵖ) : HasColimit (pair X Y) :=
  HasColimit.mk ⟨_, ousPres.hP X Y⟩

/-- `OUSᵒᵖ` has binary coproducts. -/
instance ousOpHasBinaryCoproducts : HasBinaryCoproducts (OUS.{u}ᵒᵖ) :=
  hasBinaryCoproducts_of_hasColimit_pair _

/-- `OUSᵒᵖ` has finite coproducts. -/
instance ousOpHasFiniteCoproducts : HasFiniteCoproducts (OUS.{u}ᵒᵖ) :=
  hasFiniteCoproducts_of_has_binary_and_initial

/-- **189aII.1** (`effexamplesintro`, eff.tex:2032, Examples): the three
axioms of 180I for `OUSᵒᵖ`, as an instance; `effectus_ous` bundles it. -/
instance effectusTotalForm_ous : EffectusTotalForm OUS.{u}ᵒᵖ := by
  refine effectusTotalForm_of_pres ousPres ?_ ?_ ?_
  · intro X Y
    have e₁ : ousPres.pmap (𝟙 X) (ousPres.hT.from Y)
        = Quiver.Hom.op (ousSq1i X.unop Y.unop) := by
      refine ousop_hom_ext fun p => (ousPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext rfl ?_
      exact ousPres_from_apply Y p.2
    have e₂ : ousPres.pmap (ousPres.hT.from X) (𝟙 Y)
        = Quiver.Hom.op (ousSq1h X.unop Y.unop) := by
      refine ousop_hom_ext fun p => (ousPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ rfl
      exact ousPres_from_apply X p.1
    have e₃ : ousPres.pmap (ousPres.hT.from X) (𝟙 ousPres.T)
        = Quiver.Hom.op (ousSq1g X.unop) := by
      refine ousop_hom_ext fun p => (ousPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ rfl
      exact ousPres_from_apply X p.1
    have e₄ : ousPres.pmap (𝟙 ousPres.T) (ousPres.hT.from Y)
        = Quiver.Hom.op (ousSq1f Y.unop) := by
      refine ousop_hom_ext fun p => (ousPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext rfl ?_
      exact ousPres_from_apply Y p.2
    rw [e₁, e₂, e₃, e₄]
    exact (ous_isPushout1 X.unop Y.unop).op
  · intro X Y
    have f₁ : ousPres.hT.from X = Quiver.Hom.op (ousSq2i X.unop) :=
      ousPres.hT.hom_ext _ _
    have f₄ : ousPres.pmap (ousPres.hT.from X) (ousPres.hT.from Y)
        = Quiver.Hom.op (ousSq2f X.unop Y.unop) := by
      refine ousop_hom_ext fun p => (ousPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ ?_
      · exact ousPres_from_apply X p.1
      · exact ousPres_from_apply Y p.2
    rw [f₄, f₁]
    exact (ous_isPushout2 X.unop Y.unop).op
  · intro Z a b hf hg
    apply Quiver.Hom.unop_inj
    refine ous_jointlyMonic_aux a.unop b.unop (fun x => ?_) (fun x => ?_)
    · exact ousop_comp_congr hf x
    · exact ousop_comp_congr hg x

/-- **189aII.1** (`effexamplesintro`, eff.tex:2032, Examples): the
category `OUSᵒᵖ` of order unit spaces with positive unit-preserving linear
maps in the opposite direction is an effectus in total form.

The point gives no proof.  Ours is the `vNᵒᵖ` argument of `effectus_vn`
with the C\*-algebra replaced by an ordered real vector space: `ℝ` is
initial in `OUS` and the products are the coproducts of `OUSᵒᵖ`
(`ousPres`), the two squares of 180I are the pushouts `ous_isPushout1`
and `ous_isPushout2`, and the two cotuples are jointly monic by
`ous_jointlyMonic_aux`.  That argument is the instance
`effectusTotalForm_ous` above (it is needed as an instance by the `Pred`,
`Stat` and `Scal` of 190IV.1); this theorem only bundles it. -/
theorem effectus_ous : Nonempty (EffectusTotalStructure OUS.{u}ᵒᵖ) :=
  ⟨{ hasFiniteCoproducts := inferInstance
     hasTerminal := inferInstance
     effectus := inferInstance }⟩

/-! ## Order unit groups (189aII.2) -/

/-- **189aII.2** (`effexamplesintro`, eff.tex:2037, Examples): an **order
unit group** is a partially ordered abelian group with a distinguished
order unit.  Stated as a mixin over `AddCommGroup G` and `PartialOrder G`:
the order is translation-invariant and the distinguished element `unit` is
a positive element with `∀ g, ∃ n : ℕ, g ≤ n • unit`.

Unlike for order unit spaces, positivity of the unit must be required
here (this is the standard, Goodearl, definition): in `ℤ` with positive
cone `2ℕ` the element `1` satisfies the order-unit inequality for every
`g` but is not positive. -/
class OrderUnitGroup (G : Type u) [AddCommGroup G] [PartialOrder G] where
  /-- the order is translation-invariant -/
  protected add_le_add_left (x y : G) : x ≤ y → ∀ z, x + z ≤ y + z
  /-- the distinguished order unit -/
  unit : G
  /-- ... which is positive -/
  protected unit_nonneg : 0 ≤ unit
  /-- ... and an order unit -/
  protected exists_le_nsmul_unit (g : G) : ∃ n : ℕ, g ≤ n • unit

section OUGBasic

variable {G : Type u} [AddCommGroup G] [PartialOrder G] [OrderUnitGroup G]

/-- The distinguished order unit of an order unit group, with the group as
an explicit argument. -/
abbrev ougUnit (G : Type u) [AddCommGroup G] [PartialOrder G]
    [OrderUnitGroup G] : G := OrderUnitGroup.unit

/-- An order unit group is an ordered additive monoid. -/
instance OrderUnitGroup.toIsOrderedAddMonoid : IsOrderedAddMonoid G where
  add_le_add_left := OrderUnitGroup.add_le_add_left

/-- Translation-invariance of the order, as a lemma. -/
theorem oug_add_le_add_right {x y : G} (h : x ≤ y) (z : G) : x + z ≤ y + z :=
  OrderUnitGroup.add_le_add_left x y h z

/-- The order unit is positive (an axiom, see the class doc string). -/
theorem oug_unit_nonneg : (0 : G) ≤ ougUnit G := OrderUnitGroup.unit_nonneg

/-- The order-unit axiom. -/
theorem oug_exists_le_nsmul_unit (g : G) : ∃ n : ℕ, g ≤ n • ougUnit G :=
  OrderUnitGroup.exists_le_nsmul_unit g

/-- Natural multiples of a positive element are positive. -/
theorem oug_nsmul_nonneg {a : G} (ha : 0 ≤ a) : ∀ n : ℕ, 0 ≤ n • a := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      rw [succ_nsmul]
      exact add_nonneg ih ha

/-- Integer multiples of a positive element by a non-negative integer are
positive. -/
theorem oug_zsmul_nonneg {a : G} (ha : 0 ≤ a) {n : ℤ} (hn : 0 ≤ n) :
    0 ≤ n • a := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [natCast_zsmul]
  exact oug_nsmul_nonneg ha m

/-- The multiples of the order unit are monotone in the multiplier. -/
theorem oug_nsmul_unit_mono {n m : ℕ} (h : n ≤ m) :
    n • ougUnit G ≤ m • ougUnit G := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_nsmul]
  exact le_add_of_nonneg_right (oug_nsmul_nonneg oug_unit_nonneg k)

/-- **Every element of an order unit group is a difference of two positive
elements**: from `g ≤ n • 1` one gets `g = n•1 - (n•1 - g)`. -/
theorem oug_eq_sub_of_nonneg (g : G) :
    ∃ p q : G, 0 ≤ p ∧ 0 ≤ q ∧ g = p - q := by
  obtain ⟨n, hn⟩ := oug_exists_le_nsmul_unit g
  refine ⟨n • ougUnit G, n • ougUnit G - g,
    oug_nsmul_nonneg oug_unit_nonneg n, sub_nonneg.mpr hn, ?_⟩
  abel

end OUGBasic

/-! ### The basic examples of order unit groups -/

/-- `ℤ` is an order unit group with order unit `1`. -/
instance Int.orderUnitGroup : OrderUnitGroup ℤ where
  add_le_add_left x y h z := by
    rw [add_comm x z, add_comm y z]; exact add_le_add_right h z
  unit := 1
  unit_nonneg := zero_le_one
  exists_le_nsmul_unit g := ⟨g.toNat, by simp⟩

/-- An order unit group stays one after `ULift`ing. -/
instance ULift.orderUnitGroup (G : Type u) [AddCommGroup G] [PartialOrder G]
    [OrderUnitGroup G] : OrderUnitGroup (ULift.{v} G) where
  add_le_add_left x y h z := by
    show x.down + z.down ≤ y.down + z.down
    exact oug_add_le_add_right (show x.down ≤ y.down from h) z.down
  unit := ULift.up (ougUnit G)
  unit_nonneg := by
    show (0 : G) ≤ ougUnit G
    exact oug_unit_nonneg
  exists_le_nsmul_unit g := by
    obtain ⟨n, hn⟩ := oug_exists_le_nsmul_unit g.down
    exact ⟨n, hn⟩

/-- The one-point group is an order unit group; it is the final object of
`OUG`, hence the initial object of `OUGᵒᵖ`. -/
instance PUnit.orderUnitGroup : OrderUnitGroup PUnit.{u + 1} where
  add_le_add_left _ _ _ _ := le_of_eq (Subsingleton.elim _ _)
  unit := PUnit.unit
  unit_nonneg := le_of_eq (Subsingleton.elim _ _)
  exists_le_nsmul_unit _ := ⟨0, le_of_eq (Subsingleton.elim _ _)⟩

/-- The product of two order unit groups, with the coordinatewise order
and unit `(1, 1)`. -/
instance Prod.orderUnitGroup (G H : Type u) [AddCommGroup G] [PartialOrder G]
    [OrderUnitGroup G] [AddCommGroup H] [PartialOrder H] [OrderUnitGroup H] :
    OrderUnitGroup (G × H) where
  add_le_add_left _ _ h z :=
    Prod.le_def.mpr ⟨oug_add_le_add_right (Prod.le_def.mp h).1 z.1,
      oug_add_le_add_right (Prod.le_def.mp h).2 z.2⟩
  unit := (ougUnit G, ougUnit H)
  unit_nonneg := Prod.le_def.mpr ⟨oug_unit_nonneg, oug_unit_nonneg⟩
  exists_le_nsmul_unit p := by
    obtain ⟨n, hn⟩ := oug_exists_le_nsmul_unit p.1
    obtain ⟨m, hm⟩ := oug_exists_le_nsmul_unit p.2
    refine ⟨max n m, Prod.le_def.mpr ⟨?_, ?_⟩⟩
    · exact hn.trans (oug_nsmul_unit_mono (Nat.le_max_left n m))
    · exact hm.trans (oug_nsmul_unit_mono (Nat.le_max_right n m))

/-! ### The category `OUG` -/

/-- A bundled order unit group: the object type of the category `OUG`. -/
structure OUG : Type (u + 1) where
  /-- the underlying type -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [partialOrder : PartialOrder carrier]
  [orderUnitGroup : OrderUnitGroup carrier]

attribute [instance] OUG.addCommGroup OUG.partialOrder OUG.orderUnitGroup

/-- An object of `OUG` may be used directly as its carrier type. -/
instance : CoeSort OUG.{u} (Type u) := ⟨OUG.carrier⟩

/-- Bundle an order unit group as an object of `OUG`. -/
abbrev OUG.of (G : Type u) [AddCommGroup G] [PartialOrder G]
    [OrderUnitGroup G] : OUG.{u} := ⟨G⟩

/-- The order unit of a bundled order unit group. -/
abbrev OUG.unit (G : OUG.{u}) : G.carrier := ougUnit G.carrier

/-- The product of two bundled order unit groups. -/
abbrev OUG.prod (G H : OUG.{u}) : OUG.{u} := OUG.of (G.carrier × H.carrier)

/-- The scalars `ℤᵤ`: the initial object of `OUG`, hence the final object
of `OUGᵒᵖ`. -/
abbrev ougScal : OUG.{u} := OUG.of (ULift.{u} ℤ)

/-- The zero group: the final object of `OUG`, hence the initial object of
`OUGᵒᵖ`. -/
abbrev ougTriv : OUG.{u} := OUG.of PUnit.{u + 1}

/-- The order unit of the scalars `ℤᵤ` is `1`. -/
@[simp] theorem ougScal_unit : ougScal.{u}.unit = (1 : ULift.{u} ℤ) := rfl

/-- The order unit of a product is the pair of the order units. -/
@[simp] theorem OUG.prod_unit (G H : OUG.{u}) :
    (G.prod H).unit = (G.unit, H.unit) := rfl

/-- A **positive unit-preserving homomorphism** of order unit groups: the
morphisms of `OUG` (and, read backwards, of `OUGᵒᵖ`). -/
structure OUGMap (G H : OUG.{u}) : Type u where
  /-- the underlying additive homomorphism -/
  toAddHom : G.carrier →+ H.carrier
  /-- ... which is positive -/
  map_nonneg' : ∀ g : G.carrier, 0 ≤ g → 0 ≤ toAddHom g
  /-- ... and unit-preserving -/
  map_unit' : toAddHom G.unit = H.unit

/-- Extensionality for morphisms of `OUG`. -/
theorem OUGMap.ext' {G H : OUG.{u}} {f g : OUGMap G H}
    (h : ∀ x, f.toAddHom x = g.toAddHom x) : f = g := by
  obtain ⟨f, hf₁, hf₂⟩ := f
  obtain ⟨g, hg₁, hg₂⟩ := g
  have hfg : f = g := AddMonoidHom.ext h
  subst hfg
  rfl

/-- A positive homomorphism is monotone. -/
theorem OUGMap.mono {G H : OUG.{u}} (f : OUGMap G H) {x y : G.carrier}
    (h : x ≤ y) : f.toAddHom x ≤ f.toAddHom y := by
  have h1 := f.map_nonneg' (y - x) (sub_nonneg.mpr h)
  rw [map_sub] at h1
  exact sub_nonneg.mp h1

/-- The identity morphism of `OUG`. -/
def OUGMap.id (G : OUG.{u}) : OUGMap G G where
  toAddHom := AddMonoidHom.id _
  map_nonneg' _ h := h
  map_unit' := rfl

/-- Composition in `OUG` (diagrammatic order). -/
def OUGMap.comp {G H K : OUG.{u}} (f : OUGMap G H) (g : OUGMap H K) :
    OUGMap G K where
  toAddHom := g.toAddHom.comp f.toAddHom
  map_nonneg' x h := g.map_nonneg' _ (f.map_nonneg' x h)
  map_unit' := by
    show g.toAddHom (f.toAddHom G.unit) = K.unit
    rw [f.map_unit', g.map_unit']

/-- **The category `OUG`** of order unit groups with positive
unit-preserving homomorphisms. -/
instance : Category.{u} OUG.{u} where
  Hom G H := OUGMap G H
  id G := OUGMap.id G
  comp f g := OUGMap.comp f g
  id_comp _ := OUGMap.ext' fun _ => rfl
  comp_id _ := OUGMap.ext' fun _ => rfl
  assoc _ _ _ := OUGMap.ext' fun _ => rfl

/-- Extensionality in `OUG`, for morphisms written with `⟶`. -/
theorem oug_hom_ext {G H : OUG.{u}} {f g : G ⟶ H}
    (h : ∀ x, f.toAddHom x = g.toAddHom x) : f = g := OUGMap.ext' h

/-- Composition in `OUG` is composition of the underlying functions. -/
theorem oug_comp_apply {G H K : OUG.{u}} (f : G ⟶ H) (g : H ⟶ K)
    (x : G.carrier) : (f ≫ g).toAddHom x = g.toAddHom (f.toAddHom x) := rfl

/-- The identity of `OUG` is the identity function. -/
theorem oug_id_apply {G : OUG.{u}} (x : G.carrier) :
    (𝟙 G : G ⟶ G).toAddHom x = x := rfl

/-- Equal morphisms of `OUG` agree pointwise. -/
theorem oug_congr {G H : OUG.{u}} {f g : G ⟶ H} (h : f = g) (x : G.carrier) :
    f.toAddHom x = g.toAddHom x := by rw [h]

/-- Extensionality in `OUGᵒᵖ`. -/
theorem ougop_hom_ext {G H : OUG.{u}ᵒᵖ} {f g : G ⟶ H}
    (h : ∀ x, f.unop.toAddHom x = g.unop.toAddHom x) : f = g :=
  Quiver.Hom.unop_inj (oug_hom_ext h)

/-- Composition in `OUGᵒᵖ` applies the two underlying functions in the
opposite order. -/
theorem ougop_comp_apply {G H K : OUG.{u}ᵒᵖ} (f : G ⟶ H) (g : H ⟶ K)
    (x : K.unop.carrier) :
    (f ≫ g).unop.toAddHom x = f.unop.toAddHom (g.unop.toAddHom x) :=
  oug_comp_apply g.unop f.unop x

/-- Equal morphisms of `OUGᵒᵖ` agree pointwise. -/
theorem ougop_congr {G H : OUG.{u}ᵒᵖ} {f g : G ⟶ H} (h : f = g)
    (x : H.unop.carrier) : f.unop.toAddHom x = g.unop.toAddHom x := by rw [h]

/-- Postcomposition with a fixed map, pointwise. -/
theorem ougop_comp_congr {Z P G : OUG.{u}ᵒᵖ} {F : P ⟶ G} {a b : Z ⟶ P}
    (h : a ≫ F = b ≫ F) (x : G.unop.carrier) :
    a.unop.toAddHom (F.unop.toAddHom x) = b.unop.toAddHom (F.unop.toAddHom x) :=
  ((ougop_comp_apply a F x).symm.trans (ougop_congr h x)).trans
    (ougop_comp_apply b F x)

/-! ### The concrete final, initial and product objects of `OUG` -/

/-- The unique morphism `ℤᵤ ⟶ G` of `OUG`, namely `n ↦ n · 1`. -/
def ougUnitMap (G : OUG.{u}) : ougScal.{u} ⟶ G where
  toAddHom := AddMonoidHom.mk' (fun n => n.down • G.unit) (fun a b => by
    show (a.down + b.down) • G.unit = a.down • G.unit + b.down • G.unit
    exact add_zsmul _ _ _)
  map_nonneg' n hn := oug_zsmul_nonneg oug_unit_nonneg hn
  map_unit' := one_zsmul _

/-- The defining equation of `ougUnitMap`. -/
@[simp] theorem ougUnitMap_apply (G : OUG.{u}) (n : ULift.{u} ℤ) :
    (ougUnitMap G).toAddHom n = n.down • G.unit := rfl

/-- The unique morphism `G ⟶ 0` of `OUG`. -/
def ougTrivMap (G : OUG.{u}) : G ⟶ ougTriv.{u} where
  toAddHom := 0
  map_nonneg' _ _ := le_of_eq (Subsingleton.elim _ _)
  map_unit' := Subsingleton.elim _ _

/-- The first projection `G × H ⟶ G`. -/
def ougFst (G H : OUG.{u}) : G.prod H ⟶ G where
  toAddHom := AddMonoidHom.fst G.carrier H.carrier
  map_nonneg' _ h := (Prod.le_def.mp h).1
  map_unit' := rfl

/-- The second projection `G × H ⟶ H`. -/
def ougSnd (G H : OUG.{u}) : G.prod H ⟶ H where
  toAddHom := AddMonoidHom.snd G.carrier H.carrier
  map_nonneg' _ h := (Prod.le_def.mp h).2
  map_unit' := rfl

/-- The pairing `⟨f, g⟩ : K ⟶ G × H`. -/
def ougPair {K G H : OUG.{u}} (f : K ⟶ G) (g : K ⟶ H) : K ⟶ G.prod H where
  toAddHom := AddMonoidHom.prod f.toAddHom g.toAddHom
  map_nonneg' z h := Prod.le_def.mpr ⟨f.map_nonneg' z h, g.map_nonneg' z h⟩
  map_unit' := Prod.ext f.map_unit' g.map_unit'

/-- The defining equation of `ougPair`. -/
@[simp] theorem ougPair_apply {K G H : OUG.{u}} (f : K ⟶ G) (g : K ⟶ H)
    (z : K.carrier) :
    (ougPair f g).toAddHom z = (f.toAddHom z, g.toAddHom z) := rfl

/-- The product `f × g : G × H ⟶ G' × H'` of two morphisms. -/
def ougProdMap {G G' H H' : OUG.{u}} (f : G ⟶ G') (g : H ⟶ H') :
    G.prod H ⟶ G'.prod H' where
  toAddHom := f.toAddHom.prodMap g.toAddHom
  map_nonneg' _ h :=
    Prod.le_def.mpr ⟨f.map_nonneg' _ (Prod.le_def.mp h).1,
      g.map_nonneg' _ (Prod.le_def.mp h).2⟩
  map_unit' := Prod.ext f.map_unit' g.map_unit'

/-- The defining equation of `ougProdMap`. -/
@[simp] theorem ougProdMap_apply {G G' H H' : OUG.{u}} (f : G ⟶ G')
    (g : H ⟶ H') (p : G.carrier × H.carrier) :
    (ougProdMap f g).toAddHom p = (f.toAddHom p.1, g.toAddHom p.2) := rfl

/-- Any morphism `ℤᵤ ⟶ G` is `n ↦ n · 1`. -/
theorem ougUnitMap_unique {G : OUG.{u}} (f : ougScal.{u} ⟶ G) :
    f = ougUnitMap G := by
  refine oug_hom_ext fun n => ?_
  have hn : n = n.down • (1 : ULift.{u} ℤ) := by
    apply ULift.down_injective
    simp
  rw [ougUnitMap_apply]
  conv_lhs => rw [hn]
  rw [map_zsmul]
  exact congrArg (fun z => n.down • z) f.map_unit'

/-- **`ℤᵤ` is the initial object of `OUG`**, hence the final object of
`OUGᵒᵖ`. -/
def ougScalIsInitial : IsInitial ougScal.{u} :=
  IsInitial.ofUniqueHom (fun G => ougUnitMap G) (fun _ f => ougUnitMap_unique f)

/-- **The zero group is the final object of `OUG`**, hence the initial
object of `OUGᵒᵖ`. -/
def ougTrivIsTerminal : IsTerminal ougTriv.{u} :=
  IsTerminal.ofUniqueHom (fun G => ougTrivMap G)
    (fun _ _ => oug_hom_ext fun _ =>
      Subsingleton.elim (α := PUnit.{u + 1}) _ _)

/-- The concrete presentation of `OUGᵒᵖ`: the final object is the scalars
`ℤᵤ`, the binary coproducts are the products. -/
noncomputable def ougPres : CoprodPres (OUG.{u}ᵒᵖ) where
  T := Opposite.op ougScal.{u}
  hT := IsInitial.op (OUG.{u}) ougScalIsInitial
  P G H := Opposite.op (G.unop.prod H.unop)
  pinl G H := Quiver.Hom.op (ougFst G.unop H.unop)
  pinr G H := Quiver.Hom.op (ougSnd G.unop H.unop)
  hP G H := BinaryCofan.IsColimit.mk _
    (fun {_} u v => Quiver.Hom.op (ougPair u.unop v.unop))
    (fun {_} _ _ => ougop_hom_ext fun x => ougop_comp_apply _ _ x)
    (fun {_} _ _ => ougop_hom_ext fun x => ougop_comp_apply _ _ x)
    (fun {_} _ _ m h₁ h₂ => ougop_hom_ext fun x => by
      refine Prod.ext ?_ ?_
      · exact (ougop_comp_apply _ m x).symm.trans (ougop_congr h₁ x)
      · exact (ougop_comp_apply _ m x).symm.trans (ougop_congr h₂ x))

/-- The unique morphism into the final object of `OUGᵒᵖ` is `n ↦ n · 1`. -/
theorem ougPres_from_apply (H : OUG.{u}ᵒᵖ) (n : ULift.{u} ℤ) :
    (ougPres.hT.from H).unop.toAddHom n = n.down • H.unop.unit := by
  have h : ougPres.hT.from H = Quiver.Hom.op (ougUnitMap H.unop) :=
    ougPres.hT.hom_ext _ _
  rw [h]
  rfl

/-- The coproduct of two morphisms of `OUGᵒᵖ` acts coordinatewise. -/
theorem ougPres_pmap_apply {G G' H H' : OUG.{u}ᵒᵖ} (f : G ⟶ G') (g : H ⟶ H')
    (p : (ougPres.P G' H').unop.carrier) :
    (ougPres.pmap f g).unop.toAddHom p
      = (f.unop.toAddHom p.1, g.unop.toAddHom p.2) := by
  refine Prod.ext ?_ ?_
  · exact ougop_comp_apply f _ p
  · exact ougop_comp_apply g _ p

/-! ### The left pushout square of 180I in `OUG` -/

section OUGMed1

variable {G H K : OUG.{u}}

/-- The mediating morphism `γ(x, y) = β(x, 0) + α(0, y)` of the first
pushout square of 180I, for order unit groups. -/
def ougMed1 (α : ougScal.{u}.prod H ⟶ K) (β : G.prod ougScal.{u} ⟶ K)
    (hc : ∀ z w : ULift.{u} ℤ,
      α.toAddHom (z, w.down • H.unit) = β.toAddHom (z.down • G.unit, w)) :
    G.prod H ⟶ K where
  toAddHom :=
    (β.toAddHom.comp ((AddMonoidHom.inl G.carrier (ULift.{u} ℤ)).comp
        (AddMonoidHom.fst G.carrier H.carrier)))
      + (α.toAddHom.comp ((AddMonoidHom.inr (ULift.{u} ℤ) H.carrier).comp
        (AddMonoidHom.snd G.carrier H.carrier)))
  map_nonneg' p hp := by
    show (0 : K.carrier) ≤ β.toAddHom (p.1, 0) + α.toAddHom (0, p.2)
    have h1 : (0 : G.carrier × ULift.{u} ℤ) ≤ (p.1, 0) :=
      Prod.le_def.mpr ⟨(Prod.le_def.mp hp).1, le_refl _⟩
    have h2 : (0 : ULift.{u} ℤ × H.carrier) ≤ (0, p.2) :=
      Prod.le_def.mpr ⟨le_refl _, (Prod.le_def.mp hp).2⟩
    exact add_nonneg (β.map_nonneg' _ h1) (α.map_nonneg' _ h2)
  map_unit' := by
    show β.toAddHom (G.unit, (0 : ULift.{u} ℤ))
      + α.toAddHom ((0 : ULift.{u} ℤ), H.unit) = K.unit
    have h1 : α.toAddHom ((1 : ULift.{u} ℤ), (0 : H.carrier))
        = β.toAddHom (G.unit, (0 : ULift.{u} ℤ)) := by
      have h := hc 1 0
      simpa using h
    have h2 : ((1 : ULift.{u} ℤ), (0 : H.carrier))
        + ((0 : ULift.{u} ℤ), H.unit) = ((1 : ULift.{u} ℤ), H.unit) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [← h1, ← map_add, h2]
    exact α.map_unit'

/-- The defining equation of `ougMed1`. -/
@[simp] theorem ougMed1_apply (α : ougScal.{u}.prod H ⟶ K)
    (β : G.prod ougScal.{u} ⟶ K) (hc) (p : G.carrier × H.carrier) :
    (ougMed1 α β hc).toAddHom p
      = β.toAddHom (p.1, 0) + α.toAddHom (0, p.2) := rfl

variable (α : ougScal.{u}.prod H ⟶ K) (β : G.prod ougScal.{u} ⟶ K)
  (hc : ∀ z w : ULift.{u} ℤ,
    α.toAddHom (z, w.down • H.unit) = β.toAddHom (z.down • G.unit, w))

/-- `γ ∘ (u × id) = α`. -/
theorem ougMed1_fac_left (y : ULift.{u} ℤ × H.carrier) :
    (ougMed1 α β hc).toAddHom (y.1.down • G.unit, y.2) = α.toAddHom y := by
  show β.toAddHom (y.1.down • G.unit, 0) + α.toAddHom (0, y.2)
    = α.toAddHom y
  have h1 : α.toAddHom (y.1, (0 : H.carrier))
      = β.toAddHom (y.1.down • G.unit, (0 : ULift.{u} ℤ)) := by
    have h := hc y.1 0
    simpa using h
  have h3 : ((y.1, (0 : H.carrier)) : ULift.{u} ℤ × H.carrier)
      + (((0 : ULift.{u} ℤ), y.2) : ULift.{u} ℤ × H.carrier) = y := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [← h1, ← map_add, h3]

/-- `γ ∘ (id × u) = β`. -/
theorem ougMed1_fac_right (y : G.carrier × ULift.{u} ℤ) :
    (ougMed1 α β hc).toAddHom (y.1, y.2.down • H.unit) = β.toAddHom y := by
  show β.toAddHom (y.1, 0) + α.toAddHom (0, y.2.down • H.unit)
    = β.toAddHom y
  have h1 : α.toAddHom ((0 : ULift.{u} ℤ), y.2.down • H.unit)
      = β.toAddHom ((0 : G.carrier), y.2) := by
    have h := hc 0 y.2
    simpa using h
  have h3 : ((y.1, (0 : ULift.{u} ℤ)) : G.carrier × ULift.{u} ℤ)
      + (((0 : G.carrier), y.2) : G.carrier × ULift.{u} ℤ) = y := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [h1, ← map_add, h3]

/-- `γ` is the only morphism with those two properties. -/
theorem ougMed1_uniq (m : G.prod H ⟶ K)
    (h₁ : ∀ y : ULift.{u} ℤ × H.carrier,
      m.toAddHom (y.1.down • G.unit, y.2) = α.toAddHom y)
    (h₂ : ∀ y : G.carrier × ULift.{u} ℤ,
      m.toAddHom (y.1, y.2.down • H.unit) = β.toAddHom y) :
    m = ougMed1 α β hc := by
  refine oug_hom_ext fun p => ?_
  show m.toAddHom p = β.toAddHom (p.1, 0) + α.toAddHom (0, p.2)
  have e₁ : m.toAddHom ((p.1, (0 : H.carrier)) : G.carrier × H.carrier)
      = β.toAddHom (p.1, 0) := by
    have h := h₂ ((p.1, (0 : ULift.{u} ℤ)) : G.carrier × ULift.{u} ℤ)
    simpa using h
  have e₂ : m.toAddHom (((0 : G.carrier), p.2) : G.carrier × H.carrier)
      = α.toAddHom (0, p.2) := by
    have h := h₁ (((0 : ULift.{u} ℤ), p.2) : ULift.{u} ℤ × H.carrier)
    simpa using h
  have h3 : ((p.1, (0 : H.carrier)) : G.carrier × H.carrier)
      + (((0 : G.carrier), p.2) : G.carrier × H.carrier) = p := by
    refine Prod.ext ?_ ?_ <;> simp
  have h4 : m.toAddHom p
      = m.toAddHom ((p.1, (0 : H.carrier)) : G.carrier × H.carrier)
        + m.toAddHom (((0 : G.carrier), p.2) : G.carrier × H.carrier) := by
    rw [← map_add, h3]
  rw [h4, e₁, e₂]

end OUGMed1

/-- `id × u : ℤ × ℤ ⟶ ℤ × H`. -/
def ougSq1f (H : OUG.{u}) : ougScal.{u}.prod ougScal.{u} ⟶ ougScal.{u}.prod H :=
  ougProdMap (𝟙 ougScal.{u}) (ougUnitMap H)

/-- `u × id : ℤ × ℤ ⟶ G × ℤ`. -/
def ougSq1g (G : OUG.{u}) : ougScal.{u}.prod ougScal.{u} ⟶ G.prod ougScal.{u} :=
  ougProdMap (ougUnitMap G) (𝟙 ougScal.{u})

/-- `u × id : ℤ × H ⟶ G × H`. -/
def ougSq1h (G H : OUG.{u}) : ougScal.{u}.prod H ⟶ G.prod H :=
  ougProdMap (ougUnitMap G) (𝟙 H)

/-- `id × u : G × ℤ ⟶ G × H`. -/
def ougSq1i (G H : OUG.{u}) : G.prod ougScal.{u} ⟶ G.prod H :=
  ougProdMap (𝟙 G) (ougUnitMap H)

/-- The defining equation of `ougSq1f`. -/
@[simp] theorem ougSq1f_apply (H : OUG.{u}) (p : ULift.{u} ℤ × ULift.{u} ℤ) :
    (ougSq1f H).toAddHom p = (p.1, p.2.down • H.unit) := rfl

/-- The defining equation of `ougSq1g`. -/
@[simp] theorem ougSq1g_apply (G : OUG.{u}) (p : ULift.{u} ℤ × ULift.{u} ℤ) :
    (ougSq1g G).toAddHom p = (p.1.down • G.unit, p.2) := rfl

/-- The defining equation of `ougSq1h`. -/
@[simp] theorem ougSq1h_apply (G H : OUG.{u}) (p : ULift.{u} ℤ × H.carrier) :
    (ougSq1h G H).toAddHom p = (p.1.down • G.unit, p.2) := rfl

/-- The defining equation of `ougSq1i`. -/
@[simp] theorem ougSq1i_apply (G H : OUG.{u}) (p : G.carrier × ULift.{u} ℤ) :
    (ougSq1i G H).toAddHom p = (p.1, p.2.down • H.unit) := rfl

/-- **The left pullback square of 180I in `OUGᵒᵖ`** — the same square as
for `OUSᵒᵖ`, glued by `γ(x, y) = β(x, 0) + α(0, y)`. -/
theorem oug_isPushout1 (G H : OUG.{u}) :
    IsPushout (ougSq1f H) (ougSq1g G) (ougSq1h G H) (ougSq1i G H) := by
  have w : ougSq1f H ≫ ougSq1h G H = ougSq1g G ≫ ougSq1i G H :=
    oug_hom_ext fun p =>
      (oug_comp_apply _ _ p).trans (oug_comp_apply _ _ p).symm
  have hcond : ∀ s : PushoutCocone (ougSq1f H) (ougSq1g G),
      ∀ z w : ULift.{u} ℤ,
      s.inl.toAddHom (z, w.down • H.unit)
        = s.inr.toAddHom (z.down • G.unit, w) := by
    intro s z w
    exact ((oug_comp_apply (ougSq1f H) s.inl (z, w)).symm.trans
      (oug_congr s.condition (z, w))).trans
      (oug_comp_apply (ougSq1g G) s.inr (z, w))
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s => ougMed1 s.inl s.inr (hcond s)) ?_ ?_ ?_)
  · intro s
    exact oug_hom_ext fun y =>
      (oug_comp_apply (ougSq1h G H) _ y).trans
        (ougMed1_fac_left _ _ (hcond s) y)
  · intro s
    exact oug_hom_ext fun y =>
      (oug_comp_apply (ougSq1i G H) _ y).trans
        (ougMed1_fac_right _ _ (hcond s) y)
  · intro s m h₁ h₂
    refine ougMed1_uniq _ _ (hcond s) m (fun y => ?_) (fun y => ?_)
    · exact (oug_comp_apply (ougSq1h G H) m y).symm.trans (oug_congr h₁ y)
    · exact (oug_comp_apply (ougSq1i G H) m y).symm.trans (oug_congr h₂ y)

/-! ### The right pushout square of 180I in `OUG` -/

/-- **A positive homomorphism on a product killing `(0, 1)` kills
`0 × H`**, by the order-unit axiom `c ≤ n • 1` and
`oug_eq_sub_of_nonneg`. -/
theorem oug_prod_apply_eq_zero {G H K : OUG.{u}} (α : G.prod H ⟶ K)
    (h1 : α.toAddHom ((0 : G.carrier), H.unit) = 0) (b : H.carrier) :
    α.toAddHom ((0 : G.carrier), b) = 0 := by
  have hnn : ∀ c : H.carrier, 0 ≤ c → α.toAddHom ((0 : G.carrier), c) = 0 := by
    intro c hc
    obtain ⟨n, hn⟩ := oug_exists_le_nsmul_unit c
    have hle : (((0 : G.carrier), c) : G.carrier × H.carrier)
        ≤ ((0 : G.carrier), n • H.unit) := Prod.le_def.mpr ⟨le_refl _, hn⟩
    have h0 : (0 : G.carrier × H.carrier)
        ≤ (((0 : G.carrier), c) : G.carrier × H.carrier) :=
      Prod.le_def.mpr ⟨le_refl _, hc⟩
    have hsm : (((0 : G.carrier), n • H.unit) : G.carrier × H.carrier)
        = n • (((0 : G.carrier), H.unit) : G.carrier × H.carrier) := by
      refine Prod.ext ?_ ?_ <;> simp
    have hz : α.toAddHom ((0 : G.carrier), n • H.unit) = 0 := by
      rw [hsm, map_nsmul, h1, smul_zero]
    refine le_antisymm ?_ ?_
    · rw [← hz]; exact α.mono hle
    · have hp := α.mono h0
      rwa [map_zero] at hp
  obtain ⟨p, q, hp, hq, hb⟩ := oug_eq_sub_of_nonneg b
  have hsplit : (((0 : G.carrier), b) : G.carrier × H.carrier)
      = (((0 : G.carrier), p) : G.carrier × H.carrier)
        - (((0 : G.carrier), q) : G.carrier × H.carrier) := by
    rw [hb]
    refine Prod.ext ?_ ?_ <;> simp
  rw [hsplit, map_sub, hnn p hp, hnn q hq, sub_zero]

section OUGMed2

variable {G H K : OUG.{u}}

/-- The mediating morphism `γ(x) = α(x, 0)` of the second pushout
square. -/
def ougMed2 (α : G.prod H ⟶ K) (β : ougScal.{u} ⟶ K)
    (hc : ∀ z w : ULift.{u} ℤ,
      α.toAddHom (z.down • G.unit, w.down • H.unit) = β.toAddHom z) :
    G ⟶ K where
  toAddHom := α.toAddHom.comp (AddMonoidHom.inl G.carrier H.carrier)
  map_nonneg' x hx := α.map_nonneg' _ (Prod.le_def.mpr ⟨hx, le_refl _⟩)
  map_unit' := by
    show α.toAddHom (G.unit, (0 : H.carrier)) = K.unit
    have h01 : α.toAddHom ((0 : G.carrier), H.unit) = 0 := by
      have h := hc 0 1
      rw [show β.toAddHom (0 : ULift.{u} ℤ) = 0 from map_zero _] at h
      simpa using h
    have h3 : ((G.unit, (0 : H.carrier)) : G.carrier × H.carrier)
        + (((0 : G.carrier), H.unit) : G.carrier × H.carrier)
        = (G.prod H).unit := by
      refine Prod.ext ?_ ?_ <;> simp
    have h4 : α.toAddHom (G.unit, (0 : H.carrier))
        + α.toAddHom ((0 : G.carrier), H.unit) = K.unit := by
      rw [← map_add, h3]
      exact α.map_unit'
    rwa [h01, add_zero] at h4

/-- The defining equation of `ougMed2`. -/
@[simp] theorem ougMed2_apply (α : G.prod H ⟶ K) (β : ougScal.{u} ⟶ K) (hc)
    (x : G.carrier) :
    (ougMed2 α β hc).toAddHom x = α.toAddHom (x, 0) := rfl

variable (α : G.prod H ⟶ K) (β : ougScal.{u} ⟶ K)
  (hc : ∀ z w : ULift.{u} ℤ,
    α.toAddHom (z.down • G.unit, w.down • H.unit) = β.toAddHom z)

/-- `γ ∘ π₁ = α`. -/
theorem ougMed2_fac_left (p : G.carrier × H.carrier) :
    (ougMed2 α β hc).toAddHom p.1 = α.toAddHom p := by
  show α.toAddHom (p.1, 0) = α.toAddHom p
  have h01 : α.toAddHom ((0 : G.carrier), H.unit) = 0 := by
    have h := hc 0 1
    rw [show β.toAddHom (0 : ULift.{u} ℤ) = 0 from map_zero _] at h
    simpa using h
  have h3 : ((p.1, (0 : H.carrier)) : G.carrier × H.carrier)
      + (((0 : G.carrier), p.2) : G.carrier × H.carrier) = p := by
    refine Prod.ext ?_ ?_ <;> simp
  have h4 : α.toAddHom p
      = α.toAddHom (p.1, (0 : H.carrier))
        + α.toAddHom ((0 : G.carrier), p.2) := by
    rw [← map_add, h3]
  rw [h4, oug_prod_apply_eq_zero α h01 p.2, add_zero]

/-- `γ ∘ u = β`. -/
theorem ougMed2_fac_right (z : ULift.{u} ℤ) :
    (ougMed2 α β hc).toAddHom (z.down • G.unit) = β.toAddHom z := by
  show α.toAddHom (z.down • G.unit, 0) = β.toAddHom z
  have h := hc z 0
  simpa using h

/-- `γ` is the only morphism with that property. -/
theorem ougMed2_uniq (m : G ⟶ K)
    (h₁ : ∀ p : G.carrier × H.carrier, m.toAddHom p.1 = α.toAddHom p) :
    m = ougMed2 α β hc := by
  refine oug_hom_ext fun x => ?_
  show m.toAddHom x = α.toAddHom (x, 0)
  exact h₁ ((x, (0 : H.carrier)) : G.carrier × H.carrier)

end OUGMed2

/-- `u × u : ℤ × ℤ ⟶ G × H`. -/
def ougSq2f (G H : OUG.{u}) : ougScal.{u}.prod ougScal.{u} ⟶ G.prod H :=
  ougProdMap (ougUnitMap G) (ougUnitMap H)

/-- `π₁ : ℤ × ℤ ⟶ ℤ`. -/
def ougSq2g : ougScal.{u}.prod ougScal.{u} ⟶ ougScal.{u} :=
  ougFst ougScal.{u} ougScal.{u}

/-- `π₁ : G × H ⟶ G`. -/
def ougSq2h (G H : OUG.{u}) : G.prod H ⟶ G := ougFst G H

/-- `u : ℤ ⟶ G`. -/
def ougSq2i (G : OUG.{u}) : ougScal.{u} ⟶ G := ougUnitMap G

/-- **The right pullback square of 180I in `OUGᵒᵖ`**, with mediating map
`γ(x) = α(x, 0)`. -/
theorem oug_isPushout2 (G H : OUG.{u}) :
    IsPushout (ougSq2f G H) ougSq2g.{u} (ougSq2h G H) (ougSq2i G) := by
  have w : ougSq2f G H ≫ ougSq2h G H = ougSq2g.{u} ≫ ougSq2i G :=
    oug_hom_ext fun p =>
      (oug_comp_apply _ _ p).trans (oug_comp_apply _ _ p).symm
  have hcond : ∀ s : PushoutCocone (ougSq2f G H) ougSq2g.{u},
      ∀ z w : ULift.{u} ℤ,
      s.inl.toAddHom (z.down • G.unit, w.down • H.unit)
        = s.inr.toAddHom z := by
    intro s z w
    exact ((oug_comp_apply (ougSq2f G H) s.inl (z, w)).symm.trans
      (oug_congr s.condition (z, w))).trans
      (oug_comp_apply ougSq2g.{u} s.inr (z, w))
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s => ougMed2 s.inl s.inr (hcond s)) ?_ ?_ ?_)
  · intro s
    exact oug_hom_ext fun p =>
      (oug_comp_apply (ougSq2h G H) _ p).trans
        (ougMed2_fac_left _ _ (hcond s) p)
  · intro s
    exact oug_hom_ext fun z =>
      (oug_comp_apply (ougSq2i G) _ z).trans
        (ougMed2_fac_right _ _ (hcond s) z)
  · intro s m h₁ _
    exact ougMed2_uniq _ _ (hcond s) m
      (fun p => (oug_comp_apply (ougSq2h G H) m p).symm.trans (oug_congr h₁ p))

/-! ### Joint monicity of the two cotuples in `OUGᵒᵖ` -/

/-- **The third axiom of 180I in `OUGᵒᵖ`**: a positive unit-preserving
homomorphism out of `ℤ³` is determined by its restrictions along
`(x,y) ↦ (x,y,y)` and `(x,y) ↦ (y,x,y)`, because `ℤ³` is free abelian on
the three coordinate units. -/
theorem oug_jointlyMonic_aux {K : OUG.{u}}
    (a b : (ougScal.{u}.prod ougScal.{u}).prod ougScal.{u} ⟶ K)
    (h1 : ∀ x : ULift.{u} ℤ × ULift.{u} ℤ,
      a.toAddHom ((x.1, x.2), x.2) = b.toAddHom ((x.1, x.2), x.2))
    (h2 : ∀ x : ULift.{u} ℤ × ULift.{u} ℤ,
      a.toAddHom ((x.2, x.1), x.2) = b.toAddHom ((x.2, x.1), x.2)) :
    a = b := by
  set e₁ : (ULift.{u} ℤ × ULift.{u} ℤ) × ULift.{u} ℤ := ((1, 0), 0) with he₁
  set e₂ : (ULift.{u} ℤ × ULift.{u} ℤ) × ULift.{u} ℤ := ((0, 1), 0) with he₂
  set e₃ : (ULift.{u} ℤ × ULift.{u} ℤ) × ULift.{u} ℤ := ((0, 0), 1) with he₃
  have ha1 : a.toAddHom e₁ = b.toAddHom e₁ := h1 (1, 0)
  have ha2 : a.toAddHom e₂ = b.toAddHom e₂ := h2 (1, 0)
  have ha3 : a.toAddHom e₃ = b.toAddHom e₃ := by
    have h4 := h1 (0, 1)
    have hsum : (((0 : ULift.{u} ℤ), (1 : ULift.{u} ℤ)), (1 : ULift.{u} ℤ))
        = e₂ + e₃ := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [he₂, he₃]
    rw [hsum, map_add, map_add, ha2] at h4
    exact add_left_cancel h4
  have key : ∀ (f : (ougScal.{u}.prod ougScal.{u}).prod ougScal.{u} ⟶ K)
      (y : (ULift.{u} ℤ × ULift.{u} ℤ) × ULift.{u} ℤ),
      f.toAddHom y = y.1.1.down • f.toAddHom e₁
        + (y.1.2.down • f.toAddHom e₂ + y.2.down • f.toAddHom e₃) := by
    intro f y
    have hdec : y = y.1.1.down • e₁ + (y.1.2.down • e₂ + y.2.down • e₃) := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;>
        · apply ULift.down_injective
          simp [he₁, he₂, he₃]
    conv_lhs => rw [hdec]
    rw [map_add, map_zsmul, map_add, map_zsmul, map_zsmul]
  refine oug_hom_ext fun y => ?_
  rw [key a y, key b y, ha1, ha2, ha3]

/-! ### `OUGᵒᵖ` is an effectus -/

instance ougOpHasTerminal : HasTerminal (OUG.{u}ᵒᵖ) := ougPres.hT.hasTerminal

/-- The zero group is the initial object of `OUGᵒᵖ`. -/
instance ougOpHasInitial : HasInitial (OUG.{u}ᵒᵖ) :=
  (IsTerminal.op (OUG.{u}) ougTrivIsTerminal).hasInitial

/-- Binary coproducts of `OUGᵒᵖ` are the products of `OUG`. -/
instance ougOpHasColimitPair (G H : OUG.{u}ᵒᵖ) : HasColimit (pair G H) :=
  HasColimit.mk ⟨_, ougPres.hP G H⟩

/-- `OUGᵒᵖ` has binary coproducts. -/
instance ougOpHasBinaryCoproducts : HasBinaryCoproducts (OUG.{u}ᵒᵖ) :=
  hasBinaryCoproducts_of_hasColimit_pair _

/-- `OUGᵒᵖ` has finite coproducts. -/
instance ougOpHasFiniteCoproducts : HasFiniteCoproducts (OUG.{u}ᵒᵖ) :=
  hasFiniteCoproducts_of_has_binary_and_initial

/-- **189aII.2** (`effexamplesintro`, eff.tex:2037, Examples): the three
axioms of 180I for `OUGᵒᵖ`, as an instance; `effectus_oug` bundles it. -/
instance effectusTotalForm_oug : EffectusTotalForm OUG.{u}ᵒᵖ := by
  refine effectusTotalForm_of_pres ougPres ?_ ?_ ?_
  · intro G H
    have e₁ : ougPres.pmap (𝟙 G) (ougPres.hT.from H)
        = Quiver.Hom.op (ougSq1i G.unop H.unop) := by
      refine ougop_hom_ext fun p => (ougPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext rfl ?_
      exact ougPres_from_apply H p.2
    have e₂ : ougPres.pmap (ougPres.hT.from G) (𝟙 H)
        = Quiver.Hom.op (ougSq1h G.unop H.unop) := by
      refine ougop_hom_ext fun p => (ougPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ rfl
      exact ougPres_from_apply G p.1
    have e₃ : ougPres.pmap (ougPres.hT.from G) (𝟙 ougPres.T)
        = Quiver.Hom.op (ougSq1g G.unop) := by
      refine ougop_hom_ext fun p => (ougPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ rfl
      exact ougPres_from_apply G p.1
    have e₄ : ougPres.pmap (𝟙 ougPres.T) (ougPres.hT.from H)
        = Quiver.Hom.op (ougSq1f H.unop) := by
      refine ougop_hom_ext fun p => (ougPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext rfl ?_
      exact ougPres_from_apply H p.2
    rw [e₁, e₂, e₃, e₄]
    exact (oug_isPushout1 G.unop H.unop).op
  · intro G H
    have f₁ : ougPres.hT.from G = Quiver.Hom.op (ougSq2i G.unop) :=
      ougPres.hT.hom_ext _ _
    have f₄ : ougPres.pmap (ougPres.hT.from G) (ougPres.hT.from H)
        = Quiver.Hom.op (ougSq2f G.unop H.unop) := by
      refine ougop_hom_ext fun p => (ougPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ ?_
      · exact ougPres_from_apply G p.1
      · exact ougPres_from_apply H p.2
    rw [f₄, f₁]
    exact (oug_isPushout2 G.unop H.unop).op
  · intro Z a b hf hg
    apply Quiver.Hom.unop_inj
    refine oug_jointlyMonic_aux a.unop b.unop (fun x => ?_) (fun x => ?_)
    · exact ougop_comp_congr hf x
    · exact ougop_comp_congr hg x

/-- **189aII.2** (`effexamplesintro`, eff.tex:2037, Examples): the
category `OUGᵒᵖ` of order unit groups with positive unit-preserving
homomorphisms in the opposite direction is an effectus in total form.

The point gives no proof.  Ours is the argument of `effectus_ous` with the
ordered real vector space replaced by a partially ordered abelian group:
`ℤ` is initial in `OUG`, the products are the coproducts of `OUGᵒᵖ`
(`ougPres`), and the three axioms of 180I are `oug_isPushout1`,
`oug_isPushout2` and `oug_jointlyMonic_aux`.  No scalar action is used
anywhere; the order-unit axiom does the work the norm did for von Neumann
algebras.  That argument is the instance `effectusTotalForm_oug` above (it
is needed as an instance by the `Pred`, `Stat` and `Scal` of 190IV.2); this
theorem only bundles it. -/
theorem effectus_oug : Nonempty (EffectusTotalStructure OUG.{u}ᵒᵖ) :=
  ⟨{ hasFiniteCoproducts := inferInstance
     hasTerminal := inferInstance
     effectus := inferInstance }⟩

/-! ## Predicates, states and scalars (190IV.1 and 190IV.2) -/

open Opposite

/-! ## Predicates of `Par C` from a two-point presentation of `⊤ + ⊤` -/

section OUParPred

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasTerminal C]
variable {S : C} {i₁ i₂ : (⊤_ C) ⟶ S}

/-- The comparison isomorphism `⊤ + ⊤ ≅ S`. -/
def ouGamma (hS : IsColimit (BinaryCofan.mk i₁ i₂)) : ((⊤_ C) ⨿ (⊤_ C)) ≅ S :=
  IsColimit.coconePointUniqueUpToIso (coprodIsCoprod (⊤_ C) (⊤_ C)) hS

/-- The first coprojection of `⊤ + ⊤`, transported to `S`. -/
theorem ouGamma_inl (hS : IsColimit (BinaryCofan.mk i₁ i₂)) :
    (coprod.inl : (⊤_ C) ⟶ _) ≫ (ouGamma hS).hom = i₁ :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod (⊤_ C) (⊤_ C)) hS
    (Discrete.mk WalkingPair.left)

/-- The second coprojection of `⊤ + ⊤`, transported to `S`. -/
theorem ouGamma_inr (hS : IsColimit (BinaryCofan.mk i₁ i₂)) :
    (coprod.inr : (⊤_ C) ⟶ _) ≫ (ouGamma hS).hom = i₂ :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod (⊤_ C) (⊤_ C)) hS
    (Discrete.mk WalkingPair.right)

variable [EffectusTotalForm C]

/-- The orthosupplement `[κ₂,κ₁]` of `Par C`, transported to `S`. -/
theorem ouSwapTop_ouGamma (hS : IsColimit (BinaryCofan.mk i₁ i₂)) (sw : S ⟶ S)
    (h₁ : i₁ ≫ sw = i₂) (h₂ : i₂ ≫ sw = i₁) :
    (parSwapTop : (⊤_ C) ⨿ (⊤_ C) ⟶ _) ≫ (ouGamma hS).hom
      = (ouGamma hS).hom ≫ sw := by
  refine coprod.hom_ext ?_ ?_
  · rw [parSwapTop_eq, ← Category.assoc, coprod.inl_desc, ouGamma_inr,
      ← Category.assoc, ouGamma_inl, h₁]
  · rw [parSwapTop_eq, ← Category.assoc, coprod.inr_desc, ouGamma_inl,
      ← Category.assoc, ouGamma_inr, h₂]

variable [HasFiniteCoproducts (Par C)]

/-- `Pred (Par.of X) = C(X, ⊤ + ⊤) ≃ C(X, S)`. -/
def ouPredEquiv (hS : IsColimit (BinaryCofan.mk i₁ i₂)) (X : C) :
    Pred (Par.of X) ≃ (X ⟶ S) where
  toFun p := pval p ≫ (ouGamma hS).hom
  invFun q := show Pred (Par.of X) from
    (q ≫ (ouGamma hS).inv : X ⟶ (⊤_ C) ⨿ (⊤_ C))
  left_inv p := by
    refine pval_inj ?_
    show (pval p ≫ (ouGamma hS).hom) ≫ (ouGamma hS).inv = pval p
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv q := by
    show (q ≫ (ouGamma hS).inv) ≫ (ouGamma hS).hom = q
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Under `ouPredEquiv` the truth predicate `1` is the constant `i₁`. -/
theorem ouPredEquiv_truth (hS : IsColimit (BinaryCofan.mk i₁ i₂)) (X : C) :
    ouPredEquiv hS X (truth (Par.of X)) = terminal.from X ≫ i₁ := by
  show (terminal.from X ≫ coprod.inl) ≫ (ouGamma hS).hom = _
  rw [Category.assoc, ouGamma_inl]

/-- Under `ouPredEquiv` the zero predicate `0` is the constant `i₂`. -/
theorem ouPredEquiv_zero (hS : IsColimit (BinaryCofan.mk i₁ i₂)) (X : C) :
    ouPredEquiv hS X (0 : Pred (Par.of X)) = terminal.from X ≫ i₂ := by
  have h : pval (0 : Pred (Par.of X)) = terminal.from X ≫ coprod.inr := by
    rw [par_zero_eq' (Par.of X) (Par.of (⊤_ C)), pval_zero]
    rfl
  show pval (0 : Pred (Par.of X)) ≫ (ouGamma hS).hom = _
  rw [h, Category.assoc, ouGamma_inr]

/-- Under `ouPredEquiv` the orthosupplement `p^⊥` is `sw ∘ p`, for the
involution `sw` of `S` swapping the two points. -/
theorem ouPredEquiv_orth (hS : IsColimit (BinaryCofan.mk i₁ i₂)) (sw : S ⟶ S)
    (h₁ : i₁ ≫ sw = i₂) (h₂ : i₂ ≫ sw = i₁) (X : C) (p : Pred (Par.of X)) :
    ouPredEquiv hS X (orth p) = ouPredEquiv hS X p ≫ sw := by
  show pval (parOrth p) ≫ (ouGamma hS).hom = (pval p ≫ (ouGamma hS).hom) ≫ sw
  rw [pval_parOrth, Category.assoc, ouSwapTop_ouGamma hS sw h₁ h₂,
    ← Category.assoc]

end OUParPred

/-! ## The concrete two-point presentation of `⊤ + ⊤` in `OUSᵒᵖ` -/

section OUSExample

local instance instHasFiniteCoproductsParOUS :
    HasFiniteCoproducts (Par OUS.{u}ᵒᵖ) := parHasFiniteCoproducts

/-- The final object of `OUSᵒᵖ`, read as an order unit space. -/
abbrev ousTopO : OUS.{u} := (⊤_ OUS.{u}ᵒᵖ).unop

/-- The unique map out of `ousTopO` (it is initial in `OUS`). -/
def ousTopTo (X : OUS.{u}) : ousTopO.{u} ⟶ X := (terminal.from (op X)).unop

/-- `ousTopO` is initial in `OUS`: there is at most one map out of it. -/
theorem ousTopO_hom_unique {X : OUS.{u}} (f g : ousTopO.{u} ⟶ X) : f = g :=
  Quiver.Hom.op_inj (terminalIsTerminal.hom_ext (C := OUS.{u}ᵒᵖ) f.op g.op)

/-- The unique map `ℝᵤ ⟶ ousTopO`. -/
def ousUnitTop : ousScal.{u} ⟶ ousTopO.{u} := ousUnitMap ousTopO.{u}

/-- `ℝᵤ ⟶ ousTopO ⟶ ℝᵤ` is the identity. -/
theorem ousTop_inv₁ : ousUnitTop.{u} ≫ ousTopTo ousScal.{u} = 𝟙 ousScal.{u} :=
  (ousUnitMap_unique _).trans (ousUnitMap_unique _).symm

/-- `ousTopO ⟶ ℝᵤ ⟶ ousTopO` is the identity. -/
theorem ousTop_inv₂ : ousTopTo ousScal.{u} ≫ ousUnitTop.{u} = 𝟙 ousTopO.{u} :=
  ousTopO_hom_unique _ _

/-- The first component of a pairing. -/
theorem ousPair_fst {Z X Y : OUS.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) :
    ousPair f g ≫ ousFst X Y = f := ous_hom_ext fun _ => rfl

/-- The second component of a pairing. -/
theorem ousPair_snd {Z X Y : OUS.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) :
    ousPair f g ≫ ousSnd X Y = g := ous_hom_ext fun _ => rfl

/-- A map into a product is the pairing of its two components. -/
theorem ousPair_eta {Z X Y : OUS.{u}} (m : Z ⟶ X.prod Y) :
    ousPair (m ≫ ousFst X Y) (m ≫ ousSnd X Y) = m :=
  ous_hom_ext fun _ => rfl

/-- `ℝ² = ℝᵤ × ℝᵤ`: the apex of the two-point presentation of `⊤ + ⊤`. -/
abbrev ousS : OUS.{u}ᵒᵖ := op (ousScal.{u}.prod ousScal.{u})

/-- The first point of `⊤ + ⊤`, i.e. the first projection `ℝ² ⟶ ℝ`. -/
def ousI₁ : (⊤_ OUS.{u}ᵒᵖ) ⟶ ousS.{u} :=
  Quiver.Hom.op (ousFst ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u})

/-- The second point of `⊤ + ⊤`, i.e. the second projection `ℝ² ⟶ ℝ`. -/
def ousI₂ : (⊤_ OUS.{u}ᵒᵖ) ⟶ ousS.{u} :=
  Quiver.Hom.op (ousSnd ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u})

/-- The swap of `ℝ²`, which will be the orthosupplement. -/
def ousSwap : ousS.{u} ⟶ ousS.{u} :=
  Quiver.Hom.op (ousPair (ousSnd ousScal.{u} ousScal.{u})
    (ousFst ousScal.{u} ousScal.{u}))

/-- `⊤ + ⊤` in `OUSᵒᵖ` is `ℝ²`. -/
def ousTopCofan : IsColimit (BinaryCofan.mk ousI₁.{u} ousI₂.{u}) :=
  BinaryCofan.IsColimit.mk _
    (fun {_} u v => Quiver.Hom.op
      (ousPair (u.unop ≫ ousTopTo ousScal.{u}) (v.unop ≫ ousTopTo ousScal.{u})))
    (fun {_} u v => by
      refine Quiver.Hom.unop_inj ?_
      show ousPair (u.unop ≫ ousTopTo ousScal.{u}) (v.unop ≫ ousTopTo ousScal.{u})
          ≫ (ousFst _ _ ≫ ousUnitTop.{u}) = u.unop
      rw [← Category.assoc, ousPair_fst, Category.assoc, ousTop_inv₂,
        Category.comp_id])
    (fun {_} u v => by
      refine Quiver.Hom.unop_inj ?_
      show ousPair (u.unop ≫ ousTopTo ousScal.{u}) (v.unop ≫ ousTopTo ousScal.{u})
          ≫ (ousSnd _ _ ≫ ousUnitTop.{u}) = v.unop
      rw [← Category.assoc, ousPair_snd, Category.assoc, ousTop_inv₂,
        Category.comp_id])
    (fun {W} u v m h₁ h₂ => by
      obtain ⟨m, rfl⟩ : ∃ m' : ousS.{u} ⟶ W, m' = m := ⟨m, rfl⟩
      refine Quiver.Hom.unop_inj ?_
      have k₁ : m.unop ≫ (ousFst ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u})
          = u.unop := congrArg Quiver.Hom.unop h₁
      have k₂ : m.unop ≫ (ousSnd ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u})
          = v.unop := congrArg Quiver.Hom.unop h₂
      have e₁ : m.unop ≫ ousFst ousScal.{u} ousScal.{u}
          = u.unop ≫ ousTopTo ousScal.{u} := by
        rw [← k₁, Category.assoc, Category.assoc, ousTop_inv₁, Category.comp_id]
      have e₂ : m.unop ≫ ousSnd ousScal.{u} ousScal.{u}
          = v.unop ≫ ousTopTo ousScal.{u} := by
        rw [← k₂, Category.assoc, Category.assoc, ousTop_inv₁, Category.comp_id]
      rw [← e₁, ← e₂, ousPair_eta]
      rfl)

/-- The swap of `ℝ²` exchanges the two points of `⊤ + ⊤`. -/
theorem ousI₁_swap : ousI₁.{u} ≫ ousSwap.{u} = ousI₂.{u} := by
  refine Quiver.Hom.unop_inj ?_
  show ousPair (ousSnd ousScal.{u} ousScal.{u}) (ousFst ousScal.{u} ousScal.{u})
      ≫ (ousFst _ _ ≫ ousUnitTop.{u}) = ousSnd _ _ ≫ ousUnitTop.{u}
  rw [← Category.assoc, ousPair_fst]

/-- The swap of `ℝ²` exchanges the two points of `⊤ + ⊤`. -/
theorem ousI₂_swap : ousI₂.{u} ≫ ousSwap.{u} = ousI₁.{u} := by
  refine Quiver.Hom.unop_inj ?_
  show ousPair (ousSnd ousScal.{u} ousScal.{u}) (ousFst ousScal.{u} ousScal.{u})
      ≫ (ousSnd _ _ ≫ ousUnitTop.{u}) = ousFst _ _ ≫ ousUnitTop.{u}
  rw [← Category.assoc, ousPair_snd]

/-! ## Positive unital maps out of `ℝ²` are the effects -/

theorem ous_one_zero_nonneg :
    (0 : ULift.{u} ℝ × ULift.{u} ℝ) ≤ ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ)) :=
  Prod.le_def.mpr ⟨show (0:ℝ) ≤ 1 from zero_le_one, le_refl _⟩

/-- `(0,1)` is a positive element of `ℝ²`. -/
theorem ous_zero_one_nonneg :
    (0 : ULift.{u} ℝ × ULift.{u} ℝ) ≤ ((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)) :=
  Prod.le_def.mpr ⟨le_refl _, show (0:ℝ) ≤ 1 from zero_le_one⟩

/-- Positive unital maps `ℝ² ⟶ X` of `OUS` are the effects `0 ≤ x ≤ 1`
of `X`, by `φ ↦ φ(1,0)`. -/
def ousHomEffectEquiv (X : OUS.{u}) :
    (ousScal.{u}.prod ousScal.{u} ⟶ X) ≃ {x : X.carrier // 0 ≤ x ∧ x ≤ X.unit} where
  toFun φ := ⟨φ.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ)), by
    refine ⟨φ.map_nonneg' _ ous_one_zero_nonneg.{u}, ?_⟩
    have h : ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))
        ≤ (ousScal.{u}.prod ousScal.{u}).unit :=
      Prod.le_def.mpr ⟨le_refl _, show (0:ℝ) ≤ 1 from zero_le_one⟩
    exact (φ.mono h).trans (le_of_eq φ.map_unit')⟩
  invFun x :=
    { toLinearMap :=
        { toFun := fun p => p.1.down • x.1 + p.2.down • (X.unit - x.1)
          map_add' := fun a b => by
            show (a.1.down + b.1.down) • x.1 + (a.2.down + b.2.down) • (X.unit - x.1)
              = (a.1.down • x.1 + a.2.down • (X.unit - x.1))
                + (b.1.down • x.1 + b.2.down • (X.unit - x.1))
            rw [add_smul, add_smul]
            abel
          map_smul' := fun r a => by
            show (r * a.1.down) • x.1 + (r * a.2.down) • (X.unit - x.1)
              = r • (a.1.down • x.1 + a.2.down • (X.unit - x.1))
            rw [mul_smul, mul_smul, smul_add] }
      map_nonneg' := fun p hp => by
        obtain ⟨hp1, hp2⟩ := Prod.le_def.mp hp
        have h1 : (0:ℝ) ≤ p.1.down := hp1
        have h2 : (0:ℝ) ≤ p.2.down := hp2
        show (0 : X.carrier) ≤ p.1.down • x.1 + p.2.down • (X.unit - x.1)
        have e1 : (0 : X.carrier) ≤ p.1.down • x.1 := ou_smul_nonneg h1 x.2.1
        have e2 : (0 : X.carrier) ≤ p.2.down • (X.unit - x.1) :=
          ou_smul_nonneg h2 (sub_nonneg.mpr x.2.2)
        simpa using add_le_add e1 e2
      map_unit' := by
        show (1:ℝ) • x.1 + (1:ℝ) • (X.unit - x.1) = X.unit
        rw [one_smul, one_smul]
        abel }
  left_inv φ := by
    refine ous_hom_ext fun p => ?_
    have hsum : φ.toLinearMap ((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ))
        = X.unit - φ.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ)) := by
      have h : ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ)) + ((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ))
          = (ousScal.{u}.prod ousScal.{u}).unit := by
        refine Prod.ext ?_ ?_ <;> apply ULift.down_injective <;> simp
      have h2 : φ.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))
          + φ.toLinearMap ((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)) = X.unit := by
        rw [← map_add, h, φ.map_unit']
      rw [← h2]; abel
    have hdec : p = p.1.down • ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))
        + p.2.down • ((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)) := by
      refine Prod.ext ?_ ?_ <;> apply ULift.down_injective <;> simp
    show p.1.down • φ.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))
      + p.2.down • (X.unit - φ.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ)))
      = φ.toLinearMap p
    rw [← hsum]
    conv_rhs => rw [hdec]
    rw [map_add, map_smul, map_smul]
  right_inv x := by
    refine Subtype.ext ?_
    show (1:ℝ) • x.1 + (0:ℝ) • (X.unit - x.1) = x.1
    rw [one_smul, zero_smul, add_zero]

/-- A positive unital map out of `ℝ²` sends `(0,1)` to `1 - φ(1,0)`. -/
theorem ous_hom_compl (X : OUS.{u}) (φ : ousScal.{u}.prod ousScal.{u} ⟶ X) :
    φ.toLinearMap ((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ))
      = X.unit - φ.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ)) := by
  have h : ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ)) + ((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ))
      = (ousScal.{u}.prod ousScal.{u}).unit := by
    refine Prod.ext ?_ ?_ <;> apply ULift.down_injective <;> simp
  have h2 : φ.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))
      + φ.toLinearMap ((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)) = X.unit := by
    rw [← map_add, h, φ.map_unit']
  rw [← h2]; abel

/-- Passing to the opposite category. -/
def ousOpEquiv (X : OUS.{u}) :
    ((op X : OUS.{u}ᵒᵖ) ⟶ ousS.{u}) ≃ (ousScal.{u}.prod ousScal.{u} ⟶ X) where
  toFun f := f.unop
  invFun g := Quiver.Hom.op g
  left_inv _ := rfl
  right_inv _ := rfl

/-- **190IV.1** (eff.tex:2153, Examples): the **predicates on an order unit
space `X` correspond to the points `x ∈ X` with `0 ≤ x ≤ 1`**, where `1` is
the distinguished order unit.

The correspondence is pinned by the three lemmas below: `1` is the order
unit, `0` is `0`, and `p^⊥` is `1 - p`. -/
def ous_pred_effect (X : OUS.{u}) :
    Pred (Par.of (op X)) ≃ {x : X.carrier // 0 ≤ x ∧ x ≤ X.unit} :=
  ((ouPredEquiv ousTopCofan.{u} (op X)).trans (ousOpEquiv X)).trans
    (ousHomEffectEquiv X)

/-- The effect attached to a predicate is the image of `(1,0)`. -/
theorem ous_pred_effect_val (X : OUS.{u}) (p : Pred (Par.of (op X))) :
    ((ous_pred_effect X p).1 : X.carrier)
      = (ouPredEquiv ousTopCofan.{u} (op X) p).unop.toLinearMap
          ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ)) := rfl

/-- The composite `ℝ² ⟶ ⊤ ⟶ X` through the first point is `r ↦ r · 1`
precomposed with the first projection. -/
theorem ous_from_i₁ (X : OUS.{u}) :
    terminal.from (op X) ≫ ousI₁.{u}
      = Quiver.Hom.op (ousFst ousScal.{u} ousScal.{u} ≫ ousUnitMap X) := by
  refine Quiver.Hom.unop_inj ?_
  show (ousFst ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u}) ≫ ousTopTo X
      = ousFst ousScal.{u} ousScal.{u} ≫ ousUnitMap X
  rw [Category.assoc]
  exact congrArg (fun m => ousFst ousScal.{u} ousScal.{u} ≫ m)
    (ousUnitMap_unique (ousUnitTop.{u} ≫ ousTopTo X))

/-- The composite `ℝ² ⟶ ⊤ ⟶ X` through the second point is `r ↦ r · 1`
precomposed with the second projection. -/
theorem ous_from_i₂ (X : OUS.{u}) :
    terminal.from (op X) ≫ ousI₂.{u}
      = Quiver.Hom.op (ousSnd ousScal.{u} ousScal.{u} ≫ ousUnitMap X) := by
  refine Quiver.Hom.unop_inj ?_
  show (ousSnd ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u}) ≫ ousTopTo X
      = ousSnd ousScal.{u} ousScal.{u} ≫ ousUnitMap X
  rw [Category.assoc]
  exact congrArg (fun m => ousSnd ousScal.{u} ousScal.{u} ≫ m)
    (ousUnitMap_unique (ousUnitTop.{u} ≫ ousTopTo X))

/-- **190IV.1** (eff.tex:2154, Examples): the truth predicate is the order
unit. -/
theorem ous_pred_effect_truth (X : OUS.{u}) :
    ((ous_pred_effect X (truth (Par.of (op X)))).1 : X.carrier) = X.unit := by
  rw [ous_pred_effect_val, ouPredEquiv_truth, ous_from_i₁]
  show (ousUnitMap X).toLinearMap (1 : ULift.{u} ℝ) = X.unit
  rw [ousUnitMap_apply]
  exact one_smul _ _

/-- **190IV.1** (eff.tex:2154, Examples): the zero predicate is `0`. -/
theorem ous_pred_effect_zero (X : OUS.{u}) :
    ((ous_pred_effect X (0 : Pred (Par.of (op X)))).1 : X.carrier) = 0 := by
  rw [ous_pred_effect_val, ouPredEquiv_zero, ous_from_i₂]
  show (ousUnitMap X).toLinearMap (0 : ULift.{u} ℝ) = 0
  rw [ousUnitMap_apply]
  exact zero_smul _ _

/-- **190IV.1** (eff.tex:2154, Examples): the orthosupplement is `1 - x`. -/
theorem ous_pred_effect_orth (X : OUS.{u}) (p : Pred (Par.of (op X))) :
    ((ous_pred_effect X (orth p)).1 : X.carrier)
      = X.unit - ((ous_pred_effect X p).1 : X.carrier) := by
  rw [ous_pred_effect_val, ous_pred_effect_val,
    ouPredEquiv_orth ousTopCofan.{u} ousSwap.{u} ousI₁_swap.{u} ousI₂_swap.{u}
      (op X) p]
  rw [← ous_hom_compl X (ouPredEquiv ousTopCofan.{u} (op X) p).unop]
  rfl

/-! ## The states of an order unit space -/

/-- Maps `X ⟶ ℝᵤ` of `OUS` are the positive unital linear functionals. -/
def ousHomStateEquiv (X : OUS.{u}) :
    (X ⟶ ousScal.{u})
      ≃ {f : X.carrier →ₗ[ℝ] ℝ // (∀ x, 0 ≤ x → 0 ≤ f x) ∧ f X.unit = 1} where
  toFun φ :=
    ⟨{ toFun := fun x => (φ.toLinearMap x).down
       map_add' := fun x y => congrArg ULift.down (map_add φ.toLinearMap x y)
       map_smul' := fun r x => congrArg ULift.down (map_smul φ.toLinearMap r x) },
     fun x hx => φ.map_nonneg' x hx, congrArg ULift.down φ.map_unit'⟩
  invFun f :=
    { toLinearMap :=
        { toFun := fun x => ULift.up (f.1 x)
          map_add' := fun x y => congrArg ULift.up (map_add f.1 x y)
          map_smul' := fun r x => congrArg ULift.up (map_smul f.1 r x) }
      map_nonneg' := fun x hx => f.2.1 x hx
      map_unit' := ULift.down_injective f.2.2 }
  left_inv _ := ous_hom_ext fun _ => rfl
  right_inv _ := Subtype.ext (LinearMap.ext fun _ => rfl)

/-- `ousTopO ≅ ℝᵤ`, as a bijection on maps into it. -/
def ousHomTopEquiv (X : OUS.{u}) : (X ⟶ ousTopO.{u}) ≃ (X ⟶ ousScal.{u}) where
  toFun f := f ≫ ousTopTo ousScal.{u}
  invFun g := g ≫ ousUnitTop.{u}
  left_inv f := by
    show (f ≫ ousTopTo ousScal.{u}) ≫ ousUnitTop.{u} = f
    rw [Category.assoc, ousTop_inv₂, Category.comp_id]
  right_inv g := by
    show (g ≫ ousUnitTop.{u}) ≫ ousTopTo ousScal.{u} = g
    rw [Category.assoc, ousTop_inv₁, Category.comp_id]

/-- **190IV.1** (eff.tex:2156, Examples): the **states of an order unit space
`X` are exactly what are called states for order unit spaces in the
literature**: the positive unit-preserving linear functionals `X → ℝ`. -/
def ous_stat_state (X : OUS.{u}) :
    Stat (Par.of (op X))
      ≃ {f : X.carrier →ₗ[ℝ] ℝ // (∀ x, 0 ≤ x → 0 ≤ f x) ∧ f X.unit = 1} :=
  ((parStatEquiv (op X)).trans
    { toFun := fun f => f.unop
      invFun := fun g => Quiver.Hom.op g
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
    ((ousHomTopEquiv X).trans (ousHomStateEquiv X))

/-! ## `OUSᵒᵖ` has separating predicates -/

/-- The first coprojection `X ⟶ X + 1` of `OUSᵒᵖ`, concretely. -/
def ousKap₁ (X : OUS.{u}ᵒᵖ) : X ⟶ op (X.unop.prod ousScal.{u}) :=
  Quiver.Hom.op (ousFst X.unop ousScal.{u})

/-- The second coprojection `1 ⟶ X + 1` of `OUSᵒᵖ`, concretely. -/
def ousKap₂ (X : OUS.{u}ᵒᵖ) : (⊤_ OUS.{u}ᵒᵖ) ⟶ op (X.unop.prod ousScal.{u}) :=
  Quiver.Hom.op (ousSnd X.unop ousScal.{u} ≫ ousUnitTop.{u})

/-- `X + 1` in `OUSᵒᵖ` is `X × ℝ`. -/
def ousPlusCofan (X : OUS.{u}ᵒᵖ) :
    IsColimit (BinaryCofan.mk (ousKap₁ X) (ousKap₂ X)) :=
  BinaryCofan.IsColimit.mk _
    (fun {_} u v => Quiver.Hom.op
      (ousPair u.unop (v.unop ≫ ousTopTo ousScal.{u})))
    (fun {_} _ _ => Quiver.Hom.unop_inj (ousPair_fst _ _))
    (fun {_} u v => by
      refine Quiver.Hom.unop_inj ?_
      show ousPair u.unop (v.unop ≫ ousTopTo ousScal.{u})
          ≫ (ousSnd X.unop ousScal.{u} ≫ ousUnitTop.{u}) = v.unop
      rw [← Category.assoc, ousPair_snd, Category.assoc, ousTop_inv₂,
        Category.comp_id])
    (fun {W} u v m h₁ h₂ => by
      obtain ⟨m, rfl⟩ :
          ∃ m' : (op (X.unop.prod ousScal.{u}) : OUS.{u}ᵒᵖ) ⟶ W, m' = m := ⟨m, rfl⟩
      refine Quiver.Hom.unop_inj ?_
      have k₁ : m.unop ≫ ousFst X.unop ousScal.{u} = u.unop :=
        congrArg Quiver.Hom.unop h₁
      have k₂ : m.unop ≫ (ousSnd X.unop ousScal.{u} ≫ ousUnitTop.{u}) = v.unop :=
        congrArg Quiver.Hom.unop h₂
      have e₂ : m.unop ≫ ousSnd X.unop ousScal.{u}
          = v.unop ≫ ousTopTo ousScal.{u} := by
        rw [← k₂, Category.assoc, Category.assoc, ousTop_inv₁, Category.comp_id]
      rw [← k₁, ← e₂, ousPair_eta]
      rfl)

/-- The comparison isomorphism `X + 1 ≅ X × ℝ` of `OUSᵒᵖ`. -/
def ousEps (X : OUS.{u}ᵒᵖ) :
    (X ⨿ (⊤_ OUS.{u}ᵒᵖ)) ≅ op (X.unop.prod ousScal.{u}) :=
  IsColimit.coconePointUniqueUpToIso (coprodIsCoprod X (⊤_ OUS.{u}ᵒᵖ))
    (ousPlusCofan X)

/-- The first coprojection under the comparison isomorphism `X + 1 ≅ X × ℝ`. -/
theorem ousEps_inl (X : OUS.{u}ᵒᵖ) :
    (coprod.inl : X ⟶ X ⨿ (⊤_ OUS.{u}ᵒᵖ)) ≫ (ousEps X).hom = ousKap₁ X :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod X (⊤_ OUS.{u}ᵒᵖ))
    (ousPlusCofan X) (Discrete.mk WalkingPair.left)

/-- The second coprojection under the comparison isomorphism `X + 1 ≅ X × ℝ`. -/
theorem ousEps_inr (X : OUS.{u}ᵒᵖ) :
    (coprod.inr : (⊤_ OUS.{u}ᵒᵖ) ⟶ X ⨿ (⊤_ OUS.{u}ᵒᵖ)) ≫ (ousEps X).hom
      = ousKap₂ X :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod X (⊤_ OUS.{u}ᵒᵖ))
    (ousPlusCofan X) (Discrete.mk WalkingPair.right)

/-- **190IV.1** (eff.tex:2149, Examples): `OUSᵒᵖ` has **separating
predicates**.

A map `Par.of Y ⟶ Par.of X` of `Par OUSᵒᵖ` is a positive unital linear map
`F : X × ℝ ⟶ Y`, and composing with the predicate `x` is precomposition with
`(a,b) ↦ (a·x + b·(1-x), b)`.  Since every element of `X` is a real multiple
of an effect (`ou_eq_sub_of_nonneg` and `ou_exists_le_smul_unit`, then divide
by `n+1`), and the last coordinate is pinned by unitality, the effects
determine `F`. -/
theorem ous_separating_predicates : SeparatingPredicates (Par OUS.{u}ᵒᵖ) := by
  intro Y X f g h
  refine pval_inj ?_
  refine (cancel_mono (ousEps X.base).hom).mp ?_
  refine ousop_hom_ext fun w => ?_
  -- the two concrete positive unital maps `X × ℝ ⟶ Y`
  have key : ∀ (x : X.base.unop.carrier) (hx : 0 ≤ x ∧ x ≤ X.base.unop.unit)
      (a b : ULift.{u} ℝ),
      (pval f ≫ (ousEps X.base).hom).unop.toLinearMap
          (a.down • x + b.down • (X.base.unop.unit - x), b)
        = (pval g ≫ (ousEps X.base).hom).unop.toLinearMap
          (a.down • x + b.down • (X.base.unop.unit - x), b) := by
    intro x hx a b
    set q : X.base ⟶ ousS.{u} :=
      Quiver.Hom.op ((ousHomEffectEquiv X.base.unop).symm ⟨x, hx⟩) with hqdef
    set p : Pred X := (ouPredEquiv ousTopCofan.{u} X.base).symm q with hpdef
    have hq : ouPredEquiv ousTopCofan.{u} X.base p = q :=
      (ouPredEquiv ousTopCofan.{u} X.base).apply_symm_apply q
    set Ψ : (op (X.base.unop.prod ousScal.{u}) : OUS.{u}ᵒᵖ) ⟶ ousS.{u} :=
      Quiver.Hom.op (ousPair q.unop (ousSnd ousScal.{u} ousScal.{u})) with hΨdef
    have hk₁ : ousKap₁ X.base ≫ Ψ = q := Quiver.Hom.unop_inj (ousPair_fst _ _)
    have hk₂ : ousKap₂ X.base ≫ Ψ = ousI₂.{u} := by
      refine Quiver.Hom.unop_inj ?_
      show ousPair q.unop (ousSnd ousScal.{u} ousScal.{u})
          ≫ (ousSnd X.base.unop ousScal.{u} ≫ ousUnitTop.{u})
        = ousSnd ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u}
      rw [← Category.assoc, ousPair_snd]
    have hdesc : coprod.desc (pval p)
          (coprod.inr : (⊤_ OUS.{u}ᵒᵖ) ⟶ (⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ))
          ≫ (ouGamma ousTopCofan.{u}).hom
        = (ousEps X.base).hom ≫ Ψ := by
      refine coprod.hom_ext ?_ ?_
      · rw [← Category.assoc, coprod.inl_desc, ← Category.assoc, ousEps_inl, hk₁]
        exact hq
      · rw [← Category.assoc, coprod.inr_desc, ouGamma_inr, ← Category.assoc,
          ousEps_inr, hk₂]
    have hp' : pval f ≫ coprod.desc (pval p)
          (coprod.inr : (⊤_ OUS.{u}ᵒᵖ) ⟶ (⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ))
        = pval g ≫ coprod.desc (pval p) coprod.inr := congrArg pval (h p)
    have hfg : (pval f ≫ (ousEps X.base).hom) ≫ Ψ
        = (pval g ≫ (ousEps X.base).hom) ≫ Ψ := by
      rw [Category.assoc, Category.assoc, ← hdesc, ← Category.assoc,
        ← Category.assoc, hp']
      rfl
    have happ := ousop_congr hfg ((a : ULift.{u} ℝ), (b : ULift.{u} ℝ))
    rw [ousop_comp_apply, ousop_comp_apply] at happ
    exact happ
  -- every element of `X` is a real multiple of a difference of two effects
  have stepA : ∀ (x : X.base.unop.carrier), 0 ≤ x ∧ x ≤ X.base.unop.unit →
      ∀ a : ℝ,
      (pval f ≫ (ousEps X.base).hom).unop.toLinearMap
          ((a • x : X.base.unop.carrier), (0 : ULift.{u} ℝ))
        = (pval g ≫ (ousEps X.base).hom).unop.toLinearMap
          ((a • x : X.base.unop.carrier), (0 : ULift.{u} ℝ)) := by
    intro x hx a
    have h0 := key x hx (ULift.up a) (0 : ULift.{u} ℝ)
    have hz : (0 : ULift.{u} ℝ).down • (X.base.unop.unit - x) = 0 := zero_smul _ _
    rw [hz, add_zero] at h0
    exact h0
  have stepB : ∀ z : X.base.unop.carrier, 0 ≤ z →
      (pval f ≫ (ousEps X.base).hom).unop.toLinearMap (z, (0 : ULift.{u} ℝ))
        = (pval g ≫ (ousEps X.base).hom).unop.toLinearMap
            (z, (0 : ULift.{u} ℝ)) := by
    intro z hz
    obtain ⟨n, hn⟩ := ou_exists_le_smul_unit z
    have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hmne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hm
    have hinv : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := le_of_lt (inv_pos.mpr hm)
    have hle : z ≤ ((n : ℝ) + 1) • X.base.unop.unit :=
      hn.trans (ou_smul_unit_mono (by linarith))
    have hx0 : (0 : X.base.unop.carrier) ≤ ((n : ℝ) + 1)⁻¹ • z :=
      ou_smul_nonneg hinv hz
    have hx1 : ((n : ℝ) + 1)⁻¹ • z ≤ X.base.unop.unit := by
      have h1 := ou_smul_le_smul hinv hle
      rwa [smul_smul, inv_mul_cancel₀ hmne, one_smul] at h1
    have hback : ((n : ℝ) + 1) • (((n : ℝ) + 1)⁻¹ • z) = z := by
      rw [smul_smul, mul_inv_cancel₀ hmne, one_smul]
    have := stepA (((n : ℝ) + 1)⁻¹ • z) ⟨hx0, hx1⟩ ((n : ℝ) + 1)
    rwa [hback] at this
  have stepC : ∀ z : X.base.unop.carrier,
      (pval f ≫ (ousEps X.base).hom).unop.toLinearMap (z, (0 : ULift.{u} ℝ))
        = (pval g ≫ (ousEps X.base).hom).unop.toLinearMap
            (z, (0 : ULift.{u} ℝ)) := by
    intro z
    obtain ⟨a, b, ha, hb, hz⟩ := ou_eq_sub_of_nonneg z
    have hsub : ((z : X.base.unop.carrier), (0 : ULift.{u} ℝ))
        = (a, (0 : ULift.{u} ℝ)) - (b, (0 : ULift.{u} ℝ)) := by
      refine Prod.ext ?_ ?_
      · exact hz
      · exact (sub_zero (0 : ULift.{u} ℝ)).symm
    rw [hsub, map_sub, map_sub, stepB a ha, stepB b hb]
  -- and the last coordinate is pinned by unitality
  obtain ⟨z, c⟩ := w
  have hdec : ((z : X.base.unop.carrier), (c : ULift.{u} ℝ))
      = ((z - c.down • X.base.unop.unit : X.base.unop.carrier), (0 : ULift.{u} ℝ))
        + c.down • (X.base.unop.prod ousScal.{u}).unit := by
    refine Prod.ext ?_ ?_
    · show z = (z - c.down • X.base.unop.unit) + c.down • X.base.unop.unit
      abel
    · apply ULift.down_injective
      show c.down = 0 + c.down * 1
      rw [mul_one, zero_add]
  rw [hdec, map_add, map_add, map_smul, map_smul, stepC,
    (pval f ≫ (ousEps X.base).hom).unop.map_unit',
    (pval g ≫ (ousEps X.base).hom).unop.map_unit']

/-! ## The lexicographic plane: `OUSᵒᵖ` has no separating states -/

/-- The **lexicographic plane**: `ℝ²` with the positive cone
`{(a,b) : 0 < a} ∪ {(0,b) : 0 ≤ b}` and order unit `(1,0)`.  A plain `def`,
not an `abbrev`, so that instance search does not reach `ULift`'s own
(coordinatewise) order. -/
def ousLex : Type u := ULift.{u} (ℝ × ℝ)

instance : AddCommGroup ousLex.{u} :=
  inferInstanceAs (AddCommGroup (ULift.{u} (ℝ × ℝ)))

instance : Module ℝ ousLex.{u} :=
  inferInstanceAs (Module ℝ (ULift.{u} (ℝ × ℝ)))

/-- A point of the lexicographic plane. -/
def ousLexPt (a b : ℝ) : ousLex.{u} := ULift.up (a, b)

/-- The coordinates of a point of the lexicographic plane. -/
def ousLexDown (x : ousLex.{u}) : ℝ × ℝ := ULift.down x

@[simp] theorem ousLexDown_pt (a b : ℝ) : ousLexDown (ousLexPt.{u} a b) = (a, b) := rfl

/-- Points of the lexicographic plane are determined by their coordinates. -/
theorem ousLexDown_injective {x y : ousLex.{u}} (h : ousLexDown x = ousLexDown y) :
    x = y := ULift.down_injective h

/-- Addition in the lexicographic plane is coordinatewise. -/
theorem ousLexDown_add (x y : ousLex.{u}) :
    ousLexDown (x + y) = ousLexDown x + ousLexDown y := rfl

/-- Scalar multiplication in the lexicographic plane is coordinatewise. -/
theorem ousLexDown_smul (r : ℝ) (x : ousLex.{u}) :
    ousLexDown (r • x) = r • ousLexDown x := rfl

/-- The zero of the lexicographic plane. -/
theorem ousLexDown_zero : ousLexDown (0 : ousLex.{u}) = (0, 0) := rfl

/-- The lexicographic order on `ℝ²`. -/
instance ousLexPartialOrder : PartialOrder ousLex.{u} where
  le x y := (ousLexDown x).1 < (ousLexDown y).1 ∨
    ((ousLexDown x).1 = (ousLexDown y).1 ∧ (ousLexDown x).2 ≤ (ousLexDown y).2)
  le_refl _ := Or.inr ⟨rfl, le_refl _⟩
  le_trans x y z hxy hyz := by
    rcases hxy with h1 | ⟨h1, h1'⟩
    · rcases hyz with h2 | ⟨h2, _⟩
      · exact Or.inl (lt_trans h1 h2)
      · exact Or.inl (h2 ▸ h1)
    · rcases hyz with h2 | ⟨h2, h2'⟩
      · exact Or.inl (h1 ▸ h2)
      · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩
  le_antisymm x y hxy hyx := by
    refine ousLexDown_injective (Prod.ext ?_ ?_)
    · rcases hxy with h1 | ⟨h1, _⟩
      · rcases hyx with h2 | ⟨h2, _⟩
        · exact absurd (lt_trans h1 h2) (lt_irrefl _)
        · exact absurd h1 (by rw [h2]; exact lt_irrefl _)
      · exact h1
    · rcases hxy with h1 | ⟨h1, h1'⟩
      · rcases hyx with h2 | ⟨h2, _⟩
        · exact absurd (lt_trans h1 h2) (lt_irrefl _)
        · exact absurd h1 (by rw [h2]; exact lt_irrefl _)
      · rcases hyx with h2 | ⟨_, h2'⟩
        · exact absurd h2 (by rw [h1]; exact lt_irrefl _)
        · exact le_antisymm h1' h2'

/-- The lexicographic order, unfolded. -/
theorem ousLex_le_iff (x y : ousLex.{u}) :
    x ≤ y ↔ (ousLexDown x).1 < (ousLexDown y).1 ∨
      ((ousLexDown x).1 = (ousLexDown y).1 ∧ (ousLexDown x).2 ≤ (ousLexDown y).2) :=
  Iff.rfl

/-- The lexicographic plane is an order unit space: the cone is closed under
non-negative scalars, and `(a,b) ≤ n • (1,0)` for any `n > a`.  It is **not**
archimedean: `(0,1) ≤ ε • (1,0)` for every `ε > 0`, yet `(0,1) ≰ 0`. -/
instance ousLexOrderUnitSpace : OrderUnitSpace ousLex.{u} where
  add_le_add_left x y h z := by
    rcases h with h1 | ⟨h1, h1'⟩
    · refine Or.inl ?_
      show (ousLexDown x).1 + (ousLexDown z).1 < (ousLexDown y).1 + (ousLexDown z).1
      linarith
    · refine Or.inr ⟨?_, ?_⟩
      · show (ousLexDown x).1 + (ousLexDown z).1 = (ousLexDown y).1 + (ousLexDown z).1
        rw [h1]
      · show (ousLexDown x).2 + (ousLexDown z).2 ≤ (ousLexDown y).2 + (ousLexDown z).2
        linarith
  smul_nonneg {r} {x} hr hx := by
    rcases eq_or_lt_of_le hr with hr0 | hr0
    · refine Or.inr ⟨?_, ?_⟩
      · show (0 : ℝ) = r * (ousLexDown x).1
        rw [← hr0, zero_mul]
      · show (0 : ℝ) ≤ r * (ousLexDown x).2
        rw [← hr0, zero_mul]
    · rcases hx with h1 | ⟨h1, h1'⟩
      · refine Or.inl ?_
        show (0 : ℝ) < r * (ousLexDown x).1
        have h2 : (0 : ℝ) < (ousLexDown x).1 := h1
        exact mul_pos hr0 h2
      · refine Or.inr ⟨?_, ?_⟩
        · show (0 : ℝ) = r * (ousLexDown x).1
          have h2 : (0 : ℝ) = (ousLexDown x).1 := h1
          rw [← h2, mul_zero]
        · show (0 : ℝ) ≤ r * (ousLexDown x).2
          have h2 : (0 : ℝ) ≤ (ousLexDown x).2 := h1'
          exact mul_nonneg (le_of_lt hr0) h2
  unit := ousLexPt 1 0
  exists_le_smul_unit x := by
    refine ⟨⌈(ousLexDown x).1⌉₊ + 1, Or.inl ?_⟩
    show (ousLexDown x).1 < ((⌈(ousLexDown x).1⌉₊ + 1 : ℕ) : ℝ) * 1
    have h := Nat.le_ceil (ousLexDown x).1
    push_cast
    linarith

/-- The order unit of the lexicographic plane is `(1,0)`. -/
theorem ousLex_unit : ouUnit ousLex.{u} = ousLexPt 1 0 := rfl

/-- The lexicographic plane, as an object of `OUS`. -/
abbrev ousLexObj : OUS.{u} := OUS.of ousLex.{u}

/-- `(0,1)` is an effect of the lexicographic plane. -/
theorem ousLex_e_nonneg : (0 : ousLex.{u}) ≤ ousLexPt 0 1 :=
  Or.inr ⟨rfl, by show (0 : ℝ) ≤ 1; norm_num⟩

/-- `(0,1)` is below the order unit `(1,0)` of the lexicographic plane. -/
theorem ousLex_e_le_unit : (ousLexPt 0 1 : ousLex.{u}) ≤ ouUnit ousLex.{u} :=
  Or.inl (by show (0 : ℝ) < 1; norm_num)

/-- `(0,1)` is not `0` in the lexicographic plane. -/
theorem ousLex_e_ne_zero : (ousLexPt 0 1 : ousLex.{u}) ≠ 0 := by
  intro hh
  have h2 : ((0 : ℝ), (1 : ℝ)) = (0, 0) := congrArg ousLexDown hh
  exact one_ne_zero (congrArg Prod.snd h2)

/-- **190IV.1** (eff.tex:2150, Examples): every state of the lexicographic
plane kills `(0,1)`.
Positivity of `(0,1)` gives `0 ≤ ψ(0,1)`, and positivity of `ε • (1,0) - (0,1)`
for every `ε > 0` gives `ψ(0,1) ≤ ε`. -/
theorem ousLex_state_apply (ψ : ousLexObj.{u} ⟶ ousScal.{u}) :
    ψ.toLinearMap (ousLexPt 0 1) = 0 := by
  set t : ℝ := (ψ.toLinearMap (ousLexPt.{u} 0 1)).down with ht
  have h0 : (0 : ℝ) ≤ t := ψ.map_nonneg' _ ousLex_e_nonneg.{u}
  have hup : ∀ ε : ℝ, 0 < ε → t ≤ ε := by
    intro ε hε
    have hpos : (0 : ousLex.{u}) ≤ ε • ousLexObj.{u}.unit - ousLexPt 0 1 := by
      refine Or.inl ?_
      show (0 : ℝ) < ε * 1 - 0
      linarith
    have h1 := ψ.map_nonneg' _ hpos
    rw [map_sub, map_smul, ψ.map_unit'] at h1
    have h2 : (0 : ℝ) ≤ ε * 1 - t := h1
    linarith
  have hle : t ≤ 0 := by
    by_contra hc
    have hc' : (0 : ℝ) < t := not_le.mp hc
    have h3 := hup (t / 2) (by linarith)
    linarith
  exact ULift.down_injective (le_antisymm hle h0)

/-- Two maps into `ousTopO` agreeing after the isomorphism `ousTopO ≅ ℝᵤ`
are equal. -/
theorem ous_hom_to_top_ext {Z : OUS.{u}} {a b : Z ⟶ ousTopO.{u}}
    (hab : a ≫ ousTopTo ousScal.{u} = b ≫ ousTopTo ousScal.{u}) : a = b := by
  calc a = a ≫ (ousTopTo ousScal.{u} ≫ ousUnitTop.{u}) := by
        rw [ousTop_inv₂, Category.comp_id]
    _ = (a ≫ ousTopTo ousScal.{u}) ≫ ousUnitTop.{u} := by rw [Category.assoc]
    _ = (b ≫ ousTopTo ousScal.{u}) ≫ ousUnitTop.{u} := by rw [hab]
    _ = b ≫ (ousTopTo ousScal.{u} ≫ ousUnitTop.{u}) := by rw [Category.assoc]
    _ = b := by rw [ousTop_inv₂, Category.comp_id]

/-- **190IV.1** (eff.tex:2150, Examples): `OUSᵒᵖ` does **not** have separating
states.  On the
lexicographic plane the effect `(0,1)` and the effect `0` are distinct
predicates, yet every state of the plane sends both to the scalar `0`. -/
theorem ous_no_separating_states : ¬ SeparatingStates (Par OUS.{u}ᵒᵖ) := by
  intro hsep
  set q : (op ousLexObj.{u} : OUS.{u}ᵒᵖ) ⟶ ousS.{u} :=
    Quiver.Hom.op ((ousHomEffectEquiv ousLexObj.{u}).symm
      ⟨ousLexPt 0 1, ousLex_e_nonneg.{u}, ousLex_e_le_unit.{u}⟩) with hqdef
  set p : Pred (Par.of (op ousLexObj.{u})) :=
    (ouPredEquiv ousTopCofan.{u} (op ousLexObj.{u})).symm q with hpdef
  have hq : ouPredEquiv ousTopCofan.{u} (op ousLexObj.{u}) p = q :=
    (ouPredEquiv ousTopCofan.{u} (op ousLexObj.{u})).apply_symm_apply q
  have hq' : pval p ≫ (ouGamma ousTopCofan.{u}).hom = q := hq
  have hstates : ∀ ω : Stat (Par.of (op ousLexObj.{u})),
      ω.1 ≫ p = ω.1 ≫ (0 : Pred (Par.of (op ousLexObj.{u}))) := by
    intro ω
    obtain ⟨w, hw⟩ := (par_isTotal_iff_hat ω.1).mp ω.2
    rw [hw]
    refine pval_inj ?_
    rw [par_hat_comp, par_hat_comp]
    have hzero : pval (0 : Pred (Par.of (op ousLexObj.{u})))
        = terminal.from (op ousLexObj.{u})
          ≫ (coprod.inr : (⊤_ OUS.{u}ᵒᵖ) ⟶ (⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ)) := by
      rw [par_zero_eq' (Par.of (op ousLexObj.{u})) (Par.of (⊤_ OUS.{u}ᵒᵖ)), pval_zero]
    have hterm : w ≫ terminal.from (op ousLexObj.{u}) = 𝟙 (⊤_ OUS.{u}ᵒᵖ) :=
      terminalIsTerminal.hom_ext _ _
    rw [hzero, ← Category.assoc, hterm, Category.id_comp]
    refine (cancel_mono (ouGamma ousTopCofan.{u}).hom).mp ?_
    rw [Category.assoc, ouGamma_inr, hq']
    refine Quiver.Hom.unop_inj ?_
    show q.unop ≫ w.unop = ousSnd ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u}
    refine ous_hom_to_top_ext ?_
    rw [Category.assoc, Category.assoc, ousTop_inv₁, Category.comp_id]
    refine ous_hom_ext fun ab => ?_
    show (w.unop ≫ ousTopTo ousScal.{u}).toLinearMap
        (ab.1.down • (ousLexPt 0 1 : ousLex.{u})
          + ab.2.down • (ousLexObj.{u}.unit - ousLexPt 0 1)) = ab.2
    set ψ : ousLexObj.{u} ⟶ ousScal.{u} := w.unop ≫ ousTopTo ousScal.{u} with hψ
    have he : ψ.toLinearMap (ousLexPt.{u} 0 1) = 0 := ousLex_state_apply ψ
    rw [map_add, map_smul, map_smul, map_sub, he, ψ.map_unit']
    show ab.1.down • (0 : ULift.{u} ℝ) + ab.2.down • ((1 : ULift.{u} ℝ) - 0) = ab.2
    rw [sub_zero, smul_zero, zero_add]
    apply ULift.down_injective
    show ab.2.down * 1 = ab.2.down
    rw [mul_one]
  have hpz : p = (0 : Pred (Par.of (op ousLexObj.{u}))) := hsep p 0 hstates
  have h1 := congrArg (fun r => ((ous_pred_effect ousLexObj.{u} r).1 : ousLex.{u})) hpz
  rw [ous_pred_effect_zero] at h1
  have h2 : ((ous_pred_effect ousLexObj.{u} p).1 : ousLex.{u}) = ousLexPt 0 1 := by
    rw [ous_pred_effect_val, hq]
    exact congrArg Subtype.val
      ((ousHomEffectEquiv ousLexObj.{u}).apply_symm_apply
        ⟨ousLexPt 0 1, ousLex_e_nonneg.{u}, ousLex_e_le_unit.{u}⟩)
  rw [h2] at h1
  exact ousLex_e_ne_zero.{u} h1

/-! ## The three-point presentation of `⊤ + ⊤ + ⊤`, and `⊥`, `⋁` on predicates -/

/-- `ℝ³`: the apex of the three-point presentation of `⊤ + ⊤ + ⊤`. -/
abbrev ousR : OUS.{u}ᵒᵖ := op ((ousScal.{u}.prod ousScal.{u}).prod ousScal.{u})

/-- `⊤ + ⊤ + ⊤ ≅ ℝ³`. -/
def ousDelta :
    ((((⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ)) ⨿ (⊤_ OUS.{u}ᵒᵖ))) ≅ ousR.{u} :=
  (coprod.mapIso (ouGamma ousTopCofan.{u}) (Iso.refl (⊤_ OUS.{u}ᵒᵖ))).trans
    (ousEps ousS.{u})

/-- The first coprojection under the comparison isomorphism `⊤+⊤+⊤ ≅ ℝ³`. -/
theorem ousDelta_inl :
    (coprod.inl : ((⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ)) ⟶ _) ≫ ousDelta.{u}.hom
      = (ouGamma ousTopCofan.{u}).hom ≫ ousKap₁ ousS.{u} := by
  show coprod.inl ≫ (coprod.map (ouGamma ousTopCofan.{u}).hom
      (Iso.refl (⊤_ OUS.{u}ᵒᵖ)).hom ≫ (ousEps ousS.{u}).hom) = _
  rw [← Category.assoc, coprod.inl_map, Category.assoc, ousEps_inl]

/-- The last coprojection under the comparison isomorphism `⊤+⊤+⊤ ≅ ℝ³`. -/
theorem ousDelta_inr :
    (coprod.inr : (⊤_ OUS.{u}ᵒᵖ) ⟶ _) ≫ ousDelta.{u}.hom = ousKap₂ ousS.{u} := by
  show coprod.inr ≫ (coprod.map (ouGamma ousTopCofan.{u}).hom
      (Iso.refl (⊤_ OUS.{u}ᵒᵖ)).hom ≫ (ousEps ousS.{u}).hom) = _
  rw [← Category.assoc, coprod.inr_map, Iso.refl_hom, Category.id_comp]
  exact ousEps_inr ousS.{u}

/-- `(a,b) ↦ ((a,b),b)`: the cotuple `[κ₁,κ₂,κ₂]` of 180I, on `ℝ³`. -/
def ousDl : ousR.{u} ⟶ ousS.{u} :=
  Quiver.Hom.op (ousPair (𝟙 (ousScal.{u}.prod ousScal.{u}))
    (ousSnd ousScal.{u} ousScal.{u}))

/-- `(a,b) ↦ ((b,a),b)`: the cotuple `[κ₂,κ₁,κ₂]` of 180I, on `ℝ³`. -/
def ousDr : ousR.{u} ⟶ ousS.{u} :=
  Quiver.Hom.op (ousPair (ousPair (ousSnd ousScal.{u} ousScal.{u})
    (ousFst ousScal.{u} ousScal.{u})) (ousSnd ousScal.{u} ousScal.{u}))

/-- `(a,b) ↦ ((a,a),b)`: the cotuple `[κ₁,κ₁,κ₂]`, which computes `⋁`. -/
def ousDv : ousR.{u} ⟶ ousS.{u} :=
  Quiver.Hom.op (ousPair (ousPair (ousFst ousScal.{u} ousScal.{u})
    (ousFst ousScal.{u} ousScal.{u})) (ousSnd ousScal.{u} ousScal.{u}))

private theorem ous_kap₂_D (D : (ousScal.{u}.prod ousScal.{u})
      ⟶ (ousScal.{u}.prod ousScal.{u}).prod ousScal.{u})
    (hD : D ≫ ousSnd (ousScal.{u}.prod ousScal.{u}) ousScal.{u}
      = ousSnd ousScal.{u} ousScal.{u}) :
    ousKap₂ ousS.{u} ≫ Quiver.Hom.op D = ousI₂.{u} := by
  refine Quiver.Hom.unop_inj ?_
  show D ≫ (ousSnd (ousScal.{u}.prod ousScal.{u}) ousScal.{u} ≫ ousUnitTop.{u})
    = ousSnd ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u}
  rw [← Category.assoc, hD]

/-- The cotuple `[κ₁,κ₂,κ₂]` of 180I, transported to `ℝ³ ⟶ ℝ²`. -/
theorem ous_Dl_eq :
    (coprod.desc (𝟙 ((⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ)))
        (coprod.inr : (⊤_ OUS.{u}ᵒᵖ) ⟶ _))
        ≫ (ouGamma ousTopCofan.{u}).hom
      = ousDelta.{u}.hom ≫ ousDl.{u} := by
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc, coprod.inl_desc, Category.id_comp, ← Category.assoc,
      ousDelta_inl, Category.assoc]
    have h : ousKap₁ ousS.{u} ≫ ousDl.{u} = 𝟙 ousS.{u} :=
      Quiver.Hom.unop_inj (ousPair_fst _ _)
    rw [h, Category.comp_id]
  · rw [← Category.assoc, coprod.inr_desc, ouGamma_inr, ← Category.assoc,
      ousDelta_inr]
    exact (ous_kap₂_D _ (ousPair_snd _ _)).symm

/-- The cotuple `[κ₂,κ₁,κ₂]` of 180I, transported to `ℝ³ ⟶ ℝ²`. -/
theorem ous_Dr_eq :
    (coprod.desc (parSwapTop : (⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ) ⟶ _)
        (coprod.inr : (⊤_ OUS.{u}ᵒᵖ) ⟶ _))
        ≫ (ouGamma ousTopCofan.{u}).hom
      = ousDelta.{u}.hom ≫ ousDr.{u} := by
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc, coprod.inl_desc,
      ouSwapTop_ouGamma ousTopCofan.{u} ousSwap.{u} ousI₁_swap.{u} ousI₂_swap.{u},
      ← Category.assoc, ousDelta_inl, Category.assoc]
    have h : ousKap₁ ousS.{u} ≫ ousDr.{u} = ousSwap.{u} :=
      Quiver.Hom.unop_inj (ousPair_fst _ _)
    rw [h]
  · rw [← Category.assoc, coprod.inr_desc, ouGamma_inr, ← Category.assoc,
      ousDelta_inr]
    exact (ous_kap₂_D _ (ousPair_snd _ _)).symm

/-- The codiagonal `∇ : ⊤ + ⊤ ⇸ ⊤` of `Par`, transported to `ℝ²`. -/
def ousV : ousS.{u} ⟶ ousS.{u} :=
  Quiver.Hom.op (ousPair (ousFst ousScal.{u} ousScal.{u})
    (ousFst ousScal.{u} ousScal.{u}))

/-- The codiagonal sends the first point of `⊤ + ⊤` to the first point. -/
theorem ousI₁_V : ousI₁.{u} ≫ ousV.{u} = ousI₁.{u} := by
  refine Quiver.Hom.unop_inj ?_
  show ousPair (ousFst ousScal.{u} ousScal.{u}) (ousFst ousScal.{u} ousScal.{u})
      ≫ (ousFst ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u})
    = ousFst ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u}
  rw [← Category.assoc, ousPair_fst]

/-- The codiagonal sends the second point of `⊤ + ⊤` to the first point. -/
theorem ousI₂_V : ousI₂.{u} ≫ ousV.{u} = ousI₁.{u} := by
  refine Quiver.Hom.unop_inj ?_
  show ousPair (ousFst ousScal.{u} ousScal.{u}) (ousFst ousScal.{u} ousScal.{u})
      ≫ (ousSnd ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u})
    = ousFst ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u}
  rw [← Category.assoc, ousPair_snd]

/-- The codiagonal `∇` of `Par`, transported along `⊤ + ⊤ ≅ ℝ²`. -/
theorem ous_nabla_gamma :
    pval (parNabla (⊤_ OUS.{u}ᵒᵖ)) ≫ (ouGamma ousTopCofan.{u}).hom
      = (ouGamma ousTopCofan.{u}).hom ≫ ousV.{u} := by
  have hn : pval (parNabla (⊤_ OUS.{u}ᵒᵖ))
      = coprod.desc (𝟙 (⊤_ OUS.{u}ᵒᵖ)) (𝟙 (⊤_ OUS.{u}ᵒᵖ))
        ≫ (coprod.inl : (⊤_ OUS.{u}ᵒᵖ) ⟶ _) := rfl
  have hnl : (coprod.inl : (⊤_ OUS.{u}ᵒᵖ) ⟶ _) ≫ pval (parNabla (⊤_ OUS.{u}ᵒᵖ))
      = coprod.inl := by
    rw [hn, ← Category.assoc, coprod.inl_desc, Category.id_comp]
  have hnr : (coprod.inr : (⊤_ OUS.{u}ᵒᵖ) ⟶ _) ≫ pval (parNabla (⊤_ OUS.{u}ᵒᵖ))
      = coprod.inl := by
    rw [hn, ← Category.assoc, coprod.inr_desc, Category.id_comp]
  refine coprod.hom_ext ?_ ?_
  · simp only [← Category.assoc]
    rw [hnl, ouGamma_inl, ousI₁_V]
  · simp only [← Category.assoc]
    rw [hnr, ouGamma_inl, ouGamma_inr, ousI₂_V]

/-- The cotuple `[κ₁,κ₁,κ₂]` computing `⋁`, transported to `ℝ³ ⟶ ℝ²`. -/
theorem ous_Dv_eq :
    (coprod.desc (pval (parNabla (⊤_ OUS.{u}ᵒᵖ)))
        (coprod.inr : (⊤_ OUS.{u}ᵒᵖ) ⟶ _))
        ≫ (ouGamma ousTopCofan.{u}).hom
      = ousDelta.{u}.hom ≫ ousDv.{u} := by
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc, coprod.inl_desc, ous_nabla_gamma, ← Category.assoc,
      ousDelta_inl, Category.assoc]
    have h : ousKap₁ ousS.{u} ≫ ousDv.{u} = ousV.{u} :=
      Quiver.Hom.unop_inj (ousPair_fst _ _)
    rw [h]
  · rw [← Category.assoc, coprod.inr_desc, ouGamma_inr, ← Category.assoc,
      ousDelta_inr]
    exact (ous_kap₂_D _ (ousPair_snd _ _)).symm

/-- The `ParBound` conditions of 187III, transported to `ℝ³`. -/
theorem ous_bound_iff {X : OUS.{u}ᵒᵖ} (p q : Pred (Par.of X))
    (b : Par.of X ⟶ Par.of ((⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ))) :
    ParBound p q b ↔
      ((pval b ≫ ousDelta.{u}.hom) ≫ ousDl.{u}
          = pval p ≫ (ouGamma ousTopCofan.{u}).hom ∧
        (pval b ≫ ousDelta.{u}.hom) ≫ ousDr.{u}
          = pval q ≫ (ouGamma ousTopCofan.{u}).hom) := by
  have e₁ : pval (b ≫ Par.pproj₁ (⊤_ OUS.{u}ᵒᵖ) (⊤_ OUS.{u}ᵒᵖ))
      = pval b ≫ coprod.desc (𝟙 ((⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ)))
          (coprod.inr : (⊤_ OUS.{u}ᵒᵖ) ⟶ _) := by
    rw [pval_comp]
    congr 1
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc, coprod.inl_desc]
      show (coprod.desc coprod.inl (Par.zero (⊤_ OUS.{u}ᵒᵖ) (⊤_ OUS.{u}ᵒᵖ)) :
        (⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ) ⟶ _) = _
      refine coprod.hom_ext ?_ ?_
      · rw [coprod.inl_desc, Category.comp_id]
      · rw [coprod.inr_desc, Category.comp_id]
        show terminal.from (⊤_ OUS.{u}ᵒᵖ) ≫ coprod.inr = _
        rw [par_terminal_self, Category.id_comp]
    · rw [coprod.inr_desc, coprod.inr_desc]
  have e₂ : pval (b ≫ Par.pproj₂ (⊤_ OUS.{u}ᵒᵖ) (⊤_ OUS.{u}ᵒᵖ))
      = pval b ≫ coprod.desc (parSwapTop : (⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ) ⟶ _)
          (coprod.inr : (⊤_ OUS.{u}ᵒᵖ) ⟶ _) := by
    rw [pval_comp]
    congr 1
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc, coprod.inl_desc]
      show (coprod.desc (Par.zero (⊤_ OUS.{u}ᵒᵖ) (⊤_ OUS.{u}ᵒᵖ)) coprod.inl :
        (⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ) ⟶ _) = _
      rw [parSwapTop_eq]
      refine coprod.hom_ext ?_ ?_
      · rw [coprod.inl_desc, coprod.inl_desc]
        show terminal.from (⊤_ OUS.{u}ᵒᵖ) ≫ coprod.inr = _
        rw [par_terminal_self, Category.id_comp]
      · rw [coprod.inr_desc, coprod.inr_desc]
    · rw [coprod.inr_desc, coprod.inr_desc]
  constructor
  · rintro ⟨hb₁, hb₂⟩
    have hb₁' : b ≫ Par.pproj₁ (⊤_ OUS.{u}ᵒᵖ) (⊤_ OUS.{u}ᵒᵖ) = p := hb₁
    have hb₂' : b ≫ Par.pproj₂ (⊤_ OUS.{u}ᵒᵖ) (⊤_ OUS.{u}ᵒᵖ) = q := hb₂
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, ← ous_Dl_eq, ← Category.assoc, ← e₁, hb₁']
    · rw [Category.assoc, ← ous_Dr_eq, ← Category.assoc, ← e₂, hb₂']
  · rintro ⟨hb₁, hb₂⟩
    refine ⟨?_, ?_⟩
    · show b ≫ Par.pproj₁ (⊤_ OUS.{u}ᵒᵖ) (⊤_ OUS.{u}ᵒᵖ) = p
      refine pval_inj ?_
      refine (cancel_mono (ouGamma ousTopCofan.{u}).hom).mp ?_
      rw [e₁, Category.assoc, ous_Dl_eq, ← Category.assoc]
      exact hb₁
    · show b ≫ Par.pproj₂ (⊤_ OUS.{u}ᵒᵖ) (⊤_ OUS.{u}ᵒᵖ) = q
      refine pval_inj ?_
      refine (cancel_mono (ouGamma ousTopCofan.{u}).hom).mp ?_
      rw [e₂, Category.assoc, ous_Dr_eq, ← Category.assoc]
      exact hb₂

/-- **⊥ for predicates of `OUSᵒᵖ`**, concretely: `p ⊥ q` exactly when the
pair is the image of a positive unital map out of `ℝ³`. -/
theorem ous_perp_iff {X : OUS.{u}ᵒᵖ} (p q : Pred (Par.of X)) :
    Perp p q ↔ ∃ β : X ⟶ ousR.{u},
      β ≫ ousDl.{u} = pval p ≫ (ouGamma ousTopCofan.{u}).hom ∧
      β ≫ ousDr.{u} = pval q ≫ (ouGamma ousTopCofan.{u}).hom := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨pval b ≫ ousDelta.{u}.hom, (ous_bound_iff p q b).mp hb⟩
  · rintro ⟨β, hβ₁, hβ₂⟩
    obtain ⟨b, hbv⟩ : ∃ b : Par.of X ⟶ Par.of ((⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ)),
        pval b = β ≫ ousDelta.{u}.inv := ⟨(β ≫ ousDelta.{u}.inv : X ⟶ _), rfl⟩
    refine ⟨b, (ous_bound_iff p q b).mpr ?_⟩
    rw [hbv]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact ⟨hβ₁, hβ₂⟩

/-- **⋁ for predicates of `OUSᵒᵖ`**, concretely. -/
theorem ous_ovee_eq {X : OUS.{u}ᵒᵖ} {p q : Pred (Par.of X)} (h : Perp p q)
    {β : X ⟶ ousR.{u}}
    (hβ₁ : β ≫ ousDl.{u} = pval p ≫ (ouGamma ousTopCofan.{u}).hom)
    (hβ₂ : β ≫ ousDr.{u} = pval q ≫ (ouGamma ousTopCofan.{u}).hom) :
    pval (ovee p q h) ≫ (ouGamma ousTopCofan.{u}).hom = β ≫ ousDv.{u} := by
  obtain ⟨b, hbv⟩ : ∃ b : Par.of X ⟶ Par.of ((⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ)),
      pval b = β ≫ ousDelta.{u}.inv := ⟨(β ≫ ousDelta.{u}.inv : X ⟶ _), rfl⟩
  have hb : ParBound p q b := by
    refine (ous_bound_iff p q b).mpr ?_
    rw [hbv]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact ⟨hβ₁, hβ₂⟩
  have hov : ovee p q h = b ≫ parNabla (⊤_ OUS.{u}ᵒᵖ) := parOvee_eq h hb
  rw [hov]
  have hpv2 : pval (b ≫ parNabla (⊤_ OUS.{u}ᵒᵖ))
      = pval b ≫ coprod.desc (pval (parNabla (⊤_ OUS.{u}ᵒᵖ)))
            (coprod.inr : (⊤_ OUS.{u}ᵒᵖ) ⟶ _) := pval_comp _ _
  rw [hpv2, hbv, Category.assoc, ous_Dv_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-! ## The scalars of `OUSᵒᵖ` are `[0,1]` -/

theorem ousHom_apply (X : OUS.{u}) (φ : ousScal.{u}.prod ousScal.{u} ⟶ X)
    (ab : ULift.{u} ℝ × ULift.{u} ℝ) :
    φ.toLinearMap ab
      = ab.1.down • φ.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))
        + ab.2.down • (X.unit
          - φ.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))) := by
  have hdec : ab = ab.1.down • ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))
      + ab.2.down • ((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)) := by
    refine Prod.ext ?_ ?_ <;> apply ULift.down_injective <;> simp
  conv_lhs => rw [hdec]
  rw [map_add, map_smul, map_smul, ous_hom_compl X φ]

/-- The scalars of `OUSᵒᵖ` are the positive unital maps `ℝ² ⟶ ℝ`. -/
def ousScalMapEquiv :
    Scal (Par OUS.{u}ᵒᵖ) ≃ (ousScal.{u}.prod ousScal.{u} ⟶ ousScal.{u}) :=
  ((ouPredEquiv ousTopCofan.{u} (⊤_ OUS.{u}ᵒᵖ)).trans
    { toFun := fun f => f.unop
      invFun := fun g => Quiver.Hom.op g
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
    (ousHomTopEquiv (ousScal.{u}.prod ousScal.{u}))

/-- **190IV.1** (eff.tex:2149, Examples): the scalars of `OUSᵒᵖ` are `[0,1]`,
as a bijection. -/
def ousScalEquivI : Scal (Par OUS.{u}ᵒᵖ) ≃ I :=
  (ousScalMapEquiv.{u}.trans (ousHomEffectEquiv ousScal.{u})).trans
    { toFun := fun y => ⟨y.1.down, y.2.1, y.2.2⟩
      invFun := fun r => ⟨ULift.up r.1, r.2.1, r.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The real number attached to a scalar. -/
def ousScalV (k : Scal (Par OUS.{u}ᵒᵖ)) : ℝ := (ousScalEquivI.{u} k : ℝ)

/-- The real number attached to a scalar is the image of `(1,0)`. -/
theorem ousScalV_def (k : Scal (Par OUS.{u}ᵒᵖ)) :
    ousScalV k = ((ousScalMapEquiv.{u} k).toLinearMap
      ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))).down := rfl

/-- A scalar is determined by its real number. -/
theorem ousScalV_injective {k l : Scal (Par OUS.{u}ᵒᵖ)} (h : ousScalV k = ousScalV l) :
    k = l := ousScalEquivI.{u}.injective (Subtype.ext h)

/-- A scalar acts on `ℝ²` by `(s,t) ↦ λs + (1-λ)t`. -/
theorem ousScalMap_down (k : Scal (Par OUS.{u}ᵒᵖ))
    (ab : ULift.{u} ℝ × ULift.{u} ℝ) :
    ((ousScalMapEquiv.{u} k).toLinearMap ab).down
      = ab.1.down * ousScalV k + ab.2.down * (1 - ousScalV k) := by
  rw [ousHom_apply ousScal.{u} (ousScalMapEquiv.{u} k) ab]
  rfl

/-- The scalar `1` is the first projection `ℝ² ⟶ ℝ`. -/
theorem ousScalMapEquiv_one :
    ousScalMapEquiv.{u} (1 : Scal (Par OUS.{u}ᵒᵖ)) = ousFst ousScal.{u} ousScal.{u} := by
  show (ouPredEquiv ousTopCofan.{u} (⊤_ OUS.{u}ᵒᵖ)
      (truth (Par.of (⊤_ OUS.{u}ᵒᵖ)))).unop ≫ ousTopTo ousScal.{u} = _
  rw [ouPredEquiv_truth, par_terminal_self, Category.id_comp]
  show (ousFst ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u}) ≫ ousTopTo ousScal.{u} = _
  rw [Category.assoc, ousTop_inv₁, Category.comp_id]

/-- The scalar `0` is the second projection `ℝ² ⟶ ℝ`. -/
theorem ousScalMapEquiv_zero :
    ousScalMapEquiv.{u} (0 : Scal (Par OUS.{u}ᵒᵖ)) = ousSnd ousScal.{u} ousScal.{u} := by
  show (ouPredEquiv ousTopCofan.{u} (⊤_ OUS.{u}ᵒᵖ)
      (0 : Pred (Par.of (⊤_ OUS.{u}ᵒᵖ)))).unop ≫ ousTopTo ousScal.{u} = _
  rw [ouPredEquiv_zero, par_terminal_self, Category.id_comp]
  show (ousSnd ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u}) ≫ ousTopTo ousScal.{u} = _
  rw [Category.assoc, ousTop_inv₁, Category.comp_id]

/-- The scalar `1` has value `1`. -/
theorem ousScalV_one : ousScalV (1 : Scal (Par OUS.{u}ᵒᵖ)) = 1 := by
  rw [ousScalV_def, ousScalMapEquiv_one]
  rfl

/-- The scalar `0` has value `0`. -/
theorem ousScalV_zero : ousScalV (0 : Scal (Par OUS.{u}ᵒᵖ)) = 0 := by
  rw [ousScalV_def, ousScalMapEquiv_zero]
  rfl

/-- The value of a scalar is non-negative. -/
theorem ousScalV_nonneg (k : Scal (Par OUS.{u}ᵒᵖ)) : 0 ≤ ousScalV k :=
  (ousScalEquivI.{u} k).2.1

/-- The value of a scalar is at most `1`. -/
theorem ousScalV_le_one (k : Scal (Par OUS.{u}ᵒᵖ)) : ousScalV k ≤ 1 :=
  (ousScalEquivI.{u} k).2.2

/-- A witness `β : ⊤ ⟶ ℝ³`, read as a positive unital map `ℝ³ ⟶ ℝ`. -/
def ousBmap (β : (⊤_ OUS.{u}ᵒᵖ) ⟶ ousR.{u}) :
    ((ousScal.{u}.prod ousScal.{u}).prod ousScal.{u}) ⟶ ousScal.{u} :=
  β.unop ≫ ousTopTo ousScal.{u}

/-- A witness for `⊥`, read on `ℝ³`, computes the scalar it bounds. -/
theorem ous_beta_comp {β : (⊤_ OUS.{u}ᵒᵖ) ⟶ ousR.{u}} {D : ousR.{u} ⟶ ousS.{u}}
    {k : Scal (Par OUS.{u}ᵒᵖ)}
    (h : β ≫ D = pval k ≫ (ouGamma ousTopCofan.{u}).hom) :
    D.unop ≫ ousBmap β = ousScalMapEquiv.{u} k := by
  have h1 : (β ≫ D).unop = (pval k ≫ (ouGamma ousTopCofan.{u}).hom).unop :=
    congrArg Quiver.Hom.unop h
  show D.unop ≫ (β.unop ≫ ousTopTo ousScal.{u}) = _
  rw [← Category.assoc]
  show (β ≫ D).unop ≫ ousTopTo ousScal.{u} = _
  rw [h1]
  rfl

/-- Converse of `ous_beta_comp`. -/
theorem ous_beta_comp' {β : (⊤_ OUS.{u}ᵒᵖ) ⟶ ousR.{u}} {D : ousR.{u} ⟶ ousS.{u}}
    {k : Scal (Par OUS.{u}ᵒᵖ)}
    (h : D.unop ≫ ousBmap β = ousScalMapEquiv.{u} k) :
    β ≫ D = pval k ≫ (ouGamma ousTopCofan.{u}).hom := by
  refine Quiver.Hom.unop_inj ?_
  refine ous_hom_to_top_ext ?_
  show (D.unop ≫ β.unop) ≫ ousTopTo ousScal.{u} = _
  rw [Category.assoc]
  exact h

/-- `[κ₁,κ₂,κ₂]` sends `(1,0)` to `((1,0),0)`. -/
theorem ousDl_one_zero :
    (ousDl.{u}).unop.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))
      = (((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ)) := rfl

/-- `[κ₂,κ₁,κ₂]` sends `(1,0)` to `((0,1),0)`. -/
theorem ousDr_one_zero :
    (ousDr.{u}).unop.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))
      = (((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ)) := rfl

/-- `[κ₁,κ₁,κ₂]` sends `(1,0)` to `((1,1),0)`. -/
theorem ousDv_one_zero :
    (ousDv.{u}).unop.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))
      = (((1 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ)) := rfl

/-- `((1,0),0) + ((0,1),0) = ((1,1),0)` in `ℝ³`. -/
theorem ous_sum_pt :
    ((((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ))
        + (((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ)) :
      (ULift.{u} ℝ × ULift.{u} ℝ) × ULift.{u} ℝ)
      = (((1 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ)) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> apply ULift.down_injective <;> simp

/-- `((1,1),0)` is below the order unit of `ℝ³`. -/
theorem ous_sum_le_unit :
    ((((1 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ)) :
      (ULift.{u} ℝ × ULift.{u} ℝ) × ULift.{u} ℝ)
      ≤ ((ousScal.{u}.prod ousScal.{u}).prod ousScal.{u}).unit :=
  Prod.le_def.mpr ⟨le_refl _, show (0 : ℝ) ≤ 1 from zero_le_one⟩

/-- Half of **190IV.1** (eff.tex:2149): orthogonal scalars have
`λ + μ ≤ 1`. -/
theorem ousScalV_perp {k l : Scal (Par OUS.{u}ᵒᵖ)} (h : Perp k l) :
    ousScalV k + ousScalV l ≤ 1 := by
  obtain ⟨β, hβ₁, hβ₂⟩ := (ous_perp_iff k l).mp h
  have e₁ : ((ousBmap β).toLinearMap
      (((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ))).down
      = ousScalV k := by
    rw [← ousDl_one_zero, ← ous_comp_apply, ous_beta_comp hβ₁, ousScalV_def]
  have e₂ : ((ousBmap β).toLinearMap
      (((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ))).down
      = ousScalV l := by
    rw [← ousDr_one_zero, ← ous_comp_apply, ous_beta_comp hβ₂, ousScalV_def]
  have hsum : (ousBmap β).toLinearMap
      (((1 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ))
      = (ousBmap β).toLinearMap
          (((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ))
        + (ousBmap β).toLinearMap
          (((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ)) := by
    rw [← map_add, ous_sum_pt]
  have hmono := (ousBmap β).mono ous_sum_le_unit.{u}
  rw [(ousBmap β).map_unit', hsum] at hmono
  have hd : ousScalV k + ousScalV l ≤ (1 : ℝ) := by
    have := hmono
    rw [← e₁, ← e₂]
    exact this
  exact hd

/-- The positive unital map `ℝ³ ⟶ ℝ` mixing three non-negative weights. -/
def ousMixMap (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c = 1) :
    ((ousScal.{u}.prod ousScal.{u}).prod ousScal.{u}) ⟶ ousScal.{u} where
  toLinearMap :=
    { toFun := fun p =>
        ULift.up (a * p.1.1.down + b * p.1.2.down + c * p.2.down)
      map_add' := fun p q => congrArg ULift.up (by
        show a * (p.1.1.down + q.1.1.down) + b * (p.1.2.down + q.1.2.down)
            + c * (p.2.down + q.2.down)
          = (a * p.1.1.down + b * p.1.2.down + c * p.2.down)
            + (a * q.1.1.down + b * q.1.2.down + c * q.2.down)
        ring)
      map_smul' := fun r p => congrArg ULift.up (by
        show a * (r * p.1.1.down) + b * (r * p.1.2.down) + c * (r * p.2.down)
          = r * (a * p.1.1.down + b * p.1.2.down + c * p.2.down)
        ring) }
  map_nonneg' := fun p hp => by
    obtain ⟨hp1, hp2⟩ := Prod.le_def.mp hp
    obtain ⟨hp11, hp12⟩ := Prod.le_def.mp hp1
    show (0 : ℝ) ≤ a * p.1.1.down + b * p.1.2.down + c * p.2.down
    have h1 : (0 : ℝ) ≤ p.1.1.down := hp11
    have h2 : (0 : ℝ) ≤ p.1.2.down := hp12
    have h3 : (0 : ℝ) ≤ p.2.down := hp2
    have := mul_nonneg ha h1
    have := mul_nonneg hb h2
    have := mul_nonneg hc h3
    linarith
  map_unit' := by
    apply ULift.down_injective
    show a * 1 + b * 1 + c * 1 = 1
    linarith

/-- The defining equation of `ousMixMap`. -/
theorem ousMixMap_apply (a b c : ℝ) (ha hb hc hs) (p) :
    ((ousMixMap.{u} a b c ha hb hc hs).toLinearMap p).down
      = a * p.1.1.down + b * p.1.2.down + c * p.2.down := rfl

/-- The mixing map attached to two scalars with `λ + μ ≤ 1`. -/
def ousMixOf (k l : Scal (Par OUS.{u}ᵒᵖ)) (h : ousScalV k + ousScalV l ≤ 1) :
    ((ousScal.{u}.prod ousScal.{u}).prod ousScal.{u}) ⟶ ousScal.{u} :=
  ousMixMap (ousScalV k) (ousScalV l) (1 - ousScalV k - ousScalV l)
    (ousScalV_nonneg k) (ousScalV_nonneg l)
    (by have := ousScalV_nonneg.{u} k; linarith) (by ring)

/-- The defining equation of `ousMixOf`. -/
theorem ousMixOf_down (k l : Scal (Par OUS.{u}ᵒᵖ)) (h : ousScalV k + ousScalV l ≤ 1)
    (p : (ULift.{u} ℝ × ULift.{u} ℝ) × ULift.{u} ℝ) :
    ((ousMixOf k l h).toLinearMap p).down
      = ousScalV k * p.1.1.down + ousScalV l * p.1.2.down
        + (1 - ousScalV k - ousScalV l) * p.2.down := rfl

/-- Reading a positive unital map `ℝ³ ⟶ ℝ` as a point of `ℝ³` and back. -/
theorem ousBmap_op (B : ((ousScal.{u}.prod ousScal.{u}).prod ousScal.{u})
      ⟶ ousScal.{u}) :
    ousBmap (Quiver.Hom.op (B ≫ ousUnitTop.{u})) = B := by
  show (B ≫ ousUnitTop.{u}) ≫ ousTopTo ousScal.{u} = B
  rw [Category.assoc, ousTop_inv₁, Category.comp_id]

/-- Half of **190IV.1** (eff.tex:2149): scalars with `λ + μ ≤ 1` are
orthogonal. -/
theorem ousScalV_perp' {k l : Scal (Par OUS.{u}ᵒᵖ)}
    (h : ousScalV k + ousScalV l ≤ 1) : Perp k l := by
  refine (ous_perp_iff k l).mpr
    ⟨Quiver.Hom.op (ousMixOf k l h ≫ ousUnitTop.{u}), ?_, ?_⟩
  · refine ous_beta_comp' ?_
    rw [ousBmap_op]
    refine ous_hom_ext fun ab => ?_
    apply ULift.down_injective
    rw [ous_comp_apply, ousMixOf_down, ousScalMap_down]
    show ousScalV k * ab.1.down + ousScalV l * ab.2.down
        + (1 - ousScalV k - ousScalV l) * ab.2.down
      = ab.1.down * ousScalV k + ab.2.down * (1 - ousScalV k)
    ring
  · refine ous_beta_comp' ?_
    rw [ousBmap_op]
    refine ous_hom_ext fun ab => ?_
    apply ULift.down_injective
    rw [ous_comp_apply, ousMixOf_down, ousScalMap_down]
    show ousScalV k * ab.2.down + ousScalV l * ab.1.down
        + (1 - ousScalV k - ousScalV l) * ab.2.down
      = ab.1.down * ousScalV l + ab.2.down * (1 - ousScalV l)
    ring

/-- **190IV.1** (eff.tex:2149): `⋁` of scalars is addition in `[0,1]`. -/
theorem ousScalV_ovee {k l : Scal (Par OUS.{u}ᵒᵖ)} (h : Perp k l) :
    ousScalV (ovee k l h) = ousScalV k + ousScalV l := by
  obtain ⟨β, hβ₁, hβ₂⟩ := (ous_perp_iff k l).mp h
  have e₁ : ((ousBmap β).toLinearMap
      (((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ))).down
      = ousScalV k := by
    rw [← ousDl_one_zero, ← ous_comp_apply, ous_beta_comp hβ₁, ousScalV_def]
  have e₂ : ((ousBmap β).toLinearMap
      (((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ))).down
      = ousScalV l := by
    rw [← ousDr_one_zero, ← ous_comp_apply, ous_beta_comp hβ₂, ousScalV_def]
  have ev : ((ousBmap β).toLinearMap
      (((1 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ))).down
      = ousScalV (ovee k l h) := by
    rw [← ousDv_one_zero, ← ous_comp_apply,
      ous_beta_comp (ous_ovee_eq h hβ₁ hβ₂).symm, ousScalV_def]
  rw [← ev, ← e₁, ← e₂, ← ous_sum_pt, map_add]
  rfl

/-- The round trip `ousTopO ⟶ ℝᵤ ⟶ ousTopO`. -/
theorem ous_top_round {Z : OUS.{u}} (a : Z ⟶ ousTopO.{u}) :
    (a ≫ ousTopTo ousScal.{u}) ≫ ousUnitTop.{u} = a := by
  rw [Category.assoc, ousTop_inv₂, Category.comp_id]

/-- The scalar `k` read as an endomorphism of `ℝ²`. -/
def ousMk (k : Scal (Par OUS.{u}ᵒᵖ)) : ousS.{u} ⟶ ousS.{u} :=
  Quiver.Hom.op (ousPair (ousScalMapEquiv.{u} k) (ousSnd ousScal.{u} ousScal.{u}))

/-- `ousMk k` sends the first point of `⊤ + ⊤` to `k`. -/
theorem ousI₁_Mk (k : Scal (Par OUS.{u}ᵒᵖ)) :
    ousI₁.{u} ≫ ousMk k = pval k ≫ (ouGamma ousTopCofan.{u}).hom := by
  refine Quiver.Hom.unop_inj ?_
  show ousPair (ousScalMapEquiv.{u} k) (ousSnd ousScal.{u} ousScal.{u})
      ≫ (ousFst ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u})
    = (pval k ≫ (ouGamma ousTopCofan.{u}).hom).unop
  rw [← Category.assoc, ousPair_fst]
  exact ous_top_round ((pval k ≫ (ouGamma ousTopCofan.{u}).hom).unop)

/-- `ousMk k` fixes the second point of `⊤ + ⊤`. -/
theorem ousI₂_Mk (k : Scal (Par OUS.{u}ᵒᵖ)) : ousI₂.{u} ≫ ousMk k = ousI₂.{u} := by
  refine Quiver.Hom.unop_inj ?_
  show ousPair (ousScalMapEquiv.{u} k) (ousSnd ousScal.{u} ousScal.{u})
      ≫ (ousSnd ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u})
    = ousSnd ousScal.{u} ousScal.{u} ≫ ousUnitTop.{u}
  rw [← Category.assoc, ousPair_snd]

/-- Postcomposition with the scalar `k`, transported to `ℝ²`. -/
theorem ous_desc_Mk (k : Scal (Par OUS.{u}ᵒᵖ)) :
    coprod.desc (pval k) (coprod.inr : (⊤_ OUS.{u}ᵒᵖ) ⟶ _)
        ≫ (ouGamma ousTopCofan.{u}).hom
      = (ouGamma ousTopCofan.{u}).hom ≫ ousMk k := by
  refine coprod.hom_ext ?_ ?_
  · simp only [← Category.assoc]
    rw [coprod.inl_desc, ouGamma_inl, ousI₁_Mk]
  · simp only [← Category.assoc]
    rw [coprod.inr_desc, ouGamma_inr, ouGamma_inr, ousI₂_Mk]

/-- **190IV.1** (eff.tex:2149): composition of scalars is multiplication in
`[0,1]`. -/
theorem ousScalV_mul (k l : Scal (Par OUS.{u}ᵒᵖ)) :
    ousScalV (k * l) = ousScalV k * ousScalV l := by
  have hkl : (k * l : Scal (Par OUS.{u}ᵒᵖ)) = l ≫ k := rfl
  have hpv : pval (l ≫ k) ≫ (ouGamma ousTopCofan.{u}).hom
      = (pval l ≫ (ouGamma ousTopCofan.{u}).hom) ≫ ousMk k := by
    rw [pval_comp, Category.assoc, ous_desc_Mk, ← Category.assoc]
  have hmap : ousScalMapEquiv.{u} (l ≫ k)
      = (ousMk k).unop ≫ ousScalMapEquiv.{u} l := by
    show (pval (l ≫ k) ≫ (ouGamma ousTopCofan.{u}).hom).unop ≫ ousTopTo ousScal.{u}
      = (ousMk k).unop ≫ ((pval l ≫ (ouGamma ousTopCofan.{u}).hom).unop
        ≫ ousTopTo ousScal.{u})
    rw [hpv, ← Category.assoc]
    rfl
  rw [hkl, ousScalV_def, hmap, ous_comp_apply]
  have hpt : (ousMk k).unop.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))
      = ((ousScalMapEquiv.{u} k).toLinearMap
          ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ)), (0 : ULift.{u} ℝ)) := rfl
  rw [hpt, ousScalMap_down]
  show ousScalV k * ousScalV l + 0 * (1 - ousScalV l) = ousScalV k * ousScalV l
  ring

/-! ### `Par OUSᵒᵖ` is a real effectus -/

private theorem ousI_perp_iff (x y : I) : Perp x y ↔ (x : ℝ) + (y : ℝ) ≤ 1 := Iff.rfl

/-- **190IV.1** (eff.tex:2149, Examples): `OUSᵒᵖ` is a **real effectus** —
its effect monoid of scalars is `[0,1]`.  A scalar is a positive unital map
`ℝ² ⟶ ℝ`, i.e. `(s,t) ↦ λs + (1-λ)t` for a unique `λ ∈ [0,1]`; orthogonality
is `λ + μ ≤ 1`, `⋁` is addition, and composition is multiplication. -/
theorem ous_real_effectus : IsRealEffectus (Par OUS.{u}ᵒᵖ) := by
  have hφperp : ∀ {a b : Scal (Par OUS.{u}ᵒᵖ)}, Perp a b →
      Perp (ousScalEquivI.{u} a) (ousScalEquivI.{u} b) := fun hab => ousScalV_perp hab
  have hφovee : ∀ {a b : Scal (Par OUS.{u}ᵒᵖ)} (hab : Perp a b),
      ousScalEquivI.{u} (ovee a b hab)
        = ovee (ousScalEquivI.{u} a) (ousScalEquivI.{u} b) (hφperp hab) := by
    intro a b hab
    exact Subtype.ext (ousScalV_ovee hab)
  have hφone : ousScalEquivI.{u} 1 = 1 := Subtype.ext ousScalV_one
  have hφmul : ∀ a b : Scal (Par OUS.{u}ᵒᵖ),
      ousScalEquivI.{u} (a * b) = ousScalEquivI.{u} a * ousScalEquivI.{u} b :=
    fun a b => Subtype.ext (ousScalV_mul a b)
  have hV : ∀ r : I, ousScalV (ousScalEquivI.{u}.symm r) = (r : ℝ) :=
    fun r => congrArg Subtype.val (ousScalEquivI.{u}.apply_symm_apply r)
  have hψperp : ∀ {x y : I}, Perp x y →
      Perp (ousScalEquivI.{u}.symm x) (ousScalEquivI.{u}.symm y) := by
    intro x y hxy
    refine ousScalV_perp' ?_
    rw [hV, hV]
    exact hxy
  have hψovee : ∀ {x y : I} (hxy : Perp x y),
      ousScalEquivI.{u}.symm (ovee x y hxy)
        = ovee (ousScalEquivI.{u}.symm x) (ousScalEquivI.{u}.symm y) (hψperp hxy) := by
    intro x y hxy
    refine ousScalV_injective ?_
    rw [ousScalV_ovee (hψperp hxy), hV, hV, hV]
    rfl
  have hψone : ousScalEquivI.{u}.symm 1 = 1 := by
    refine ousScalV_injective ?_
    rw [hV, ousScalV_one]
    rfl
  have hψmul : ∀ x y : I,
      ousScalEquivI.{u}.symm (x * y)
        = ousScalEquivI.{u}.symm x * ousScalEquivI.{u}.symm y := by
    intro x y
    refine ousScalV_injective ?_
    rw [ousScalV_mul, hV, hV, hV]
    rfl
  exact ⟨⟨⟨⟨ousScalEquivI.{u}, hφperp, hφovee⟩, hφone⟩, hφmul⟩,
    ⟨⟨⟨ousScalEquivI.{u}.symm, hψperp, hψovee⟩, hψone⟩, hψmul⟩,
    fun k => ousScalEquivI.{u}.symm_apply_apply k,
    fun r => ousScalEquivI.{u}.apply_symm_apply r⟩

/-! ## The parenthetical of 190IV.1: separating states and archimedeanness

eff.tex:2151 says, of a *single* order unit space, that its states are
separating if and only if it is archimedean.  Half of that holds and is
`ous_separatingStatesAt_of_archimedean`; the other half is **false**, and
`ous_separating_states_not_archimedean` refutes it with `ousAlm` below.  The
sharp statement is `ous_separatingStatesAt_iff_almostArchimedean`: the states
of `X` are separating exactly when `X` is *almost* archimedean.  See the
ERRATA row on 190IV.1. -/

/-- The **per-object form of `SeparatingStates`** (190II.7, eff.tex:2129):
the states of a single object are jointly epic.  `SeparatingStates` is the
conjunction of these over all objects (`separatingStates_iff_forall`), and it
is this per-object form that 190IV.1's parenthetical speaks of. -/
def SeparatingStatesAt {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] (X : C) : Prop :=
  ∀ ⦃Y : C⦄ (f g : X ⟶ Y), (∀ ω : Stat X, ω.1 ≫ f = ω.1 ≫ g) → f = g

/-- An effectus has separating states exactly when every one of its objects
has. -/
theorem separatingStates_iff_forall (C : Type u) [Category.{v} C]
    [HasFiniteCoproducts C] [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C]
    [EffectusPartialForm C] :
    SeparatingStates C ↔ ∀ X : C, SeparatingStatesAt X :=
  ⟨fun h _ _ f g hfg => h f g hfg, fun h _ _ f g hfg => h _ f g hfg⟩

/-- A **state of the order unit space `X`** in the sense of the literature: a
positive unital linear functional.  By `ous_stat_state` these are exactly the
states of `op X` in `Par OUSᵒᵖ`. -/
abbrev OUSState (X : OUS.{u}) : Type u :=
  {f : X.carrier →ₗ[ℝ] ℝ // (∀ x, 0 ≤ x → 0 ≤ f x) ∧ f X.unit = 1}

/-- The states of `X` **separate its points**.  This is what joint epicity of
`Stat (op X)` comes to, by `ous_separatingStatesAt_iff_points`. -/
def OUSSeparatingPoints (X : OUS.{u}) : Prop :=
  ∀ x y : X.carrier, (∀ ψ : OUSState X, ψ.1 x = ψ.1 y) → x = y

/-- `ousTopO ⟶ ℝᵤ` is injective on points, being half of an isomorphism. -/
theorem ousTopTo_injective {a b : ousTopO.{u}.carrier}
    (h : (ousTopTo ousScal.{u}).toLinearMap a
      = (ousTopTo ousScal.{u}).toLinearMap b) : a = b := by
  have h1 := ous_congr (ousTop_inv₂.{u}) a
  have h2 := ous_congr (ousTop_inv₂.{u}) b
  rw [ous_comp_apply, ous_id_apply] at h1 h2
  rw [← h1, ← h2, h]

/-- A state of `Par.of (op X)` is `ŵ` for its underlying point `w`
(`parStatEquiv`, i.e. 186VIII.1 read as a bijection). -/
theorem ous_stat_hat (X : OUS.{u}) (ω : Stat (Par.of (op X))) :
    ω.1 = Par.hat (parStatEquiv (op X) ω) :=
  (congrArg Subtype.val ((parStatEquiv (op X)).symm_apply_apply ω)).symm

/-- The functional attached to a state by `ous_stat_state`, unfolded. -/
theorem ous_stat_state_val (X : OUS.{u}) (ω : Stat (Par.of (op X)))
    (x : X.carrier) :
    (ous_stat_state X ω).1 x
      = ((ousTopTo ousScal.{u}).toLinearMap
          ((parStatEquiv (op X) ω).unop.toLinearMap x)).down := rfl

/-- **The state calculus of `OUSᵒᵖ`**: a state identifies two partial maps
out of `X` exactly when its functional identifies their two underlying
positive unital maps.  A state is `ŵ`, and `ŵ ⊙ f = w ∘ f` (`par_hat_comp`),
which in `OUS` is postcomposition with `w`. -/
theorem ous_stat_comp_iff (X : OUS.{u}) {Y : Par OUS.{u}ᵒᵖ}
    (f g : Par.of (op X) ⟶ Y) (ω : Stat (Par.of (op X))) :
    ω.1 ≫ f = ω.1 ≫ g
      ↔ ∀ z : (Y.base ⨿ (⊤_ OUS.{u}ᵒᵖ)).unop.carrier,
          (ous_stat_state X ω).1 ((pval f).unop.toLinearMap z)
            = (ous_stat_state X ω).1 ((pval g).unop.toLinearMap z) := by
  constructor
  · intro h z
    have h1 : pval (ω.1 ≫ f) = pval (ω.1 ≫ g) := congrArg pval h
    rw [ous_stat_hat X ω, par_hat_comp, par_hat_comp] at h1
    have h2 := ousop_congr h1 z
    rw [ousop_comp_apply, ousop_comp_apply] at h2
    rw [ous_stat_state_val, ous_stat_state_val, h2]
  · intro h
    refine pval_inj ?_
    rw [ous_stat_hat X ω, par_hat_comp, par_hat_comp]
    refine ousop_hom_ext fun z => ?_
    rw [ousop_comp_apply, ousop_comp_apply]
    refine ousTopTo_injective (ULift.down_injective ?_)
    rw [← ous_stat_state_val, ← ous_stat_state_val]
    exact h z

/-- If the states of `X` separate its points then they are jointly epic:
two partial maps out of `X` are two positive unital maps *into* `X`, and
those are determined pointwise. -/
theorem ous_separatingStatesAt_of_points (X : OUS.{u})
    (h : OUSSeparatingPoints X) : SeparatingStatesAt (Par.of (op X)) := by
  intro Y f g hfg
  refine pval_inj ?_
  refine ousop_hom_ext fun z => ?_
  refine h _ _ fun ψ => ?_
  have h2 := (ous_stat_comp_iff X f g ((ous_stat_state X).symm ψ)).mp
    (hfg ((ous_stat_state X).symm ψ)) z
  rwa [(ous_stat_state X).apply_symm_apply ψ] at h2

/-! ### Separating points, archimedeanness and almost archimedeanness -/

/-- Archimedean spaces are almost archimedean. -/
theorem ous_almostArchimedean_of_archimedean {X : Type u} [AddCommGroup X]
    [Module ℝ X] [PartialOrder X] [OrderUnitSpace X] (h : OUSArchimedean X) :
    OUSAlmostArchimedean X := by
  intro x hx
  have h1 : x ≤ 0 := h x fun ε hε => (hx ε hε).1
  have h2 : -x ≤ 0 := h (-x) fun ε hε => (hx ε hε).2
  exact le_antisymm h1 (neg_nonpos.mp h2)

/-- **The states of an almost archimedean order unit space separate its
points.**  If `x - y ≠ 0` then, `X` being almost archimedean, `x - y` (or its
negative) fails to be below some `ε · 1`, so its gauge is positive, and
`ou_exists_state` — the Hahn–Banach separation through the gauge — produces a
state that does not kill it. -/
theorem ous_separatingPoints_of_almostArchimedean (X : OUS.{u})
    (hA : OUSAlmostArchimedean X.carrier) : OUSSeparatingPoints X := by
  intro x y hxy
  by_contra hne
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hu : ouUnit X.carrier ≠ 0 := ou_unit_ne_zero_of_ne hd
  have key : ∀ d : X.carrier, (∀ ψ : OUSState X, ψ.1 d = 0) →
      ∀ ε : ℝ, 0 < ε → d ≤ ε • ouUnit X.carrier := by
    intro d hd0 ε hε
    by_contra hc
    obtain ⟨f, hpos, hunit, hfd⟩ :=
      ou_exists_state hu d (ou_gauge_pos_of_not_le hε hc)
    have hz : (⟨f, hpos, hunit⟩ : OUSState X).1 d = 0 := hd0 _
    exact absurd hz (ne_of_gt hfd)
  have hz1 : ∀ ψ : OUSState X, ψ.1 (x - y) = 0 := by
    intro ψ
    rw [map_sub, hxy ψ, sub_self]
  have hz2 : ∀ ψ : OUSState X, ψ.1 (-(x - y)) = 0 := by
    intro ψ
    rw [map_neg, hz1 ψ, neg_zero]
  exact hd (hA (x - y) fun ε hε => ⟨key _ hz1 ε hε, key _ hz2 ε hε⟩)

/-- Conversely, states separating the points forces almost archimedeanness:
a state of an `x` with `-ε · 1 ≤ x ≤ ε · 1` for all `ε > 0` has
`|ψ(x)| ≤ ε` for all `ε`, so `ψ(x) = 0 = ψ(0)`. -/
theorem ous_almostArchimedean_of_separatingPoints (X : OUS.{u})
    (h : OUSSeparatingPoints X) : OUSAlmostArchimedean X.carrier := by
  intro x hx
  refine h x 0 fun ψ => ?_
  rw [map_zero]
  have hle : ∀ ε : ℝ, 0 < ε → ψ.1 x ≤ ε := by
    intro ε hε
    have h1 := ψ.2.1 (ε • ouUnit X.carrier - x) (sub_nonneg.mpr (hx ε hε).1)
    rw [map_sub, map_smul, ψ.2.2, smul_eq_mul, mul_one] at h1
    linarith
  have hge : ∀ ε : ℝ, 0 < ε → -ψ.1 x ≤ ε := by
    intro ε hε
    have h1 := ψ.2.1 (ε • ouUnit X.carrier - -x) (sub_nonneg.mpr (hx ε hε).2)
    rw [map_sub, map_smul, map_neg, ψ.2.2, smul_eq_mul, mul_one] at h1
    linarith
  have k1 : ψ.1 x ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using hle ε hε
  have k2 : -ψ.1 x ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using hge ε hε
  linarith

/-- **190IV.1** (eff.tex:2151, Examples, item 1, the parenthetical), the half
that holds: **the states of an archimedean order unit space are
separating.** -/
theorem ous_separatingStatesAt_of_archimedean (X : OUS.{u})
    (h : OUSArchimedean X.carrier) : SeparatingStatesAt (Par.of (op X)) :=
  ous_separatingStatesAt_of_points X
    (ous_separatingPoints_of_almostArchimedean X
      (ous_almostArchimedean_of_archimedean h))

/-- The states of `X` **determine its order**: an element on which every
state is non-negative is non-negative. -/
def OUSStatesDetermineOrder (X : OUS.{u}) : Prop :=
  ∀ x : X.carrier, (∀ ψ : OUSState X, 0 ≤ ψ.1 x) → 0 ≤ x

/-- **Archimedeanness is what the states determining the order comes to**
(Kadison).  This is the reading under which 190IV.1's parenthetical is
*true*: the printed equivalence holds for the states determining the order,
not for the states being separating in the sense of 190II.7, which is
`ous_separatingStatesAt_iff_almostArchimedean`. -/
theorem ous_statesDetermineOrder_iff_archimedean (X : OUS.{u}) :
    OUSStatesDetermineOrder X ↔ OUSArchimedean X.carrier := by
  constructor
  · intro h x hx
    have h1 : (0 : X.carrier) ≤ -x := by
      refine h (-x) fun ψ => ?_
      have hle : ∀ ε : ℝ, 0 < ε → ψ.1 x ≤ ε := by
        intro ε hε
        have h2 := ψ.2.1 (ε • ouUnit X.carrier - x) (sub_nonneg.mpr (hx ε hε))
        rw [map_sub, map_smul, ψ.2.2, smul_eq_mul, mul_one] at h2
        linarith
      have h3 : ψ.1 x ≤ 0 :=
        le_of_forall_pos_le_add fun ε hε => by simpa using hle ε hε
      rw [map_neg]
      linarith
    exact neg_nonneg.mp h1
  · intro h x hx
    by_cases hu : ouUnit X.carrier = 0
    · rw [ou_eq_zero_of_unit_eq_zero hu x]
    · have h1 : ∀ ε : ℝ, 0 < ε → -x ≤ ε • ouUnit X.carrier := by
        intro ε hε
        by_contra hc
        obtain ⟨f, hpos, hunit, hfd⟩ :=
          ou_exists_state hu (-x) (ou_gauge_pos_of_not_le hε hc)
        have h2 : (0 : ℝ) ≤ (⟨f, hpos, hunit⟩ : OUSState X).1 x := hx _
        have h3 : f (-x) = -f x := map_neg f x
        have h4 : (0 : ℝ) ≤ f x := h2
        linarith
      exact neg_nonpos.mp (h (-x) h1)

/-! ### The states are jointly epic only if they separate points -/

/-- A positive unital map out of `ℝ²`, in terms of its effect `φ(1,0)`:
`φ(a,b) = a·φ(1,0) + b·(1 - φ(1,0))`. -/
theorem ous_hom_apply_effect (X : OUS.{u})
    (φ : ousScal.{u}.prod ousScal.{u} ⟶ X) (w : ULift.{u} ℝ × ULift.{u} ℝ) :
    φ.toLinearMap w
      = w.1.down • φ.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))
        + w.2.down • (X.unit
            - φ.toLinearMap ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))) := by
  have hdec : w = w.1.down • ((1 : ULift.{u} ℝ), (0 : ULift.{u} ℝ))
      + w.2.down • ((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)) := by
    refine Prod.ext ?_ ?_ <;> apply ULift.down_injective <;> simp
  conv_lhs => rw [hdec]
  rw [map_add, map_smul, map_smul, ous_hom_compl]

/-- The underlying map of a predicate, in terms of its effect: transport
along the comparison isomorphism `⊤ + ⊤ ≅ ℝ²` and apply
`ous_hom_apply_effect`. -/
theorem ous_pred_apply (X : OUS.{u}) (p : Pred (Par.of (op X)))
    (z : ((⊤_ OUS.{u}ᵒᵖ) ⨿ (⊤_ OUS.{u}ᵒᵖ)).unop.carrier) :
    (pval p).unop.toLinearMap z
      = ((ouGamma ousTopCofan.{u}).inv.unop.toLinearMap z).1.down
            • ((ous_pred_effect X p).1 : X.carrier)
        + ((ouGamma ousTopCofan.{u}).inv.unop.toLinearMap z).2.down
            • (X.unit - ((ous_pred_effect X p).1 : X.carrier)) := by
  have hz : (ouGamma ousTopCofan.{u}).hom.unop.toLinearMap
      ((ouGamma ousTopCofan.{u}).inv.unop.toLinearMap z) = z := by
    have h := ousop_congr (Iso.hom_inv_id (ouGamma ousTopCofan.{u})) z
    rw [ousop_comp_apply] at h
    exact h
  have hq : (pval p ≫ (ouGamma ousTopCofan.{u}).hom).unop.toLinearMap
        ((ouGamma ousTopCofan.{u}).inv.unop.toLinearMap z)
      = (pval p).unop.toLinearMap ((ouGamma ousTopCofan.{u}).hom.unop.toLinearMap
          ((ouGamma ousTopCofan.{u}).inv.unop.toLinearMap z)) :=
    ousop_comp_apply (pval p) (ouGamma ousTopCofan.{u}).hom _
  have hpq : (ouPredEquiv ousTopCofan.{u} (op X) p)
      = pval p ≫ (ouGamma ousTopCofan.{u}).hom := rfl
  have h1 : (pval p).unop.toLinearMap z
      = (ouPredEquiv ousTopCofan.{u} (op X) p).unop.toLinearMap
          ((ouGamma ousTopCofan.{u}).inv.unop.toLinearMap z) := by
    rw [hpq, hq, hz]
  rw [h1, ous_hom_apply_effect, ← ous_pred_effect_val]

/-- **If the states of `X` are jointly epic then they separate its points.**
Given `x ≠ y` that no state separates, shrink `d = x - y` by a positive `c`
until `c · d` lies between `-½ · 1` and `½ · 1` (the order-unit axiom, then
divide); then `½ · 1 + c · d` and `½ · 1` are two distinct effects, hence two
distinct predicates, on which every state agrees, contradicting joint
epicity. -/
theorem ous_separatingPoints_of_separatingStatesAt (X : OUS.{u})
    (h : SeparatingStatesAt (Par.of (op X))) : OUSSeparatingPoints X := by
  intro x y hxy
  by_contra hne
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨n, hn⟩ := ou_exists_le_smul_unit (x - y)
  obtain ⟨m, hm⟩ := ou_exists_le_smul_unit (-(x - y))
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set N : ℝ := (n : ℝ) + (m : ℝ) + 1 with hN
  have hNpos : 0 < N := by rw [hN]; linarith
  set c : ℝ := (2 * N)⁻¹ with hc
  have hcpos : 0 < c := by
    rw [hc]
    exact inv_pos.mpr (by linarith)
  have hshrink : ∀ (z : X.carrier) (k : ℝ), k ≤ N → z ≤ k • ouUnit X.carrier →
      c • z ≤ (2 : ℝ)⁻¹ • ouUnit X.carrier := by
    intro z k hkN hk
    have h1 : c • z ≤ c • (k • ouUnit X.carrier) :=
      ou_smul_le_smul (le_of_lt hcpos) hk
    rw [smul_smul] at h1
    refine h1.trans (ou_smul_unit_mono ?_)
    have h2 : c * k ≤ c * N := mul_le_mul_of_nonneg_left hkN (le_of_lt hcpos)
    have h3 : c * N = (2 : ℝ)⁻¹ := by
      rw [hc]
      field_simp
    linarith
  have hd1 : c • (x - y) ≤ (2 : ℝ)⁻¹ • ouUnit X.carrier :=
    hshrink _ (n : ℝ) (by rw [hN]; linarith) hn
  have hd2 : c • (-(x - y)) ≤ (2 : ℝ)⁻¹ • ouUnit X.carrier :=
    hshrink _ (m : ℝ) (by rw [hN]; linarith) hm
  set e : X.carrier := (2 : ℝ)⁻¹ • ouUnit X.carrier + c • (x - y) with he
  have he0 : (0 : X.carrier) ≤ e := by
    have h1 : -(c • (x - y)) ≤ (2 : ℝ)⁻¹ • ouUnit X.carrier := by
      rwa [smul_neg] at hd2
    have h3 := add_le_add_left (neg_le.mp h1) ((2 : ℝ)⁻¹ • ouUnit X.carrier)
    rw [neg_add_cancel] at h3
    rw [he, add_comm]
    exact h3
  have hhalf : (2 : ℝ)⁻¹ • ouUnit X.carrier + (2 : ℝ)⁻¹ • ouUnit X.carrier
      = ouUnit X.carrier := by
    rw [← add_smul]
    norm_num
  have he1 : e ≤ ouUnit X.carrier := by
    have h3 := add_le_add_left hd1 ((2 : ℝ)⁻¹ • ouUnit X.carrier)
    rw [hhalf] at h3
    rw [he, add_comm]
    exact h3
  have hf0 : (0 : X.carrier) ≤ (2 : ℝ)⁻¹ • ouUnit X.carrier :=
    ou_smul_unit_nonneg (by norm_num)
  have hf1 : (2 : ℝ)⁻¹ • ouUnit X.carrier ≤ ouUnit X.carrier := by
    have h1 : (2 : ℝ)⁻¹ • ouUnit X.carrier ≤ (1 : ℝ) • ouUnit X.carrier :=
      ou_smul_unit_mono (by norm_num)
    rwa [one_smul] at h1
  have hcd : c • (x - y) ≠ 0 := by
    intro hz
    refine hd ?_
    have h1 : c⁻¹ • (c • (x - y)) = x - y := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hcpos), one_smul]
    rw [← h1, hz, smul_zero]
  have hene : e ≠ (2 : ℝ)⁻¹ • ouUnit X.carrier := by
    intro hEq
    refine hcd ?_
    have h5 : (2 : ℝ)⁻¹ • ouUnit X.carrier + c • (x - y)
        = (2 : ℝ)⁻¹ • ouUnit X.carrier + 0 := by
      rw [add_zero]
      exact hEq
    exact add_left_cancel h5
  set p₁ : Pred (Par.of (op X)) := (ous_pred_effect X).symm ⟨e, he0, he1⟩ with hp₁
  set p₂ : Pred (Par.of (op X)) :=
    (ous_pred_effect X).symm ⟨(2 : ℝ)⁻¹ • ouUnit X.carrier, hf0, hf1⟩ with hp₂
  have hE₁ : ((ous_pred_effect X p₁).1 : X.carrier) = e :=
    congrArg Subtype.val ((ous_pred_effect X).apply_symm_apply ⟨e, he0, he1⟩)
  have hE₂ : ((ous_pred_effect X p₂).1 : X.carrier)
      = (2 : ℝ)⁻¹ • ouUnit X.carrier :=
    congrArg Subtype.val ((ous_pred_effect X).apply_symm_apply
      ⟨(2 : ℝ)⁻¹ • ouUnit X.carrier, hf0, hf1⟩)
  have hpne : p₁ ≠ p₂ := by
    intro hEq
    refine hene ?_
    rw [← hE₁, ← hE₂, hEq]
  refine hpne (h p₁ p₂ fun ω => ?_)
  refine (ous_stat_comp_iff X p₁ p₂ ω).mpr fun z => ?_
  have hψd : (ous_stat_state X ω).1 (x - y) = 0 := by
    rw [map_sub, hxy (ous_stat_state X ω), sub_self]
  have hz2 : (ous_stat_state X ω).1 (c • (x - y)) = 0 := by
    rw [map_smul, hψd, smul_zero]
  have hee : (ous_stat_state X ω).1 e
      = (ous_stat_state X ω).1 ((2 : ℝ)⁻¹ • ouUnit X.carrier) := by
    rw [he, map_add, hz2, add_zero]
  have hψ : ∀ (a b : ℝ) (v w : X.carrier),
      (ous_stat_state X ω).1 v = (ous_stat_state X ω).1 w →
      (ous_stat_state X ω).1 (a • v + b • (X.unit - v))
        = (ous_stat_state X ω).1 (a • w + b • (X.unit - w)) := by
    intro a b v w hvw
    rw [map_add, map_add, map_smul, map_smul, map_smul, map_smul, map_sub,
      map_sub, hvw]
  rw [ous_pred_apply, ous_pred_apply, hE₁, hE₂]
  exact hψ _ _ e ((2 : ℝ)⁻¹ • ouUnit X.carrier) hee

/-- **190IV.1's parenthetical, in the form in which it is true**: the states
of a single order unit space are separating exactly when the space is
*almost* archimedean.  (As printed the condition is archimedeanness, which is
strictly stronger — see `ous_separating_states_not_archimedean`.) -/
theorem ous_separatingStatesAt_iff_almostArchimedean (X : OUS.{u}) :
    SeparatingStatesAt (Par.of (op X)) ↔ OUSAlmostArchimedean X.carrier :=
  ⟨fun h => ous_almostArchimedean_of_separatingPoints X
      (ous_separatingPoints_of_separatingStatesAt X h),
    fun h => ous_separatingStatesAt_of_points X
      (ous_separatingPoints_of_almostArchimedean X h)⟩

/-- Joint epicity of the states of `X` is exactly separation of its
points. -/
theorem ous_separatingStatesAt_iff_points (X : OUS.{u}) :
    SeparatingStatesAt (Par.of (op X)) ↔ OUSSeparatingPoints X :=
  ⟨ous_separatingPoints_of_separatingStatesAt X,
    ous_separatingStatesAt_of_points X⟩

/-! ### `ousAlm`: almost archimedean, not archimedean -/

/-- `ℝ²` with positive cone `{0} ∪ {(a,b) : 0 < a, 0 ≤ b}` and order unit
`(1,1)`: the counterexample to 190IV.1's parenthetical.  A plain `def`, not
an `abbrev`, so that instance search does not reach `ULift`'s own
(coordinatewise) order. -/
def ousAlm : Type u := ULift.{u} (ℝ × ℝ)

instance : AddCommGroup ousAlm.{u} :=
  inferInstanceAs (AddCommGroup (ULift.{u} (ℝ × ℝ)))

instance : Module ℝ ousAlm.{u} :=
  inferInstanceAs (Module ℝ (ULift.{u} (ℝ × ℝ)))

/-- A point of `ousAlm`. -/
def ousAlmPt (a b : ℝ) : ousAlm.{u} := ULift.up (a, b)

/-- The underlying pair of a point of `ousAlm`. -/
def ousAlmDown (x : ousAlm.{u}) : ℝ × ℝ := ULift.down x

@[simp] theorem ousAlmDown_pt (a b : ℝ) :
    ousAlmDown (ousAlmPt.{u} a b) = (a, b) := rfl

theorem ousAlmDown_injective {x y : ousAlm.{u}} (h : ousAlmDown x = ousAlmDown y) :
    x = y := ULift.down_injective h

/-- The order of `ousAlm`: `x ≤ y` iff they are equal or `x` is strictly
below `y` in the first coordinate and below in the second. -/
instance ousAlmPartialOrder : PartialOrder ousAlm.{u} where
  le x y := ousAlmDown x = ousAlmDown y ∨
    ((ousAlmDown x).1 < (ousAlmDown y).1 ∧ (ousAlmDown x).2 ≤ (ousAlmDown y).2)
  le_refl _ := Or.inl rfl
  le_trans x y z hxy hyz := by
    rcases hxy with h1 | ⟨h1, h1'⟩
    · rcases hyz with h2 | ⟨h2, h2'⟩
      · exact Or.inl (h1.trans h2)
      · exact Or.inr ⟨by rw [h1]; exact h2, by rw [h1]; exact h2'⟩
    · rcases hyz with h2 | ⟨h2, h2'⟩
      · exact Or.inr ⟨by rw [← h2]; exact h1, by rw [← h2]; exact h1'⟩
      · exact Or.inr ⟨lt_trans h1 h2, le_trans h1' h2'⟩
  le_antisymm x y hxy hyx := by
    rcases hxy with h1 | ⟨h1, _⟩
    · exact ousAlmDown_injective h1
    · rcases hyx with h2 | ⟨h2, _⟩
      · exact (ousAlmDown_injective h2).symm
      · exact absurd (lt_trans h1 h2) (lt_irrefl _)

/-- The order of `ousAlm`, unfolded. -/
theorem ousAlm_le_iff (x y : ousAlm.{u}) :
    x ≤ y ↔ ousAlmDown x = ousAlmDown y ∨
      ((ousAlmDown x).1 < (ousAlmDown y).1 ∧ (ousAlmDown x).2 ≤ (ousAlmDown y).2) :=
  Iff.rfl

/-- `ousAlm` is an order unit space with unit `(1,1)`: `(a,b) ≤ n · (1,1)`
for any `n` above both coordinates. -/
instance ousAlmOrderUnitSpace : OrderUnitSpace ousAlm.{u} where
  add_le_add_left x y h z := by
    rcases h with h1 | ⟨h1, h1'⟩
    · refine Or.inl ?_
      show ousAlmDown x + ousAlmDown z = ousAlmDown y + ousAlmDown z
      rw [h1]
    · have e1 : (ousAlmDown x).1 < (ousAlmDown y).1 := h1
      have e2 : (ousAlmDown x).2 ≤ (ousAlmDown y).2 := h1'
      refine Or.inr ⟨?_, ?_⟩
      · show (ousAlmDown x).1 + (ousAlmDown z).1 < (ousAlmDown y).1 + (ousAlmDown z).1
        linarith
      · show (ousAlmDown x).2 + (ousAlmDown z).2 ≤ (ousAlmDown y).2 + (ousAlmDown z).2
        linarith
  smul_nonneg {r} {x} hr hx := by
    rcases eq_or_lt_of_le hr with hr0 | hr0
    · refine Or.inl ?_
      show (0 : ℝ × ℝ) = r • ousAlmDown x
      rw [← hr0, zero_smul]
    · rcases hx with h1 | ⟨h1, h1'⟩
      · refine Or.inl ?_
        have h2 : (0 : ℝ × ℝ) = ousAlmDown x := h1
        show (0 : ℝ × ℝ) = r • ousAlmDown x
        rw [← h2, smul_zero]
      · have e1 : (0 : ℝ) < (ousAlmDown x).1 := h1
        have e2 : (0 : ℝ) ≤ (ousAlmDown x).2 := h1'
        refine Or.inr ⟨?_, ?_⟩
        · show (0 : ℝ) < r * (ousAlmDown x).1
          exact mul_pos hr0 e1
        · show (0 : ℝ) ≤ r * (ousAlmDown x).2
          exact mul_nonneg (le_of_lt hr0) e2
  unit := ousAlmPt 1 1
  exists_le_smul_unit x := by
    refine ⟨⌈max (ousAlmDown x).1 (ousAlmDown x).2⌉₊ + 1, Or.inr ⟨?_, ?_⟩⟩
    · show (ousAlmDown x).1
        < ((⌈max (ousAlmDown x).1 (ousAlmDown x).2⌉₊ + 1 : ℕ) : ℝ) * 1
      have h := Nat.le_ceil (max (ousAlmDown x).1 (ousAlmDown x).2)
      have h2 := le_max_left (ousAlmDown x).1 (ousAlmDown x).2
      push_cast
      linarith
    · show (ousAlmDown x).2
        ≤ ((⌈max (ousAlmDown x).1 (ousAlmDown x).2⌉₊ + 1 : ℕ) : ℝ) * 1
      have h := Nat.le_ceil (max (ousAlmDown x).1 (ousAlmDown x).2)
      have h2 := le_max_right (ousAlmDown x).1 (ousAlmDown x).2
      push_cast
      linarith

/-- The order unit of `ousAlm` is `(1,1)`. -/
theorem ousAlm_unit : ouUnit ousAlm.{u} = ousAlmPt 1 1 := rfl

/-- `ousAlm`, as an object of `OUS`. -/
abbrev ousAlmObj : OUS.{u} := OUS.of ousAlm.{u}

/-- Both coordinates of an element below `ε · (1,1)` are at most `ε`. -/
theorem ousAlm_coords_le {x : ousAlm.{u}} {ε : ℝ}
    (h : x ≤ ε • ouUnit ousAlm.{u}) :
    (ousAlmDown x).1 ≤ ε ∧ (ousAlmDown x).2 ≤ ε := by
  rcases h with h | ⟨h, h'⟩
  · have e1 : (ousAlmDown x).1 = ε * 1 := congrArg Prod.fst h
    have e2 : (ousAlmDown x).2 = ε * 1 := congrArg Prod.snd h
    constructor
    · linarith
    · linarith
  · have e1 : (ousAlmDown x).1 < ε * 1 := h
    have e2 : (ousAlmDown x).2 ≤ ε * 1 := h'
    exact ⟨by linarith, by linarith⟩

/-- `ousAlm` **is** almost archimedean: both coordinates of an infinitesimal
element are squeezed to `0`. -/
theorem ousAlm_almostArchimedean : OUSAlmostArchimedean ousAlm.{u} := by
  intro x hx
  have hle : ∀ ε : ℝ, 0 < ε → (ousAlmDown x).1 ≤ ε ∧ (ousAlmDown x).2 ≤ ε :=
    fun ε hε => ousAlm_coords_le (hx ε hε).1
  have hge : ∀ ε : ℝ, 0 < ε → -(ousAlmDown x).1 ≤ ε ∧ -(ousAlmDown x).2 ≤ ε := by
    intro ε hε
    have h := ousAlm_coords_le (hx ε hε).2
    have e1 : (ousAlmDown (-x)).1 = -(ousAlmDown x).1 := rfl
    have e2 : (ousAlmDown (-x)).2 = -(ousAlmDown x).2 := rfl
    rw [e1, e2] at h
    exact h
  have k1 : (ousAlmDown x).1 ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using (hle ε hε).1
  have k2 : (ousAlmDown x).2 ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using (hle ε hε).2
  have k3 : -(ousAlmDown x).1 ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using (hge ε hε).1
  have k4 : -(ousAlmDown x).2 ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using (hge ε hε).2
  refine ousAlmDown_injective (Prod.ext ?_ ?_)
  · show (ousAlmDown x).1 = 0
    linarith
  · show (ousAlmDown x).2 = 0
    linarith

/-- `ousAlm` is **not archimedean**: `(0,-1) ≤ ε · (1,1)` for every `ε > 0`
— the first coordinate `0` is strictly below `ε` — yet `(0,-1) ≰ 0`, the
first coordinates being equal and the second not below. -/
theorem ousAlm_not_archimedean : ¬ OUSArchimedean ousAlm.{u} := by
  intro h
  have h1 : (ousAlmPt.{u} 0 (-1)) ≤ 0 := by
    refine h _ fun ε hε => ?_
    refine Or.inr ⟨?_, ?_⟩
    · show (0 : ℝ) < ε * 1
      linarith
    · show (-1 : ℝ) ≤ ε * 1
      linarith
  rcases h1 with h2 | ⟨h2, _⟩
  · have h3 : (-1 : ℝ) = 0 := congrArg Prod.snd h2
    norm_num at h3
  · have h3 : (0 : ℝ) < 0 := h2
    exact lt_irrefl _ h3

/-- **190IV.1's parenthetical is false as printed**: the states of `ousAlm`
*are* separating, and `ousAlm` is *not* archimedean.  What separating states
amount to is almost archimedeanness
(`ous_separatingStatesAt_iff_almostArchimedean`); the two part exactly here,
`ousAlm` having no non-zero infinitesimal but a positive cone that is not its
own archimedean closure — `(0,1)` is a limit of positives without being
positive.  See the ERRATA row on 190IV.1. -/
theorem ous_separating_states_not_archimedean :
    ∃ X : OUS.{u}, SeparatingStatesAt (Par.of (op X)) ∧
      ¬ OUSArchimedean X.carrier :=
  ⟨ousAlmObj.{u},
    ous_separatingStatesAt_of_points ousAlmObj.{u}
      (ous_separatingPoints_of_almostArchimedean ousAlmObj.{u}
        ousAlm_almostArchimedean.{u}),
    ousAlm_not_archimedean.{u}⟩

end OUSExample

/-! # 190IV.2: the effectus `OUGᵒᵖ` -/

section OUGExample

local instance instHasFiniteCoproductsParOUG :
    HasFiniteCoproducts (Par OUG.{u}ᵒᵖ) := parHasFiniteCoproducts

/-- The final object of `OUGᵒᵖ`, read as an order unit group. -/
abbrev ougTopO : OUG.{u} := (⊤_ OUG.{u}ᵒᵖ).unop

/-- The unique map out of `ougTopO` (it is initial in `OUG`). -/
def ougTopTo (G : OUG.{u}) : ougTopO.{u} ⟶ G := (terminal.from (op G)).unop

/-- `ougTopO` is initial in `OUG`: there is at most one map out of it. -/
theorem ougTopO_hom_unique {G : OUG.{u}} (f g : ougTopO.{u} ⟶ G) : f = g :=
  Quiver.Hom.op_inj (terminalIsTerminal.hom_ext (C := OUG.{u}ᵒᵖ) f.op g.op)

/-- The unique map `ℤᵤ ⟶ ougTopO`. -/
def ougUnitTop : ougScal.{u} ⟶ ougTopO.{u} := ougUnitMap ougTopO.{u}

/-- `ℤᵤ ⟶ ougTopO ⟶ ℤᵤ` is the identity. -/
theorem ougTop_inv₁ : ougUnitTop.{u} ≫ ougTopTo ougScal.{u} = 𝟙 ougScal.{u} :=
  (ougUnitMap_unique _).trans (ougUnitMap_unique _).symm

/-- `ougTopO ⟶ ℤᵤ ⟶ ougTopO` is the identity. -/
theorem ougTop_inv₂ : ougTopTo ougScal.{u} ≫ ougUnitTop.{u} = 𝟙 ougTopO.{u} :=
  ougTopO_hom_unique _ _

/-- The round trip `ougTopO ⟶ ℤᵤ ⟶ ougTopO`. -/
theorem oug_top_round {K : OUG.{u}} (a : K ⟶ ougTopO.{u}) :
    (a ≫ ougTopTo ougScal.{u}) ≫ ougUnitTop.{u} = a := by
  rw [Category.assoc, ougTop_inv₂, Category.comp_id]

/-- Two maps into `ougTopO` agreeing after the isomorphism `ougTopO ≅ ℤᵤ`
are equal. -/
theorem oug_hom_to_top_ext {K : OUG.{u}} {a b : K ⟶ ougTopO.{u}}
    (hab : a ≫ ougTopTo ougScal.{u} = b ≫ ougTopTo ougScal.{u}) : a = b := by
  rw [← oug_top_round a, hab, oug_top_round b]

/-- The first component of a pairing. -/
theorem ougPair_fst {K G H : OUG.{u}} (f : K ⟶ G) (g : K ⟶ H) :
    ougPair f g ≫ ougFst G H = f := oug_hom_ext fun _ => rfl

/-- The second component of a pairing. -/
theorem ougPair_snd {K G H : OUG.{u}} (f : K ⟶ G) (g : K ⟶ H) :
    ougPair f g ≫ ougSnd G H = g := oug_hom_ext fun _ => rfl

/-- A map into a product is the pairing of its two components. -/
theorem ougPair_eta {K G H : OUG.{u}} (m : K ⟶ G.prod H) :
    ougPair (m ≫ ougFst G H) (m ≫ ougSnd G H) = m :=
  oug_hom_ext fun _ => rfl

/-- `ℤ² = ℤᵤ × ℤᵤ`: the apex of the two-point presentation of `⊤ + ⊤`. -/
abbrev ougS : OUG.{u}ᵒᵖ := op (ougScal.{u}.prod ougScal.{u})

/-- The first point of `⊤ + ⊤` in `OUGᵒᵖ`. -/
def ougI₁ : (⊤_ OUG.{u}ᵒᵖ) ⟶ ougS.{u} :=
  Quiver.Hom.op (ougFst ougScal.{u} ougScal.{u} ≫ ougUnitTop.{u})

/-- The second point of `⊤ + ⊤` in `OUGᵒᵖ`. -/
def ougI₂ : (⊤_ OUG.{u}ᵒᵖ) ⟶ ougS.{u} :=
  Quiver.Hom.op (ougSnd ougScal.{u} ougScal.{u} ≫ ougUnitTop.{u})

/-- The swap of `ℤ²`, which will be the orthosupplement. -/
def ougSwap : ougS.{u} ⟶ ougS.{u} :=
  Quiver.Hom.op (ougPair (ougSnd ougScal.{u} ougScal.{u})
    (ougFst ougScal.{u} ougScal.{u}))

/-- `⊤ + ⊤` in `OUGᵒᵖ` is `ℤ²`. -/
def ougTopCofan : IsColimit (BinaryCofan.mk ougI₁.{u} ougI₂.{u}) :=
  BinaryCofan.IsColimit.mk _
    (fun {_} u v => Quiver.Hom.op
      (ougPair (u.unop ≫ ougTopTo ougScal.{u}) (v.unop ≫ ougTopTo ougScal.{u})))
    (fun {_} u v => by
      refine Quiver.Hom.unop_inj ?_
      show ougPair (u.unop ≫ ougTopTo ougScal.{u}) (v.unop ≫ ougTopTo ougScal.{u})
          ≫ (ougFst _ _ ≫ ougUnitTop.{u}) = u.unop
      rw [← Category.assoc, ougPair_fst, Category.assoc, ougTop_inv₂,
        Category.comp_id])
    (fun {_} u v => by
      refine Quiver.Hom.unop_inj ?_
      show ougPair (u.unop ≫ ougTopTo ougScal.{u}) (v.unop ≫ ougTopTo ougScal.{u})
          ≫ (ougSnd _ _ ≫ ougUnitTop.{u}) = v.unop
      rw [← Category.assoc, ougPair_snd, Category.assoc, ougTop_inv₂,
        Category.comp_id])
    (fun {W} u v m h₁ h₂ => by
      obtain ⟨m, rfl⟩ : ∃ m' : ougS.{u} ⟶ W, m' = m := ⟨m, rfl⟩
      refine Quiver.Hom.unop_inj ?_
      have k₁ : m.unop ≫ (ougFst ougScal.{u} ougScal.{u} ≫ ougUnitTop.{u})
          = u.unop := congrArg Quiver.Hom.unop h₁
      have k₂ : m.unop ≫ (ougSnd ougScal.{u} ougScal.{u} ≫ ougUnitTop.{u})
          = v.unop := congrArg Quiver.Hom.unop h₂
      have e₁ : m.unop ≫ ougFst ougScal.{u} ougScal.{u}
          = u.unop ≫ ougTopTo ougScal.{u} := by
        rw [← k₁, Category.assoc, Category.assoc, ougTop_inv₁, Category.comp_id]
      have e₂ : m.unop ≫ ougSnd ougScal.{u} ougScal.{u}
          = v.unop ≫ ougTopTo ougScal.{u} := by
        rw [← k₂, Category.assoc, Category.assoc, ougTop_inv₁, Category.comp_id]
      rw [← e₁, ← e₂, ougPair_eta]
      rfl)

/-- The swap of `ℤ²` exchanges the two points of `⊤ + ⊤`. -/
theorem ougI₁_swap : ougI₁.{u} ≫ ougSwap.{u} = ougI₂.{u} := by
  refine Quiver.Hom.unop_inj ?_
  show ougPair (ougSnd ougScal.{u} ougScal.{u}) (ougFst ougScal.{u} ougScal.{u})
      ≫ (ougFst _ _ ≫ ougUnitTop.{u}) = ougSnd _ _ ≫ ougUnitTop.{u}
  rw [← Category.assoc, ougPair_fst]

/-- The swap of `ℤ²` exchanges the two points of `⊤ + ⊤`. -/
theorem ougI₂_swap : ougI₂.{u} ≫ ougSwap.{u} = ougI₁.{u} := by
  refine Quiver.Hom.unop_inj ?_
  show ougPair (ougSnd ougScal.{u} ougScal.{u}) (ougFst ougScal.{u} ougScal.{u})
      ≫ (ougSnd _ _ ≫ ougUnitTop.{u}) = ougFst _ _ ≫ ougUnitTop.{u}
  rw [← Category.assoc, ougPair_snd]

/-- A positive unital homomorphism out of `ℤ²` sends `(0,1)` to `1 - φ(1,0)`. -/
theorem oug_hom_compl (G : OUG.{u}) (φ : ougScal.{u}.prod ougScal.{u} ⟶ G) :
    φ.toAddHom ((0 : ULift.{u} ℤ), (1 : ULift.{u} ℤ))
      = G.unit - φ.toAddHom ((1 : ULift.{u} ℤ), (0 : ULift.{u} ℤ)) := by
  have h : ((1 : ULift.{u} ℤ), (0 : ULift.{u} ℤ))
      + ((0 : ULift.{u} ℤ), (1 : ULift.{u} ℤ))
      = (ougScal.{u}.prod ougScal.{u}).unit := by
    refine Prod.ext ?_ ?_ <;> apply ULift.down_injective <;> simp
  have h2 : φ.toAddHom ((1 : ULift.{u} ℤ), (0 : ULift.{u} ℤ))
      + φ.toAddHom ((0 : ULift.{u} ℤ), (1 : ULift.{u} ℤ)) = G.unit := by
    rw [← map_add, h, φ.map_unit']
  rw [← h2]; abel

/-- A positive unital homomorphism out of `ℤ²` is `(a,b) ↦ a·x + b·(1-x)`
for `x = φ(1,0)`. -/
theorem ougHom_apply (G : OUG.{u}) (φ : ougScal.{u}.prod ougScal.{u} ⟶ G)
    (ab : ULift.{u} ℤ × ULift.{u} ℤ) :
    φ.toAddHom ab
      = ab.1.down • φ.toAddHom ((1 : ULift.{u} ℤ), (0 : ULift.{u} ℤ))
        + ab.2.down • (G.unit
          - φ.toAddHom ((1 : ULift.{u} ℤ), (0 : ULift.{u} ℤ))) := by
  have hdec : ab = ab.1.down • ((1 : ULift.{u} ℤ), (0 : ULift.{u} ℤ))
      + ab.2.down • ((0 : ULift.{u} ℤ), (1 : ULift.{u} ℤ)) := by
    refine Prod.ext ?_ ?_ <;> apply ULift.down_injective <;> simp
  conv_lhs => rw [hdec]
  rw [map_add, AddMonoidHom.map_zsmul, AddMonoidHom.map_zsmul, oug_hom_compl G φ]

/-- `(1,0)` is a positive element of `ℤ²`. -/
theorem oug_one_zero_nonneg :
    (0 : ULift.{u} ℤ × ULift.{u} ℤ) ≤ ((1 : ULift.{u} ℤ), (0 : ULift.{u} ℤ)) :=
  Prod.le_def.mpr ⟨show (0:ℤ) ≤ 1 from zero_le_one, le_refl _⟩

/-- **190IV.2** (eff.tex:2162, Examples): positive unital homomorphisms
`ℤ² ⟶ G` of `OUG` are the
elements `0 ≤ x ≤ 1` of `G`, by `φ ↦ φ(1,0)`. -/
def ougHomEffectEquiv (G : OUG.{u}) :
    (ougScal.{u}.prod ougScal.{u} ⟶ G)
      ≃ {x : G.carrier // 0 ≤ x ∧ x ≤ G.unit} where
  toFun φ := ⟨φ.toAddHom ((1 : ULift.{u} ℤ), (0 : ULift.{u} ℤ)), by
    refine ⟨φ.map_nonneg' _ oug_one_zero_nonneg.{u}, ?_⟩
    have h : ((1 : ULift.{u} ℤ), (0 : ULift.{u} ℤ))
        ≤ (ougScal.{u}.prod ougScal.{u}).unit :=
      Prod.le_def.mpr ⟨le_refl _, show (0:ℤ) ≤ 1 from zero_le_one⟩
    exact (φ.mono h).trans (le_of_eq φ.map_unit')⟩
  invFun x :=
    { toAddHom := AddMonoidHom.mk'
        (fun p => p.1.down • x.1 + p.2.down • (G.unit - x.1))
        (fun a b => by
          show (a.1.down + b.1.down) • x.1
              + (a.2.down + b.2.down) • (G.unit - x.1)
            = (a.1.down • x.1 + a.2.down • (G.unit - x.1))
              + (b.1.down • x.1 + b.2.down • (G.unit - x.1))
          rw [add_zsmul, add_zsmul]
          abel)
      map_nonneg' := fun p hp => by
        obtain ⟨hp1, hp2⟩ := Prod.le_def.mp hp
        have h1 : (0:ℤ) ≤ p.1.down := hp1
        have h2 : (0:ℤ) ≤ p.2.down := hp2
        show (0 : G.carrier) ≤ p.1.down • x.1 + p.2.down • (G.unit - x.1)
        have e1 : (0 : G.carrier) ≤ p.1.down • x.1 :=
          oug_zsmul_nonneg x.2.1 h1
        have e2 : (0 : G.carrier) ≤ p.2.down • (G.unit - x.1) :=
          oug_zsmul_nonneg (sub_nonneg.mpr x.2.2) h2
        simpa using add_le_add e1 e2
      map_unit' := by
        show (1:ℤ) • x.1 + (1:ℤ) • (G.unit - x.1) = G.unit
        rw [one_zsmul, one_zsmul]
        abel }
  left_inv φ := oug_hom_ext fun p => (ougHom_apply G φ p).symm
  right_inv x := by
    refine Subtype.ext ?_
    show (1:ℤ) • x.1 + (0:ℤ) • (G.unit - x.1) = x.1
    rw [one_zsmul, zero_zsmul, add_zero]

/-- Passing to the opposite category. -/
def ougOpEquiv (G : OUG.{u}) :
    ((op G : OUG.{u}ᵒᵖ) ⟶ ougS.{u}) ≃ (ougScal.{u}.prod ougScal.{u} ⟶ G) where
  toFun f := f.unop
  invFun g := Quiver.Hom.op g
  left_inv _ := rfl
  right_inv _ := rfl

/-- **190IV.2** (eff.tex:2162, Examples): the predicates on an order unit
group `G` are the elements `0 ≤ x ≤ 1`. -/
def oug_pred_effect (G : OUG.{u}) :
    Pred (Par.of (op G)) ≃ {x : G.carrier // 0 ≤ x ∧ x ≤ G.unit} :=
  ((ouPredEquiv ougTopCofan.{u} (op G)).trans (ougOpEquiv G)).trans
    (ougHomEffectEquiv G)

/-- The effect attached to a predicate is the image of `(1,0)`. -/
theorem oug_pred_effect_val (G : OUG.{u}) (p : Pred (Par.of (op G))) :
    ((oug_pred_effect G p).1 : G.carrier)
      = (ouPredEquiv ougTopCofan.{u} (op G) p).unop.toAddHom
          ((1 : ULift.{u} ℤ), (0 : ULift.{u} ℤ)) := rfl

/-- The composite `ℤ² ⟶ ⊤ ⟶ G` through the first point is `n ↦ n · 1`
precomposed with the first projection. -/
theorem oug_from_i₁ (G : OUG.{u}) :
    terminal.from (op G) ≫ ougI₁.{u}
      = Quiver.Hom.op (ougFst ougScal.{u} ougScal.{u} ≫ ougUnitMap G) := by
  refine Quiver.Hom.unop_inj ?_
  show (ougFst ougScal.{u} ougScal.{u} ≫ ougUnitTop.{u}) ≫ ougTopTo G
      = ougFst ougScal.{u} ougScal.{u} ≫ ougUnitMap G
  rw [Category.assoc]
  exact congrArg (fun m => ougFst ougScal.{u} ougScal.{u} ≫ m)
    (ougUnitMap_unique (ougUnitTop.{u} ≫ ougTopTo G))

/-- The composite `ℤ² ⟶ ⊤ ⟶ G` through the second point is `n ↦ n · 1`
precomposed with the second projection. -/
theorem oug_from_i₂ (G : OUG.{u}) :
    terminal.from (op G) ≫ ougI₂.{u}
      = Quiver.Hom.op (ougSnd ougScal.{u} ougScal.{u} ≫ ougUnitMap G) := by
  refine Quiver.Hom.unop_inj ?_
  show (ougSnd ougScal.{u} ougScal.{u} ≫ ougUnitTop.{u}) ≫ ougTopTo G
      = ougSnd ougScal.{u} ougScal.{u} ≫ ougUnitMap G
  rw [Category.assoc]
  exact congrArg (fun m => ougSnd ougScal.{u} ougScal.{u} ≫ m)
    (ougUnitMap_unique (ougUnitTop.{u} ≫ ougTopTo G))

/-- **190IV.2** (eff.tex:2163, Examples): the truth predicate is the order
unit. -/
theorem oug_pred_effect_truth (G : OUG.{u}) :
    ((oug_pred_effect G (truth (Par.of (op G)))).1 : G.carrier) = G.unit := by
  rw [oug_pred_effect_val, ouPredEquiv_truth, oug_from_i₁]
  show (ougUnitMap G).toAddHom (1 : ULift.{u} ℤ) = G.unit
  rw [ougUnitMap_apply]
  exact one_zsmul _

/-- **190IV.2** (eff.tex:2163, Examples): the zero predicate is `0`. -/
theorem oug_pred_effect_zero (G : OUG.{u}) :
    ((oug_pred_effect G (0 : Pred (Par.of (op G)))).1 : G.carrier) = 0 := by
  rw [oug_pred_effect_val, ouPredEquiv_zero, oug_from_i₂]
  show (ougUnitMap G).toAddHom (0 : ULift.{u} ℤ) = 0
  rw [ougUnitMap_apply]
  exact zero_zsmul _

/-- **190IV.2** (eff.tex:2163, Examples): the orthosupplement is `1 - x`. -/
theorem oug_pred_effect_orth (G : OUG.{u}) (p : Pred (Par.of (op G))) :
    ((oug_pred_effect G (orth p)).1 : G.carrier)
      = G.unit - ((oug_pred_effect G p).1 : G.carrier) := by
  rw [oug_pred_effect_val, oug_pred_effect_val,
    ouPredEquiv_orth ougTopCofan.{u} ougSwap.{u} ougI₁_swap.{u} ougI₂_swap.{u}
      (op G) p]
  rw [← oug_hom_compl G (ouPredEquiv ougTopCofan.{u} (op G) p).unop]
  rfl

/-! ### The states of an order unit group -/

/-- Maps `G ⟶ ℤᵤ` of `OUG` are the unit-preserving positive homomorphisms
`G → ℤ`. -/
def ougHomStateEquiv (G : OUG.{u}) :
    (G ⟶ ougScal.{u})
      ≃ {f : G.carrier →+ ℤ // (∀ x, 0 ≤ x → 0 ≤ f x) ∧ f G.unit = 1} where
  toFun φ :=
    ⟨AddMonoidHom.mk' (fun x => (φ.toAddHom x).down)
       (fun x y => congrArg ULift.down (map_add φ.toAddHom x y)),
     fun x hx => φ.map_nonneg' x hx, congrArg ULift.down φ.map_unit'⟩
  invFun f :=
    { toAddHom := AddMonoidHom.mk' (fun x => ULift.up (f.1 x))
        (fun x y => congrArg ULift.up (map_add f.1 x y))
      map_nonneg' := fun x hx => f.2.1 x hx
      map_unit' := ULift.down_injective f.2.2 }
  left_inv _ := oug_hom_ext fun _ => rfl
  right_inv _ := Subtype.ext (AddMonoidHom.ext fun _ => rfl)

/-- `ougTopO ≅ ℤᵤ`, as a bijection on maps into it. -/
def ougHomTopEquiv (G : OUG.{u}) : (G ⟶ ougTopO.{u}) ≃ (G ⟶ ougScal.{u}) where
  toFun f := f ≫ ougTopTo ougScal.{u}
  invFun g := g ≫ ougUnitTop.{u}
  left_inv f := by
    show (f ≫ ougTopTo ougScal.{u}) ≫ ougUnitTop.{u} = f
    rw [Category.assoc, ougTop_inv₂, Category.comp_id]
  right_inv g := by
    show (g ≫ ougUnitTop.{u}) ≫ ougTopTo ougScal.{u} = g
    rw [Category.assoc, ougTop_inv₁, Category.comp_id]

/-- **190IV.2** (eff.tex:2165, Examples): the states on an order unit group
`G` are the unit-preserving positive homomorphisms `G → ℤ`. -/
def oug_stat_hom (G : OUG.{u}) :
    Stat (Par.of (op G))
      ≃ {f : G.carrier →+ ℤ // (∀ x, 0 ≤ x → 0 ≤ f x) ∧ f G.unit = 1} :=
  ((parStatEquiv (op G)).trans
    { toFun := fun f => f.unop
      invFun := fun g => Quiver.Hom.op g
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
    ((ougHomTopEquiv G).trans (ougHomStateEquiv G))

/-! ### The scalars of `OUGᵒᵖ` are the two-element effect monoid `2` -/

/-- Copy of `ExtensiveExamples.lean`'s `scalarsAreTwo_of_forall`, with the
conclusion written out inline: the two modules are siblings, so neither can
import the other's abbreviation `ScalarsAreTwo`. -/
theorem ouScalarsTwo_of_forall {D : Type u} [Category.{v} D]
    [HasFiniteCoproducts D] [∀ X Y : D, PCM (X ⟶ Y)] [FinPAC D]
    [EffectusPartialForm D]
    (hex : ∀ k : Scal D, k = 0 ∨ k = 1) (hne : (0 : Scal D) ≠ 1) :
    ∃ (φ : EffectMonoidHom (Scal D) Bool) (ψ : EffectMonoidHom Bool (Scal D)),
      (∀ k, ψ.toFun (φ.toFun k) = k) ∧ ∀ b, φ.toFun (ψ.toFun b) = b := by
  classical
  obtain ⟨φf, hφ0, hφ1⟩ : ∃ f : Scal D → Bool, f 0 = false ∧ f 1 = true := by
    refine ⟨fun k => if k = 1 then true else false, ?_, ?_⟩
    · simp [hne]
    · simp
  obtain ⟨ψf, hψ0, hψ1⟩ : ∃ g : Bool → Scal D, g false = 0 ∧ g true = 1 :=
    ⟨fun b => cond b 1 0, rfl, rfl⟩
  have hbne : ¬ ((true : Bool) = 0) := fun hh => Bool.noConfusion hh
  have hbcases : ∀ b : Bool, b = false ∨ b = true := by
    intro b; cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hnp : ¬ Perp (1 : Scal D) (1 : Scal D) := fun hh =>
    hne (EffectAlgebra.eq_zero_of_perp_one hh).symm
  have hnpb : ¬ Perp (true : Bool) (true : Bool) := fun hh =>
    hbne (EffectAlgebra.eq_zero_of_perp_one hh)
  have hzm : ∀ a : Scal D, (0 : Scal D) * a = 0 := fun a =>
    show a ≫ (0 : Scal D) = 0 from FinPAC.comp_zero a
  have hmz : ∀ a : Scal D, a * (0 : Scal D) = 0 := fun a =>
    show (0 : Scal D) ≫ a = 0 from FinPAC.zero_comp a
  have hbzm : ∀ b : Bool, (false : Bool) * b = false := by
    intro b; cases b <;> rfl
  have hbmz : ∀ b : Bool, b * (false : Bool) = false := by
    intro b; cases b <;> rfl
  have hbtt : (true : Bool) * true = true := rfl
  have hpfl : ∀ x : Bool, Perp (false : Bool) x := fun x => PCM.zero_perp x
  have hpfr : ∀ x : Bool, Perp x (false : Bool) := fun x => PCM.perp_zero x
  have hzol : ∀ x : Bool, ovee (false : Bool) x (hpfl x) = x := fun x =>
    PCM.zero_ovee x
  have hzor : ∀ x : Bool, ovee x (false : Bool) (hpfr x) = x := fun x =>
    PCM.ovee_zero x (hpfr x)
  have φperp : ∀ {a b : Scal D}, Perp a b → Perp (φf a) (φf b) := by
    intro a b hab
    rcases hex a with rfl | rfl
    · rw [hφ0]; exact hpfl _
    · rcases hex b with rfl | rfl
      · rw [hφ0]; exact hpfr _
      · exact absurd hab hnp
  have φovee : ∀ {a b : Scal D} (h : Perp a b),
      φf (ovee a b h) = ovee (φf a) (φf b) (φperp h) := by
    intro a b hab
    rcases hex a with rfl | rfl
    · rw [congrArg φf (PCM.zero_ovee (M := Scal D) b)]
      symm
      exact (PCM.ovee_congr hφ0 rfl (φperp hab) (hpfl (φf b))).trans (hzol (φf b))
    · rcases hex b with rfl | rfl
      · rw [congrArg φf (PCM.ovee_zero (1 : Scal D) hab)]
        symm
        exact (PCM.ovee_congr rfl hφ0 (φperp hab) (hpfr (φf 1))).trans
          (hzor (φf 1))
      · exact absurd hab hnp
  have φmul : ∀ a b : Scal D, φf (a * b) = φf a * φf b := by
    intro a b
    rcases hex a with rfl | rfl
    · rw [hzm, hφ0, hbzm]
    · rcases hex b with rfl | rfl
      · rw [hmz, hφ0, hφ1, hbmz]
      · rw [EffectMonoid.one_mul, hφ1, hbtt]
  have ψperp : ∀ {a b : Bool}, Perp a b → Perp (ψf a) (ψf b) := by
    intro a b hab
    rcases hbcases a with rfl | rfl
    · rw [hψ0]; exact PCM.zero_perp _
    · rcases hbcases b with rfl | rfl
      · rw [hψ0]; exact PCM.perp_zero _
      · exact absurd hab hnpb
  have ψovee : ∀ {a b : Bool} (h : Perp a b),
      ψf (ovee a b h) = ovee (ψf a) (ψf b) (ψperp h) := by
    intro a b hab
    rcases hbcases a with rfl | rfl
    · rw [congrArg ψf (hzol b)]
      symm
      exact (PCM.ovee_congr hψ0 rfl (ψperp hab) (PCM.zero_perp (ψf b))).trans
        (PCM.zero_ovee (ψf b))
    · rcases hbcases b with rfl | rfl
      · rw [congrArg ψf (hzor true)]
        symm
        exact (PCM.ovee_congr rfl hψ0 (ψperp hab) (PCM.perp_zero (ψf true))).trans
          (PCM.ovee_zero (ψf true) (PCM.perp_zero (ψf true)))
      · exact absurd hab hnpb
  have ψmul : ∀ a b : Bool, ψf (a * b) = ψf a * ψf b := by
    intro a b
    rcases hbcases a with rfl | rfl
    · rw [hbzm, hψ0, hzm]
    · rcases hbcases b with rfl | rfl
      · rw [hbmz, hψ0, hψ1, hmz]
      · rw [hbtt, hψ1, EffectMonoid.one_mul]
  refine ⟨⟨⟨⟨φf, φperp, φovee⟩, hφ1⟩, φmul⟩, ⟨⟨⟨ψf, ψperp, ψovee⟩, hψ1⟩, ψmul⟩,
    ?_, ?_⟩
  · intro k
    rcases hex k with rfl | rfl
    · show ψf (φf 0) = 0
      rw [hφ0, hψ0]
    · show ψf (φf 1) = 1
      rw [hφ1, hψ1]
  · intro b
    rcases hbcases b with rfl | rfl
    · show φf (ψf false) = false
      rw [hψ0, hφ0]
    · show φf (ψf true) = true
      rw [hψ1, hφ1]

/-- The scalars of `OUGᵒᵖ` are the positive unital homomorphisms `ℤ² ⟶ ℤ`. -/
def ougScalMapEquiv :
    Scal (Par OUG.{u}ᵒᵖ) ≃ (ougScal.{u}.prod ougScal.{u} ⟶ ougScal.{u}) :=
  ((ouPredEquiv ougTopCofan.{u} (⊤_ OUG.{u}ᵒᵖ)).trans
    { toFun := fun f => f.unop
      invFun := fun g => Quiver.Hom.op g
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
    (ougHomTopEquiv (ougScal.{u}.prod ougScal.{u}))

/-- The scalars of `OUGᵒᵖ` are `{0, 1} ⊆ ℤ`, as a bijection. -/
def ougScalEquivZ : Scal (Par OUG.{u}ᵒᵖ) ≃ {n : ℤ // 0 ≤ n ∧ n ≤ 1} :=
  (ougScalMapEquiv.{u}.trans (ougHomEffectEquiv ougScal.{u})).trans
    { toFun := fun y => ⟨y.1.down, y.2.1, y.2.2⟩
      invFun := fun r => ⟨ULift.up r.1, r.2.1, r.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The integer attached to a scalar of `OUGᵒᵖ`. -/
def ougScalV (k : Scal (Par OUG.{u}ᵒᵖ)) : ℤ := (ougScalEquivZ.{u} k).1

/-- A scalar of `OUGᵒᵖ` is determined by its integer. -/
theorem ougScalV_injective {k l : Scal (Par OUG.{u}ᵒᵖ)}
    (h : ougScalV k = ougScalV l) : k = l :=
  ougScalEquivZ.{u}.injective (Subtype.ext h)

/-- The integer of a scalar of `OUGᵒᵖ` lies in `{0, 1}`. -/
theorem ougScalV_bounds (k : Scal (Par OUG.{u}ᵒᵖ)) :
    0 ≤ ougScalV k ∧ ougScalV k ≤ 1 := (ougScalEquivZ.{u} k).2

/-- The scalar `1` is the first projection `ℤ² ⟶ ℤ`. -/
theorem ougScalMapEquiv_one :
    ougScalMapEquiv.{u} (1 : Scal (Par OUG.{u}ᵒᵖ))
      = ougFst ougScal.{u} ougScal.{u} := by
  show (ouPredEquiv ougTopCofan.{u} (⊤_ OUG.{u}ᵒᵖ)
      (truth (Par.of (⊤_ OUG.{u}ᵒᵖ)))).unop ≫ ougTopTo ougScal.{u} = _
  rw [ouPredEquiv_truth, par_terminal_self, Category.id_comp]
  show (ougFst ougScal.{u} ougScal.{u} ≫ ougUnitTop.{u}) ≫ ougTopTo ougScal.{u} = _
  rw [Category.assoc, ougTop_inv₁, Category.comp_id]

/-- The scalar `0` is the second projection `ℤ² ⟶ ℤ`. -/
theorem ougScalMapEquiv_zero :
    ougScalMapEquiv.{u} (0 : Scal (Par OUG.{u}ᵒᵖ))
      = ougSnd ougScal.{u} ougScal.{u} := by
  show (ouPredEquiv ougTopCofan.{u} (⊤_ OUG.{u}ᵒᵖ)
      (0 : Pred (Par.of (⊤_ OUG.{u}ᵒᵖ)))).unop ≫ ougTopTo ougScal.{u} = _
  rw [ouPredEquiv_zero, par_terminal_self, Category.id_comp]
  show (ougSnd ougScal.{u} ougScal.{u} ≫ ougUnitTop.{u}) ≫ ougTopTo ougScal.{u} = _
  rw [Category.assoc, ougTop_inv₁, Category.comp_id]

/-- The scalar `1` has integer `1`. -/
theorem ougScalV_one : ougScalV (1 : Scal (Par OUG.{u}ᵒᵖ)) = 1 := by
  show ((ougScalMapEquiv.{u} 1).toAddHom
    ((1 : ULift.{u} ℤ), (0 : ULift.{u} ℤ))).down = 1
  rw [ougScalMapEquiv_one]
  rfl

/-- The scalar `0` has integer `0`. -/
theorem ougScalV_zero : ougScalV (0 : Scal (Par OUG.{u}ᵒᵖ)) = 0 := by
  show ((ougScalMapEquiv.{u} 0).toAddHom
    ((1 : ULift.{u} ℤ), (0 : ULift.{u} ℤ))).down = 0
  rw [ougScalMapEquiv_zero]
  rfl

/-- **190IV.2** (eff.tex:2160, Examples): `OUGᵒᵖ` **has the two-element
effect monoid `2` as scalars**.  A scalar is a positive unital homomorphism
`ℤ² ⟶ ℤ`, determined by the image `n` of `(1,0)`, which must satisfy
`0 ≤ n ≤ 1`; so there are exactly the two scalars `0` and `1`.

The statement is `ExtensiveExamples.lean`'s `ScalarsAreTwo (Par OUG.{u}ᵒᵖ)`
written out inline: that file is a sibling leaf module of this one, so the
abbreviation cannot be shared. -/
theorem oug_scalars_two :
    ∃ (φ : EffectMonoidHom (Scal (Par OUG.{u}ᵒᵖ)) Bool)
      (ψ : EffectMonoidHom Bool (Scal (Par OUG.{u}ᵒᵖ))),
      (∀ k, ψ.toFun (φ.toFun k) = k) ∧ ∀ b, φ.toFun (ψ.toFun b) = b := by
  refine ouScalarsTwo_of_forall ?_ ?_
  · intro k
    obtain ⟨h0, h1⟩ := ougScalV_bounds.{u} k
    have hk : ougScalV k = 0 ∨ ougScalV k = 1 := by omega
    rcases hk with hk | hk
    · exact Or.inl (ougScalV_injective (hk.trans ougScalV_zero.symm))
    · exact Or.inr (ougScalV_injective (hk.trans ougScalV_one.symm))
  · intro hz
    have h := congrArg ougScalV hz
    rw [ougScalV_zero, ougScalV_one] at h
    exact absurd h (by norm_num)

/-! ### `ℤ` with order unit `2`: `OUGᵒᵖ` has no separating states -/

/-- `ℤ` with the usual order but with the order unit `2`.  A plain `def`,
so that instance search does not reach the `OrderUnitGroup` instance of
`ULift ℤ` (whose order unit is `1`). -/
def ougTwo : Type u := ULift.{u} ℤ

instance : AddCommGroup ougTwo.{u} := inferInstanceAs (AddCommGroup (ULift.{u} ℤ))

instance : PartialOrder ougTwo.{u} := inferInstanceAs (PartialOrder (ULift.{u} ℤ))

/-- An element of `ougTwo`. -/
def ougTwoPt (n : ℤ) : ougTwo.{u} := ULift.up n

/-- The integer underlying an element of `ougTwo`. -/
def ougTwoDown (x : ougTwo.{u}) : ℤ := ULift.down x

/-- Natural multiples in `ougTwo`, on the underlying integer. -/
theorem ougTwoDown_nsmul (n : ℕ) (x : ougTwo.{u}) :
    ougTwoDown (n • x) = (n : ℤ) * ougTwoDown x := by
  induction n with
  | zero =>
      show ougTwoDown (0 • x) = _
      rw [zero_nsmul]
      show (0 : ℤ) = _
      push_cast
      ring
  | succ k ih =>
      rw [succ_nsmul]
      show ougTwoDown (k • x) + ougTwoDown x = _
      rw [ih]
      push_cast
      ring

/-- `ℤ` with order unit `2` is an order unit group: `2 ≥ 0`, and every `g`
satisfies `g ≤ n • 2`. -/
instance ougTwoOrderUnitGroup : OrderUnitGroup ougTwo.{u} where
  add_le_add_left x y h z := by
    have h' : ougTwoDown x ≤ ougTwoDown y := h
    show ougTwoDown x + ougTwoDown z ≤ ougTwoDown y + ougTwoDown z
    omega
  unit := ougTwoPt 2
  unit_nonneg := by
    show (0 : ℤ) ≤ 2
    norm_num
  exists_le_nsmul_unit g := by
    refine ⟨(ougTwoDown g).toNat, ?_⟩
    show ougTwoDown g ≤ ougTwoDown ((ougTwoDown g).toNat • ougTwoPt.{u} 2)
    rw [ougTwoDown_nsmul]
    show ougTwoDown g ≤ ((ougTwoDown g).toNat : ℤ) * 2
    omega

/-- `ℤ` with order unit `2`, as an object of `OUG`. -/
abbrev ougTwoObj : OUG.{u} := OUG.of ougTwo.{u}

/-- The order unit of `ougTwo` is `2`. -/
theorem ougTwoObj_unit : ougTwoObj.{u}.unit = ougTwoPt 2 := rfl

/-- **190IV.2** (eff.tex:2165, Examples): `ℤ` with order unit `2` has **no**
states: a unit-preserving
positive homomorphism to `ℤ` would send `2` to `1`, but `h(2) = 2·h(1)` is
even. -/
theorem oug_two_no_states :
    IsEmpty {f : ougTwo.{u} →+ ℤ //
      (∀ x, 0 ≤ x → 0 ≤ f x) ∧ f ougTwoObj.{u}.unit = 1} := by
  refine ⟨fun f => ?_⟩
  have hsplit : (ougTwoPt.{u} 2) = ougTwoPt.{u} 1 + ougTwoPt.{u} 1 := by
    apply ULift.down_injective
    show (2 : ℤ) = 1 + 1
    norm_num
  have h2 : f.1 (ougTwoPt.{u} 2) = 1 := f.2.2
  rw [hsplit, map_add] at h2
  omega

/-- **190IV.2** (eff.tex:2165, Examples): `OUGᵒᵖ` does **not** have separating
states.  On `ℤ` with order unit `2` there are no states at all, while `1 ≠ 0`
as predicates on it. -/
theorem oug_no_separating_states : ¬ SeparatingStates (Par OUG.{u}ᵒᵖ) := by
  intro hsep
  have hE := oug_two_no_states.{u}
  have hemp : IsEmpty (Stat (Par.of (op ougTwoObj.{u}))) :=
    @Function.isEmpty _ _ hE (oug_stat_hom ougTwoObj.{u})
  have h : truth (Par.of (op ougTwoObj.{u}))
      = (0 : Pred (Par.of (op ougTwoObj.{u}))) :=
    hsep (truth (Par.of (op ougTwoObj.{u}))) 0 (fun ω => isEmptyElim ω)
  have h1 := congrArg
    (fun q => ((oug_pred_effect ougTwoObj.{u} q).1 : ougTwo.{u})) h
  rw [oug_pred_effect_truth, oug_pred_effect_zero] at h1
  have h2 : (2 : ℤ) = 0 := congrArg ULift.down h1
  exact absurd h2 (by norm_num)

/-! ### `OUGᵒᵖ` does **not** have separating predicates -/

/-- The first coprojection `G ⟶ G + 1` of `OUGᵒᵖ`, concretely. -/
def ougKap₁ (G : OUG.{u}ᵒᵖ) : G ⟶ op (G.unop.prod ougScal.{u}) :=
  Quiver.Hom.op (ougFst G.unop ougScal.{u})

/-- The second coprojection `1 ⟶ G + 1` of `OUGᵒᵖ`, concretely. -/
def ougKap₂ (G : OUG.{u}ᵒᵖ) : (⊤_ OUG.{u}ᵒᵖ) ⟶ op (G.unop.prod ougScal.{u}) :=
  Quiver.Hom.op (ougSnd G.unop ougScal.{u} ≫ ougUnitTop.{u})

/-- `G + 1` in `OUGᵒᵖ` is `G × ℤ`. -/
def ougPlusCofan (G : OUG.{u}ᵒᵖ) :
    IsColimit (BinaryCofan.mk (ougKap₁ G) (ougKap₂ G)) :=
  BinaryCofan.IsColimit.mk _
    (fun {_} u v => Quiver.Hom.op
      (ougPair u.unop (v.unop ≫ ougTopTo ougScal.{u})))
    (fun {_} _ _ => Quiver.Hom.unop_inj (ougPair_fst _ _))
    (fun {_} u v => by
      refine Quiver.Hom.unop_inj ?_
      show ougPair u.unop (v.unop ≫ ougTopTo ougScal.{u})
          ≫ (ougSnd G.unop ougScal.{u} ≫ ougUnitTop.{u}) = v.unop
      rw [← Category.assoc, ougPair_snd, Category.assoc, ougTop_inv₂,
        Category.comp_id])
    (fun {W} u v m h₁ h₂ => by
      obtain ⟨m, rfl⟩ :
          ∃ m' : (op (G.unop.prod ougScal.{u}) : OUG.{u}ᵒᵖ) ⟶ W, m' = m := ⟨m, rfl⟩
      refine Quiver.Hom.unop_inj ?_
      have k₁ : m.unop ≫ ougFst G.unop ougScal.{u} = u.unop :=
        congrArg Quiver.Hom.unop h₁
      have k₂ : m.unop ≫ (ougSnd G.unop ougScal.{u} ≫ ougUnitTop.{u}) = v.unop :=
        congrArg Quiver.Hom.unop h₂
      have e₂ : m.unop ≫ ougSnd G.unop ougScal.{u}
          = v.unop ≫ ougTopTo ougScal.{u} := by
        rw [← k₂, Category.assoc, Category.assoc, ougTop_inv₁, Category.comp_id]
      rw [← k₁, ← e₂, ougPair_eta]
      rfl)

/-- The comparison isomorphism `G + 1 ≅ G × ℤ` of `OUGᵒᵖ`. -/
def ougEps (G : OUG.{u}ᵒᵖ) :
    (G ⨿ (⊤_ OUG.{u}ᵒᵖ)) ≅ op (G.unop.prod ougScal.{u}) :=
  IsColimit.coconePointUniqueUpToIso (coprodIsCoprod G (⊤_ OUG.{u}ᵒᵖ))
    (ougPlusCofan G)

/-- The first coprojection under the comparison isomorphism `G + 1 ≅ G × ℤ`. -/
theorem ougEps_inl (G : OUG.{u}ᵒᵖ) :
    (coprod.inl : G ⟶ G ⨿ (⊤_ OUG.{u}ᵒᵖ)) ≫ (ougEps G).hom = ougKap₁ G :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod G (⊤_ OUG.{u}ᵒᵖ))
    (ougPlusCofan G) (Discrete.mk WalkingPair.left)

/-- The second coprojection under the comparison isomorphism `G + 1 ≅ G × ℤ`. -/
theorem ougEps_inr (G : OUG.{u}ᵒᵖ) :
    (coprod.inr : (⊤_ OUG.{u}ᵒᵖ) ⟶ G ⨿ (⊤_ OUG.{u}ᵒᵖ)) ≫ (ougEps G).hom
      = ougKap₂ G :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod G (⊤_ OUG.{u}ᵒᵖ))
    (ougPlusCofan G) (Discrete.mk WalkingPair.right)

/-- The order unit group `ℤ²` whose positive cone is
`{(0,0)} ∪ {(a,b) : a ≥ 1, b ≥ 0}`, with order unit `(1,1)`.  Its only
effects are `0` and `(1,1)`. -/
def ougCex : Type u := ULift.{u} (ℤ × ℤ)

instance : AddCommGroup ougCex.{u} :=
  inferInstanceAs (AddCommGroup (ULift.{u} (ℤ × ℤ)))

/-- A point of `ougCex`. -/
def ougCexPt (a b : ℤ) : ougCex.{u} := ULift.up (a, b)

/-- The coordinates of a point of `ougCex`. -/
def ougCexDown (x : ougCex.{u}) : ℤ × ℤ := ULift.down x

@[simp] theorem ougCexDown_pt (a b : ℤ) :
    ougCexDown (ougCexPt.{u} a b) = (a, b) := rfl

/-- Points of `ougCex` are determined by their coordinates. -/
theorem ougCexDown_injective {x y : ougCex.{u}} (h : ougCexDown x = ougCexDown y) :
    x = y := ULift.down_injective h

/-- The zero of `ougCex`. -/
theorem ougCexDown_zero : ougCexDown (0 : ougCex.{u}) = (0, 0) := rfl

/-- Addition in `ougCex` is coordinatewise. -/
theorem ougCexDown_add (x y : ougCex.{u}) :
    ougCexDown (x + y) = ougCexDown x + ougCexDown y := rfl

/-- The order of `ougCex`, with positive cone
`{(0,0)} ∪ {(a,b) : a ≥ 1, b ≥ 0}`. -/
instance ougCexPartialOrder : PartialOrder ougCex.{u} where
  le x y := ((ougCexDown y).1 = (ougCexDown x).1
      ∧ (ougCexDown y).2 = (ougCexDown x).2)
    ∨ ((ougCexDown x).1 + 1 ≤ (ougCexDown y).1
      ∧ (ougCexDown x).2 ≤ (ougCexDown y).2)
  le_refl _ := Or.inl ⟨rfl, rfl⟩
  le_trans x y z hxy hyz := by
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hyz with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  le_antisymm x y hxy hyx := by
    refine ougCexDown_injective (Prod.ext ?_ ?_) <;>
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hyx with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        omega

/-- The order of `ougCex`, unfolded. -/
theorem ougCex_le_iff (x y : ougCex.{u}) :
    x ≤ y ↔ ((ougCexDown y).1 = (ougCexDown x).1
        ∧ (ougCexDown y).2 = (ougCexDown x).2)
      ∨ ((ougCexDown x).1 + 1 ≤ (ougCexDown y).1
        ∧ (ougCexDown x).2 ≤ (ougCexDown y).2) := Iff.rfl

/-- Natural multiples in `ougCex`, on the underlying coordinates. -/
theorem ougCexDown_nsmul (n : ℕ) (x : ougCex.{u}) :
    ougCexDown (n • x)
      = ((n : ℤ) * (ougCexDown x).1, (n : ℤ) * (ougCexDown x).2) := by
  induction n with
  | zero =>
      rw [zero_nsmul]
      refine Prod.ext ?_ ?_ <;> · show (0 : ℤ) = _; push_cast; ring
  | succ k ih =>
      rw [succ_nsmul, ougCexDown_add, ih]
      refine Prod.ext ?_ ?_
      · show (k : ℤ) * (ougCexDown x).1 + (ougCexDown x).1
          = ((k + 1 : ℕ) : ℤ) * (ougCexDown x).1
        push_cast
        ring
      · show (k : ℤ) * (ougCexDown x).2 + (ougCexDown x).2
          = ((k + 1 : ℕ) : ℤ) * (ougCexDown x).2
        push_cast
        ring

/-- `ougCex` is an order unit group: the cone is closed under addition and
`(a,b) ≤ n • (1,1)` for `n` large. -/
instance ougCexOrderUnitGroup : OrderUnitGroup ougCex.{u} where
  add_le_add_left x y h z := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by
        show (ougCexDown y).1 + (ougCexDown z).1
          = (ougCexDown x).1 + (ougCexDown z).1
        omega, by
        show (ougCexDown y).2 + (ougCexDown z).2
          = (ougCexDown x).2 + (ougCexDown z).2
        omega⟩
    · exact Or.inr ⟨by
        show (ougCexDown x).1 + (ougCexDown z).1 + 1
          ≤ (ougCexDown y).1 + (ougCexDown z).1
        omega, by
        show (ougCexDown x).2 + (ougCexDown z).2
          ≤ (ougCexDown y).2 + (ougCexDown z).2
        omega⟩
  unit := ougCexPt 1 1
  unit_nonneg := Or.inr ⟨by show (0 : ℤ) + 1 ≤ 1; omega, by show (0 : ℤ) ≤ 1; omega⟩
  exists_le_nsmul_unit g := by
    refine ⟨(max (ougCexDown g).1 (ougCexDown g).2).toNat + 1, Or.inr ⟨?_, ?_⟩⟩
    · show (ougCexDown g).1 + 1
        ≤ (ougCexDown ((((max (ougCexDown g).1 (ougCexDown g).2).toNat + 1 : ℕ))
            • ougCexPt.{u} 1 1)).1
      rw [ougCexDown_nsmul]
      show (ougCexDown g).1 + 1
        ≤ (((max (ougCexDown g).1 (ougCexDown g).2).toNat + 1 : ℕ) : ℤ) * 1
      push_cast
      omega
    · show (ougCexDown g).2
        ≤ (ougCexDown ((((max (ougCexDown g).1 (ougCexDown g).2).toNat + 1 : ℕ))
            • ougCexPt.{u} 1 1)).2
      rw [ougCexDown_nsmul]
      show (ougCexDown g).2
        ≤ (((max (ougCexDown g).1 (ougCexDown g).2).toNat + 1 : ℕ) : ℤ) * 1
      push_cast
      omega

/-- The counterexample group, as an object of `OUG`. -/
abbrev ougCexObj : OUG.{u} := OUG.of ougCex.{u}

/-- The order unit of `ougCex` is `(1,1)`. -/
theorem ougCexObj_unit : ougCexObj.{u}.unit = ougCexPt 1 1 := rfl

/-- **The only effects of `ougCex` are `0` and `1`** (`0 ≤ (a,b)` forces
`a ≥ 1` unless `(a,b) = 0`, and then `(1,1) - (a,b) ≥ 0` forces `a = b = 1`). -/
theorem ougCex_effect_cases (x : ougCex.{u}) (h0 : 0 ≤ x)
    (h1 : x ≤ ougCexObj.{u}.unit) : x = 0 ∨ x = ougCexObj.{u}.unit := by
  rcases h0 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left
    exact (ougCexDown_injective (Prod.ext e1 e2)).symm ▸ rfl
  · right
    refine ougCexDown_injective (Prod.ext ?_ ?_) <;>
      rcases h1 with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;>
        · simp only [ougCexDown_zero, ougCexObj_unit, ougCexDown_pt] at *
          omega

/-- The first coordinate: a positive unital homomorphism `ougCex × ℤ ⟶ ℤ`. -/
def ougCexF : ougCexObj.{u}.prod ougScal.{u} ⟶ ougScal.{u} where
  toAddHom := AddMonoidHom.mk' (fun p => ULift.up (ougCexDown p.1).1)
    (fun p q => congrArg ULift.up rfl)
  map_nonneg' p hp := by
    obtain ⟨hp1, _⟩ := Prod.le_def.mp hp
    have hp1' : (0 : ougCex.{u}) ≤ p.1 := hp1
    show (0 : ℤ) ≤ (ougCexDown p.1).1
    rcases hp1' with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      · rw [ougCexDown_zero] at e1 e2
        omega
  map_unit' := rfl

/-- The second coordinate: another positive unital homomorphism. -/
def ougCexG : ougCexObj.{u}.prod ougScal.{u} ⟶ ougScal.{u} where
  toAddHom := AddMonoidHom.mk' (fun p => ULift.up (ougCexDown p.1).2)
    (fun p q => congrArg ULift.up rfl)
  map_nonneg' p hp := by
    obtain ⟨hp1, _⟩ := Prod.le_def.mp hp
    have hp1' : (0 : ougCex.{u}) ≤ p.1 := hp1
    show (0 : ℤ) ≤ (ougCexDown p.1).2
    rcases hp1' with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      · rw [ougCexDown_zero] at e1 e2
        omega
  map_unit' := rfl

/-- Integer multiples of a point of `ougCex`. -/
theorem ougCex_zsmul_pt (n a b : ℤ) :
    n • (ougCexPt.{u} a b) = ougCexPt (n * a) (n * b) := by
  refine ougCexDown_injective (Prod.ext ?_ ?_)
  · show n • a = n * a
    simp
  · show n • b = n * b
    simp

/-- The two coordinate maps of `ougCex × ℤ` are distinct: they differ at
`((1,0), 0)`. -/
theorem ougCexF_ne_G : ougCexF.{u} ≠ ougCexG.{u} := by
  intro hh
  have h : (1 : ℤ) = 0 := congrArg
    (fun m : ougCexObj.{u}.prod ougScal.{u} ⟶ ougScal.{u} =>
      (m.toAddHom (ougCexPt.{u} 1 0, (0 : ULift.{u} ℤ))).down) hh
  exact absurd h (by norm_num)

/-- The two maps agree on every point with equal coordinates. -/
theorem ougCexFG_eq_on_diag (c : ℤ) (b : ULift.{u} ℤ) :
    ougCexF.{u}.toAddHom (ougCexPt.{u} c c, b)
      = ougCexG.{u}.toAddHom (ougCexPt.{u} c c, b) := rfl

/-- **190IV.2** (eff.tex:2161, Examples) **is false as printed**: `OUGᵒᵖ` does
**not** have separating
predicates.  On the order unit group `ℤ²` with positive cone
`{0} ∪ {(a,b) : a ≥ 1, b ≥ 0}` and order unit `(1,1)` the only effects are
`0` and `1`, so the predicates only see the diagonal, on which the two
distinct positive unital maps `(x, n) ↦ x₁` and `(x, n) ↦ x₂` into `ℤ`
agree. -/
theorem oug_no_separating_predicates : ¬ SeparatingPredicates (Par OUG.{u}ᵒᵖ) := by
  intro hsep
  refine ougCexF_ne_G.{u} ?_
  set X : Par OUG.{u}ᵒᵖ := Par.of (op ougCexObj.{u}) with hX
  set Y : Par OUG.{u}ᵒᵖ := Par.of (op ougScal.{u}) with hY
  obtain ⟨f, hf⟩ : ∃ f : Y ⟶ X,
      pval f = Quiver.Hom.op ougCexF.{u} ≫ (ougEps X.base).inv :=
    ⟨(Quiver.Hom.op ougCexF.{u} ≫ (ougEps (op ougCexObj.{u})).inv :
      (op ougScal.{u} : OUG.{u}ᵒᵖ) ⟶ _), rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Y ⟶ X,
      pval g = Quiver.Hom.op ougCexG.{u} ≫ (ougEps X.base).inv :=
    ⟨(Quiver.Hom.op ougCexG.{u} ≫ (ougEps (op ougCexObj.{u})).inv :
      (op ougScal.{u} : OUG.{u}ᵒᵖ) ⟶ _), rfl⟩
  have hfg : f = g := by
    refine hsep f g ?_
    intro p
    set q : X.base ⟶ ougS.{u} := ouPredEquiv ougTopCofan.{u} X.base p with hqdef
    set Ψ : (op (ougCexObj.{u}.prod ougScal.{u}) : OUG.{u}ᵒᵖ) ⟶ ougS.{u} :=
      Quiver.Hom.op (ougPair q.unop (ougSnd ougScal.{u} ougScal.{u})) with hΨdef
    have hk₁ : ougKap₁ X.base ≫ Ψ = q := Quiver.Hom.unop_inj (ougPair_fst _ _)
    have hk₂ : ougKap₂ X.base ≫ Ψ = ougI₂.{u} := by
      refine Quiver.Hom.unop_inj ?_
      show ougPair q.unop (ougSnd ougScal.{u} ougScal.{u})
          ≫ (ougSnd ougCexObj.{u} ougScal.{u} ≫ ougUnitTop.{u})
        = ougSnd ougScal.{u} ougScal.{u} ≫ ougUnitTop.{u}
      rw [← Category.assoc, ougPair_snd]
    have hdesc : coprod.desc (pval p)
          (coprod.inr : (⊤_ OUG.{u}ᵒᵖ) ⟶ (⊤_ OUG.{u}ᵒᵖ) ⨿ (⊤_ OUG.{u}ᵒᵖ))
          ≫ (ouGamma ougTopCofan.{u}).hom
        = (ougEps X.base).hom ≫ Ψ := by
      refine coprod.hom_ext ?_ ?_
      · rw [← Category.assoc, coprod.inl_desc, ← Category.assoc, ougEps_inl, hk₁]
        rfl
      · rw [← Category.assoc, coprod.inr_desc, ouGamma_inr, ← Category.assoc,
          ougEps_inr, hk₂]
    -- the predicate `p` only sees the diagonal
    have hx : ((oug_pred_effect ougCexObj.{u} p).1 : ougCex.{u}) = 0
        ∨ ((oug_pred_effect ougCexObj.{u} p).1 : ougCex.{u}) = ougCexObj.{u}.unit :=
      ougCex_effect_cases _ (oug_pred_effect ougCexObj.{u} p).2.1
        (oug_pred_effect ougCexObj.{u} p).2.2
    have hdiag : ∀ ab : ULift.{u} ℤ × ULift.{u} ℤ, ∃ c : ℤ,
        Ψ.unop.toAddHom ab = (ougCexPt.{u} c c, ab.2) := by
      intro ab
      have hq : q.unop.toAddHom ab
          = ab.1.down • ((oug_pred_effect ougCexObj.{u} p).1 : ougCex.{u})
            + ab.2.down • (ougCexObj.{u}.unit
              - ((oug_pred_effect ougCexObj.{u} p).1 : ougCex.{u})) :=
        ougHom_apply ougCexObj.{u} q.unop ab
      rcases hx with hx0 | hx1
      · refine ⟨ab.2.down, ?_⟩
        refine Prod.ext ?_ rfl
        show q.unop.toAddHom ab = ougCexPt.{u} ab.2.down ab.2.down
        rw [hq, hx0, smul_zero, sub_zero, zero_add, ougCexObj_unit,
          ougCex_zsmul_pt, mul_one]
      · refine ⟨ab.1.down, ?_⟩
        refine Prod.ext ?_ rfl
        show q.unop.toAddHom ab = ougCexPt.{u} ab.1.down ab.1.down
        rw [hq, hx1, sub_self, smul_zero, add_zero, ougCexObj_unit,
          ougCex_zsmul_pt, mul_one]
    have hFG : Ψ.unop ≫ ougCexF.{u} = Ψ.unop ≫ ougCexG.{u} := by
      refine oug_hom_ext fun ab => ?_
      obtain ⟨c, hc⟩ := hdiag ab
      show ougCexF.{u}.toAddHom (Ψ.unop.toAddHom ab)
        = ougCexG.{u}.toAddHom (Ψ.unop.toAddHom ab)
      rw [hc]
      exact ougCexFG_eq_on_diag c ab.2
    have hcong : pval f ≫ ((ougEps X.base).hom ≫ Ψ)
        = pval g ≫ ((ougEps X.base).hom ≫ Ψ) := by
      rw [hf, hg]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact Quiver.Hom.unop_inj hFG
    have e1 := congrArg (fun m => pval f ≫ m) hdesc
    have e2 := congrArg (fun m => pval g ≫ m) hdesc
    refine pval_inj ?_
    refine (cancel_mono (ouGamma ougTopCofan.{u}).hom).mp ?_
    show (pval f ≫ coprod.desc (pval p) coprod.inr)
        ≫ (ouGamma ougTopCofan.{u}).hom
      = (pval g ≫ coprod.desc (pval p) coprod.inr)
        ≫ (ouGamma ougTopCofan.{u}).hom
    rw [Category.assoc, Category.assoc]
    exact e1.trans (hcong.trans e2.symm)
  have h2 : Quiver.Hom.op ougCexF.{u} ≫ (ougEps X.base).inv
      = Quiver.Hom.op ougCexG.{u} ≫ (ougEps X.base).inv := by
    rw [← hf, ← hg, hfg]
  have h3 := congrArg (fun m => m ≫ (ougEps X.base).hom) h2
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h3
  exact Quiver.Hom.op_inj h3

end OUGExample

end

end Theses.B.Eff
