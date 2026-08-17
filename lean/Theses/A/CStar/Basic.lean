/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 1: C*-algebras — cstar.tex, lines 1–1713.

  §Definition and Examples  (parsecs 20–60: C*-algebras, Hilbert spaces,
                             bounded operators, B(H))
  §The Basics               (parsecs 70–110: self-adjoint elements, positive
                             elements, morphisms, invertibles, spectrum,
                             spectral permanence)

All statements of parsecs 20–110 are proved.  See CONVENTIONS.md for the
numbering (**4V** = parsec 40, point 50) and naming conventions.
-/
import Theses.Common

open scoped ComplexOrder ComplexInnerProductSpace ComplexStarModule

namespace Theses.A.CStar

/-! ## Parsec 30: Definition and first examples

**3I** (cstar.tex:84, Definition): a *C*-algebra* is a complex vector space
with an associative bilinear multiplication, a unit, an involution `(·)*`,
and a complete submultiplicative norm satisfying the C*-identity
`‖a* a‖ = ‖a‖²`.  In Mathlib this (unital, as everywhere in the thesis)
notion is the class `CStarAlgebra A`; a *commutative* C*-algebra (**3I**,
last clause) is `CommCStarAlgebra A`.

**3III** (cstar.tex:135, Example): ℂ is a commutative C*-algebra —
Mathlib instance below.

**3IV** (cstar.tex:145, Example): a *C*-subalgebra* — a norm-closed
unital ∗-subalgebra — is in Mathlib a `StarSubalgebra ℂ A` that is
`IsClosed` as a set (each such is again a C*-algebra).

**3V** (`cstar-product`, cstar.tex:159, Example): the direct sum
`⊕ᵢ 𝒜ᵢ = {a ∈ Π 𝒜ᵢ | supᵢ ‖a i‖ < ∞}` with coordinatewise operations and
supremum norm is a C*-algebra; in Mathlib this is `lp (fun i => 𝒜 i) ∞`
(with its `CStarRing` instance).  In particular `ℓ∞(X)`, the bounded
functions on a set `X`, is `lp (fun _ : X => ℂ) ∞`.

**3VI** (cstar.tex:195, Example): the bounded continuous functions
`BC(X)` on a topological space (`BoundedContinuousFunction X ℂ`) and the
continuous functions `C(X)` on a compact Hausdorff space (`C(X, ℂ)`) are
commutative C*-algebras — Mathlib instances.

**3VII** (`cstar-matrices-example`, cstar.tex:214, Example): the n×n
complex matrices with conjugate-transpose involution and operator norm
form a C*-algebra; in Mathlib the matrix type carrying this C*-norm is
`CStarMatrix (Fin n) (Fin n) ℂ`.

**3VIII** (cstar.tex:255, Remark): `⊕ₖ M_{n_k}` is a finite-dimensional
C*-algebra, and every finite-dimensional C*-algebra is of this form
(proved at 84II, vn.tex).
-/

/-- **3III** (cstar.tex:135, Example): ℂ is a (commutative) C*-algebra. -/
noncomputable example : CStarAlgebra ℂ := inferInstance

/-! ## Parsec 40 (`hilb`): Hilbert spaces and bounded operators -/

section Operators

variable {𝒳 𝒴 𝒵 : Type*}
  [NormedAddCommGroup 𝒳] [NormedSpace ℂ 𝒳]
  [NormedAddCommGroup 𝒴] [NormedSpace ℂ 𝒴]
  [NormedAddCommGroup 𝒵] [NormedSpace ℂ 𝒵]

/-! **4I** (`example-hilb`, cstar.tex:279, Example): the bounded operators
`B(H)` on a Hilbert space form a C*-algebra (composition, adjoint, identity,
operator norm) — in Mathlib, `H →L[ℂ] H` with `ContinuousLinearMap.adjoint`
as star.  A *concrete C*-algebra* is a closed `StarSubalgebra` of it.

**4II** (`bounded-linear-maps`, cstar.tex:300, Definition): bound, bounded
operator, operator norm `‖T‖`, and the space `B(𝒳,𝒴)` of bounded operators —
in Mathlib `𝒳 →L[ℂ] 𝒴` with its operator norm. -/

/-- **4III** (`bounded-operators-basic`, cstar.tex:326, Exercise), part 1:
the operator norm on `B(𝒳,𝒴)` is a norm.  (Packaged in Mathlib by the
`NormedAddCommGroup (𝒳 →L[ℂ] 𝒴)` instance; as a sample claim we state
definiteness, the nontrivial part.) -/
theorem boundedOperators_basic_1 (T : 𝒳 →L[ℂ] 𝒴) (h : ‖T‖ = 0) : T = 0 :=
  norm_eq_zero.mp h

/-- **4III** (`bounded-operators-basic`, cstar.tex:326, Exercise), part 2:
`‖S ∘ T‖ ≤ ‖S‖ ‖T‖` for bounded operators `T : 𝒳 → 𝒴`, `S : 𝒴 → 𝒵`. -/
theorem boundedOperators_basic_2 (S : 𝒴 →L[ℂ] 𝒵) (T : 𝒳 →L[ℂ] 𝒴) :
    ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ :=
  ContinuousLinearMap.opNorm_comp_le S T

/-- **4III** (`bounded-operators-basic`, cstar.tex:326, Exercise), part 3:
the identity operator is bounded by 1. -/
theorem boundedOperators_basic_3 : ‖(ContinuousLinearMap.id ℂ 𝒳)‖ ≤ 1 :=
  ContinuousLinearMap.norm_id_le

/-- **4IV** (`operator-norm-ball`, cstar.tex:343, Exercise):
`r ‖T‖ = sup { ‖T x‖ : ‖x‖ ≤ r }` for a bounded operator `T` and
`r ∈ [0,∞)`. -/
theorem operatorNorm_ball (T : 𝒳 →L[ℂ] 𝒴) (r : ℝ) (hr : 0 ≤ r) :
    r * ‖T‖ = ⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖ :=
  by
    have hzero : ‖(0 : 𝒳)‖ ≤ r := by simpa using hr
    have hne : Nonempty {x : 𝒳 // ‖x‖ ≤ r} := ⟨⟨0, hzero⟩⟩
    have hle : ∀ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖ ≤ r * ‖T‖ := by
      intro x
      calc ‖T x‖ ≤ ‖T‖ * ‖(x : 𝒳)‖ := T.le_opNorm _
        _ ≤ ‖T‖ * r := mul_le_mul_of_nonneg_left x.2 (norm_nonneg T)
        _ = r * ‖T‖ := mul_comm _ _
    have hbdd : BddAbove (Set.range fun x : {x : 𝒳 // ‖x‖ ≤ r} => ‖T x‖) := by
      refine ⟨r * ‖T‖, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hle x
    refine le_antisymm ?_ (ciSup_le hle)
    -- `0 ≤ ⨆`, witnessed by `x = 0`
    have hS0 : (0 : ℝ) ≤ ⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖ :=
      le_ciSup_of_le hbdd ⟨0, hzero⟩ (by simp)
    rcases eq_or_lt_of_le hr with hr0 | hr0
    · have hz : r * ‖T‖ = 0 := by rw [← hr0]; ring
      rw [hz]; exact hS0
    -- For `0 < r`, bound `‖T‖` by `(⨆)/r` by rescaling `x` to norm exactly `r`.
    have hTle : ‖T‖ ≤ (⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖) / r := by
      refine T.opNorm_le_bound (by positivity) fun x => ?_
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hy : ‖(r / ‖x‖ : ℝ) • x‖ ≤ r := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
            div_mul_cancel₀ _ (ne_of_gt hxn)]
        have hTy : ‖T ((r / ‖x‖ : ℝ) • x)‖ ≤ ⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖ :=
          le_ciSup_of_le hbdd ⟨(r / ‖x‖ : ℝ) • x, hy⟩ le_rfl
        rw [T.map_smul_of_tower, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)] at hTy
        rw [div_mul_eq_mul_div, le_div_iff₀ hr0]
        calc ‖T x‖ * r = (r / ‖x‖ * ‖T x‖) * ‖x‖ := by field_simp
          _ ≤ (⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖) * ‖x‖ :=
              mul_le_mul_of_nonneg_right hTy (norm_nonneg x)
    calc r * ‖T‖ ≤ r * ((⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖) / r) :=
          mul_le_mul_of_nonneg_left hTle hr
      _ = ⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖ := by field_simp

/-- **4V** (`operator-norm-complete`, cstar.tex:359, Lemma): the operator
norm on `B(𝒳,𝒴)` is complete when `𝒴` is complete.  (Mathlib instance:
`ContinuousLinearMap.completeSpace`.) -/
theorem operatorNorm_complete [CompleteSpace 𝒴] : CompleteSpace (𝒳 →L[ℂ] 𝒴) :=
  inferInstance

/-! **4VII** (`bounded-operators-banach-algebra`, cstar.tex:401): `B(𝒳)` on a
complete normed vector space `𝒳` satisfies all requirements of a C*-algebra
not involving the involution, i.e. it is a *Banach algebra* — in Mathlib the
`NormedRing (𝒳 →L[ℂ] 𝒳)` and `CompleteSpace` instances. -/

end Operators

section PreHilbert

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-! **4VIII** (`hilb-def`, cstar.tex:416, Definition): inner product,
definiteness, pre-Hilbert space, Hilbert space — in Mathlib
`[NormedAddCommGroup H] [InnerProductSpace ℂ H]` (the inner product is
definite by construction), with `[CompleteSpace H]` for Hilbert spaces.
The remaining notion, *adjointness* of a pair of operators between
pre-Hilbert spaces, is defined here (for bare functions, so that it applies
to unbounded operators as in **4XI** as well as to `→L[ℂ]` maps).

**4IX** (`hilb-basic-examples`, cstar.tex:461, Example): `ℂ^N`
(`EuclideanSpace ℂ (Fin N)`) is a Hilbert space; the finitely-supported
sequences `c₀₀` are a non-complete pre-Hilbert space; `ℓ²` is treated
in **6II**. -/

/-- **4VIII** (`hilb-def`, cstar.tex:416, Definition): `T : H → K` is
*adjoint to* `S : K → H` when `⟪T x, y⟫ = ⟪x, S y⟫` for all `x ∈ H`,
`y ∈ K`. -/
def IsAdjointTo (T : H → K) (S : K → H) : Prop :=
  ∀ (x : H) (y : K), ⟪T x, y⟫ = ⟪x, S y⟫

/-- **4VIII** (`hilb-def`, cstar.tex:416, Definition): an operator is
*adjointable* when it is adjoint to some operator. -/
def Adjointable (T : H → K) : Prop :=
  ∃ S : K → H, IsAdjointTo T S

/-- **4X** (`uniqueness-adjoint`, cstar.tex:496, Exercise), part 1: vectors
of a pre-Hilbert space with `⟪y, x⟫ = ⟪y, x'⟫` for all `y` are equal. -/
theorem uniqueness_adjoint_1 (x x' : H) (h : ∀ y : H, ⟪y, x⟫ = ⟪y, x'⟫) :
    x = x' :=
  ext_inner_left ℂ h

/-- **4X** (`uniqueness-adjoint`, cstar.tex:496, Exercise), part 2: every
operator between pre-Hilbert spaces has at most one adjoint. -/
theorem uniqueness_adjoint_2 (T : H → K) (S S' : K → H)
    (hS : IsAdjointTo T S) (hS' : IsAdjointTo T S') : S = S' :=
  by
    funext y
    exact ext_inner_left ℂ fun x => by rw [← hS x y, hS' x y]

/-- **4XII** (cstar.tex:520, Exercise), part 1: if `T` is adjoint to `S`
then `S` is adjoint to `T` (so `T** = T`). -/
theorem isAdjointTo_symm (T : H → K) (S : K → H) (h : IsAdjointTo T S) :
    IsAdjointTo S T :=
  by
    intro y x
    simpa [inner_conj_symm] using congrArg (starRingEnd ℂ) (h x y).symm

/-- **4XII** (cstar.tex:520, Exercise), part 2 (sums): `(T + T')* = T* + T'*`
for adjointable operators on a pre-Hilbert space. -/
theorem isAdjointTo_add (T T' : H → K) (S S' : K → H)
    (h : IsAdjointTo T S) (h' : IsAdjointTo T' S') :
    IsAdjointTo (T + T') (S + S') :=
  by
    intro x y
    simp [inner_add_left, inner_add_right, h x y, h' x y]

/-- **4XII** (cstar.tex:520, Exercise), part 2 (scalars):
`(λ T)* = conj λ · T*`. -/
theorem isAdjointTo_smul (T : H → K) (S : K → H) (z : ℂ)
    (h : IsAdjointTo T S) :
    IsAdjointTo (fun x => z • T x) (fun y => (starRingEnd ℂ) z • S y) :=
  by
    intro x y
    simp [inner_smul_left, inner_smul_right, h x y, mul_comm]

/-- **4XII** (cstar.tex:520, Exercise), part 3: `S ∘ T` is adjoint to
`T* ∘ S*`, i.e. `(ST)* = T* S*`. -/
theorem isAdjointTo_comp {L : Type*} [NormedAddCommGroup L]
    [InnerProductSpace ℂ L] (T : H → K) (T' : K → H) (S : K → L) (S' : L → K)
    (hT : IsAdjointTo T T') (hS : IsAdjointTo S S') :
    IsAdjointTo (S ∘ T) (T' ∘ S') :=
  by
    intro x z
    simp only [Function.comp_apply]
    rw [hS, hT]

/-- **4XIII** (`positive-2x2matrix`, cstar.tex:540, Lemma), part 1: if the
2×2 matrix `[[p, c̄], [c, q]]` is positive (i.e. `(ū v̄) A (u v)ᵀ ≥ 0` for
all `u, v ∈ ℂ`), then `p, q ≥ 0`. -/
theorem positive_2x2matrix_1 (p q c : ℂ)
    (h : ∀ u v : ℂ, 0 ≤ (starRingEnd ℂ) u * (p * u + (starRingEnd ℂ) c * v)
      + (starRingEnd ℂ) v * (c * u + q * v)) :
    0 ≤ p ∧ 0 ≤ q :=
  by
    exact ⟨by simpa using h 1 0, by simpa using h 0 1⟩

/-- **4XIII** (`positive-2x2matrix`, cstar.tex:540, Lemma), part 2: for a
positive 2×2 matrix `[[p, c̄], [c, q]]` we have `|c|² ≤ p q`. -/
theorem positive_2x2matrix_2 (p q c : ℂ)
    (h : ∀ u v : ℂ, 0 ≤ (starRingEnd ℂ) u * (p * u + (starRingEnd ℂ) c * v)
      + (starRingEnd ℂ) v * (c * u + q * v)) :
    ((‖c‖ : ℂ)) ^ 2 ≤ p * q :=
  by
    obtain ⟨hp0, hq0⟩ := positive_2x2matrix_1 p q c h
    have key : ∀ t : ℝ,
        (0 : ℂ) ≤ p * (‖c‖ : ℂ) ^ 2 * (t : ℂ) ^ 2 + 2 * (‖c‖ : ℂ) ^ 2 * (t : ℂ) + q := by
      intro t
      have H := h ((t : ℂ) * (starRingEnd ℂ) c) 1
      have e : (starRingEnd ℂ) ((t : ℂ) * (starRingEnd ℂ) c)
              * (p * ((t : ℂ) * (starRingEnd ℂ) c) + (starRingEnd ℂ) c * 1)
            + (starRingEnd ℂ) 1 * (c * ((t : ℂ) * (starRingEnd ℂ) c) + q * 1)
          = p * (‖c‖ : ℂ) ^ 2 * (t : ℂ) ^ 2 + 2 * (‖c‖ : ℂ) ^ 2 * (t : ℂ) + q := by
        simp only [map_mul, Complex.conj_conj, map_one, one_mul, mul_one,
          Complex.conj_ofReal]
        rw [← Complex.conj_mul' c]
        ring
      rwa [e] at H
    rw [Complex.nonneg_iff] at hp0 hq0
    obtain ⟨hpre, hpim⟩ := hp0
    obtain ⟨hqre, hqim⟩ := hq0
    have hp : p = (p.re : ℂ) := by apply Complex.ext <;> simp [← hpim]
    have hq : q = (q.re : ℂ) := by apply Complex.ext <;> simp [← hqim]
    have keyR : ∀ t : ℝ, 0 ≤ p.re * ‖c‖ ^ 2 * t ^ 2 + 2 * ‖c‖ ^ 2 * t + q.re := by
      intro t
      have H := key t
      rw [Complex.nonneg_iff] at H
      simpa [Complex.add_re, Complex.mul_re, ← Complex.ofReal_pow, ← hpim] using H.1
    have hK0 : (0 : ℝ) ≤ ‖c‖ ^ 2 := by positivity
    have main : ‖c‖ ^ 2 ≤ p.re * q.re := by
      rcases eq_or_lt_of_le hpre with hP | hP
      · have hKz : ‖c‖ ^ 2 = 0 := by
          by_contra hne
          have hKpos : 0 < ‖c‖ ^ 2 := lt_of_le_of_ne hK0 (Ne.symm hne)
          have hcne : ‖c‖ ≠ 0 := by
            intro h0
            rw [h0] at hKpos
            simp at hKpos
          have hx := keyR (-(q.re + 1) / (2 * ‖c‖ ^ 2))
          rw [← hP, zero_mul, zero_mul, zero_add] at hx
          rw [show 2 * ‖c‖ ^ 2 * (-(q.re + 1) / (2 * ‖c‖ ^ 2)) = -(q.re + 1) by
            field_simp] at hx
          linarith
        rw [hKz, ← hP]
        simp
      · have hne : p.re ≠ 0 := ne_of_gt hP
        have hx := keyR (-1 / p.re)
        field_simp at hx
        nlinarith [hx, hP, hK0]
    rw [hp, hq]
    exact_mod_cast main

/-! **4XV** (`inner-product-basic`, cstar.tex:590, Exercise): the formula
`‖x‖ = √⟪x,x⟫` defines a seminorm, and a norm when the inner product is
definite.  In Mathlib the norm of an inner product space is packaged in the
`InnerProductSpace` structure (`InnerProductSpace.Core` handles the
construction of the norm from the inner product); the four listed
identities follow. -/

/-- **4XV** (`inner-product-basic`, cstar.tex:590, Exercise), part 1: the
Cauchy–Schwarz inequality `|⟪x,y⟫|² ≤ ⟪x,x⟫ ⟪y,y⟫`. -/
theorem inner_product_basic_1 (x y : H) :
    ‖⟪x, y⟫‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 :=
  by
    have h := norm_inner_le_norm (𝕜 := ℂ) x y
    nlinarith [norm_nonneg ((⟪x, y⟫ : ℂ)), norm_nonneg x, norm_nonneg y,
      mul_nonneg (norm_nonneg x) (norm_nonneg y)]

/-- **4XV** (`inner-product-basic`, cstar.tex:590, Exercise), part 2:
Pythagoras' theorem: `‖x‖² + ‖y‖² = ‖x + y‖²` when `⟪x,y⟫ = 0`. -/
theorem inner_product_basic_2 (x y : H) (h : ⟪x, y⟫ = 0) :
    ‖x‖ ^ 2 + ‖y‖ ^ 2 = ‖x + y‖ ^ 2 :=
  by
    rw [norm_add_sq (𝕜 := ℂ) x y, h]
    simp

/-- **4XV** (`inner-product-basic`, cstar.tex:590, Exercise), part 3: the
parallelogram law. -/
theorem inner_product_basic_3 (x y : H) :
    ‖x‖ ^ 2 + ‖y‖ ^ 2 = (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2 :=
  by
    have := parallelogram_law_with_norm ℂ x y
    linarith

/-- **4XV** (`inner-product-basic`, cstar.tex:590, Exercise), part 4: the
polarisation identity `⟪x,y⟫ = ¼ ∑_{n<4} iⁿ ‖iⁿ x + y‖²`. -/
theorem inner_product_basic_4 (x y : H) :
    ⟪x, y⟫ = (∑ n ∈ Finset.range 4,
      Complex.I ^ n * ((‖(Complex.I ^ n : ℂ) • x + y‖ : ℂ)) ^ 2) / 4 :=
  by
    have h1 : ‖(Complex.I : ℂ) • x + y‖ = ‖x - Complex.I • y‖ := by
      have e : (Complex.I : ℂ) • x + y = Complex.I • (x - Complex.I • y) := by
        rw [smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add]
      rw [e, norm_smul, Complex.norm_I, one_mul]
    have h2 : ‖(-Complex.I : ℂ) • x + y‖ = ‖x + Complex.I • y‖ := by
      have e : (-Complex.I : ℂ) • x + y = (-Complex.I) • (x + Complex.I • y) := by
        rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
      rw [e, norm_smul, norm_neg, Complex.norm_I, one_mul]
    have h3 : ‖(-1 : ℂ) • x + y‖ = ‖x - y‖ := by
      rw [neg_one_smul, neg_add_eq_sub, norm_sub_rev]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, one_smul]
    rw [show (Complex.I : ℂ) ^ 2 = -1 from Complex.I_sq,
      show (Complex.I : ℂ) ^ 3 = -Complex.I from Complex.I_pow_three,
      h1, h2, h3, inner_eq_sum_norm_sq_div_four]
    simp [RCLike.I]
    ring

/-- Auxiliary: if `A` is adjoint to `B` (as bounded operators on a pre-Hilbert
space) then `‖A‖ ≤ ‖B‖`.  Used for both parts of **4XVI**. -/
private theorem norm_le_of_isAdjointTo (A B : H →L[ℂ] H)
    (hAB : IsAdjointTo (⇑A) (⇑B)) : ‖A‖ ≤ ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound A (norm_nonneg B) fun x => ?_
  have e1 : (‖A x‖ : ℝ) ^ 2 = ‖(⟪x, B (A x)⟫ : ℂ)‖ := by
    rw [← hAB x (A x), inner_self_eq_norm_sq_to_K]
    simp
  have e2 : ‖(⟪x, B (A x)⟫ : ℂ)‖ ≤ ‖x‖ * (‖B‖ * ‖A x‖) :=
    (norm_inner_le_norm (𝕜 := ℂ) x (B (A x))).trans
      (by gcongr; exact B.le_opNorm (A x))
  rw [← e1] at e2
  nlinarith [norm_nonneg (A x), norm_nonneg x, norm_nonneg B,
    mul_nonneg (norm_nonneg B) (norm_nonneg x)]

/-- **4XVI** (`operators-cstar-identity`, cstar.tex:642, Lemma), part 1: for
a bounded adjointable operator `T` on a pre-Hilbert space, `‖T* T‖ = ‖T‖²`
(the C*-identity). -/
theorem operators_cstar_identity_1 (T S : H →L[ℂ] H)
    (h : IsAdjointTo T S) : ‖S.comp T‖ = ‖T‖ ^ 2 :=
  by
    have hST : ‖S‖ = ‖T‖ := le_antisymm (norm_le_of_isAdjointTo S T (isAdjointTo_symm T S h))
      (norm_le_of_isAdjointTo T S h)
    refine le_antisymm ?_ ?_
    · calc ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le S T
        _ = ‖T‖ ^ 2 := by rw [hST, sq]
    · have h1 : ∀ x : H, ‖T x‖ ≤ Real.sqrt ‖S.comp T‖ * ‖x‖ := by
        intro x
        have e1 : (‖T x‖ : ℝ) ^ 2 = ‖(⟪x, (S.comp T) x⟫ : ℂ)‖ := by
          rw [show (S.comp T) x = S (T x) from rfl, ← h x (T x), inner_self_eq_norm_sq_to_K]
          simp
        have e2 : ‖(⟪x, (S.comp T) x⟫ : ℂ)‖ ≤ ‖x‖ * (‖S.comp T‖ * ‖x‖) :=
          (norm_inner_le_norm (𝕜 := ℂ) x _).trans (by gcongr; exact (S.comp T).le_opNorm x)
        have e3 : (‖T x‖ : ℝ) ^ 2 ≤ ‖S.comp T‖ * ‖x‖ ^ 2 := by
          rw [e1]
          nlinarith [e2]
        calc ‖T x‖ = Real.sqrt (‖T x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (‖S.comp T‖ * ‖x‖ ^ 2) := Real.sqrt_le_sqrt e3
          _ = Real.sqrt ‖S.comp T‖ * ‖x‖ := by
              rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      have h2 := ContinuousLinearMap.opNorm_le_bound T (Real.sqrt_nonneg _) h1
      nlinarith [Real.sq_sqrt (norm_nonneg (S.comp T)), Real.sqrt_nonneg ‖S.comp T‖,
        norm_nonneg T]

/-- **4XVI** (`operators-cstar-identity`, cstar.tex:642, Lemma), part 2:
`‖T*‖ = ‖T‖`. -/
theorem operators_cstar_identity_2 (T S : H →L[ℂ] H)
    (h : IsAdjointTo T S) : ‖S‖ = ‖T‖ :=
  by
    exact le_antisymm (norm_le_of_isAdjointTo S T (isAdjointTo_symm T S h))
      (norm_le_of_isAdjointTo T S h)

/-- **4XVIII** (cstar.tex:666, Exercise): for a Hilbert space `H` the
adjointable operators form a closed (sub)space of `B(H)`. -/
theorem adjointable_isClosed [CompleteSpace H] :
    IsClosed {T : H →L[ℂ] H | Adjointable (⇑T)} :=
  by
    have h : {T : H →L[ℂ] H | Adjointable (⇑T)} = Set.univ := by
      ext T
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, Adjointable]
      exact ⟨⇑(ContinuousLinearMap.adjoint T), fun x y =>
        (ContinuousLinearMap.adjoint_inner_right T x y).symm⟩
    rw [h]
    exact isClosed_univ

/-- **4XIX** (`ketbra`, cstar.tex:671, Exercise): the operator
`|x⟩⟨y| : z ↦ ⟪y, z⟫ x` on a Hilbert space, bounded by construction. -/
noncomputable def ketbra (x y : H) : H →L[ℂ] H :=
  (innerSL ℂ y).smulRight x

/-- **4XIX** (`ketbra`, cstar.tex:671, Exercise), part 1: `|x⟩⟨y|` maps `z`
to `⟪y, z⟫ x` and has operator norm `‖x‖ ‖y‖`. -/
theorem ketbra_norm (x y : H) : ‖ketbra x y‖ = ‖x‖ * ‖y‖ :=
  by
    rw [ketbra, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

/-- **4XIX** (`ketbra`, cstar.tex:671, Exercise), part 2: `|x⟩⟨y|` is
adjointable, with `(|x⟩⟨y|)* = |y⟩⟨x|`. -/
theorem ketbra_adjoint (x y : H) :
    IsAdjointTo (⇑(ketbra x y)) (⇑(ketbra y x)) :=
  by
    intro z w
    simp [ketbra, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]

/-! ## Parsec 50 (`hilb-adjoint`): projections, Riesz representation, B(H)

**5I** (`adjoinables-cstar-algebra`, cstar.tex:689): the adjointable
operators on a Hilbert space form a C*-algebra; to see that `B(H)` is one
it remains to show every bounded operator is adjointable (**5XI**). -/

/-- **5II** (`projection-on-closed-linear-subspace`, cstar.tex:702,
Definition): `y` is a *projection of `x` on* a linear subspace `C` when
`y ∈ C` and `‖x - y‖ = min { ‖x - y'‖ : y' ∈ C }`. -/
def IsProjectionOn (C : Submodule ℂ H) (x y : H) : Prop :=
  y ∈ C ∧ ∀ y' ∈ C, ‖x - y‖ ≤ ‖x - y'‖

/-- Auxiliary: a projection on `C` realizes the infimum of the distances to
the members of `C`, which is the form the Mathlib characterisation
`Submodule.norm_eq_iInf_iff_inner_eq_zero` takes. -/
private theorem IsProjectionOn.norm_eq_iInf {C : Submodule ℂ H} {x y : H}
    (h : IsProjectionOn C x y) : ‖x - y‖ = ⨅ w : C, ‖x - w‖ := by
  have hbdd : BddBelow (Set.range fun w : C => ‖x - (w : H)‖) := by
    refine ⟨0, ?_⟩
    rintro r ⟨w, rfl⟩
    exact norm_nonneg _
  refine le_antisymm (le_ciInf fun w => h.2 w w.2) ?_
  exact ciInf_le hbdd (⟨y, h.1⟩ : C)

/-- Auxiliary: a projection `y` of `x` on `C` has `x - y` orthogonal to `C`
(**5VI**.4), via the Mathlib characterisation of minimisers. -/
private theorem IsProjectionOn.inner_eq_zero {C : Submodule ℂ H} {x y : H}
    (h : IsProjectionOn C x y) {y' : H} (hy' : y' ∈ C) : ⟪y', x - y⟫ = 0 := by
  have hz := (C.norm_eq_iInf_iff_inner_eq_zero h.1).mp h.norm_eq_iInf y' hy'
  simpa only [inner_conj_symm, map_zero] using congrArg (starRingEnd ℂ) hz

/-- Auxiliary (**5IV**): the Pythagoras identity for the distance from `x` to
a point of the line `ℂe` spanned by a unit vector `e`. -/
private theorem norm_sub_smul_sq (x e : H) (he : ‖e‖ = 1) (c : ℂ) :
    ‖x - c • e‖ ^ 2 = ‖x - ⟪e, x⟫ • e‖ ^ 2 + ‖⟪e, x⟫ - c‖ ^ 2 := by
  have hee : (⟪e, e⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]
    norm_num
  have horth : (⟪x - ⟪e, x⟫ • e, (⟪e, x⟫ - c) • e⟫ : ℂ) = 0 := by
    rw [inner_smul_right, inner_sub_left, inner_smul_left, hee, mul_one, inner_conj_symm,
      sub_self, mul_zero]
  have hsplit : x - c • e = (x - ⟪e, x⟫ • e) + (⟪e, x⟫ - c) • e := by
    rw [sub_smul]; abel
  have hp := inner_product_basic_2 (x - ⟪e, x⟫ • e) ((⟪e, x⟫ - c) • e) horth
  rw [← hsplit] at hp
  rw [← hp, norm_smul, he, mul_one]

/-- **5III** (cstar.tex:713, Exercise): in `ℓ²` the only vectors having a
projection on the (non-closed) subspace `c₀₀` of finitely supported
sequences are the vectors of `c₀₀` themselves.  (Here `c₀₀` is the span of
the coordinate vectors `lp.single 2 n z`.) -/
theorem projection_on_c00 (x : lp (fun _ : ℕ => ℂ) 2) :
    (∃ y, IsProjectionOn
        (Submodule.span ℂ {f : lp (fun _ : ℕ => ℂ) 2 | ∃ n z, f = lp.single 2 n z})
        x y) ↔
      x ∈ Submodule.span ℂ
        {f : lp (fun _ : ℕ => ℂ) 2 | ∃ n z, f = lp.single 2 n z} :=
  by
    constructor
    · rintro ⟨y, hy⟩
      have hmem : ∀ n : ℕ, (lp.single 2 n (1 : ℂ)) ∈
          Submodule.span ℂ {f : lp (fun _ : ℕ => ℂ) 2 | ∃ n z, f = lp.single 2 n z} :=
        fun n => Submodule.subset_span ⟨n, 1, rfl⟩
      have hcoord : ∀ n : ℕ, (x - y) n = 0 := by
        intro n
        have h0 := hy.inner_eq_zero (hmem n)
        rw [lp.inner_single_left] at h0
        simpa using h0
      have hxy : x - y = 0 := lp.ext (funext fun n => by simpa using hcoord n)
      rw [sub_eq_zero] at hxy
      rw [hxy]
      exact hy.1
    · intro hx
      exact ⟨x, hx, fun y' _ => by simpa using norm_nonneg (x - y')⟩

/-- **5IV** (cstar.tex:726, Lemma): for a unit vector `e` of a pre-Hilbert
space, `⟪e, x⟫ e` is a projection of `x` on the line `ℂe`. -/
theorem projection_on_line (x e : H) (he : ‖e‖ = 1) :
    IsProjectionOn (ℂ ∙ e) x (⟪e, x⟫ • e) :=
  by
    refine ⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e), ?_⟩
    intro y' hy'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy'
    have hkey := norm_sub_smul_sq x e he c
    nlinarith [norm_nonneg (x - ⟪e, x⟫ • e), norm_nonneg (x - c • e),
      norm_nonneg ((⟪e, x⟫ : ℂ) - c), sq_nonneg (‖(⟪e, x⟫ : ℂ) - c‖)]

/-- **5IV** (cstar.tex:726, Lemma), uniqueness part: `⟪e, x⟫ e` is the
*unique* projection of `x` on `ℂe`. -/
theorem projection_on_line_unique (x e : H) (he : ‖e‖ = 1) (y : H)
    (hy : IsProjectionOn (ℂ ∙ e) x y) : y = ⟪e, x⟫ • e :=
  by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy.1
    subst hc
    have h1 := hy.2 ((⟪e, x⟫ : ℂ) • e)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
    have hkey := norm_sub_smul_sq x e he c
    have h2 : ‖(⟪e, x⟫ : ℂ) - c‖ ≤ 0 := by
      nlinarith [norm_nonneg (x - c • e), norm_nonneg (x - (⟪e, x⟫ : ℂ) • e),
        norm_nonneg ((⟪e, x⟫ : ℂ) - c)]
    have h3 := le_antisymm h2 (norm_nonneg _)
    rw [norm_eq_zero, sub_eq_zero] at h3
    rw [h3]

/-- **5VI** (`hilb-projection-basic`, cstar.tex:755, Exercise), part 1: a
projection `y` of `x` on a linear subspace `C` is a projection of `x` on
the line `ℂy`. -/
theorem hilb_projection_basic_1 (C : Submodule ℂ H) (x y : H)
    (h : IsProjectionOn C x y) : IsProjectionOn (ℂ ∙ y) x y :=
  by
    refine ⟨Submodule.mem_span_singleton_self y, ?_⟩
    intro y' hy'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy'
    exact h.2 _ (C.smul_mem c h.1)

/-- **5VI** (`hilb-projection-basic`, cstar.tex:755, Exercise), part 2: the
projection of `x` on `C` is unique, and `⟪y, x - y⟫ = 0`. -/
theorem hilb_projection_basic_2 (C : Submodule ℂ H) (x y y' : H)
    (h : IsProjectionOn C x y) (h' : IsProjectionOn C x y') :
    y' = y ∧ ⟪y, x - y⟫ = 0 :=
  by
    have hmem := Submodule.sub_mem _ h'.1 h.1
    have e1 := h.inner_eq_zero hmem
    have e2 := h'.inner_eq_zero hmem
    have hkey : (⟪y' - y, y' - y⟫ : ℂ) = 0 := by
      have hy : y' - y = (x - y) - (x - y') := by abel
      calc (⟪y' - y, y' - y⟫ : ℂ) = ⟪y' - y, (x - y) - (x - y')⟫ := by rw [← hy]
        _ = 0 := by rw [inner_sub_right, e1, e2, sub_zero]
    have hzero : y' - y = 0 := inner_self_eq_zero.mp hkey
    exact ⟨sub_eq_zero.mp hzero, h.inner_eq_zero h.1⟩

/-- **5VI** (`hilb-projection-basic`, cstar.tex:755, Exercise), part 3:
`y + c` is the projection of `x + c` on `C` for every `c ∈ C`. -/
theorem hilb_projection_basic_3 (C : Submodule ℂ H) (x y : H)
    (h : IsProjectionOn C x y) (c : H) (hc : c ∈ C) :
    IsProjectionOn C (x + c) (y + c) :=
  by
    refine ⟨Submodule.add_mem _ h.1 hc, ?_⟩
    intro y' hy'
    rw [show x + c - (y + c) = x - y by abel, show x + c - y' = x - (y' - c) by abel]
    exact h.2 _ (Submodule.sub_mem _ hy' hc)

/-- **5VI** (`hilb-projection-basic`, cstar.tex:755, Exercise), part 4:
`⟪y', x - y⟫ = 0` for every `y' ∈ C`. -/
theorem hilb_projection_basic_4 (C : Submodule ℂ H) (x y : H)
    (h : IsProjectionOn C x y) (y' : H) (hy' : y' ∈ C) :
    ⟪y', x - y⟫ = 0 :=
  by
    exact h.inner_eq_zero hy'

/-- **5VII** (`projection-theorem`, cstar.tex:766, Projection Theorem): every
vector `x` of a Hilbert space has a unique projection `y` on a closed linear
subspace `C`.  (Mathlib: `Submodule.orthogonalProjection`.) -/
theorem projection_theorem [CompleteSpace H] (C : Submodule ℂ H)
    (hC : IsClosed (C : Set H)) (x : H) :
    ∃! y, IsProjectionOn C x y :=
  by
    obtain ⟨v, hvC, hv⟩ := Submodule.exists_norm_eq_iInf_of_complete_subspace C hC.isComplete x
    have hbdd : BddBelow (Set.range fun w : C => ‖x - (w : H)‖) := by
      refine ⟨0, ?_⟩
      rintro r ⟨w, rfl⟩
      exact norm_nonneg _
    have hproj : IsProjectionOn C x v := by
      refine ⟨hvC, fun y' hy' => ?_⟩
      rw [hv]
      exact ciInf_le hbdd (⟨y', hy'⟩ : C)
    exact ⟨v, hproj, fun z hz => (hilb_projection_basic_2 C x v z hproj hz).1⟩

/-- **5VII** (`projection-theorem`, cstar.tex:766, Projection Theorem),
second part: the projection `y` of `x` on `C` satisfies `⟪y', y⟫ = ⟪y', x⟫`
for all `y' ∈ C`. -/
theorem projection_theorem_inner [CompleteSpace H] (C : Submodule ℂ H)
    (hC : IsClosed (C : Set H)) (x y : H) (h : IsProjectionOn C x y) :
    ∀ y' ∈ C, ⟪y', y⟫ = ⟪y', x⟫ :=
  by
    intro y' hy'
    have hzero := hilb_projection_basic_4 C x y h y' hy'
    rw [inner_sub_right, sub_eq_zero] at hzero
    exact hzero.symm

/-- **5IX** (`riesz-representation-theorem`, cstar.tex:811, Riesz'
Representation Theorem): for every bounded linear map `f : H → ℂ` on a
Hilbert space there is a unique `x ∈ H` with `⟪x, ·⟫ = f`.  (Mathlib:
`InnerProductSpace.toDual`.) -/
theorem riesz_representation_theorem [CompleteSpace H] (f : H →L[ℂ] ℂ) :
    ∃! x : H, ∀ z : H, ⟪x, z⟫ = f z :=
  by
    refine ⟨(InnerProductSpace.toDual ℂ H).symm f, fun z => ?_, fun x hx => ?_⟩
    · exact InnerProductSpace.toDual_symm_apply
    · refine ext_inner_right ℂ fun z => ?_
      rw [hx z, InnerProductSpace.toDual_symm_apply]

/-- **5XI** (`bounded-operator-adjoinable`, cstar.tex:842, Exercise): every
bounded operator on a Hilbert space is adjointable.  (Mathlib:
`ContinuousLinearMap.adjoint`.) -/
theorem bounded_operator_adjoinable [CompleteSpace H] (T : H →L[ℂ] H) :
    ∃ S : H →L[ℂ] H, IsAdjointTo (⇑T) (⇑S) :=
  by
    exact ⟨ContinuousLinearMap.adjoint T, fun x y =>
      (ContinuousLinearMap.adjoint_inner_right T x y).symm⟩

/-! **5XII** (cstar.tex:854): thus the bounded operators on a Hilbert space
form a C*-algebra `B(H)` — Mathlib's `CStarAlgebra (H →L[ℂ] H)` instance. -/

end PreHilbert

/-! ## Parsec 60: the Hilbert direct sum -/

section HilbSum

variable {ι : Type*} {Hi : ι → Type*} [∀ i, NormedAddCommGroup (Hi i)]
  [∀ i, InnerProductSpace ℂ (Hi i)] [∀ i, CompleteSpace (Hi i)]

/-- **6II** (`hilb-sum`, cstar.tex:873, Proposition), part 1: for members
`x, y` of the direct sum `⊕ᵢ Hᵢ = {x ∈ Π Hᵢ | ∑ᵢ ‖xᵢ‖² < ∞}` (Mathlib:
`lp Hi 2`) the sum `∑ᵢ ⟪xᵢ, yᵢ⟫` defining the inner product converges. -/
theorem hilb_sum_summable (x y : lp Hi 2) :
    Summable fun i => ⟪(x : ∀ i, Hi i) i, (y : ∀ i, Hi i) i⟫ :=
  by
    exact lp.summable_inner x y

/-- **6II** (`hilb-sum`, cstar.tex:873, Proposition), part 2: `⊕ᵢ Hᵢ` with
the inner product `⟪x, y⟫ = ∑ᵢ ⟪xᵢ, yᵢ⟫` is a Hilbert space (i.e. the
resulting norm is complete).  (Mathlib: `lp.completeSpace` and the
`InnerProductSpace` instance on `lp Hi 2`.) -/
theorem hilb_sum_complete : CompleteSpace (lp Hi 2) :=
  inferInstance

end HilbSum

/-! ## Parsec 70: self-adjoint elements

**7II** (cstar.tex:989, Definition): `a` is *self-adjoint* when `a* = a`
(Mathlib: `IsSelfAdjoint a`, and `selfAdjoint 𝒜` for the set); the *real*
and *imaginary parts* are `Re a = (a + a*)/2` and `Im a = (a - a*)/2i`
(Mathlib: `realPart`/`imaginaryPart`, notation `ℜ`/`ℑ` in the
`ComplexStarModule` scope, valued in `selfAdjoint 𝒜`). -/

section Involution

variable {𝒜 : Type*} [CStarAlgebra 𝒜]

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 1:
`ℜa` and `ℑa` are self-adjoint (automatic here from their type) and
`a = ℜa + i·ℑa`. -/
theorem cstar_involution_basic_1 (a : 𝒜) :
    a = (ℜ a : 𝒜) + Complex.I • (ℑ a : 𝒜) :=
  (realPart_add_I_smul_imaginaryPart a).symm

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 2:
if `a = b + i·c` with `b, c` self-adjoint then `b = ℜa` and `c = ℑa`. -/
theorem cstar_involution_basic_2 (a b c : 𝒜) (hb : IsSelfAdjoint b)
    (hc : IsSelfAdjoint c) (h : a = b + Complex.I • c) :
    b = (ℜ a : 𝒜) ∧ c = (ℑ a : 𝒜) :=
  by
    subst h
    constructor
    · simp [map_add, hc.imaginaryPart, hb.coe_realPart]
    · simp [map_add, hb.imaginaryPart, hc.coe_realPart]

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 3:
`ℜ(a*) = ℜa` and `ℑ(a*) = -ℑa`. -/
theorem cstar_involution_basic_3 (a : 𝒜) :
    (ℜ (star a) : 𝒜) = (ℜ a : 𝒜) ∧ (ℑ (star a) : 𝒜) = -(ℑ a : 𝒜) :=
  by
    constructor
    · rw [realPart_apply_coe, realPart_apply_coe, star_star, add_comm]
    · rw [imaginaryPart_apply_coe, imaginaryPart_apply_coe, star_star, ← smul_neg, ← smul_neg,
        neg_sub]

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 4:
`a` is self-adjoint iff `ℜa = a` iff `ℑa = 0`. -/
theorem cstar_involution_basic_4 (a : 𝒜) :
    (IsSelfAdjoint a ↔ (ℜ a : 𝒜) = a) ∧ (IsSelfAdjoint a ↔ (ℑ a : 𝒜) = 0) :=
  by
    refine ⟨⟨fun ha => ha.coe_realPart, fun ha => ha ▸ (ℜ a).property⟩, ⟨fun ha => ?_, fun ha => ?_⟩⟩
    · rw [ha.imaginaryPart]
      rfl
    · exact imaginaryPart_eq_zero_iff.mp (ZeroMemClass.coe_eq_zero.mp ha)

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 5:
`a ↦ ℜa` and `a ↦ ℑa` are ℝ-linear (in Mathlib they are bundled as
`𝒜 →ₗ[ℝ] selfAdjoint 𝒜`; we state additivity as sample claim). -/
theorem cstar_involution_basic_5 (a b : 𝒜) :
    (ℜ (a + b) : 𝒜) = (ℜ a : 𝒜) + (ℜ b : 𝒜) ∧
      (ℑ (a + b) : 𝒜) = (ℑ a : 𝒜) + (ℑ b : 𝒜) :=
  by
    exact ⟨by simp, by simp⟩

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 6:
`ℑa = -ℜ(ia)` and `ℜa = ℑ(ia)`. -/
theorem cstar_involution_basic_6 (a : 𝒜) :
    (ℑ a : 𝒜) = -(ℜ (Complex.I • a) : 𝒜) ∧
      (ℜ a : 𝒜) = (ℑ (Complex.I • a) : 𝒜) :=
  by
    exact ⟨by simp, by simp⟩

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 7:
`a* a` is self-adjoint, and
`a* a = (ℜa)² + (ℑa)² + i(ℜa·ℑa - ℑa·ℜa)`. -/
theorem cstar_involution_basic_7 (a : 𝒜) :
    IsSelfAdjoint (star a * a) ∧
      star a * a = (ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2 +
        Complex.I • ((ℜ a : 𝒜) * (ℑ a : 𝒜) - (ℑ a : 𝒜) * (ℜ a : 𝒜)) :=
  by
    refine ⟨IsSelfAdjoint.star_mul_self a, ?_⟩
    have ha : a = (ℜ a : 𝒜) + Complex.I • (ℑ a : 𝒜) := (realPart_add_I_smul_imaginaryPart a).symm
    have has : star a = (ℜ a : 𝒜) - Complex.I • (ℑ a : 𝒜) := by
      conv_lhs => rw [ha]
      rw [star_add, star_smul, selfAdjoint.star_val_eq, selfAdjoint.star_val_eq]
      simp [sub_eq_add_neg]
    calc star a * a
        = ((ℜ a : 𝒜) - Complex.I • (ℑ a : 𝒜)) * ((ℜ a : 𝒜) + Complex.I • (ℑ a : 𝒜)) := by
          rw [← has, ← ha]
      _ = (ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2 +
            Complex.I • ((ℜ a : 𝒜) * (ℑ a : 𝒜) - (ℑ a : 𝒜) * (ℜ a : 𝒜)) := by
          rw [sub_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
            mul_smul_comm, smul_smul, Complex.I_mul_I, neg_smul, one_smul, smul_sub, sq, sq]
          abel

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 8:
real and imaginary part need not commute: an example in the 2×2 matrices. -/
theorem cstar_involution_basic_8 :
    ∃ a : Matrix (Fin 2) (Fin 2) ℂ,
      (ℜ a : Matrix (Fin 2) (Fin 2) ℂ) * (ℑ a : Matrix (Fin 2) (Fin 2) ℂ) ≠
        (ℑ a : Matrix (Fin 2) (Fin 2) ℂ) * (ℜ a : Matrix (Fin 2) (Fin 2) ℂ) :=
  by
    refine ⟨!![0, 1; 0, 0], fun hcomm => ?_⟩
    have h := congrFun (congrFun hcomm 0) 0
    rw [realPart_apply_coe, imaginaryPart_apply_coe] at h
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply] at h
    exact Complex.I_ne_zero (by linear_combination 2 * h)

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 9:
`a* a + a a* = 2((ℜa)² + (ℑa)²)`. -/
theorem cstar_involution_basic_9 (a : 𝒜) :
    star a * a + a * star a = 2 * ((ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2) :=
  by
    have ha : a = (ℜ a : 𝒜) + Complex.I • (ℑ a : 𝒜) := (realPart_add_I_smul_imaginaryPart a).symm
    have has : star a = (ℜ a : 𝒜) - Complex.I • (ℑ a : 𝒜) := by
      conv_lhs => rw [ha]
      rw [star_add, star_smul, selfAdjoint.star_val_eq, selfAdjoint.star_val_eq]
      simp [sub_eq_add_neg]
    have h7 := (cstar_involution_basic_7 a).2
    have h7' : a * star a = (ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2 -
        Complex.I • ((ℜ a : 𝒜) * (ℑ a : 𝒜) - (ℑ a : 𝒜) * (ℜ a : 𝒜)) := by
      calc a * star a
          = ((ℜ a : 𝒜) + Complex.I • (ℑ a : 𝒜)) * ((ℜ a : 𝒜) - Complex.I • (ℑ a : 𝒜)) := by
            rw [← has, ← ha]
        _ = (ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2 -
              Complex.I • ((ℜ a : 𝒜) * (ℑ a : 𝒜) - (ℑ a : 𝒜) * (ℜ a : 𝒜)) := by
            rw [add_mul, mul_sub, mul_sub, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
              mul_smul_comm, smul_smul, Complex.I_mul_I, neg_smul, one_smul, smul_sub, sq, sq]
            abel
    rw [h7, h7', two_mul]
    abel

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 10:
for self-adjoint `b, c` the product `bc` is self-adjoint iff `bc = cb`. -/
theorem cstar_involution_basic_10 (b c : 𝒜) (hb : IsSelfAdjoint b)
    (hc : IsSelfAdjoint c) : IsSelfAdjoint (b * c) ↔ b * c = c * b :=
  by
    rw [isSelfAdjoint_iff, star_mul, hb.star_eq, hc.star_eq]
    exact eq_comm

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 11:
`‖a*‖ = ‖a‖`.  (Mathlib: `norm_star`.) -/
theorem cstar_involution_basic_11 (a : 𝒜) : ‖star a‖ = ‖a‖ :=
  norm_star a

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 12:
`‖ℜa‖ ≤ ‖a‖` and `‖ℑa‖ ≤ ‖a‖`. -/
theorem cstar_involution_basic_12 (a : 𝒜) :
    ‖(ℜ a : 𝒜)‖ ≤ ‖a‖ ∧ ‖(ℑ a : 𝒜)‖ ≤ ‖a‖ :=
  by
    exact ⟨by simpa using realPart.norm_le a, by simpa using imaginaryPart.norm_le a⟩

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 13:
`‖a²‖ = ‖a‖²` for self-adjoint `a`. -/
theorem cstar_involution_basic_13 (a : 𝒜) (ha : IsSelfAdjoint a) :
    ‖a ^ 2‖ = ‖a‖ ^ 2 :=
  by
    have h : a ^ 2 = star a * a := by rw [ha.star_eq, sq]
    rw [h, CStarRing.norm_star_mul_self, sq]

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 13
(counterexample): `‖a²‖ ≠ ‖a‖²` may occur for non-self-adjoint `a`
(e.g. `[[0,1],[0,0]]` as an operator on ℂ²). -/
theorem cstar_involution_basic_13' :
    ∃ T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      ‖T ^ 2‖ ≠ ‖T‖ ^ 2 :=
  by
    refine ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ), ?_⟩
    have hsq : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ^ 2 = 0 := by
      rw [pow_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ]
    have h1 : (Matrix.toEuclideanCLM (𝕜 := ℂ)
        (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) ^ 2 = 0 := by
      rw [← map_pow, hsq, map_zero]
    have h2 : Matrix.toEuclideanCLM (𝕜 := ℂ)
        (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
      intro hc
      have hM : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
        have := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm hc
        simpa using this
      have := congrFun (congrFun hM 0) 1
      simp at this
    rw [h1, norm_zero]
    intro hc
    exact h2 (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hc.symm))

/-! ## Parsec 80: scalars in a C*-algebra

**8I** (cstar.tex:1060, Notation): for `λ ∈ ℂ` we write `λ` also for the
element `λ·1` of `𝒜`; in Lean this is `algebraMap ℂ 𝒜 λ`. -/

/-- **8II** (cstar.tex:1071, Exercise), part 1: in the trivial C*-algebra
`{0}` we have `‖1‖ = 0 ≠ 1`. -/
theorem scalar_norm_1 [Subsingleton 𝒜] : ‖(1 : 𝒜)‖ = 0 :=
  by
    rw [Subsingleton.elim (1 : 𝒜) 0, norm_zero]

/-- **8II** (cstar.tex:1071, Exercise), part 2: `‖λ·1‖ ≤ |λ|` for every
scalar `λ ∈ ℂ`. -/
theorem scalar_norm_2 (z : ℂ) : ‖algebraMap ℂ 𝒜 z‖ ≤ ‖z‖ :=
  by
    rcases subsingleton_or_nontrivial 𝒜 with h | h
    · simp [Subsingleton.elim (algebraMap ℂ 𝒜 z) 0]
    · rw [Algebra.algebraMap_eq_smul_one, norm_smul, norm_one, mul_one]

/-- **8II** (cstar.tex:1071, Exercise), part 3: `‖λ·1‖ = |λ|` holds when
both sides are interpreted as elements of `𝒜`. -/
theorem scalar_norm_3 (z : ℂ) :
    algebraMap ℂ 𝒜 (‖algebraMap ℂ 𝒜 z‖ : ℂ) = algebraMap ℂ 𝒜 (‖z‖ : ℂ) :=
  by
    rcases subsingleton_or_nontrivial 𝒜 with h | h
    · exact Subsingleton.elim _ _
    · rw [Algebra.algebraMap_eq_smul_one (r := z), norm_smul, norm_one, mul_one]

end Involution

/-! ## Parsec 90: positive elements -/

section CxPositive

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- **9II** (`cx-positive`, cstar.tex:1106, Exercise): for a self-adjoint
`f ∈ C(X)`, `X` compact Hausdorff, the following are equivalent:
(1) `f(X) ⊆ [0,∞)`; (2) `f = g²` for some self-adjoint `g`;
(3) `f = g* g` for some `g`; (4) `‖f - t‖ ≤ t` for some `t ∈ ℝ`;
(5) `‖f - t‖ ≤ t` for all `t ≥ ‖f‖/2`. -/
theorem cx_positive (f : C(X, ℂ)) (hf : IsSelfAdjoint f) :
    List.TFAE [
      ∀ x, 0 ≤ f x,
      ∃ g : C(X, ℂ), IsSelfAdjoint g ∧ f = g ^ 2,
      ∃ g : C(X, ℂ), f = star g * g,
      ∃ t : ℝ, ‖f - algebraMap ℂ C(X, ℂ) (t : ℂ)‖ ≤ t,
      ∀ t : ℝ, ‖f‖ / 2 ≤ t → ‖f - algebraMap ℂ C(X, ℂ) (t : ℂ)‖ ≤ t] :=
  by
    have hstar : ∀ x, (starRingEnd ℂ) (f x) = f x := by
      intro x
      have h := hf.star_eq
      have := congrArg (fun g : C(X, ℂ) => g x) h
      simpa using this
    have him : ∀ x, (f x).im = 0 := by
      intro x
      have h := hstar x
      rw [Complex.ext_iff] at h
      have := h.2
      simp only [Complex.conj_im] at this
      linarith
    tfae_have 1 → 2 := by
      intro h1
      have hcont : Continuous fun x => ((Real.sqrt (f x).re : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp
          (Real.continuous_sqrt.comp (Complex.continuous_re.comp f.continuous))
      refine ⟨⟨_, hcont⟩, ?_, ?_⟩
      · ext x
        simp
      · ext x
        have hre : 0 ≤ (f x).re := (Complex.nonneg_iff.mp (h1 x)).1
        have hsq : ((Real.sqrt (f x).re : ℝ) : ℂ) ^ 2 = ((f x).re : ℂ) := by
          rw [← Complex.ofReal_pow, Real.sq_sqrt hre]
        have hfx : f x = ((f x).re : ℂ) := by
          apply Complex.ext <;> simp [him x]
        simp only [ContinuousMap.pow_apply, ContinuousMap.coe_mk]
        rw [hsq]
        exact hfx
    tfae_have 2 → 3 := by
      rintro ⟨g, hg, rfl⟩
      exact ⟨g, by rw [hg.star_eq, sq]⟩
    tfae_have 3 → 1 := by
      rintro ⟨g, rfl⟩ x
      have hx : (star g * g) x = (starRingEnd ℂ) (g x) * g x := by simp
      rw [hx, Complex.conj_mul', ← Complex.ofReal_pow]
      simp [Complex.nonneg_iff]
    tfae_have 1 → 5 := by
      intro h1 t ht
      have ht0 : 0 ≤ t := le_trans (by positivity) ht
      rw [ContinuousMap.norm_le _ ht0]
      intro x
      have hre : 0 ≤ (f x).re := (Complex.nonneg_iff.mp (h1 x)).1
      have hfx : f x = ((f x).re : ℂ) := by
        apply Complex.ext <;> simp [him x]
      have hle : (f x).re ≤ ‖f‖ := by
        have h := ContinuousMap.norm_coe_le_norm f x
        rw [hfx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre] at h
        exact h
      have hval : (f - algebraMap ℂ C(X, ℂ) (t : ℂ)) x = f x - (t : ℂ) := by simp
      rw [hval, hfx, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    tfae_have 5 → 4 := fun h5 => ⟨‖f‖ / 2, h5 _ le_rfl⟩
    tfae_have 4 → 1 := by
      rintro ⟨t, ht⟩ x
      have hpt : ‖(f - algebraMap ℂ C(X, ℂ) (t : ℂ)) x‖ ≤ t :=
        le_trans (ContinuousMap.norm_coe_le_norm _ x) ht
      have hval : (f - algebraMap ℂ C(X, ℂ) (t : ℂ)) x = f x - (t : ℂ) := by simp
      rw [hval] at hpt
      have hfx : f x = ((f x).re : ℂ) := by
        apply Complex.ext <;> simp [him x]
      rw [hfx, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hpt
      rw [Complex.nonneg_iff]
      exact ⟨by linarith [(abs_le.mp hpt).1], (him x).symm⟩
    tfae_finish

/-- **9III** (cstar.tex:1123, Exercise): `λ ∈ f(X)` iff `f - λ` is not
invertible in `C(X)`. -/
theorem cx_mem_range_iff_not_isUnit (f : C(X, ℂ)) (z : ℂ) :
    (∃ x, f x = z) ↔ ¬IsUnit (f - algebraMap ℂ C(X, ℂ) z) :=
  by
    rw [ContinuousMap.isUnit_iff_forall_ne_zero]
    simp only [not_forall, not_not, ContinuousMap.sub_apply, sub_eq_zero]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by simpa using hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, by simpa using hx⟩

end CxPositive

section Positive

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- Auxiliary: the two ways of viewing a real scalar as an element of a
C*-algebra agree. -/
theorem algebraMap_real_eq (r : ℝ) : algebraMap ℝ 𝒜 r = algebraMap ℂ 𝒜 (r : ℂ) := by
  rw [IsScalarTower.algebraMap_apply ℝ ℂ 𝒜, Complex.coe_algebraMap]

/-- Auxiliary: a real scalar is a self-adjoint element of a C*-algebra. -/
theorem isSelfAdjoint_algebraMap_ofReal (r : ℝ) :
    IsSelfAdjoint (algebraMap ℂ 𝒜 (r : ℂ)) := by
  rw [← algebraMap_real_eq]
  exact IsSelfAdjoint.algebraMap 𝒜 (IsSelfAdjoint.all r)

/-- Auxiliary (**9X**.1): a nonnegative real multiple of a positive element is
positive.  (Proved by conjugating with the scalar `√r`.) -/
theorem ofReal_smul_nonneg {a : 𝒜} (ha : 0 ≤ a) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ (r : ℂ) • a := by
  have h := star_left_conjugate_nonneg ha (algebraMap ℂ 𝒜 (Real.sqrt r : ℂ))
  have he : star (algebraMap ℂ 𝒜 (Real.sqrt r : ℂ)) * a * algebraMap ℂ 𝒜 (Real.sqrt r : ℂ)
      = (r : ℂ) • a := by
    rw [← algebraMap_star_comm]
    simp only [Complex.star_def, Complex.conj_ofReal, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt hr]
  rwa [he] at h

/-- Auxiliary: a nonnegative real scalar is a positive element. -/
theorem algebraMap_ofReal_nonneg {r : ℝ} (hr : 0 ≤ r) :
    (0 : 𝒜) ≤ algebraMap ℂ 𝒜 (r : ℂ) := by
  have h := ofReal_smul_nonneg (zero_le_one (α := 𝒜)) hr
  rwa [← Algebra.algebraMap_eq_smul_one] at h

/-- Auxiliary: `r ↦ r·1` is monotone. -/
theorem algebraMap_ofReal_mono {s t : ℝ} (h : s ≤ t) :
    algebraMap ℂ 𝒜 (s : ℂ) ≤ algebraMap ℂ 𝒜 (t : ℂ) := by
  rw [← sub_nonneg, ← map_sub, ← Complex.ofReal_sub]
  exact algebraMap_ofReal_nonneg (by linarith)

/-- Auxiliary (**17VI**.3a): for a self-adjoint element, `‖a‖ ≤ r` iff
`-r ≤ a ≤ r`. -/
theorem norm_le_iff_neg_algebraMap_le {a : 𝒜} (ha : IsSelfAdjoint a) {r : ℝ}
    (hr : 0 ≤ r) :
    ‖a‖ ≤ r ↔ (-(algebraMap ℂ 𝒜 (r : ℂ)) ≤ a ∧ a ≤ algebraMap ℂ 𝒜 (r : ℂ)) := by
  have hle : a ≤ algebraMap ℂ 𝒜 (‖a‖ : ℂ) := by
    rw [← algebraMap_real_eq]
    exact ha.le_algebraMap_norm_self
  have hge : -(algebraMap ℂ 𝒜 (‖a‖ : ℂ)) ≤ a := by
    rw [← algebraMap_real_eq]
    exact ha.neg_algebraMap_norm_le_self
  constructor
  · intro h
    exact ⟨le_trans (neg_le_neg (algebraMap_ofReal_mono h)) hge,
      le_trans hle (algebraMap_ofReal_mono h)⟩
  · rintro ⟨h1, h2⟩
    rcases subsingleton_or_nontrivial 𝒜 with hs | hs
    · rw [Subsingleton.elim a 0, norm_zero]
      exact hr
    · have h2' : a ≤ algebraMap ℝ 𝒜 r := by
        rw [algebraMap_real_eq]
        exact h2
      have h1' : algebraMap ℝ 𝒜 (-r) ≤ a := by
        rw [algebraMap_real_eq, Complex.ofReal_neg, map_neg]
        exact h1
      rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (a := a) ha with hmem | hmem
      · exact (le_algebraMap_iff_spectrum_le (R := ℝ) (a := a) ha).mp h2' ‖a‖ hmem
      · have h3 := (algebraMap_le_iff_le_spectrum (R := ℝ) (a := a) ha).mp h1' (-‖a‖) hmem
        linarith

/-- **9IV** (`cstar-positive-def`, cstar.tex:1130, Definition): a
self-adjoint `a` is *positive* when `‖a - t‖ ≤ t` for some `t ∈ ℝ`, and
`a ≤ b` means `b - a` is positive.  In this formalization the canonical
order of Mathlib's `[PartialOrder 𝒜] [StarOrderedRing 𝒜]` is used instead;
this lemma records that the two definitions agree.
(**9IVa**, cstar.tex:1143: the interval `[a,b]` is `Set.Icc a b`.) -/
theorem cstar_positive_def (a : 𝒜) (ha : IsSelfAdjoint a) :
    0 ≤ a ↔ ∃ t : ℝ, ‖a - algebraMap ℂ 𝒜 (t : ℂ)‖ ≤ t :=
  by
    constructor
    · intro h
      refine ⟨‖a‖, ?_⟩
      have hsa : IsSelfAdjoint (a - algebraMap ℂ 𝒜 (‖a‖ : ℂ)) :=
        ha.sub (isSelfAdjoint_algebraMap_ofReal ‖a‖)
      rw [norm_le_iff_neg_algebraMap_le hsa (norm_nonneg a)]
      constructor
      · rw [le_sub_iff_add_le, neg_add_cancel]
        exact h
      · rw [sub_le_iff_le_add]
        refine le_trans ?_ (le_add_of_nonneg_left (algebraMap_ofReal_nonneg (norm_nonneg a)))
        rw [← algebraMap_real_eq]
        exact ha.le_algebraMap_norm_self
    · rintro ⟨t, ht⟩
      have ht0 : 0 ≤ t := le_trans (norm_nonneg _) ht
      have hsa : IsSelfAdjoint (a - algebraMap ℂ 𝒜 (t : ℂ)) :=
        ha.sub (isSelfAdjoint_algebraMap_ofReal t)
      have hkey := ((norm_le_iff_neg_algebraMap_le hsa ht0).mp ht).1
      rwa [le_sub_iff_add_le, neg_add_cancel] at hkey

/-! **9VI** (cstar.tex:1180, Example): a bounded operator `T` on a Hilbert
space is positive iff `⟪x, Tx⟫ ≥ 0` for all `x` — stated at **25V**. -/

/-- **9VII** (`cstar-positive-sum`, cstar.tex:1185, Lemma): the sum of two
positive elements of a C*-algebra is positive. -/
theorem cstar_positive_sum (a b : 𝒜) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a + b :=
  add_nonneg ha hb

/-- **9IX** (cstar.tex:1197, Exercise): if `a` is an *effect*
(`0 ≤ a ≤ 1`), then so is its *orthosupplement* `a^⊥ := 1 - a`. -/
theorem effect_orthosupplement (a : 𝒜) (ha : a ∈ effects 𝒜) :
    1 - a ∈ effects 𝒜 :=
  by
    simp only [effects, Set.mem_Icc] at ha ⊢
    exact ⟨sub_nonneg.mpr ha.2, sub_le_self 1 ha.1⟩

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 1: the
positive elements form a *cone*: `0` is positive, sums of positive elements
are positive (**9VII**), and nonnegative real multiples of positive
elements are positive; consequently `≤` is a preorder. -/
theorem cstar_positive_1 (a : 𝒜) (ha : 0 ≤ a) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ (r : ℂ) • a :=
  ofReal_smul_nonneg ha hr

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 2: `1` is
positive and `-‖a‖ ≤ a ≤ ‖a‖` for self-adjoint `a` (so `1` is an order
unit of `sa(𝒜)`). -/
theorem cstar_positive_2 (a : 𝒜) (ha : IsSelfAdjoint a) :
    (0 : 𝒜) ≤ 1 ∧ -(algebraMap ℂ 𝒜 (‖a‖ : ℂ)) ≤ a ∧
      a ≤ algebraMap ℂ 𝒜 (‖a‖ : ℂ) :=
  by
    have key : ∀ r : ℝ, algebraMap ℝ 𝒜 r = algebraMap ℂ 𝒜 (r : ℂ) := fun r => by
      rw [IsScalarTower.algebraMap_apply ℝ ℂ 𝒜, Complex.coe_algebraMap]
    refine ⟨zero_le_one, ?_, ?_⟩
    · have h := ha.neg_algebraMap_norm_le_self
      rwa [key] at h
    · have h := ha.le_algebraMap_norm_self
      rwa [key] at h

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 3: the product
of two positive elements need not be positive (example among the operators
on ℂ²). -/
theorem cstar_positive_3 :
    ∃ a b : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      0 ≤ a ∧ 0 ≤ b ∧ ¬(0 ≤ a * b) :=
  by
    refine ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ),
      Matrix.toEuclideanCLM (𝕜 := ℂ) (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ),
      ?_, ?_, ?_⟩
    · have hP : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)
          = star (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, 0] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose,
            Matrix.conjTranspose_apply]
      rw [hP, map_mul, map_star]
      exact star_mul_self_nonneg _
    · have hQ : (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ)
          = star (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 1; 0, 0] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose,
            Matrix.conjTranspose_apply]
      rw [hQ, map_mul, map_star]
      exact star_mul_self_nonneg _
    · intro hle
      have hsa := hle.isSelfAdjoint
      rw [← map_mul] at hsa
      have h := hsa.star_eq
      rw [← map_star] at h
      have hstar : star ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 1; 1, 1])
          = (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 1; 1, 1] :=
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).injective h
      have h01 := congrFun (congrFun hstar 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply] at h01

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 4: the *order
(semi)norm* `‖a‖ₒ = inf { λ ≥ 0 : -λ ≤ a ≤ λ }` on the self-adjoint
elements. -/
noncomputable def orderNorm (a : 𝒜) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ -(algebraMap ℂ 𝒜 (r : ℂ)) ≤ a ∧ a ≤ algebraMap ℂ 𝒜 (r : ℂ)}

/-- Auxiliary (**9X**.5d): the order seminorm of a self-adjoint element is
its norm. -/
theorem orderNorm_eq_norm {a : 𝒜} (ha : IsSelfAdjoint a) : orderNorm a = ‖a‖ := by
  have hset : {r : ℝ | 0 ≤ r ∧ -(algebraMap ℂ 𝒜 (r : ℂ)) ≤ a ∧ a ≤ algebraMap ℂ 𝒜 (r : ℂ)}
      = Set.Ici ‖a‖ := by
    ext r
    constructor
    · rintro ⟨hr, h1, h2⟩
      exact (norm_le_iff_neg_algebraMap_le ha hr).mpr ⟨h1, h2⟩
    · intro hr
      have hr0 : 0 ≤ r := (norm_nonneg a).trans hr
      exact ⟨hr0, (norm_le_iff_neg_algebraMap_le ha hr0).mp hr⟩
  rw [orderNorm, hset, csInf_Ici]

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 4a: `‖·‖ₒ` is
a seminorm on `sa(𝒜)`: subadditive and absolutely homogeneous. -/
theorem orderNorm_seminorm (a b : 𝒜) (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (r : ℝ) :
    orderNorm (a + b) ≤ orderNorm a + orderNorm b ∧
      orderNorm ((r : ℂ) • a) = |r| * orderNorm a :=
  by
    have hrsa : IsSelfAdjoint ((r : ℂ) • a) := by
      refine IsSelfAdjoint.smul ?_ ha
      rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]
    rw [orderNorm_eq_norm (ha.add hb), orderNorm_eq_norm ha, orderNorm_eq_norm hb,
      orderNorm_eq_norm hrsa]
    exact ⟨norm_add_le a b, by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]⟩

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 4b:
`‖a‖ₒ ≤ ‖a‖` for self-adjoint `a`. -/
theorem orderNorm_le_norm (a : 𝒜) (ha : IsSelfAdjoint a) :
    orderNorm a ≤ ‖a‖ :=
  (orderNorm_eq_norm ha).le

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 4c:
`0 ≤ a ≤ b` implies `‖a‖ₒ ≤ ‖b‖ₒ`. -/
theorem orderNorm_mono (a b : 𝒜) (ha : 0 ≤ a) (hab : a ≤ b) :
    orderNorm a ≤ orderNorm b :=
  by
    have ha' : IsSelfAdjoint a := .of_nonneg ha
    have hb' : IsSelfAdjoint b := .of_nonneg (ha.trans hab)
    rw [orderNorm_eq_norm ha', orderNorm_eq_norm hb']
    exact CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5a: `a²` is
positive for self-adjoint `a` (proved later, at 17V/25I). -/
theorem cstar_positive_5a (a : 𝒜) (ha : IsSelfAdjoint a) : 0 ≤ a ^ 2 :=
  by
    have h : a ^ 2 = star a * a := by rw [ha.star_eq, sq]
    rw [h]
    exact star_mul_self_nonneg a

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5b: a limit of
positive elements is positive. -/
theorem cstar_positive_5b (a : 𝒜) (f : ℕ → 𝒜) (hf : ∀ n, 0 ≤ f n)
    (hlim : Filter.Tendsto f Filter.atTop (nhds a)) : 0 ≤ a :=
  by
    exact ge_of_tendsto hlim (.of_forall hf)

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5c: if
`a ≥ -1/n` for all `n ∈ ℕ`, then `a ≥ 0`. -/
theorem cstar_positive_5c (a : 𝒜) (ha : IsSelfAdjoint a)
    (h : ∀ n : ℕ, -(algebraMap ℂ 𝒜 ((n : ℂ) + 1)⁻¹) ≤ a) : 0 ≤ a :=
  by
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) a ha]
    intro x hx
    have key : ∀ n : ℕ, -((n : ℝ) + 1)⁻¹ ≤ x := by
      intro n
      have hconv : algebraMap ℝ 𝒜 (-((n : ℝ) + 1)⁻¹) = -(algebraMap ℂ 𝒜 ((n : ℂ) + 1)⁻¹) := by
        rw [algebraMap_real_eq, ← map_neg]
        congr 1
        push_cast
        ring
      have hn := h n
      rw [← hconv] at hn
      exact (algebraMap_le_iff_le_spectrum (R := ℝ) (a := a) ha).mp hn x hx
    have h0 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hlim : Filter.Tendsto (fun n : ℕ => -((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
      simpa only [neg_zero] using h0.neg
    exact le_of_tendsto hlim (.of_forall key)

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5d:
`‖a‖ = ‖a‖ₒ` for self-adjoint `a`. -/
theorem cstar_positive_5d (a : 𝒜) (ha : IsSelfAdjoint a) :
    ‖a‖ = orderNorm a :=
  (orderNorm_eq_norm ha).symm

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5e: `a = 0`
when `0 ≤ a ≤ 0` (antisymmetry). -/
theorem cstar_positive_5e (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 0) : a = 0 :=
  by
    exact le_antisymm h1 h0

end Positive

/-! ## Parsec 100: morphisms of C*-algebras -/

section Maps

variable {𝒜 ℬ : Type*} [CStarAlgebra 𝒜] [CStarAlgebra ℬ]

/-- **10II** (`maps`, cstar.tex:1267, Definition), part 1: a linear map
between C*-algebras is *multiplicative* when it preserves products. -/
def IsMultiplicativeMap (f : 𝒜 →ₗ[ℂ] ℬ) : Prop :=
  ∀ a b : 𝒜, f (a * b) = f a * f b

/-- **10II** (`maps`, cstar.tex:1267, Definition), part 2: a linear map is
*involution preserving* when `f(a*) = f(a)*`. -/
def IsInvolutionPreserving (f : 𝒜 →ₗ[ℂ] ℬ) : Prop :=
  ∀ a : 𝒜, f (star a) = star (f a)

/-- **10II** (`maps`, cstar.tex:1267, Definition), part 3: a linear map is
*unital* when `f 1 = 1`.  (Part 4, *subunital* `f 1 ≤ 1`, is
`Theses.Subunital` from `Theses.Common`.) -/
def IsUnitalMap (f : 𝒜 →ₗ[ℂ] ℬ) : Prop :=
  f 1 = 1

section Order

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **10II** (`maps`, cstar.tex:1267, Definition), part 5: a linear map is
*positive* when it maps positive elements to positive elements.
(Mathlib's bundled version: `𝒜 →ₚ[ℂ] ℬ`, `PositiveLinearMap`.) -/
def IsPositiveMap (f : 𝒜 →ₗ[ℂ] ℬ) : Prop :=
  ∀ a : 𝒜, 0 ≤ a → 0 ≤ f a

/-- **10II** (`maps`, cstar.tex:1267, Definition), part 6: a linear map is
*completely positive* when `∑_{i,j} bᵢ* f(aᵢ* aⱼ) bⱼ ≥ 0` for all
`a₁,…,aₙ ∈ 𝒜` and `b₁,…,bₙ ∈ ℬ`.  (Mathlib's bundled version:
`𝒜 →CP ℬ`, `CompletelyPositiveMap`.)

**10III** (cstar.tex:1305): the abbreviations pu, miu, cpsu, … for
combinations of these properties, and the categories `CStar_miu` etc.;
miu-maps are Mathlib's ∗-homomorphisms `𝒜 →⋆ₐ[ℂ] ℬ` (see `Theses.MIUMap`). -/
def IsCompletelyPositiveMap (f : 𝒜 →ₗ[ℂ] ℬ) : Prop :=
  ∀ (n : ℕ) (a : Fin n → 𝒜) (b : Fin n → ℬ),
    0 ≤ ∑ i, ∑ j, star (b i) * f (star (a i) * a j) * b j

/-- **10IV** (`cstar-p-implies-i`, cstar.tex:1338, Lemma (p⇒i)): a positive
linear map between C*-algebras is involution preserving. -/
theorem cstar_p_implies_i (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) :
    IsInvolutionPreserving f :=
  by
    have hsa : ∀ x : 𝒜, IsSelfAdjoint x → IsSelfAdjoint (f x) := by
      intro x hx
      have h1 := CFC.posPart_sub_negPart x hx
      rw [← h1, map_sub]
      exact (IsSelfAdjoint.of_nonneg (hf _ (CFC.posPart_nonneg x))).sub
        (IsSelfAdjoint.of_nonneg (hf _ (CFC.negPart_nonneg x)))
    intro a
    have ha : a = (ℜ a : 𝒜) + Complex.I • (ℑ a : 𝒜) := (realPart_add_I_smul_imaginaryPart a).symm
    have has : star a = (ℜ a : 𝒜) - Complex.I • (ℑ a : 𝒜) := by
      conv_lhs => rw [ha]
      rw [star_add, star_smul, selfAdjoint.star_val_eq, selfAdjoint.star_val_eq]
      simp [sub_eq_add_neg]
    have h1 := hsa _ (ℜ a).property
    have h2 := hsa _ (ℑ a).property
    rw [has, map_sub, map_smul]
    conv_rhs => rw [ha]
    rw [map_add, map_smul, star_add, star_smul, h1.star_eq, h2.star_eq]
    simp [sub_eq_add_neg]

end Order

end Maps

/-! ## Parsec 110: invertible elements and the spectrum -/

section Invertibles

variable {𝒜 : Type*} [CStarAlgebra 𝒜]

/-- **11II** (`geometric`, cstar.tex:1403, Lemma), part 1: for `‖a‖ < 1`
the geometric series `∑ aⁿ` converges absolutely. -/
theorem geometric_1 (a : 𝒜) (ha : ‖a‖ < 1) :
    Summable fun n : ℕ => ‖a ^ n‖ :=
  by
    exact summable_norm_geometric_of_norm_lt_one ha

/-- **11II** (`geometric`, cstar.tex:1403, Lemma), part 2: for `‖a‖ < 1`
the element `a^⊥ = 1 - a` is invertible with inverse `∑ₙ aⁿ`. -/
theorem geometric_2 (a : 𝒜) (ha : ‖a‖ < 1) :
    IsUnit (1 - a) ∧ (1 - a) * ∑' n : ℕ, a ^ n = 1 ∧
      (∑' n : ℕ, a ^ n) * (1 - a) = 1 :=
  by
    exact ⟨⟨Units.oneSub a ha, rfl⟩, mul_neg_geom_series a ha, geom_series_mul_neg a ha⟩

/-- **11VI** (`spectrum-bounded`, cstar.tex:1450, Exercise), part 1:
`a - λ` is invertible for every `λ ∈ ℂ` with `‖a‖ < |λ|`. -/
theorem spectrum_bounded_1 (a : 𝒜) (z : ℂ) (h : ‖a‖ < ‖z‖) :
    IsUnit (a - algebraMap ℂ 𝒜 z) :=
  by
    rcases subsingleton_or_nontrivial 𝒜 with hs | hs
    · exact isUnit_of_subsingleton _
    · have hz : z ∉ spectrum ℂ a := fun hmem =>
        absurd (spectrum.norm_le_norm_of_mem hmem) (not_le.mpr h)
      rw [spectrum.notMem_iff] at hz
      simpa using hz.neg

/-- **11VI** (`spectrum-bounded`, cstar.tex:1450, Exercise), part 2:
`a - b` is invertible when `b` is invertible and `a` is small compared
to `b`.  (The thesis states the hypothesis as `‖a‖ < ‖b‖`, which appears to
be an erratum; the standard — and provable — bound `‖a‖ < ‖b⁻¹‖⁻¹` is used
here.) -/
theorem spectrum_bounded_2 (a : 𝒜) (b : 𝒜ˣ)
    (h : ‖a‖ < ‖((b⁻¹ : 𝒜ˣ) : 𝒜)‖⁻¹) :
    IsUnit (a - (b : 𝒜)) :=
  by
    have hb0 : ‖((b⁻¹ : 𝒜ˣ) : 𝒜)‖ ≠ 0 := by
      intro h0
      rw [h0, inv_zero] at h
      exact absurd h (not_lt.mpr (norm_nonneg a))
    have hpos : 0 < ‖((b⁻¹ : 𝒜ˣ) : 𝒜)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb0)
    have h1 : ‖((b⁻¹ : 𝒜ˣ) : 𝒜) * a‖ < 1 := by
      refine lt_of_le_of_lt (norm_mul_le _ _) ?_
      have h2 := mul_lt_mul_of_pos_left h hpos
      rwa [mul_inv_cancel₀ hb0] at h2
    have hu : IsUnit (1 - ((b⁻¹ : 𝒜ˣ) : 𝒜) * a) := ⟨Units.oneSub _ h1, rfl⟩
    have h3 : IsUnit ((b : 𝒜) * (1 - ((b⁻¹ : 𝒜ˣ) : 𝒜) * a)) := b.isUnit.mul hu
    rw [mul_sub, mul_one, ← mul_assoc] at h3
    simp only [Units.mul_inv, one_mul] at h3
    simpa using h3.neg

/-- **11VI** (`spectrum-bounded`, cstar.tex:1450, Exercise), part 3: the
invertible elements form an open subset of `𝒜`. -/
theorem spectrum_bounded_3 : IsOpen {b : 𝒜 | IsUnit b} :=
  by
    exact Units.isOpen

/-- **11VII** (`geometric-convergence`, cstar.tex:1466, Lemma): for
self-adjoint `a` the series `∑ₙ aⁿ` converges iff `‖a‖ < 1` (and then
converges absolutely, see **11II**). -/
theorem geometric_convergence (a : 𝒜) (ha : IsSelfAdjoint a) :
    (Summable fun n : ℕ => a ^ n) ↔ ‖a‖ < 1 :=
  by
    constructor
    · intro hs
      by_contra hcon
      push_neg at hcon
      have hpow : ∀ k : ℕ, ‖a ^ 2 ^ k‖ = ‖a‖ ^ 2 ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hsa : IsSelfAdjoint (a ^ 2 ^ k) := ha.pow _
          have he : a ^ 2 ^ (k + 1) = (a ^ 2 ^ k) ^ 2 := by
            rw [← pow_mul, ← pow_succ]
          rw [he, cstar_involution_basic_13 _ hsa, ih, ← pow_mul, ← pow_succ]
      have h1 : ∀ k : ℕ, (1 : ℝ) ≤ ‖a ^ 2 ^ k‖ := by
        intro k
        rw [hpow k]
        exact one_le_pow₀ hcon
      have hnorm : Filter.Tendsto (fun n : ℕ => ‖a ^ n‖) Filter.atTop (nhds 0) := by
        simpa using hs.tendsto_atTop_zero.norm
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hnorm 1 one_pos
      have h2 := hN (2 ^ N) (Nat.le_of_lt (Nat.lt_two_pow_self))
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h2
      linarith [h1 N]
    · intro h
      exact summable_geometric_of_norm_lt_one h

/-- **11X** (`cstar-inv-continuous`, cstar.tex:1507, Lemma): the assignment
`a ↦ a⁻¹` is continuous on the set of invertible elements. -/
theorem cstar_inv_continuous :
    ContinuousOn (Ring.inverse : 𝒜 → 𝒜) {a : 𝒜 | IsUnit a} :=
  by
    intro a ha
    have h := NormedRing.inverse_continuousAt (R := 𝒜) ha.unit
    rw [ha.unit_spec] at h
    exact h.continuousWithinAt

/-- **11XIII** (cstar.tex:1547, Lemma): `a - i` is invertible for
self-adjoint `a`. -/
theorem selfAdjoint_sub_I_isUnit (a : 𝒜) (ha : IsSelfAdjoint a) :
    IsUnit (a - algebraMap ℂ 𝒜 Complex.I) :=
  by
    have hI : Complex.I ∉ spectrum ℂ a := by
      intro hmem
      simpa using ha.im_eq_zero_of_mem_spectrum hmem
    rw [spectrum.notMem_iff] at hI
    simpa using hI.neg

/-- **11XV** (`spectrum-self-adjoint-real`, cstar.tex:1569, Exercise),
part 1: `a - λ` is invertible for self-adjoint `a` and `λ ∈ ℂ \ ℝ`. -/
theorem spectrum_self_adjoint_real_1 (a : 𝒜) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z.im ≠ 0) : IsUnit (a - algebraMap ℂ 𝒜 z) :=
  by
    have hI : z ∉ spectrum ℂ a := by
      intro hmem
      exact hz (ha.im_eq_zero_of_mem_spectrum hmem)
    rw [spectrum.notMem_iff] at hI
    simpa using hI.neg

/-- **11XV** (`spectrum-self-adjoint-real`, cstar.tex:1569, Exercise),
part 2: `aⁿ - λ` is invertible for self-adjoint `a`, even `n` (in
particular `n = 2`) and `λ ∈ ℂ \ [0,∞)`. -/
theorem spectrum_self_adjoint_real_2 (a : 𝒜) (ha : IsSelfAdjoint a)
    (n : ℕ) (hn : Even n) (z : ℂ) (hz : ∀ r : ℝ, 0 ≤ r → z ≠ r) :
    IsUnit (a ^ n - algebraMap ℂ 𝒜 z) :=
  by
    rcases subsingleton_or_nontrivial 𝒜 with hs | hs
    · exact isUnit_of_subsingleton _
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have h1 : (1 : ℂ) ≠ z := by
        intro hcon
        exact hz 1 zero_le_one (by rw [← hcon]; norm_num)
      have he : a ^ 0 - algebraMap ℂ 𝒜 z = algebraMap ℂ 𝒜 (1 - z) := by
        rw [map_sub, map_one, pow_zero]
      rw [he]
      exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h1)).map (algebraMap ℂ 𝒜)
    · have hz' : z ∉ spectrum ℂ (a ^ n) := by
        intro hmem
        rw [spectrum.map_pow_of_pos a hn0] at hmem
        obtain ⟨w, hw, rfl⟩ := hmem
        refine hz (w.re ^ n) (hn.pow_nonneg _) ?_
        push_cast
        rw [← ha.mem_spectrum_eq_re hw]
      rw [spectrum.notMem_iff] at hz'
      simpa using hz'.neg

/-- **11XV** (`spectrum-self-adjoint-real`, cstar.tex:1569, Exercise),
part 3: for self-adjoint `a` and *odd* `n`: `aⁿ - λ` is invertible for all
`λ ∈ ℂ \ [0,∞)` iff `a - λ` is invertible for all `λ ∈ ℂ \ [0,∞)`. -/
theorem spectrum_self_adjoint_real_3 (a : 𝒜) (ha : IsSelfAdjoint a)
    (n : ℕ) (hn : Odd n) :
    (∀ z : ℂ, (∀ r : ℝ, 0 ≤ r → z ≠ r) → IsUnit (a ^ n - algebraMap ℂ 𝒜 z)) ↔
      (∀ z : ℂ, (∀ r : ℝ, 0 ≤ r → z ≠ r) → IsUnit (a - algebraMap ℂ 𝒜 z)) :=
  by
    have hn0 : 0 < n := hn.pos
    have hunit : ∀ (b : 𝒜) (z : ℂ), IsUnit (b - algebraMap ℂ 𝒜 z) ↔ z ∉ spectrum ℂ b := by
      intro b z
      rw [spectrum.mem_iff, not_not]
      constructor
      · intro h; rw [← neg_sub]; exact h.neg
      · intro h; rw [← neg_sub] at h; simpa using h.neg
    simp only [hunit]
    constructor
    · -- `spec aⁿ ⊆ ℝ≥0` forces `spec a ⊆ ℝ≥0`, using that `n` is odd
      intro h z hz hmem
      have hzr : z = (z.re : ℂ) := ha.mem_spectrum_eq_re hmem
      have hpow : z ^ n ∈ spectrum ℂ (a ^ n) := spectrum.pow_mem_pow a n hmem
      by_cases hnn : ∀ r : ℝ, 0 ≤ r → z ^ n ≠ (r : ℂ)
      · exact h _ hnn hpow
      · push_neg at hnn
        obtain ⟨r, hr0, hrz⟩ := hnn
        -- `z` is real and `z ^ n = r ≥ 0`, so `z.re ≥ 0` since `n` is odd
        have hre : (z.re : ℂ) ^ n = (r : ℂ) := by rw [← hzr]; exact hrz
        have hre' : z.re ^ n = r := by exact_mod_cast hre
        have : 0 ≤ z.re := by
          have : 0 ≤ z.re ^ n := hre' ▸ hr0
          exact (hn.pow_nonneg_iff).mp this
        exact absurd hzr (hz z.re this)
    · -- `spec a ⊆ ℝ≥0` forces `spec aⁿ ⊆ ℝ≥0`
      intro h z hz hmem
      rw [spectrum.map_pow_of_pos a hn0] at hmem
      obtain ⟨lam, hlam, rfl⟩ := hmem
      by_cases hnn : ∀ r : ℝ, 0 ≤ r → lam ≠ (r : ℂ)
      · exact h _ hnn hlam
      · push_neg at hnn
        obtain ⟨r, hr0, rfl⟩ := hnn
        exact hz (r ^ n) (by positivity) (by push_cast; ring)

variable {ℬ : Type*} [CStarAlgebra ℬ]

/-- **11XVI** (`inverse-permanence`, cstar.tex:1594, Proposition): if a
self-adjoint element `a` of a closed ∗-subalgebra `𝒮` of a C*-algebra `ℬ`
has an inverse in `ℬ`, then `a⁻¹ ∈ 𝒮`. -/
theorem inverse_permanence (𝒮 : StarSubalgebra ℂ ℬ)
    (h𝒮 : IsClosed (𝒮 : Set ℬ)) (a : ℬ) (ha : a ∈ 𝒮)
    (hsa : IsSelfAdjoint a) (hu : IsUnit a) :
    Ring.inverse a ∈ 𝒮 :=
  by
    haveI := h𝒮
    obtain ⟨u, hu2⟩ := (StarSubalgebra.coe_isUnit 𝒮 (a := ⟨a, ha⟩)).mp hu
    have hau : ((u : 𝒮) : ℬ) = a := congrArg Subtype.val hu2
    have h1 : a * ((↑(u⁻¹) : 𝒮) : ℬ) = 1 := by
      rw [← hau, ← MulMemClass.coe_mul, u.mul_inv, OneMemClass.coe_one]
    have key : Ring.inverse a = ((↑(u⁻¹) : 𝒮) : ℬ) := by
      calc Ring.inverse a = Ring.inverse a * (a * ((↑(u⁻¹) : 𝒮) : ℬ)) := by rw [h1, mul_one]
        _ = (Ring.inverse a * a) * ((↑(u⁻¹) : 𝒮) : ℬ) := (mul_assoc _ _ _).symm
        _ = ((↑(u⁻¹) : 𝒮) : ℬ) := by rw [Ring.inverse_mul_cancel a hu, one_mul]
    rw [key]
    exact SetLike.coe_mem _

/-- **11XVIII** (`improved-inverse-permanence`, cstar.tex:1615, Exercise):
the self-adjointness assumption in **11XVI** may be dropped. -/
theorem improved_inverse_permanence (𝒮 : StarSubalgebra ℂ ℬ)
    (h𝒮 : IsClosed (𝒮 : Set ℬ)) (a : ℬ) (ha : a ∈ 𝒮) (hu : IsUnit a) :
    Ring.inverse a ∈ 𝒮 :=
  by
    haveI := h𝒮
    obtain ⟨u, hu2⟩ := (StarSubalgebra.coe_isUnit 𝒮 (a := ⟨a, ha⟩)).mp hu
    have hau : ((u : 𝒮) : ℬ) = a := congrArg Subtype.val hu2
    have h1 : a * ((↑(u⁻¹) : 𝒮) : ℬ) = 1 := by
      rw [← hau, ← MulMemClass.coe_mul, u.mul_inv, OneMemClass.coe_one]
    have key : Ring.inverse a = ((↑(u⁻¹) : 𝒮) : ℬ) := by
      calc Ring.inverse a = Ring.inverse a * (a * ((↑(u⁻¹) : 𝒮) : ℬ)) := by rw [h1, mul_one]
        _ = (Ring.inverse a * a) * ((↑(u⁻¹) : 𝒮) : ℬ) := (mul_assoc _ _ _).symm
        _ = ((↑(u⁻¹) : 𝒮) : ℬ) := by rw [Ring.inverse_mul_cancel a hu, one_mul]
    rw [key]
    exact SetLike.coe_mem _

/-! **11XIX** (`spectrum-of-element`, cstar.tex:1622, Definition): the
*spectrum* of `a` is the set of `λ ∈ ℂ` for which `a - λ` is not
invertible — Mathlib's `spectrum ℂ a`. -/

/-- **11XX** (cstar.tex:1632, Exercise), part 1: the spectrum of a
continuous function `f`, as an element of the C*-algebra `C(X)`, is its
image.  (Mathlib: `ContinuousMap.spectrum_eq_range`.) -/
theorem spectrum_continuousMap {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (f : C(X, ℂ)) :
    spectrum ℂ f = Set.range f :=
  by
    exact ContinuousMap.spectrum_eq_range f

/-- **11XX** (cstar.tex:1632, Exercise), part 2: the spectrum of a square
matrix `A ∈ Mₙ` is its set of eigenvalues. -/
theorem spectrum_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A = {z : ℂ | ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.mulVec v = z • v} :=
  by
    ext z
    have key : ∀ v : Fin n → ℂ,
        (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) z - A).mulVec v = 0 ↔
          A.mulVec v = z • v := by
      intro v
      rw [Matrix.sub_mulVec, sub_eq_zero, Algebra.algebraMap_eq_smul_one,
        Matrix.smul_mulVec, Matrix.one_mulVec]
      exact eq_comm
    rw [Set.mem_setOf_eq, spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, not_not, ← Matrix.exists_mulVec_eq_zero_iff]
    exact exists_congr fun v => and_congr_right fun _ => key v

/-- **11XXI** (`spectrum-basic`, cstar.tex:1648, Exercise), part 1: the
spectrum of a self-adjoint element is real. -/
theorem spectrum_basic_1 (a : 𝒜) (ha : IsSelfAdjoint a) :
    spectrum ℂ a ⊆ Set.range ((↑) : ℝ → ℂ) :=
  by
    intro z hz
    exact ⟨z.re, (ha.mem_spectrum_eq_re hz).symm⟩

/-- **11XXI** (`spectrum-basic`, cstar.tex:1648, Exercise), part 1
(counterexample): the converse fails, e.g. `spec [[0,2],[0,0]] = {0}`
while the matrix is not self-adjoint. -/
theorem spectrum_basic_1' :
    spectrum ℂ (!![0, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = {0} :=
  by
    rw [spectrum_matrix]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨v, hv, hvz⟩
      by_contra hz
      refine hv (funext fun i => ?_)
      have h0 := congrFun hvz 0
      have h1 := congrFun hvz 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        Matrix.vecHead, Matrix.vecTail] at h0 h1
      have hv1 : v 1 = 0 := by
        rcases h1 with h1 | h1
        · exact absurd h1 hz
        · exact h1
      rw [hv1, mul_zero] at h0
      have hv0 : v 0 = 0 := by
        rcases mul_eq_zero.mp h0.symm with h | h
        · exact absurd h hz
        · exact h
      fin_cases i <;> simp [hv0, hv1]
    · rintro rfl
      refine ⟨![1, 0], ?_, ?_⟩
      · intro hc
        have := congrFun hc 0
        simp at this
      · funext i
        fin_cases i <;>
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- **11XXI** (`spectrum-basic`, cstar.tex:1648, Exercise), part 2:
`spec(a²) ⊆ [0,∞)` for self-adjoint `a`. -/
theorem spectrum_basic_2 (a : 𝒜) (ha : IsSelfAdjoint a) :
    spectrum ℂ (a ^ 2) ⊆ {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = r} :=
  by
    intro z hz
    rcases subsingleton_or_nontrivial 𝒜 with hs | hs
    · exact absurd (isUnit_of_subsingleton _) (spectrum.mem_iff.mp hz)
    · rw [spectrum.map_pow_of_pos a (by norm_num : 0 < 2)] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      refine ⟨w.re ^ 2, by positivity, ?_⟩
      push_cast
      rw [← ha.mem_spectrum_eq_re hw]

/-- **11XXI** (`spectrum-basic`, cstar.tex:1648, Exercise), part 3:
`|λ| ≤ ‖a‖` for every `λ ∈ spec(a)`. -/
theorem spectrum_basic_3 (a : 𝒜) (z : ℂ) (hz : z ∈ spectrum ℂ a) :
    ‖z‖ ≤ ‖a‖ :=
  by
    rcases subsingleton_or_nontrivial 𝒜 with hs | hs
    · exact absurd (isUnit_of_subsingleton _) (spectrum.mem_iff.mp hz)
    · exact spectrum.norm_le_norm_of_mem hz

/-- **11XXI** (`spectrum-basic`, cstar.tex:1648, Exercise), part 4: the
spectrum is closed, hence compact. -/
theorem spectrum_basic_4 (a : 𝒜) :
    IsClosed (spectrum ℂ a) ∧ IsCompact (spectrum ℂ a) :=
  by
    exact ⟨(spectrum.isCompact a).isClosed, spectrum.isCompact a⟩

/-- **11XXI** (`spectrum-basic`, cstar.tex:1648, Exercise), part 5:
`spec(a + z) = { λ + z : λ ∈ spec(a) }` for `z ∈ ℂ`. -/
theorem spectrum_basic_5 (a : 𝒜) (z : ℂ) :
    spectrum ℂ (a + algebraMap ℂ 𝒜 z) = (fun w => w + z) '' spectrum ℂ a :=
  by
    have hEq : ∀ w : ℂ, algebraMap ℂ 𝒜 w - (a + algebraMap ℂ 𝒜 z)
        = algebraMap ℂ 𝒜 (w - z) - a := by
      intro w
      rw [map_sub]
      abel
    ext w
    simp only [Set.mem_image, spectrum.mem_iff, hEq]
    constructor
    · intro hw
      exact ⟨w - z, hw, by ring⟩
    · rintro ⟨v, hv, rfl⟩
      simpa using hv

/-- **11XXI** (`spectrum-basic`, cstar.tex:1648, Exercise), part 6:
`spec(a⁻¹) = { λ⁻¹ : λ ∈ spec(a) }` for invertible `a`. -/
theorem spectrum_basic_6 (a : 𝒜ˣ) :
    spectrum ℂ ((a⁻¹ : 𝒜ˣ) : 𝒜) = (fun z => z⁻¹) '' spectrum ℂ (a : 𝒜) :=
  by
    rw [← spectrum.map_inv a]
    ext w
    simp only [Set.mem_inv, Set.mem_image]
    constructor
    · intro hw
      exact ⟨w⁻¹, hw, inv_inv w⟩
    · rintro ⟨v, hv, rfl⟩
      simpa using hv

/-- **11XXIII** (`spectral-permanence`, cstar.tex:1694, Theorem (Spectral
Permanence)): for a closed ∗-subalgebra `𝒮` of a C*-algebra `ℬ` and
`a ∈ 𝒮`, the spectrum of `a` computed in `𝒮` equals the one computed in
`ℬ`.  (Mathlib: `StarSubalgebra.spectrum_eq`.) -/
theorem spectral_permanence (𝒮 : StarSubalgebra ℂ ℬ)
    (h𝒮 : IsClosed (𝒮 : Set ℬ)) (a : 𝒮) :
    spectrum ℂ (a : ℬ) = spectrum ℂ a :=
  by
    haveI := h𝒮
    exact (StarSubalgebra.spectrum_eq 𝒮 (a := a)).symm

end Invertibles

end Theses.A.CStar
