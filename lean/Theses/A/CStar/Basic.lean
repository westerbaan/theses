/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 1: C*-algebras — cstar.tex, lines 1–1713.

  §Definition and Examples  (parsecs 20–60: C*-algebras, Hilbert spaces,
                             bounded operators, B(H))
  §The Basics               (parsecs 70–110: self-adjoint elements, positive
                             elements, morphisms, invertibles, spectrum,
                             spectral permanence)

Statements only; every proof is `sorry`.  See CONVENTIONS.md for the
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
  sorry

/-- **4III** (`bounded-operators-basic`, cstar.tex:326, Exercise), part 2:
`‖S ∘ T‖ ≤ ‖S‖ ‖T‖` for bounded operators `T : 𝒳 → 𝒴`, `S : 𝒴 → 𝒵`. -/
theorem boundedOperators_basic_2 (S : 𝒴 →L[ℂ] 𝒵) (T : 𝒳 →L[ℂ] 𝒴) :
    ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ :=
  sorry

/-- **4III** (`bounded-operators-basic`, cstar.tex:326, Exercise), part 3:
the identity operator is bounded by 1. -/
theorem boundedOperators_basic_3 : ‖(ContinuousLinearMap.id ℂ 𝒳)‖ ≤ 1 :=
  sorry

/-- **4IV** (`operator-norm-ball`, cstar.tex:343, Exercise):
`r ‖T‖ = sup { ‖T x‖ : ‖x‖ ≤ r }` for a bounded operator `T` and
`r ∈ [0,∞)`. -/
theorem operatorNorm_ball (T : 𝒳 →L[ℂ] 𝒴) (r : ℝ) (hr : 0 ≤ r) :
    r * ‖T‖ = ⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖ :=
  sorry

/-- **4V** (`operator-norm-complete`, cstar.tex:359, Lemma): the operator
norm on `B(𝒳,𝒴)` is complete when `𝒴` is complete.  (Mathlib instance:
`ContinuousLinearMap.completeSpace`.) -/
theorem operatorNorm_complete [CompleteSpace 𝒴] : CompleteSpace (𝒳 →L[ℂ] 𝒴) :=
  sorry

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
  sorry

/-- **4X** (`uniqueness-adjoint`, cstar.tex:496, Exercise), part 2: every
operator between pre-Hilbert spaces has at most one adjoint. -/
theorem uniqueness_adjoint_2 (T : H → K) (S S' : K → H)
    (hS : IsAdjointTo T S) (hS' : IsAdjointTo T S') : S = S' :=
  sorry

/-- **4XII** (cstar.tex:520, Exercise), part 1: if `T` is adjoint to `S`
then `S` is adjoint to `T` (so `T** = T`). -/
theorem isAdjointTo_symm (T : H → K) (S : K → H) (h : IsAdjointTo T S) :
    IsAdjointTo S T :=
  sorry

/-- **4XII** (cstar.tex:520, Exercise), part 2 (sums): `(T + T')* = T* + T'*`
for adjointable operators on a pre-Hilbert space. -/
theorem isAdjointTo_add (T T' : H → K) (S S' : K → H)
    (h : IsAdjointTo T S) (h' : IsAdjointTo T' S') :
    IsAdjointTo (T + T') (S + S') :=
  sorry

/-- **4XII** (cstar.tex:520, Exercise), part 2 (scalars):
`(λ T)* = conj λ · T*`. -/
theorem isAdjointTo_smul (T : H → K) (S : K → H) (z : ℂ)
    (h : IsAdjointTo T S) :
    IsAdjointTo (fun x => z • T x) (fun y => (starRingEnd ℂ) z • S y) :=
  sorry

/-- **4XII** (cstar.tex:520, Exercise), part 3: `S ∘ T` is adjoint to
`T* ∘ S*`, i.e. `(ST)* = T* S*`. -/
theorem isAdjointTo_comp {L : Type*} [NormedAddCommGroup L]
    [InnerProductSpace ℂ L] (T : H → K) (T' : K → H) (S : K → L) (S' : L → K)
    (hT : IsAdjointTo T T') (hS : IsAdjointTo S S') :
    IsAdjointTo (S ∘ T) (T' ∘ S') :=
  sorry

/-- **4XIII** (`positive-2x2matrix`, cstar.tex:540, Lemma), part 1: if the
2×2 matrix `[[p, c̄], [c, q]]` is positive (i.e. `(ū v̄) A (u v)ᵀ ≥ 0` for
all `u, v ∈ ℂ`), then `p, q ≥ 0`. -/
theorem positive_2x2matrix_1 (p q c : ℂ)
    (h : ∀ u v : ℂ, 0 ≤ (starRingEnd ℂ) u * (p * u + (starRingEnd ℂ) c * v)
      + (starRingEnd ℂ) v * (c * u + q * v)) :
    0 ≤ p ∧ 0 ≤ q :=
  sorry

/-- **4XIII** (`positive-2x2matrix`, cstar.tex:540, Lemma), part 2: for a
positive 2×2 matrix `[[p, c̄], [c, q]]` we have `|c|² ≤ p q`. -/
theorem positive_2x2matrix_2 (p q c : ℂ)
    (h : ∀ u v : ℂ, 0 ≤ (starRingEnd ℂ) u * (p * u + (starRingEnd ℂ) c * v)
      + (starRingEnd ℂ) v * (c * u + q * v)) :
    ((‖c‖ : ℂ)) ^ 2 ≤ p * q :=
  sorry

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
  sorry

/-- **4XV** (`inner-product-basic`, cstar.tex:590, Exercise), part 2:
Pythagoras' theorem: `‖x‖² + ‖y‖² = ‖x + y‖²` when `⟪x,y⟫ = 0`. -/
theorem inner_product_basic_2 (x y : H) (h : ⟪x, y⟫ = 0) :
    ‖x‖ ^ 2 + ‖y‖ ^ 2 = ‖x + y‖ ^ 2 :=
  sorry

/-- **4XV** (`inner-product-basic`, cstar.tex:590, Exercise), part 3: the
parallelogram law. -/
theorem inner_product_basic_3 (x y : H) :
    ‖x‖ ^ 2 + ‖y‖ ^ 2 = (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2 :=
  sorry

/-- **4XV** (`inner-product-basic`, cstar.tex:590, Exercise), part 4: the
polarisation identity `⟪x,y⟫ = ¼ ∑_{n<4} iⁿ ‖iⁿ x + y‖²`. -/
theorem inner_product_basic_4 (x y : H) :
    ⟪x, y⟫ = (∑ n ∈ Finset.range 4,
      Complex.I ^ n * ((‖(Complex.I ^ n : ℂ) • x + y‖ : ℂ)) ^ 2) / 4 :=
  sorry

/-- **4XVI** (`operators-cstar-identity`, cstar.tex:642, Lemma), part 1: for
a bounded adjointable operator `T` on a pre-Hilbert space, `‖T* T‖ = ‖T‖²`
(the C*-identity). -/
theorem operators_cstar_identity_1 (T S : H →L[ℂ] H)
    (h : IsAdjointTo T S) : ‖S.comp T‖ = ‖T‖ ^ 2 :=
  sorry

/-- **4XVI** (`operators-cstar-identity`, cstar.tex:642, Lemma), part 2:
`‖T*‖ = ‖T‖`. -/
theorem operators_cstar_identity_2 (T S : H →L[ℂ] H)
    (h : IsAdjointTo T S) : ‖S‖ = ‖T‖ :=
  sorry

/-- **4XVIII** (cstar.tex:666, Exercise): for a Hilbert space `H` the
adjointable operators form a closed (sub)space of `B(H)`. -/
theorem adjointable_isClosed [CompleteSpace H] :
    IsClosed {T : H →L[ℂ] H | Adjointable (⇑T)} :=
  sorry

/-- **4XIX** (`ketbra`, cstar.tex:671, Exercise): the operator
`|x⟩⟨y| : z ↦ ⟪y, z⟫ x` on a Hilbert space, bounded by construction. -/
noncomputable def ketbra (x y : H) : H →L[ℂ] H :=
  (innerSL ℂ y).smulRight x

/-- **4XIX** (`ketbra`, cstar.tex:671, Exercise), part 1: `|x⟩⟨y|` maps `z`
to `⟪y, z⟫ x` and has operator norm `‖x‖ ‖y‖`. -/
theorem ketbra_norm (x y : H) : ‖ketbra x y‖ = ‖x‖ * ‖y‖ :=
  sorry

/-- **4XIX** (`ketbra`, cstar.tex:671, Exercise), part 2: `|x⟩⟨y|` is
adjointable, with `(|x⟩⟨y|)* = |y⟩⟨x|`. -/
theorem ketbra_adjoint (x y : H) :
    IsAdjointTo (⇑(ketbra x y)) (⇑(ketbra y x)) :=
  sorry

/-! ## Parsec 50 (`hilb-adjoint`): projections, Riesz representation, B(H)

**5I** (`adjoinables-cstar-algebra`, cstar.tex:689): the adjointable
operators on a Hilbert space form a C*-algebra; to see that `B(H)` is one
it remains to show every bounded operator is adjointable (**5XI**). -/

/-- **5II** (`projection-on-closed-linear-subspace`, cstar.tex:702,
Definition): `y` is a *projection of `x` on* a linear subspace `C` when
`y ∈ C` and `‖x - y‖ = min { ‖x - y'‖ : y' ∈ C }`. -/
def IsProjectionOn (C : Submodule ℂ H) (x y : H) : Prop :=
  y ∈ C ∧ ∀ y' ∈ C, ‖x - y‖ ≤ ‖x - y'‖

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
  sorry

/-- **5IV** (cstar.tex:726, Lemma): for a unit vector `e` of a pre-Hilbert
space, `⟪e, x⟫ e` is a projection of `x` on the line `ℂe`. -/
theorem projection_on_line (x e : H) (he : ‖e‖ = 1) :
    IsProjectionOn (ℂ ∙ e) x (⟪e, x⟫ • e) :=
  sorry

/-- **5IV** (cstar.tex:726, Lemma), uniqueness part: `⟪e, x⟫ e` is the
*unique* projection of `x` on `ℂe`. -/
theorem projection_on_line_unique (x e : H) (he : ‖e‖ = 1) (y : H)
    (hy : IsProjectionOn (ℂ ∙ e) x y) : y = ⟪e, x⟫ • e :=
  sorry

/-- **5VI** (`hilb-projection-basic`, cstar.tex:755, Exercise), part 1: a
projection `y` of `x` on a linear subspace `C` is a projection of `x` on
the line `ℂy`. -/
theorem hilb_projection_basic_1 (C : Submodule ℂ H) (x y : H)
    (h : IsProjectionOn C x y) : IsProjectionOn (ℂ ∙ y) x y :=
  sorry

/-- **5VI** (`hilb-projection-basic`, cstar.tex:755, Exercise), part 2: the
projection of `x` on `C` is unique, and `⟪y, x - y⟫ = 0`. -/
theorem hilb_projection_basic_2 (C : Submodule ℂ H) (x y y' : H)
    (h : IsProjectionOn C x y) (h' : IsProjectionOn C x y') :
    y' = y ∧ ⟪y, x - y⟫ = 0 :=
  sorry

/-- **5VI** (`hilb-projection-basic`, cstar.tex:755, Exercise), part 3:
`y + c` is the projection of `x + c` on `C` for every `c ∈ C`. -/
theorem hilb_projection_basic_3 (C : Submodule ℂ H) (x y : H)
    (h : IsProjectionOn C x y) (c : H) (hc : c ∈ C) :
    IsProjectionOn C (x + c) (y + c) :=
  sorry

/-- **5VI** (`hilb-projection-basic`, cstar.tex:755, Exercise), part 4:
`⟪y', x - y⟫ = 0` for every `y' ∈ C`. -/
theorem hilb_projection_basic_4 (C : Submodule ℂ H) (x y : H)
    (h : IsProjectionOn C x y) (y' : H) (hy' : y' ∈ C) :
    ⟪y', x - y⟫ = 0 :=
  sorry

/-- **5VII** (`projection-theorem`, cstar.tex:766, Projection Theorem): every
vector `x` of a Hilbert space has a unique projection `y` on a closed linear
subspace `C`.  (Mathlib: `Submodule.orthogonalProjection`.) -/
theorem projection_theorem [CompleteSpace H] (C : Submodule ℂ H)
    (hC : IsClosed (C : Set H)) (x : H) :
    ∃! y, IsProjectionOn C x y :=
  sorry

/-- **5VII** (`projection-theorem`, cstar.tex:766, Projection Theorem),
second part: the projection `y` of `x` on `C` satisfies `⟪y', y⟫ = ⟪y', x⟫`
for all `y' ∈ C`. -/
theorem projection_theorem_inner [CompleteSpace H] (C : Submodule ℂ H)
    (hC : IsClosed (C : Set H)) (x y : H) (h : IsProjectionOn C x y) :
    ∀ y' ∈ C, ⟪y', y⟫ = ⟪y', x⟫ :=
  sorry

/-- **5IX** (`riesz-representation-theorem`, cstar.tex:811, Riesz'
Representation Theorem): for every bounded linear map `f : H → ℂ` on a
Hilbert space there is a unique `x ∈ H` with `⟪x, ·⟫ = f`.  (Mathlib:
`InnerProductSpace.toDual`.) -/
theorem riesz_representation_theorem [CompleteSpace H] (f : H →L[ℂ] ℂ) :
    ∃! x : H, ∀ z : H, ⟪x, z⟫ = f z :=
  sorry

/-- **5XI** (`bounded-operator-adjoinable`, cstar.tex:842, Exercise): every
bounded operator on a Hilbert space is adjointable.  (Mathlib:
`ContinuousLinearMap.adjoint`.) -/
theorem bounded_operator_adjoinable [CompleteSpace H] (T : H →L[ℂ] H) :
    ∃ S : H →L[ℂ] H, IsAdjointTo (⇑T) (⇑S) :=
  sorry

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
  sorry

/-- **6II** (`hilb-sum`, cstar.tex:873, Proposition), part 2: `⊕ᵢ Hᵢ` with
the inner product `⟪x, y⟫ = ∑ᵢ ⟪xᵢ, yᵢ⟫` is a Hilbert space (i.e. the
resulting norm is complete).  (Mathlib: `lp.completeSpace` and the
`InnerProductSpace` instance on `lp Hi 2`.) -/
theorem hilb_sum_complete : CompleteSpace (lp Hi 2) :=
  sorry

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
  sorry

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 2:
if `a = b + i·c` with `b, c` self-adjoint then `b = ℜa` and `c = ℑa`. -/
theorem cstar_involution_basic_2 (a b c : 𝒜) (hb : IsSelfAdjoint b)
    (hc : IsSelfAdjoint c) (h : a = b + Complex.I • c) :
    b = (ℜ a : 𝒜) ∧ c = (ℑ a : 𝒜) :=
  sorry

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 3:
`ℜ(a*) = ℜa` and `ℑ(a*) = -ℑa`. -/
theorem cstar_involution_basic_3 (a : 𝒜) :
    (ℜ (star a) : 𝒜) = (ℜ a : 𝒜) ∧ (ℑ (star a) : 𝒜) = -(ℑ a : 𝒜) :=
  sorry

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 4:
`a` is self-adjoint iff `ℜa = a` iff `ℑa = 0`. -/
theorem cstar_involution_basic_4 (a : 𝒜) :
    (IsSelfAdjoint a ↔ (ℜ a : 𝒜) = a) ∧ (IsSelfAdjoint a ↔ (ℑ a : 𝒜) = 0) :=
  sorry

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 5:
`a ↦ ℜa` and `a ↦ ℑa` are ℝ-linear (in Mathlib they are bundled as
`𝒜 →ₗ[ℝ] selfAdjoint 𝒜`; we state additivity as sample claim). -/
theorem cstar_involution_basic_5 (a b : 𝒜) :
    (ℜ (a + b) : 𝒜) = (ℜ a : 𝒜) + (ℜ b : 𝒜) ∧
      (ℑ (a + b) : 𝒜) = (ℑ a : 𝒜) + (ℑ b : 𝒜) :=
  sorry

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 6:
`ℑa = -ℜ(ia)` and `ℜa = ℑ(ia)`. -/
theorem cstar_involution_basic_6 (a : 𝒜) :
    (ℑ a : 𝒜) = -(ℜ (Complex.I • a) : 𝒜) ∧
      (ℜ a : 𝒜) = (ℑ (Complex.I • a) : 𝒜) :=
  sorry

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 7:
`a* a` is self-adjoint, and
`a* a = (ℜa)² + (ℑa)² + i(ℜa·ℑa - ℑa·ℜa)`. -/
theorem cstar_involution_basic_7 (a : 𝒜) :
    IsSelfAdjoint (star a * a) ∧
      star a * a = (ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2 +
        Complex.I • ((ℜ a : 𝒜) * (ℑ a : 𝒜) - (ℑ a : 𝒜) * (ℜ a : 𝒜)) :=
  sorry

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 8:
real and imaginary part need not commute: an example in the 2×2 matrices. -/
theorem cstar_involution_basic_8 :
    ∃ a : Matrix (Fin 2) (Fin 2) ℂ,
      (ℜ a : Matrix (Fin 2) (Fin 2) ℂ) * (ℑ a : Matrix (Fin 2) (Fin 2) ℂ) ≠
        (ℑ a : Matrix (Fin 2) (Fin 2) ℂ) * (ℜ a : Matrix (Fin 2) (Fin 2) ℂ) :=
  sorry

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 9:
`a* a + a a* = 2((ℜa)² + (ℑa)²)`. -/
theorem cstar_involution_basic_9 (a : 𝒜) :
    star a * a + a * star a = 2 * ((ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2) :=
  sorry

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 10:
for self-adjoint `b, c` the product `bc` is self-adjoint iff `bc = cb`. -/
theorem cstar_involution_basic_10 (b c : 𝒜) (hb : IsSelfAdjoint b)
    (hc : IsSelfAdjoint c) : IsSelfAdjoint (b * c) ↔ b * c = c * b :=
  sorry

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 11:
`‖a*‖ = ‖a‖`.  (Mathlib: `norm_star`.) -/
theorem cstar_involution_basic_11 (a : 𝒜) : ‖star a‖ = ‖a‖ :=
  sorry

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 12:
`‖ℜa‖ ≤ ‖a‖` and `‖ℑa‖ ≤ ‖a‖`. -/
theorem cstar_involution_basic_12 (a : 𝒜) :
    ‖(ℜ a : 𝒜)‖ ≤ ‖a‖ ∧ ‖(ℑ a : 𝒜)‖ ≤ ‖a‖ :=
  sorry

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 13:
`‖a²‖ = ‖a‖²` for self-adjoint `a`. -/
theorem cstar_involution_basic_13 (a : 𝒜) (ha : IsSelfAdjoint a) :
    ‖a ^ 2‖ = ‖a‖ ^ 2 :=
  sorry

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 13
(counterexample): `‖a²‖ ≠ ‖a‖²` may occur for non-self-adjoint `a`
(e.g. `[[0,1],[0,0]]` as an operator on ℂ²). -/
theorem cstar_involution_basic_13' :
    ∃ T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      ‖T ^ 2‖ ≠ ‖T‖ ^ 2 :=
  sorry

/-! ## Parsec 80: scalars in a C*-algebra

**8I** (cstar.tex:1060, Notation): for `λ ∈ ℂ` we write `λ` also for the
element `λ·1` of `𝒜`; in Lean this is `algebraMap ℂ 𝒜 λ`. -/

/-- **8II** (cstar.tex:1071, Exercise), part 1: in the trivial C*-algebra
`{0}` we have `‖1‖ = 0 ≠ 1`. -/
theorem scalar_norm_1 [Subsingleton 𝒜] : ‖(1 : 𝒜)‖ = 0 :=
  sorry

/-- **8II** (cstar.tex:1071, Exercise), part 2: `‖λ·1‖ ≤ |λ|` for every
scalar `λ ∈ ℂ`. -/
theorem scalar_norm_2 (z : ℂ) : ‖algebraMap ℂ 𝒜 z‖ ≤ ‖z‖ :=
  sorry

/-- **8II** (cstar.tex:1071, Exercise), part 3: `‖λ·1‖ = |λ|` holds when
both sides are interpreted as elements of `𝒜`. -/
theorem scalar_norm_3 (z : ℂ) :
    algebraMap ℂ 𝒜 (‖algebraMap ℂ 𝒜 z‖ : ℂ) = algebraMap ℂ 𝒜 (‖z‖ : ℂ) :=
  sorry

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
  sorry

/-- **9III** (cstar.tex:1123, Exercise): `λ ∈ f(X)` iff `f - λ` is not
invertible in `C(X)`. -/
theorem cx_mem_range_iff_not_isUnit (f : C(X, ℂ)) (z : ℂ) :
    (∃ x, f x = z) ↔ ¬IsUnit (f - algebraMap ℂ C(X, ℂ) z) :=
  sorry

end CxPositive

section Positive

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **9IV** (`cstar-positive-def`, cstar.tex:1130, Definition): a
self-adjoint `a` is *positive* when `‖a - t‖ ≤ t` for some `t ∈ ℝ`, and
`a ≤ b` means `b - a` is positive.  In this formalization the canonical
order of Mathlib's `[PartialOrder 𝒜] [StarOrderedRing 𝒜]` is used instead;
this lemma records that the two definitions agree.
(**9IVa**, cstar.tex:1143: the interval `[a,b]` is `Set.Icc a b`.) -/
theorem cstar_positive_def (a : 𝒜) (ha : IsSelfAdjoint a) :
    0 ≤ a ↔ ∃ t : ℝ, ‖a - algebraMap ℂ 𝒜 (t : ℂ)‖ ≤ t :=
  sorry

/-! **9VI** (cstar.tex:1180, Example): a bounded operator `T` on a Hilbert
space is positive iff `⟪x, Tx⟫ ≥ 0` for all `x` — stated at **25V**. -/

/-- **9VII** (`cstar-positive-sum`, cstar.tex:1185, Lemma): the sum of two
positive elements of a C*-algebra is positive. -/
theorem cstar_positive_sum (a b : 𝒜) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a + b :=
  sorry

/-- **9IX** (cstar.tex:1197, Exercise): if `a` is an *effect*
(`0 ≤ a ≤ 1`), then so is its *orthosupplement* `a^⊥ := 1 - a`. -/
theorem effect_orthosupplement (a : 𝒜) (ha : a ∈ effects 𝒜) :
    1 - a ∈ effects 𝒜 :=
  sorry

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 1: the
positive elements form a *cone*: `0` is positive, sums of positive elements
are positive (**9VII**), and nonnegative real multiples of positive
elements are positive; consequently `≤` is a preorder. -/
theorem cstar_positive_1 (a : 𝒜) (ha : 0 ≤ a) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ (r : ℂ) • a :=
  sorry

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 2: `1` is
positive and `-‖a‖ ≤ a ≤ ‖a‖` for self-adjoint `a` (so `1` is an order
unit of `sa(𝒜)`). -/
theorem cstar_positive_2 (a : 𝒜) (ha : IsSelfAdjoint a) :
    (0 : 𝒜) ≤ 1 ∧ -(algebraMap ℂ 𝒜 (‖a‖ : ℂ)) ≤ a ∧
      a ≤ algebraMap ℂ 𝒜 (‖a‖ : ℂ) :=
  sorry

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 3: the product
of two positive elements need not be positive (example among the operators
on ℂ²). -/
theorem cstar_positive_3 :
    ∃ a b : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      0 ≤ a ∧ 0 ≤ b ∧ ¬(0 ≤ a * b) :=
  sorry

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 4: the *order
(semi)norm* `‖a‖ₒ = inf { λ ≥ 0 : -λ ≤ a ≤ λ }` on the self-adjoint
elements. -/
noncomputable def orderNorm (a : 𝒜) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ -(algebraMap ℂ 𝒜 (r : ℂ)) ≤ a ∧ a ≤ algebraMap ℂ 𝒜 (r : ℂ)}

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 4a: `‖·‖ₒ` is
a seminorm on `sa(𝒜)`: subadditive and absolutely homogeneous. -/
theorem orderNorm_seminorm (a b : 𝒜) (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (r : ℝ) :
    orderNorm (a + b) ≤ orderNorm a + orderNorm b ∧
      orderNorm ((r : ℂ) • a) = |r| * orderNorm a :=
  sorry

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 4b:
`‖a‖ₒ ≤ ‖a‖` for self-adjoint `a`. -/
theorem orderNorm_le_norm (a : 𝒜) (ha : IsSelfAdjoint a) :
    orderNorm a ≤ ‖a‖ :=
  sorry

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 4c:
`0 ≤ a ≤ b` implies `‖a‖ₒ ≤ ‖b‖ₒ`. -/
theorem orderNorm_mono (a b : 𝒜) (ha : 0 ≤ a) (hab : a ≤ b) :
    orderNorm a ≤ orderNorm b :=
  sorry

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5a: `a²` is
positive for self-adjoint `a` (proved later, at 17V/25I). -/
theorem cstar_positive_5a (a : 𝒜) (ha : IsSelfAdjoint a) : 0 ≤ a ^ 2 :=
  sorry

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5b: a limit of
positive elements is positive. -/
theorem cstar_positive_5b (a : 𝒜) (f : ℕ → 𝒜) (hf : ∀ n, 0 ≤ f n)
    (hlim : Filter.Tendsto f Filter.atTop (nhds a)) : 0 ≤ a :=
  sorry

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5c: if
`a ≥ -1/n` for all `n ∈ ℕ`, then `a ≥ 0`. -/
theorem cstar_positive_5c (a : 𝒜) (ha : IsSelfAdjoint a)
    (h : ∀ n : ℕ, -(algebraMap ℂ 𝒜 ((n : ℂ) + 1)⁻¹) ≤ a) : 0 ≤ a :=
  sorry

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5d:
`‖a‖ = ‖a‖ₒ` for self-adjoint `a`. -/
theorem cstar_positive_5d (a : 𝒜) (ha : IsSelfAdjoint a) :
    ‖a‖ = orderNorm a :=
  sorry

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5e: `a = 0`
when `0 ≤ a ≤ 0` (antisymmetry). -/
theorem cstar_positive_5e (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 0) : a = 0 :=
  sorry

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
  sorry

end Order

end Maps

/-! ## Parsec 110: invertible elements and the spectrum -/

section Invertibles

variable {𝒜 : Type*} [CStarAlgebra 𝒜]

/-- **11II** (`geometric`, cstar.tex:1403, Lemma), part 1: for `‖a‖ < 1`
the geometric series `∑ aⁿ` converges absolutely. -/
theorem geometric_1 (a : 𝒜) (ha : ‖a‖ < 1) :
    Summable fun n : ℕ => ‖a ^ n‖ :=
  sorry

/-- **11II** (`geometric`, cstar.tex:1403, Lemma), part 2: for `‖a‖ < 1`
the element `a^⊥ = 1 - a` is invertible with inverse `∑ₙ aⁿ`. -/
theorem geometric_2 (a : 𝒜) (ha : ‖a‖ < 1) :
    IsUnit (1 - a) ∧ (1 - a) * ∑' n : ℕ, a ^ n = 1 ∧
      (∑' n : ℕ, a ^ n) * (1 - a) = 1 :=
  sorry

/-- **11VI** (`spectrum-bounded`, cstar.tex:1450, Exercise), part 1:
`a - λ` is invertible for every `λ ∈ ℂ` with `‖a‖ < |λ|`. -/
theorem spectrum_bounded_1 (a : 𝒜) (z : ℂ) (h : ‖a‖ < ‖z‖) :
    IsUnit (a - algebraMap ℂ 𝒜 z) :=
  sorry

/-- **11VI** (`spectrum-bounded`, cstar.tex:1450, Exercise), part 2:
`a - b` is invertible when `b` is invertible and `a` is small compared
to `b`.  (The thesis states the hypothesis as `‖a‖ < ‖b‖`, which appears to
be an erratum; the standard — and provable — bound `‖a‖ < ‖b⁻¹‖⁻¹` is used
here.) -/
theorem spectrum_bounded_2 (a : 𝒜) (b : 𝒜ˣ)
    (h : ‖a‖ < ‖((b⁻¹ : 𝒜ˣ) : 𝒜)‖⁻¹) :
    IsUnit (a - (b : 𝒜)) :=
  sorry

/-- **11VI** (`spectrum-bounded`, cstar.tex:1450, Exercise), part 3: the
invertible elements form an open subset of `𝒜`. -/
theorem spectrum_bounded_3 : IsOpen {b : 𝒜 | IsUnit b} :=
  sorry

/-- **11VII** (`geometric-convergence`, cstar.tex:1466, Lemma): for
self-adjoint `a` the series `∑ₙ aⁿ` converges iff `‖a‖ < 1` (and then
converges absolutely, see **11II**). -/
theorem geometric_convergence (a : 𝒜) (ha : IsSelfAdjoint a) :
    (Summable fun n : ℕ => a ^ n) ↔ ‖a‖ < 1 :=
  sorry

/-- **11X** (`cstar-inv-continuous`, cstar.tex:1507, Lemma): the assignment
`a ↦ a⁻¹` is continuous on the set of invertible elements. -/
theorem cstar_inv_continuous :
    ContinuousOn (Ring.inverse : 𝒜 → 𝒜) {a : 𝒜 | IsUnit a} :=
  sorry

/-- **11XIII** (cstar.tex:1547, Lemma): `a - i` is invertible for
self-adjoint `a`. -/
theorem selfAdjoint_sub_I_isUnit (a : 𝒜) (ha : IsSelfAdjoint a) :
    IsUnit (a - algebraMap ℂ 𝒜 Complex.I) :=
  sorry

/-- **11XV** (`spectrum-self-adjoint-real`, cstar.tex:1569, Exercise),
part 1: `a - λ` is invertible for self-adjoint `a` and `λ ∈ ℂ \ ℝ`. -/
theorem spectrum_self_adjoint_real_1 (a : 𝒜) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z.im ≠ 0) : IsUnit (a - algebraMap ℂ 𝒜 z) :=
  sorry

/-- **11XV** (`spectrum-self-adjoint-real`, cstar.tex:1569, Exercise),
part 2: `aⁿ - λ` is invertible for self-adjoint `a`, even `n` (in
particular `n = 2`) and `λ ∈ ℂ \ [0,∞)`. -/
theorem spectrum_self_adjoint_real_2 (a : 𝒜) (ha : IsSelfAdjoint a)
    (n : ℕ) (hn : Even n) (z : ℂ) (hz : ∀ r : ℝ, 0 ≤ r → z ≠ r) :
    IsUnit (a ^ n - algebraMap ℂ 𝒜 z) :=
  sorry

/-- **11XV** (`spectrum-self-adjoint-real`, cstar.tex:1569, Exercise),
part 3: for self-adjoint `a` and *odd* `n`: `aⁿ - λ` is invertible for all
`λ ∈ ℂ \ [0,∞)` iff `a - λ` is invertible for all `λ ∈ ℂ \ [0,∞)`. -/
theorem spectrum_self_adjoint_real_3 (a : 𝒜) (ha : IsSelfAdjoint a)
    (n : ℕ) (hn : Odd n) :
    (∀ z : ℂ, (∀ r : ℝ, 0 ≤ r → z ≠ r) → IsUnit (a ^ n - algebraMap ℂ 𝒜 z)) ↔
      (∀ z : ℂ, (∀ r : ℝ, 0 ≤ r → z ≠ r) → IsUnit (a - algebraMap ℂ 𝒜 z)) :=
  sorry

variable {ℬ : Type*} [CStarAlgebra ℬ]

/-- **11XVI** (`inverse-permanence`, cstar.tex:1594, Proposition): if a
self-adjoint element `a` of a closed ∗-subalgebra `𝒮` of a C*-algebra `ℬ`
has an inverse in `ℬ`, then `a⁻¹ ∈ 𝒮`. -/
theorem inverse_permanence (𝒮 : StarSubalgebra ℂ ℬ)
    (h𝒮 : IsClosed (𝒮 : Set ℬ)) (a : ℬ) (ha : a ∈ 𝒮)
    (hsa : IsSelfAdjoint a) (hu : IsUnit a) :
    Ring.inverse a ∈ 𝒮 :=
  sorry

/-- **11XVIII** (`improved-inverse-permanence`, cstar.tex:1615, Exercise):
the self-adjointness assumption in **11XVI** may be dropped. -/
theorem improved_inverse_permanence (𝒮 : StarSubalgebra ℂ ℬ)
    (h𝒮 : IsClosed (𝒮 : Set ℬ)) (a : ℬ) (ha : a ∈ 𝒮) (hu : IsUnit a) :
    Ring.inverse a ∈ 𝒮 :=
  sorry

/-! **11XIX** (`spectrum-of-element`, cstar.tex:1622, Definition): the
*spectrum* of `a` is the set of `λ ∈ ℂ` for which `a - λ` is not
invertible — Mathlib's `spectrum ℂ a`. -/

/-- **11XX** (cstar.tex:1632, Exercise), part 1: the spectrum of a
continuous function `f`, as an element of the C*-algebra `C(X)`, is its
image.  (Mathlib: `ContinuousMap.spectrum_eq_range`.) -/
theorem spectrum_continuousMap {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (f : C(X, ℂ)) :
    spectrum ℂ f = Set.range f :=
  sorry

/-- **11XX** (cstar.tex:1632, Exercise), part 2: the spectrum of a square
matrix `A ∈ Mₙ` is its set of eigenvalues. -/
theorem spectrum_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A = {z : ℂ | ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.mulVec v = z • v} :=
  sorry

/-- **11XXI** (`spectrum-basic`, cstar.tex:1648, Exercise), part 1: the
spectrum of a self-adjoint element is real. -/
theorem spectrum_basic_1 (a : 𝒜) (ha : IsSelfAdjoint a) :
    spectrum ℂ a ⊆ Set.range ((↑) : ℝ → ℂ) :=
  sorry

/-- **11XXI** (`spectrum-basic`, cstar.tex:1648, Exercise), part 1
(counterexample): the converse fails, e.g. `spec [[0,2],[0,0]] = {0}`
while the matrix is not self-adjoint. -/
theorem spectrum_basic_1' :
    spectrum ℂ (!![0, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = {0} :=
  sorry

/-- **11XXI** (`spectrum-basic`, cstar.tex:1648, Exercise), part 2:
`spec(a²) ⊆ [0,∞)` for self-adjoint `a`. -/
theorem spectrum_basic_2 (a : 𝒜) (ha : IsSelfAdjoint a) :
    spectrum ℂ (a ^ 2) ⊆ {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = r} :=
  sorry

/-- **11XXI** (`spectrum-basic`, cstar.tex:1648, Exercise), part 3:
`|λ| ≤ ‖a‖` for every `λ ∈ spec(a)`. -/
theorem spectrum_basic_3 (a : 𝒜) (z : ℂ) (hz : z ∈ spectrum ℂ a) :
    ‖z‖ ≤ ‖a‖ :=
  sorry

/-- **11XXI** (`spectrum-basic`, cstar.tex:1648, Exercise), part 4: the
spectrum is closed, hence compact. -/
theorem spectrum_basic_4 (a : 𝒜) :
    IsClosed (spectrum ℂ a) ∧ IsCompact (spectrum ℂ a) :=
  sorry

/-- **11XXI** (`spectrum-basic`, cstar.tex:1648, Exercise), part 5:
`spec(a + z) = { λ + z : λ ∈ spec(a) }` for `z ∈ ℂ`. -/
theorem spectrum_basic_5 (a : 𝒜) (z : ℂ) :
    spectrum ℂ (a + algebraMap ℂ 𝒜 z) = (fun w => w + z) '' spectrum ℂ a :=
  sorry

/-- **11XXI** (`spectrum-basic`, cstar.tex:1648, Exercise), part 6:
`spec(a⁻¹) = { λ⁻¹ : λ ∈ spec(a) }` for invertible `a`. -/
theorem spectrum_basic_6 (a : 𝒜ˣ) :
    spectrum ℂ ((a⁻¹ : 𝒜ˣ) : 𝒜) = (fun z => z⁻¹) '' spectrum ℂ (a : 𝒜) :=
  sorry

/-- **11XXIII** (`spectral-permanence`, cstar.tex:1694, Theorem (Spectral
Permanence)): for a closed ∗-subalgebra `𝒮` of a C*-algebra `ℬ` and
`a ∈ 𝒮`, the spectrum of `a` computed in `𝒮` equals the one computed in
`ℬ`.  (Mathlib: `StarSubalgebra.spectrum_eq`.) -/
theorem spectral_permanence (𝒮 : StarSubalgebra ℂ ℬ)
    (h𝒮 : IsClosed (𝒮 : Set ℬ)) (a : 𝒮) :
    spectrum ℂ (a : ℬ) = spectrum ℂ a :=
  sorry

end Invertibles

end Theses.A.CStar
