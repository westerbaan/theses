/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 1267–2621.

  parsec 1410:  Hilbert C*-modules: 𝒷-valued inner products, self-duality
  parsec 1420:  Cauchy–Schwarz, seminorms, 𝒷-sesquilinear forms,
                polarization
  parsec 1430:  adjointable maps, the C*-algebra 𝒷ᵃ(X)
  parsec 1440:  vector states are order separating, ⟨Tx,Tx⟩ ≤ ‖T‖²⟨x,x⟩
  parsec 1450:  vector states are completely positive
  parsec 1460:  uniform spaces, the ultranorm uniformity
  parsec 1470:  basics of uniform spaces
  parsec 1480:  ultranorm continuity of the module operations
  parsec 1490:  orthonormal bases; self-dual ⇔ (bounded) ultranorm complete
                ⇔ basis

Statements only; every proof is `sorry`.

Conventions.  Mathlib's `CStarModule 𝒷 X` plays the role of the thesis's
pre-Hilbert 𝒷-modules (`[CompleteSpace X]` for Hilbert 𝒷-modules); note
that Mathlib works with *left* actions and the inner product
`⟪x, y⟫_𝒷 = "y x*"` (left-linear in the second argument:
`⟪x, b • y⟫ = b ⟪x, y⟫`), the mirror image of the thesis's right modules
with `⟨x, y·b⟩ = ⟨x,y⟩b`; all statements below are the faithful mirror
images of the thesis's.  Possibly indefinite 𝒷-valued inner products (used
for the completion in `SelfDualCompletion.lean`) are bundled as `BInner`.
The ultranorm uniformity is represented by its family of seminorms
`unSeminorm ω B x = √(ω (B x x))` for np-functionals `ω` (cf.
`Theses.A.VN.omegaNorm`), through the predicates `UnTendsto`, `UnCauchy`,
`UnDense`, `UnComplete` — the uniform space itself is not bundled.
-/
import Theses.Common
import Theses.A.CStar.Matrices
import Theses.A.VN.Projections

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra WithCStarModule
open Filter Topology Theses Theses.A.CStar Theses.A.VN
open scoped Uniformity

universe u v w

namespace Theses.B.Dils

/-! ## Parsec 1410: Hilbert C*-modules

**141I** (dils.tex:1269): introduction — nothing to formalize. -/

section BInnerDef

variable (𝒷 : Type u) (X : Type v)
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [AddCommGroup X] [Module ℂ X] [SMul 𝒷 X]

/-- **141II** (`dils-basicdfns`, dils.tex:1302, Definition): a **𝒷-valued
inner product** on a (right) 𝒷-module `X` for a C*-algebra `𝒷`: a map
`X × X → 𝒷` which is 𝒷-linear in the second argument, conjugate symmetric
and positive.  (Not necessarily definite; mirrored to Mathlib's left-action
convention, cf. `CStarModule`.)  A *pre-Hilbert 𝒷-module* is a 𝒷-module
with a definite 𝒷-valued inner product — in Mathlib the class
`CStarModule 𝒷 X` (which also bundles the norm `‖x‖ = ‖⟨x,x⟩‖^½`); a
*Hilbert 𝒷-module* is a complete one (`[CompleteSpace X]`). -/
structure BInner : Type (max u v) where
  /-- The inner product `[x, y]`. -/
  inner : X → X → 𝒷
  inner_add_right : ∀ x y z : X, inner x (y + z) = inner x y + inner x z
  inner_op_smul_right : ∀ (b : 𝒷) (x y : X), inner x (b • y) = b * inner x y
  inner_smul_right_complex :
    ∀ (c : ℂ) (x y : X), inner x (c • y) = c • inner x y
  star_inner : ∀ x y : X, star (inner x y) = inner y x
  inner_self_nonneg : ∀ x : X, 0 ≤ inner x x

variable {𝒷 X}

/-- **141II** (`dils-basicdfns`, dils.tex:1302, Definition): a 𝒷-valued
inner product is **definite** when `[x,x] = 0` implies `x = 0`. -/
def BInner.Definite (B : BInner 𝒷 X) : Prop :=
  ∀ x : X, B.inner x x = 0 → x = 0

/-- **141II** (`dils-basicdfns`, dils.tex:1302, Definition), the seminorm
`‖x‖ = ‖[x,x]‖^½` of a 𝒷-valued inner product (that this is a seminorm is
**142V**). -/
noncomputable def BInner.norm (B : BInner 𝒷 X) (x : X) : ℝ :=
  Real.sqrt ‖B.inner x x‖

end BInnerDef

section SelfDualDef

variable (𝒷 : Type u) (X : Type v)
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]

/-- **141IIa** (`moved-dfn-selfdual`, dils.tex:1331): a pre-Hilbert
𝒷-module `X` is **self dual** if every bounded 𝒷-linear map `τ : X → 𝒷`
is of the form `τ = ⟨t, ·⟩` for some `t ∈ X`.

**141IIb** (Beware) and **141III** (Examples: Hilbert spaces, `𝒷` over
itself, closed right ideals, `e𝒷`, direct sums) — not converted. -/
def SelfDual : Prop :=
  ∀ τ : X →ₗ[ℂ] 𝒷, (∀ (b : 𝒷) (x : X), τ (b • x) = b * τ x) →
    (∃ C : ℝ, ∀ x, ‖τ x‖ ≤ C * ‖x‖) →
    ∃ t : X, ∀ x, τ x = inner 𝒷 t x

end SelfDualDef

/-! ## Parsec 1420: Cauchy–Schwarz and sesquilinear forms

**142I** (dils.tex:1388): introduction — nothing to formalize. -/

section CauchySchwarz

variable {𝒷 : Type u} {X : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [AddCommGroup X] [Module ℂ X] [SMul 𝒷 X]

/-- **142II** (`module-innerprod-state`, dils.tex:1399, Definition): for a
𝒷-valued inner product and a positive functional `f : 𝒷 → ℂ`, the
complex-valued form `⟨x,y⟩_f = f([x,y])`. -/
noncomputable def innerF (f : 𝒷 →ₗ[ℂ] ℂ) (B : BInner 𝒷 X) (x y : X) : ℂ :=
  f (B.inner x y)

/-- **142II** (`module-innerprod-state`, dils.tex:1399, Definition): the
seminorm `‖x‖_f = ⟨x,x⟩_f^½`. -/
noncomputable def seminormF (f : 𝒷 →ₗ[ℂ] ℂ) (B : BInner 𝒷 X) (x : X) : ℝ :=
  Real.sqrt (f (B.inner x x)).re

/-- **142II** (`module-innerprod-state`, dils.tex:1399, Definition),
embedded claim: `⟨·,·⟩_f` is a complex-valued (semidefinite) inner product;
in particular it is conjugate symmetric and positive (whence `‖·‖_f` is a
seminorm, by cstar.tex 4XV `inner-product-basic`).

**142IIa** (dils.tex:1411): discussion — nothing to formalize. -/
theorem innerF_inner_product (f : 𝒷 →ₗ[ℂ] ℂ) (hf : IsPositiveMap f)
    (B : BInner 𝒷 X) :
    (∀ x y : X, innerF f B y x = starRingEnd ℂ (innerF f B x y)) ∧
      ∀ x : X, 0 ≤ (innerF f B x x).re ∧ (innerF f B x x).im = 0 :=
  sorry

/-- **142III** (`module-CS`, dils.tex:1419, Proposition (Cauchy–Schwarz)):
for a (possibly indefinite) 𝒷-valued inner product,
`[x,y][y,x] ≤ ‖[y,y]‖ [x,x]`.

**142IV** is the proof — not converted. -/
theorem module_CS (B : BInner 𝒷 X) (x y : X) :
    B.inner x y * B.inner y x ≤ ‖B.inner y y‖ • B.inner x x :=
  sorry

/-- **142V** (`module-seminorm`, dils.tex:1448, Exercise), part 1:
`‖[x,y]‖ ≤ ‖x‖‖y‖` for the seminorm `‖x‖ = ‖[x,x]‖^½`. -/
theorem module_seminorm_1 (B : BInner 𝒷 X) (x y : X) :
    ‖B.inner x y‖ ≤ B.norm x * B.norm y :=
  sorry

/-- **142V** (`module-seminorm`, dils.tex:1448, Exercise), part 2:
`‖x‖ = ‖[x,x]‖^½` is a seminorm with `‖x·b‖ ≤ ‖x‖‖b‖`.

**142VI** (dils.tex:1458): uniform continuity of the operations — the
quantitative statements appear as **148I**–**148V** below. -/
theorem module_seminorm_2 (B : BInner 𝒷 X) (x y : X) (c : ℂ) (b : 𝒷) :
    B.norm (x + y) ≤ B.norm x + B.norm y ∧
      B.norm (c • x) = ‖c‖ * B.norm x ∧
      B.norm (b • x) ≤ B.norm x * ‖b‖ :=
  sorry

/-- **142VII** (dils.tex:1468, Definition): a **𝒷-sesquilinear form** on a
𝒷-module `V`: a map `B : V × V → 𝒷` which is 𝒷-linear in the second
argument and conjugate-𝒷-linear in the first; in the mirrored convention:
`B (β • x) (b • y) = b * B x y * star β`.

**142VIIa** (Remark) — not converted. -/
structure IsBSesquilinear (B : X → X → 𝒷) : Prop where
  add_left : ∀ x y z : X, B (x + y) z = B x z + B y z
  add_right : ∀ x y z : X, B x (y + z) = B x y + B x z
  smul_op : ∀ (β b : 𝒷) (x y : X), B (β • x) (b • y) = b * B x y * star β
  smul_left_complex :
    ∀ (c : ℂ) (x y : X), B (c • x) y = starRingEnd ℂ c • B x y
  smul_right_complex : ∀ (c : ℂ) (x y : X), B x (c • y) = c • B x y

/-! **142VIII** (dils.tex:1487, Example): `⟨·, T·⟩` is a 𝒷-sesquilinear
form for every 𝒷-linear `T` — subsumed by
`hilbmod_sesquilinear_forms` (152V, in `SelfDualCompletion.lean`). -/

/-- **142IX** (`hilbmod-polarization`, dils.tex:1498, Exercise): the
polarization identity `B(x,y) = ¼ ∑_{k=0}^{3} iᵏ B(iᵏx + y, iᵏx + y)` for a
𝒷-sesquilinear form `B`. -/
theorem hilbmod_polarization (B : X → X → 𝒷) (hB : IsBSesquilinear B)
    (x y : X) :
    B x y = (4 : ℂ)⁻¹ •
      ∑ k ∈ Finset.range 4,
        Complex.I ^ k • B (Complex.I ^ k • x + y) (Complex.I ^ k • x + y) :=
  sorry

end CauchySchwarz

/-! ## Parsec 1430: adjointable maps and 𝒷ᵃ(X)

**143I** (dils.tex:1509, Definition): adjointable maps between pre-Hilbert
𝒷-modules and the set `𝒷ᵃ(X)` of adjointable bounded operators — already
formalized in `Theses.A.CStar.Matrices` as `ModuleAdjointTo` /
`ModuleAdjointable` (with uniqueness of adjoints, `moduleAdjointTo_unique`).
**143Ia** (dils.tex:1526): discussion — nothing to formalize. -/

section Adjointable

variable {𝒷 : Type u} {X Y : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul 𝒷 Y] [CStarModule 𝒷 Y]

/-- An operator `T ∈ 𝒷ᵃ(X)` is *positive* when it is of the form `R* R`
for an adjointable bounded `R` (positivity in the C*-algebra `𝒷ᵃ(X)` of
**143IV**); used to state order-separation results below. -/
def IsPositiveOp (𝒷 : Type u) [CStarAlgebra 𝒷] [PartialOrder 𝒷]
    [StarOrderedRing 𝒷] {X : Type v} [NormedAddCommGroup X] [Module ℂ X]
    [SMul 𝒷 X] [CStarModule 𝒷 X] (T : X →L[ℂ] X) : Prop :=
  ∃ R R' : X →L[ℂ] X, ModuleAdjointTo 𝒷 ⇑R ⇑R' ∧ T = R'.comp R

/-- **143II** (`adjointable-cstar-identity`, dils.tex:1532, Lemma), part 1:
for a linear map `T : X → Y` between pre-Hilbert 𝒷-modules and `B > 0`:
`‖Tx‖ ≤ B‖x‖` for all `x` iff `‖⟨y,Tx⟩‖ ≤ B‖y‖‖x‖` for all `x, y`.
(Same statement as cstar.tex 32X, `chilb_form_bounded`.) -/
theorem adjointable_cstar_identity_1 (T : X →ₗ[ℂ] Y) (B : ℝ) (hB : 0 < B) :
    (∀ x : X, ‖T x‖ ≤ B * ‖x‖) ↔
      ∀ (x : X) (y : Y), ‖inner 𝒷 y (T x)‖ ≤ B * ‖y‖ * ‖x‖ :=
  sorry

/-- **143II** (`adjointable-cstar-identity`, dils.tex:1532, Lemma), part 2:
for bounded adjointable `T` (with adjoint `S`): `‖T*‖ = ‖T‖` and
`‖T*T‖ = ‖T‖²`.

**143III** is the proof — not converted. -/
theorem adjointable_cstar_identity_2 (T : X →L[ℂ] Y) (S : Y →L[ℂ] X)
    (h : ModuleAdjointTo 𝒷 ⇑T ⇑S) :
    ‖S‖ = ‖T‖ ∧ ‖S.comp T‖ = ‖T‖ ^ 2 :=
  sorry

/-- **143IV** (`hilbmod-cstar`, dils.tex:1580, Proposition): for a Hilbert
𝒷-module `X` the adjointable bounded operators `𝒷ᵃ(X)` form a C*-algebra.
As in cstar.tex 32XIII (`bax_cstar`) the missing ingredient beyond the
∗-algebra structure and the C*-identity (**143II**) is closedness in
`B(X)`, stated here.  (The type `Ba 𝒷 X` with its C*-algebra structure is
set up in `SelfDualCompletion.lean`.)

**143V** is the proof — not converted. -/
theorem hilbmod_cstar [CompleteSpace X] :
    IsClosed {T : X →L[ℂ] X | ModuleAdjointable 𝒷 ⇑T} :=
  sorry

end Adjointable

/-! ## Parsec 1440 -/

section OrderSep

variable {𝒷 : Type u} {X Y : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]
  [NormedAddCommGroup Y] [Module ℂ Y] [SMul 𝒷 Y] [CStarModule 𝒷 Y]

/-- **144I** (`hilbmod-ordersep`, dils.tex:1623, Proposition): the vector
states on `𝒷ᵃ(X)` are order separating: for adjointable bounded `T`,
`T ≥ 0` (i.e. `T = S*S`) iff `⟨x, Tx⟩ ≥ 0` for all `x ∈ X`.

**144II** is the proof — not converted. -/
theorem hilbmod_ordersep [CompleteSpace X] (T : X →L[ℂ] X)
    (hT : ModuleAdjointable 𝒷 ⇑T) :
    IsPositiveOp 𝒷 T ↔ ∀ x : X, 0 ≤ inner 𝒷 x (T x) :=
  sorry

/-- **144III** (dils.tex:1653, Lemma): an adjointable map between
pre-Hilbert 𝒷-modules is 𝒷-linear (and ℂ-linear) — already stated in
cstar.tex 32I as `moduleAdjointable_linear`, re-exported here.

**144IV** is the proof — not converted. -/
theorem hilbmod_adjointable_blinear (T : X → Y)
    (hT : ModuleAdjointable 𝒷 T) :
    (∀ x x' : X, T (x + x') = T x + T x') ∧
      (∀ (c : ℂ) (x : X), T (c • x) = c • T x) ∧
      ∀ (b : 𝒷) (x : X), T (b • x) = b • T x :=
  Theses.A.CStar.moduleAdjointable_linear T hT

end OrderSep

section BLinearBound

variable {𝒷 : Type u} {X : Type v} {Y : Type w}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [AddCommGroup X] [Module ℂ X] [SMul 𝒷 X]
  [AddCommGroup Y] [Module ℂ Y] [SMul 𝒷 Y]

/-- A 𝒷-linear map between 𝒷-modules with 𝒷-valued inner products,
*bounded* by `C` for the seminorms `‖x‖ = ‖[x,x]‖^½` (auxiliary predicate
for **144V**, **148I**, and the completion theorems). -/
structure IsBoundedModuleMap (B₁ : BInner 𝒷 X) (B₂ : BInner 𝒷 Y)
    (C : ℝ) (T : X → Y) : Prop where
  add : ∀ x y : X, T (x + y) = T x + T y
  smul_complex : ∀ (c : ℂ) (x : X), T (c • x) = c • T x
  smul : ∀ (b : 𝒷) (x : X), T (b • x) = b • T x
  bound : ∀ x : X, B₂.norm (T x) ≤ C * B₁.norm x

/-- **144V** (`blinear-inprod-inequality`, dils.tex:1670, Proposition): a
𝒷-linear map `T : X → Y` between 𝒷-modules with 𝒷-valued inner products
which is bounded by `C ≥ 0` satisfies `[Tx, Tx] ≤ C² [x, x]`.

**144VI** is the proof — not converted. -/
theorem blinear_inprod_inequality (B₁ : BInner 𝒷 X) (B₂ : BInner 𝒷 Y)
    (C : ℝ) (hC : 0 ≤ C) (T : X → Y) (hT : IsBoundedModuleMap B₁ B₂ C T)
    (x : X) :
    B₂.inner (T x) (T x) ≤ (C ^ 2) • B₁.inner x x :=
  sorry

end BLinearBound

/-! ## Parsec 1450 -/

section VectStatesCP

variable {𝒷 : Type u} {X : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]

/-- **145I** (`hilbmod-vectstates-cp`, dils.tex:1706, Proposition): for a
von Neumann algebra `𝒷`, a Hilbert 𝒷-module `X` and `x ∈ X`, the vector
state `h(T) = ⟨x, Tx⟩` on `𝒷ᵃ(X)` is completely positive: for adjointable
`T₁, …, Tₙ` (with adjoints `Sᵢ`) and `b₁, …, bₙ ∈ 𝒷`,
`∑_{i,j} bᵢ* h(Tᵢ* Tⱼ) bⱼ ≥ 0` (mirrored).

**145II** is the proof — not converted. -/
theorem hilbmod_vectstates_cp [VonNeumannAlgebra 𝒷] [CompleteSpace X]
    (x : X) (n : ℕ) (T S : Fin n → (X →L[ℂ] X))
    (hTS : ∀ i, ModuleAdjointTo 𝒷 ⇑(T i) ⇑(S i)) (b : Fin n → 𝒷) :
    0 ≤ ∑ i, ∑ j,
      star (b i) * inner 𝒷 x (((S i).comp (T j)) x) * b j :=
  sorry

end VectStatesCP

/-! ## Parsec 1460: the ultranorm uniformity

**146I** (dils.tex:1730): introduction — nothing to formalize.
**146II** (`dils-dfn-uniformity`, dils.tex:1762, Definition): uniform
spaces — Mathlib's `UniformSpace`; **146III** discussion.
**146IIIa** (dils.tex:1820, Definition): subbases for uniformities. -/

section Uniformity

/-- **146IV** (`exc-subbase`, dils.tex:1827, Exercise): a family `B` of
relations on `X` satisfying reflexivity, the half-entourage axiom and the
symmetry axiom (a *subbase*, **146IIIa**) generates a uniformity: there is
a uniform space structure whose uniformity filter is generated by `B`.

**146V** (`dils-uniformity-examples`, Examples: metric spaces, families of
pseudometrics, seminorms, the ultrastrong/ultraweak uniformities) and
**146VI** — not converted. -/
theorem exc_subbase {X : Type v} (B : Set (Set (X × X)))
    (hrefl : ∀ V ∈ B, ∀ x : X, (x, x) ∈ V)
    (hcomp : ∀ V ∈ B, ∃ W ∈ B, SetRel.comp W W ⊆ V)
    (hsymm : ∀ V ∈ B, ∃ W ∈ B, Prod.swap ⁻¹' W ⊆ V) :
    ∃ U : UniformSpace X, @uniformity X U = Filter.generate B :=
  sorry

end Uniformity

section Ultranorm

variable {𝒷 : Type u}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]

/-- **146VII** (`dils-ultranorm`, dils.tex:1889, Definition): the seminorm
`‖x‖_ω = ω([x,x])^½` of an np-functional `ω : 𝒷 → ℂ`, for a 𝒷-module with
𝒷-valued inner product `B` (given as a bare function `B : X → X → 𝒷` so
that this applies to `BInner`s, to `CStarModule`s via `inner 𝒷`, and to `𝒷`
itself via `mulInner`).  The family of these seminorms, over all
np-functionals `ω`, constitutes the **ultranorm uniformity**; it is encoded
through the predicates `UnTendsto`, `UnCauchy`, `UnDense`, `UnComplete`
below.

**146VIII**–**146X** (relation to the norm and ultrastrong uniformities;
Beware; Remarks) — not converted. -/
noncomputable def unSeminorm {X : Type v} [AddCommGroup X]
    (ω : NPFunctional 𝒷) (B : X → X → 𝒷) (x : X) : ℝ :=
  Real.sqrt (ω (B x x)).re

/-- The inner product `⟨x, y⟩ = y x*` of the C*-algebra `𝒷` viewed as a
module over itself (Mathlib's `CStarModule 𝒷 𝒷` instance); with respect to
it the ultranorm uniformity on `𝒷` is the ultrastrong uniformity
(**146VIII**). -/
def mulInner (𝒷 : Type u) [CStarAlgebra 𝒷] : 𝒷 → 𝒷 → 𝒷 :=
  fun a b => b * star a

variable {X : Type v} [AddCommGroup X]

/-- **147I**.1 (`uniformity-basics`, dils.tex:1930, Definition),
specialized to the ultranorm uniformity: a net `x : ι → X` (along a filter
`l`) *converges ultranorm* to `x₀` when `‖x i - x₀‖_ω → 0` for every
np-functional `ω`. -/
def UnTendsto {ι : Type w} (B : X → X → 𝒷) (x : ι → X) (l : Filter ι)
    (x₀ : X) : Prop :=
  ∀ ω : NPFunctional 𝒷, Tendsto (fun i => unSeminorm ω B (x i - x₀)) l (𝓝 0)

/-- **147I**.2 (`uniformity-basics`, dils.tex:1930, Definition),
specialized to the ultranorm uniformity: a filter `F` on `X` (e.g. the
eventuality filter of a net) is *ultranorm Cauchy* when it contains, for
every `ω` and `ε > 0`, a set of diameter `≤ ε` for `‖·‖_ω`. -/
def UnCauchy (B : X → X → 𝒷) (F : Filter X) : Prop :=
  ∀ (ω : NPFunctional 𝒷) (ε : ℝ), 0 < ε →
    ∃ s ∈ F, ∀ x ∈ s, ∀ y ∈ s, unSeminorm ω B (x - y) ≤ ε

/-- **147I**.5 (`uniformity-basics`, dils.tex:1930, Definition),
specialized to the ultranorm uniformity: a subset `D ⊆ X` is *ultranorm
dense* when every `x ∈ X` is approximated within every entourage (finitely
many seminorms, `ε > 0`) by an element of `D`. -/
def UnDense (B : X → X → 𝒷) (D : Set X) : Prop :=
  ∀ (x : X) (n : ℕ) (ωs : Fin n → NPFunctional 𝒷) (ε : ℝ), 0 < ε →
    ∃ d ∈ D, ∀ i, unSeminorm (ωs i) B (x - d) ≤ ε

/-- **147I**.2 (`uniformity-basics`, dils.tex:1930, Definition), continued:
the ultranorm uniformity on `X` is *complete* when every (nontrivial)
ultranorm Cauchy filter converges. -/
def UnComplete (B : X → X → 𝒷) : Prop :=
  ∀ F : Filter X, F.NeBot → UnCauchy B F → ∃ x₀, UnTendsto B id F x₀

end Ultranorm

/-! ## Parsec 1470: basics of uniform spaces

**147I** (`uniformity-basics`, dils.tex:1930, Definition): convergence,
Cauchy nets, (uniform) continuity, equivalence of Cauchy nets, density —
Mathlib's `Tendsto`/`Cauchy`/`UniformContinuous`/`Dense` (for the ultranorm
uniformity, the specialized predicates above). -/

section UniformBasics

variable {X Y : Type v} [UniformSpace X] [UniformSpace Y]

/-- Two filters on a uniform space are *equivalent* (as Cauchy nets,
**147I**.4) when they contain arbitrarily `𝓤`-close pairs of sets
(auxiliary for **147II**). -/
def FilterEquiv (F G : Filter X) : Prop :=
  ∀ V ∈ 𝓤 X, ∃ s ∈ F, ∃ t ∈ G, s ×ˢ t ⊆ V

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1982, Exercise), part
1: equivalence of Cauchy filters is reflexive, symmetric and transitive. -/
theorem dils_uniform_spaces_basics_1 :
    (∀ F : Filter X, Cauchy F → FilterEquiv F F) ∧
    (∀ F G : Filter X, Cauchy F → Cauchy G → FilterEquiv F G →
      FilterEquiv G F) ∧
    (∀ F G H : Filter X, Cauchy F → Cauchy G → Cauchy H →
      FilterEquiv F G → FilterEquiv G H → FilterEquiv F H) :=
  sorry

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1982, Exercise), part
2: equivalent Cauchy filters have the same limits. -/
theorem dils_uniform_spaces_basics_2 (F G : Filter X) (hF : Cauchy F)
    (hG : Cauchy G) (h : FilterEquiv F G) (x : X) (hFx : F ≤ 𝓝 x) :
    G ≤ 𝓝 x :=
  sorry

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1982, Exercise), part
3: limits are unique in a Hausdorff uniform space (Mathlib:
`tendsto_nhds_unique`). -/
theorem dils_uniform_spaces_basics_3 [T2Space X] {ι : Type w} (l : Filter ι)
    [l.NeBot] (x : ι → X) (a b : X) (ha : Tendsto x l (𝓝 a))
    (hb : Tendsto x l (𝓝 b)) : a = b :=
  sorry

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1982, Exercise), part
4: continuous maps preserve limits of nets (Mathlib:
`Continuous.tendsto.comp`). -/
theorem dils_uniform_spaces_basics_4 (f : X → Y) (hf : Continuous f)
    {ι : Type w} (l : Filter ι) (x : ι → X) (a : X)
    (ha : Tendsto x l (𝓝 a)) : Tendsto (f ∘ x) l (𝓝 (f a)) :=
  sorry

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1982, Exercise), part
5: uniformly continuous maps send Cauchy filters to Cauchy filters and
preserve equivalence (Mathlib: `Cauchy.map`). -/
theorem dils_uniform_spaces_basics_5 (f : X → Y) (hf : UniformContinuous f) :
    (∀ F : Filter X, Cauchy F → Cauchy (F.map f)) ∧
    (∀ F G : Filter X, Cauchy F → Cauchy G → FilterEquiv F G →
      FilterEquiv (F.map f) (G.map f)) :=
  sorry

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1982, Exercise), part
6: for a dense `D ⊆ X`, every point is the limit of a Cauchy filter living
on `D`. -/
theorem dils_uniform_spaces_basics_6 (D : Set X) (hD : Dense D) (x : X) :
    ∃ F : Filter X, F.NeBot ∧ D ∈ F ∧ Cauchy F ∧ F ≤ 𝓝 x :=
  sorry

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1982, Exercise), part
7: continuous maps into a Hausdorff space agreeing on a dense set are equal
(Mathlib: `Continuous.ext_on`). -/
theorem dils_uniform_spaces_basics_7 [T2Space Y] (f g : X → Y)
    (hf : Continuous f) (hg : Continuous g) (D : Set X) (hD : Dense D)
    (h : Set.EqOn f g D) : f = g :=
  sorry

/-- **147III** (`dils-product-uniformity`, dils.tex:2021, Exercise): the
product uniformity (Mathlib: `Pi.uniformSpace`) makes the projections
uniformly continuous and is the categorical product: a map into the product
is uniformly continuous iff all its components are (Mathlib:
`uniformContinuous_pi`). -/
theorem dils_product_uniformity {ι : Type w} {Z : ι → Type v}
    [∀ i, UniformSpace (Z i)] (f : X → ∀ i, Z i) :
    (∀ i, UniformContinuous fun z : ∀ i, Z i => z i) ∧
      (UniformContinuous f ↔ ∀ i, UniformContinuous fun x => f x i) :=
  sorry

end UniformBasics

/-! ## Parsec 1480: ultranorm continuity of the operations -/

section UltranormContinuity

variable {𝒷 : Type u} {X Y : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [AddCommGroup X] [Module ℂ X] [SMul 𝒷 X]
  [AddCommGroup Y] [Module ℂ Y] [SMul 𝒷 Y]

/-- **148I** (`blinear-bounded-is-ultranorm`, dils.tex:2041, Proposition):
a bounded 𝒷-linear map `T : X → Y` between 𝒷-modules with 𝒷-valued inner
products is uniformly ultranorm continuous: for every `ω` and `ε > 0` there
is `δ > 0` with `‖x-y‖_ω ≤ δ ⟹ ‖Tx-Ty‖_ω ≤ ε`.

**148II** is the proof — not converted. -/
theorem blinear_bounded_is_ultranorm (B₁ : BInner 𝒷 X) (B₂ : BInner 𝒷 Y)
    (C : ℝ) (T : X → Y) (hT : IsBoundedModuleMap B₁ B₂ C T)
    (ω : NPFunctional 𝒷) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ x y : X, unSeminorm ω B₁.inner (x - y) ≤ δ →
      unSeminorm ω B₂.inner (T x - T y) ≤ ε :=
  sorry

variable {ι : Type w} {l : Filter ι}

/-- **148III** (`ultranormcontstruct`, dils.tex:2060, Corollary), part 1:
addition is (jointly uniformly) ultranorm continuous: it preserves
ultranorm limits. -/
theorem ultranormcontstruct_add (B : BInner 𝒷 X) (x y : ι → X) (x₀ y₀ : X)
    (hx : UnTendsto B.inner x l x₀) (hy : UnTendsto B.inner y l y₀) :
    UnTendsto B.inner (fun i => x i + y i) l (x₀ + y₀) :=
  sorry

/-- **148III** (`ultranormcontstruct`, dils.tex:2060, Corollary), part 2:
for fixed `x₀`, the map `x ↦ [x₀, x] : X → 𝒷` is uniformly continuous from
the ultranorm uniformity of `X` to the ultrastrong uniformity of `𝒷` (the
ultranorm uniformity of `mulInner`): it preserves limits. -/
theorem ultranormcontstruct_inner [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 X)
    (x₀ : X) (x : ι → X) (xlim : X) (hx : UnTendsto B.inner x l xlim) :
    UnTendsto (mulInner 𝒷) (fun i => B.inner x₀ (x i)) l (B.inner x₀ xlim) :=
  sorry

/-- **148III** (`ultranormcontstruct`, dils.tex:2060, Corollary), part 3:
for fixed `x₀`, the map `b ↦ x₀ · b : 𝒷 → X` is uniformly continuous from
the ultrastrong uniformity of `𝒷` to the ultranorm uniformity of `X`
(mirrored: `b • x₀`): it preserves limits. -/
theorem ultranormcontstruct_smul [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 X)
    (x₀ : X) (b : ι → 𝒷) (blim : 𝒷)
    (hb : UnTendsto (mulInner 𝒷) b l blim) :
    UnTendsto B.inner (fun i => b i • x₀) l (blim • x₀) :=
  sorry

/-- **148IV** (`ultranormscalar`, dils.tex:2072, Exercise): for fixed
`b ∈ 𝒷`, the map `x ↦ x·b` (mirrored: `b • x`) is ultranorm continuous:
it preserves ultranorm limits. -/
theorem ultranormscalar (B : BInner 𝒷 X) (b : 𝒷) (x : ι → X) (xlim : X)
    (hx : UnTendsto B.inner x l xlim) :
    UnTendsto B.inner (fun i => b • x i) l (b • xlim) :=
  sorry

/-- **148V** (`innerprod-ultraweak`, dils.tex:2078, Proposition): if
`x_α → x` and `y_α → y` in the ultranorm uniformity, then
`[x_α, y_α] → [x, y]` ultraweakly.

**148VI** is the proof — not converted. -/
theorem innerprod_ultraweak (B : BInner 𝒷 X) (x y : ι → X) (xlim ylim : X)
    (hx : UnTendsto B.inner x l xlim) (hy : UnTendsto B.inner y l ylim) :
    UWTendsto (fun i => B.inner (x i) (y i)) l (B.inner xlim ylim) :=
  sorry

end UltranormContinuity

section DenseOrderSep

variable {𝒷 : Type u} {X : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]

/-- **148VII** (`hilbmod-denseordersep`, dils.tex:2116, Corollary): for a
Hilbert 𝒷-module `X` with ultranorm-dense subset `D`, the vector states
from `D` are order separating: for adjointable bounded `T`, `T ≥ 0` iff
`⟨x, Tx⟩ ≥ 0` for all `x ∈ D`. -/
theorem hilbmod_denseordersep [CompleteSpace X] (D : Set X)
    (hD : UnDense (inner 𝒷) D) (T : X →L[ℂ] X)
    (hT : ModuleAdjointable 𝒷 ⇑T) :
    IsPositiveOp 𝒷 T ↔ ∀ x ∈ D, 0 ≤ inner 𝒷 x (T x) :=
  sorry

end DenseOrderSep

/-! ## Parsec 1490: orthonormal bases and self-duality -/

section Bases

variable {𝒷 : Type u} {X : Type v} {ι : Type w}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]

variable (𝒷)

/-- **149I** (`dfn-selfdual-basis`, dils.tex:2127, Definition), part 1: a
family in a pre-Hilbert 𝒷-module is **orthogonal** when distinct members
have inner product `0`. -/
def OrthogonalFam (e : ι → X) : Prop :=
  ∀ i j : ι, i ≠ j → inner 𝒷 (e i) (e j) = 0

/-- **149I** (`dfn-selfdual-basis`, dils.tex:2127, Definition), part 2: an
orthogonal family is **orthonormal** when moreover each `⟨e,e⟩` is a
non-zero projection. -/
def OrthonormalFam (e : ι → X) : Prop :=
  OrthogonalFam 𝒷 e ∧
    ∀ i : ι, IsStarProjection (inner 𝒷 (e i) (e i)) ∧
      inner 𝒷 (e i) (e i) ≠ 0

variable (X) in
/-- **149I** (`dfn-selfdual-basis`, dils.tex:2127, Definition), part 3: a
family `(bᵢ)` in `𝒷` is **ℓ²-summable** when the partial sums of
`∑ᵢ bᵢ* bᵢ` are (norm-)bounded (mirrored: `∑ᵢ bᵢ bᵢ*`). -/
def L2Summable (b : ι → 𝒷) : Prop :=
  ∃ M : ℝ, ∀ s : Finset ι, ‖∑ i ∈ s, b i * star (b i)‖ ≤ M

/-- **149I** (`dfn-selfdual-basis`, dils.tex:2127, Definition), part 4: an
orthonormal family `(eᵢ)` is an **(orthonormal) basis** when (a) every
`x ∈ X` is the ultranorm limit of `∑ᵢ eᵢ⟨eᵢ,x⟩` (mirrored:
`∑ᵢ ⟨eᵢ,x⟩ • eᵢ`), and (b) `∑ᵢ eᵢbᵢ` converges ultranorm for every
ℓ²-summable family `(bᵢ)`.

**149II**–**149IIb** (Notation, Remark, Beware) — not converted. -/
def IsONBasis (e : ι → X) : Prop :=
  OrthonormalFam 𝒷 e ∧
    (∀ x : X,
      UnTendsto (inner 𝒷)
        (fun s : Finset ι => ∑ i ∈ s, inner 𝒷 (e i) x • e i) atTop x) ∧
    ∀ b : ι → 𝒷, L2Summable 𝒷 b →
      ∃ x : X, UnTendsto (inner 𝒷)
        (fun s : Finset ι => ∑ i ∈ s, b i • e i) atTop x

variable {𝒷}

/-- **149III** (`mod-projelabs`, dils.tex:2216, Exercise): if `⟨e,e⟩` is a
projection, then `e⟨e,e⟩ = e` (mirrored: `⟨e,e⟩ • e = e`). -/
theorem mod_projelabs (e : X) (he : IsStarProjection (inner 𝒷 e e)) :
    inner 𝒷 e e • e = e :=
  sorry

/-- **149IV** (`mod-parseval`, dils.tex:2225, Exercise (Parseval's
identity)): for an orthonormal basis `(eᵢ)` of a pre-Hilbert 𝒷-module over
a von Neumann algebra, `⟨x,x⟩ = ∑ᵢ ⟨x,eᵢ⟩⟨eᵢ,x⟩`, the sum converging
ultraweakly. -/
theorem mod_parseval [VonNeumannAlgebra 𝒷] (e : ι → X)
    (he : IsONBasis 𝒷 e) (x : X) :
    UWTendsto
      (fun s : Finset ι => ∑ i ∈ s, inner 𝒷 (e i) x * inner 𝒷 x (e i))
      atTop (inner 𝒷 x x) :=
  sorry

variable (𝒷 X) in
/-- Norm-bounded ultranorm completeness (condition 3 of **149V**): every
norm-bounded ultranorm-Cauchy filter converges. -/
def BddUnComplete : Prop :=
  ∀ F : Filter X, F.NeBot → UnCauchy (inner 𝒷) F →
    (∃ M : ℝ, ∃ s ∈ F, ∀ x ∈ s, ‖x‖ ≤ M) →
    ∃ x₀, UnTendsto (inner 𝒷) id F x₀

/-- **149V** (`dils-selfdual`, dils.tex:2236, Theorem): for a pre-Hilbert
𝒷-module `X` over a von Neumann algebra `𝒷` the following are equivalent:
(1) `X` is self dual; (2) `X` is ultranorm complete; (3) every norm-bounded
ultranorm-Cauchy net converges; (4) `X` has an orthonormal basis (indexed
by a set of elements of `X`, i.e. a family over a type in the universe of
`X`).

**149VI**–**149XI** are the proof — not converted. -/
theorem dils_selfdual [VonNeumannAlgebra 𝒷] :
    List.TFAE
      [SelfDual 𝒷 X,
       UnComplete (inner 𝒷 : X → X → 𝒷),
       BddUnComplete 𝒷 X,
       ∃ (ι' : Type v) (e : ι' → X), IsONBasis 𝒷 e] :=
  sorry

end Bases

end Theses.B.Dils
