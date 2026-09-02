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
import Theses.A.VN.Completeness
import Theses.A.VN.NormalFunctionals

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra WithCStarModule
open Filter Topology Theses Theses.A.CStar Theses.A.VN
open scoped Uniformity

universe u v w

namespace Theses.B.Dils

/-! ## Parsec 1410: Hilbert C*-modules

**141I** (dils.tex:1277): introduction — nothing to formalize. -/

section BInnerDef

variable (𝒷 : Type u) (X : Type v)
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [AddCommGroup X] [Module ℂ X] [SMul 𝒷 X]

/-- **141II** (`dils-basicdfns`, dils.tex:1310, Definition): a **𝒷-valued
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

/-- **141II** (`dils-basicdfns`, dils.tex:1310, Definition): a 𝒷-valued
inner product is **definite** when `[x,x] = 0` implies `x = 0`. -/
def BInner.Definite (B : BInner 𝒷 X) : Prop :=
  ∀ x : X, B.inner x x = 0 → x = 0

/-- **141II** (`dils-basicdfns`, dils.tex:1310, Definition), the seminorm
`‖x‖ = ‖[x,x]‖^½` of a 𝒷-valued inner product (that this is a seminorm is
**142V**). -/
noncomputable def BInner.norm (B : BInner 𝒷 X) (x : X) : ℝ :=
  Real.sqrt ‖B.inner x x‖

end BInnerDef

/-- The bundled 𝒷-valued inner product of a `CStarModule` (used to compare
`BInner`-modules with `CStarModule`s). -/
def cstarBInner (𝒷 : Type u) (X : Type w) [CStarAlgebra 𝒷] [PartialOrder 𝒷]
    [StarOrderedRing 𝒷] [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X]
    [CStarModule 𝒷 X] : BInner 𝒷 X where
  inner := inner 𝒷
  inner_add_right _ _ _ := CStarModule.inner_add_right
  inner_op_smul_right _ _ _ := CStarModule.inner_op_smul_right
  inner_smul_right_complex _ _ _ := CStarModule.inner_smul_right_complex
  star_inner _ _ := CStarModule.star_inner _ _
  inner_self_nonneg _ := CStarModule.inner_self_nonneg

/-! ### Elementary properties of the module action

`CStarModule 𝒷 X` assumes only `SMul 𝒷 X`; the module laws for that action
are consequences of the axioms, by definiteness of the inner product (the
same derivation as `Theses.A.CStar.moduleAdjointable_linear`).  Together
with `norm_op_smul_le` these are what is needed to define the operator
`|x⟩⟨y|` of **159II** as a `LinearMap.mkContinuous`, and to compute with
the module action of `𝒜 ⊗_φ ℬ` in `Paschke.lean`. -/

section ModuleAction

variable {𝒷 : Type u} {X : Type w}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]

theorem op_add_smul (a b : 𝒷) (x : X) : (a + b) • x = a • x + b • x :=
  eq_of_inner_right_eq (𝒜 := 𝒷) fun z => by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_add_right,
      CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_right, add_mul]

theorem op_mul_smul (a b : 𝒷) (x : X) : (a * b) • x = a • (b • x) :=
  eq_of_inner_right_eq (𝒜 := 𝒷) fun z => by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_right,
      CStarModule.inner_op_smul_right, mul_assoc]

theorem op_one_smul (x : X) : (1 : 𝒷) • x = x :=
  eq_of_inner_right_eq (𝒜 := 𝒷) fun z => by
    rw [CStarModule.inner_op_smul_right, one_mul]

theorem op_smul_complex_smul (c : ℂ) (a : 𝒷) (x : X) :
    (c • a) • x = c • (a • x) :=
  eq_of_inner_right_eq (𝒜 := 𝒷) fun z => by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_smul_right_complex,
      CStarModule.inner_op_smul_right, smul_mul_assoc]

theorem op_smul_comm_complex (c : ℂ) (a : 𝒷) (x : X) :
    a • (c • x) = c • (a • x) :=
  eq_of_inner_right_eq (𝒜 := 𝒷) fun z => by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_smul_right_complex,
      CStarModule.inner_smul_right_complex, CStarModule.inner_op_smul_right,
      mul_smul_comm]

theorem op_smul_add (a : 𝒷) (x y : X) : a • (x + y) = a • x + a • y :=
  eq_of_inner_right_eq (𝒜 := 𝒷) fun z => by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_add_right,
      CStarModule.inner_add_right, CStarModule.inner_op_smul_right,
      CStarModule.inner_op_smul_right, mul_add]

theorem op_zero_smul (x : X) : (0 : 𝒷) • x = 0 :=
  eq_of_inner_right_eq (𝒜 := 𝒷) fun z => by
    rw [CStarModule.inner_op_smul_right, zero_mul, CStarModule.inner_zero_right]

theorem op_smul_zero (a : 𝒷) : a • (0 : X) = 0 :=
  eq_of_inner_right_eq (𝒜 := 𝒷) fun z => by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_zero_right, mul_zero]

theorem norm_op_smul_le (a : 𝒷) (x : X) : ‖a • x‖ ≤ ‖a‖ * ‖x‖ := by
  have hinner : (inner 𝒷 (a • x) (a • x) : 𝒷) = a * inner 𝒷 x x * star a := by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_left,
      mul_assoc]
  have hsq : ‖a • x‖ ^ 2 ≤ (‖a‖ * ‖x‖) ^ 2 := by
    rw [CStarModule.norm_sq_eq (A := 𝒷), hinner]
    calc ‖a * inner 𝒷 x x * star a‖ ≤ ‖a‖ * ‖(inner 𝒷 x x : 𝒷)‖ * ‖star a‖ :=
          (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = (‖a‖ * ‖x‖) ^ 2 := by
          rw [norm_star, ← CStarModule.norm_sq_eq (A := 𝒷)]; ring
  have h1 : (0 : ℝ) ≤ ‖a • x‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖a‖ * ‖x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

end ModuleAction

section SelfDualDef

variable (𝒷 : Type u) (X : Type v)
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]

/-- **141IIa** (`moved-dfn-selfdual`, dils.tex:1339): a pre-Hilbert
𝒷-module `X` is **self dual** if every bounded 𝒷-linear map `τ : X → 𝒷`
is of the form `τ = ⟨t, ·⟩` for some `t ∈ X`.

**141IIb** (Beware) and **141III** (Examples: Hilbert spaces, `𝒷` over
itself, closed right ideals, `e𝒷`, direct sums) — not converted. -/
def SelfDual : Prop :=
  ∀ τ : X →ₗ[ℂ] 𝒷, (∀ (b : 𝒷) (x : X), τ (b • x) = b * τ x) →
    (∃ C : ℝ, ∀ x, ‖τ x‖ ≤ C * ‖x‖) →
    ∃ t : X, ∀ x, τ x = inner 𝒷 t x

end SelfDualDef

/-- **141III** (dils.tex:1357, Examples): a C*-algebra `𝒷` is self dual as
a Hilbert `𝒷`-module over itself, because a `𝒷`-linear `τ : 𝒷 → 𝒷` is
`τ x = x · τ 1 = ⟨(τ 1)*, x⟩` (boundedness is not needed).  Used in
`Paschke.lean` to run the universal property of `𝒜 ⊗_φ ℬ` against `ℬ`
itself. -/
theorem selfDual_self (𝒷 : Type u) [CStarAlgebra 𝒷] [PartialOrder 𝒷]
    [StarOrderedRing 𝒷] : SelfDual 𝒷 𝒷 := by
  intro τ hmod _
  refine ⟨star (τ 1), fun x => ?_⟩
  have h := hmod x 1
  rw [smul_eq_mul, mul_one] at h
  show τ x = x * star (star (τ 1))
  rw [star_star, h]

/-! ## Parsec 1420: Cauchy–Schwarz and sesquilinear forms

**142I** (dils.tex:1396): introduction — nothing to formalize. -/

section CauchySchwarz

variable {𝒷 : Type u} {X : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [AddCommGroup X] [Module ℂ X] [SMul 𝒷 X]

/-! ### Elementary consequences of the `BInner` axioms

`BInner` bundles only right-additivity, right-𝒷-linearity, right-ℂ-linearity,
conjugate symmetry and positivity; the corresponding left-hand rules follow
by conjugate symmetry, exactly as in Mathlib's `CStarModule`. -/

namespace BInner

variable (B : BInner 𝒷 X)

theorem inner_add_left (x y z : X) :
    B.inner (x + y) z = B.inner x z + B.inner y z := by
  rw [← B.star_inner z (x + y), B.inner_add_right, star_add, B.star_inner,
    B.star_inner]

theorem inner_op_smul_left (b : 𝒷) (x y : X) :
    B.inner (b • x) y = B.inner x y * star b := by
  rw [← B.star_inner y (b • x), B.inner_op_smul_right, star_mul, B.star_inner]

theorem inner_smul_left_complex (c : ℂ) (x y : X) :
    B.inner (c • x) y = (starRingEnd ℂ) c • B.inner x y := by
  rw [← B.star_inner y (c • x), B.inner_smul_right_complex, star_smul,
    B.star_inner]
  rfl

theorem inner_zero_right (x : X) : B.inner x 0 = 0 := by
  have := B.inner_add_right x 0 0
  simpa using this.symm

theorem inner_zero_left (x : X) : B.inner 0 x = 0 := by
  rw [← B.star_inner x 0, B.inner_zero_right, star_zero]

theorem inner_sub_right (x y z : X) :
    B.inner x (y - z) = B.inner x y - B.inner x z := by
  rw [sub_eq_add_neg, B.inner_add_right, ← neg_one_smul ℂ z,
    B.inner_smul_right_complex]
  simp [sub_eq_add_neg]

theorem inner_sub_left (x y z : X) :
    B.inner (x - y) z = B.inner x z - B.inner y z := by
  rw [← B.star_inner z (x - y), B.inner_sub_right, star_sub, B.star_inner,
    B.star_inner]

theorem inner_op_smul_self (b : 𝒷) (x : X) :
    B.inner (b • x) (b • x) = b * B.inner x x * star b := by
  rw [B.inner_op_smul_right, B.inner_op_smul_left, mul_assoc]

end BInner


/-- **142II** (`module-innerprod-state`, dils.tex:1407, Definition): for a
𝒷-valued inner product and a positive functional `f : 𝒷 → ℂ`, the
complex-valued form `⟨x,y⟩_f = f([x,y])`. -/
noncomputable def innerF (f : 𝒷 →ₗ[ℂ] ℂ) (B : BInner 𝒷 X) (x y : X) : ℂ :=
  f (B.inner x y)

/-- **142II** (`module-innerprod-state`, dils.tex:1407, Definition): the
seminorm `‖x‖_f = ⟨x,x⟩_f^½`. -/
noncomputable def seminormF (f : 𝒷 →ₗ[ℂ] ℂ) (B : BInner 𝒷 X) (x : X) : ℝ :=
  Real.sqrt (f (B.inner x x)).re

/-- **142II** (`module-innerprod-state`, dils.tex:1407, Definition), two of
the four identities that make `⟨·,·⟩_f` an inner product: conjugate symmetry
and positivity.  This is **weaker than the point**, whose stated conclusion
is that `‖·‖_f` is a seminorm; that is `seminormF_seminorm` below, and the
"is a complex-valued inner product" claim in full is `innerFCore`.  Kept
because these are the two identities the ultranorm estimates use directly. -/
theorem innerF_inner_product (f : 𝒷 →ₗ[ℂ] ℂ) (hf : IsPositiveMap f)
    (B : BInner 𝒷 X) :
    (∀ x y : X, innerF f B y x = starRingEnd ℂ (innerF f B x y)) ∧
      ∀ x : X, 0 ≤ (innerF f B x x).re ∧ (innerF f B x x).im = 0 := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · -- conjugate symmetry: a positive map is involution preserving (10IV)
    show f (B.inner y x) = starRingEnd ℂ (f (B.inner x y))
    rw [← B.star_inner x y]
    exact cstar_p_implies_i f hf (B.inner x y)
  · have h : (0 : ℂ) ≤ f (B.inner x x) := hf _ (B.inner_self_nonneg x)
    rw [Complex.le_def] at h
    refine ⟨?_, ?_⟩
    · show (0 : ℝ) ≤ (f (B.inner x x)).re
      simpa using h.1
    · show (f (B.inner x x)).im = 0
      simpa using h.2.symm

/-- **142II** (`module-innerprod-state`, dils.tex:1407, Definition), the
embedded claim in full: *"this `⟨·,·⟩_f` is a complex-valued inner
product"*.  Bundled as Mathlib's `PreInnerProductSpace.Core ℂ X`, which is
exactly the possibly-indefinite complex inner product of cstar.tex **4XV**
(`inner-product-basic`): conjugate symmetric, positive, additive and
conjugate-homogeneous in the first argument — hence, by conjugate symmetry,
additive and ℂ-linear in the second, the two clauses the audit found
unstated. -/
@[instance_reducible]
noncomputable def innerFCore (f : 𝒷 →ₗ[ℂ] ℂ) (hf : IsPositiveMap f)
    (B : BInner 𝒷 X) : PreInnerProductSpace.Core ℂ X where
  inner x y := innerF f B x y
  conj_inner_symm x y := by
    show starRingEnd ℂ (innerF f B y x) = innerF f B x y
    rw [(innerF_inner_product f hf B).1 x y]
    simp
  re_inner_nonneg x := by
    have h := ((innerF_inner_product f hf B).2 x).1
    simpa using h
  add_left x y z := by
    show f (B.inner (x + y) z) = f (B.inner x z) + f (B.inner y z)
    rw [B.inner_add_left, map_add]
  smul_left x y r := by
    show f (B.inner (r • x) y) = starRingEnd ℂ r * f (B.inner x y)
    rw [B.inner_smul_left_complex, map_smul, smul_eq_mul]

/-- **142II** (`module-innerprod-state`, dils.tex:1407, Definition), the
point's **conclusion**: *"Hence, by `inner-product-basic`, we know that
`‖·‖_f` is a seminorm"* — nonnegative, absolutely homogeneous and
subadditive.  The proof is the point's own: `⟨·,·⟩_f` is a complex-valued
inner product (`innerFCore`), so cstar.tex **4XV**
`inner_product_seminorm` applies verbatim.

**142IIa** (dils.tex:1419): discussion — nothing to formalize. -/
theorem seminormF_seminorm (f : 𝒷 →ₗ[ℂ] ℂ) (hf : IsPositiveMap f)
    (B : BInner 𝒷 X) (x y : X) (c : ℂ) :
    0 ≤ seminormF f B x ∧
      seminormF f B (c • x) = ‖c‖ * seminormF f B x ∧
      seminormF f B (x + y) ≤ seminormF f B x + seminormF f B y := by
  letI : PreInnerProductSpace.Core ℂ X := innerFCore f hf B
  have h := Theses.A.CStar.inner_product_seminorm (V := X) x y c
  have hs : ∀ z : X, Theses.A.CStar.innerNorm (V := X) z = seminormF f B z :=
    fun _ => rfl
  rw [hs, hs, hs] at h
  exact h

/-- **142III** (`module-CS`, dils.tex:1427, Proposition (Cauchy–Schwarz)):
for a (possibly indefinite) 𝒷-valued inner product,
`⟨x,y⟩⟨y,x⟩ ≤ ‖⟨y,y⟩‖ ⟨x,x⟩`.

**Convention.** The thesis uses *right* 𝒷-modules with `⟨x, y·b⟩ = ⟨x,y⟩ b`,
whereas `BInner` follows Mathlib's `CStarModule` convention `[x, b•y] =
b [x,y]`, so that `[u,v] = ⟨v,u⟩_thesis` (see the file header).  The Lean
statement below is therefore the thesis's inequality with the two factors of
the left-hand side interchanged, exactly as in `Theses.A.CStar.chilb_cs`.
Stated without the swap it is *false*: for `𝒷 = M₂(ℂ)`, `X = 𝒷` with
`[a,b] = b a*`, `x = e₁₁`, `y = e₂₁` it would assert `e₂₂ ≤ e₁₁`.

**142IV** is the proof, and it is the proof below: the states are order
separating (**22VIII**, `states_order_separating_2`), so it suffices to test
the inequality at a single state `f`, where Cauchy–Schwarz for the
complex-valued inner product `⟨·,·⟩_f` of **142II** (`innerFCore`, cstar.tex
**4XV**.1) applies to the pair `x`, `y·⟨y,x⟩` — mirrored, `x` and
`[y,x] • y`. -/
theorem module_CS (B : BInner 𝒷 X) (x y : X) :
    B.inner y x * B.inner x y ≤ ‖B.inner y y‖ • B.inner x x := by
  set b : 𝒷 := B.inner y x with hb
  have hbs : star b = B.inner x y := B.star_inner y x
  have hsa : IsSelfAdjoint (B.inner y y) := B.star_inner y y
  set K : ℝ := ‖B.inner y y‖ with hK
  have hK0 : (0 : ℝ) ≤ K := norm_nonneg _
  -- `⟨y,y⟩ ≤ ‖⟨y,y⟩‖`, conjugated: `⟨x,y⟩⟨y,y⟩⟨y,x⟩ ≤ ‖⟨y,y⟩‖ ⟨x,y⟩⟨y,x⟩`
  have hconj : b * B.inner y y * star b ≤ K • (b * star b) :=
    CStarAlgebra.star_right_conjugate_le_norm_smul hsa
  rw [← hbs, ← sub_nonneg]
  -- "Let `f : 𝒷 → ℂ` be any state.  Since the states on `𝒷` are order
  -- separating, it suffices to show `f(⟨x,y⟩⟨y,x⟩) ≤ ‖⟨y,y⟩‖ f(⟨x,x⟩)`."
  refine (states_order_separating_2 (𝒜 := 𝒷) _).mpr ?_
  rintro ⟨f, hfs⟩
  have hf : IsPositiveMap f := hfs.1
  have hmono : ∀ a c : 𝒷, a ≤ c → (f a).re ≤ (f c).re := by
    intro a c hac
    have h := hf (c - a) (sub_nonneg.mpr hac)
    rw [map_sub] at h
    have h2 := (Complex.le_def.mp h).1
    simp only [Complex.sub_re, Complex.zero_re] at h2
    linarith
  -- "Using Cauchy–Schwarz for `⟨·,·⟩_f`":
  -- `f(⟨x,y⟩⟨y,x⟩)² = ⟨x, y⟨y,x⟩⟩_f² ≤ ‖x‖_f² ‖y⟨y,x⟩‖_f²`
  let _core : PreInnerProductSpace.Core ℂ X := innerFCore f hf B
  have hcs : ‖f (B.inner (b • y) x)‖ ^ 2
      ≤ (f (B.inner (b • y) (b • y))).re * (f (B.inner x x)).re :=
    Theses.A.CStar.inner_product_basic_1 (V := X) (b • y) x
  have e1 : B.inner (b • y) x = b * star b := by
    rw [B.inner_op_smul_left, ← hb]
  have e2 : B.inner (b • y) (b • y) = b * B.inner y y * star b :=
    B.inner_op_smul_self b y
  rw [e1, e2] at hcs
  have hreal : ∀ a : 𝒷, 0 ≤ a → f a = ((f a).re : ℂ) := by
    intro a ha
    have h := hf a ha
    rw [Complex.le_def] at h
    exact Complex.ext rfl (by simp [← h.2])
  have hbb : (0 : 𝒷) ≤ b * star b := by
    have h := star_mul_self_nonneg (star b)
    rwa [star_star] at h
  have hxx : (0 : 𝒷) ≤ B.inner x x := B.inner_self_nonneg x
  set T : ℝ := (f (b * star b)).re with hT
  set S : ℝ := (f (B.inner x x)).re with hS
  have hT0 : 0 ≤ T := Complex.zero_re ▸ (Complex.le_def.mp (hf _ hbb)).1
  have hS0 : 0 ≤ S := Complex.zero_re ▸ (Complex.le_def.mp (hf _ hxx)).1
  have hnorm : ‖f (b * star b)‖ = T := by
    rw [hreal _ hbb, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0]
  -- "`= ‖x‖_f² f(⟨x,y⟩⟨y,y⟩⟨y,x⟩) ≤ ‖x‖_f² ‖⟨y,y⟩‖ f(⟨x,y⟩⟨y,x⟩)`"
  have hU : (f (b * B.inner y y * star b)).re ≤ K * T := by
    have h := hmono _ _ hconj
    rw [show (K • (b * star b)) = ((K : ℝ) : ℂ) • (b * star b) from
      (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _), map_smul] at h
    simpa using h
  rw [hnorm] at hcs
  -- "which yields the inequality by dividing by `f(⟨x,y⟩⟨y,x⟩)`"
  have hkey : T ≤ K * S := by
    rcases eq_or_lt_of_le hT0 with h0 | h0
    · nlinarith
    · nlinarith
  rw [map_sub, sub_nonneg,
    show (K • B.inner x x) = ((K : ℝ) : ℂ) • B.inner x x from
      (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _), map_smul, smul_eq_mul,
    hreal _ hbb, hreal _ hxx, ← Complex.ofReal_mul]
  exact (RCLike.ofReal_le_ofReal (K := ℂ)).mpr hkey

/-- **142V** (`module-seminorm`, dils.tex:1456, Exercise), part 1:
`‖[x,y]‖ ≤ ‖x‖‖y‖` for the seminorm `‖x‖ = ‖[x,x]‖^½`. -/
theorem module_seminorm_1 (B : BInner 𝒷 X) (x y : X) :
    ‖B.inner x y‖ ≤ B.norm x * B.norm y := by
  -- `‖[x,y]‖² = ‖[y,x][x,y]‖ ≤ ‖ ‖[y,y]‖ [x,x] ‖ = ‖x‖²‖y‖²`
  have hyx : B.inner y x = star (B.inner x y) := (B.star_inner x y).symm
  have h1 : ‖B.inner y x * B.inner x y‖ ≤ ‖B.inner y y‖ * ‖B.inner x x‖ := by
    have h0 : (0 : 𝒷) ≤ B.inner y x * B.inner x y := by
      rw [hyx]; exact star_mul_self_nonneg _
    have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le h0
      (module_CS B x y)
    rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
  have h2 : ‖B.inner x y‖ ^ 2 = ‖B.inner y x * B.inner x y‖ := by
    rw [hyx, CStarRing.norm_star_mul_self]; ring
  have h3 : ‖B.inner x y‖ ^ 2 ≤ (B.norm x * B.norm y) ^ 2 := by
    rw [h2, mul_pow]
    simp only [BInner.norm, Real.sq_sqrt (norm_nonneg _)]
    rw [mul_comm]
    exact h1
  have hnx : 0 ≤ B.norm x := Real.sqrt_nonneg _
  have hny : 0 ≤ B.norm y := Real.sqrt_nonneg _
  nlinarith [norm_nonneg (B.inner x y), mul_nonneg hnx hny]

/-- **142V** (`module-seminorm`, dils.tex:1456, Exercise), part 2:
`‖x‖ = ‖[x,x]‖^½` is a seminorm with `‖x·b‖ ≤ ‖x‖‖b‖`.

**142VI** (dils.tex:1466): uniform continuity of the operations — the
quantitative statements appear as **148I**–**148V** below. -/
theorem module_seminorm_2 (B : BInner 𝒷 X) (x y : X) (c : ℂ) (b : 𝒷) :
    B.norm (x + y) ≤ B.norm x + B.norm y ∧
      B.norm (c • x) = ‖c‖ * B.norm x ∧
      B.norm (b • x) ≤ B.norm x * ‖b‖ := by
  have hnx : 0 ≤ B.norm x := Real.sqrt_nonneg _
  have hny : 0 ≤ B.norm y := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · -- triangle inequality, via `‖[x,y]‖ ≤ ‖x‖‖y‖`
    have hexp : B.inner (x + y) (x + y) =
        B.inner x x + B.inner x y + B.inner y x + B.inner y y := by
      rw [B.inner_add_right, B.inner_add_left, B.inner_add_left]
      abel
    have hyx : ‖B.inner y x‖ = ‖B.inner x y‖ := by
      rw [← B.star_inner x y, norm_star]
    have hxx : ‖B.inner x x‖ = B.norm x ^ 2 := by
      simp [BInner.norm, Real.sq_sqrt (norm_nonneg _)]
    have hyy : ‖B.inner y y‖ = B.norm y ^ 2 := by
      simp [BInner.norm, Real.sq_sqrt (norm_nonneg _)]
    have hb : ‖B.inner (x + y) (x + y)‖ ≤ (B.norm x + B.norm y) ^ 2 := by
      rw [hexp]
      have h1 : ‖B.inner x x + B.inner x y + B.inner y x + B.inner y y‖ ≤
          ‖B.inner x x‖ + ‖B.inner x y‖ + ‖B.inner y x‖ + ‖B.inner y y‖ :=
        calc ‖B.inner x x + B.inner x y + B.inner y x + B.inner y y‖
            ≤ ‖B.inner x x + B.inner x y + B.inner y x‖ + ‖B.inner y y‖ :=
              norm_add_le _ _
          _ ≤ (‖B.inner x x + B.inner x y‖ + ‖B.inner y x‖) + ‖B.inner y y‖ := by
              gcongr; exact norm_add_le _ _
          _ ≤ ((‖B.inner x x‖ + ‖B.inner x y‖) + ‖B.inner y x‖)
                + ‖B.inner y y‖ := by
              gcongr; exact norm_add_le _ _
      have h2 := module_seminorm_1 B x y
      rw [hyx] at h1
      nlinarith [h1, h2, hxx, hyy]
    have := Real.sqrt_le_sqrt hb
    rwa [Real.sqrt_sq (by positivity)] at this
  · -- `[cx,cx] = |c|² [x,x]`
    have hconj : (starRingEnd ℂ) c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.conj_mul]; norm_cast
    have hexp : B.inner (c • x) (c • x) =
        ((‖c‖ ^ 2 : ℝ) : ℂ) • B.inner x x := by
      rw [B.inner_smul_left_complex, B.inner_smul_right_complex, smul_smul,
        hconj]
    show Real.sqrt ‖B.inner (c • x) (c • x)‖ = ‖c‖ * Real.sqrt ‖B.inner x x‖
    rw [hexp, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖c‖ ^ 2),
      Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg c)]
  · -- `[bx,bx] = b[x,x]b*`, so `‖bx‖² ≤ ‖x‖²‖b‖²`
    have hxx : ‖B.inner x x‖ = B.norm x ^ 2 := by
      simp [BInner.norm, Real.sq_sqrt (norm_nonneg _)]
    have hexp : B.inner (b • x) (b • x) = b * B.inner x x * star b := by
      rw [B.inner_op_smul_left, B.inner_op_smul_right]
    have hb : ‖B.inner (b • x) (b • x)‖ ≤ (B.norm x * ‖b‖) ^ 2 := by
      rw [hexp]
      have h1 : ‖b * B.inner x x * star b‖ ≤ ‖b‖ * ‖B.inner x x‖ * ‖b‖ := by
        refine (norm_mul_le _ _).trans ?_
        rw [norm_star]
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg b)
      have h2 : (B.norm x * ‖b‖) ^ 2 = ‖b‖ * ‖B.inner x x‖ * ‖b‖ := by
        rw [mul_pow, hxx]; ring
      rw [h2]; exact h1
    have := Real.sqrt_le_sqrt hb
    rwa [Real.sqrt_sq (by positivity)] at this

/-- **142VII** (dils.tex:1476, Definition): a **𝒷-sesquilinear form** on a
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

/-! **142VIII** (dils.tex:1495, Example): `⟨·, T·⟩` is a 𝒷-sesquilinear
form for every 𝒷-linear `T` — subsumed by
`hilbmod_sesquilinear_forms` (152V, in `SelfDualCompletion.lean`). -/

/-- **142IX** (`hilbmod-polarization`, dils.tex:1506, Exercise): the
polarization identity `B(x,y) = ¼ ∑_{k=0}^{3} iᵏ B(iᵏx + y, iᵏx + y)` for a
𝒷-sesquilinear form `B`. -/
theorem hilbmod_polarization (B : X → X → 𝒷) (hB : IsBSesquilinear B)
    (x y : X) :
    B x y = (4 : ℂ)⁻¹ •
      ∑ k ∈ Finset.range 4,
        Complex.I ^ k • B (Complex.I ^ k • x + y) (Complex.I ^ k • x + y) := by
  -- expand `B(cx+y, cx+y)`; the author's table of the sixteen resulting terms
  have key : ∀ c : ℂ, B (c • x + y) (c • x + y) =
      (starRingEnd ℂ c * c) • B x x + (starRingEnd ℂ c) • B x y
        + c • B y x + B y y := by
    intro c
    rw [hB.add_left, hB.add_right, hB.add_right, hB.smul_left_complex,
      hB.smul_left_complex, hB.smul_right_complex, hB.smul_right_complex,
      smul_smul]
    abel
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, key,
    pow_zero, pow_one, map_one, one_mul, one_smul, smul_add, smul_smul]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, hI2, neg_one_mul]
  have hc1 : starRingEnd ℂ Complex.I = -Complex.I := Complex.conj_I
  match_scalars <;> simp [hI2, hI3, hc1, Complex.ext_iff] <;> ring

end CauchySchwarz

/-! ## Parsec 1430: adjointable maps and 𝒷ᵃ(X)

**143I** (dils.tex:1517, Definition): adjointable maps between pre-Hilbert
𝒷-modules and the set `𝒷ᵃ(X)` of adjointable bounded operators — already
formalized in `Theses.A.CStar.Matrices` as `ModuleAdjointTo` /
`ModuleAdjointable` (with uniqueness of adjoints, `moduleAdjointTo_unique`).
**143Ia** (dils.tex:1534): discussion — nothing to formalize. -/

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

/-- **143II** (`adjointable-cstar-identity`, dils.tex:1540, Lemma), part 1:
for a linear map `T : X → Y` between pre-Hilbert 𝒷-modules and `B > 0`:
`‖Tx‖ ≤ B‖x‖` for all `x` iff `‖⟨y,Tx⟩‖ ≤ B‖y‖‖x‖` for all `x, y`.
(Same statement as cstar.tex 32X, `chilb_form_bounded`.) -/
theorem adjointable_cstar_identity_1 (T : X →ₗ[ℂ] Y) (B : ℝ) (hB : 0 < B) :
    (∀ x : X, ‖T x‖ ≤ B * ‖x‖) ↔
      ∀ (x : X) (y : Y), ‖inner 𝒷 y (T x)‖ ≤ B * ‖y‖ * ‖x‖ :=
  Theses.A.CStar.chilb_form_bounded T B hB

/-- **143III** (dils.tex:1567), the step *"`‖⟨x,T*y⟩‖ = ‖⟨y,Tx⟩‖ ≤
‖T‖‖y‖‖x‖` for all `x, y`, and so by the previous `‖T*‖ ≤ ‖T‖`"* — "the
previous" being part 1, `adjointable_cstar_identity_1`, applied at the bound
`B = ‖T‖`.  Part 1 asks for a *strictly* positive bound, so the degenerate
case `‖T‖ = 0` — where `T = 0` and hence `⟨Sy,Sy⟩ = ⟨T(Sy),y⟩ = 0`, so
`S = 0` — is taken separately; the thesis passes over it. -/
private theorem norm_adjoint_le (T : X →L[ℂ] Y) (S : Y →L[ℂ] X)
    (h : ModuleAdjointTo 𝒷 ⇑T ⇑S) : ‖S‖ ≤ ‖T‖ := by
  rcases (norm_nonneg T).eq_or_lt with hT | hT
  · -- `‖T‖ = 0`, so `T = 0` and `⟨Sy, Sy⟩ = ⟨T (S y), y⟩ = 0`
    have hT0 : T = 0 := norm_eq_zero.mp hT.symm
    refine (S.opNorm_le_bound le_rfl fun y => ?_).trans_eq hT
    have hy : inner 𝒷 (S y) (S y) = (0 : 𝒷) := by
      rw [← h (S y) y, hT0]
      simp
    have h2 : ‖S y‖ ^ 2 = 0 := by
      rw [CStarModule.norm_sq_eq (A := 𝒷) (x := S y), hy, norm_zero]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    simp [this]
  · -- the printed step, with `B = ‖T‖` in part 1
    refine S.opNorm_le_bound (norm_nonneg T) ?_
    refine (adjointable_cstar_identity_1 (𝒷 := 𝒷) (S : Y →ₗ[ℂ] X) ‖T‖ hT).mpr
      fun y x => ?_
    show ‖inner 𝒷 x (S y)‖ ≤ ‖T‖ * ‖x‖ * ‖y‖
    rw [← h x y]
    calc ‖inner 𝒷 (T x) y‖ ≤ ‖T x‖ * ‖y‖ := CStarModule.norm_inner_le Y
      _ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
          gcongr
          exact T.le_opNorm x

/-- **143II** (`adjointable-cstar-identity`, dils.tex:1540, Lemma), part 2:
for bounded adjointable `T` (with adjoint `S`): `‖T*‖ = ‖T‖` and
`‖T*T‖ = ‖T‖²`.

**143III** is the proof, and is transcribed: `‖T*‖ ≤ ‖T‖` comes from part 1
(`norm_adjoint_le` above), and `T** = T` — adjoints being unique, `T` is an
adjoint of `T*` (`moduleAdjointTo_symm`) — turns that into `‖T‖ = ‖T**‖ ≤
‖T*‖ ≤ ‖T‖`.  The C*-identity is then the point's own two estimates. -/
theorem adjointable_cstar_identity_2 (T : X →L[ℂ] Y) (S : Y →L[ℂ] X)
    (h : ModuleAdjointTo 𝒷 ⇑T ⇑S) :
    ‖S‖ = ‖T‖ ∧ ‖S.comp T‖ = ‖T‖ ^ 2 := by
  have hST : ‖S‖ = ‖T‖ :=
    le_antisymm (norm_adjoint_le T S h)
      (norm_adjoint_le S T (Theses.A.CStar.moduleAdjointTo_symm T S h))
  refine ⟨hST, le_antisymm ?_ ?_⟩
  · calc ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ := S.opNorm_comp_le T
      _ = ‖T‖ ^ 2 := by rw [hST]; ring
  · -- `‖Tx‖² = ‖⟨Tx,Tx⟩‖ = ‖⟨x, S(Tx)⟩‖ ≤ ‖x‖ ‖S T‖ ‖x‖`
    have key : ∀ x : X, ‖T x‖ ≤ Real.sqrt ‖S.comp T‖ * ‖x‖ := by
      intro x
      have h1 : ‖T x‖ ^ 2 ≤ ‖S.comp T‖ * ‖x‖ ^ 2 := by
        rw [CStarModule.norm_sq_eq (A := 𝒷) (x := T x), h x (T x)]
        calc ‖inner 𝒷 x (S (T x))‖ ≤ ‖x‖ * ‖S (T x)‖ :=
              CStarModule.norm_inner_le X
          _ ≤ ‖x‖ * (‖S.comp T‖ * ‖x‖) := by
              gcongr
              exact (S.comp T).le_opNorm x
          _ = ‖S.comp T‖ * ‖x‖ ^ 2 := by ring
      have h2 := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (norm_nonneg _),
        Real.sqrt_sq (norm_nonneg _)] at h2
    have hT : ‖T‖ ≤ Real.sqrt ‖S.comp T‖ :=
      T.opNorm_le_bound (Real.sqrt_nonneg _) key
    calc ‖T‖ ^ 2 ≤ (Real.sqrt ‖S.comp T‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg T) hT 2
      _ = ‖S.comp T‖ := Real.sq_sqrt (norm_nonneg _)

/-- **143IV** (`hilbmod-cstar`, dils.tex:1588, Proposition), *one
ingredient only*, and strictly weaker than the Proposition: for a Hilbert
𝒷-module `X` the adjointable bounded operators are a **closed** subset of
`B(X)`.  As in cstar.tex 32XIII (`bax_cstar`) this is the missing
ingredient beyond the ∗-algebra structure and the C*-identity (**143II**).

**The Proposition itself — that `𝒷ᵃ(X)` is a C*-algebra — is
`Ba.instCStarAlgebra` below**, which assembles the three ingredients; read
this declaration as its closedness lemma, not as 143IV.

**143V** is the proof — not converted. -/
theorem hilbmod_cstar [CompleteSpace X] :
    IsClosed {T : X →L[ℂ] X | ModuleAdjointable 𝒷 ⇑T} :=
  Theses.A.CStar.bax_cstar

end Adjointable

/-! ## The C*-algebra `𝒷ᵃ(X)` as a type

The C*-structure of **143IV** (`hilbmod-cstar`, dils.tex:1588) is assembled
here as **143V** assembles it: the adjointable bounded operators form a
ℂ-subalgebra of `B(X)` with the adjoint as an involutive conjugate-linear
anti-automorphism (cstar.tex 32III, `moduleAdjointTo_symm` /
`moduleAdjointTo_add_smul`); *"by `adjointable-cstar-identity` the C*-identity
holds"* — that is **143II**.2, `adjointable_cstar_identity_2` above; and
*"it only remains to be shown that `𝒷ᵃ(X)` is complete"* — that is
`hilbmod_cstar` above, the closedness ingredient. -/

section BaConstruction

variable {𝒷 : Type u} {X : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]

variable (𝒷 X)

/-- **143IV** (`hilbmod-cstar`, dils.tex:1588, Proposition), the algebraic
half: the adjointable bounded operators form a unital ℂ-subalgebra of
`B(X)` (cstar.tex 32III). -/
def baSubalgebra : Subalgebra ℂ (X →L[ℂ] X) where
  carrier := {T | ModuleAdjointable 𝒷 ⇑T}
  mul_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    refine ⟨fun y => b' (a' y), fun x y => ?_⟩
    show inner 𝒷 (a (b x)) y = inner 𝒷 x (b' (a' y))
    rw [ha (b x) y, hb x (a' y)]
  one_mem' := ⟨id, fun _ _ => rfl⟩
  add_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    exact ⟨fun y => a' y + b' y,
      (Theses.A.CStar.moduleAdjointTo_add_smul (𝒜 := 𝒷) _ _ _ _ 0 ha hb).1⟩
  zero_mem' := ⟨fun _ => 0, by intro x y; simp⟩
  algebraMap_mem' := by
    intro c
    refine ⟨fun y => (starRingEnd ℂ) c • y, fun x y => ?_⟩
    show inner 𝒷 (c • x) y = inner 𝒷 x ((starRingEnd ℂ) c • y)
    simp

variable {𝒷 X}

@[simp] theorem mem_baSubalgebra {T : X →L[ℂ] X} :
    T ∈ baSubalgebra 𝒷 X ↔ ModuleAdjointable 𝒷 ⇑T := Iff.rfl

/-- The adjoint of an adjointable bounded operator, as a bounded operator. -/
private noncomputable def baAdj (T : baSubalgebra 𝒷 X) : X →L[ℂ] X :=
  (Theses.A.CStar.exists_clm_adjointTo (T := (T : X →L[ℂ] X)) T.2.choose_spec).choose

private theorem baAdj_spec (T : baSubalgebra 𝒷 X) :
    ModuleAdjointTo 𝒷 ⇑(T : X →L[ℂ] X) ⇑(baAdj T) :=
  (Theses.A.CStar.exists_clm_adjointTo (T := (T : X →L[ℂ] X)) T.2.choose_spec).choose_spec

/-- The star operation of `𝒷ᵃ(X)`: `T ↦ T*`. -/
private noncomputable def baStar (T : baSubalgebra 𝒷 X) : baSubalgebra 𝒷 X :=
  ⟨baAdj T, ⟨_, Theses.A.CStar.moduleAdjointTo_symm _ _ (baAdj_spec T)⟩⟩

/-- Adjoints are unique, so `baStar` is pinned down by the adjointness
relation. -/
private theorem baStar_eq {T : baSubalgebra 𝒷 X} {S : X →L[ℂ] X}
    (h : ModuleAdjointTo 𝒷 ⇑(T : X →L[ℂ] X) ⇑S) :
    ((baStar T : baSubalgebra 𝒷 X) : X →L[ℂ] X) = S :=
  DFunLike.coe_injective
    (Theses.A.CStar.moduleAdjointTo_unique _ _ _ (baAdj_spec T) h)

noncomputable instance baInstStarRing : StarRing (baSubalgebra 𝒷 X) where
  star := baStar
  star_involutive T := Subtype.ext <| baStar_eq (T := baStar T) (S := T)
    (Theses.A.CStar.moduleAdjointTo_symm _ _ (baAdj_spec T))
  star_mul a b := Subtype.ext <| baStar_eq (T := a * b)
    (S := (baAdj b).comp (baAdj a)) (by
      intro x y
      show inner 𝒷 ((a : X →L[ℂ] X) ((b : X →L[ℂ] X) x)) y
        = inner 𝒷 x (baAdj b (baAdj a y))
      rw [baAdj_spec a _ y, baAdj_spec b x _])
  star_add a b := Subtype.ext <| baStar_eq (T := a + b)
    (S := baAdj a + baAdj b)
    ((Theses.A.CStar.moduleAdjointTo_add_smul (𝒜 := 𝒷) _ _ _ _ 0
      (baAdj_spec a) (baAdj_spec b)).1)

noncomputable instance baInstStarModule : StarModule ℂ (baSubalgebra 𝒷 X) where
  star_smul c T := Subtype.ext <| baStar_eq (T := c • T)
    (S := (starRingEnd ℂ) c • baAdj T)
    ((Theses.A.CStar.moduleAdjointTo_add_smul (𝒜 := 𝒷) ⇑(T : X →L[ℂ] X)
      ⇑(T : X →L[ℂ] X) _ _ c (baAdj_spec T) (baAdj_spec T)).2)

/-- **143V** (dils.tex:1611), *"by `adjointable-cstar-identity` the C*-identity
holds"*: the C*-identity of `𝒷ᵃ(X)` is the second half of **143II**. -/
instance baInstCStarRing : CStarRing (baSubalgebra 𝒷 X) where
  norm_mul_self_le T := by
    have h : ‖(baAdj T).comp (T : X →L[ℂ] X)‖ = ‖(T : X →L[ℂ] X)‖ ^ 2 :=
      (adjointable_cstar_identity_2 (𝒷 := 𝒷) _ _ (baAdj_spec T)).2
    have h' : ‖star T * T‖ = ‖(T : X →L[ℂ] X)‖ ^ 2 := h
    rw [h']
    exact le_of_eq (sq ‖(T : X →L[ℂ] X)‖).symm

/-- **143V** (dils.tex:1611), *"it only remains to be shown that `𝒷ᵃ(X)` is
complete"*: closedness of `𝒷ᵃ(X)` in `B(X)` is `hilbmod_cstar` above. -/
instance baInstCompleteSpace [CompleteSpace X] :
    CompleteSpace (baSubalgebra 𝒷 X) :=
  (hilbmod_cstar (𝒷 := 𝒷) (X := X)).completeSpace_coe

noncomputable instance baInstCStarAlgebra [CompleteSpace X] :
    CStarAlgebra (baSubalgebra 𝒷 X) where

/-- The `star` of the C*-algebra `𝒷ᵃ(X)` *is* the adjoint: `star T` is an
adjoint of `T` in the sense of `ModuleAdjointTo`.  (Public bridge to the
private `baAdj`; needed to reason about `𝒷ᵃ(X)` through its action on
`X`.) -/
theorem baSubalgebra_star_spec (T : baSubalgebra 𝒷 X) :
    ModuleAdjointTo 𝒷 ⇑(T : X →L[ℂ] X)
      ⇑((star T : baSubalgebra 𝒷 X) : X →L[ℂ] X) :=
  baAdj_spec T

/-- Multiplication in `𝒷ᵃ(X)` is composition of operators. -/
theorem baSubalgebra_coe_mul_apply (S T : baSubalgebra 𝒷 X) (x : X) :
    ((S * T : baSubalgebra 𝒷 X) : X →L[ℂ] X) x
      = (S : X →L[ℂ] X) ((T : X →L[ℂ] X) x) := rfl

/-- The vector form of an element of `𝒷ᵃ(X)` of the shape `T* T` is a Gram
form: `⟨x, T*Tx⟩ = ⟨Tx, Tx⟩`.  (The easy half of **144I**.) -/
theorem baSubalgebra_inner_star_mul_self [CompleteSpace X]
    (T : baSubalgebra 𝒷 X) (x : X) :
    inner 𝒷 x (((star T * T : baSubalgebra 𝒷 X) : X →L[ℂ] X) x)
      = inner 𝒷 ((T : X →L[ℂ] X) x) ((T : X →L[ℂ] X) x) := by
  rw [baSubalgebra_coe_mul_apply]
  exact (baSubalgebra_star_spec T _ _).symm

end BaConstruction

section BaDef

variable (𝒷 : Type u) {X : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]

variable (X) in
/-- The set `𝒷ᵃ(X)` of adjointable bounded operators on a (pre-)Hilbert
𝒷-module `X` (**143I**, dils.tex:1517), as a type. -/
def Ba : Type v :=
  {T : X →L[ℂ] X // ModuleAdjointable 𝒷 ⇑T}

/-- The underlying bounded operator of an element of `𝒷ᵃ(X)`. -/
def Ba.toCLM (T : Ba 𝒷 X) : X →L[ℂ] X := T.1

variable [CompleteSpace X]

/-- **143IV** (`hilbmod-cstar`, dils.tex:1588, Proposition), as an
instance: `𝒷ᵃ(X)` is a C*-algebra for a Hilbert 𝒷-module `X`.  The
structure is that of the closed ℂ-subalgebra `baSubalgebra 𝒷 X` of `B(X)`,
to which `Ba 𝒷 X` is definitionally equal; the `NormedSpace ℂ X` needed to
speak of the operator norm is the one determined by the `CStarModule`
axioms (`CStarModule.normedSpaceCore`), which Mathlib deliberately does not
register as an instance. -/
noncomputable instance Ba.instCStarAlgebra : CStarAlgebra (Ba 𝒷 X) := by
  letI : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  exact inferInstanceAs (CStarAlgebra (baSubalgebra 𝒷 X))

/-- The canonical (Loewner) partial order of the C*-algebra `𝒷ᵃ(X)`
(cf. **144I**): the spectral order of its C*-structure. -/
noncomputable instance Ba.instPartialOrder : PartialOrder (Ba 𝒷 X) :=
  CStarAlgebra.spectralOrder (Ba 𝒷 X)

/-- The canonical order of `𝒷ᵃ(X)` makes it a star-ordered ring
(cf. **144I**). -/
noncomputable instance Ba.instStarOrderedRing : StarOrderedRing (Ba 𝒷 X) :=
  CStarAlgebra.spectralOrderedRing (Ba 𝒷 X)

end BaDef

/-! ## Parsec 1440 -/

section OrderSep

variable {𝒷 : Type u} {X Y : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]
  [NormedAddCommGroup Y] [Module ℂ Y] [SMul 𝒷 Y] [CStarModule 𝒷 Y]

set_option maxHeartbeats 1000000 in
/-- **144I** (`hilbmod-ordersep`, dils.tex:1631, Proposition): the vector
states on `𝒷ᵃ(X)` are order separating: for adjointable bounded `T`,
`T ≥ 0` (i.e. `T = S*S`) iff `⟨x, Tx⟩ ≥ 0` for all `x ∈ X`.

**144II** is the proof — not converted. -/
theorem hilbmod_ordersep [CompleteSpace X] (T : X →L[ℂ] X)
    (hT : ModuleAdjointable 𝒷 ⇑T) :
    IsPositiveOp 𝒷 T ↔ ∀ x : X, 0 ≤ inner 𝒷 x (T x) := by
  -- the C*-algebra `𝒷ᵃ(X)` (**143IV**), with its spectral order
  letI : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  constructor
  · -- `T = S*S` gives `⟨x,Tx⟩ = ⟨Sx,Sx⟩ ≥ 0`
    rintro ⟨R, R', hRR', rfl⟩ x
    show (0 : 𝒷) ≤ inner 𝒷 x (R' (R x))
    rw [← hRR' x (R x)]
    exact CStarModule.inner_self_nonneg
  · intro hpos
    letI : PartialOrder (baSubalgebra 𝒷 X) := CStarAlgebra.spectralOrder _
    letI : StarOrderedRing (baSubalgebra 𝒷 X) := CStarAlgebra.spectralOrderedRing _
    set a : baSubalgebra 𝒷 X := ⟨T, hT⟩ with ha
    have hcoe : ((a : baSubalgebra 𝒷 X) : X →L[ℂ] X) = T := rfl
    -- `T` is self-adjoint, by polarization — cstar.tex 32XV.1
    have hsa : IsSelfAdjoint a := by
      have h := (Theses.A.CStar.chilb_vector_states_1 (𝒜 := 𝒷) T
        ((star a : baSubalgebra 𝒷 X) : X →L[ℂ] X)
        (hcoe ▸ baSubalgebra_star_spec a)).mpr
        (fun x _ => IsSelfAdjoint.of_nonneg (hpos x))
      exact Subtype.ext (hcoe.trans h).symm
    -- `T = T₊ - T₋` with `T₊T₋ = 0`, and `r := √T₋`
    have hn0 : (0 : baSubalgebra 𝒷 X) ≤ a⁻ := CFC.negPart_nonneg a
    have hdec : a⁺ - a⁻ = a := CFC.posPart_sub_negPart a hsa
    have hr0 : (0 : baSubalgebra 𝒷 X) ≤ CFC.sqrt a⁻ := CFC.sqrt_nonneg _
    have hrr : CFC.sqrt a⁻ * CFC.sqrt a⁻ = a⁻ := CFC.sqrt_mul_sqrt_self _ hn0
    set r : baSubalgebra 𝒷 X := CFC.sqrt a⁻ with hrdef
    have hrsa : star r = r := IsSelfAdjoint.of_nonneg hr0
    have hnsa : star a⁻ = a⁻ := IsSelfAdjoint.of_nonneg hn0
    set q : baSubalgebra 𝒷 X := r * r * r with hqdef
    have hqstar : star q * q = a⁻ * a⁻ * a⁻ := by
      rw [hqdef]
      simp only [star_mul, hrsa]
      rw [← hrr]; noncomm_ring
    have hadj := baSubalgebra_star_spec (a⁻ : baSubalgebra 𝒷 X)
    rw [hnsa] at hadj
    have hprod : a⁻ * a * a⁻ = -(a⁻ * a⁻ * a⁻) := by
      have h : a⁻ * (a⁺ - a⁻) * a⁻ = -(a⁻ * a⁻ * a⁻) := by
        rw [mul_sub, CFC.negPart_mul_posPart, zero_sub, neg_mul]
      rwa [hdec] at h
    -- `0 ≤ ⟨T₋x, T T₋x⟩` reads `⟨x, T₋³x⟩ ≤ 0`
    have hle : ∀ x : X, inner 𝒷 x (((a⁻ * a⁻ * a⁻ : baSubalgebra 𝒷 X) :
        X →L[ℂ] X) x) ≤ 0 := by
      intro x
      have h1 := hpos (((a⁻ : baSubalgebra 𝒷 X) : X →L[ℂ] X) x)
      rw [← hcoe, hadj, ← baSubalgebra_coe_mul_apply, ← baSubalgebra_coe_mul_apply,
        hprod] at h1
      have h2 : (((-(a⁻ * a⁻ * a⁻) : baSubalgebra 𝒷 X) : X →L[ℂ] X)) x
          = -((((a⁻ * a⁻ * a⁻ : baSubalgebra 𝒷 X) : X →L[ℂ] X)) x) := rfl
      rw [h2, CStarModule.inner_neg_right] at h1
      exact neg_nonneg.mp h1
    -- but `T₋³ = q*q` with `q = r³`, so `⟨qx,qx⟩ = 0` and `q = 0`
    have hq0 : q = 0 := by
      refine Subtype.ext (ContinuousLinearMap.ext fun x => ?_)
      refine (CStarModule.inner_self (A := 𝒷)).mp
        (le_antisymm ?_ CStarModule.inner_self_nonneg)
      have hA := baSubalgebra_inner_star_mul_self q x
      rw [hqstar] at hA
      rw [← hA]
      exact hle x
    have hnn : (a⁻ : baSubalgebra 𝒷 X) * a⁻ = 0 := by
      have hrq : (a⁻ : baSubalgebra 𝒷 X) * a⁻ = r * q := by
        rw [hqdef, ← hrr]; noncomm_ring
      rw [hrq, hq0, mul_zero]
    have hnzero : (a⁻ : baSubalgebra 𝒷 X) = 0 := by
      have hnorm : ‖(a⁻ : baSubalgebra 𝒷 X)‖ * ‖(a⁻ : baSubalgebra 𝒷 X)‖ = 0 := by
        rw [← CStarRing.norm_star_mul_self, hnsa, hnn, norm_zero]
      exact norm_eq_zero.mp (mul_self_eq_zero.mp hnorm)
    -- hence `T = T₊ ≥ 0`, and `√T` exhibits `T` as `R*R`
    have haeq : (a⁺ : baSubalgebra 𝒷 X) = a := by
      rw [hnzero, sub_zero] at hdec; exact hdec
    have hapos : (0 : baSubalgebra 𝒷 X) ≤ a := haeq ▸ CFC.posPart_nonneg a
    have hs0 : (0 : baSubalgebra 𝒷 X) ≤ CFC.sqrt a := CFC.sqrt_nonneg _
    have hss : CFC.sqrt a * CFC.sqrt a = a := CFC.sqrt_mul_sqrt_self _ hapos
    set s : baSubalgebra 𝒷 X := CFC.sqrt a with hsdef
    have hssa : star s = s := IsSelfAdjoint.of_nonneg hs0
    refine ⟨((s : baSubalgebra 𝒷 X) : X →L[ℂ] X),
      (((star s : baSubalgebra 𝒷 X)) : X →L[ℂ] X), baSubalgebra_star_spec s, ?_⟩
    refine ContinuousLinearMap.ext fun x => ?_
    rw [ContinuousLinearMap.comp_apply, ← baSubalgebra_coe_mul_apply, hssa, hss,
      hcoe]

/-- **144III** (dils.tex:1661, Lemma): an adjointable map between
pre-Hilbert 𝒷-modules is 𝒷-linear (and ℂ-linear).  The same statement is
cstar.tex **32I**'s embedded claim, `moduleAdjointable_linear`; the proof
below is **144IV**'s own computation, *in situ*.

**144IV**: *"We have `⟨y,(Tx)b⟩ = ⟨T*y,x⟩b = ⟨y,T(xb)⟩` for any `x`, `y`,
`b`.  In particular we get `⟨(Tx)b − T(xb), (Tx)b − T(xb)⟩ = 0` taking
`y = (Tx)b − T(xb)`, and so `T(x)b = T(xb)`."*  Mirrored (`[u,v] =
⟨v,u⟩_thesis`, so the adjoint identity reads `[Tx,y] = [x,T*y]`), and run
three times — for the sum, the scalar and the 𝒷-action — since the Lean
statement asks for additivity and ℂ-linearity as well; `T` is a bare
function here, not assumed linear. -/
theorem hilbmod_adjointable_blinear (T : X → Y)
    (hT : ModuleAdjointable 𝒷 T) :
    (∀ x x' : X, T (x + x') = T x + T x') ∧
      (∀ (c : ℂ) (x : X), T (c • x) = c • T x) ∧
      ∀ (b : 𝒷) (x : X), T (b • x) = b • T x := by
  obtain ⟨S, hS⟩ := hT
  have hS' : ∀ (x : X) (y : Y), (inner 𝒷 (T x) y : 𝒷) = inner 𝒷 x (S y) := hS
  -- "taking `y = (Tx)b − T(xb)`": a vector with zero inner product against
  -- every `y` has zero inner product with itself, hence is zero
  have key : ∀ d : Y, (∀ y : Y, (inner 𝒷 d y : 𝒷) = 0) → d = 0 := by
    intro d hd
    refine eq_of_inner_right_eq (𝒜 := 𝒷) fun y => ?_
    rw [← CStarModule.star_inner (A := 𝒷) d y, hd, star_zero,
      CStarModule.inner_zero_right]
  refine ⟨fun x x' => ?_, fun c x => ?_, fun b x => ?_⟩
  · refine sub_eq_zero.mp (key _ fun y => ?_)
    rw [CStarModule.inner_sub_left, hS', CStarModule.inner_add_left,
      CStarModule.inner_add_left, hS', hS', sub_self]
  · refine sub_eq_zero.mp (key _ fun y => ?_)
    rw [CStarModule.inner_sub_left, hS', CStarModule.inner_smul_left_complex,
      CStarModule.inner_smul_left_complex, hS', sub_self]
  · -- `[T(b·x), y] = [b·x, S y] = [x, S y] b* = [Tx, y] b* = [b·Tx, y]`
    refine sub_eq_zero.mp (key _ fun y => ?_)
    rw [CStarModule.inner_sub_left, hS', CStarModule.inner_op_smul_left,
      CStarModule.inner_op_smul_left, hS', sub_self]

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

/-- **144V** (`blinear-inprod-inequality`, dils.tex:1678, Proposition): a
𝒷-linear map `T : X → Y` between 𝒷-modules with 𝒷-valued inner products
which is bounded by `C ≥ 0` satisfies `[Tx, Tx] ≤ C² [x, x]`.

**144VI** is the proof — not converted. -/
theorem blinear_inprod_inequality (B₁ : BInner 𝒷 X) (B₂ : BInner 𝒷 Y)
    (C : ℝ) (hC : 0 ≤ C) (T : X → Y) (hT : IsBoundedModuleMap B₁ B₂ C T)
    (x : X) :
    B₂.inner (T x) (T x) ≤ (C ^ 2) • B₁.inner x x := by
  have ha : (0 : 𝒷) ≤ B₁.inner x x := B₁.inner_self_nonneg x
  have key : ∀ ε : ℝ, 0 < ε →
      B₂.inner (T x) (T x) ≤ (C ^ 2) • B₁.inner x x + (C ^ 2 * ε) • (1 : 𝒷) := by
    intro ε hε
    set s : 𝒷 := B₁.inner x x + ε • (1 : 𝒷) with hs
    have hsp : IsStrictlyPositive s :=
      IsStrictlyPositive.nonneg_add ha (IsStrictlyPositive.smul hε isStrictlyPositive_one)
    set h : 𝒷 := s ^ (-(1 / 2) : ℝ) with hh
    set k : 𝒷 := s ^ ((1 / 2) : ℝ) with hk
    have hhnn : (0 : 𝒷) ≤ h := CFC.rpow_nonneg
    have hknn : (0 : 𝒷) ≤ k := CFC.rpow_nonneg
    have hhsa : IsSelfAdjoint h := IsSelfAdjoint.of_nonneg hhnn
    have hksa : IsSelfAdjoint k := IsSelfAdjoint.of_nonneg hknn
    have hstar : star h = h := hhsa
    have hconj : h * s * h = 1 := CFC.conjugate_rpow_neg_one_half s hsp
    have hkh : k * h = 1 := by
      rw [hk, hh, ← CFC.rpow_add hsp.isUnit]
      norm_num
      exact CFC.rpow_zero s
    have hhk : h * k = 1 := by
      rw [hk, hh, ← CFC.rpow_add hsp.isUnit]
      norm_num
      exact CFC.rpow_zero s
    have hkk : k * k = s := by
      rw [hk, ← CFC.rpow_add hsp.isUnit]
      norm_num
      exact CFC.rpow_one s
    -- `‖h•x‖ ≤ 1`
    have h1 : B₁.inner (h • x) (h • x) ≤ 1 := by
      rw [B₁.inner_op_smul_self, hstar]
      calc h * B₁.inner x x * h ≤ h * s * h :=
            hhsa.conjugate_le_conjugate
              (by rw [hs]; exact le_add_of_nonneg_right (smul_nonneg hε.le zero_le_one))
        _ = 1 := hconj
    have h1nn : (0 : 𝒷) ≤ B₁.inner (h • x) (h • x) := B₁.inner_self_nonneg _
    have hnorm1 : B₁.norm (h • x) ≤ 1 := by
      have hn : ‖B₁.inner (h • x) (h • x)‖ ≤ 1 :=
        (CStarAlgebra.norm_le_one_iff_of_nonneg _ h1nn).mpr h1
      rw [BInner.norm]
      calc Real.sqrt ‖B₁.inner (h • x) (h • x)‖ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hn
        _ = 1 := Real.sqrt_one
    -- the bound on `T (h•x) = h • T x`
    have hTh : T (h • x) = h • T x := hT.smul h x
    have hz : B₂.inner (h • T x) (h • T x) = h * B₂.inner (T x) (T x) * h := by
      rw [B₂.inner_op_smul_self, hstar]
    have h2 : B₂.norm (h • T x) ≤ C := by
      have hb := hT.bound (h • x)
      rw [hTh] at hb
      calc B₂.norm (h • T x) ≤ C * B₁.norm (h • x) := hb
        _ ≤ C * 1 := by gcongr
        _ = C := mul_one C
    have h3 : ‖h * B₂.inner (T x) (T x) * h‖ ≤ C ^ 2 := by
      rw [BInner.norm, hz] at h2
      nlinarith [Real.sq_sqrt (norm_nonneg (h * B₂.inner (T x) (T x) * h)),
        Real.sqrt_nonneg ‖h * B₂.inner (T x) (T x) * h‖]
    -- `h c h ≤ C² · 1`
    have hznn : (0 : 𝒷) ≤ h * B₂.inner (T x) (T x) * h := by
      rw [← hz]; exact B₂.inner_self_nonneg _
    have h4 : h * B₂.inner (T x) (T x) * h ≤ (C ^ 2) • (1 : 𝒷) := by
      refine le_trans (hznn.isSelfAdjoint.le_algebraMap_norm_self) ?_
      rw [Algebra.algebraMap_eq_smul_one]
      have : (0 : 𝒷) ≤ (C ^ 2 - ‖h * B₂.inner (T x) (T x) * h‖) • (1 : 𝒷) :=
        smul_nonneg (by linarith) zero_le_one
      rw [sub_smul] at this
      exact sub_nonneg.mp this
    -- conjugate back by `k`
    have h5 := hksa.conjugate_le_conjugate h4
    have hlhs : k * (h * B₂.inner (T x) (T x) * h) * k = B₂.inner (T x) (T x) := by
      calc k * (h * B₂.inner (T x) (T x) * h) * k
          = (k * h) * B₂.inner (T x) (T x) * (h * k) := by simp only [mul_assoc]
        _ = B₂.inner (T x) (T x) := by rw [hkh, hhk, one_mul, mul_one]
    have hrhs : k * ((C ^ 2) • (1 : 𝒷)) * k = (C ^ 2) • B₁.inner x x + (C ^ 2 * ε) • (1 : 𝒷) := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, hkk, hs, smul_add, smul_smul]
    rw [hlhs, hrhs] at h5
    exact h5
  -- let `ε → 0`
  have hlim : Tendsto (fun ε : ℝ => (C ^ 2) • B₁.inner x x + (C ^ 2 * ε) • (1 : 𝒷))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 ((C ^ 2) • B₁.inner x x)) := by
    have hcont : Continuous
        (fun ε : ℝ => (C ^ 2) • B₁.inner x x + (C ^ 2 * ε) • (1 : 𝒷)) := by fun_prop
    have h0 := hcont.tendsto 0
    simp only [mul_zero, zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε using key ε hε


end BLinearBound

/-! ## Parsec 1450 -/

section VectStatesCP

variable {𝒷 : Type u} {X : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]

/-- **145I** (`hilbmod-vectstates-cp`, dils.tex:1714, Proposition): for a
von Neumann algebra `𝒷`, a Hilbert 𝒷-module `X` and `x ∈ X`, the vector
state `h(T) = ⟨x, Tx⟩` on `𝒷ᵃ(X)` is completely positive: for adjointable
`T₁, …, Tₙ` (with adjoints `Sᵢ`) and `b₁, …, bₙ ∈ 𝒷`,
`∑_{i,j} bᵢ* h(Tᵢ* Tⱼ) bⱼ ≥ 0`.

**Convention.**  The thesis uses *right* 𝒷-modules, whereas `inner` follows
Mathlib's `CStarModule` convention, so that `⟪u, v⟫ = ⟨v, u⟩_thesis` (see the
file header, and `module_CS` / `Theses.A.CStar.chilb_cs` for the same swap).
The thesis's `∑ᵢⱼ bᵢ* ⟨x, Tᵢ*Tⱼ x⟩ bⱼ ≥ 0` therefore mirrors to
`∑ᵢⱼ star (bᵢ) * ⟪Sᵢ(Tⱼ x), x⟫ * bⱼ ≥ 0` — the inner product's *arguments*
are interchanged.  Stated without the swap, i.e. with `⟪x, Sᵢ(Tⱼ x)⟫`, it is
**false**: taking `𝒷 = M₂(ℂ)` and `X = 𝒷` over itself (`⟪u,v⟫ = v u*`,
`yᵢ := Tᵢ x`) it would read `∑ᵢⱼ bᵢ* yⱼ yᵢ* bⱼ ≥ 0`, and random
`y₁,y₂,b₁,b₂ ∈ M₂(ℂ)` make the left-hand side (always self-adjoint)
indefinite.  The correct form is the Gram matrix
`∑ᵢⱼ bᵢ* ⟪Tⱼ x, Tᵢ x⟫ bⱼ = ⟪v, v⟫` for `v = ∑ₖ star (bₖ) • Tₖ x`, which is
what is proved here.

**145II** is the proof — not converted. -/
theorem hilbmod_vectstates_cp [VonNeumannAlgebra 𝒷] [CompleteSpace X]
    (x : X) (n : ℕ) (T S : Fin n → (X →L[ℂ] X))
    (hTS : ∀ i, ModuleAdjointTo 𝒷 ⇑(T i) ⇑(S i)) (b : Fin n → 𝒷) :
    0 ≤ ∑ i, ∑ j,
      star (b i) * inner 𝒷 (((S i).comp (T j)) x) x * b j := by
  -- `⟪Sᵢ(Tⱼ x), x⟫ = ⟪Tⱼ x, Tᵢ x⟫`
  have hadj : ∀ i j : Fin n,
      inner 𝒷 (((S i).comp (T j)) x) x = inner 𝒷 (T j x) (T i x) := fun i j =>
    moduleAdjointTo_symm (𝒜 := 𝒷) _ _ (hTS i) (T j x) x
  set v : X := ∑ k, star (b k) • T k x with hv
  have hvv : (inner 𝒷 v v : 𝒷)
      = ∑ i, ∑ j, star (b j) * inner 𝒷 (T i x) (T j x) * b i := by
    rw [hv, CStarModule.inner_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [CStarModule.inner_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
      star_star, mul_assoc]
  have hpos : (0 : 𝒷) ≤ inner 𝒷 v v := CStarModule.inner_self_nonneg
  rw [hvv, Finset.sum_comm] at hpos
  simpa only [hadj] using hpos

end VectStatesCP

/-! ## Parsec 1460: the ultranorm uniformity

**146I** (dils.tex:1738): introduction — nothing to formalize.
**146II** (`dils-dfn-uniformity`, dils.tex:1770, Definition): uniform
spaces — Mathlib's `UniformSpace`; **146III** discussion.
**146IIIa** (dils.tex:1828, Definition): subbases for uniformities. -/

section Uniformity

/-- **146IV** (`exc-subbase`, dils.tex:1835, Exercise): a family `B` of
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
    ∃ U : UniformSpace X, @uniformity X U = Filter.generate B := by
  choose! Wc hWcB hWcsub using hcomp
  choose! Ws hWsB hWssub using hsymm
  refine ⟨UniformSpace.ofCore (UniformSpace.Core.mk' (Filter.generate B) ?_ ?_ ?_), rfl⟩
  · -- every set of the generated filter contains the diagonal
    intro r hr x
    obtain ⟨t, htB, htfin, htr⟩ := Filter.mem_generate_iff.mp hr
    exact htr fun V hV => hrefl V (htB hV) x
  · -- symmetry
    intro r hr
    obtain ⟨t, htB, htfin, htr⟩ := Filter.mem_generate_iff.mp hr
    refine Filter.mem_generate_iff.mpr ⟨Ws '' t, ?_, htfin.image Ws, fun p hp => ?_⟩
    · rintro _ ⟨V, hV, rfl⟩
      exact hWsB V (htB hV)
    · refine htr fun V hV => ?_
      have hpW : p ∈ Ws V := hp _ ⟨V, hV, rfl⟩
      exact hWssub V (htB hV) (by simpa using hpW)
  · -- half-entourages
    intro r hr
    obtain ⟨t, htB, htfin, htr⟩ := Filter.mem_generate_iff.mp hr
    refine ⟨⋂₀ (Wc '' t),
      Filter.mem_generate_iff.mpr ⟨Wc '' t, ?_, htfin.image Wc, subset_rfl⟩, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩
      exact hWcB V (htB hV)
    · rintro ⟨a, c⟩ ⟨b, hab, hbc⟩
      refine htr fun V hV => ?_
      exact hWcsub V (htB hV) ⟨b, hab _ ⟨V, hV, rfl⟩, hbc _ ⟨V, hV, rfl⟩⟩

end Uniformity

section Ultranorm

variable {𝒷 : Type u}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]

/-- **146VII** (`dils-ultranorm`, dils.tex:1897, Definition): the seminorm
`‖x‖_ω = ω([x,x])^½` of an np-functional `ω : 𝒷 → ℂ`, for a 𝒷-module with
𝒷-valued inner product `B` (given as a bare function `B : X → X → 𝒷` so
that this applies to `BInner`s, to `CStarModule`s via `inner 𝒷`, and to `𝒷`
itself via `mulInner`).  The family of these seminorms, over all
np-functionals `ω`, constitutes the **ultranorm uniformity**; it is encoded
through the predicates `UnTendsto`, `UnCauchy`, `UnDense`, `UnComplete`
below.

**146VIII**'s two identifications are `unSeminorm_complex` and
`unSeminorm_mulInner_eq_omegaNorm` below; of **146IX** (Beware) the
quantitative half is `unSeminorm_le_norm_mul` and its converse ("but not
necessarily the other way around") is `unTendsto_not_norm_tendsto` below,
whose counterexample is `|n⟩⟨0|` on `ℓ²`.  146IX's remaining clause — that
the ultranorm uniformity is "in general not given by a single norm" — is
`unSeminorm_not_finitely_dominated` below: on `B(ℓ²)` no finite family of
the `‖·‖_ω` dominates all of them, which is what a generating single norm
would force.  **146X** (Remarks) has nothing to formalize. -/
noncomputable def unSeminorm {X : Type v} [AddCommGroup X]
    (ω : NPFunctional 𝒷) (B : X → X → 𝒷) (x : X) : ℝ :=
  Real.sqrt (ω (B x x)).re

/-- The inner product `⟨x, y⟩ = y x*` of the C*-algebra `𝒷` viewed as a
module over itself (Mathlib's `CStarModule 𝒷 𝒷` instance); with respect to
it the ultranorm uniformity on `𝒷` is the ultrastrong uniformity
(**146VIII**). -/
def mulInner (𝒷 : Type u) [CStarAlgebra 𝒷] : 𝒷 → 𝒷 → 𝒷 :=
  fun a b => b * star a

omit [StarOrderedRing 𝒷] in
/-- **146VIII** (dils.tex:1907), second identification: *"if `X = 𝒷` with
`[a,b] = a*b`, then the ultranorm uniformity coincides with the ultrastrong
uniformity"*.  Mirrored, as everywhere in this file: our `mulInner` is
`[a,b] = b a*`, so the ultranorm seminorms of `𝒷` over itself are the
ultrastrong seminorms `‖·‖_ω` of vn.tex **43I** composed with `star` — an
isomorphism of uniform spaces, so the two uniformities do coincide.
(`Kaplansky.lean` carries the same identity untagged, as
`unSeminorm_mulInner_eq`, where it is used to transfer 55V.) -/
theorem unSeminorm_mulInner_eq_omegaNorm (ω : NPFunctional 𝒷) (a : 𝒷) :
    unSeminorm ω (mulInner 𝒷) a = omegaNorm 𝒷 ω (star a) := by
  rw [omegaNorm, unSeminorm, star_star]
  rfl

variable {X : Type v} [AddCommGroup X]

/-- **146VIII** (dils.tex:1907), first identification: *"if `𝒷 = ℂ`, then
the ultranorm uniformity is the same as the uniformity induced by the
norm"*.  Every ultranorm seminorm of a ℂ-valued inner product is a scalar
multiple of the norm `‖x‖ = ‖[x,x]‖^½`, the scalar being `ω(1)^½` — so the
two seminorm families, and hence the two uniformities, agree. -/
theorem unSeminorm_complex {X : Type v} [AddCommGroup X] [Module ℂ X]
    (ω : NPFunctional ℂ) (B : BInner ℂ X) (x : X) :
    unSeminorm ω B.inner x = Real.sqrt (ω 1).re * B.norm x := by
  set a : ℂ := B.inner x x with ha
  have h0 : (0 : ℂ) ≤ a := B.inner_self_nonneg x
  have hre : 0 ≤ a.re := (Complex.le_def.mp h0).1
  have him : a.im = 0 := ((Complex.le_def.mp h0).2).symm
  have hlin : ω a = a * ω 1 := by
    have h : ω (a • (1 : ℂ)) = a * ω 1 := map_smul ω.toPositiveLinearMap a 1
    simpa using h
  have hnorm : ‖a‖ = a.re := by
    rw [Complex.norm_def, Complex.normSq_apply, him]
    simp [Real.sqrt_mul_self hre]
  rw [unSeminorm, BInner.norm, ← ha, hlin, hnorm, Complex.mul_re, him]
  simp [Real.sqrt_mul hre, mul_comm]

/-- **147I**.1 (`uniformity-basics`, dils.tex:1938, Definition),
specialized to the ultranorm uniformity: a net `x : ι → X` (along a filter
`l`) *converges ultranorm* to `x₀` when `‖x i - x₀‖_ω → 0` for every
np-functional `ω`. -/
def UnTendsto {ι : Type w} (B : X → X → 𝒷) (x : ι → X) (l : Filter ι)
    (x₀ : X) : Prop :=
  ∀ ω : NPFunctional 𝒷, Tendsto (fun i => unSeminorm ω B (x i - x₀)) l (𝓝 0)

/-- **147I**.2 (`uniformity-basics`, dils.tex:1938, Definition),
specialized to the ultranorm uniformity: a filter `F` on `X` (e.g. the
eventuality filter of a net) is *ultranorm Cauchy* when it contains, for
every `ω` and `ε > 0`, a set of diameter `≤ ε` for `‖·‖_ω`. -/
def UnCauchy (B : X → X → 𝒷) (F : Filter X) : Prop :=
  ∀ (ω : NPFunctional 𝒷) (ε : ℝ), 0 < ε →
    ∃ s ∈ F, ∀ x ∈ s, ∀ y ∈ s, unSeminorm ω B (x - y) ≤ ε

/-- **147I**.5 (`uniformity-basics`, dils.tex:1938, Definition),
specialized to the ultranorm uniformity: a subset `D ⊆ X` is *ultranorm
dense* when every `x ∈ X` is approximated within every entourage (finitely
many seminorms, `ε > 0`) by an element of `D`. -/
def UnDense (B : X → X → 𝒷) (D : Set X) : Prop :=
  ∀ (x : X) (n : ℕ) (ωs : Fin n → NPFunctional 𝒷) (ε : ℝ), 0 < ε →
    ∃ d ∈ D, ∀ i, unSeminorm (ωs i) B (x - d) ≤ ε

/-- **147I**.2 (`uniformity-basics`, dils.tex:1938, Definition), continued:
the ultranorm uniformity on `X` is *complete* when every (nontrivial)
ultranorm Cauchy filter converges. -/
def UnComplete (B : X → X → 𝒷) : Prop :=
  ∀ F : Filter X, F.NeBot → UnCauchy B F → ∃ x₀, UnTendsto B id F x₀

section Converse

local notation "ℓ²" => lp (fun _ : ℕ => ℂ) 2

/-- **146IX** (`dils-ultranorm`, dils.tex:1918, Beware), the converse half:
*"norm convergence implies ultranorm convergence, but not necessarily the
other way around"*.  The quantitative forward half is
`unSeminorm_le_norm_mul` below; here is the counterexample for the converse,
which the thesis leaves to the reader.

Take `𝒷 = X = B(ℓ²)` with `mulInner`, and `xₙ = |n⟩⟨0|`.  Then `xₙ → 0`
ultranorm: by `unSeminorm_mulInner_eq_omegaNorm` the ultranorm seminorms of
`mulInner` are the ultrastrong seminorms of `𝒷` composed with `star`, and
`(xₙ)* = |0⟩⟨n| → 0` ultrastrongly by **43II**.4
(`Theses.A.VN.vn_counterexamples_4_ket`).  But `(xₙ)` converges in norm to
*nothing at all*: norm convergence implies ultrastrong convergence (from
`‖a‖_ω ≤ ‖a‖ ‖1‖_ω`), and **43II**.4's second half
(`Theses.A.VN.vn_counterexamples_4_bra`) says `(xₙ)` has no ultrastrong
limit.  So the ultranorm uniformity is *strictly* weaker than the norm
uniformity. -/
theorem unTendsto_not_norm_tendsto :
    UnTendsto (mulInner (ℓ² →L[ℂ] ℓ²)) (fun n : ℕ => ketbraNat n 0) atTop 0 ∧
      ¬∃ T : ℓ² →L[ℂ] ℓ²,
        Tendsto (fun n : ℕ => ketbraNat n 0) atTop (𝓝 T) := by
  constructor
  · -- `‖xₙ‖_ω = ‖(xₙ)*‖_ω = ‖|0⟩⟨n|‖_ω → 0`
    intro ω
    have h := (usTendsto_iff (fun n : ℕ => ketbraNat 0 n) atTop 0).mp
      vn_counterexamples_4_ket ω
    refine h.congr fun n => ?_
    rw [sub_zero, sub_zero, unSeminorm_mulInner_eq_omegaNorm,
      (vn_counterexamples_1 0 0 0 n).1]
  · -- a norm limit would be an ultrastrong limit, and there is none
    rintro ⟨T, hT⟩
    refine vn_counterexamples_4_bra.2 ⟨T, ?_⟩
    rw [usTendsto_iff]
    intro ω
    have h0 : Tendsto (fun n : ℕ => ketbraNat n 0 - T) atTop (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.mpr hT
    have hnorm : Tendsto (fun n : ℕ => ‖ketbraNat n 0 - T‖) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp h0
    have hbd : Tendsto
        (fun n : ℕ => ‖ketbraNat n 0 - T‖ * omegaNorm (ℓ² →L[ℂ] ℓ²) ω 1)
        atTop (𝓝 0) := by
      simpa using hnorm.mul_const (omegaNorm (ℓ² →L[ℂ] ℓ²) ω 1)
    refine squeeze_zero (fun n => omegaNorm_nonneg _ _) (fun n => ?_) hbd
    have h := omegaNorm_mul_le ω (ketbraNat n 0 - T) 1
    rwa [mul_one] at h

/-! #### 146IX's first clause: the ultranorm uniformity is not normable

`unSeminorm_not_finitely_dominated` below, on the same `𝒷 = X = B(ℓ²)` with
`mulInner`.  Throughout `pₙ = |n⟩⟨n|` is `ketbraNat n n`, and the elements
tested are the multiples `t • |n⟩⟨0|`, for which
`‖t • |n⟩⟨0|‖_ω = |t| ω(pₙ)^½` (`nsn_unSeminorm_smul_ketbraNat`). -/

/-- An np-functional sends positive elements to nonnegative reals. -/
private theorem nsn_np_re_nonneg {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ω : NPFunctional A) {a : A} (ha : 0 ≤ a) :
    0 ≤ (ω a).re := by
  have h0 : (ω (0 : A) : ℂ) = 0 := map_zero ω.toPositiveLinearMap
  have h1 : (ω (0 : A) : ℂ) ≤ ω a := ω.monotone ha
  rw [h0] at h1
  simpa using (Complex.le_def.mp h1).1

/-- An np-functional is monotone, in particular on real parts. -/
private theorem nsn_np_re_mono {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ω : NPFunctional A) {a b : A} (hab : a ≤ b) :
    (ω a).re ≤ (ω b).re := by
  have h1 : (ω a : ℂ) ≤ ω b := ω.monotone hab
  exact (Complex.le_def.mp h1).1

/-- `pₙ = (|0⟩⟨n|)* |0⟩⟨n|`. -/
private theorem nsn_star_mul_self_ketbraNat (n : ℕ) :
    star (ketbraNat 0 n) * ketbraNat 0 n = ketbraNat n n := by
  rw [(vn_counterexamples_1 0 0 n 0).1, (vn_counterexamples_1 n 0 0 n).2, ite_eq_left rfl]

/-- `pₙ ≥ 0`. -/
private theorem nsn_ketbraNat_diag_nonneg (n : ℕ) :
    (0 : ℓ² →L[ℂ] ℓ²) ≤ ketbraNat n n :=
  (nsn_star_mul_self_ketbraNat n) ▸ star_mul_self_nonneg (ketbraNat 0 n)

/-- `‖t • |n⟩⟨0|‖_ω = |t| ω(pₙ)^½`, because
`(t |n⟩⟨0|) (t |n⟩⟨0|)* = t² |n⟩⟨0|0⟩⟨n| = t² pₙ`. -/
private theorem nsn_unSeminorm_smul_ketbraNat (ω : NPFunctional (ℓ² →L[ℂ] ℓ²))
    (t : ℝ) (n : ℕ) :
    unSeminorm ω (mulInner (ℓ² →L[ℂ] ℓ²)) ((t : ℂ) • ketbraNat n 0)
      = |t| * Real.sqrt (ω (ketbraNat n n)).re := by
  have hct : star ((t : ℂ)) = (t : ℂ) := Complex.conj_ofReal t
  have hstar : star ((t : ℂ) • ketbraNat n 0) = (t : ℂ) • ketbraNat 0 n := by
    rw [star_smul, hct, (vn_counterexamples_1 0 0 0 n).1]
  have hon : omegaNorm (ℓ² →L[ℂ] ℓ²) ω (ketbraNat 0 n)
      = Real.sqrt (ω (ketbraNat n n)).re := by
    rw [omegaNorm, nsn_star_mul_self_ketbraNat n]
  rw [unSeminorm_mulInner_eq_omegaNorm, hstar, omegaNorm_smul, hon,
    Complex.norm_real, Real.norm_eq_abs]

/-- `∑_{n<N} pₙ ≤ 1`: the partial sum `q` is a self-adjoint idempotent, so
`1 − q = (1 − q)* (1 − q) ≥ 0`. -/
private theorem nsn_sum_ketbraNat_le_one (N : ℕ) :
    (∑ n ∈ Finset.range N, ketbraNat n n) ≤ (1 : ℓ² →L[ℂ] ℓ²) := by
  obtain ⟨q, hq⟩ : ∃ q : ℓ² →L[ℂ] ℓ², q = ∑ n ∈ Finset.range N, ketbraNat n n :=
    ⟨_, rfl⟩
  rw [← hq]
  have hstar : star q = q := by
    rw [hq, star_sum]
    exact Finset.sum_congr rfl fun n _ => (vn_counterexamples_1 0 0 n n).1
  have hidem : q * q = q := by
    rw [hq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hsingle : ∑ m ∈ Finset.range N, ketbraNat n n * ketbraNat m m
        = ketbraNat n n * ketbraNat n n :=
      Finset.sum_eq_single n
        (fun m _ hmn => by rw [(vn_counterexamples_1 m m n n).2, ite_eq_right (Ne.symm hmn)])
        (fun h => absurd hn h)
    rw [Finset.mul_sum, hsingle, (vn_counterexamples_1 n n n n).2, ite_eq_left rfl]
  have hpos : (0 : ℓ² →L[ℂ] ℓ²) ≤ 1 - q := by
    have hexp : (1 - q) * (1 - q) = 1 - q - q + q * q := by
      simp only [sub_mul, mul_sub, one_mul, mul_one]
      abel
    have h : star (1 - q) * (1 - q) = 1 - q := by
      rw [star_sub, star_one, hstar, hexp, hidem]
      abel
    exact h ▸ star_mul_self_nonneg (1 - q)
  exact sub_nonneg.mp hpos

/-- The partial sums `∑_{n<N} ω(pₙ)` are bounded by `ω(1)`. -/
private theorem nsn_sum_re_le (ω : NPFunctional (ℓ² →L[ℂ] ℓ²)) (N : ℕ) :
    ∑ n ∈ Finset.range N, (ω (ketbraNat n n)).re ≤ (ω 1).re := by
  have hsum : ω (∑ n ∈ Finset.range N, ketbraNat n n)
      = ∑ n ∈ Finset.range N, ω (ketbraNat n n) :=
    map_sum ω.toPositiveLinearMap _ _
  calc ∑ n ∈ Finset.range N, (ω (ketbraNat n n)).re
      = (ω (∑ n ∈ Finset.range N, ketbraNat n n)).re := by rw [hsum, Complex.re_sum]
    _ ≤ (ω 1).re := nsn_np_re_mono ω (nsn_sum_ketbraNat_le_one N)

/-- The one piece of real analysis behind the theorem: for a *positive
summable* sequence `b` there is a positive summable `c` with `cₙ / bₙ → ∞`.
Take the tails `rₙ = ∑_{m ≥ n} bₘ` and `cₙ = √rₙ − √r_{n+1} > 0`: then
`cₙ (√rₙ + √r_{n+1}) = bₙ`, so `cₙ / bₙ ≥ 1 / (2√rₙ) → ∞`, while
`∑_{n<N} cₙ = √r₀ − √r_N ≤ √r₀`. -/
private theorem nsn_exists_summable_div_atTop {b : ℕ → ℝ} (hbpos : ∀ n, 0 < b n)
    (hb : Summable b) :
    ∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧ Summable c ∧
      Tendsto (fun n => c n / b n) atTop atTop := by
  have hbs : ∀ n : ℕ, Summable fun m => b (m + n) := fun n =>
    (summable_nat_add_iff n).2 hb
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, ∀ n, r n = ∑' m, b (m + n) := ⟨_, fun _ => rfl⟩
  have hrnonneg : ∀ n, 0 ≤ r n := by
    intro n
    rw [hr]
    exact tsum_nonneg fun m => (hbpos _).le
  have hrec : ∀ n, r n = b n + r (n + 1) := by
    intro n
    have key : ∑' m, b (m + n) = b (0 + n) + ∑' m, b (m + 1 + n) :=
      (hbs n).tsum_eq_zero_add
    have h2 : ∑' m, b (m + 1 + n) = ∑' m, b (m + (n + 1)) :=
      tsum_congr fun m => by rw [show m + 1 + n = m + (n + 1) from by omega]
    rw [hr n, hr (n + 1), key, h2, zero_add]
  have hrpos : ∀ n, 0 < r n := by
    intro n
    rw [hrec n]
    exact add_pos_of_pos_of_nonneg (hbpos n) (hrnonneg (n + 1))
  have hrlt : ∀ n, r (n + 1) < r n := by
    intro n
    have h := hrec n
    linarith [hbpos n]
  have hrtend : Tendsto r atTop (𝓝 0) :=
    (tendsto_sum_nat_add b).congr fun n => (hr n).symm
  have hcpos : ∀ n, 0 < Real.sqrt (r n) - Real.sqrt (r (n + 1)) := fun n =>
    sub_pos.mpr (Real.sqrt_lt_sqrt (hrnonneg (n + 1)) (hrlt n))
  refine ⟨fun n => Real.sqrt (r n) - Real.sqrt (r (n + 1)), hcpos, ?_, ?_⟩
  · refine summable_of_sum_range_le (c := Real.sqrt (r 0))
      (fun n => (hcpos n).le) fun N => ?_
    show (∑ i ∈ Finset.range N, (Real.sqrt (r i) - Real.sqrt (r (i + 1))))
      ≤ Real.sqrt (r 0)
    rw [Finset.sum_range_sub' (fun n => Real.sqrt (r n)) N]
    have h : 0 ≤ Real.sqrt (r N) := Real.sqrt_nonneg _
    linarith
  · -- `cₙ / bₙ ≥ 1 / (2√rₙ) → ∞`
    have hsqrt : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hrtend
      simpa [Function.comp_def] using h
    have hg : Tendsto (fun n => 2 * Real.sqrt (r n)) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa using hsqrt.const_mul 2
      · filter_upwards with n
        exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (hrpos n))
    have hginv : Tendsto (fun n => (2 * Real.sqrt (r n))⁻¹) atTop atTop :=
      hg.inv_tendsto_nhdsGT_zero
    refine tendsto_atTop_mono (fun n => ?_) hginv
    have hu : 0 < Real.sqrt (r n) := Real.sqrt_pos.mpr (hrpos n)
    have hv : 0 ≤ Real.sqrt (r (n + 1)) := Real.sqrt_nonneg _
    have hvu : Real.sqrt (r (n + 1)) < Real.sqrt (r n) :=
      Real.sqrt_lt_sqrt (hrnonneg (n + 1)) (hrlt n)
    have h1 : Real.sqrt (r n) ^ 2 = r n := Real.sq_sqrt (hrnonneg n)
    have h2 : Real.sqrt (r (n + 1)) ^ 2 = r (n + 1) := Real.sq_sqrt (hrnonneg (n + 1))
    have hprod : (Real.sqrt (r n) - Real.sqrt (r (n + 1))) *
        (Real.sqrt (r n) + Real.sqrt (r (n + 1))) = b n := by
      have h3 := hrec n
      nlinarith [h1, h2, h3]
    have hden : (0 : ℝ) < 2 * Real.sqrt (r n) := by linarith
    show (2 * Real.sqrt (r n))⁻¹
      ≤ (Real.sqrt (r n) - Real.sqrt (r (n + 1))) / b n
    rw [le_div_iff₀ (hbpos n), inv_mul_le_iff₀ hden]
    nlinarith [hprod, sq_nonneg (Real.sqrt (r n) - Real.sqrt (r (n + 1)))]

/-- **146IX** (`dils-ultranorm`, dils.tex:1915, Beware), first clause: the
ultranorm uniformity is *"in general not given by a single norm"*.  The
uniformity is encoded here as the family of seminorms `‖·‖_ω` over all
np-functionals, so a single norm generating it would make finitely many
`‖·‖_ω` dominate all of them; on `𝒷 = X = B(ℓ²)` with `mulInner` that fails:
for every finite family `ω₁, …, ωₘ` there is an np-functional `ω₀` and a
sequence bounded by `1` in every `‖·‖_{ωₖ}` whose `‖·‖_{ω₀}` tends to
infinity.

The witness.  With `pₙ = |n⟩⟨n|` put `aₙ = ∑_{ω ∈ s} ω(pₙ)`, which is
summable because `∑_{n<N} pₙ ≤ 1` (`nsn_sum_ketbraNat_le_one`), and
`bₙ = aₙ + 2⁻ⁿ > 0`.  Pick, by `nsn_exists_summable_div_atTop`, a positive
summable `c` with `cₙ/bₙ → ∞`; let `ξ ∈ ℓ²` have coordinates `√cₙ` and
`ω₀ = ⟪ξ, (·) ξ⟫`, so that `ω₀(pₙ) = cₙ`.  Then `xₙ = bₙ^{-½} |n⟩⟨0|` has
`‖xₙ‖_ω = √(ω(pₙ)/bₙ) ≤ 1` for `ω ∈ s`, while `‖xₙ‖_{ω₀} = √(cₙ/bₙ) → ∞`. -/
theorem unSeminorm_not_finitely_dominated (s : Finset (NPFunctional (ℓ² →L[ℂ] ℓ²))) :
    ∃ (ω₀ : NPFunctional (ℓ² →L[ℂ] ℓ²)) (x : ℕ → ℓ² →L[ℂ] ℓ²),
      (∀ ω ∈ s, ∀ n, unSeminorm ω (mulInner (ℓ² →L[ℂ] ℓ²)) (x n) ≤ 1) ∧
      Tendsto (fun n => unSeminorm ω₀ (mulInner (ℓ² →L[ℂ] ℓ²)) (x n)) atTop atTop := by
  -- `aₙ = ∑_{ω ∈ s} ω(pₙ)` is nonnegative and summable
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ n, a n = ∑ ω ∈ s, (ω (ketbraNat n n)).re :=
    ⟨_, fun _ => rfl⟩
  have hanonneg : ∀ n, 0 ≤ a n := by
    intro n
    rw [ha]
    exact Finset.sum_nonneg fun ω _ => nsn_np_re_nonneg ω (nsn_ketbraNat_diag_nonneg n)
  have hasummable : Summable a := by
    refine summable_of_sum_range_le (c := ∑ ω ∈ s, (ω 1).re) hanonneg fun N => ?_
    simp only [ha]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun ω _ => nsn_sum_re_le ω N
  -- `bₙ = aₙ + 2⁻ⁿ` is positive and summable
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, ∀ n, b n = a n + (1 / 2 : ℝ) ^ n := ⟨_, fun _ => rfl⟩
  have hbpos : ∀ n, 0 < b n := by
    intro n
    have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    rw [hb]
    linarith [hanonneg n]
  have hbsummable : Summable b :=
    (hasummable.add summable_geometric_two).congr fun n => (hb n).symm
  obtain ⟨c, hcpos, hcsummable, hctend⟩ := nsn_exists_summable_div_atTop hbpos hbsummable
  -- the vector `ξ ∈ ℓ²` with coordinates `√cₙ`, and `ω₀ = ⟪ξ, (·) ξ⟫`
  have hmem : Memℓp (fun n : ℕ => ((Real.sqrt (c n) : ℝ) : ℂ)) 2 := by
    have hpow : ∀ n : ℕ,
        ‖((Real.sqrt (c n) : ℝ) : ℂ)‖ ^ (2 : ENNReal).toReal = c n := by
      intro n
      have h1 : ‖((Real.sqrt (c n) : ℝ) : ℂ)‖ = Real.sqrt (c n) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [h1, show (2 : ENNReal).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        Real.sq_sqrt (hcpos n).le]
    exact memℓp_gen (hcsummable.congr fun n => (hpow n).symm)
  obtain ⟨ξ, hxi⟩ : ∃ ξ : ℓ², ∀ n : ℕ, (ξ : ℕ → ℂ) n = ((Real.sqrt (c n) : ℝ) : ℂ) :=
    ⟨⟨fun n => ((Real.sqrt (c n) : ℝ) : ℂ), hmem⟩, fun _ => rfl⟩
  have hket : ∀ n : ℕ, ketbraNat n n ξ
      = (⟪(lp.single 2 n (1 : ℂ) : ℓ²), ξ⟫ : ℂ) • (lp.single 2 n (1 : ℂ) : ℓ²) :=
    fun _ => rfl
  have hval : ∀ n : ℕ, ((vectorNP ξ) (ketbraNat n n) : ℂ) = ((c n : ℝ) : ℂ) := by
    intro n
    have e1 : (⟪(lp.single 2 n (1 : ℂ) : ℓ²), ξ⟫ : ℂ) = ((Real.sqrt (c n) : ℝ) : ℂ) := by
      rw [lp.inner_single_left]
      simp [hxi n]
    have e2 : (⟪ξ, (lp.single 2 n (1 : ℂ) : ℓ²)⟫ : ℂ) = ((Real.sqrt (c n) : ℝ) : ℂ) := by
      rw [lp.inner_single_right]
      simp [hxi n]
    rw [vectorNP_apply, hket n, inner_smul_right, e1, e2, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hcpos n).le]
  have hre : ∀ n : ℕ, ((vectorNP ξ) (ketbraNat n n)).re = c n := by
    intro n
    rw [hval n, Complex.ofReal_re]
  refine ⟨vectorNP ξ, fun n => (((1 : ℝ) / Real.sqrt (b n) : ℝ) : ℂ) • ketbraNat n 0,
    ?_, ?_⟩
  · -- the family `s` sees the sequence as bounded by `1`
    intro ω hω n
    have hbs : 0 < Real.sqrt (b n) := Real.sqrt_pos.mpr (hbpos n)
    have h1 : (ω (ketbraNat n n)).re ≤ a n := by
      rw [ha]
      exact Finset.single_le_sum
        (f := fun ω : NPFunctional (ℓ² →L[ℂ] ℓ²) => (ω (ketbraNat n n)).re)
        (fun ω' _ => nsn_np_re_nonneg ω' (nsn_ketbraNat_diag_nonneg n)) hω
    have hle : (ω (ketbraNat n n)).re ≤ b n := by
      have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
      rw [hb]
      linarith
    show unSeminorm ω (mulInner (ℓ² →L[ℂ] ℓ²))
      ((((1 : ℝ) / Real.sqrt (b n) : ℝ) : ℂ) • ketbraNat n 0) ≤ 1
    rw [nsn_unSeminorm_smul_ketbraNat, abs_of_pos (one_div_pos.mpr hbs),
      div_mul_eq_mul_div, one_mul, div_le_one hbs]
    exact Real.sqrt_le_sqrt hle
  · -- but `ω₀` does not
    have hform : ∀ n : ℕ, unSeminorm (vectorNP ξ) (mulInner (ℓ² →L[ℂ] ℓ²))
        ((((1 : ℝ) / Real.sqrt (b n) : ℝ) : ℂ) • ketbraNat n 0)
        = Real.sqrt (c n / b n) := by
      intro n
      have hbs : 0 < Real.sqrt (b n) := Real.sqrt_pos.mpr (hbpos n)
      rw [nsn_unSeminorm_smul_ketbraNat, hre n, abs_of_pos (one_div_pos.mpr hbs),
        Real.sqrt_div (hcpos n).le, div_mul_eq_mul_div, one_mul]
    simp only [hform]
    simpa [Function.comp_def] using Real.tendsto_sqrt_atTop.comp hctend

end Converse

end Ultranorm

/-! ## Parsec 1470: basics of uniform spaces

**147I** (`uniformity-basics`, dils.tex:1938, Definition): convergence,
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

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1990, Exercise), part
1, **both claims**: equivalence of Cauchy filters is reflexive, symmetric
and transitive; *and* a subnet of a Cauchy net is equivalent to it.

A subnet is rendered by its eventuality filter: the tail filter of a subnet
of `(y_α)_α` refines the tail filter of `(y_α)_α`, so "`F` is a subnet of
`G`" is `F ≤ G` — that, and Cauchyness of `G`, is all the fourth clause
needs. -/
theorem dils_uniform_spaces_basics_1 :
    (∀ F : Filter X, Cauchy F → FilterEquiv F F) ∧
    (∀ F G : Filter X, Cauchy F → Cauchy G → FilterEquiv F G →
      FilterEquiv G F) ∧
    (∀ F G H : Filter X, Cauchy F → Cauchy G → Cauchy H →
      FilterEquiv F G → FilterEquiv G H → FilterEquiv F H) ∧
    (∀ F G : Filter X, Cauchy G → F ≤ G → FilterEquiv F G) := by
  refine ⟨fun F hF V hV => ?_, fun F G _ _ h V hV => ?_,
    fun F G H _ hG _ hFG hGH V hV => ?_, fun F G hG hFG V hV => ?_⟩
  · -- reflexivity: `F ×ˢ F ≤ 𝓤 X` is exactly Cauchyness
    obtain ⟨s, hs, t, ht, hst⟩ := Filter.mem_prod_iff.mp (hF.2 hV)
    exact ⟨s, hs, t, ht, hst⟩
  · -- symmetry: use that `𝓤 X` is invariant under `Prod.swap`
    obtain ⟨s, hs, t, ht, hst⟩ := h _ (symm_le_uniformity hV)
    refine ⟨t, ht, s, hs, ?_⟩
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact hst (Set.mk_mem_prod hb ha)
  · -- transitivity: split `V` as `W ○ W` and use a point of the middle filter
    obtain ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV
    obtain ⟨s, hs, t₁, ht₁, hst⟩ := hFG W hW
    obtain ⟨t₂, ht₂, u, hu, htu⟩ := hGH W hW
    obtain ⟨y, hy₁, hy₂⟩ := hG.1.nonempty_of_mem (Filter.inter_mem ht₁ ht₂)
    refine ⟨s, hs, u, hu, ?_⟩
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact hWV ⟨y, hst (Set.mk_mem_prod ha hy₁), htu (Set.mk_mem_prod hy₂ hb)⟩
  · -- a subnet is equivalent to its net: `G`'s own Cauchy witness works on
    -- both sides, since every set of `G` is a set of `F`
    obtain ⟨s, hs, t, ht, hst⟩ := Filter.mem_prod_iff.mp (hG.2 hV)
    exact ⟨s, hFG hs, t, ht, hst⟩

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1990, Exercise), part
2: equivalent Cauchy filters have the same limits. -/
theorem dils_uniform_spaces_basics_2 (F G : Filter X) (hF : Cauchy F)
    (hG : Cauchy G) (h : FilterEquiv F G) (x : X) (hFx : F ≤ 𝓝 x) :
    G ≤ 𝓝 x := by
  rw [nhds_eq_comap_uniformity, ← Filter.map_le_iff_le_comap]
  rw [nhds_eq_comap_uniformity, ← Filter.map_le_iff_le_comap] at hFx
  intro V hV
  -- split `V = W ○ W`; `F` is `W`-close to `x` and `G` is `W`-close to `F`
  obtain ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV
  obtain ⟨s, hs, t, ht, hst⟩ := h W hW
  obtain ⟨y, hy₁, hy₂⟩ := hF.1.nonempty_of_mem (Filter.inter_mem hs (hFx hW))
  refine Filter.mem_map.mpr (Filter.mem_of_superset ht fun z hz => ?_)
  exact hWV ⟨y, hy₂, hst (Set.mk_mem_prod hy₁ hz)⟩

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1990, Exercise), part
3: limits are unique in a Hausdorff uniform space.

*Class 1 — faithful.*  The proof is the printed solution's
(`bsols.tex:543`, item 3): given an entourage `ε`, pick `δ` with `δ² ⊆ ε` and
`δ' ⊆ δ⁻¹`; the net is eventually `δ`-close to `a` and `δ'`-close to `b`, so
`a ε b`; and since this holds for every entourage and the space is Hausdorff,
`a = b`. -/
theorem dils_uniform_spaces_basics_3 [T2Space X] {ι : Type w} (l : Filter ι)
    [l.NeBot] (x : ι → X) (a b : X) (ha : Tendsto x l (𝓝 a))
    (hb : Tendsto x l (𝓝 b)) : a = b := by
  -- "as our space is Hausdorff", it is enough to get `a ε b` for every `ε`
  refine eq_of_uniformity fun {V} hV => ?_
  -- "pick `δ` and `δ'` with `δ² ⊆ ε` and `δ' ⊆ δ⁻¹`"
  obtain ⟨δ, hδ, hδV⟩ := comp_mem_uniformity_sets hV
  have hδs : Prod.swap ⁻¹' δ ∈ 𝓤 X := symm_le_uniformity hδ
  rw [nhds_eq_comap_uniformity, Filter.tendsto_comap_iff] at ha hb
  -- "there is an `α₀` such that `x_α δ a` and `x_α δ' b` for all `α ≥ α₀`"
  have h₁ : ∀ᶠ i in l, (a, x i) ∈ δ := ha hδ
  have h₂ : ∀ᶠ i in l, (x i, b) ∈ δ := hb hδs
  obtain ⟨i, hi₁, hi₂⟩ := (h₁.and h₂).exists
  -- "thus `a ε b`", through `δ ○ δ ⊆ ε` at the point `x i` of the net
  exact hδV ⟨x i, hi₁, hi₂⟩

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1990, Exercise), part
4: continuous maps preserve limits of nets (Mathlib:
`Continuous.tendsto.comp`). -/
theorem dils_uniform_spaces_basics_4 (f : X → Y) (hf : Continuous f)
    {ι : Type w} (l : Filter ι) (x : ι → X) (a : X)
    (ha : Tendsto x l (𝓝 a)) : Tendsto (f ∘ x) l (𝓝 (f a)) :=
  (hf.tendsto a).comp ha

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1990, Exercise), part
5: uniformly continuous maps send Cauchy filters to Cauchy filters and
preserve equivalence.

The printed solution's order (`bsols.tex:621`): it proves first that `f`
preserves the relation *"for each entourage `ε` there are `α₀, β₀` with
`x_α ε y_β`"* between two nets — by uniform continuity, pick `δ` with
`x δ y ⟹ f(x) ε f(y)` and push the witnesses through — and then remarks
*"from the previous it follows that `f` preserves Cauchy nets (by setting
`x_α = y_α`) and that it preserves equivalence between Cauchy nets"*.  That
relation is `FilterEquiv`, and `Cauchy F` is `FilterEquiv F F` with `F` non
trivial (part 1's reflexivity), so both halves come out of the one
argument. -/
theorem dils_uniform_spaces_basics_5 (f : X → Y) (hf : UniformContinuous f) :
    (∀ F : Filter X, Cauchy F → Cauchy (F.map f)) ∧
    (∀ F G : Filter X, Cauchy F → Cauchy G → FilterEquiv F G →
      FilterEquiv (F.map f) (G.map f)) := by
  -- the solution's single argument: `(f × f)⁻¹ V` is an entourage of `X`,
  -- and the images of the witnesses work
  have key : ∀ F G : Filter X, FilterEquiv F G → FilterEquiv (F.map f) (G.map f) := by
    intro F G h V hV
    obtain ⟨s, hs, t, ht, hst⟩ := h _ (hf hV)
    refine ⟨f '' s, Filter.image_mem_map hs, f '' t, Filter.image_mem_map ht, ?_⟩
    rintro ⟨a, b⟩ ⟨⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩⟩
    exact hst (Set.mk_mem_prod ha' hb')
  refine ⟨fun F hF => ⟨hF.1.map f, fun V hV => ?_⟩, fun F G _ _ h => key F G h⟩
  -- "by setting `x_α = y_α`": `F` is equivalent to itself by part 1
  obtain ⟨s, hs, t, ht, hst⟩ :=
    key F F ((dils_uniform_spaces_basics_1 (X := X)).1 F hF) V hV
  exact Filter.mem_prod_iff.mpr ⟨s, hs, t, ht, hst⟩

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1990, Exercise), part
6: for a dense `D ⊆ X`, every point is the limit of a Cauchy filter living
on `D`.

The solution's own construction: *"Pick for every `ε ∈ Φ` an element
`d_ε ∈ D` with `x ε d_ε`.  Clearly `(d_ε)_{ε∈Φ}` is a net with inverse
inclusion.  We have `d_ε → x` as `d_δ ε x` whenever `δ ⊆ ε`."*  The net is
indexed by the entourages ordered by reverse inclusion — `(𝓤 X)`'s sets as
an `OrderDual` subtype, directed because `𝓤 X` is a filter — and the Cauchy
filter of the statement is the filter of that net, `map d atTop`; it is
Cauchy because it converges. -/
theorem dils_uniform_spaces_basics_6 (D : Set X) (hD : Dense D) (x : X) :
    ∃ F : Filter X, F.NeBot ∧ D ∈ F ∧ Cauchy F ∧ F ≤ 𝓝 x := by
  -- "a net with inverse inclusion": `Φ` ordered by `δ ≥ ε ⟺ δ ⊆ ε`
  have hdir : IsDirectedOrder ({V : Set (X × X) // V ∈ 𝓤 X})ᵒᵈ := by
    refine ⟨fun V W => ⟨(⟨V.1 ∩ W.1, inter_mem V.2 W.2⟩ :
      {V : Set (X × X) // V ∈ 𝓤 X}), ?_, ?_⟩⟩
    · exact Set.inter_subset_left
    · exact Set.inter_subset_right
  -- "Pick for every `ε ∈ Φ` an element `d_ε ∈ D` with `x ε d_ε`"
  have hpick : ∀ V : ({V : Set (X × X) // V ∈ 𝓤 X})ᵒᵈ,
      ∃ p : X, p ∈ D ∧ (x, p) ∈ V.1 := by
    intro V
    obtain ⟨p, hp, hpD⟩ := mem_closure_iff_nhds.mp (hD x) _
      (UniformSpace.ball_mem_nhds x V.2)
    exact ⟨p, hpD, hp⟩
  choose d hdD hdV using hpick
  -- "`d_ε → x`, as `d_δ ε x` whenever `δ ⊆ ε`"
  have htends : Tendsto d atTop (𝓝 x) := by
    rw [(nhds_basis_uniformity' (Filter.basis_sets (𝓤 X))).tendsto_right_iff]
    intro V hV
    exact Filter.eventually_atTop.mpr ⟨⟨V, hV⟩, fun W hW => hW (hdV W)⟩
  have hne : (Filter.map d atTop).NeBot := Filter.map_neBot
  exact ⟨Filter.map d atTop, hne, Filter.mem_map.mpr (Filter.univ_mem' hdD),
    cauchy_nhds.mono htends, htends⟩

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1990, Exercise), part
7: continuous maps into a Hausdorff space agreeing on a dense set are equal.

The exercise's own instruction is *"Conclude from
`ex-continuous-preserves-lims` and `ex-cauchy-from-dense-subset`"*, i.e.
from parts **4** and **6**, and that is the proof: part 6 puts a Cauchy
filter `F` on `D` converging to `x`, part 4 (applied to the "net"
`id : X → X` along `F`) sends it to `f x` and to `g x`, and `f = g` along
`F` because `D ∈ F`; part **3** then identifies the two limits.  (Mathlib's
`Continuous.ext_on` closes this in one step, but that hides the point of the
item — and leaves part 6 with no consumer at all.) -/
theorem dils_uniform_spaces_basics_7 [T2Space Y] (f g : X → Y)
    (hf : Continuous f) (hg : Continuous g) (D : Set X) (hD : Dense D)
    (h : Set.EqOn f g D) : f = g := by
  funext x
  obtain ⟨F, hFne, hFD, -, hFx⟩ := dils_uniform_spaces_basics_6 D hD x
  haveI : F.NeBot := hFne
  have hfx : Tendsto (f ∘ id) F (𝓝 (f x)) :=
    dils_uniform_spaces_basics_4 f hf F id x hFx
  have hgx : Tendsto (g ∘ id) F (𝓝 (g x)) :=
    dils_uniform_spaces_basics_4 g hg F id x hFx
  have hEq : (g ∘ id) =ᶠ[F] (f ∘ id) :=
    Filter.eventuallyEq_of_mem hFD fun z hz => (h hz).symm
  exact dils_uniform_spaces_basics_3 (X := Y) F (f ∘ id) (f x) (g x) hfx
    (hgx.congr' hEq)

/-- **147III** (`dils-product-uniformity`, dils.tex:2029, Exercise): the
relations `(x_i)_i ε̂ (y_i)_i ⟺ x_{i₀} ε y_{i₀}` of the exercise, one for
each `i₀ ∈ I` and each entourage `ε ∈ Φ_{i₀}`. -/
def piSubbase {ι : Type w} (Z : ι → Type v) [∀ i, UniformSpace (Z i)] :
    Set (Set ((∀ i, Z i) × (∀ i, Z i))) :=
  {V | ∃ (i : ι) (ε : Set (Z i × Z i)), ε ∈ 𝓤 (Z i) ∧
    V = {q : (∀ i, Z i) × (∀ i, Z i) | (q.1 i, q.2 i) ∈ ε}}

/-- **147III** (`dils-product-uniformity`, dils.tex:2029, Exercise), **all
three claims**.

1. The relations `ε̂` are a *subbase* (**146IIIa**) for the product
   uniformity: they satisfy the three subbase axioms that **146IV**
   `exc_subbase` takes as its hypotheses, and the product uniformity
   (Mathlib: `Pi.uniformSpace`) *is* the filter they generate.
2. The projections are uniformly continuous — the solution's *"define
   `δ ≡ ε̂`"*, which here is the observation that `ε̂` is a subbase element
   and so an entourage.
3. `Π Xᵢ` is the categorical product in uniform spaces: a map into it is
   uniformly continuous iff all its components are.  The solution's own
   argument: an entourage of `Π Xᵢ` contains a finite intersection
   `⋂ⱼ ε̂ⱼ`, one picks `δⱼ` for each `fᵢⱼ` and takes `δ = ⋂ⱼ δⱼ`; through
   `le_generate_iff` the finite intersection is handled by the filter, so
   only the single-`ε̂` step is left to do. -/
theorem dils_product_uniformity {ι : Type w} {Z : ι → Type v}
    [∀ i, UniformSpace (Z i)] (f : X → ∀ i, Z i) :
    ((∀ V ∈ piSubbase Z, ∀ x : ∀ i, Z i, (x, x) ∈ V) ∧
        (∀ V ∈ piSubbase Z, ∃ W ∈ piSubbase Z, SetRel.comp W W ⊆ V) ∧
        (∀ V ∈ piSubbase Z, ∃ W ∈ piSubbase Z, Prod.swap ⁻¹' W ⊆ V) ∧
        𝓤 (∀ i, Z i) = Filter.generate (piSubbase Z)) ∧
      (∀ i, UniformContinuous fun z : ∀ i, Z i => z i) ∧
      (UniformContinuous f ↔ ∀ i, UniformContinuous fun x => f x i) := by
  -- the generated filter: `𝓤 (Π Xᵢ) = ⨅ᵢ comap πᵢ (𝓤 Xᵢ)`, and the
  -- infimum of comaps is generated by the preimages.  (The solution does
  -- not need this: it *defines* the product uniformity by the subbase,
  -- where we must match Mathlib's `Pi.uniformSpace`.)
  have hgen : 𝓤 (∀ i, Z i) = Filter.generate (piSubbase Z) := by
    refine le_antisymm ?_ ?_
    · rw [le_generate_iff]
      rintro V ⟨i, ε, hε, rfl⟩
      rw [Pi.uniformity]
      exact Filter.mem_iInf_of_mem i (Filter.preimage_mem_comap hε)
    · rw [Pi.uniformity]
      refine le_iInf fun i => fun t ht => ?_
      obtain ⟨u, hu, hut⟩ := Filter.mem_comap.mp ht
      exact Filter.mem_of_superset
        (Filter.mem_generate_of_mem (⟨i, u, hu, rfl⟩ : _ ∈ piSubbase Z)) hut
  -- clause 2, the solution's `δ ≡ ε̂`
  have hproj : ∀ i, UniformContinuous fun z : ∀ i, Z i => z i := by
    intro i
    rw [uniformContinuous_def]
    intro ε hε
    rw [hgen]
    exact Filter.mem_generate_of_mem (⟨i, ε, hε, rfl⟩ : _ ∈ piSubbase Z)
  refine ⟨⟨?_, ?_, ?_, hgen⟩, hproj, ⟨fun h i => (hproj i).comp h, fun h => ?_⟩⟩
  · -- axiom 2: `x ε̂ x`, because `x_i ε x_i`
    rintro _ ⟨i, ε, hε, rfl⟩ x
    exact (refl_mem_uniformity hε : (x i, x i) ∈ ε)
  · -- axiom 3: a half-entourage of `ε` gives a half-entourage of `ε̂`
    rintro _ ⟨i, ε, hε, rfl⟩
    obtain ⟨δ, hδ, hδε⟩ := comp_mem_uniformity_sets hε
    refine ⟨_, ⟨i, δ, hδ, rfl⟩, ?_⟩
    rintro ⟨a, c⟩ ⟨b, hab, hbc⟩
    exact hδε ⟨b i, hab, hbc⟩
  · -- axiom 4: the reverse of `ε̂` is the hat of the reverse of `ε`
    rintro _ ⟨i, ε, hε, rfl⟩
    exact ⟨_, ⟨i, Prod.swap ⁻¹' ε, symm_le_uniformity hε, rfl⟩, fun _ h => h⟩
  · -- clause 3, "⟸": it is enough to hit every `ε̂`, the filter taking care
    -- of the solution's `δ = ⋂ⱼ δⱼ`
    have hle : Filter.map (fun x : X × X => (f x.1, f x.2)) (𝓤 X)
        ≤ 𝓤 (∀ i, Z i) := by
      rw [hgen, le_generate_iff]
      rintro V ⟨i, ε, hε, rfl⟩
      exact Filter.mem_map.mpr (uniformContinuous_def.mp (h i) ε hε)
    exact hle

end UniformBasics

/-! ## Parsec 1480: ultranorm continuity of the operations -/

section UltranormContinuity

-- `Y` is deliberately in its own universe: **148I** and the seminorm form of
-- **144V** below are applied with `Y = 𝒷` (in universe `u`) in the proof of
-- **149V**.
variable {𝒷 : Type u} {X : Type v} {Y : Type*}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [AddCommGroup X] [Module ℂ X] [SMul 𝒷 X]
  [AddCommGroup Y] [Module ℂ Y] [SMul 𝒷 Y]

/-! ### Auxiliary: the seminorms `‖·‖_ω` of the ultranorm uniformity

By **142II** the ℂ-valued form `(x,y) ↦ ω[x,y]` of an np-functional `ω` and a
𝒷-valued inner product `B` is a (semidefinite) inner product; the
Cauchy–Schwarz and triangle inequalities for `‖x‖_ω = ω([x,x])^½` below are
cstar.tex 4XV (`inner-product-basic`) for that form, written out for the
semidefinite case (Mathlib's `InnerProductSpace` machinery needs
definiteness).  First, the linearity, involutivity and positivity of an
np-functional in the form in which they are used. -/

omit [StarOrderedRing 𝒷] in
private theorem np_add (ω : NPFunctional 𝒷) (a b : 𝒷) : ω (a + b) = ω a + ω b :=
  map_add ω.toPositiveLinearMap a b

omit [StarOrderedRing 𝒷] in
private theorem np_smul (ω : NPFunctional 𝒷) (c : ℂ) (a : 𝒷) : ω (c • a) = c * ω a :=
  map_smul ω.toPositiveLinearMap c a

omit [StarOrderedRing 𝒷] in
private theorem np_sub (ω : NPFunctional 𝒷) (a b : 𝒷) : ω (a - b) = ω a - ω b :=
  map_sub ω.toPositiveLinearMap a b

private theorem np_star (ω : NPFunctional 𝒷) (a : 𝒷) :
    ω (star a) = starRingEnd ℂ (ω a) :=
  map_star ω.toPositiveLinearMap a

omit [StarOrderedRing 𝒷] in
private theorem np_nonneg (ω : NPFunctional 𝒷) {a : 𝒷} (ha : 0 ≤ a) :
    (0 : ℂ) ≤ ω a := by
  have h : ω.toPositiveLinearMap 0 ≤ ω.toPositiveLinearMap a :=
    ω.toPositiveLinearMap.monotone ha
  rwa [map_zero] at h

omit [StarOrderedRing 𝒷] in
private theorem np_re_nonneg (ω : NPFunctional 𝒷) {a : 𝒷} (ha : 0 ≤ a) :
    0 ≤ (ω a).re := by
  simpa using (Complex.le_def.mp (np_nonneg ω ha)).1

omit [StarOrderedRing 𝒷] in
private theorem np_im_zero (ω : NPFunctional 𝒷) {a : 𝒷} (ha : 0 ≤ a) :
    (ω a).im = 0 := by
  simpa using ((Complex.le_def.mp (np_nonneg ω ha)).2).symm

omit [StarOrderedRing 𝒷] in
private theorem np_re_mono (ω : NPFunctional 𝒷) {a b : 𝒷} (h : a ≤ b) :
    (ω a).re ≤ (ω b).re :=
  (Complex.le_def.mp (ω.toPositiveLinearMap.monotone h)).1

omit [StarOrderedRing 𝒷] in
private theorem np_re_smul (ω : NPFunctional 𝒷) (r : ℝ) (a : 𝒷) :
    (ω (r • a)).re = r * (ω a).re := by
  rw [show (r • a) = ((r : ℝ) : ℂ) • a from (RCLike.real_smul_eq_coe_smul (K := ℂ) r a),
    np_smul]
  simp

omit [StarOrderedRing 𝒷] [Module ℂ X] [SMul 𝒷 X] in
theorem unSeminorm_nonneg (ω : NPFunctional 𝒷) (B : X → X → 𝒷) (x : X) :
    0 ≤ unSeminorm ω B x := Real.sqrt_nonneg _

theorem unSeminorm_sq (ω : NPFunctional 𝒷) (B : BInner 𝒷 X) (x : X) :
    unSeminorm ω B.inner x ^ 2 = (ω (B.inner x x)).re :=
  Real.sq_sqrt (np_re_nonneg ω (B.inner_self_nonneg x))

/-- The complex inner product `⟨x,y⟩_ω = ω[x,y]` of **142II** at an
np-functional, as `innerFCore` — the bridge that lets the ultranorm
seminorms use 142II's own conclusion. -/
private noncomputable def unInnerCore (ω : NPFunctional 𝒷) (B : BInner 𝒷 X) :
    PreInnerProductSpace.Core ℂ X :=
  innerFCore ω.toPositiveLinearMap.toLinearMap
    (fun _ ha => npFunctional_nonneg ω ha) B

/-- Cauchy–Schwarz for `‖·‖_ω`: `|ω[x,y]| ≤ ‖x‖_ω ‖y‖_ω`.

`⟨·,·⟩_ω` is a complex-valued inner product — that is **142II**'s embedded
claim, `innerFCore` — and `‖·‖_ω` is its `seminormF`, so this is cstar.tex
**4XV**.1 `inner_product_basic_1` verbatim. -/
theorem unSeminorm_inner_le (ω : NPFunctional 𝒷) (B : BInner 𝒷 X) (x y : X) :
    ‖ω (B.inner x y)‖ ≤ unSeminorm ω B.inner x * unSeminorm ω B.inner y := by
  letI : PreInnerProductSpace.Core ℂ X := unInnerCore ω B
  have h := Theses.A.CStar.inner_product_basic_1 (V := X) x y
  have hx : Theses.A.CStar.innerNorm (V := X) x = unSeminorm ω B.inner x := rfl
  have hy : Theses.A.CStar.innerNorm (V := X) y = unSeminorm ω B.inner y := rfl
  rw [← Theses.A.CStar.innerNorm_sq (V := X) x,
    ← Theses.A.CStar.innerNorm_sq (V := X) y, hx, hy] at h
  have hcs : ‖ω (B.inner x y)‖ ^ 2
      ≤ unSeminorm ω B.inner x ^ 2 * unSeminorm ω B.inner y ^ 2 := h
  have hnx : 0 ≤ unSeminorm ω B.inner x := unSeminorm_nonneg ω B.inner x
  have hny : 0 ≤ unSeminorm ω B.inner y := unSeminorm_nonneg ω B.inner y
  nlinarith [norm_nonneg (ω (B.inner x y)), mul_nonneg hnx hny]

/-- The triangle inequality for `‖·‖_ω` — the *conclusion* of **142II**
(`seminormF_seminorm`), read at the np-functional `ω`. -/
theorem unSeminorm_add_le (ω : NPFunctional 𝒷) (B : BInner 𝒷 X) (x y : X) :
    unSeminorm ω B.inner (x + y)
      ≤ unSeminorm ω B.inner x + unSeminorm ω B.inner y :=
  (seminormF_seminorm ω.toPositiveLinearMap.toLinearMap
    (fun _ ha => npFunctional_nonneg ω ha) B x y 1).2.2

/-- The seminorm form of **144V** (`blinear-inprod-inequality`), which is
what the proof of **148I** below computes: applying an np-functional `ω` to
`[Tx,Tx] ≤ C²[x,x]` gives `‖Tx‖_ω ≤ C ‖x‖_ω`. -/
theorem unSeminorm_boundedModuleMap_le (B₁ : BInner 𝒷 X) (B₂ : BInner 𝒷 Y)
    (C : ℝ) (hC : 0 ≤ C) (T : X → Y) (hT : IsBoundedModuleMap B₁ B₂ C T)
    (ω : NPFunctional 𝒷) (x : X) :
    unSeminorm ω B₂.inner (T x) ≤ C * unSeminorm ω B₁.inner x := by
  have h144 := blinear_inprod_inequality B₁ B₂ C hC T hT x
  have hmono := ω.toPositiveLinearMap.monotone h144
  have hre : (ω (B₂.inner (T x) (T x))).re ≤ (ω ((C ^ 2) • B₁.inner x x)).re :=
    (Complex.le_def.mp hmono).1
  have hsmul : (ω ((C ^ 2) • B₁.inner x x)).re
      = C ^ 2 * (ω (B₁.inner x x)).re := by
    rw [show ((C ^ 2 : ℝ) • B₁.inner x x) = ((C ^ 2 : ℝ) : ℂ) • B₁.inner x x from
      (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _), np_smul]
    simp [-Complex.ofReal_pow]
  rw [hsmul] at hre
  rw [unSeminorm, unSeminorm]
  calc Real.sqrt (ω (B₂.inner (T x) (T x))).re
      ≤ Real.sqrt (C ^ 2 * (ω (B₁.inner x x)).re) := Real.sqrt_le_sqrt hre
    _ = C * Real.sqrt (ω (B₁.inner x x)).re := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]

/-- **148I** (`blinear-bounded-is-ultranorm`, dils.tex:2049, Proposition):
a bounded 𝒷-linear map `T : X → Y` between 𝒷-modules with 𝒷-valued inner
products is uniformly ultranorm continuous: for every `ω` and `ε > 0` there
is `δ > 0` with `‖x-y‖_ω ≤ δ ⟹ ‖Tx-Ty‖_ω ≤ ε`.

**148II** is the proof — not converted. -/
theorem blinear_bounded_is_ultranorm (B₁ : BInner 𝒷 X) (B₂ : BInner 𝒷 Y)
    (C : ℝ) (T : X → Y) (hT : IsBoundedModuleMap B₁ B₂ C T)
    (ω : NPFunctional 𝒷) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ x y : X, unSeminorm ω B₁.inner (x - y) ≤ δ →
      unSeminorm ω B₂.inner (T x - T y) ≤ ε := by
  set C' := max C 0 with hC'
  have hC'0 : (0 : ℝ) ≤ C' := le_max_right _ _
  have hT' : IsBoundedModuleMap B₁ B₂ C' T :=
    { hT with
      bound := fun x => (hT.bound x).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) }
  refine ⟨ε / (C' + 1), by positivity, fun x y hxy => ?_⟩
  have hTsub : T x - T y = T (x - y) := by
    have h := hT.add (x - y) y
    rw [sub_add_cancel] at h
    rw [h]; abel
  have hkey : unSeminorm ω B₂.inner (T (x - y)) ≤ C' * unSeminorm ω B₁.inner (x - y) := by
    have h144 := blinear_inprod_inequality B₁ B₂ C' hC'0 T hT' (x - y)
    have hmono := ω.toPositiveLinearMap.monotone h144
    have hre : (ω (B₂.inner (T (x - y)) (T (x - y)))).re
        ≤ (ω ((C' ^ 2) • B₁.inner (x - y) (x - y))).re := (Complex.le_def.mp hmono).1
    have hlin : ∀ (c : ℂ) (a : 𝒷), ω (c • a) = c * ω a := fun c a =>
      map_smul ω.toPositiveLinearMap c a
    have hsmul : (ω ((C' ^ 2) • B₁.inner (x - y) (x - y))).re
        = C' ^ 2 * (ω (B₁.inner (x - y) (x - y))).re := by
      rw [show ((C' ^ 2 : ℝ) • B₁.inner (x - y) (x - y))
          = ((C' ^ 2 : ℝ) : ℂ) • B₁.inner (x - y) (x - y) from
        (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _), hlin]
      simp [-Complex.ofReal_pow]
    rw [hsmul] at hre
    rw [unSeminorm, unSeminorm]
    calc Real.sqrt (ω (B₂.inner (T (x - y)) (T (x - y)))).re
        ≤ Real.sqrt (C' ^ 2 * (ω (B₁.inner (x - y) (x - y))).re) := Real.sqrt_le_sqrt hre
      _ = C' * Real.sqrt (ω (B₁.inner (x - y) (x - y))).re := by
          rw [Real.sqrt_mul (sq_nonneg C'), Real.sqrt_sq hC'0]
  rw [hTsub]
  calc unSeminorm ω B₂.inner (T (x - y)) ≤ C' * unSeminorm ω B₁.inner (x - y) := hkey
    _ ≤ C' * (ε / (C' + 1)) := by
        have : (0:ℝ) ≤ unSeminorm ω B₁.inner (x - y) := Real.sqrt_nonneg _
        nlinarith
    _ ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith

/-! ### **148III**: the three module operations are *uniformly* continuous

The Corollary asserts uniform continuity — which is what **150IX** then uses
to extend the operations to `V̄` — so that is what the three declarations
below state, in the same shape as **148I**: for each np-functional `ω` and
each `ε > 0` there is a `δ > 0` that works *uniformly* in the arguments.
(As in 148I one np-functional at a time suffices, because each of the three
estimates goes through a single seminorm.)

The Corollary is a corollary of **148I**: each of the three maps is a
bounded 𝒷-linear map, and the bound is the content of the two estimates
below — Cauchy–Schwarz (**142III**) for `x ↦ [x₀,x]`, and the conjugation
bound for `b ↦ x₀·b` (mirrored `b ↦ b • x₀`), the map for which no bounded
𝒷-linear packaging is available here because `SMul 𝒷 X` carries no module
axioms.  Limit preservation, the weaker form, follows and is recorded
afterwards as `ultranormcontstruct_*_unTendsto`.

**Dead limb, recorded 2026-08-26.**  All six declarations of this
sub-section have *no consumer anywhere in* `Theses/`.  The reason is
structural and already deliberate: 148III's consumer in dils.tex is
**150IX**, which extends the operations to `V̄`, and 150IX–150V are
deliberately not transcribed (`B/Dils/SelfDualCompletion` takes `V̄` to be
Mathlib's `UniformSpace.Completion`, whose functorial extension supplies
that step).  The thesis's other citations of `ultranormcontstruct`
(dils.tex:2440, 2469, 2487, 4520, 4528, 5165, 5358) all land on proofs
whose Lean forms phrase ultranorm closure through the entourage predicate
`unClosure` rather than through nets, and so use the underlying estimates —
`unSeminorm_add_le` (**142II**, 27 call sites), `unSeminorm_inner_le`,
`unSeminorm_boundedModuleMap_le` — directly.  Restoring the citations would
mean re-phrasing those proofs in terms of nets, which is a change of
formulation, not of argument, so this is recorded and not repaired. -/

/-- The estimate behind **148III** part 2, by Cauchy–Schwarz (**142III**):
`‖[x₀,d]‖_ω ≤ ‖[x₀,x₀]‖^½ ‖d‖_ω`, the mirrored ultrastrong seminorm on the
left. -/
theorem unSeminorm_inner_left_le (B : BInner 𝒷 X) (ω : NPFunctional 𝒷)
    (x₀ d : X) :
    unSeminorm ω (mulInner 𝒷) (B.inner x₀ d)
      ≤ Real.sqrt ‖B.inner x₀ x₀‖ * unSeminorm ω B.inner d := by
  have hmul : mulInner 𝒷 (B.inner x₀ d) (B.inner x₀ d)
      = B.inner x₀ d * B.inner d x₀ := by
    show B.inner x₀ d * star (B.inner x₀ d) = _
    rw [B.star_inner]
  have hCS := module_CS B d x₀
  have hre : (ω (mulInner 𝒷 (B.inner x₀ d) (B.inner x₀ d))).re
      ≤ ‖B.inner x₀ x₀‖ * (ω (B.inner d d)).re := by
    rw [hmul, ← np_re_smul]
    exact np_re_mono ω hCS
  rw [unSeminorm, unSeminorm]
  calc Real.sqrt (ω (mulInner 𝒷 (B.inner x₀ d) (B.inner x₀ d))).re
      ≤ Real.sqrt (‖B.inner x₀ x₀‖ * (ω (B.inner d d)).re) := Real.sqrt_le_sqrt hre
    _ = _ := Real.sqrt_mul (norm_nonneg _) _

/-- The estimate behind **148III** part 3:
`‖x₀·b − x₀·c‖_ω ≤ ‖[x₀,x₀]‖^½ ‖b − c‖_ω` (mirrored), from the conjugation
bound `d [x₀,x₀] d* ≤ ‖[x₀,x₀]‖ d d*`. -/
theorem unSeminorm_op_smul_right_le (B : BInner 𝒷 X) (ω : NPFunctional 𝒷)
    (x₀ : X) (b c : 𝒷) :
    unSeminorm ω B.inner (b • x₀ - c • x₀)
      ≤ Real.sqrt ‖B.inner x₀ x₀‖ * unSeminorm ω (mulInner 𝒷) (b - c) := by
  have hexp : B.inner (b • x₀ - c • x₀) (b • x₀ - c • x₀)
      = (b - c) * B.inner x₀ x₀ * star (b - c) := by
    simp only [B.inner_sub_left, B.inner_sub_right, B.inner_op_smul_left,
      B.inner_op_smul_right, star_sub, sub_mul, mul_sub, mul_assoc]
  have hsa : IsSelfAdjoint (B.inner x₀ x₀) := B.star_inner x₀ x₀
  have hconj : (b - c) * B.inner x₀ x₀ * star (b - c)
      ≤ ‖B.inner x₀ x₀‖ • ((b - c) * star (b - c)) :=
    CStarAlgebra.star_right_conjugate_le_norm_smul hsa
  have hre : (ω (B.inner (b • x₀ - c • x₀) (b • x₀ - c • x₀))).re
      ≤ ‖B.inner x₀ x₀‖ * (ω (mulInner 𝒷 (b - c) (b - c))).re := by
    rw [hexp, ← np_re_smul]
    exact np_re_mono ω hconj
  rw [unSeminorm, unSeminorm]
  calc Real.sqrt (ω (B.inner (b • x₀ - c • x₀) (b • x₀ - c • x₀))).re
      ≤ Real.sqrt (‖B.inner x₀ x₀‖ * (ω (mulInner 𝒷 (b - c) (b - c))).re) :=
        Real.sqrt_le_sqrt hre
    _ = _ := Real.sqrt_mul (norm_nonneg _) _

/-- **148III** (`ultranormcontstruct`, dils.tex:2068, Corollary), part 1:
`(x,y) ↦ x + y : X × X → X` is **uniformly** continuous for the ultranorm
uniformity (the product uniformity on `X × X` being the one of **147III**,
whose subbase relations are the two coordinatewise ones — hence the two
hypotheses below). -/
theorem ultranormcontstruct_add (B : BInner 𝒷 X) (ω : NPFunctional 𝒷)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ x y x' y' : X,
      unSeminorm ω B.inner (x - x') ≤ δ → unSeminorm ω B.inner (y - y') ≤ δ →
        unSeminorm ω B.inner (x + y - (x' + y')) ≤ ε := by
  refine ⟨ε / 2, by positivity, fun x y x' y' hx hy => ?_⟩
  rw [show x + y - (x' + y') = (x - x') + (y - y') by abel]
  calc unSeminorm ω B.inner ((x - x') + (y - y'))
      ≤ unSeminorm ω B.inner (x - x') + unSeminorm ω B.inner (y - y') :=
        unSeminorm_add_le ω B _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hx hy
    _ = ε := by ring

/-- **148III** (`ultranormcontstruct`, dils.tex:2068, Corollary), part 2:
for fixed `x₀`, the map `x ↦ [x₀, x] : X → 𝒷` is **uniformly** continuous
from the ultranorm uniformity of `X` to the ultrastrong uniformity of `𝒷`
(the ultranorm uniformity of `mulInner`). -/
theorem ultranormcontstruct_inner [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 X)
    (x₀ : X) (ω : NPFunctional 𝒷) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ x y : X, unSeminorm ω B.inner (x - y) ≤ δ →
      unSeminorm ω (mulInner 𝒷) (B.inner x₀ x - B.inner x₀ y) ≤ ε := by
  set K : ℝ := Real.sqrt ‖B.inner x₀ x₀‖ with hK
  have hK0 : (0 : ℝ) ≤ K := Real.sqrt_nonneg _
  refine ⟨ε / (K + 1), by positivity, fun x y hxy => ?_⟩
  rw [(B.inner_sub_right x₀ x y).symm]
  calc unSeminorm ω (mulInner 𝒷) (B.inner x₀ (x - y))
      ≤ K * unSeminorm ω B.inner (x - y) := unSeminorm_inner_left_le B ω x₀ (x - y)
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hxy hK0
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

/-- **148III** (`ultranormcontstruct`, dils.tex:2068, Corollary), part 3:
for fixed `x₀`, the map `b ↦ x₀ · b : 𝒷 → X` (mirrored: `b • x₀`) is
**uniformly** continuous from the ultrastrong uniformity of `𝒷` to the
ultranorm uniformity of `X`. -/
theorem ultranormcontstruct_smul [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 X)
    (x₀ : X) (ω : NPFunctional 𝒷) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ b c : 𝒷, unSeminorm ω (mulInner 𝒷) (b - c) ≤ δ →
      unSeminorm ω B.inner (b • x₀ - c • x₀) ≤ ε := by
  set K : ℝ := Real.sqrt ‖B.inner x₀ x₀‖ with hK
  have hK0 : (0 : ℝ) ≤ K := Real.sqrt_nonneg _
  refine ⟨ε / (K + 1), by positivity, fun b c hbc => ?_⟩
  calc unSeminorm ω B.inner (b • x₀ - c • x₀)
      ≤ K * unSeminorm ω (mulInner 𝒷) (b - c) :=
        unSeminorm_op_smul_right_le B ω x₀ b c
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hbc hK0
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

variable {ι : Type w} {l : Filter ι}

/-- **148III**, part 1, in the weaker net form: addition preserves
ultranorm limits.  (A corollary of `ultranormcontstruct_add`.  The claim
that used to stand here — "kept because it is the form the net arguments of
parsec 1490 use" — is **false**: parsec 1490's Lean proofs go through
`unSeminorm_add_le` and `unSeminorm_inner_le` directly, and this form has no
consumer.  See the sub-section note above.) -/
theorem ultranormcontstruct_add_unTendsto (B : BInner 𝒷 X) (x y : ι → X)
    (x₀ y₀ : X) (hx : UnTendsto B.inner x l x₀) (hy : UnTendsto B.inner y l y₀) :
    UnTendsto B.inner (fun i => x i + y i) l (x₀ + y₀) := by
  intro ω
  refine squeeze_zero (fun i => unSeminorm_nonneg ω B.inner _) (g := fun i =>
    unSeminorm ω B.inner (x i - x₀) + unSeminorm ω B.inner (y i - y₀)) (fun i => ?_) ?_
  · have hrw : x i + y i - (x₀ + y₀) = (x i - x₀) + (y i - y₀) := by abel
    rw [hrw]
    exact unSeminorm_add_le ω B _ _
  · simpa using (hx ω).add (hy ω)

/-- **148III**, part 2, in the weaker net form: `x ↦ [x₀,x]` preserves
ultranorm limits. -/
theorem ultranormcontstruct_inner_unTendsto [VonNeumannAlgebra 𝒷]
    (B : BInner 𝒷 X) (x₀ : X) (x : ι → X) (xlim : X)
    (hx : UnTendsto B.inner x l xlim) :
    UnTendsto (mulInner 𝒷) (fun i => B.inner x₀ (x i)) l (B.inner x₀ xlim) := by
  intro ω
  refine squeeze_zero (fun i => unSeminorm_nonneg ω (mulInner 𝒷) _) (g := fun i =>
    Real.sqrt ‖B.inner x₀ x₀‖ * unSeminorm ω B.inner (x i - xlim)) (fun i => ?_) ?_
  · rw [(B.inner_sub_right x₀ (x i) xlim).symm]
    exact unSeminorm_inner_left_le B ω x₀ (x i - xlim)
  · simpa using (hx ω).const_mul (Real.sqrt ‖B.inner x₀ x₀‖)

/-- **148III**, part 3, in the weaker net form: `b ↦ x₀ · b` (mirrored:
`b • x₀`) preserves ultrastrong limits. -/
theorem ultranormcontstruct_smul_unTendsto [VonNeumannAlgebra 𝒷]
    (B : BInner 𝒷 X) (x₀ : X) (b : ι → 𝒷) (blim : 𝒷)
    (hb : UnTendsto (mulInner 𝒷) b l blim) :
    UnTendsto B.inner (fun i => b i • x₀) l (blim • x₀) := by
  intro ω
  refine squeeze_zero (fun i => unSeminorm_nonneg ω B.inner _) (g := fun i =>
    Real.sqrt ‖B.inner x₀ x₀‖ * unSeminorm ω (mulInner 𝒷) (b i - blim)) (fun i => ?_) ?_
  · exact unSeminorm_op_smul_right_le B ω x₀ (b i) blim
  · simpa using (hb ω).const_mul (Real.sqrt ‖B.inner x₀ x₀‖)

/-- **148IV** (`ultranormscalar`, dils.tex:2080, Exercise): for fixed
`b ∈ 𝒷`, the map `x ↦ x·b` (mirrored: `b • x`) is ultranorm continuous:
it preserves ultranorm limits. -/
theorem ultranormscalar [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 X) (b : 𝒷)
    (x : ι → X) (xlim : X) (hx : UnTendsto B.inner x l xlim) :
    UnTendsto B.inner (fun i => b • x i) l (b • xlim) := by
  intro ω
  have key : ∀ i, unSeminorm ω B.inner (b • x i - b • xlim)
      = unSeminorm (conjNP (star b) ω) B.inner (x i - xlim) := by
    intro i
    have hexp : B.inner (b • x i - b • xlim) (b • x i - b • xlim)
        = star (star b) * B.inner (x i - xlim) (x i - xlim) * star b := by
      simp only [B.inner_sub_left, B.inner_sub_right, B.inner_op_smul_left,
        B.inner_op_smul_right, star_star, sub_mul, mul_sub, mul_assoc]
    rw [unSeminorm, unSeminorm, hexp, ← conjNP_apply (star b) ω]
  simpa only [key] using hx (conjNP (star b) ω)

/-- **148V** (`innerprod-ultraweak`, dils.tex:2086, Proposition): if
`x_α → x` and `y_α → y` in the ultranorm uniformity, then
`[x_α, y_α] → [x, y]` ultraweakly.

**148VI** is the proof — not converted. -/
theorem innerprod_ultraweak (B : BInner 𝒷 X) (x y : ι → X) (xlim ylim : X)
    (hx : UnTendsto B.inner x l xlim) (hy : UnTendsto B.inner y l ylim) :
    UWTendsto (fun i => B.inner (x i) (y i)) l (B.inner xlim ylim) := by
  rw [uwTendsto_iff]
  intro ω
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (a := fun i =>
    unSeminorm ω B.inner (x i - xlim)
        * (unSeminorm ω B.inner ylim + unSeminorm ω B.inner (y i - ylim))
      + unSeminorm ω B.inner xlim * unSeminorm ω B.inner (y i - ylim)) (fun i => ?_) ?_
  · have hsplit : B.inner (x i) (y i) - B.inner xlim ylim
        = B.inner (x i - xlim) (y i) + B.inner xlim (y i - ylim) := by
      rw [B.inner_sub_left, B.inner_sub_right]
      abel
    have hy' : unSeminorm ω B.inner (y i)
        ≤ unSeminorm ω B.inner ylim + unSeminorm ω B.inner (y i - ylim) := by
      have hrw : y i = ylim + (y i - ylim) := by abel
      calc unSeminorm ω B.inner (y i)
          = unSeminorm ω B.inner (ylim + (y i - ylim)) := by rw [← hrw]
        _ ≤ _ := unSeminorm_add_le ω B _ _
    calc ‖ω (B.inner (x i) (y i)) - ω (B.inner xlim ylim)‖
        = ‖ω (B.inner (x i - xlim) (y i)) + ω (B.inner xlim (y i - ylim))‖ := by
          rw [← np_add, ← hsplit, np_sub]
      _ ≤ ‖ω (B.inner (x i - xlim) (y i))‖ + ‖ω (B.inner xlim (y i - ylim))‖ :=
          norm_add_le _ _
      _ ≤ unSeminorm ω B.inner (x i - xlim) * unSeminorm ω B.inner (y i)
            + unSeminorm ω B.inner xlim * unSeminorm ω B.inner (y i - ylim) :=
          add_le_add (unSeminorm_inner_le ω B _ _) (unSeminorm_inner_le ω B _ _)
      _ ≤ _ := by
          have h1 := unSeminorm_nonneg ω B.inner (x i - xlim)
          nlinarith [unSeminorm_nonneg ω B.inner (y i)]
  · have h0 : Tendsto (fun i => unSeminorm ω B.inner (x i - xlim)
        * (unSeminorm ω B.inner ylim + unSeminorm ω B.inner (y i - ylim))
      + unSeminorm ω B.inner xlim * unSeminorm ω B.inner (y i - ylim)) l
        (𝓝 (0 * (unSeminorm ω B.inner ylim + 0) + unSeminorm ω B.inner xlim * 0)) :=
      ((hx ω).mul (tendsto_const_nhds.add (hy ω))).add (tendsto_const_nhds.mul (hy ω))
    simpa using h0

end UltranormContinuity

section DenseOrderSep

variable {𝒷 : Type u} {X : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]

set_option maxHeartbeats 1000000 in
/-- The analytic core of **148VII**: if the vector states coming from an
ultranorm-dense subset `D` are nonnegative on a bounded 𝒷-linear `T`, then
*every* vector state of `T` is.  This is **148I**/**148VI** (ultranorm
continuity of `x ↦ ⟨x,Tx⟩`) followed by order separation of the
np-functionals, **44XI** (`Theses.A.VN.nonneg_of_conjNP`), and needs `𝒷` to
be a von Neumann algebra — as does the ultranorm uniformity itself
(**146VII**, dils.tex:1897).  Together with **144I** this gives **148VII**
below. -/
theorem unDense_inner_nonneg [VonNeumannAlgebra 𝒷] (D : Set X)
    (hD : UnDense (inner 𝒷) D) (T : X →L[ℂ] X)
    (hTmod : ∀ (a : 𝒷) (x : X), T (a • x) = a • T x)
    (hDpos : ∀ x ∈ D, 0 ≤ inner 𝒷 x (T x)) (x : X) :
    0 ≤ inner 𝒷 x (T x) := by
  letI : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  set C : ℝ := ‖T‖ + 1 with hC
  have hC0 : (0 : ℝ) ≤ C := by positivity
  have hbdd : IsBoundedModuleMap (cstarBInner 𝒷 X) (cstarBInner 𝒷 X) C ⇑T :=
    { add := fun x y => map_add T x y
      smul_complex := fun c x => map_smul T c x
      smul := hTmod
      bound := fun x => by
        change Real.sqrt ‖(inner 𝒷 (T x) (T x) : 𝒷)‖
          ≤ C * Real.sqrt ‖(inner 𝒷 x x : 𝒷)‖
        rw [← CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷),
          ← CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷)]
        have := T.le_opNorm x
        have h0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
        nlinarith }
  have hTsem : ∀ (ω : NPFunctional 𝒷) (z : X),
      unSeminorm ω (inner 𝒷) (T z) ≤ C * unSeminorm ω (inner 𝒷) z := fun ω z =>
    unSeminorm_boundedModuleMap_le _ _ C hC0 _ hbdd ω z
  -- every np-functional is nonnegative on every vector state of `T`
  have hall : ∀ (y : X) (ω : NPFunctional 𝒷),
      (0 : ℂ) ≤ ω (inner 𝒷 y (T y)) := by
    intro y ω
    set M : ℝ := unSeminorm ω (inner 𝒷) y with hM
    set N : ℝ := unSeminorm ω (inner 𝒷) (T y) with hN
    have hM0 : (0 : ℝ) ≤ M := unSeminorm_nonneg _ _ _
    have hN0 : (0 : ℝ) ≤ N := unSeminorm_nonneg _ _ _
    set K : ℝ := N + (M + 1) * C + 1 with hKdef
    have hK : (0 : ℝ) < K := by nlinarith
    -- approximate `⟨y,Ty⟩` by a vector state coming from `V`
    have key : ∀ ε : ℝ, 0 < ε → ∃ z : ℂ, 0 ≤ z ∧
        ‖(ω (inner 𝒷 y (T y)) : ℂ) - z‖ ≤ ε * K := by
      intro ε hε
      set ε' : ℝ := min ε 1 with hε'
      have hε'0 : 0 < ε' := lt_min hε one_pos
      obtain ⟨d, hdD, hd⟩ := hD y 1 (fun _ => ω) ε' hε'0
      have ht : unSeminorm ω (inner 𝒷) (y - d) ≤ ε' := hd 0
      have ht0 : (0 : ℝ) ≤ unSeminorm ω (inner 𝒷) (y - d) :=
        unSeminorm_nonneg _ _ _
      refine ⟨ω (inner 𝒷 (d) (T (d))), npFunctional_nonneg ω (hDpos d hdD), ?_⟩
      have hsplit : (inner 𝒷 y (T y) : 𝒷)
          = inner 𝒷 (y - d) (T y) + inner 𝒷 (d) (T (y - d))
            + inner 𝒷 (d) (T (d)) := by
        rw [map_sub T, CStarModule.inner_sub_right, CStarModule.inner_sub_left]
        abel
      have hadd1 : ω (inner 𝒷 (y - d) (T y) + inner 𝒷 (d) (T (y - d))
            + inner 𝒷 (d) (T (d)))
          = ω (inner 𝒷 (y - d) (T y) + inner 𝒷 (d) (T (y - d)))
            + ω (inner 𝒷 (d) (T (d))) :=
        map_add ω.toPositiveLinearMap _ _
      have hadd2 : ω (inner 𝒷 (y - d) (T y)
            + inner 𝒷 (d) (T (y - d)))
          = ω (inner 𝒷 (y - d) (T y))
            + ω (inner 𝒷 (d) (T (y - d))) :=
        map_add ω.toPositiveLinearMap _ _
      rw [hsplit, hadd1, add_sub_cancel_right, hadd2]
      have hcs1 : ‖ω (inner 𝒷 (y - d) (T y))‖
          ≤ unSeminorm ω (inner 𝒷) (y - d) * N :=
        unSeminorm_inner_le ω (cstarBInner 𝒷 X) _ _
      have hdM : unSeminorm ω (inner 𝒷) (d) ≤ M + ε' := by
        have htri := unSeminorm_add_le ω (cstarBInner 𝒷 X) y (d - y)
        simp only [show (cstarBInner 𝒷 X).inner = (inner 𝒷 : X → X → 𝒷)
          from rfl, add_sub_cancel] at htri
        have hneg : d - y = -(y - d) := by abel
        have hsymm : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (d - y)
            = unSeminorm ω (inner 𝒷) (y - d) := by
          rw [unSeminorm, unSeminorm, hneg, CStarModule.inner_neg_left,
            CStarModule.inner_neg_right, neg_neg]
        rw [hsymm] at htri
        linarith [ht]
      have hcs2 : ‖ω (inner 𝒷 (d) (T (y - d)))‖
          ≤ unSeminorm ω (inner 𝒷) (d)
              * (C * unSeminorm ω (inner 𝒷) (y - d)) := by
        refine (unSeminorm_inner_le ω (cstarBInner 𝒷 X) _ _).trans ?_
        exact mul_le_mul_of_nonneg_left (hTsem ω _) (unSeminorm_nonneg _ _ _)
      have hεle : ε' ≤ ε := min_le_left _ _
      have hε1 : ε' ≤ 1 := min_le_right _ _
      have hdM0 : (0 : ℝ) ≤ unSeminorm ω (inner 𝒷) (d) := unSeminorm_nonneg _ _ _
      have htε : unSeminorm ω (inner 𝒷) (y - d) ≤ ε := ht.trans hεle
      have h1 : ‖ω (inner 𝒷 (y - d) (T y))‖ ≤ ε * N :=
        hcs1.trans (mul_le_mul_of_nonneg_right htε hN0)
      have h2 : ‖ω (inner 𝒷 (d) (T (y - d)))‖ ≤ ε * ((M + 1) * C) := by
        refine hcs2.trans ?_
        have hD : unSeminorm ω (inner 𝒷) (d) ≤ M + 1 := by linarith
        have hCt : C * unSeminorm ω (inner 𝒷) (y - d) ≤ C * ε :=
          mul_le_mul_of_nonneg_left htε hC0
        calc unSeminorm ω (inner 𝒷) (d)
              * (C * unSeminorm ω (inner 𝒷) (y - d))
            ≤ (M + 1) * (C * unSeminorm ω (inner 𝒷) (y - d)) :=
              mul_le_mul_of_nonneg_right hD (by positivity)
          _ ≤ (M + 1) * (C * ε) := mul_le_mul_of_nonneg_left hCt (by linarith)
          _ = ε * ((M + 1) * C) := by ring
      have hεK : ε * N + ε * ((M + 1) * C) ≤ ε * K := by
        rw [hKdef]; nlinarith
      calc ‖ω (inner 𝒷 (y - d) (T y)) + ω (inner 𝒷 (d) (T (y - d)))‖
          ≤ ‖ω (inner 𝒷 (y - d) (T y))‖
              + ‖ω (inner 𝒷 (d) (T (y - d)))‖ := norm_add_le _ _
        _ ≤ ε * K := by linarith
    -- let `ε ↓ 0`
    set z : ℂ := ω (inner 𝒷 y (T y)) with hz
    have hbound : ∀ ε : ℝ, 0 < ε → |z.im| ≤ ε * K ∧ -(ε * K) ≤ z.re := by
      intro ε hε
      obtain ⟨w, hw, hwe⟩ := key ε hε
      have hwre : 0 ≤ w.re := (Complex.le_def.mp hw).1
      have hwim : w.im = 0 := (Complex.le_def.mp hw).2.symm
      have hre : |(z - w).re| ≤ ‖z - w‖ := Complex.abs_re_le_norm _
      have him : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
      simp only [Complex.sub_re, Complex.sub_im, hwim, sub_zero] at hre him
      constructor
      · linarith [him, hwe]
      · have := abs_le.mp (hre.trans hwe)
        linarith [this.1, hwre]
    have him0 : z.im = 0 := by
      by_contra hne
      have hpos : 0 < |z.im| := abs_pos.mpr hne
      have := (hbound (|z.im| / (2 * K)) (by positivity)).1
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
      nlinarith
    have hre0 : 0 ≤ z.re := by
      by_contra hne
      have hlt : z.re < 0 := lt_of_not_ge hne
      have hpos : 0 < -z.re := by linarith
      have h := neg_le.mp
        (hbound (-z.re / (2 * K)) (div_pos hpos (by positivity))).2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h
      nlinarith
    exact Complex.le_def.mpr ⟨by simpa using hre0, by simpa using him0.symm⟩
  -- np-functionals are order separating (**44XI**)
  refine nonneg_of_conjNP fun ω c => ?_
  have hrw : star c * (inner 𝒷 x (T x) : 𝒷) * c
      = inner 𝒷 ((star c) • x) (T ((star c) • x)) := by
    rw [hTmod, CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_left,
      star_star, mul_assoc]
  rw [hrw]
  exact hall _ ω

/-- **148VII** (`hilbmod-denseordersep`, dils.tex:2124, Corollary): for a
Hilbert 𝒷-module `X` with ultranorm-dense subset `D`, the vector states
from `D` are order separating: for adjointable bounded `T`, `T ≥ 0` iff
`⟨x, Tx⟩ ≥ 0` for all `x ∈ D`.

The `[VonNeumannAlgebra 𝒷]` hypothesis is the thesis's: the ultranorm
uniformity — and hence the phrase "ultranorm-dense" in the statement — is
defined only for a von Neumann algebra `𝒷` (**146VII**, dils.tex:1897, "Let
𝒷 be a von Neumann algebra").  Order separation of `𝒷`'s np-functionals
(**44XI**) is what the proof consumes, and that is exactly the faithfulness
clause of `VonNeumannAlgebra`. -/
theorem hilbmod_denseordersep [VonNeumannAlgebra 𝒷] [CompleteSpace X] (D : Set X)
    (hD : UnDense (inner 𝒷) D) (T : X →L[ℂ] X)
    (hT : ModuleAdjointable 𝒷 ⇑T) :
    IsPositiveOp 𝒷 T ↔ ∀ x ∈ D, 0 ≤ inner 𝒷 x (T x) :=
  ⟨fun h x _ => (hilbmod_ordersep T hT).mp h x, fun h =>
    (hilbmod_ordersep T hT).mpr
      (unDense_inner_nonneg D hD T
        (moduleAdjointable_linear (𝒜 := 𝒷) ⇑T hT).2.2 h)⟩

end DenseOrderSep

/-! ## Parsec 1490: orthonormal bases and self-duality -/

section Bases

variable {𝒷 : Type u} {X : Type v} {ι : Type w}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]

variable (𝒷)

/-- **149I** (`dfn-selfdual-basis`, dils.tex:2135, Definition), part 1: a
family in a pre-Hilbert 𝒷-module is **orthogonal** when distinct members
have inner product `0`. -/
def OrthogonalFam (e : ι → X) : Prop :=
  ∀ i j : ι, i ≠ j → inner 𝒷 (e i) (e j) = 0

/-- **149I** (`dfn-selfdual-basis`, dils.tex:2135, Definition), part 2: an
orthogonal family is **orthonormal** when moreover each `⟨e,e⟩` is a
non-zero projection. -/
def OrthonormalFam (e : ι → X) : Prop :=
  OrthogonalFam 𝒷 e ∧
    ∀ i : ι, IsStarProjection (inner 𝒷 (e i) (e i)) ∧
      inner 𝒷 (e i) (e i) ≠ 0

variable (X) in
/-- **149I** (`dfn-selfdual-basis`, dils.tex:2135, Definition), part 3: a
family `(bᵢ)` in `𝒷` is **ℓ²-summable** when the partial sums of
`∑ᵢ bᵢ* bᵢ` are (norm-)bounded (mirrored: `∑ᵢ bᵢ bᵢ*`). -/
def L2Summable (b : ι → 𝒷) : Prop :=
  ∃ M : ℝ, ∀ s : Finset ι, ‖∑ i ∈ s, b i * star (b i)‖ ≤ M

/-- **149I** (`dfn-selfdual-basis`, dils.tex:2135, Definition), part 4: an
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

/-! ### Auxiliary: `𝒷` as a module over itself, and mirrored **43I**

The proof of **149V** applies **144V**/**148I** to the 𝒷-linear map
`τ : X → 𝒷` itself, so `𝒷` is needed as a `BInner`-module over itself; and it
compares the mirrored ultrastrong uniformity of `𝒷` (which is the ultranorm
uniformity of `mulInner`, **146VIII**) with the ultraweak topology. -/

variable (𝒷) in
/-- `mulInner` as a bundled `BInner`: `𝒷` as a module over itself
(**141III**). -/
def mulBInner : BInner 𝒷 𝒷 where
  inner := mulInner 𝒷
  inner_add_right _ _ _ := by simp [mulInner, add_mul]
  inner_op_smul_right _ _ _ := by simp [mulInner, mul_assoc]
  inner_smul_right_complex _ _ _ := by simp [mulInner, smul_mul_assoc]
  star_inner _ _ := by simp [mulInner]
  inner_self_nonneg _ := mul_star_self_nonneg _

@[simp] theorem mulBInner_inner : (mulBInner 𝒷).inner = mulInner 𝒷 := rfl

theorem mulBInner_norm (a : 𝒷) : (mulBInner 𝒷).norm a = ‖a‖ := by
  change Real.sqrt ‖a * star a‖ = ‖a‖
  rw [CStarRing.norm_self_mul_star]
  exact Real.sqrt_mul_self (norm_nonneg a)

theorem cstarBInner_norm (x : X) : (cstarBInner 𝒷 X).norm x = ‖x‖ :=
  (CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷) (E := X) x).symm

/-- **43I** in the mirrored form: the (mirrored) ultrastrong seminorms
dominate the ultraweak ones, `|ω(a)| ≤ ‖a*‖_ω ω(1)^½`. -/
theorem norm_np_le_unSeminorm_mulInner (ω : NPFunctional 𝒷) (a : 𝒷) :
    ‖ω a‖ ≤ unSeminorm ω (mulInner 𝒷) a * Real.sqrt (ω 1).re := by
  have h := norm_apply_le_omegaNorm ω (star a)
  have h1 : ‖ω (star a)‖ = ‖ω a‖ := by rw [np_star]; exact RCLike.norm_conj _
  have h2 : omegaNorm 𝒷 ω (star a) = unSeminorm ω (mulInner 𝒷) a := by
    rw [omegaNorm, unSeminorm, star_star]
    rfl
  rwa [h1, h2] at h

/-- **43I** in the mirrored form: (mirrored) ultrastrong convergence implies
ultraweak convergence. -/
theorem uwTendsto_of_unTendsto_mulInner {l : Filter ι} (a : ι → 𝒷) (a₀ : 𝒷)
    (h : UnTendsto (mulInner 𝒷) a l a₀) : UWTendsto a l a₀ := by
  rw [uwTendsto_iff]
  intro ω
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (a := fun i =>
    unSeminorm ω (mulInner 𝒷) (a i - a₀) * Real.sqrt (ω 1).re) (fun i => ?_) ?_
  · rw [← np_sub]
    exact norm_np_le_unSeminorm_mulInner ω _
  · simpa using (h ω).mul_const (Real.sqrt (ω 1).re)

/-- Uniqueness of ultraweak limits (**44XI**.1, `vn_positive_basic_1`). -/
private theorem uwTendsto_unique' [VonNeumannAlgebra 𝒷] {l : Filter ι} [l.NeBot]
    {f : ι → 𝒷} {a c : 𝒷} (ha : UWTendsto f l a) (hc : UWTendsto f l c) : a = c :=
  @tendsto_nhds_unique 𝒷 ι (ultraweak 𝒷) (vn_positive_basic_1 (A := 𝒷)).1
    f l a c _ ha hc

/-- **149III** (`mod-projelabs`, dils.tex:2224, Exercise): if `⟨e,e⟩` is a
projection, then `e⟨e,e⟩ = e` (mirrored: `⟨e,e⟩ • e = e`). -/
theorem mod_projelabs (e : X) (he : IsStarProjection (inner 𝒷 e e)) :
    inner 𝒷 e e • e = e := by
  set p : 𝒷 := inner 𝒷 e e with hp
  have hpp : p * p = p := he.isIdempotentElem
  have hps : star p = p := he.isSelfAdjoint
  -- `⟨pe - e, pe - e⟩ = (p-1)p(p-1) = 0`, so `pe - e = 0`
  have hzero : inner 𝒷 (p • e - e) (p • e - e) = (0 : 𝒷) := by
    simp only [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
      CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right, ← hp,
      hps, hpp, mul_zero, sub_zero]
    simp
  have := CStarModule.inner_self (A := 𝒷) (x := p • e - e) |>.mp hzero
  rwa [sub_eq_zero] at this

omit [StarOrderedRing 𝒷] in
/-- The Gram computation for a finite partial sum over an orthogonal family:
`⟨∑ eᵢbᵢ, ∑ eᵢcᵢ⟩ = ∑ bᵢ*⟨eᵢ,eᵢ⟩cᵢ` (mirrored). -/
theorem inner_sum_smul_orthogonal {e : ι → X} (he : OrthogonalFam 𝒷 e)
    (b c : ι → 𝒷) (s : Finset ι) :
    (inner 𝒷 (∑ i ∈ s, b i • e i) (∑ i ∈ s, c i • e i) : 𝒷)
      = ∑ i ∈ s, c i * inner 𝒷 (e i) (e i) * star (b i) := by
  rw [CStarModule.inner_sum_left]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [CStarModule.inner_sum_right, Finset.sum_eq_single_of_mem i hi]
  · rw [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right]
  · intro j _ hji
    rw [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
      he i j (Ne.symm hji), mul_zero, zero_mul]

omit [StarOrderedRing 𝒷] in
/-- When the coefficients are absorbed by the projections `⟨eᵢ,eᵢ⟩`, the Gram
sum collapses to `∑ bᵢ*bᵢ` (mirrored: `∑ bᵢbᵢ*`). -/
theorem inner_sum_smul_self {e : ι → X} (he : OrthogonalFam 𝒷 e) (b : ι → 𝒷)
    (hb : ∀ i, b i * inner 𝒷 (e i) (e i) = b i) (s : Finset ι) :
    (inner 𝒷 (∑ i ∈ s, b i • e i) (∑ i ∈ s, b i • e i) : 𝒷)
      = ∑ i ∈ s, b i * star (b i) := by
  rw [inner_sum_smul_orthogonal he b b s]
  exact Finset.sum_congr rfl fun i _ => by rw [hb i]

/-- The coefficients `⟨eᵢ,x⟩` of an orthonormal family are absorbed by the
projections `⟨eᵢ,eᵢ⟩` — the first step of the proof of **149IV**, used again
throughout **149V**. -/
theorem onbasis_coef_absorb {e : ι → X} (he : OrthonormalFam 𝒷 e) (x : X)
    (i : ι) : (inner 𝒷 (e i) x : 𝒷) * inner 𝒷 (e i) (e i) = inner 𝒷 (e i) x := by
  have hps : star (inner 𝒷 (e i) (e i) : 𝒷) = inner 𝒷 (e i) (e i) :=
    (he.2 i).1.isSelfAdjoint
  have h2 : (inner 𝒷 ((inner 𝒷 (e i) (e i) : 𝒷) • e i) x : 𝒷) = inner 𝒷 (e i) x := by
    rw [mod_projelabs (e i) (he.2 i).1]
  rwa [CStarModule.inner_op_smul_left, hps] at h2

/-- **Bessel's inequality** (dils.tex:2378, inside the proof of **149V**): for
an orthonormal family `(eᵢ)` and any `x`, `∑_{i∈S} ⟨x,eᵢ⟩⟨eᵢ,x⟩ ≤ ⟨x,x⟩` for
every finite `S` (mirrored: `∑_{i∈S} ⟨eᵢ,x⟩⟨x,eᵢ⟩ ≤ ⟨x,x⟩`).  It is the
positivity of `⟨x − ∑_{i∈S} eᵢ⟨eᵢ,x⟩, x − ∑_{i∈S} eᵢ⟨eᵢ,x⟩⟩`. -/
theorem mod_bessel {e : ι → X} (he : OrthonormalFam 𝒷 e) (x : X) (s : Finset ι) :
    ∑ i ∈ s, (inner 𝒷 (e i) x : 𝒷) * inner 𝒷 x (e i) ≤ inner 𝒷 x x := by
  set b : ι → 𝒷 := fun i => inner 𝒷 (e i) x with hbdef
  set P : X := ∑ i ∈ s, b i • e i with hP
  have hstar : ∀ i, star (b i) = (inner 𝒷 x (e i) : 𝒷) := fun i =>
    CStarModule.star_inner _ _
  have hPP : (inner 𝒷 P P : 𝒷) = ∑ i ∈ s, b i * star (b i) :=
    inner_sum_smul_self he.1 b (fun i => onbasis_coef_absorb he x i) s
  have hxP : (inner 𝒷 x P : 𝒷) = ∑ i ∈ s, b i * star (b i) := by
    rw [hP, CStarModule.inner_sum_right]
    exact Finset.sum_congr rfl fun i _ => by
      rw [CStarModule.inner_op_smul_right, hstar i]
  have hPx : (inner 𝒷 P x : 𝒷) = ∑ i ∈ s, b i * star (b i) := by
    have h := congrArg star hxP
    rw [CStarModule.star_inner, star_sum] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by rw [star_mul, star_star]
  have h0 : (0 : 𝒷) ≤ inner 𝒷 (x - P) (x - P) := CStarModule.inner_self_nonneg
  rw [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
    CStarModule.inner_sub_right, hPP, hxP, hPx] at h0
  have hQ : ∑ i ∈ s, b i * star (b i)
      = ∑ i ∈ s, (inner 𝒷 (e i) x : 𝒷) * inner 𝒷 x (e i) :=
    Finset.sum_congr rfl fun i _ => by rw [hstar i]
  rw [sub_self, sub_zero, hQ] at h0
  exact sub_nonneg.mp h0

/-- **149IV** (`mod-parseval`, dils.tex:2233, Exercise (Parseval's
identity)): for an orthonormal basis `(eᵢ)` of a pre-Hilbert 𝒷-module over
a von Neumann algebra, `⟨x,x⟩ = ∑ᵢ ⟨x,eᵢ⟩⟨eᵢ,x⟩`, the sum converging
ultraweakly. -/
theorem mod_parseval [VonNeumannAlgebra 𝒷] (e : ι → X)
    (he : IsONBasis 𝒷 e) (x : X) :
    UWTendsto
      (fun s : Finset ι => ∑ i ∈ s, inner 𝒷 (e i) x * inner 𝒷 x (e i))
      atTop (inner 𝒷 x x) := by
  -- `⟨eᵢ,eᵢ⟩` is a projection, so `⟨eᵢ,x⟩⟨eᵢ,eᵢ⟩ = ⟨eᵢ,x⟩`
  have hp : ∀ i, IsStarProjection (inner 𝒷 (e i) (e i) : 𝒷) := fun i => (he.1.2 i).1
  have hself : ∀ i, (inner 𝒷 (e i) x : 𝒷) * inner 𝒷 (e i) (e i)
      = inner 𝒷 (e i) x := by
    intro i
    have hps : star (inner 𝒷 (e i) (e i) : 𝒷) = inner 𝒷 (e i) (e i) :=
      (hp i).isSelfAdjoint
    have h2 : (inner 𝒷 ((inner 𝒷 (e i) (e i) : 𝒷) • e i) x : 𝒷)
        = inner 𝒷 (e i) x := by rw [mod_projelabs (e i) (hp i)]
    rwa [CStarModule.inner_op_smul_left, hps] at h2
  -- the Gram sum of the partial sums is the Parseval sum
  have hkey : ∀ s : Finset ι,
      (inner 𝒷 (∑ i ∈ s, (inner 𝒷 (e i) x : 𝒷) • e i)
          (∑ i ∈ s, (inner 𝒷 (e i) x : 𝒷) • e i) : 𝒷)
        = ∑ i ∈ s, (inner 𝒷 (e i) x : 𝒷) * inner 𝒷 x (e i) := by
    intro s
    rw [CStarModule.inner_sum_left]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [CStarModule.inner_sum_right, Finset.sum_eq_single_of_mem i hi]
    · rw [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
        hself i, CStarModule.star_inner]
    · intro j _ hji
      rw [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
        he.1.1 i j (Ne.symm hji), mul_zero, zero_mul]
  have h := innerprod_ultraweak (cstarBInner 𝒷 X)
    (fun s : Finset ι => ∑ i ∈ s, (inner 𝒷 (e i) x : 𝒷) • e i)
    (fun s : Finset ι => ∑ i ∈ s, (inner 𝒷 (e i) x : 𝒷) • e i) x x
    (he.2.1 x) (he.2.1 x)
  simpa only [show (cstarBInner 𝒷 X).inner = (inner 𝒷 : X → X → 𝒷) from rfl,
    hkey] using h

variable (𝒷 X) in
/-- Norm-bounded ultranorm completeness (condition 3 of **149V**): every
norm-bounded ultranorm-Cauchy filter converges. -/
def BddUnComplete : Prop :=
  ∀ F : Filter X, F.NeBot → UnCauchy (inner 𝒷) F →
    (∃ M : ℝ, ∃ s ∈ F, ∀ x ∈ s, ‖x‖ ≤ M) →
    ∃ x₀, UnTendsto (inner 𝒷) id F x₀

/-! ### The four implications of **149V**

**149VI** (dils.tex:2257) fixes the route `1 ⇒ 3 ⇒ 4 ⇒ 2 ⇒ 4 ⇒ 1`; the four
non-trivial implications are stated separately below, so that they can be
used (and proved) one at a time.  All four are proved (`3 ⇒ 4` through
**80IV** `approximate_pseudoinverse`, `4 ⇒ 2` through **87VIII**
`ultraweakly_bounded_implies_bounded`, both from `A/VN`). -/

section OneImpliesThree

private theorem inner_neg_left' (B : BInner 𝒷 X) (x y : X) :
    B.inner (-x) y = -B.inner x y := by
  rw [show (-x) = (0 : X) - x by abel, B.inner_sub_left, B.inner_zero_left,
    zero_sub]

private theorem inner_neg_right' (B : BInner 𝒷 X) (x y : X) :
    B.inner x (-y) = -B.inner x y := by
  rw [show (-y) = (0 : X) - y by abel, B.inner_sub_right, B.inner_zero_right,
    zero_sub]

private theorem unSeminorm_neg' (ω : NPFunctional 𝒷) (B : BInner 𝒷 X) (x : X) :
    unSeminorm ω B.inner (-x) = unSeminorm ω B.inner x := by
  rw [unSeminorm, unSeminorm, inner_neg_left', inner_neg_right', neg_neg]

/-- Uniqueness of ultrastrong limits (**44XI**.1, `vn_positive_basic_1`). -/
private theorem usTendsto_unique' [VonNeumannAlgebra 𝒷] {J : Type*}
    {l : Filter J} [l.NeBot] {f : J → 𝒷} {a c : 𝒷} (ha : USTendsto f l a)
    (hc : USTendsto f l c) : a = c :=
  @tendsto_nhds_unique 𝒷 J (ultrastrong 𝒷) (vn_positive_basic_1 (A := 𝒷)).2
    f l a c _ ha hc

private theorem usTendsto_add' {J : Type*} {l : Filter J} {f g : J → 𝒷}
    {a b : 𝒷} (hf : USTendsto f l a) (hg : USTendsto g l b) :
    USTendsto (fun i => f i + g i) l (a + b) := by
  rw [usTendsto_iff] at hf hg ⊢
  intro ω
  refine squeeze_zero (fun i => omegaNorm_nonneg ω _) (fun i => ?_)
    (by simpa using (hf ω).add (hg ω))
  rw [show f i + g i - (a + b) = (f i - a) + (g i - b) by abel]
  exact omegaNorm_add_le ω _ _

private theorem usTendsto_const_mul' {J : Type*} {l : Filter J} {f : J → 𝒷}
    {a : 𝒷} (b : 𝒷) (hf : USTendsto f l a) :
    USTendsto (fun i => b * f i) l (b * a) := by
  rw [usTendsto_iff] at hf ⊢
  intro ω
  refine squeeze_zero (fun i => omegaNorm_nonneg ω _) (fun i => ?_)
    (by simpa using (hf ω).const_mul ‖b‖)
  rw [← mul_sub]
  exact omegaNorm_mul_le ω b _

private theorem usTendsto_smul' {J : Type*} {l : Filter J} {f : J → 𝒷}
    {a : 𝒷} (c : ℂ) (hf : USTendsto f l a) :
    USTendsto (fun i => c • f i) l (c • a) := by
  rw [usTendsto_iff] at hf ⊢
  intro ω
  have heq : ∀ i, omegaNorm 𝒷 ω (c • f i - c • a)
      = ‖c‖ * omegaNorm 𝒷 ω (f i - a) := fun i => by
    rw [← smul_sub, omegaNorm_smul]
  simp only [heq]
  simpa using (hf ω).const_mul ‖c‖

omit [PartialOrder 𝒷] [StarOrderedRing 𝒷] in
private theorem isSelfAdjoint_real_smul_one (r : ℝ) :
    IsSelfAdjoint ((r : ℝ) • (1 : 𝒷)) := by
  rw [show ((r : ℝ) • (1 : 𝒷)) = ((r : ℝ) : ℂ) • (1 : 𝒷) from
    RCLike.real_smul_eq_coe_smul (K := ℂ) r 1]
  exact IsSelfAdjoint.smul (Complex.conj_ofReal r) (IsSelfAdjoint.one 𝒷)

/-- Order separation of the np-functionals in the form used below: a bound
`‖a‖_ω ≤ C ω(1)^½` for every np-functional `ω` is a bound on `‖a‖`.  (This
is the `hchar` of `vn_positive_basic_3`, stated for a general `C`.) -/
private theorem norm_le_of_omegaNorm_le [VonNeumannAlgebra 𝒷] {a : 𝒷} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ ω : NPFunctional 𝒷, omegaNorm 𝒷 ω a ≤ C * Real.sqrt (ω 1).re) :
    ‖a‖ ≤ C := by
  rcases subsingleton_or_nontrivial 𝒷 with _ | _
  · rw [Subsingleton.elim a 0, norm_zero]; exact hC
  have hle : star a * a ≤ (C ^ 2 : ℝ) • (1 : 𝒷) := by
    refine np_orderSeparating _ _ (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg a))
      (isSelfAdjoint_real_smul_one (C ^ 2)) fun ω => ?_
    have hnn : 0 ≤ (ω (star a * a)).re := np_re_nonneg ω (star_mul_self_nonneg a)
    have hnn1 : 0 ≤ (ω 1).re := np_re_nonneg ω zero_le_one
    have hω := h ω
    rw [omegaNorm] at hω
    have hre : (ω (star a * a)).re ≤ (ω ((C ^ 2 : ℝ) • (1 : 𝒷))).re := by
      rw [np_re_smul]
      have h2 : Real.sqrt (ω (star a * a)).re * Real.sqrt (ω (star a * a)).re
          ≤ (C * Real.sqrt (ω 1).re) * (C * Real.sqrt (ω 1).re) :=
        mul_self_le_mul_self (Real.sqrt_nonneg _) hω
      rw [Real.mul_self_sqrt hnn] at h2
      calc (ω (star a * a)).re
          ≤ (C * Real.sqrt (ω 1).re) * (C * Real.sqrt (ω 1).re) := h2
        _ = C ^ 2 * (Real.sqrt (ω 1).re * Real.sqrt (ω 1).re) := by ring
        _ = C ^ 2 * (ω 1).re := by rw [Real.mul_self_sqrt hnn1]
    refine Complex.le_def.mpr ⟨hre, ?_⟩
    have i1 : (ω (star a * a)).im = 0 := np_im_zero ω (star_mul_self_nonneg a)
    have i2 : (ω ((C ^ 2 : ℝ) • (1 : 𝒷))).im = 0 := by
      rw [show ((C ^ 2 : ℝ) • (1 : 𝒷)) = ((C ^ 2 : ℝ) : ℂ) • (1 : 𝒷) from
        RCLike.real_smul_eq_coe_smul (K := ℂ) _ 1, np_smul, Complex.mul_im,
        np_im_zero ω (zero_le_one (α := 𝒷)), Complex.ofReal_im]
      ring
    rw [i1, i2]
  have hn : ‖star a * a‖ ≤ ‖((C ^ 2 : ℝ) • (1 : 𝒷))‖ :=
    CStarAlgebra.norm_le_norm_of_nonneg_of_le (star_mul_self_nonneg a) hle
  rw [CStarRing.norm_star_mul_self] at hn
  have h1 : ‖((C ^ 2 : ℝ) • (1 : 𝒷))‖ = C ^ 2 := by
    rw [norm_smul, norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg C)]
  rw [h1] at hn
  nlinarith [norm_nonneg a]

/-- **142III** in the form used by **149VII**: `‖[d,y]‖_ω ≤ ‖y‖ ‖d‖_ω`. -/
private theorem omegaNorm_inner_le (ω : NPFunctional 𝒷) (d y : X) :
    omegaNorm 𝒷 ω (inner 𝒷 d y) ≤ ‖y‖ * unSeminorm ω (inner 𝒷 : X → X → 𝒷) d := by
  have hcs : (inner 𝒷 y d : 𝒷) * inner 𝒷 d y
      ≤ ‖(inner 𝒷 y y : 𝒷)‖ • (inner 𝒷 d d : 𝒷) := module_CS (cstarBInner 𝒷 X) d y
  have hyy : ‖(inner 𝒷 y y : 𝒷)‖ = ‖y‖ ^ 2 := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷) (E := X) y,
      Real.sq_sqrt (norm_nonneg _)]
  have h1 := np_re_mono ω hcs
  rw [np_re_smul, hyy] at h1
  have hd : (ω (inner 𝒷 d d : 𝒷)).re
      = unSeminorm ω (inner 𝒷 : X → X → 𝒷) d ^ 2 :=
    (unSeminorm_sq ω (cstarBInner 𝒷 X) d).symm
  have hnn : 0 ≤ (ω (star (inner 𝒷 d y : 𝒷) * inner 𝒷 d y)).re :=
    np_re_nonneg ω (star_mul_self_nonneg _)
  have hstar : star (inner 𝒷 d y : 𝒷) = inner 𝒷 y d := CStarModule.star_inner _ _
  have hsq : omegaNorm 𝒷 ω (inner 𝒷 d y) ^ 2
      ≤ (‖y‖ * unSeminorm ω (inner 𝒷 : X → X → 𝒷) d) ^ 2 := by
    rw [omegaNorm, Real.sq_sqrt hnn, hstar, mul_pow, ← hd]
    exact h1
  nlinarith [omegaNorm_nonneg (A := 𝒷) ω (inner 𝒷 d y),
    mul_nonneg (norm_nonneg y) (unSeminorm_nonneg ω (inner 𝒷 : X → X → 𝒷) d)]

/-- **146IX** (dils.tex:1915, Beware), the quantitative half: *"the
ultranorm uniformity is weaker than the norm uniformity — norm convergence
implies ultranorm convergence"*, as the estimate `‖x‖_ω ≤ ‖x‖ ω(1)^½`, in
the form that **149VII** uses.  (Earlier revisions of this file labelled it
146VIII, whose two identifications are `unSeminorm_complex` and
`unSeminorm_mulInner_eq_omegaNorm` above.  The converse half of 146IX —
"but not necessarily the other way around" — is `unTendsto_not_norm_tendsto`
above, with the counterexample `|n⟩⟨0|` on `ℓ²`.) -/
theorem unSeminorm_le_norm_mul (ω : NPFunctional 𝒷) (x : X) :
    unSeminorm ω (inner 𝒷 : X → X → 𝒷) x ≤ ‖x‖ * Real.sqrt (ω 1).re := by
  have hle : (inner 𝒷 x x : 𝒷) ≤ (‖(inner 𝒷 x x : 𝒷)‖ : ℝ) • (1 : 𝒷) :=
    le_norm_smul_one (CStarModule.inner_self_nonneg (E := X) (x := x))
  have h1 := np_re_mono ω hle
  rw [np_re_smul] at h1
  have hxx : ‖(inner 𝒷 x x : 𝒷)‖ = ‖x‖ ^ 2 := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷) (E := X) x,
      Real.sq_sqrt (norm_nonneg _)]
  rw [hxx] at h1
  rw [unSeminorm]
  calc Real.sqrt (ω (inner 𝒷 x x : 𝒷)).re
      ≤ Real.sqrt (‖x‖ ^ 2 * (ω 1).re) := Real.sqrt_le_sqrt h1
    _ = ‖x‖ * Real.sqrt (ω 1).re := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg x)]

end OneImpliesThree

/-- **149VII** (dils.tex:2266): (1) ⇒ (3) of **149V** — a self-dual
pre-Hilbert 𝒷-module is norm-bounded ultranorm complete.

Divergence class 1 (faithful), with one notational mirror.  The thesis's
`τ(y) = (uslim_α ⟨y,x_α⟩)*` is *unstarred* here — `τ(y) = uslim_α [x_α,y]` —
because it is the *second* argument of Mathlib's `[·,·]` that is 𝒷-linear;
the ultrastrong limit exists by **77I**.1 `Theses.A.VN.vn_complete_1` (whence
the import of `Theses.A.VN.Completeness`), and `τ` is linear by uniqueness of
ultrastrong limits (**44XI**.1).  The bound on `τ` is the thesis's own: **46II**
`usconv` turns the ultrastrong limit into the ultraweak limit
`τ(y)*τ(y) = uwlim_α [y,x_α][x_α,y]` (the mirror of the thesis's
`τ(y)τ(y)* = uwlim_α ⟨x_α,y⟩⟨y,x_α⟩`), whose terms **142III** bounds by
`‖y‖²B²`; passing to the limit gives `‖τ(y)‖_ω ≤ ‖y‖ B ω(1)^½` for every
np-functional, which is `‖τ(y)‖ ≤ B‖y‖` by order separation (**44XI**).  The
closing estimate is the thesis's verbatim, with Kadison's inequality in the
form `norm_apply_le_omegaNorm`. -/
theorem bddUnComplete_of_selfDual [VonNeumannAlgebra 𝒷] (h : SelfDual 𝒷 X) :
    BddUnComplete 𝒷 X := by
  classical
  rintro F hF hcauchy ⟨M, s₀, hs₀F, hs₀⟩
  haveI : F.NeBot := hF
  have hMnn : 0 ≤ M := by
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hs₀F
    exact le_trans (norm_nonneg x) (hs₀ x hx)
  -- rewriting rules for the inner product, phrased with `inner 𝒷` so that
  -- they can be used by `rw`
  have hsubL : ∀ a b c : X, (inner 𝒷 (a - b) c : 𝒷) = inner 𝒷 a c - inner 𝒷 b c :=
    fun a b c => (cstarBInner 𝒷 X).inner_sub_left a b c
  -- (a) for each `y`, `x ↦ [x,y]` is an ultrastrong-Cauchy net along `F`
  have hcau : ∀ y : X, ∀ ω : NPFunctional 𝒷,
      Tendsto (fun p : X × X =>
          omegaNorm 𝒷 ω ((inner 𝒷 p.1 y : 𝒷) - inner 𝒷 p.2 y)) (F ×ˢ F) (𝓝 0) := by
    intro y ω
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨s, hsF, hs⟩ := hcauchy ω (ε / (2 * (‖y‖ + 1))) (by positivity)
    filter_upwards [prod_mem_prod hsF hsF] with p hp
    have h1 : omegaNorm 𝒷 ω ((inner 𝒷 p.1 y : 𝒷) - inner 𝒷 p.2 y)
        ≤ ‖y‖ * unSeminorm ω (inner 𝒷 : X → X → 𝒷) (p.1 - p.2) := by
      rw [← hsubL]; exact omegaNorm_inner_le ω _ y
    have h2 := hs p.1 hp.1 p.2 hp.2
    have h3 : ‖y‖ * (ε / (2 * (‖y‖ + 1))) < ε := by
      have hpos : (0 : ℝ) < 2 * (‖y‖ + 1) := by positivity
      have h0 : ‖y‖ * (ε / (2 * (‖y‖ + 1))) * (2 * (‖y‖ + 1)) = ‖y‖ * ε := by
        field_simp
      nlinarith [norm_nonneg y, hε, hpos]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (omegaNorm_nonneg ω _)]
    calc omegaNorm 𝒷 ω ((inner 𝒷 p.1 y : 𝒷) - inner 𝒷 p.2 y)
        ≤ ‖y‖ * unSeminorm ω (inner 𝒷 : X → X → 𝒷) (p.1 - p.2) := h1
      _ ≤ ‖y‖ * (ε / (2 * (‖y‖ + 1))) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg y)
      _ < ε := h3
  -- (b) `τ y = uslim_α [x_α, y]` (**77I**.1)
  have hex : ∀ y : X, ∃ a : 𝒷, USTendsto (fun x : X => (inner 𝒷 x y : 𝒷)) F a :=
    fun y => vn_complete_1 F (fun x : X => (inner 𝒷 x y : 𝒷)) (hcau y)
  choose t' ht' using hex
  -- (c) `τ` is ℂ-linear and 𝒷-linear, by uniqueness of ultrastrong limits
  have hadd : ∀ y z : X, t' (y + z) = t' y + t' z := fun y z => by
    refine usTendsto_unique' (ht' (y + z)) ?_
    have h2 := usTendsto_add' (ht' y) (ht' z)
    have heq : (fun x : X => (inner 𝒷 x y : 𝒷) + inner 𝒷 x z)
        = fun x : X => (inner 𝒷 x (y + z) : 𝒷) :=
      funext fun x => CStarModule.inner_add_right.symm
    rwa [heq] at h2
  have hsmul : ∀ (c : ℂ) (y : X), t' (c • y) = c • t' y := fun c y => by
    refine usTendsto_unique' (ht' (c • y)) ?_
    have h2 := usTendsto_smul' c (ht' y)
    have heq : (fun x : X => c • (inner 𝒷 x y : 𝒷))
        = fun x : X => (inner 𝒷 x (c • y) : 𝒷) :=
      funext fun x => CStarModule.inner_smul_right_complex.symm
    rwa [heq] at h2
  have hbsmul : ∀ (b : 𝒷) (y : X), t' (b • y) = b * t' y := fun b y => by
    refine usTendsto_unique' (ht' (b • y)) ?_
    have h2 := usTendsto_const_mul' b (ht' y)
    have heq : (fun x : X => b * (inner 𝒷 x y : 𝒷))
        = fun x : X => (inner 𝒷 x (b • y) : 𝒷) :=
      funext fun x => CStarModule.inner_op_smul_right.symm
    rwa [heq] at h2
  -- (d) **46II** `usconv` turns the ultrastrong limit `τ(y)` into the
  -- ultraweak limit `τ(y)*τ(y) = uwlim_α ⟨y,x_α⟩⟨x_α,y⟩` (the mirror of the
  -- thesis's `τ(y)τ(y)* = uwlim_α ⟨x_α,y⟩⟨y,x_α⟩`), and each term of that net
  -- is bounded by `‖y‖²B²` through **142III**; so `‖τ y‖_ω ≤ ‖y‖ B ω(1)^½`,
  -- and `‖τ y‖ ≤ B ‖y‖` by order separation of the np-functionals (**44XI**)
  have hbound : ∀ (ω : NPFunctional 𝒷) (y : X),
      omegaNorm 𝒷 ω (t' y) ≤ ‖y‖ * M * Real.sqrt (ω 1).re := by
    intro ω y
    have huw : UWTendsto
        (fun x : X => star (inner 𝒷 x y : 𝒷) * (inner 𝒷 x y : 𝒷)) F
        (star (t' y) * t' y) :=
      ((usconv (fun x : X => (inner 𝒷 x y : 𝒷)) F (t' y)).mp (ht' y)).1
    have hlim : Tendsto (fun x : X => omegaNorm 𝒷 ω (inner 𝒷 x y : 𝒷)) F
        (𝓝 (omegaNorm 𝒷 ω (t' y))) :=
      (Real.continuous_sqrt.tendsto _).comp
        ((Complex.continuous_re.tendsto _).comp ((uwTendsto_iff _ F _).mp huw ω))
    refine le_of_tendsto hlim ?_
    filter_upwards [hs₀F] with x hx
    have hsq : (0 : ℝ) ≤ Real.sqrt (ω 1).re := Real.sqrt_nonneg _
    calc omegaNorm 𝒷 ω ((inner 𝒷 x y : 𝒷))
        ≤ ‖y‖ * unSeminorm ω (inner 𝒷 : X → X → 𝒷) x := omegaNorm_inner_le ω x y
      _ ≤ ‖y‖ * (‖x‖ * Real.sqrt (ω 1).re) :=
          mul_le_mul_of_nonneg_left (unSeminorm_le_norm_mul ω x) (norm_nonneg y)
      _ ≤ ‖y‖ * (M * Real.sqrt (ω 1).re) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hs₀ x hx) hsq) (norm_nonneg y)
      _ = ‖y‖ * M * Real.sqrt (ω 1).re := (mul_assoc _ _ _).symm
  have hnormbound : ∀ y : X, ‖t' y‖ ≤ M * ‖y‖ := fun y =>
    le_trans (norm_le_of_omegaNorm_le (a := t' y) (C := ‖y‖ * M)
      (mul_nonneg (norm_nonneg y) hMnn) (fun ω => hbound ω y))
      (le_of_eq (mul_comm _ _))
  -- (e) self-duality produces the candidate limit `t`
  obtain ⟨t, hts⟩ := h
    { toFun := t', map_add' := hadd, map_smul' := fun c y => hsmul c y }
    (fun b x => hbsmul b x) ⟨M, hnormbound⟩
  have htt : ∀ y : X, t' y = inner 𝒷 t y := hts
  -- (f) `x_α → t` ultranorm
  refine ⟨t, fun ω => ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = Real.sqrt (ω 1).re := ⟨_, rfl⟩
  have hSnn : (0 : ℝ) ≤ S := hS ▸ Real.sqrt_nonneg _
  obtain ⟨K, hK⟩ : ∃ K : ℝ,
      K = unSeminorm ω (inner 𝒷 : X → X → 𝒷) t + M * S := ⟨_, rfl⟩
  have hKnn : (0 : ℝ) ≤ K := by
    rw [hK]
    have h1 := unSeminorm_nonneg ω (inner 𝒷 : X → X → 𝒷) t
    have h2 : (0 : ℝ) ≤ M * S := mul_nonneg hMnn hSnn
    linarith
  obtain ⟨s, hsF, hs⟩ := hcauchy ω ((ε / 2) ^ 2 / (2 * (K + 1))) (by positivity)
  filter_upwards [inter_mem hsF hs₀F] with x hx
  simp only [id_eq]
  -- `‖t - x‖_ω ≤ K`
  have hwK : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (t - x) ≤ K := by
    have h1 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (t + -x)
        ≤ unSeminorm ω (inner 𝒷 : X → X → 𝒷) t
          + unSeminorm ω (inner 𝒷 : X → X → 𝒷) (-x) :=
      unSeminorm_add_le ω (cstarBInner 𝒷 X) t (-x)
    have hneg : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (-x)
        = unSeminorm ω (inner 𝒷 : X → X → 𝒷) x :=
      unSeminorm_neg' ω (cstarBInner 𝒷 X) x
    rw [hneg] at h1
    have h2 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) x ≤ M * S := by
      have h3 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) x ≤ ‖x‖ * Real.sqrt (ω 1).re :=
        unSeminorm_le_norm_mul ω x
      rw [← hS] at h3
      exact le_trans h3 (mul_le_mul_of_nonneg_right (hs₀ x hx.2) hSnn)
    rw [show t - x = t + -x by abel, hK]
    linarith
  -- pick `β` with `|[t-x, t-β]_ω|` small
  have hmem : {z : X | omegaNorm 𝒷 ω ((inner 𝒷 z (t - x) : 𝒷)
      - inner 𝒷 t (t - x)) < (ε / 2) ^ 2 / (2 * (S + 1))} ∈ F := by
    have h0 := (usTendsto_iff _ _ _).mp (ht' (t - x)) ω
    filter_upwards [(Metric.tendsto_nhds.mp h0)
      ((ε / 2) ^ 2 / (2 * (S + 1))) (by positivity)] with z hz
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (omegaNorm_nonneg ω _),
      htt (t - x)] at hz
  obtain ⟨β, hβ⟩ := Filter.nonempty_of_mem (inter_mem hmem hsF)
  -- split `[t-x, t-x] = [t-x, t-β] + [t-x, β-x]`
  have hre : (ω (inner 𝒷 (t - x) (t - x) : 𝒷)).re
      = (ω (inner 𝒷 (t - x) (t - β) : 𝒷)).re
        + (ω (inner 𝒷 (t - x) (β - x) : 𝒷)).re := by
    have hsplit : (inner 𝒷 (t - x) (t - x) : 𝒷)
        = inner 𝒷 (t - x) (t - β) + inner 𝒷 (t - x) (β - x) := by
      rw [← CStarModule.inner_add_right, show (t - β) + (β - x) = t - x by abel]
    rw [hsplit, np_add, Complex.add_re]
  have hT1 : (ω (inner 𝒷 (t - x) (t - β) : 𝒷)).re ≤ (ε / 2) ^ 2 / 2 := by
    have hnorm : ‖ω (inner 𝒷 (t - x) (t - β) : 𝒷)‖
        = ‖ω (inner 𝒷 (t - β) (t - x) : 𝒷)‖ := by
      rw [show (inner 𝒷 (t - x) (t - β) : 𝒷) = star (inner 𝒷 (t - β) (t - x)) from
        (CStarModule.star_inner _ _).symm, np_star, RCLike.norm_conj]
    have hb1 : ‖ω (inner 𝒷 (t - β) (t - x) : 𝒷)‖
        ≤ omegaNorm 𝒷 ω (inner 𝒷 (t - β) (t - x)) * S := by
      have := norm_apply_le_omegaNorm ω (inner 𝒷 (t - β) (t - x) : 𝒷)
      rwa [← hS] at this
    have hb2 : omegaNorm 𝒷 ω (inner 𝒷 (t - β) (t - x))
        = omegaNorm 𝒷 ω ((inner 𝒷 β (t - x) : 𝒷) - inner 𝒷 t (t - x)) := by
      rw [show (inner 𝒷 (t - β) (t - x) : 𝒷)
          = -((inner 𝒷 β (t - x) : 𝒷) - inner 𝒷 t (t - x)) by rw [hsubL]; abel,
        omegaNorm_neg]
    have hfin : ((ε / 2) ^ 2 / (2 * (S + 1))) * S ≤ (ε / 2) ^ 2 / 2 := by
      have hpos : (0 : ℝ) < 2 * (S + 1) := by positivity
      have key : ((ε / 2) ^ 2 / (2 * (S + 1))) * S * (2 * (S + 1))
          = (ε / 2) ^ 2 * S := by field_simp
      nlinarith [hSnn, pow_pos (by linarith : (0:ℝ) < ε / 2) 2, hpos]
    have hmain : ‖ω (inner 𝒷 (t - x) (t - β) : 𝒷)‖
        ≤ ((ε / 2) ^ 2 / (2 * (S + 1))) * S := by
      rw [hnorm]
      refine le_trans hb1 ?_
      rw [hb2]
      exact mul_le_mul_of_nonneg_right hβ.1.le hSnn
    have := Complex.re_le_norm (ω (inner 𝒷 (t - x) (t - β) : 𝒷))
    linarith
  have hT2 : (ω (inner 𝒷 (t - x) (β - x) : 𝒷)).re ≤ (ε / 2) ^ 2 / 2 := by
    have h1 := Complex.re_le_norm (ω (inner 𝒷 (t - x) (β - x) : 𝒷))
    have h2 : ‖ω (inner 𝒷 (t - x) (β - x) : 𝒷)‖
        ≤ unSeminorm ω (inner 𝒷 : X → X → 𝒷) (t - x)
          * unSeminorm ω (inner 𝒷 : X → X → 𝒷) (β - x) :=
      unSeminorm_inner_le ω (cstarBInner 𝒷 X) (t - x) (β - x)
    have h3 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (β - x)
        ≤ (ε / 2) ^ 2 / (2 * (K + 1)) := hs β hβ.2 x hx.1
    have h4 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (t - x)
        * unSeminorm ω (inner 𝒷 : X → X → 𝒷) (β - x)
        ≤ K * ((ε / 2) ^ 2 / (2 * (K + 1))) :=
      mul_le_mul hwK h3 (unSeminorm_nonneg _ _ _) hKnn
    have h5 : K * ((ε / 2) ^ 2 / (2 * (K + 1))) ≤ (ε / 2) ^ 2 / 2 := by
      have hpos : (0 : ℝ) < 2 * (K + 1) := by positivity
      have key : K * ((ε / 2) ^ 2 / (2 * (K + 1))) * (2 * (K + 1))
          = K * (ε / 2) ^ 2 := by field_simp
      nlinarith [hKnn, pow_pos (by linarith : (0:ℝ) < ε / 2) 2, hpos]
    linarith
  have hfinal : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (x - t) ≤ ε / 2 := by
    have hneg : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (-(t - x))
        = unSeminorm ω (inner 𝒷 : X → X → 𝒷) (t - x) :=
      unSeminorm_neg' ω (cstarBInner 𝒷 X) (t - x)
    have hsq : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (x - t) ^ 2
        = (ω (inner 𝒷 (t - x) (t - x) : 𝒷)).re := by
      rw [show x - t = -(t - x) by abel, hneg]
      exact unSeminorm_sq ω (cstarBInner 𝒷 X) (t - x)
    have h2 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (x - t) ^ 2 ≤ (ε / 2) ^ 2 := by
      rw [hsq, hre]; linarith
    nlinarith [unSeminorm_nonneg ω (inner 𝒷 : X → X → 𝒷) (x - t),
      (by linarith : (0:ℝ) ≤ ε / 2)]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (unSeminorm_nonneg _ _ _)]
  linarith

/-! ### Auxiliary: the algebra of the `𝒷`-action, and ultranorm estimates

Mathlib's `CStarModule` carries a bare `SMul 𝒷 X` with no distributivity
axioms for the `𝒷`-action; on a pre-Hilbert module those laws are *forced* by
the inner product axioms and definiteness (the same argument as **149III**),
so we derive the ones the proofs of **149VIII**/**149IX** need. -/

private theorem add_smul' (a b : 𝒷) (x : X) : (a + b) • x = a • x + b • x := by
  have h : (inner 𝒷 ((a + b) • x - (a • x + b • x))
      ((a + b) • x - (a • x + b • x)) : 𝒷) = 0 := by
    simp only [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
      CStarModule.inner_add_left, CStarModule.inner_add_right,
      CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right, star_add]
    noncomm_ring
  have := (CStarModule.inner_self (A := 𝒷)).mp h
  rwa [sub_eq_zero] at this

private theorem zero_smul' (x : X) : (0 : 𝒷) • x = 0 := by
  have h := add_smul' (0 : 𝒷) 0 x
  rw [add_zero] at h
  have h2 : (0 : 𝒷) • x + (0 : 𝒷) • x = (0 : 𝒷) • x + 0 := by
    rw [add_zero, ← h]
  exact (add_left_cancel h2)

private theorem sub_smul' (a b : 𝒷) (x : X) : (a - b) • x = a • x - b • x := by
  have h := add_smul' (a - b) b x
  rw [sub_add_cancel] at h
  rw [eq_sub_iff_add_eq, ← h]

/-- `‖ω(a)‖ = Re ω(a)` for positive `a`. -/
private theorem norm_np_eq_re (ω : NPFunctional 𝒷) {a : 𝒷} (ha : 0 ≤ a) :
    ‖ω a‖ = (ω a).re := by
  have him : (ω a).im = 0 := np_im_zero ω ha
  have hre : 0 ≤ (ω a).re := np_re_nonneg ω ha
  have h1 : ω a = ((ω a).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him]
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre,
    Complex.ofReal_re]

/-- The `ω`-seminorm form of Bessel's inequality: the coefficient partial
sums are `‖·‖_ω`-contractions of `z`. -/
private theorem unSeminorm_coeff_sum_le {e : ι → X} (he : OrthonormalFam 𝒷 e)
    (ω : NPFunctional 𝒷) (z : X) (s : Finset ι) :
    unSeminorm ω (inner 𝒷 : X → X → 𝒷) (∑ i ∈ s, (inner 𝒷 (e i) z : 𝒷) • e i)
      ≤ unSeminorm ω (inner 𝒷 : X → X → 𝒷) z := by
  have h1 : (inner 𝒷 (∑ i ∈ s, (inner 𝒷 (e i) z : 𝒷) • e i)
      (∑ i ∈ s, (inner 𝒷 (e i) z : 𝒷) • e i) : 𝒷)
      = ∑ i ∈ s, (inner 𝒷 (e i) z : 𝒷) * inner 𝒷 z (e i) := by
    rw [inner_sum_smul_self he.1 _ (fun i => onbasis_coef_absorb he z i) s]
    exact Finset.sum_congr rfl fun i _ => by rw [CStarModule.star_inner]
  rw [unSeminorm, unSeminorm, h1]
  exact Real.sqrt_le_sqrt (np_re_mono ω (mod_bessel he z s))

/-- `‖d • x‖_ω ≤ ‖d*‖_ω` when `⟨x,x⟩` is a projection. -/
private theorem unSeminorm_smul_proj_le {x : X}
    (hx : IsStarProjection (inner 𝒷 x x : 𝒷)) (ω : NPFunctional 𝒷) (d : 𝒷) :
    unSeminorm ω (inner 𝒷 : X → X → 𝒷) (d • x) ≤ omegaNorm 𝒷 ω (star d) := by
  have h1 : (inner 𝒷 (d • x) (d • x) : 𝒷) = d * inner 𝒷 x x * star d := by
    simp only [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
      mul_assoc]
  rw [unSeminorm, h1, omegaNorm]
  refine Real.sqrt_le_sqrt (np_re_mono ω ?_)
  rw [star_star]
  calc d * inner 𝒷 x x * star d ≤ d * 1 * star d :=
        star_right_conjugate_le_conjugate hx.le_one d
    _ = d * star d := by rw [mul_one]

private theorem unSeminorm_sum_le (ω : NPFunctional 𝒷) {κ : Type*}
    (s : Finset κ) (f : κ → X) :
    unSeminorm ω (inner 𝒷 : X → X → 𝒷) (∑ i ∈ s, f i)
      ≤ ∑ i ∈ s, unSeminorm ω (inner 𝒷 : X → X → 𝒷) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (inner 𝒷 (0 : X) (0 : X) : 𝒷) = 0 :=
      (cstarBInner 𝒷 X).inner_zero_left 0
    simp [unSeminorm, h0]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (unSeminorm_add_le ω (cstarBInner 𝒷 X) _ _)
      (add_le_add le_rfl ih)

/-- Along an ultranorm-Cauchy filter the mirrored coefficients `z ↦ [z, x]`
form an ultrastrong-Cauchy net (via **142III**). -/
private theorem unCauchy_inner_tendsto {F : Filter X}
    (hcauchy : UnCauchy (inner 𝒷 : X → X → 𝒷) F) (x : X) (ω : NPFunctional 𝒷) :
    Tendsto (fun p : X × X =>
        omegaNorm 𝒷 ω ((inner 𝒷 p.1 x : 𝒷) - inner 𝒷 p.2 x))
      (F ×ˢ F) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  obtain ⟨s, hsF, hs⟩ := hcauchy ω (ε / (‖x‖ + 1)) (by positivity)
  filter_upwards [Filter.prod_mem_prod hsF hsF] with p hp
  have hsub : (inner 𝒷 p.1 x : 𝒷) - inner 𝒷 p.2 x = inner 𝒷 (p.1 - p.2) x :=
    ((cstarBInner 𝒷 X).inner_sub_left p.1 p.2 x).symm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (omegaNorm_nonneg _ _), hsub]
  calc omegaNorm 𝒷 ω (inner 𝒷 (p.1 - p.2) x)
      ≤ ‖x‖ * unSeminorm ω (inner 𝒷 : X → X → 𝒷) (p.1 - p.2) :=
        omegaNorm_inner_le ω _ x
    _ ≤ ‖x‖ * (ε / (‖x‖ + 1)) :=
        mul_le_mul_of_nonneg_left (hs p.1 hp.1 p.2 hp.2) hx
    _ = ε * (‖x‖ / (‖x‖ + 1)) := by ring
    _ < ε * 1 := by
        refine mul_lt_mul_of_pos_left ?_ hε
        rw [div_lt_one (by positivity)]
        linarith
    _ = ε := mul_one ε

private theorem uwTendsto_const {κ : Type*} (l : Filter κ) (aa : 𝒷) :
    UWTendsto (fun _ : κ => aa) l aa := by
  rw [uwTendsto_iff]
  exact fun ω => tendsto_const_nhds

/-- An increasing sequence of self-adjoint elements with supremum `q`
converges to `q` ultraweakly, along with its left `b*`-multiples (**44XIV**,
**46VII**, through `vna_supremum_uwlimit`/`vna_supremum_mult`, transferred
from the directed-set index to `ℕ`). -/
private theorem uwTendsto_partialSums [VonNeumannAlgebra 𝒷] {q : 𝒷}
    (cc : ℕ → 𝒷) (hmono : Monotone cc) (hsa : ∀ N, IsSelfAdjoint (cc N))
    (hqsa : IsSelfAdjoint q) (hlub : IsLUB {x : 𝒷 | ∃ N : ℕ, x = cc N} q)
    (bb : 𝒷) :
    UWTendsto cc atTop q ∧
      UWTendsto (fun N => star bb * cc N) atTop (star bb * q) := by
  classical
  set mk : ℕ → selfAdjoint 𝒷 :=
    fun N => ⟨cc N, selfAdjoint.mem_iff.mpr (hsa N)⟩ with hmk
  set qmk : selfAdjoint 𝒷 := ⟨q, selfAdjoint.mem_iff.mpr hqsa⟩ with hqmk
  set D : Set (selfAdjoint 𝒷) := {d : selfAdjoint 𝒷 | ∃ N : ℕ, (d : 𝒷) = cc N}
    with hD
  have hmkmem : ∀ N, mk N ∈ D := fun N => ⟨N, rfl⟩
  have hne : D.Nonempty := ⟨mk 0, hmkmem 0⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro x ⟨N, hN⟩ y ⟨M, hM⟩
    refine ⟨mk (max N M), hmkmem _, ?_, ?_⟩
    · exact Subtype.coe_le_coe.mp (by rw [hN]; exact hmono (le_max_left _ _))
    · exact Subtype.coe_le_coe.mp (by rw [hM]; exact hmono (le_max_right _ _))
  have hbdd : BddAbove D := ⟨qmk, by
    rintro x ⟨N, hN⟩
    exact Subtype.coe_le_coe.mp (by rw [hN]; exact hlub.1 ⟨N, rfl⟩)⟩
  have h3 : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, hbdd⟩
  have hlubD : IsLUB D qmk := by
    constructor
    · rintro x ⟨N, hN⟩
      exact Subtype.coe_le_coe.mp (by rw [hN]; exact hlub.1 ⟨N, rfl⟩)
    · intro v hv
      refine Subtype.coe_le_coe.mp (hlub.2 ?_)
      rintro x ⟨N, rfl⟩
      exact Subtype.coe_le_coe.mpr (hv (hmkmem N))
  have hds : dirSup D h3 = qmk := (isLUB_dirSup D h3).unique hlubD
  set φ : ℕ → D := fun N => ⟨mk N, hmkmem N⟩ with hφ
  have hφmono : Monotone φ := fun N M hNM => by
    refine Subtype.coe_le_coe.mp (Subtype.coe_le_coe.mp ?_)
    show cc N ≤ cc M
    exact hmono hNM
  have hφtendsto : Tendsto φ atTop atTop := by
    refine tendsto_atTop_atTop_of_monotone hφmono ?_
    rintro ⟨d, N, hN⟩
    refine ⟨N, ?_⟩
    refine Subtype.coe_le_coe.mp (Subtype.coe_le_coe.mp ?_)
    show (d : 𝒷) ≤ cc N
    exact le_of_eq hN
  have h1 := Filter.Tendsto.comp (vna_supremum_uwlimit D h3) hφtendsto
  have h2 := Filter.Tendsto.comp ((vna_supremum_mult D h3 bb).2) hφtendsto
  rw [hds] at h1 h2
  exact ⟨h1, h2⟩

/-- **Polar decomposition** in a norm-bounded ultranorm complete pre-Hilbert
𝒷-module (dils.tex:2389, the first half of the proof of **149VIII**): every
`y` factors as `y = √⟨y,y⟩ • u` (mirrored) with `⟨u,u⟩ = ⌈√⟨y,y⟩⌋`.  The
element `u` is the ultranorm limit of `(∑_{n<N} hₙ) • y` for an approximate
pseudoinverse `(hₙ)ₙ` of `√⟨y,y⟩` (**80IV**).

That last clause is recorded in the statement as the third conjunct: `u` is
an ultranorm limit of 𝒷-multiples *of `y` itself*.  It costs nothing here
(the approximants are `sm N • y` by construction) and is what makes the
polar decomposition usable inside an ultranorm-closed 𝒷-submodule `W`: for
`y ∈ W` the isometric part `u` again lies in `W`, which is the step the
relativized orthonormalization of **160IV**.3 needs. -/
theorem polar_decomposition [VonNeumannAlgebra 𝒷]
    (h : BddUnComplete 𝒷 X) (y : X) :
    ∃ u : X, (inner 𝒷 u u : 𝒷) = suppProj (CFC.sqrt (inner 𝒷 y y : 𝒷))
      ∧ CFC.sqrt (inner 𝒷 y y : 𝒷) • u = y
      ∧ ∃ c : ℕ → 𝒷,
          UnTendsto (inner 𝒷 : X → X → 𝒷) (fun N => c N • y) atTop u := by
  classical
  set a : 𝒷 := (inner 𝒷 y y : 𝒷) with hadef
  have hann : (0 : 𝒷) ≤ a := CStarModule.inner_self_nonneg
  set bb : 𝒷 := CFC.sqrt a with hbbdef
  have hbnn : (0 : 𝒷) ≤ bb := CFC.sqrt_nonneg a
  have hbsa : IsSelfAdjoint bb := .of_nonneg hbnn
  have hbb : bb * bb = a := CFC.sqrt_mul_sqrt_self a hann
  set q : 𝒷 := suppProj bb with hqdef
  have hqproj : IsStarProjection q := (ceill_basic_1 bb).1.1
  have hbq : bb * q = bb := (ceill_basic_1 bb).1.2
  have hqb : q * bb = bb := by
    have := congrArg star hbq
    rwa [star_mul, hqproj.isSelfAdjoint.star_eq, hbsa.star_eq] at this
  obtain ⟨τ, hτ⟩ := approximate_pseudoinverse_of_nonneg bb hbnn
  have hτsa : ∀ n, IsSelfAdjoint (τ n) := fun n =>
    hτ.isSelfAdjoint_of_nonneg hbnn n
  set p : ℕ → 𝒷 := fun n => suppProj (τ n) with hpdef
  have hpproj : ∀ n, IsStarProjection (p n) := fun n => (ceill_basic_1 (τ n)).1.1
  have hbτ : ∀ n, bb * τ n = p n := fun n => hτ.mul_eq_suppProj n
  have hτb : ∀ n, τ n * bb = p n := fun n => by
    rw [hτ.mul_eq_rangeProj n, rangeProj_eq_suppProj_of_isSelfAdjoint (hτsa n)]
  set sm : ℕ → 𝒷 := fun N => ∑ n ∈ Finset.range N, τ n with hsmdef
  set qq : ℕ → 𝒷 := fun N => ∑ n ∈ Finset.range N, p n with hqqdef
  have hsmsa : ∀ N, star (sm N) = sm N := by
    intro N
    rw [hsmdef]
    rw [star_sum]
    exact Finset.sum_congr rfl fun n _ => (hτsa n).star_eq
  have hlub : IsLUB {x : 𝒷 | ∃ N : ℕ, x = qq N} q := by
    have h1 := hτ.sum_supp
    rwa [rangeProj_eq_suppProj_of_isSelfAdjoint hbsa] at h1
  have hqle1 : ∀ N, qq N ≤ 1 := fun N =>
    le_trans (hlub.1 ⟨N, rfl⟩) hqproj.le_one
  have horth : ∀ n m, n ≠ m → p n * p m = 0 := by
    intro n m hnm
    have hle : p n + p m ≤ 1 := by
      have hsub : ({n, m} : Finset ℕ) ⊆ Finset.range (max n m + 1) := by
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_left _ _))
        · rw [Finset.mem_singleton.mp hk]
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_right _ _))
      have h1 : ∑ k ∈ ({n, m} : Finset ℕ), p k ≤ qq (max n m + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => (hpproj k).nonneg
      rw [Finset.sum_pair hnm] at h1
      exact le_trans h1 (hqle1 _)
    exact ((orthogonal_tuple_of_projections_1 (p n) (p m) (hpproj n)
      (hpproj m)).out 3 0).mp hle
  have hqqproj : ∀ N, IsStarProjection (qq N) := fun N =>
    isStarProjection_sum (Finset.range N) p hpproj
      fun i _ j _ hij => horth i j hij
  have hqqmono : Monotone qq := fun N M hNM =>
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hk) hNM))
      fun k _ _ => (hpproj k).nonneg
  have hsb : ∀ N, sm N * bb = qq N := fun N => by
    rw [hsmdef, hqqdef]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => hτb n
  have hbs : ∀ N, bb * sm N = qq N := fun N => by
    rw [hsmdef, hqqdef]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => hbτ n
  -- the approximants and their Gram matrix
  set w : ℕ → X := fun N => sm N • y with hwdef
  have hww : ∀ N M, (inner 𝒷 (w N) (w M) : 𝒷) = qq M * qq N := by
    intro N M
    rw [hwdef]
    simp only [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right]
    rw [hsmsa N, ← mul_assoc, ← hadef, ← hbb,
      show sm M * (bb * bb) * sm N = (sm M * bb) * (bb * sm N) by noncomm_ring,
      hsb, hbs]
  have hmul_le : ∀ {N M : ℕ}, M ≤ N → qq M * qq N = qq M := fun {N M} hMN =>
    ((projection_below_effect (qq N) (qq M)
      ⟨(hqqproj N).nonneg, (hqqproj N).le_one⟩ (hqqproj M)).out 0 7).mp
      (hqqmono hMN)
  -- ultranorm Cauchy, norm bounded
  set F : Filter X := Filter.map w atTop with hFdef
  haveI hFne : F.NeBot := Filter.map_neBot
  have hwcau : UnCauchy (inner 𝒷 : X → X → 𝒷) F := by
    intro ω ε hε
    set r : ℕ → ℝ := fun N => (ω (qq N)).re with hrdef
    have hrmono : Monotone r := fun N M hNM => np_re_mono ω (hqqmono hNM)
    have hrbdd : BddAbove (Set.range r) := ⟨(ω q).re, by
      rintro x ⟨N, rfl⟩
      exact np_re_mono ω (hlub.1 ⟨N, rfl⟩)⟩
    have hrconv := tendsto_atTop_ciSup hrmono hrbdd
    have hσ : ∀ᶠ N in atTop, (⨆ i, r i) - ε ^ 2 < r N :=
      hrconv.eventually (lt_mem_nhds (by nlinarith))
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hσ
    have key : ∀ {N M : ℕ}, N₀ ≤ M → M ≤ N →
        unSeminorm ω (inner 𝒷 : X → X → 𝒷) (w N - w M) ≤ ε := by
      intro N M hN₀M hMN
      have hMN' : qq M * qq N = qq M := hmul_le hMN
      have hNM' : qq N * qq M = qq M := by
        have := congrArg star hMN'
        rwa [star_mul, (hqqproj N).isSelfAdjoint.star_eq,
          (hqqproj M).isSelfAdjoint.star_eq] at this
      have hinner : (inner 𝒷 (w N - w M) (w N - w M) : 𝒷) = qq N - qq M := by
        rw [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
          CStarModule.inner_sub_right, hww N N, hww N M, hww M N, hww M M,
          (hqqproj N).isIdempotentElem.eq, (hqqproj M).isIdempotentElem.eq,
          hMN', hNM']
        abel
      rw [unSeminorm, hinner]
      have h1 : (ω (qq N - qq M)).re = r N - r M := by
        rw [np_sub, Complex.sub_re]
      have h2 : r N - r M ≤ ε ^ 2 := by
        have h3 : r N ≤ ⨆ i, r i := le_ciSup hrbdd N
        have h4 := hN₀ M hN₀M
        linarith
      calc Real.sqrt (ω (qq N - qq M)).re ≤ Real.sqrt (ε ^ 2) := by
            rw [h1]; exact Real.sqrt_le_sqrt h2
        _ = ε := by rw [Real.sqrt_sq hε.le]
    refine ⟨w '' Set.Ici N₀, ?_, ?_⟩
    · rw [hFdef, Filter.mem_map]
      exact Filter.mem_of_superset (Filter.Ici_mem_atTop N₀)
        (Set.subset_preimage_image w _)
    · rintro x ⟨N, hN, rfl⟩ x' ⟨M, hM, rfl⟩
      rcases le_total M N with hMN | hNM
      · exact key hM hMN
      · have hkey := key hN hNM
        have hns : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (w N - w M)
            = unSeminorm ω (inner 𝒷 : X → X → 𝒷) (w M - w N) := by
          have h' := unSeminorm_neg' ω (cstarBInner 𝒷 X) (w M - w N)
          rw [neg_sub] at h'
          exact h'
        rw [hns]
        exact hkey
  have hwnorm : ∀ N, ‖w N‖ ≤ 1 := by
    intro N
    have h1 : ‖w N‖ = Real.sqrt ‖(inner 𝒷 (w N) (w N) : 𝒷)‖ :=
      CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷) (E := X) (w N)
    rw [h1, hww N N, (hqqproj N).isIdempotentElem.eq]
    have h2 : ‖qq N‖ ≤ 1 :=
      norm_le_one_of_mem_effects ⟨(hqqproj N).nonneg, hqle1 N⟩
    calc Real.sqrt ‖qq N‖ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h2
      _ = 1 := Real.sqrt_one
  obtain ⟨u, hu⟩ := h F hFne hwcau ⟨1, Set.range w, by
      rw [hFdef, Filter.mem_map]
      exact Filter.univ_mem' fun N => Set.mem_range_self N,
    by rintro x ⟨N, rfl⟩; exact hwnorm N⟩
  have huw : UnTendsto (inner 𝒷 : X → X → 𝒷) w atTop u := by
    intro ω
    have h1 := hu ω
    rwa [hFdef, Filter.tendsto_map'_iff] at h1
  -- the ultraweak limits of the partial sums
  have hqlim := uwTendsto_partialSums qq hqqmono
    (fun N => (hqqproj N).isSelfAdjoint) hqproj.isSelfAdjoint hlub bb
  have huu : (inner 𝒷 u u : 𝒷) = q := by
    have h1 : UWTendsto (fun N => (inner 𝒷 (w N) (w N) : 𝒷)) atTop
        (inner 𝒷 u u) :=
      innerprod_ultraweak (cstarBInner 𝒷 X) w w u u huw huw
    have h4 : (fun N => (inner 𝒷 (w N) (w N) : 𝒷)) = qq := by
      funext N
      rw [hww N N, (hqqproj N).isIdempotentElem.eq]
    rw [h4] at h1
    exact uwTendsto_unique' h1 hqlim.1
  have huy : (inner 𝒷 u y : 𝒷) = bb := by
    have hconst : UnTendsto (inner 𝒷 : X → X → 𝒷) (fun _ : ℕ => y) atTop y := by
      intro ω
      simp only [sub_self]
      have h0 : (inner 𝒷 (0 : X) (0 : X) : 𝒷) = 0 :=
        (cstarBInner 𝒷 X).inner_zero_left 0
      simp [unSeminorm, h0]
    have h1 : UWTendsto (fun N => (inner 𝒷 (w N) y : 𝒷)) atTop
        (inner 𝒷 u y) :=
      innerprod_ultraweak (cstarBInner 𝒷 X) w (fun _ => y) u y huw hconst
    have h4 : (fun N => (inner 𝒷 (w N) y : 𝒷)) = fun N => star bb * qq N := by
      funext N
      rw [hwdef]
      rw [CStarModule.inner_op_smul_left, hsmsa N, hbsa.star_eq, ← hbs N,
        ← hadef, ← hbb, mul_assoc]
    have h5 : star bb * q = bb := by rw [hbsa.star_eq, hbq]
    have h2 := hqlim.2
    rw [← h4, h5] at h2
    exact uwTendsto_unique' h1 h2
  refine ⟨u, huu, ?_, sm, huw⟩
  have e1 : (inner 𝒷 (bb • u) (bb • u) : 𝒷) = a := by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_left, huu,
      hbsa.star_eq, hqb, hbb]
  have e2 : (inner 𝒷 (bb • u) y : 𝒷) = a := by
    rw [CStarModule.inner_op_smul_left, huy, hbsa.star_eq, hbb]
  have e3 : (inner 𝒷 y (bb • u) : 𝒷) = a := by
    rw [CStarModule.inner_op_smul_right]
    have h6 : (inner 𝒷 y u : 𝒷) = bb := by
      have := congrArg star huy
      rwa [CStarModule.star_inner, hbsa.star_eq] at this
    rw [h6, hbb]
  have hz : (inner 𝒷 (bb • u - y) (bb • u - y) : 𝒷) = 0 := by
    rw [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
      CStarModule.inner_sub_right, e1, e2, e3, ← hadef]
    abel
  have := (CStarModule.inner_self (A := 𝒷)).mp hz
  rwa [sub_eq_zero] at this

/-- The Gram matrix of the partial sums of `∑ᵢ bᵢ • eᵢ` over an orthogonal
family (extracted from the proof of **149VIII** below, where it is used for
a maximal orthonormal *set*; the general family is what **160IV**.3 needs). -/
private theorem inner_sum_smul_cross [DecidableEq ι] {e : ι → X}
    (he : OrthogonalFam 𝒷 e) (bc : ι → 𝒷) (S T : Finset ι) :
    (inner 𝒷 (∑ i ∈ S, bc i • e i) (∑ j ∈ T, bc j • e j) : 𝒷)
      = ∑ j ∈ S ∩ T, bc j * (inner 𝒷 (e j) (e j) : 𝒷) * star (bc j) := by
  rw [CStarModule.inner_sum_right]
  have hj : ∀ j : ι, (inner 𝒷 (∑ i ∈ S, bc i • e i) (e j) : 𝒷)
      = if j ∈ S then (inner 𝒷 (e j) (e j) : 𝒷) * star (bc j) else 0 := by
    intro j
    rw [CStarModule.inner_sum_left]
    by_cases hjS : j ∈ S
    · rw [if_pos hjS, Finset.sum_eq_single_of_mem j hjS]
      · rw [CStarModule.inner_op_smul_left]
      · intro i _ hij
        rw [CStarModule.inner_op_smul_left, he i j hij, zero_mul]
    · rw [if_neg hjS, Finset.sum_eq_zero]
      intro i hiS
      rw [CStarModule.inner_op_smul_left,
        he i j (fun hh => hjS (hh ▸ hiS)), zero_mul]
  calc ∑ j ∈ T, (inner 𝒷 (∑ i ∈ S, bc i • e i) (bc j • e j) : 𝒷)
      = ∑ j ∈ T, if j ∈ S
          then bc j * (inner 𝒷 (e j) (e j) : 𝒷) * star (bc j) else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [CStarModule.inner_op_smul_right, hj j]
        by_cases hjS : j ∈ S
        · rw [if_pos hjS, if_pos hjS, ← mul_assoc]
        · rw [if_neg hjS, if_neg hjS, mul_zero]
    _ = ∑ j ∈ T ∩ S, bc j * (inner 𝒷 (e j) (e j) : 𝒷) * star (bc j) :=
        Finset.sum_ite_mem T S _
    _ = ∑ j ∈ S ∩ T, bc j * (inner 𝒷 (e j) (e j) : 𝒷) * star (bc j) := by
        rw [Finset.inter_comm]

/-- Clause (b) of `IsONBasis` holds for *every* orthonormal family in a
norm-bounded ultranorm complete module, not only for a maximal one: the
partial sums of `∑ᵢ bᵢ • eᵢ` are ultranorm Cauchy (the monotone bounded net
`Re ω(∑ᵢ bᵢ⟨eᵢ,eᵢ⟩bᵢ*)` of Gram values converges) and norm bounded, so they
converge.  Extracted from the proof of **149VIII** below; used there, and by
the relativized orthonormalization of **160IV**.3. -/
theorem exists_unTendsto_of_l2Summable [VonNeumannAlgebra 𝒷]
    (h : BddUnComplete 𝒷 X) {e : ι → X} (he : OrthonormalFam 𝒷 e)
    (bc : ι → 𝒷) (hbc : L2Summable 𝒷 bc) :
    ∃ x : X, UnTendsto (inner 𝒷 : X → X → 𝒷)
      (fun s : Finset ι => ∑ i ∈ s, bc i • e i) atTop x := by
  classical
  obtain ⟨M, hM⟩ := hbc
  set v : Finset ι → X := fun s => ∑ i ∈ s, bc i • e i with hvdef
  set G : Finset ι → 𝒷 :=
    fun s => ∑ i ∈ s, bc i * (inner 𝒷 (e i) (e i) : 𝒷) * star (bc i) with hGdef
  have hgram : ∀ S T, (inner 𝒷 (v S) (v T) : 𝒷)
      = ∑ j ∈ S ∩ T, bc j * (inner 𝒷 (e j) (e j) : 𝒷) * star (bc j) := by
    intro S T
    simp only [hvdef]
    exact inner_sum_smul_cross he.1 bc S T
  have hGterm : ∀ i : ι,
      (0 : 𝒷) ≤ bc i * (inner 𝒷 (e i) (e i) : 𝒷) * star (bc i) := fun i =>
    star_right_conjugate_nonneg (he.2 i).1.nonneg (bc i)
  have hGmono : ∀ {S T : Finset ι}, S ⊆ T → G S ≤ G T := fun {S T} hST =>
    Finset.sum_le_sum_of_subset_of_nonneg hST fun i _ _ => hGterm i
  have hGnn : ∀ S, (0 : 𝒷) ≤ G S := fun S =>
    Finset.sum_nonneg fun i _ => hGterm i
  have hGleM : ∀ S, ‖G S‖ ≤ M := by
    intro S
    have h1 : G S ≤ ∑ i ∈ S, bc i * star (bc i) := by
      refine Finset.sum_le_sum fun i _ => ?_
      calc bc i * (inner 𝒷 (e i) (e i) : 𝒷) * star (bc i)
          ≤ bc i * 1 * star (bc i) :=
            star_right_conjugate_le_conjugate (he.2 i).1.le_one (bc i)
        _ = bc i * star (bc i) := by rw [mul_one]
    exact le_trans
      (CStarAlgebra.norm_le_norm_of_nonneg_of_le (hGnn S) h1) (hM S)
  set F : Filter X := Filter.map v atTop with hFdef
  haveI hFne : F.NeBot := Filter.map_neBot
  have hvcau : UnCauchy (inner 𝒷 : X → X → 𝒷) F := by
    intro ω ε hε
    set g : Finset ι → ℝ := fun S => (ω (G S)).re with hgdef
    have hgmono : ∀ {S T : Finset ι}, S ⊆ T → g S ≤ g T :=
      fun hST => np_re_mono ω (hGmono hST)
    have hgbdd : BddAbove (Set.range g) := ⟨M * (ω 1).re, by
      rintro r ⟨S, rfl⟩
      have h1 : G S ≤ (‖G S‖ : ℝ) • (1 : 𝒷) := le_norm_smul_one (hGnn S)
      have h2 := np_re_mono ω h1
      rw [np_re_smul] at h2
      have h3 : (0 : ℝ) ≤ (ω 1).re := np_re_nonneg ω zero_le_one
      calc g S ≤ ‖G S‖ * (ω 1).re := h2
        _ ≤ M * (ω 1).re := mul_le_mul_of_nonneg_right (hGleM S) h3⟩
    set σ : ℝ := sSup (Set.range g) with hσdef
    have hne' : (Set.range g).Nonempty := ⟨g ∅, ⟨∅, rfl⟩⟩
    obtain ⟨r₀, ⟨S₀, rfl⟩, hS₀⟩ := exists_lt_of_lt_csSup hne'
      (show σ - ε ^ 2 / 2 < σ by nlinarith)
    refine ⟨v '' Set.Ici S₀, ?_, ?_⟩
    · rw [hFdef, Filter.mem_map]
      exact Filter.mem_of_superset (Filter.Ici_mem_atTop S₀)
        (Set.subset_preimage_image v _)
    · rintro z ⟨S, hS, rfl⟩ z' ⟨T, hT, rfl⟩
      have hSS : S₀ ⊆ S ∩ T := Finset.subset_inter hS hT
      have hinner : (inner 𝒷 (v S - v T) (v S - v T) : 𝒷)
          = G S + G T - G (S ∩ T) - G (S ∩ T) := by
        rw [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
          CStarModule.inner_sub_right, hgram S S, hgram S T, hgram T S,
          hgram T T, Finset.inter_self, Finset.inter_self,
          Finset.inter_comm T S]
        simp only [hGdef]
        abel
      have hre : (ω (inner 𝒷 (v S - v T) (v S - v T) : 𝒷)).re
          = g S + g T - g (S ∩ T) - g (S ∩ T) := by
        rw [hinner, np_sub, np_sub,
          show ω (G S + G T) = ω (G S) + ω (G T) from
            map_add ω.toPositiveLinearMap _ _,
          Complex.sub_re, Complex.sub_re, Complex.add_re]
      have hbound : g S + g T - g (S ∩ T) - g (S ∩ T) ≤ ε ^ 2 := by
        have h1 : g S ≤ σ := le_csSup hgbdd ⟨S, rfl⟩
        have h2 : g T ≤ σ := le_csSup hgbdd ⟨T, rfl⟩
        have h3 : σ - ε ^ 2 / 2 < g (S ∩ T) :=
          lt_of_lt_of_le hS₀ (hgmono hSS)
        linarith
      rw [unSeminorm]
      calc Real.sqrt (ω (inner 𝒷 (v S - v T) (v S - v T) : 𝒷)).re
          ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt (by rw [hre]; exact hbound)
        _ = ε := Real.sqrt_sq hε.le
  have hvnorm : ∀ S, ‖v S‖ ≤ Real.sqrt M := by
    intro S
    have h1 : ‖v S‖ = Real.sqrt ‖(inner 𝒷 (v S) (v S) : 𝒷)‖ :=
      CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷) (E := X) (v S)
    have h2 : (inner 𝒷 (v S) (v S) : 𝒷) = G S := by
      rw [hgram S S, Finset.inter_self]
    rw [h1, h2]
    exact Real.sqrt_le_sqrt (hGleM S)
  obtain ⟨x, hx⟩ := h F hFne hvcau ⟨Real.sqrt M, Set.range v, by
      rw [hFdef, Filter.mem_map]
      exact Filter.univ_mem' fun S => Set.mem_range_self S,
    by rintro z ⟨S, rfl⟩; exact hvnorm S⟩
  refine ⟨x, fun ω => ?_⟩
  have h1 := hx ω
  rwa [hFdef, Filter.tendsto_map'_iff] at h1

/-- The coefficients of an ultranorm-convergent sum `∑ᵢ bᵢ • eᵢ` over an
orthonormal family are the `bᵢ` again, provided each `bᵢ` is absorbed by
`⟨eᵢ,eᵢ⟩` (which holds for `bᵢ = ⟨eᵢ,x⟩` by `onbasis_coef_absorb`).
Extracted from the proof of **149VIII** below. -/
theorem inner_of_unTendsto_sum_smul [VonNeumannAlgebra 𝒷] {e : ι → X}
    (he : OrthonormalFam 𝒷 e) (bc : ι → 𝒷)
    (habs : ∀ i, bc i * (inner 𝒷 (e i) (e i) : 𝒷) = bc i) {y : X}
    (hy : UnTendsto (inner 𝒷 : X → X → 𝒷)
      (fun s : Finset ι => ∑ i ∈ s, bc i • e i) atTop y) (j : ι) :
    (inner 𝒷 (e j) y : 𝒷) = bc j := by
  classical
  have hconstj : UnTendsto (inner 𝒷 : X → X → 𝒷)
      (fun _ : Finset ι => e j) atTop (e j) := by
    intro ω
    simp only [sub_self]
    have h0 : (inner 𝒷 (0 : X) (0 : X) : 𝒷) = 0 :=
      (cstarBInner 𝒷 X).inner_zero_left 0
    simp [unSeminorm, h0]
  have h1 : UWTendsto (fun S : Finset ι =>
      (inner 𝒷 (e j) (∑ i ∈ S, bc i • e i) : 𝒷)) atTop (inner 𝒷 (e j) y) :=
    innerprod_ultraweak (cstarBInner 𝒷 X) _ _ _ _ hconstj hy
  have h2 : (fun S : Finset ι => (inner 𝒷 (e j) (∑ i ∈ S, bc i • e i) : 𝒷))
      =ᶠ[atTop] fun _ => bc j := by
    filter_upwards [Filter.Ici_mem_atTop ({j} : Finset ι)] with S hS
    have hjS : j ∈ S := Finset.singleton_subset_iff.mp hS
    rw [CStarModule.inner_sum_right, Finset.sum_eq_single_of_mem j hjS]
    · rw [CStarModule.inner_op_smul_right]
      exact habs j
    · intro i _ hij
      rw [CStarModule.inner_op_smul_right, he.1 j i (Ne.symm hij), mul_zero]
  exact uwTendsto_unique' (Filter.Tendsto.congr' h2 h1) (uwTendsto_const atTop _)

/-- The isometric part `u` of the polar decomposition of `y` is orthogonal
to everything `y` is orthogonal to.  Extracted from the proof of **149VIII**
below, where it rules out a non-zero remainder; the argument is the
cancellation `⟨z,u⟩ = ⟨z,u⟩⟨u,u⟩` of **60VIII** `mult_cancellation_1`
through `⌈·⌋⌊·⌉`. -/
theorem inner_eq_zero_of_polar [VonNeumannAlgebra 𝒷] {y u : X}
    (huu : (inner 𝒷 u u : 𝒷) = suppProj (CFC.sqrt (inner 𝒷 y y : 𝒷)))
    (hbu : CFC.sqrt (inner 𝒷 y y : 𝒷) • u = y) {z : X}
    (hz : (inner 𝒷 z y : 𝒷) = 0) : (inner 𝒷 z u : 𝒷) = 0 := by
  have hqproj : IsStarProjection (inner 𝒷 u u : 𝒷) := by
    rw [huu]; exact (ceill_basic_1 _).1.1
  rw [← hbu, CStarModule.inner_op_smul_right] at hz
  have h2 : suppProj (CFC.sqrt (inner 𝒷 y y : 𝒷))
      * rangeProj (inner 𝒷 z u : 𝒷) = 0 :=
    ((mult_cancellation_1 ((inner 𝒷 z u : 𝒷))
      (CFC.sqrt (inner 𝒷 y y : 𝒷))).out 0 1).mp hz
  have h3 : rangeProj (inner 𝒷 z u : 𝒷) * (inner 𝒷 z u : 𝒷)
      = (inner 𝒷 z u : 𝒷) := (ceill_basic_2 _).1.2
  have h4 : (inner 𝒷 u u : 𝒷) • u = u := mod_projelabs u hqproj
  calc (inner 𝒷 z u : 𝒷)
      = inner 𝒷 z ((inner 𝒷 u u : 𝒷) • u) := by rw [h4]
    _ = (inner 𝒷 u u : 𝒷) * inner 𝒷 z u := CStarModule.inner_op_smul_right
    _ = suppProj (CFC.sqrt (inner 𝒷 y y : 𝒷))
        * (rangeProj (inner 𝒷 z u : 𝒷) * (inner 𝒷 z u : 𝒷)) := by rw [huu, h3]
    _ = (suppProj (CFC.sqrt (inner 𝒷 y y : 𝒷))
        * rangeProj (inner 𝒷 z u : 𝒷)) * (inner 𝒷 z u : 𝒷) := by rw [mul_assoc]
    _ = 0 := by rw [h2, zero_mul]

/-- **149VIII** (`selfdual-bcompl-then-basis`, dils.tex:2354): (3) ⇒ (4) of
**149V** — a norm-bounded ultranorm complete pre-Hilbert 𝒷-module has an
orthonormal basis.

Divergence class 1 (faithful), mirrored.  A maximal orthonormal set `E`
exists by Zorn; the summability clause (b) holds because the partial sums of
`∑ₑ e bₑ` are ultranorm Cauchy (the monotone bounded net `Re ω(∑ bₑ⟨e,e⟩bₑ*)`
of Gram values converges) and norm bounded, so they converge by (3); and a
non-zero `x' = x − ∑ₑ e⟨e,x⟩` is ruled out by *polar decomposition*
(`polar_decomposition` above, resting on **80IV**
`Theses.A.VN.approximate_pseudoinverse`), whose isometric part `u` would
extend `E`.  Where the thesis writes `x' = u⟨x',x'⟩^½`, the mirror image is
`x' = ⟨x',x'⟩^½ • u`, and the closing cancellation `⟨e,u⟩ = ⟨e,u⟩⟨u,u⟩` uses
**60VIII** `mult_cancellation_1` through `⌈·⌋⌊·⌉`. -/
theorem exists_isONBasis_of_bddUnComplete [VonNeumannAlgebra 𝒷]
    (h : BddUnComplete 𝒷 X) :
    ∃ (ι' : Type v) (e : ι' → X), IsONBasis 𝒷 e := by
  classical
  -- Zorn's lemma: a maximal orthonormal subset of `X`
  obtain ⟨E, hEmax⟩ := zorn_subset
    {E : Set X | (∀ x ∈ E, ∀ y ∈ E, x ≠ y → (inner 𝒷 x y : 𝒷) = 0)
      ∧ ∀ x ∈ E, IsStarProjection (inner 𝒷 x x : 𝒷) ∧ (inner 𝒷 x x : 𝒷) ≠ 0}
    (fun c hc hchain => by
      refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
      · rintro x ⟨s₁, hs₁, hxs₁⟩ y ⟨s₂, hs₂, hys₂⟩ hxy
        rcases hchain.total hs₁ hs₂ with h12 | h21
        · exact (hc hs₂).1 x (h12 hxs₁) y hys₂ hxy
        · exact (hc hs₁).1 x hxs₁ y (h21 hys₂) hxy
      · rintro x ⟨s₁, hs₁, hxs₁⟩
        exact (hc hs₁).2 x hxs₁)
  have hE := hEmax.1
  have horth : OrthonormalFam 𝒷 (fun i : E => (i : X)) := by
    constructor
    · intro i j hij
      exact hE.1 (i : X) i.2 (j : X) j.2 fun hh => hij (Subtype.ext hh)
    · intro i
      exact hE.2 (i : X) i.2
  -- clause (b): ℓ²-summable families are summable, by norm-bounded
  -- ultranorm completeness (`exists_unTendsto_of_l2Summable` above)
  have hclauseb : ∀ bc : ↥E → 𝒷, L2Summable 𝒷 bc →
      ∃ x : X, UnTendsto (inner 𝒷 : X → X → 𝒷)
        (fun s : Finset ↥E => ∑ i ∈ s, bc i • (i : X)) atTop x :=
    fun bc hbc => exists_unTendsto_of_l2Summable h horth bc hbc
  -- clause (a): every `x` is the sum of its coefficients over `E`
  have hclausea : ∀ x : X, UnTendsto (inner 𝒷 : X → X → 𝒷)
      (fun s : Finset ↥E => ∑ i ∈ s, (inner 𝒷 ((i : X)) x : 𝒷) • (i : X))
      atTop x := by
    intro x
    have hcfL2 : L2Summable 𝒷 (fun i : ↥E => (inner 𝒷 ((i : X)) x : 𝒷)) := by
      refine ⟨‖(inner 𝒷 x x : 𝒷)‖, fun s => ?_⟩
      have h1 : ∑ i ∈ s, (inner 𝒷 ((i : X)) x : 𝒷) * star (inner 𝒷 ((i : X)) x : 𝒷)
          = ∑ i ∈ s, (inner 𝒷 ((i : X)) x : 𝒷) * (inner 𝒷 x ((i : X)) : 𝒷) :=
        Finset.sum_congr rfl fun i _ => by rw [CStarModule.star_inner]
      rw [h1]
      have h3 : (0 : 𝒷) ≤ ∑ i ∈ s,
          (inner 𝒷 ((i : X)) x : 𝒷) * (inner 𝒷 x ((i : X)) : 𝒷) := by
        rw [← h1]
        exact Finset.sum_nonneg fun i _ => mul_star_self_nonneg _
      exact CStarAlgebra.norm_le_norm_of_nonneg_of_le h3 (mod_bessel horth x s)
    obtain ⟨y, hy⟩ := hclauseb _ hcfL2
    -- the coefficients of the sum `y` agree with those of `x`
    have hcoefy : ∀ j : ↥E, (inner 𝒷 ((j : X)) y : 𝒷) = inner 𝒷 ((j : X)) x :=
      fun j => inner_of_unTendsto_sum_smul horth _
        (fun i => onbasis_coef_absorb horth x i) hy j
    -- a non-zero remainder would extend `E`, contradicting maximality
    have hxy : x - y = 0 := by
      by_contra hne
      obtain ⟨u, huu, hbu, -⟩ := polar_decomposition h (x - y)
      have ha'ne : (inner 𝒷 (x - y) (x - y) : 𝒷) ≠ 0 := fun h0 =>
        hne ((CStarModule.inner_self (A := 𝒷)).mp h0)
      have hbne : CFC.sqrt (inner 𝒷 (x - y) (x - y) : 𝒷) ≠ 0 := by
        intro h0
        refine ha'ne ?_
        rw [← CFC.sqrt_mul_sqrt_self (inner 𝒷 (x - y) (x - y) : 𝒷)
          CStarModule.inner_self_nonneg, h0, mul_zero]
      have hqproj : IsStarProjection (inner 𝒷 u u : 𝒷) := by
        rw [huu]
        exact (ceill_basic_1 _).1.1
      have hqne : (inner 𝒷 u u : 𝒷) ≠ 0 := by
        rw [huu]
        intro h0
        have h1 := (ceill_basic_1 (CFC.sqrt (inner 𝒷 (x - y) (x - y) : 𝒷))).1.2
        rw [h0, mul_zero] at h1
        exact hbne h1.symm
      have horthu : ∀ j : ↥E, (inner 𝒷 ((j : X)) u : 𝒷) = 0 := by
        intro j
        refine inner_eq_zero_of_polar huu hbu ?_
        rw [CStarModule.inner_sub_right, hcoefy j, sub_self]
      have huE : u ∉ E := fun huE => hqne (horthu ⟨u, huE⟩)
      have hEu : (insert u E) ∈ {E' : Set X |
          (∀ x' ∈ E', ∀ y' ∈ E', x' ≠ y' → (inner 𝒷 x' y' : 𝒷) = 0)
          ∧ ∀ x' ∈ E', IsStarProjection (inner 𝒷 x' x' : 𝒷)
            ∧ (inner 𝒷 x' x' : 𝒷) ≠ 0} := by
        constructor
        · rintro x' (rfl | hx') y' (rfl | hy') hne'
          · exact absurd rfl hne'
          · have h5 := congrArg star (horthu ⟨y', hy'⟩)
            rwa [CStarModule.star_inner, star_zero] at h5
          · exact horthu ⟨x', hx'⟩
          · exact hE.1 x' hx' y' hy' hne'
        · rintro x' (rfl | hx')
          · exact ⟨hqproj, hqne⟩
          · exact hE.2 x' hx'
      have hsub : insert u E ⊆ E := hEmax.2 hEu (Set.subset_insert u E)
      exact huE (hsub (Set.mem_insert u E))
    have hxeq : x = y := by rwa [sub_eq_zero] at hxy
    rwa [← hxeq] at hy
  exact ⟨↥E, fun i => (i : X), horth, hclausea, hclauseb⟩

/-- **149IX** (dils.tex:2487): (4) ⇒ (2) of **149V** — a pre-Hilbert
𝒷-module with an orthonormal basis is ultranorm complete.

Divergence class 1 (faithful), mirrored.  The limit is `∑ₑ e bₑ` with
`bₑ = uslim_α ⟨e, x_α⟩`, whose mirror image is `bₑ = (uslim_α [x_α, e])*` —
it is the net `[x_α, e]` of *starred* coefficients that is ultrastrong
Cauchy (by **142III**), converging by **77I**.1 `Theses.A.VN.vn_complete_1`.
The ℓ²-summability of `(bₑ)ₑ` follows from an ultraweak bound (Bessel at
approximants) through **87VIII**
`Theses.A.VN.ultraweakly_bounded_implies_bounded`; where the thesis sums
Parseval tails, we bound `x_α − ∑ₑ eb_ₑ` at a *finite* stage `S` by the four
terms `x_α − P_S x_α`, `P_S(x_α − x_β)`, `∑_{S} e(⟨e,x_β⟩ − b_e)` and
`∑_S eb_e − t`, with `x_β` chosen late — same estimates, no infinite sums. -/
theorem unComplete_of_isONBasis [VonNeumannAlgebra 𝒷] {e : ι → X}
    (he : IsONBasis 𝒷 e) : UnComplete (inner 𝒷 : X → X → 𝒷) := by
  classical
  intro F hF hcauchy
  haveI : F.NeBot := hF
  -- (1) the mirrored coefficients `[z, eᵢ]` converge ultrastrongly along `F`
  have hexist : ∀ i : ι, ∃ c : 𝒷,
      USTendsto (fun z : X => (inner 𝒷 z (e i) : 𝒷)) F c := fun i =>
    vn_complete_1 F _ fun ω => unCauchy_inner_tendsto hcauchy (e i) ω
  choose c hc using hexist
  set b : ι → 𝒷 := fun i => star (c i) with hbdef
  -- coefficient-approximation sets are in `F`
  have hcoef : ∀ (ω : NPFunctional 𝒷) (S : Finset ι) (δ : ℝ), 0 < δ →
      ∀ᶠ z in F, ∀ i ∈ S,
        omegaNorm 𝒷 ω ((inner 𝒷 z (e i) : 𝒷) - c i) < δ := by
    intro ω S δ hδ
    refine (Filter.eventually_all_finset S).mpr fun i _ => ?_
    exact ((usTendsto_iff _ _ _).mp (hc i) ω).eventually (gt_mem_nhds hδ)
  -- (2) the coefficients are ℓ²-summable, via the ultraweak bound (**87VIII**)
  have hL2 : L2Summable 𝒷 b := by
    have hub : ∀ ω : NPFunctional 𝒷, BddAbove
        (Set.range fun S : Finset ι => ‖ω (∑ i ∈ S, b i * star (b i))‖) := by
      intro ω
      obtain ⟨s₁, hs₁F, hs₁⟩ := hcauchy ω 1 one_pos
      obtain ⟨z₀, hz₀⟩ := Filter.nonempty_of_mem hs₁F
      set K : ℝ := unSeminorm ω (inner 𝒷 : X → X → 𝒷) z₀ + 1 with hK
      have hKz : ∀ z ∈ s₁, unSeminorm ω (inner 𝒷 : X → X → 𝒷) z ≤ K := by
        intro z hz
        have h1 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) z
            ≤ unSeminorm ω (inner 𝒷 : X → X → 𝒷) (z - z₀)
              + unSeminorm ω (inner 𝒷 : X → X → 𝒷) z₀ := by
          have := unSeminorm_add_le ω (cstarBInner 𝒷 X) (z - z₀) z₀
          rwa [sub_add_cancel] at this
        have h2 := hs₁ z hz z₀ hz₀
        rw [hK]; linarith
      refine ⟨2 * K ^ 2 + 2, ?_⟩
      rintro r ⟨S, rfl⟩
      set δ : ℝ := (1 + (S.card : ℝ))⁻¹ with hδdef
      have hδpos : 0 < δ := by positivity
      have hmulδ : (1 + (S.card : ℝ)) * δ = 1 :=
        mul_inv_cancel₀ (by positivity)
      have hcard0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
      have hδ1 : δ ≤ 1 := by nlinarith
      have hcardδ : (S.card : ℝ) * δ ^ 2 ≤ 1 := by nlinarith [sq_nonneg δ]
      obtain ⟨z, hzs, hzc⟩ :=
        Filter.nonempty_of_mem (Filter.inter_mem hs₁F (hcoef ω S δ hδpos))
      -- pointwise: `‖cᵢ‖_ω ≤ ‖[z,eᵢ]‖_ω + δ`
      have hci : ∀ i ∈ S, omegaNorm 𝒷 ω (c i)
          ≤ omegaNorm 𝒷 ω (inner 𝒷 z (e i)) + δ := by
        intro i hi
        have h1 := omegaNorm_sub_le ω (c i) (inner 𝒷 z (e i)) 0
        rw [sub_zero, sub_zero] at h1
        have h2 : omegaNorm 𝒷 ω (c i - inner 𝒷 z (e i)) ≤ δ := by
          have h3 := hzc i hi
          rw [show c i - (inner 𝒷 z (e i) : 𝒷)
            = -((inner 𝒷 z (e i) : 𝒷) - c i) by abel, omegaNorm_neg]
          linarith
        linarith
      -- Bessel at `z`: `∑_{i∈S} ‖[z,eᵢ]‖_ω² ≤ ‖z‖_ω² ≤ K²`
      have hbes : ∑ i ∈ S, omegaNorm 𝒷 ω ((inner 𝒷 z (e i) : 𝒷)) ^ 2
          ≤ K ^ 2 := by
        have h1 : ∀ i : ι, omegaNorm 𝒷 ω ((inner 𝒷 z (e i) : 𝒷)) ^ 2
            = (ω ((inner 𝒷 (e i) z : 𝒷) * inner 𝒷 z (e i))).re := by
          intro i
          rw [omegaNorm, Real.sq_sqrt (np_re_nonneg ω (star_mul_self_nonneg _)),
            CStarModule.star_inner]
        have h2 : ω (∑ i ∈ S, (inner 𝒷 (e i) z : 𝒷) * inner 𝒷 z (e i))
            = ∑ i ∈ S, ω ((inner 𝒷 (e i) z : 𝒷) * inner 𝒷 z (e i)) :=
          map_sum ω.toPositiveLinearMap _ S
        have h3 := np_re_mono ω (mod_bessel he.1 z S)
        rw [h2, Complex.re_sum] at h3
        have h4 : (ω (inner 𝒷 z z : 𝒷)).re
            = unSeminorm ω (inner 𝒷 : X → X → 𝒷) z ^ 2 :=
          (unSeminorm_sq ω (cstarBInner 𝒷 X) z).symm
        have h5 := hKz z hzs
        have h6 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) z ^ 2 ≤ K ^ 2 := by
          nlinarith [unSeminorm_nonneg ω (inner 𝒷 : X → X → 𝒷) z]
        calc ∑ i ∈ S, omegaNorm 𝒷 ω ((inner 𝒷 z (e i) : 𝒷)) ^ 2
            = ∑ i ∈ S, (ω ((inner 𝒷 (e i) z : 𝒷) * inner 𝒷 z (e i))).re :=
              Finset.sum_congr rfl fun i _ => h1 i
          _ ≤ (ω (inner 𝒷 z z : 𝒷)).re := h3
          _ = unSeminorm ω (inner 𝒷 : X → X → 𝒷) z ^ 2 := h4
          _ ≤ K ^ 2 := h6
      -- assemble the ultraweak bound
      have hpos : (0 : 𝒷) ≤ ∑ i ∈ S, b i * star (b i) :=
        Finset.sum_nonneg fun i _ => mul_star_self_nonneg (b i)
      show ‖ω (∑ i ∈ S, b i * star (b i))‖ ≤ 2 * K ^ 2 + 2
      rw [norm_np_eq_re ω hpos]
      have hexp : (ω (∑ i ∈ S, b i * star (b i))).re
          = ∑ i ∈ S, omegaNorm 𝒷 ω (c i) ^ 2 := by
        have h1 : ω (∑ i ∈ S, b i * star (b i))
            = ∑ i ∈ S, ω (b i * star (b i)) :=
          map_sum ω.toPositiveLinearMap _ S
        rw [h1, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [omegaNorm, Real.sq_sqrt (np_re_nonneg ω (star_mul_self_nonneg _))]
        congr 2
        rw [hbdef]
        simp
      rw [hexp]
      have hterm : ∀ i ∈ S, omegaNorm 𝒷 ω (c i) ^ 2
          ≤ 2 * omegaNorm 𝒷 ω (inner 𝒷 z (e i)) ^ 2 + 2 * δ ^ 2 := by
        intro i hi
        have h := hci i hi
        nlinarith [omegaNorm_nonneg (A := 𝒷) ω (c i),
          omegaNorm_nonneg (A := 𝒷) ω (inner 𝒷 z (e i)),
          sq_nonneg (omegaNorm 𝒷 ω (inner 𝒷 z (e i)) - δ)]
      calc ∑ i ∈ S, omegaNorm 𝒷 ω (c i) ^ 2
          ≤ ∑ i ∈ S, (2 * omegaNorm 𝒷 ω (inner 𝒷 z (e i)) ^ 2 + 2 * δ ^ 2) :=
            Finset.sum_le_sum hterm
        _ = 2 * (∑ i ∈ S, omegaNorm 𝒷 ω ((inner 𝒷 z (e i) : 𝒷)) ^ 2)
            + 2 * ((S.card : ℝ) * δ ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
              nsmul_eq_mul]
            ring
        _ ≤ 2 * K ^ 2 + 2 := by nlinarith
    obtain ⟨M, hM⟩ := ultraweakly_bounded_implies_bounded
      (fun S : Finset ι => ∑ i ∈ S, b i * star (b i)) hub
    exact ⟨M, fun S => hM ⟨S, rfl⟩⟩
  -- (3) the candidate limit
  obtain ⟨t, ht⟩ := he.2.2 b hL2
  refine ⟨t, fun ω => ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / 8 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨s₀, hs₀F, hs₀⟩ := hcauchy ω δ hδpos
  obtain ⟨S₀, hS₀⟩ :=
    Filter.eventually_atTop.mp ((ht ω).eventually (gt_mem_nhds hδpos))
  -- (4) every `z ∈ s₀` is `6δ`-close to `t`
  have hclaim : ∀ z ∈ s₀,
      unSeminorm ω (inner 𝒷 : X → X → 𝒷) (z - t) ≤ 6 * δ := by
    intro z hz
    obtain ⟨S₁', hS₁'⟩ := Filter.eventually_atTop.mp
      (((he.2.1 z) ω).eventually (gt_mem_nhds hδpos))
    set S : Finset ι := S₀ ∪ S₁' with hSdef
    set P : X := ∑ i ∈ S, (inner 𝒷 (e i) z : 𝒷) • e i with hPdef
    set V : X := ∑ i ∈ S, b i • e i with hVdef
    have hT1 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (P - z) < δ :=
      hS₁' S le_sup_right
    have hT4 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (V - t) < δ :=
      hS₀ S le_sup_left
    -- late choice of `β`
    set δ' : ℝ := δ / (S.card + 1) with hδ'def
    have hδ'pos : 0 < δ' := by positivity
    obtain ⟨β, hβs, hβc⟩ :=
      Filter.nonempty_of_mem (Filter.inter_mem hs₀F (hcoef ω S δ' hδ'pos))
    -- middle terms
    set Q : X := ∑ i ∈ S, (inner 𝒷 (e i) β : 𝒷) • e i with hQdef
    have hT2 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (P - Q) ≤ δ := by
      have h1 : P - Q = ∑ i ∈ S, (inner 𝒷 (e i) (z - β) : 𝒷) • e i := by
        rw [hPdef, hQdef, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [CStarModule.inner_sub_right, sub_smul']
      rw [h1]
      exact le_trans (unSeminorm_coeff_sum_le he.1 ω (z - β) S)
        (hs₀ z hz β hβs)
    have hT3 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (Q - V) ≤ δ := by
      have h1 : Q - V = ∑ i ∈ S, ((inner 𝒷 (e i) β : 𝒷) - b i) • e i := by
        rw [hQdef, hVdef, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => (sub_smul' _ _ _).symm
      have hterm : ∀ i ∈ S, unSeminorm ω (inner 𝒷 : X → X → 𝒷)
          (((inner 𝒷 (e i) β : 𝒷) - b i) • e i) ≤ δ' := by
        intro i hi
        refine (unSeminorm_smul_proj_le (he.1.2 i).1 ω _).trans ?_
        have hstar : star ((inner 𝒷 (e i) β : 𝒷) - b i)
            = (inner 𝒷 β (e i) : 𝒷) - c i := by
          rw [star_sub, CStarModule.star_inner, hbdef]
          simp
        rw [hstar]
        exact (hβc i hi).le
      have hmulδ' : ((S.card : ℝ) + 1) * δ' = δ := by
        rw [hδ'def]; field_simp
      have h2 : ∑ i ∈ S, unSeminorm ω (inner 𝒷 : X → X → 𝒷)
          (((inner 𝒷 (e i) β : 𝒷) - b i) • e i) ≤ (S.card : ℝ) * δ' := by
        refine le_trans (Finset.sum_le_sum hterm) ?_
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [h1]
      refine le_trans (unSeminorm_sum_le ω S _) (le_trans h2 ?_)
      nlinarith [hδ'pos.le]
    -- assemble via the triangle inequality
    have hd1 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (z - t)
        ≤ unSeminorm ω (inner 𝒷 : X → X → 𝒷) (-(P - z) + (P - Q) + (Q - V))
          + unSeminorm ω (inner 𝒷 : X → X → 𝒷) (V - t) := by
      have h := unSeminorm_add_le ω (cstarBInner 𝒷 X)
        (-(P - z) + (P - Q) + (Q - V)) (V - t)
      rw [show -(P - z) + (P - Q) + (Q - V) + (V - t) = z - t by abel] at h
      exact h
    have hd2 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (-(P - z) + (P - Q) + (Q - V))
        ≤ unSeminorm ω (inner 𝒷 : X → X → 𝒷) (-(P - z) + (P - Q))
          + unSeminorm ω (inner 𝒷 : X → X → 𝒷) (Q - V) :=
      unSeminorm_add_le ω (cstarBInner 𝒷 X) _ _
    have hd3 : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (-(P - z) + (P - Q))
        ≤ unSeminorm ω (inner 𝒷 : X → X → 𝒷) (-(P - z))
          + unSeminorm ω (inner 𝒷 : X → X → 𝒷) (P - Q) :=
      unSeminorm_add_le ω (cstarBInner 𝒷 X) _ _
    have hneg : unSeminorm ω (inner 𝒷 : X → X → 𝒷) (-(P - z))
        = unSeminorm ω (inner 𝒷 : X → X → 𝒷) (P - z) :=
      unSeminorm_neg' ω (cstarBInner 𝒷 X) _
    rw [hneg] at hd3
    linarith [hT1.le, hT2, hT3, hT4.le]
  filter_upwards [hs₀F] with z hz
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (unSeminorm_nonneg _ _ _)]
  calc unSeminorm ω (inner 𝒷 : X → X → 𝒷) (id z - t) ≤ 6 * δ := hclaim z hz
    _ < ε := by rw [hδdef]; linarith

omit [StarOrderedRing 𝒷] in
/-- **149X** (dils.tex:2573): (2) ⇒ (3) of **149V** — trivially, since a
norm-bounded ultranorm-Cauchy filter is in particular ultranorm Cauchy. -/
theorem bddUnComplete_of_unComplete (h : UnComplete (inner 𝒷 : X → X → 𝒷)) :
    BddUnComplete 𝒷 X :=
  fun F hF hCauchy _ => h F hF hCauchy

/-- **149XI** (dils.tex:2577): (4) ⇒ (1) of **149V** — a pre-Hilbert
𝒷-module with an orthonormal basis is self dual.

Divergence class 1 (faithful).  Given a bounded 𝒷-linear `τ : X → 𝒷`, the
candidate is `t = ∑ᵢ eᵢ τ(eᵢ)*` (mirrored: `∑ᵢ τ(eᵢ)* • eᵢ`), which exists by
clause (b) of `IsONBasis` once `(τ(eᵢ)*)ᵢ` is shown ℓ²-summable; the thesis's
argument for that is the "substitute the partial sum for `x`" trick, which
gives `‖∑_{i∈S} τ(eᵢ)* • eᵢ‖ ≤ ‖τ‖` and rests on Bessel (`mod_bessel`).  The
identification `τ x = ⟨t,x⟩` is then ultranorm continuity of `τ` (**148I**)
against **148V**, both read off in the ultraweak topology, where limits are
unique. -/
theorem selfDual_of_isONBasis [VonNeumannAlgebra 𝒷] {e : ι → X}
    (he : IsONBasis 𝒷 e) : SelfDual 𝒷 X := by
  rintro τ hmod ⟨C₀, hC₀⟩
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : (0 : ℝ) ≤ C := le_max_right _ _
  have hC : ∀ x, ‖τ x‖ ≤ C * ‖x‖ := fun x =>
    (hC₀ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  have hp : ∀ i, IsStarProjection (inner 𝒷 (e i) (e i) : 𝒷) := fun i => (he.1.2 i).1
  -- the candidate coefficients `bᵢ = τ(eᵢ)*`
  set b : ι → 𝒷 := fun i => star (τ (e i)) with hbdef
  have hbabs : ∀ i, b i * inner 𝒷 (e i) (e i) = b i := by
    intro i
    have h1 : τ (e i) = (inner 𝒷 (e i) (e i) : 𝒷) * τ (e i) := by
      conv_lhs => rw [← mod_projelabs (e i) (hp i)]
      exact hmod _ _
    have h2 := congrArg star h1
    rw [star_mul, (hp i).isSelfAdjoint.star_eq] at h2
    exact h2.symm
  set v : Finset ι → X := fun s => ∑ i ∈ s, b i • e i with hvdef
  have hvv : ∀ s, (inner 𝒷 (v s) (v s) : 𝒷) = ∑ i ∈ s, b i * star (b i) :=
    fun s => inner_sum_smul_self he.1.1 b hbabs s
  -- `⟨∑_{i∈S} eᵢτ(eᵢ)*, y⟩ = τ (∑_{i∈S} eᵢ⟨eᵢ,y⟩)`
  have hkey1 : ∀ (s : Finset ι) (y : X),
      (inner 𝒷 (v s) y : 𝒷) = τ (∑ i ∈ s, (inner 𝒷 (e i) y : 𝒷) • e i) := by
    intro s y
    rw [map_sum, hvdef, CStarModule.inner_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [CStarModule.inner_op_smul_left, hbdef, hmod]
    simp
  -- Bessel: the partial sums of `∑ᵢ eᵢ⟨eᵢ,y⟩` are norm-bounded by `‖y‖`
  have hkey2 : ∀ (s : Finset ι) (y : X),
      ‖∑ i ∈ s, (inner 𝒷 (e i) y : 𝒷) • e i‖ ≤ ‖y‖ := by
    intro s y
    have h1 : (inner 𝒷 (∑ i ∈ s, (inner 𝒷 (e i) y : 𝒷) • e i)
        (∑ i ∈ s, (inner 𝒷 (e i) y : 𝒷) • e i) : 𝒷)
        = ∑ i ∈ s, (inner 𝒷 (e i) y : 𝒷) * inner 𝒷 y (e i) := by
      rw [inner_sum_smul_self he.1.1 _ (fun i => onbasis_coef_absorb he.1 y i) s]
      exact Finset.sum_congr rfl fun i _ => by rw [CStarModule.star_inner]
    have hle := mod_bessel he.1 y s
    rw [← h1] at hle
    have hnn : (0 : 𝒷) ≤ inner 𝒷 (∑ i ∈ s, (inner 𝒷 (e i) y : 𝒷) • e i)
        (∑ i ∈ s, (inner 𝒷 (e i) y : 𝒷) • e i) := CStarModule.inner_self_nonneg
    have hnorm := CStarAlgebra.norm_le_norm_of_nonneg_of_le hnn hle
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷) (E := X),
      CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷) (E := X) (x := y)]
    exact Real.sqrt_le_sqrt hnorm
  have hkey3 : ∀ (s : Finset ι) (y : X), ‖(inner 𝒷 (v s) y : 𝒷)‖ ≤ C * ‖y‖ := by
    intro s y
    rw [hkey1 s y]
    exact (hC _).trans (mul_le_mul_of_nonneg_left (hkey2 s y) hC0)
  have hnormsq : ∀ z : X, ‖(inner 𝒷 z z : 𝒷)‖ = ‖z‖ * ‖z‖ := by
    intro z
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷) (E := X) (x := z)]
    exact (Real.mul_self_sqrt (norm_nonneg _)).symm
  -- substituting `∑_{i∈S} eᵢτ(eᵢ)*` for `y` gives `‖∑_{i∈S} eᵢτ(eᵢ)*‖ ≤ ‖τ‖`
  have hkey4 : ∀ s, ‖v s‖ ≤ C := by
    intro s
    have h := hkey3 s (v s)
    rw [hnormsq (v s)] at h
    rcases eq_or_lt_of_le (norm_nonneg (v s)) with h0 | h0
    · rw [← h0]; exact hC0
    · nlinarith
  have hL2 : L2Summable 𝒷 b := by
    refine ⟨C * C, fun s => ?_⟩
    rw [← hvv s, hnormsq (v s)]
    exact mul_le_mul (hkey4 s) (hkey4 s) (norm_nonneg _) hC0
  obtain ⟨t, ht⟩ := he.2.2 b hL2
  refine ⟨t, fun y => ?_⟩
  -- the net `⟨v S, y⟩` converges ultraweakly to `⟨t,y⟩` by **148V**
  have hconst : UnTendsto (inner 𝒷) (fun _ : Finset ι => y) atTop y := by
    intro ω
    simp only [sub_self]
    have hz : unSeminorm ω (inner 𝒷 : X → X → 𝒷) 0 = 0 := by
      simp [unSeminorm]
    simp [hz]
  have hnet1 : UWTendsto (fun s => (inner 𝒷 (v s) y : 𝒷)) atTop (inner 𝒷 t y) :=
    innerprod_ultraweak (cstarBInner 𝒷 X) v (fun _ => y) t y ht hconst
  -- and to `τ y`, since `τ` is ultranorm continuous (**148I**)
  have hbdd : IsBoundedModuleMap (cstarBInner 𝒷 X) (mulBInner 𝒷) C ⇑τ :=
    { add := fun x z => map_add τ x z
      smul_complex := fun c x => map_smul τ c x
      smul := fun a x => (hmod a x).trans (smul_eq_mul a (τ x)).symm
      bound := fun x => by rw [mulBInner_norm, cstarBInner_norm]; exact hC x }
  have hun : UnTendsto (mulInner 𝒷)
      (fun s => τ (∑ i ∈ s, (inner 𝒷 (e i) y : 𝒷) • e i)) atTop (τ y) := by
    intro ω
    refine squeeze_zero (fun s => unSeminorm_nonneg ω (mulInner 𝒷) _)
      (g := fun s => C * unSeminorm ω (inner 𝒷 : X → X → 𝒷)
        ((∑ i ∈ s, (inner 𝒷 (e i) y : 𝒷) • e i) - y)) (fun s => ?_) ?_
    · have hsub : τ (∑ i ∈ s, (inner 𝒷 (e i) y : 𝒷) • e i) - τ y
          = τ ((∑ i ∈ s, (inner 𝒷 (e i) y : 𝒷) • e i) - y) := (map_sub τ _ _).symm
      rw [hsub]
      exact unSeminorm_boundedModuleMap_le _ _ C hC0 _ hbdd ω _
    · simpa using ((he.2.1 y) ω).const_mul C
  have hnet2 : UWTendsto (fun s => (inner 𝒷 (v s) y : 𝒷)) atTop (τ y) := by
    have h := uwTendsto_of_unTendsto_mulInner _ _ hun
    simpa only [← hkey1] using h
  exact uwTendsto_unique' hnet2 hnet1

/-- **149V** (`dils-selfdual`, dils.tex:2244, Theorem): for a pre-Hilbert
𝒷-module `X` over a von Neumann algebra `𝒷` the following are equivalent:
(1) `X` is self dual; (2) `X` is ultranorm complete; (3) every norm-bounded
ultranorm-Cauchy net converges; (4) `X` has an orthonormal basis (indexed
by a set of elements of `X`, i.e. a family over a type in the universe of
`X`).

The proof is **149VI**–**149XI**, the cycle `1 ⇒ 3 ⇒ 4 ⇒ 2 ⇒ 4 ⇒ 1` of the
five implications above, all proved. -/
theorem dils_selfdual [VonNeumannAlgebra 𝒷] :
    List.TFAE
      [SelfDual 𝒷 X,
       UnComplete (inner 𝒷 : X → X → 𝒷),
       BddUnComplete 𝒷 X,
       ∃ (ι' : Type v) (e : ι' → X), IsONBasis 𝒷 e] := by
  tfae_have 1 → 3 := fun h => bddUnComplete_of_selfDual h
  tfae_have 3 → 4 := fun h => exists_isONBasis_of_bddUnComplete h
  tfae_have 4 → 2 := fun ⟨_, _, he⟩ => unComplete_of_isONBasis he
  tfae_have 2 → 3 := fun h => bddUnComplete_of_unComplete h
  tfae_have 4 → 1 := fun ⟨_, _, he⟩ => selfDual_of_isONBasis he
  tfae_finish

end Bases

end Theses.B.Dils
