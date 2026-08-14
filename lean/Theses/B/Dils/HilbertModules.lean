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
import Theses.A.VN.Completeness

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

/-- **142III** (`module-CS`, dils.tex:1419, Proposition (Cauchy–Schwarz)):
for a (possibly indefinite) 𝒷-valued inner product,
`⟨x,y⟩⟨y,x⟩ ≤ ‖⟨y,y⟩‖ ⟨x,x⟩`.

**Convention.** The thesis uses *right* 𝒷-modules with `⟨x, y·b⟩ = ⟨x,y⟩ b`,
whereas `BInner` follows Mathlib's `CStarModule` convention `[x, b•y] =
b [x,y]`, so that `[u,v] = ⟨v,u⟩_thesis` (see the file header).  The Lean
statement below is therefore the thesis's inequality with the two factors of
the left-hand side interchanged, exactly as in `Theses.A.CStar.chilb_cs`.
Stated without the swap it is *false*: for `𝒷 = M₂(ℂ)`, `X = 𝒷` with
`[a,b] = b a*`, `x = e₁₁`, `y = e₂₁` it would assert `e₂₂ ≤ e₁₁`.

**142IV** is the proof — not converted. -/
theorem module_CS (B : BInner 𝒷 X) (x y : X) :
    B.inner y x * B.inner x y ≤ ‖B.inner y y‖ • B.inner x x := by
  set b : 𝒷 := B.inner y x with hb
  have hbs : star b = B.inner x y := B.star_inner y x
  have hrs : ∀ (r : ℝ) (a : 𝒷), ((r : ℂ)) • a = r • a := fun r a =>
    (RCLike.real_smul_eq_coe_smul (K := ℂ) r a).symm
  have hpos : (0 : 𝒷) ≤ b * star b := by
    simpa using star_mul_self_nonneg (star b)
  have hsa : IsSelfAdjoint (B.inner y y) := B.star_inner y y
  -- `0 ≤ [b·y - t·x, b·y - t·x] = b[y,y]b* - 2t·bb* + t²·[x,x]`
  have hexp : ∀ t : ℝ,
      (2 * t) • (b * star b) ≤
        b * B.inner y y * star b + (t ^ 2) • B.inner x x := by
    intro t
    have h0 := B.inner_self_nonneg (b • y - ((t : ℝ) : ℂ) • x)
    have hz : B.inner (b • y - ((t : ℝ) : ℂ) • x) (b • y - ((t : ℝ) : ℂ) • x)
        = (b * B.inner y y * star b + (t ^ 2) • B.inner x x)
          - (2 * t) • (b * star b) := by
      simp only [B.inner_sub_right, B.inner_sub_left, B.inner_op_smul_left,
        B.inner_op_smul_right, B.inner_smul_left_complex,
        B.inner_smul_right_complex, Complex.conj_ofReal, smul_smul, hrs,
        ← hb, ← hbs, ← Complex.ofReal_mul, smul_mul_assoc, mul_smul_comm]
      rw [show (t * t : ℝ) = t ^ 2 by ring, two_mul, add_smul]
      abel
    rw [hz] at h0
    exact sub_nonneg.mp h0
  rcases eq_or_lt_of_le (norm_nonneg (B.inner y y)) with hs | hs
  · -- degenerate case `[y,y] = 0`: then `bb* ≤ ε[x,x]` for every `ε > 0`
    have hyy : B.inner y y = 0 := by
      rwa [eq_comm, norm_eq_zero] at hs
    have hbound : ∀ ε : ℝ, 0 < ε → ‖b * star b‖ ≤ ‖B.inner x x‖ * ε := by
      intro ε hε
      have h1 := hexp (2 * ε)
      rw [hyy] at h1
      simp only [mul_zero, zero_mul, zero_add] at h1
      have h2 := CStarAlgebra.norm_le_norm_of_nonneg_of_le
        (a := (2 * (2 * ε)) • (b * star b)) (by positivity) h1
      rw [norm_smul, norm_smul] at h2
      simp only [Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (2 * ε)),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * ε) ^ 2)] at h2
      nlinarith [norm_nonneg (b * star b), norm_nonneg (B.inner x x)]
    have hzero : ‖b * star b‖ ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hden : (0 : ℝ) < ‖B.inner x x‖ + 1 := by positivity
      have := hbound (ε / (‖B.inner x x‖ + 1)) (by positivity)
      rw [mul_div_assoc'] at this
      have hle : ‖B.inner x x‖ * ε / (‖B.inner x x‖ + 1) ≤ ε := by
        rw [div_le_iff₀ hden]
        nlinarith [norm_nonneg (B.inner x x), hε.le]
      linarith
    have hbb : b * star b = 0 :=
      norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))
    rw [← hbs, hbb, ← hs, zero_smul]
  · -- generic case: put `t = ‖[y,y]‖ > 0` and divide by it
    have hconj : b * B.inner y y * star b ≤ ‖B.inner y y‖ • (b * star b) :=
      CStarAlgebra.star_right_conjugate_le_norm_smul hsa
    have h := (hexp ‖B.inner y y‖).trans
      (add_le_add hconj (le_refl ((‖B.inner y y‖ ^ 2) • B.inner x x)))
    have hsplit : (2 * ‖B.inner y y‖) • (b * star b)
        = ‖B.inner y y‖ • (b * star b) + ‖B.inner y y‖ • (b * star b) := by
      rw [two_mul, add_smul]
    rw [hsplit] at h
    have h2 : ‖B.inner y y‖ • (b * star b)
        ≤ ‖B.inner y y‖ • (‖B.inner y y‖ • B.inner x x) := by
      rw [smul_smul, ← pow_two]
      exact le_of_add_le_add_left h
    rw [← hbs]
    exact le_of_smul_le_smul_left h2 hs

/-- **142V** (`module-seminorm`, dils.tex:1448, Exercise), part 1:
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

/-- **142V** (`module-seminorm`, dils.tex:1448, Exercise), part 2:
`‖x‖ = ‖[x,x]‖^½` is a seminorm with `‖x·b‖ ≤ ‖x‖‖b‖`.

**142VI** (dils.tex:1458): uniform continuity of the operations — the
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
  Theses.A.CStar.chilb_form_bounded T B hB

/-- **143II** (`adjointable-cstar-identity`, dils.tex:1532, Lemma), part 2:
for bounded adjointable `T` (with adjoint `S`): `‖T*‖ = ‖T‖` and
`‖T*T‖ = ‖T‖²`.

**143III** is the proof — not converted. -/
theorem adjointable_cstar_identity_2 (T : X →L[ℂ] Y) (S : Y →L[ℂ] X)
    (h : ModuleAdjointTo 𝒷 ⇑T ⇑S) :
    ‖S‖ = ‖T‖ ∧ ‖S.comp T‖ = ‖T‖ ^ 2 := by
  refine ⟨Theses.A.CStar.chilb_form_bounded_adjoint T S h, le_antisymm ?_ ?_⟩
  · calc ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ := S.opNorm_comp_le T
      _ = ‖T‖ ^ 2 := by
          rw [Theses.A.CStar.chilb_form_bounded_adjoint T S h]; ring
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

/-- **143IV** (`hilbmod-cstar`, dils.tex:1580, Proposition): for a Hilbert
𝒷-module `X` the adjointable bounded operators `𝒷ᵃ(X)` form a C*-algebra.
As in cstar.tex 32XIII (`bax_cstar`) the missing ingredient beyond the
∗-algebra structure and the C*-identity (**143II**) is closedness in
`B(X)`, stated here.  (The type `Ba 𝒷 X` with its C*-algebra structure is
set up below, right after **143IV**.)

**143V** is the proof — not converted. -/
theorem hilbmod_cstar [CompleteSpace X] :
    IsClosed {T : X →L[ℂ] X | ModuleAdjointable 𝒷 ⇑T} :=
  Theses.A.CStar.bax_cstar

end Adjointable

/-! ## The C*-algebra `𝒷ᵃ(X)` as a type

The C*-structure of **143IV** (`hilbmod-cstar`, dils.tex:1580) is assembled
here from thesis A's cstar.tex 32X/32XII/32XIII (`chilb_form_bounded`,
`module_maps_cstar_identity`, `bax_cstar`, all proved in
`Theses.A.CStar.Matrices`): the adjointable bounded operators form a
ℂ-subalgebra of `B(X)` which is closed (32XIII), the adjoint is an
involutive conjugate-linear anti-automorphism (32III), and the C*-identity
is 32XII. -/

section BaConstruction

variable {𝒷 : Type u} {X : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]

variable (𝒷 X)

/-- **143IV** (`hilbmod-cstar`, dils.tex:1580, Proposition), the algebraic
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

instance baInstCStarRing : CStarRing (baSubalgebra 𝒷 X) where
  norm_mul_self_le T := by
    have h : ‖(baAdj T).comp (T : X →L[ℂ] X)‖ = ‖(T : X →L[ℂ] X)‖ ^ 2 :=
      Theses.A.CStar.module_maps_cstar_identity (𝒜 := 𝒷) _ _ (baAdj_spec T)
    have h' : ‖star T * T‖ = ‖(T : X →L[ℂ] X)‖ ^ 2 := h
    rw [h']
    exact le_of_eq (sq ‖(T : X →L[ℂ] X)‖).symm

instance baInstCompleteSpace [CompleteSpace X] :
    CompleteSpace (baSubalgebra 𝒷 X) :=
  (Theses.A.CStar.bax_cstar (𝒜 := 𝒷) (X := X)).completeSpace_coe

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
𝒷-module `X` (**143I**, dils.tex:1509), as a type. -/
def Ba : Type v :=
  {T : X →L[ℂ] X // ModuleAdjointable 𝒷 ⇑T}

/-- The underlying bounded operator of an element of `𝒷ᵃ(X)`. -/
def Ba.toCLM (T : Ba 𝒷 X) : X →L[ℂ] X := T.1

variable [CompleteSpace X]

/-- **143IV** (`hilbmod-cstar`, dils.tex:1580, Proposition), as an
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
/-- **144I** (`hilbmod-ordersep`, dils.tex:1623, Proposition): the vector
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

/-- **145I** (`hilbmod-vectstates-cp`, dils.tex:1706, Proposition): for a
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
      FilterEquiv F G → FilterEquiv G H → FilterEquiv F H) := by
  refine ⟨fun F hF V hV => ?_, fun F G _ _ h V hV => ?_,
    fun F G H _ hG _ hFG hGH V hV => ?_⟩
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

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1982, Exercise), part
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

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1982, Exercise), part
3: limits are unique in a Hausdorff uniform space (Mathlib:
`tendsto_nhds_unique`). -/
theorem dils_uniform_spaces_basics_3 [T2Space X] {ι : Type w} (l : Filter ι)
    [l.NeBot] (x : ι → X) (a b : X) (ha : Tendsto x l (𝓝 a))
    (hb : Tendsto x l (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1982, Exercise), part
4: continuous maps preserve limits of nets (Mathlib:
`Continuous.tendsto.comp`). -/
theorem dils_uniform_spaces_basics_4 (f : X → Y) (hf : Continuous f)
    {ι : Type w} (l : Filter ι) (x : ι → X) (a : X)
    (ha : Tendsto x l (𝓝 a)) : Tendsto (f ∘ x) l (𝓝 (f a)) :=
  (hf.tendsto a).comp ha

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1982, Exercise), part
5: uniformly continuous maps send Cauchy filters to Cauchy filters and
preserve equivalence (Mathlib: `Cauchy.map`). -/
theorem dils_uniform_spaces_basics_5 (f : X → Y) (hf : UniformContinuous f) :
    (∀ F : Filter X, Cauchy F → Cauchy (F.map f)) ∧
    (∀ F G : Filter X, Cauchy F → Cauchy G → FilterEquiv F G →
      FilterEquiv (F.map f) (G.map f)) := by
  refine ⟨fun F hF => hF.map hf, fun F G _ _ h V hV => ?_⟩
  -- `(f × f)⁻¹ V` is an entourage of `X`, and images of witnesses work
  obtain ⟨s, hs, t, ht, hst⟩ := h _ (hf hV)
  refine ⟨f '' s, Filter.image_mem_map hs, f '' t, Filter.image_mem_map ht, ?_⟩
  rintro ⟨a, b⟩ ⟨⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩⟩
  exact hst (Set.mk_mem_prod ha' hb')

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1982, Exercise), part
6: for a dense `D ⊆ X`, every point is the limit of a Cauchy filter living
on `D`. -/
theorem dils_uniform_spaces_basics_6 (D : Set X) (hD : Dense D) (x : X) :
    ∃ F : Filter X, F.NeBot ∧ D ∈ F ∧ Cauchy F ∧ F ≤ 𝓝 x := by
  have hne : (𝓝[D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hD x)
  exact ⟨𝓝[D] x, hne, self_mem_nhdsWithin,
    cauchy_nhds.mono nhdsWithin_le_nhds, nhdsWithin_le_nhds⟩

/-- **147II** (`dils-uniform-spaces-basics`, dils.tex:1982, Exercise), part
7: continuous maps into a Hausdorff space agreeing on a dense set are equal
(Mathlib: `Continuous.ext_on`). -/
theorem dils_uniform_spaces_basics_7 [T2Space Y] (f g : X → Y)
    (hf : Continuous f) (hg : Continuous g) (D : Set X) (hD : Dense D)
    (h : Set.EqOn f g D) : f = g :=
  hf.ext_on hD hg h

/-- **147III** (`dils-product-uniformity`, dils.tex:2021, Exercise): the
product uniformity (Mathlib: `Pi.uniformSpace`) makes the projections
uniformly continuous and is the categorical product: a map into the product
is uniformly continuous iff all its components are (Mathlib:
`uniformContinuous_pi`). -/
theorem dils_product_uniformity {ι : Type w} {Z : ι → Type v}
    [∀ i, UniformSpace (Z i)] (f : X → ∀ i, Z i) :
    (∀ i, UniformContinuous fun z : ∀ i, Z i => z i) ∧
      (UniformContinuous f ↔ ∀ i, UniformContinuous fun x => f x i) :=
  ⟨fun i => Pi.uniformContinuous_proj Z i, uniformContinuous_pi⟩

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

/-- Cauchy–Schwarz for `‖·‖_ω`: `|ω[x,y]| ≤ ‖x‖_ω ‖y‖_ω`. -/
theorem unSeminorm_inner_le (ω : NPFunctional 𝒷) (B : BInner 𝒷 X) (x y : X) :
    ‖ω (B.inner x y)‖ ≤ unSeminorm ω B.inner x * unSeminorm ω B.inner y := by
  have ha : 0 ≤ (ω (B.inner x x)).re := np_re_nonneg ω (B.inner_self_nonneg x)
  have hb : 0 ≤ (ω (B.inner y y)).re := np_re_nonneg ω (B.inner_self_nonneg y)
  have hyx : ω (B.inner y x) = starRingEnd ℂ (ω (B.inner x y)) := by
    rw [← B.star_inner x y, np_star]
  -- the quadratic `0 ≤ ω [x + λy, x + λy]`
  have hquad : ∀ lam : ℂ, 0 ≤ (ω (B.inner x x)).re + 2 * (lam * ω (B.inner x y)).re
      + Complex.normSq lam * (ω (B.inner y y)).re := by
    intro lam
    have hz : (0 : ℝ) ≤ (ω (B.inner (x + lam • y) (x + lam • y))).re :=
      np_re_nonneg ω (B.inner_self_nonneg _)
    have hexp : B.inner (x + lam • y) (x + lam • y)
        = B.inner x x + lam • B.inner x y
          + ((starRingEnd ℂ) lam • B.inner y x
            + (starRingEnd ℂ lam * lam) • B.inner y y) := by
      rw [B.inner_add_left, B.inner_add_right, B.inner_add_right,
        B.inner_smul_right_complex, B.inner_smul_left_complex,
        B.inner_smul_left_complex, B.inner_smul_right_complex, smul_smul, add_assoc]
    rw [hexp, np_add, np_add, np_add, np_smul, np_smul, np_smul, hyx] at hz
    have hbim : (ω (B.inner y y)).im = 0 := np_im_zero ω (B.inner_self_nonneg y)
    simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply, hbim] at hz ⊢
    nlinarith [hz]
  -- specialize to `λ = -t · conj ω[x,y]`
  set c := ω (B.inner x y) with hc
  have hspec : ∀ t : ℝ, 0 ≤ (ω (B.inner x x)).re - 2 * t * Complex.normSq c
      + t ^ 2 * Complex.normSq c * (ω (B.inner y y)).re := by
    intro t
    have h := hquad (-(t : ℂ) * (starRingEnd ℂ) c)
    have h1 : (-(t : ℂ) * (starRingEnd ℂ) c * c).re = -(t * Complex.normSq c) := by
      rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self]
      simp
    have h2 : Complex.normSq (-(t : ℂ) * (starRingEnd ℂ) c)
        = t ^ 2 * Complex.normSq c := by
      simp [Complex.normSq_apply]
      ring
    rw [h1, h2] at h
    nlinarith [h]
  have hN : 0 ≤ Complex.normSq c := Complex.normSq_nonneg c
  have hkey : Complex.normSq c ≤ (ω (B.inner x x)).re * (ω (B.inner y y)).re := by
    rcases eq_or_lt_of_le hN with hN0 | hN0
    · nlinarith
    · rcases eq_or_lt_of_le hb with hb0 | hb0
      · exfalso
        have h := hspec (((ω (B.inner x x)).re + 1) / (2 * Complex.normSq c))
        rw [← hb0] at h
        field_simp at h
        nlinarith [h]
      · have h := hspec ((ω (B.inner y y)).re⁻¹)
        have hbne : (ω (B.inner y y)).re ≠ 0 := ne_of_gt hb0
        field_simp at h
        nlinarith [h]
  calc ‖c‖ = Real.sqrt (Complex.normSq c) := Complex.norm_def c
    _ ≤ Real.sqrt ((ω (B.inner x x)).re * (ω (B.inner y y)).re) := Real.sqrt_le_sqrt hkey
    _ = unSeminorm ω B.inner x * unSeminorm ω B.inner y := by
        rw [unSeminorm, unSeminorm, Real.sqrt_mul ha]

/-- The triangle inequality for `‖·‖_ω`. -/
theorem unSeminorm_add_le (ω : NPFunctional 𝒷) (B : BInner 𝒷 X) (x y : X) :
    unSeminorm ω B.inner (x + y)
      ≤ unSeminorm ω B.inner x + unSeminorm ω B.inner y := by
  have hx := unSeminorm_nonneg ω B.inner x
  have hy := unSeminorm_nonneg ω B.inner y
  have hcs := unSeminorm_inner_le ω B x y
  have hexp : (ω (B.inner (x + y) (x + y))).re
      = (ω (B.inner x x)).re + 2 * (ω (B.inner x y)).re + (ω (B.inner y y)).re := by
    have hyx : ω (B.inner y x) = starRingEnd ℂ (ω (B.inner x y)) := by
      rw [← B.star_inner x y, np_star]
    rw [B.inner_add_left, B.inner_add_right, B.inner_add_right, np_add, np_add,
      np_add, hyx]
    simp only [Complex.add_re, Complex.conj_re]
    ring
  have hre : (ω (B.inner x y)).re ≤ ‖ω (B.inner x y)‖ := Complex.re_le_norm _
  have hsq : unSeminorm ω B.inner (x + y) ^ 2
      ≤ (unSeminorm ω B.inner x + unSeminorm ω B.inner y) ^ 2 := by
    rw [unSeminorm_sq, hexp, add_sq, unSeminorm_sq, unSeminorm_sq]
    nlinarith
  nlinarith [unSeminorm_nonneg ω B.inner (x + y)]

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

/-- **148I** (`blinear-bounded-is-ultranorm`, dils.tex:2041, Proposition):
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

variable {ι : Type w} {l : Filter ι}

/-- **148III** (`ultranormcontstruct`, dils.tex:2060, Corollary), part 1:
addition is (jointly uniformly) ultranorm continuous: it preserves
ultranorm limits. -/
theorem ultranormcontstruct_add (B : BInner 𝒷 X) (x y : ι → X) (x₀ y₀ : X)
    (hx : UnTendsto B.inner x l x₀) (hy : UnTendsto B.inner y l y₀) :
    UnTendsto B.inner (fun i => x i + y i) l (x₀ + y₀) := by
  intro ω
  refine squeeze_zero (fun i => unSeminorm_nonneg ω B.inner _) (g := fun i =>
    unSeminorm ω B.inner (x i - x₀) + unSeminorm ω B.inner (y i - y₀)) (fun i => ?_) ?_
  · have hrw : x i + y i - (x₀ + y₀) = (x i - x₀) + (y i - y₀) := by abel
    rw [hrw]
    exact unSeminorm_add_le ω B _ _
  · simpa using (hx ω).add (hy ω)

/-- **148III** (`ultranormcontstruct`, dils.tex:2060, Corollary), part 2:
for fixed `x₀`, the map `x ↦ [x₀, x] : X → 𝒷` is uniformly continuous from
the ultranorm uniformity of `X` to the ultrastrong uniformity of `𝒷` (the
ultranorm uniformity of `mulInner`): it preserves limits. -/
theorem ultranormcontstruct_inner [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 X)
    (x₀ : X) (x : ι → X) (xlim : X) (hx : UnTendsto B.inner x l xlim) :
    UnTendsto (mulInner 𝒷) (fun i => B.inner x₀ (x i)) l (B.inner x₀ xlim) := by
  intro ω
  refine squeeze_zero (fun i => unSeminorm_nonneg ω (mulInner 𝒷) _) (g := fun i =>
    Real.sqrt ‖B.inner x₀ x₀‖ * unSeminorm ω B.inner (x i - xlim)) (fun i => ?_) ?_
  · have hd : B.inner x₀ (x i) - B.inner x₀ xlim = B.inner x₀ (x i - xlim) :=
      (B.inner_sub_right x₀ (x i) xlim).symm
    have hmul : mulInner 𝒷 (B.inner x₀ (x i - xlim)) (B.inner x₀ (x i - xlim))
        = B.inner x₀ (x i - xlim) * B.inner (x i - xlim) x₀ := by
      show B.inner x₀ (x i - xlim) * star (B.inner x₀ (x i - xlim)) = _
      rw [B.star_inner]
    have hCS := module_CS B (x i - xlim) x₀
    have hre : (ω (mulInner 𝒷 (B.inner x₀ (x i - xlim)) (B.inner x₀ (x i - xlim)))).re
        ≤ ‖B.inner x₀ x₀‖ * (ω (B.inner (x i - xlim) (x i - xlim))).re := by
      rw [hmul, ← np_re_smul]
      exact np_re_mono ω hCS
    rw [hd, unSeminorm, unSeminorm]
    calc Real.sqrt (ω (mulInner 𝒷 (B.inner x₀ (x i - xlim)) (B.inner x₀ (x i - xlim)))).re
        ≤ Real.sqrt (‖B.inner x₀ x₀‖ * (ω (B.inner (x i - xlim) (x i - xlim))).re) :=
          Real.sqrt_le_sqrt hre
      _ = _ := Real.sqrt_mul (norm_nonneg _) _
  · simpa using (hx ω).const_mul (Real.sqrt ‖B.inner x₀ x₀‖)

/-- **148III** (`ultranormcontstruct`, dils.tex:2060, Corollary), part 3:
for fixed `x₀`, the map `b ↦ x₀ · b : 𝒷 → X` is uniformly continuous from
the ultrastrong uniformity of `𝒷` to the ultranorm uniformity of `X`
(mirrored: `b • x₀`): it preserves limits. -/
theorem ultranormcontstruct_smul [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 X)
    (x₀ : X) (b : ι → 𝒷) (blim : 𝒷)
    (hb : UnTendsto (mulInner 𝒷) b l blim) :
    UnTendsto B.inner (fun i => b i • x₀) l (blim • x₀) := by
  intro ω
  refine squeeze_zero (fun i => unSeminorm_nonneg ω B.inner _) (g := fun i =>
    Real.sqrt ‖B.inner x₀ x₀‖ * unSeminorm ω (mulInner 𝒷) (b i - blim)) (fun i => ?_) ?_
  · have hexp : B.inner (b i • x₀ - blim • x₀) (b i • x₀ - blim • x₀)
        = (b i - blim) * B.inner x₀ x₀ * star (b i - blim) := by
      simp only [B.inner_sub_left, B.inner_sub_right, B.inner_op_smul_left,
        B.inner_op_smul_right, star_sub, sub_mul, mul_sub, mul_assoc]
    have hsa : IsSelfAdjoint (B.inner x₀ x₀) := B.star_inner x₀ x₀
    have hconj : (b i - blim) * B.inner x₀ x₀ * star (b i - blim)
        ≤ ‖B.inner x₀ x₀‖ • ((b i - blim) * star (b i - blim)) :=
      CStarAlgebra.star_right_conjugate_le_norm_smul hsa
    have hre : (ω (B.inner (b i • x₀ - blim • x₀) (b i • x₀ - blim • x₀))).re
        ≤ ‖B.inner x₀ x₀‖ * (ω (mulInner 𝒷 (b i - blim) (b i - blim))).re := by
      rw [hexp, ← np_re_smul]
      exact np_re_mono ω hconj
    rw [unSeminorm, unSeminorm]
    calc Real.sqrt (ω (B.inner (b i • x₀ - blim • x₀) (b i • x₀ - blim • x₀))).re
        ≤ Real.sqrt (‖B.inner x₀ x₀‖ * (ω (mulInner 𝒷 (b i - blim) (b i - blim))).re) :=
          Real.sqrt_le_sqrt hre
      _ = _ := Real.sqrt_mul (norm_nonneg _) _
  · simpa using (hb ω).const_mul (Real.sqrt ‖B.inner x₀ x₀‖)

/-- **148IV** (`ultranormscalar`, dils.tex:2072, Exercise): for fixed
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

/-- **148V** (`innerprod-ultraweak`, dils.tex:2078, Proposition): if
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
(**146VII**, dils.tex:1889).  Together with **144I** this gives **148VII**
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

/-- **148VII** (`hilbmod-denseordersep`, dils.tex:2116, Corollary): for a
Hilbert 𝒷-module `X` with ultranorm-dense subset `D`, the vector states
from `D` are order separating: for adjointable bounded `T`, `T ≥ 0` iff
`⟨x, Tx⟩ ≥ 0` for all `x ∈ D`.

The `[VonNeumannAlgebra 𝒷]` hypothesis is the thesis's: the ultranorm
uniformity — and hence the phrase "ultranorm-dense" in the statement — is
defined only for a von Neumann algebra `𝒷` (**146VII**, dils.tex:1889, "Let
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

/-- **149III** (`mod-projelabs`, dils.tex:2216, Exercise): if `⟨e,e⟩` is a
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

/-- **149IV** (`mod-parseval`, dils.tex:2225, Exercise (Parseval's
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

**149VI** (dils.tex:2249) fixes the route `1 ⇒ 3 ⇒ 4 ⇒ 2 ⇒ 4 ⇒ 1`; the four
non-trivial implications are stated separately below, so that they can be
used (and proved) one at a time.  Of the four, `1 ⇒ 3` and `4 ⇒ 1` are
proved; the other two still consume results of `A/VN` that are `sorry`
there (**80IV** for `3 ⇒ 4`, **87VIII** for `4 ⇒ 2`) — see their doc
comments. -/

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

/-- `‖x‖_ω ≤ ‖x‖ ω(1)^½` (**146VIII**, the half that **149VII** uses). -/
private theorem unSeminorm_le_norm_mul (ω : NPFunctional 𝒷) (x : X) :
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

/-- **149VII** (dils.tex:2258): (1) ⇒ (3) of **149V** — a self-dual
pre-Hilbert 𝒷-module is norm-bounded ultranorm complete.

Divergence class 1 (faithful) with one forced deviation, class 2, at the
bound on `τ`.  The thesis's `τ(y) = (uslim_α ⟨y,x_α⟩)*` is *unstarred* in
the mirrored convention — `τ(y) = uslim_α [x_α,y]` — because it is the
*second* argument of Mathlib's `[·,·]` that is 𝒷-linear; the ultrastrong
limit exists by **77I**.1 `Theses.A.VN.vn_complete_1` (whence the import of
`Theses.A.VN.Completeness`), and `τ` is linear by uniqueness of ultrastrong
limits (**44XI**.1).  Where the thesis identifies `τ(y)τ(y)*` with an
ultraweak limit through **46II** (`usconv`), we bound `‖τ(y)‖_ω` directly by
`‖y‖ B ω(1)^½` — every `‖[x_α,y]‖_ω` obeys that bound by **142III**, and
`‖·‖_ω` is `‖·‖_ω`-continuous — and then turn the family of bounds into
`‖τ(y)‖ ≤ B‖y‖` by order separation of the np-functionals (**44XI**), which
is what `usconv` would have been used for.  The closing estimate is the
thesis's verbatim, with Kadison's inequality in the form
`norm_apply_le_omegaNorm`. -/
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
  -- (d) `‖τ y‖_ω ≤ ‖y‖ B ω(1)^½`, hence `‖τ y‖ ≤ B ‖y‖` by order separation
  have hbound : ∀ (ω : NPFunctional 𝒷) (y : X),
      omegaNorm 𝒷 ω (t' y) ≤ ‖y‖ * M * Real.sqrt (ω 1).re := by
    intro ω y
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hmem : {x : X | omegaNorm 𝒷 ω ((inner 𝒷 x y : 𝒷) - t' y) < ε} ∈ F := by
      have h0 := (usTendsto_iff _ _ _).mp (ht' y) ω
      filter_upwards [(Metric.tendsto_nhds.mp h0) ε hε] with x hx
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (omegaNorm_nonneg ω _)] at hx
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem (inter_mem hmem hs₀F)
    have e1 : omegaNorm 𝒷 ω (t' y - (inner 𝒷 x y : 𝒷))
        = omegaNorm 𝒷 ω ((inner 𝒷 x y : 𝒷) - t' y) := by
      rw [show t' y - (inner 𝒷 x y : 𝒷) = -((inner 𝒷 x y : 𝒷) - t' y) by abel,
        omegaNorm_neg]
    have e2 : omegaNorm 𝒷 ω ((inner 𝒷 x y : 𝒷))
        ≤ ‖y‖ * M * Real.sqrt (ω 1).re := by
      have hsq : (0 : ℝ) ≤ Real.sqrt (ω 1).re := Real.sqrt_nonneg _
      have hxM := hs₀ x hx.2
      calc omegaNorm 𝒷 ω ((inner 𝒷 x y : 𝒷))
          ≤ ‖y‖ * unSeminorm ω (inner 𝒷 : X → X → 𝒷) x := omegaNorm_inner_le ω x y
        _ ≤ ‖y‖ * (‖x‖ * Real.sqrt (ω 1).re) :=
            mul_le_mul_of_nonneg_left (unSeminorm_le_norm_mul ω x) (norm_nonneg y)
        _ ≤ ‖y‖ * (M * Real.sqrt (ω 1).re) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hxM hsq) (norm_nonneg y)
        _ = ‖y‖ * M * Real.sqrt (ω 1).re := (mul_assoc _ _ _).symm
    have h3 := omegaNorm_sub_le ω (t' y) (inner 𝒷 x y) 0
    rw [sub_zero, sub_zero, e1] at h3
    have hx1 : omegaNorm 𝒷 ω ((inner 𝒷 x y : 𝒷) - t' y) < ε := hx.1
    linarith
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

/-- **149VIII** (`selfdual-bcompl-then-basis`, dils.tex:2328): (3) ⇒ (4) of
**149V** — a norm-bounded ultranorm complete pre-Hilbert 𝒷-module has an
orthonormal basis.

**Blocked on `A/VN`.**  The proof takes a maximal orthonormal set by Zorn and
rules out a non-zero `x'` orthogonal to it by *polar decomposition* in `X`,
`x' = u⟨x',x'⟩^½` with `⟨u,u⟩ = ⌈⟨x',x'⟩⌉`, which is built from an
approximate pseudoinverse of `⟨x',x'⟩^½`: **80IV**
`Theses.A.VN.approximate_pseudoinverse` — still `sorry` in
`Theses/A/VN/Division.lean`, and not on this file's import path.  (Bessel,
`mod_bessel`, and the ℓ²-summability half of the argument are available.) -/
theorem exists_isONBasis_of_bddUnComplete [VonNeumannAlgebra 𝒷]
    (h : BddUnComplete 𝒷 X) :
    ∃ (ι' : Type v) (e : ι' → X), IsONBasis 𝒷 e :=
  sorry

/-- **149IX** (dils.tex:2461): (4) ⇒ (2) of **149V** — a pre-Hilbert
𝒷-module with an orthonormal basis is ultranorm complete.

**Blocked on `A/VN`.**  The limit is `∑ₑ e bₑ` with
`bₑ = uslim_α ⟨e, x_α⟩`, which is now available (**77I**.1
`Theses.A.VN.vn_complete_1`, imported and proved); but the ℓ²-summability of
`(bₑ)ₑ` is deduced from an ultraweak bound by **87VIII**
`Theses.A.VN.ultraweakly_bounded_implies_bounded`, still `sorry` in
`Theses/A/VN/NormalFunctionals.lean`. -/
theorem unComplete_of_isONBasis [VonNeumannAlgebra 𝒷] {e : ι → X}
    (he : IsONBasis 𝒷 e) : UnComplete (inner 𝒷 : X → X → 𝒷) :=
  sorry

omit [StarOrderedRing 𝒷] in
/-- **149X** (dils.tex:2565): (2) ⇒ (3) of **149V** — trivially, since a
norm-bounded ultranorm-Cauchy filter is in particular ultranorm Cauchy. -/
theorem bddUnComplete_of_unComplete (h : UnComplete (inner 𝒷 : X → X → 𝒷)) :
    BddUnComplete 𝒷 X :=
  fun F hF hCauchy _ => h F hF hCauchy

/-- **149XI** (dils.tex:2569): (4) ⇒ (1) of **149V** — a pre-Hilbert
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

/-- **149V** (`dils-selfdual`, dils.tex:2236, Theorem): for a pre-Hilbert
𝒷-module `X` over a von Neumann algebra `𝒷` the following are equivalent:
(1) `X` is self dual; (2) `X` is ultranorm complete; (3) every norm-bounded
ultranorm-Cauchy net converges; (4) `X` has an orthonormal basis (indexed
by a set of elements of `X`, i.e. a family over a type in the universe of
`X`).

The proof is **149VI**–**149XI**, the cycle `1 ⇒ 3 ⇒ 4 ⇒ 2 ⇒ 4 ⇒ 1` of the
five implications above; `4 ⇒ 1` and `2 ⇒ 3` are proved, the remaining three
are `sorry` and blocked on `A/VN`. -/
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
