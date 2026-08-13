/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 4280–5965.

  parsec 1590:  |x⟩⟨y| operators, ultraweak density of their span
  parsec 1600:  orthocomplements and the projection theorem
  parsec 1610:  ℓ²((pᵢ)ᵢ) and orthonormal bases
  parsec 1620:  comparison of projections; the normal form of self-dual
                modules over factors
  parsec 1630:  the completion is determined by its universal property
  parsec 1640:  the self-dual exterior tensor product
  parsec 1650:  𝒷ᵃ(X) ⊗ 𝒷ᵃ(Y) ≅ 𝒷ᵃ(X ⊗ Y)
  parsec 1660:  ultranorm continuity of the exterior tensor product
  parsec 1670:  the tensor product of Paschke dilations

Statements only; every proof is `sorry`.  Conventions as in
`HilbertModules.lean` (mirrored left-action convention).

NOTE(proc-dep): the tensor product of von Neumann algebras is developed in
thesis A (proc.tex, parsec 1080, label `tensor`), which is not yet
formalized; the interface needed here (an miu-bilinear map whose product
np-functionals are separating and whose image generates) is axiomatized
below as `IsVNTensor`.
-/
import Theses.B.Dils.Paschke
import Theses.B.Dils.Kaplansky

open scoped ComplexOrder CStarAlgebra WithCStarModule Uniformity
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u v

namespace Theses.B.Dils

/-! ## Parsec 1590: the operators |x⟩⟨y|

**159I** (dils.tex:4282): introduction — nothing to formalize. -/

section Ketbra

variable {ℬ : Type u} {X : Type v}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X]

/-! ### Elementary properties of the module action

`CStarModule ℬ X` assumes only `SMul ℬ X`; the module laws for that action
are consequences of the axioms, by definiteness of the inner product (the
same derivation as `Theses.A.CStar.moduleAdjointable_linear`).  Together
with `norm_op_smul_le` these are exactly what is needed to *define* the
operator `|x⟩⟨y| : z ↦ ⟨y,z⟩ • x` of **159II** as a
`LinearMap.mkContinuous`; see the note before `mketbra` below for why that
definition cannot be written down at the present signature. -/

theorem op_add_smul (a b : ℬ) (x : X) : (a + b) • x = a • x + b • x :=
  eq_of_inner_right_eq (𝒜 := ℬ) fun z => by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_add_right,
      CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_right, add_mul]

theorem op_mul_smul (a b : ℬ) (x : X) : (a * b) • x = a • (b • x) :=
  eq_of_inner_right_eq (𝒜 := ℬ) fun z => by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_right,
      CStarModule.inner_op_smul_right, mul_assoc]

theorem op_smul_complex_smul (c : ℂ) (a : ℬ) (x : X) :
    (c • a) • x = c • (a • x) :=
  eq_of_inner_right_eq (𝒜 := ℬ) fun z => by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_smul_right_complex,
      CStarModule.inner_op_smul_right, smul_mul_assoc]

theorem norm_op_smul_le (a : ℬ) (x : X) : ‖a • x‖ ≤ ‖a‖ * ‖x‖ := by
  have hinner : (inner ℬ (a • x) (a • x) : ℬ) = a * inner ℬ x x * star a := by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_left,
      mul_assoc]
  have hsq : ‖a • x‖ ^ 2 ≤ (‖a‖ * ‖x‖) ^ 2 := by
    rw [CStarModule.norm_sq_eq (A := ℬ), hinner]
    calc ‖a * inner ℬ x x * star a‖ ≤ ‖a‖ * ‖(inner ℬ x x : ℬ)‖ * ‖star a‖ :=
          (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = (‖a‖ * ‖x‖) ^ 2 := by
          rw [norm_star, ← CStarModule.norm_sq_eq (A := ℬ)]; ring
  have h1 : (0 : ℝ) ≤ ‖a • x‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖a‖ * ‖x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-! ### FIXME(mketbra-signature)

`mketbra` below elaborates to
`{X} → [NormedAddCommGroup X] → [NormedSpace ℂ X] → X → X → X →L[ℂ] X`:
because its body is `sorry`, variable inclusion drops `ℬ` and every
instance mentioning it, so the declared operator **does not depend on ℬ at
all** and therefore cannot be defined — `z ↦ ⟨y,z⟩ • x` needs the
ℬ-valued inner product.  (`mketbra_apply` does mention `ℬ`, so it pins
`mketbra` down and is consistent; it is only the *definition* that is
impossible.)

Repairing this means making `ℬ` an argument (`variable (ℬ)` in this
section, i.e. `mketbra ℬ x y`), which rewrites the ten downstream
statements that mention `mketbra`, so it is left to whoever owns the
statements.  Once `ℬ` is an argument, **159II** and both halves of
**159III** all go through; the following four declarations have been
checked to compile (with `mketbra ℬ` substituted throughout the statements
of the last three):

    noncomputable def mketbra (x y : X) : X →L[ℂ] X :=
      LinearMap.mkContinuous
        { toFun := fun z => inner ℬ y z • x
          map_add' := fun z z' => by
            rw [CStarModule.inner_add_right, op_add_smul]
          map_smul' := fun c z => by
            rw [CStarModule.inner_smul_right_complex, op_smul_complex_smul,
              RingHom.id_apply] }
        (‖y‖ * ‖x‖) fun z => by
          calc ‖(inner ℬ y z : ℬ) • x‖ ≤ ‖(inner ℬ y z : ℬ)‖ * ‖x‖ :=
                norm_op_smul_le _ _
            _ ≤ ‖y‖ * ‖z‖ * ‖x‖ :=
                mul_le_mul_of_nonneg_right (CStarModule.norm_inner_le X)
                  (norm_nonneg _)
            _ = ‖y‖ * ‖x‖ * ‖z‖ := by ring

    theorem mketbra_apply (x y z : X) : mketbra x y z = inner ℬ y z • x := rfl

    theorem mketbra_adjointable (x y : X) :
        ModuleAdjointTo ℬ (⇑(mketbra x y) : X → X) ⇑(mketbra y x) := by
      intro z w
      rw [mketbra_apply, mketbra_apply, CStarModule.inner_op_smul_left,
        CStarModule.inner_op_smul_right, CStarModule.star_inner]

    theorem mketbra_rules … := by     -- statement unchanged apart from `ℬ`
      obtain ⟨-, hTc, hTm⟩ := moduleAdjointable_linear (𝒜 := ℬ) ⇑T ⟨_, hT⟩
      refine ⟨?_, ?_, ⟨?_, mketbra_adjointable ℬ e e⟩, ?_, ?_⟩
      · ext z
        show (inner ℬ y z : ℬ) • (b • x) = (inner ℬ (star b • y) z : ℬ) • x
        rw [CStarModule.inner_op_smul_left, star_star, op_mul_smul]
      · ext z
        show (inner ℬ y ((inner ℬ w z : ℬ) • v) : ℬ) • x
          = (inner ℬ w z : ℬ) • ((inner ℬ y v : ℬ) • x)
        rw [CStarModule.inner_op_smul_right, op_mul_smul]
      · ext z
        show (inner ℬ e ((inner ℬ e z : ℬ) • e) : ℬ) • e = (inner ℬ e z : ℬ) • e
        rw [CStarModule.inner_op_smul_right, op_mul_smul, mod_projelabs e he]
      · ext z
        show T ((inner ℬ y z : ℬ) • x) = (inner ℬ y z : ℬ) • T x
        rw [hTm]
      · ext z
        show (inner ℬ y (T' z) : ℬ) • x = (inner ℬ (T y) z : ℬ) • x
        rw [hT y z]
-/

/-- **159II** (dils.tex:4292, Definition): for `x, y` in a Hilbert
ℬ-module `X`, the bounded operator `|x⟩⟨y| : z ↦ x⟨y,z⟩` (mirrored:
`⟨y,z⟩ • x`; in the literature `θ_{x,y}`, **159IIa**).  (Definition
deferred; only the characterizing property `mketbra_apply` is used.) -/
noncomputable def mketbra (x y : X) : X →L[ℂ] X :=
  sorry

/-- **159II** (dils.tex:4292, Definition), characterizing property:
`|x⟩⟨y| z = ⟨y,z⟩ • x`. -/
theorem mketbra_apply (x y z : X) :
    mketbra x y z = inner ℬ y z • x :=
  sorry

/-- **159III** (`hilbmodketbrarules`, dils.tex:4302): `|x⟩⟨y|` is
adjointable, with adjoint `|y⟩⟨x|`. -/
theorem mketbra_adjointable (x y : X) :
    ModuleAdjointTo ℬ (⇑(mketbra x y) : X → X) ⇑(mketbra y x) :=
  sorry

/-- **159III** (`hilbmodketbrarules`, dils.tex:4302): the calculus of the
`|x⟩⟨y|`: `|xb⟩⟨y| = |x⟩⟨yb*|` (mirrored) and
`|x⟩⟨y| |v⟩⟨w| = |x⟨y,v⟩⟩⟨w|`; if `⟨e,e⟩` is a projection then `|e⟩⟨e|`
is a projection; and `T|x⟩⟨y| = |Tx⟩⟨y|`, `|x⟩⟨y| T* = |x⟩⟨Ty|` for
adjointable `T`. -/
theorem mketbra_rules (x y v w e : X) (b : ℬ)
    (T T' : X →L[ℂ] X) (hT : ModuleAdjointTo ℬ ⇑T ⇑T')
    (he : IsStarProjection (inner ℬ e e)) :
    mketbra (b • x) y = mketbra x (star b • y) ∧
    (mketbra x y).comp (mketbra v w) = mketbra (inner ℬ y v • x) w ∧
    ((mketbra e e).comp (mketbra e e) = mketbra e e ∧
      ModuleAdjointTo ℬ (⇑(mketbra e e) : X → X) ⇑(mketbra e e)) ∧
    T.comp (mketbra x y) = mketbra (T x) y ∧
    (mketbra x y).comp T' = mketbra x (T y) :=
  sorry

variable [CompleteSpace X]

/-- **159IV** (`ketbra-ultraweakly-dense`, dils.tex:4319, Proposition): for
a self-dual Hilbert ℬ-module `X` with orthonormal basis `(eᵢ)`, the linear
span of the operators `|eᵢb⟩⟨eⱼ|` is ultraweakly dense in `ℬᵃ(X)`: every
`T` is the ultraweak limit of a net (canonically `p_S T p_S`, indexed by
finite subsets of the basis) from the span.

**159V**–**159VIII** are the proof — not converted. -/
theorem ketbra_ultraweakly_dense [VonNeumannAlgebra ℬ]
    (hX : SelfDual ℬ X) {ι : Type v} (e : ι → X) (he : IsONBasis ℬ e)
    (T : Ba ℬ X) :
    ∃ approx : Finset ι → Ba ℬ X,
      (∀ s, approx s ∈ Submodule.span ℂ
        {S : Ba ℬ X | ∃ (i j : ι) (b : ℬ), S.1 = mketbra (b • e i) (e j)}) ∧
      UWTendsto approx atTop T :=
  sorry

/-- **159IX** (`ketbra-ultranorm-continuous`, dils.tex:4378, Proposition):
for a self-dual Hilbert ℬ-module `X`: if a norm-bounded net `x_α → x`
ultranorm, then `|x_α⟩⟨y| → |x⟩⟨y|` ultraweakly.

**159X**–**159XI** are the proof — not converted. -/
theorem ketbra_ultranorm_continuous [VonNeumannAlgebra ℬ]
    (hX : SelfDual ℬ X) {ι : Type v} {l : Filter ι} (x : ι → X) (x₀ : X)
    (hbdd : ∃ M : ℝ, ∀ i, ‖x i‖ ≤ M)
    (hx : UnTendsto (inner ℬ) x l x₀) (y : X)
    (K : ι → Ba ℬ X) (hK : ∀ i, (K i).1 = mketbra (x i) y)
    (K₀ : Ba ℬ X) (hK₀ : K₀.1 = mketbra x₀ y) :
    UWTendsto K l K₀ :=
  sorry

end Ketbra

/-! ## Parsec 1600: orthocomplements

**160I** (dils.tex:4456): introduction — nothing to formalize. -/

section Ortho

variable {ℬ : Type u} {X Y Z : Type v}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul ℬ Y] [CStarModule ℬ Y]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z] [SMul ℬ Z] [CStarModule ℬ Z]

/-- **160II** (`direct-prod-self-dual-basis`, dils.tex:4465, Exercise): the
direct sum of self-dual Hilbert ℬ-modules `X ⊕ Y` (represented abstractly:
a Hilbert ℬ-module `Z` with module embeddings `κ₁, κ₂` which are mutually
orthogonal, inner-product-preserving and jointly surjective) has
`κ₁(E) ∪ κ₂(F)` as an orthonormal basis for bases `E` of `X`, `F` of `Y`;
in particular it is self dual. -/
theorem direct_prod_self_dual_basis [VonNeumannAlgebra ℬ]
    [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z]
    (κ₁ : X → Z) (κ₂ : Y → Z)
    (h₁ : ∀ x x' : X, inner ℬ (κ₁ x) (κ₁ x') = inner ℬ x x')
    (h₂ : ∀ y y' : Y, inner ℬ (κ₂ y) (κ₂ y') = inner ℬ y y')
    (h₁₂ : ∀ (x : X) (y : Y), inner ℬ (κ₁ x) (κ₂ y) = 0)
    (hadd : ∀ z : Z, ∃ (x : X) (y : Y), z = κ₁ x + κ₂ y)
    (hκ₁ : ∀ (b : ℬ) (x : X), κ₁ (b • x) = b • κ₁ x)
    (hκ₂ : ∀ (b : ℬ) (y : Y), κ₂ (b • y) = b • κ₂ y)
    {ι κ : Type v} (e : ι → X) (d : κ → Y)
    (he : IsONBasis ℬ e) (hd : IsONBasis ℬ d) :
    IsONBasis ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d)) ∧ SelfDual ℬ Z :=
  sorry

variable (ℬ) in
/-- **160III** (dils.tex:4476, Definition): the **orthocomplement**
`V^⊥ = {x : ⟨x,v⟩ = 0 for all v ∈ V}` of a subset `V` of a Hilbert
C*-module. -/
def orthoCompl (V : Set X) : Set X :=
  {x : X | ∀ v ∈ V, inner ℬ x v = 0}

variable (ℬ) in
/-- The set of points ultranorm-approximable from `S` (the ultranorm
closure; auxiliary for **160IV**). -/
def unClosure (B : X → X → ℬ) (S : Set X) : Set X :=
  {x : X | ∀ (n : ℕ) (ωs : Fin n → NPFunctional ℬ) (ε : ℝ), 0 < ε →
    ∃ d ∈ S, ∀ i, unSeminorm (ωs i) B (x - d) ≤ ε}

variable (ℬ) in
/-- The ℬ-linear span of a subset of a Hilbert ℬ-module (auxiliary for
**160IV**). -/
def bSpan (V : Set X) : Set X :=
  {x : X | ∃ (n : ℕ) (c : Fin n → ℂ) (b : Fin n → ℬ) (v : Fin n → X),
    (∀ i, v i ∈ V) ∧ x = ∑ i, c i • b i • v i}

/-- **160IV** (`hilbmod-projthm`, dils.tex:4488, Proposition), part 1: for
a subset `V` of a self-dual Hilbert ℬ-module `X`, the orthocomplement
`V^⊥` is an ultranorm-closed ℬ-submodule of `X` (and hence so is
`V^⊥⊥`). -/
theorem hilbmod_projthm_1 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) (V : Set X) :
    (0 : X) ∈ orthoCompl ℬ V ∧
    (∀ x ∈ orthoCompl ℬ V, ∀ y ∈ orthoCompl ℬ V, x + y ∈ orthoCompl ℬ V) ∧
    (∀ (b : ℬ), ∀ x ∈ orthoCompl ℬ V, b • x ∈ orthoCompl ℬ V) ∧
    (∀ (c : ℂ), ∀ x ∈ orthoCompl ℬ V, c • x ∈ orthoCompl ℬ V) ∧
    unClosure ℬ (inner ℬ) (orthoCompl ℬ V) = orthoCompl ℬ V :=
  sorry

/-- **160IV** (`hilbmod-projthm`, dils.tex:4488, Proposition), part 2:
`V^⊥⊥` is the ultranorm closure of the ℬ-linear span of `V`. -/
theorem hilbmod_projthm_2 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) (V : Set X) :
    orthoCompl ℬ (orthoCompl ℬ V) = unClosure ℬ (inner ℬ) (bSpan ℬ V) :=
  sorry

/-- **160IV** (`hilbmod-projthm`, dils.tex:4488, Proposition), part 3:
`V^⊥⊥ ⊕ V^⊥ ≅ X` via `(x,y) ↦ x + y`: every element of `X` decomposes
uniquely as a sum of an element of `V^⊥⊥` and one of `V^⊥`.

**160V**–**160VIII** are the proof — not converted. -/
theorem hilbmod_projthm_3 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) (V : Set X) (x : X) :
    ∃! p : X × X, p.1 ∈ orthoCompl ℬ (orthoCompl ℬ V) ∧
      p.2 ∈ orthoCompl ℬ V ∧ x = p.1 + p.2 :=
  sorry

/-- **160IX** (`selfdual-orthn-basis`, dils.tex:4565, Exercise): for an
orthonormal family `(eᵢ)` in a self-dual Hilbert ℬ-module: (1) `(eᵢ)` is a
basis of `E^⊥⊥` (every `x ∈ E^⊥⊥` is the ultranorm limit of its basis
expansion); (2) `x ∈ E^⊥⊥` iff `⟨x,x⟩ = ∑ᵢ ⟨x,eᵢ⟩⟨eᵢ,x⟩` (mirrored). -/
theorem selfdual_orthn_basis [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) {ι : Type v} (e : ι → X)
    (he : OrthonormalFam ℬ e) (x : X) :
    (x ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) →
      UnTendsto (inner ℬ)
        (fun s : Finset ι => ∑ i ∈ s, inner ℬ (e i) x • e i) atTop x) ∧
    (x ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) ↔
      UWTendsto
        (fun s : Finset ι => ∑ i ∈ s, inner ℬ (e i) x * inner ℬ x (e i))
        atTop (inner ℬ x x)) :=
  sorry

/-- **160X** (`selfdual-gramschmidt`, dils.tex:4581, Exercise): for
`x₁, …, xₙ` in a self-dual Hilbert ℬ-module there is a finite orthonormal
basis of `{x₁,…,xₙ}^⊥⊥` of at most `n` elements (each `xᵢ` is its finite
basis expansion). -/
theorem selfdual_gramschmidt [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) {n : ℕ} (x : Fin n → X) :
    ∃ (m : ℕ), m ≤ n ∧ ∃ f : Fin m → X,
      OrthonormalFam ℬ f ∧
      (∀ k, f k ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range x))) ∧
      ∀ i, x i = ∑ k, inner ℬ (f k) (x i) • f k :=
  sorry

end Ortho

/-! ## Parsec 1610: ℓ²((pᵢ)) and orthonormal bases

**161I** (`thel2matter`, dils.tex:4594) and **161III** (`hilbel-matter`,
dils.tex:4625, counterexamples): discussion — nothing to formalize. -/

section L2

variable {ℬ : Type u}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

variable (ℬ) in
/-- The set `ℓ²((pᵢ)ᵢ)` of ℓ²-summable tuples `(bᵢ)` with
`⌈bᵢbᵢ*⌉ ≤ pᵢ` (**161II**; mirrored), as a subset of `ι → ℬ`. -/
def L2Set [VonNeumannAlgebra ℬ] {ι : Type v} (p : ι → ℬ) : Set (ι → ℬ) :=
  {b | L2Summable ℬ b ∧ ∀ i, ceil (b i * star (b i)) ≤ p i}

/-- **161II** (`hilbmod-el2`, dils.tex:4602, Exercise), part 1: for
ℓ²-summable tuples `(bᵢ)`, `(cᵢ)` over a von Neumann algebra the inner
product `∑ᵢ bᵢ* cᵢ` (mirrored: `∑ᵢ cᵢ bᵢ*`) converges ultraweakly; with
the coordinatewise operations this turns `ℓ²((pᵢ)ᵢ)` into a (pre-)Hilbert
ℬ-module. -/
theorem hilbmod_el2_inner [VonNeumannAlgebra ℬ] {ι : Type v} (b c : ι → ℬ)
    (hb : L2Summable ℬ b) (hc : L2Summable ℬ c) :
    ∃ s : ℬ, UWTendsto (fun t : Finset ι => ∑ i ∈ t, c i * star (b i))
      atTop s :=
  sorry

variable {X : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X]

/-- **161II** (`hilbmod-el2`, dils.tex:4602, Exercise), part 2:
`ℓ²((pᵢ)ᵢ)` is self dual, and every self-dual Hilbert ℬ-module `X` with
orthonormal basis `(eᵢ)ᵢ` is isomorphic to `ℓ²((⟨eᵢ,eᵢ⟩)ᵢ)` via the
coordinate map `x ↦ (⟨eᵢ,x⟩)ᵢ`: the coordinate map is injective, additive,
lands bijectively on `ℓ²((⟨eᵢ,eᵢ⟩)ᵢ)` and identifies the inner
products. -/
theorem hilbmod_el2 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) {ι : Type v} (e : ι → X) (he : IsONBasis ℬ e) :
    Set.BijOn (fun (x : X) (i : ι) => inner ℬ (e i) x) Set.univ
        (L2Set ℬ fun i => inner ℬ (e i) (e i)) ∧
      ∀ x y : X,
        UWTendsto
          (fun t : Finset ι =>
            ∑ i ∈ t, inner ℬ (e i) y * star (inner ℬ (e i) x))
          atTop (inner ℬ x y) :=
  sorry

/-- **161IV** (`onb1`, dils.tex:4673, Exercise), part 1: if `(eᵢ)` is an
orthonormal basis of a Hilbert ℬ-module `X` and `(uᵢ)` are partial
isometries with `uᵢuᵢ* = ⟨eᵢ,eᵢ⟩`, then `(eᵢuᵢ)ᵢ` (mirrored:
`star uᵢ • eᵢ`) is an orthonormal basis of `X`. -/
theorem onb1 [VonNeumannAlgebra ℬ] [CompleteSpace X] {ι : Type v}
    (e : ι → X) (he : IsONBasis ℬ e) (u : ι → ℬ)
    (hpi : ∀ i, IsStarProjection (star (u i) * u i))
    (hu : ∀ i, u i * star (u i) = inner ℬ (e i) (e i)) :
    IsONBasis ℬ fun i => star (u i) • e i :=
  sorry

/-- Murray–von Neumann equivalence `p ∼ q` of projections: `u* u = p` and
`u u* = q` for some partial isometry `u` (**161IV**; cf. vn.tex 83II
`vmleq`). -/
def MvNEquiv (p q : ℬ) : Prop :=
  ∃ u : ℬ, star u * u = p ∧ u * star u = q

/-- **161IV** (`onb1`, dils.tex:4673, Exercise), part 2:
`ℓ²((pᵢ)ᵢ) ≅ ℓ²((qᵢ)ᵢ)` for pointwise Murray–von Neumann equivalent
families of projections: there is a bijection between the tuple sets that
identifies the (ultraweakly converging) inner products. -/
theorem onb1_el2 [VonNeumannAlgebra ℬ] {ι : Type v} (p q : ι → ℬ)
    (hp : ∀ i, IsStarProjection (p i)) (hq : ∀ i, IsStarProjection (q i))
    (hpq : ∀ i, MvNEquiv (p i) (q i)) :
    ∃ Φ : (ι → ℬ) → (ι → ℬ),
      Set.BijOn Φ (L2Set ℬ p) (L2Set ℬ q) ∧
      ∀ b ∈ L2Set ℬ p, ∀ c ∈ L2Set ℬ p, ∀ s : ℬ,
        UWTendsto (fun t : Finset ι => ∑ i ∈ t, c i * star (b i)) atTop s ↔
        UWTendsto (fun t : Finset ι => ∑ i ∈ t, Φ c i * star (Φ b i))
          atTop s :=
  sorry

/-- **161V** (`onb2`, dils.tex:4696, Exercise): if `(eᵢ)` is an orthonormal
basis of `X` with distinguished indices `i₁ ≠ i₂` and
`⟨e_{i₁},e_{i₁}⟩ + ⟨e_{i₂},e_{i₂}⟩ ≤ 1`, then removing `e_{i₁}, e_{i₂}`
and inserting `e_{i₁} + e_{i₂}` again yields an orthonormal basis.  (The
consequence `pℬ ⊕ qℬ ≅ (p+q)ℬ` for `p + q ≤ 1` is not converted
separately.) -/
theorem onb2 [VonNeumannAlgebra ℬ] [CompleteSpace X] {ι : Type v}
    [DecidableEq ι]
    (e : ι → X) (he : IsONBasis ℬ e) (i₁ i₂ : ι) (hne : i₁ ≠ i₂)
    (hle : inner ℬ (e i₁) (e i₁) + inner ℬ (e i₂) (e i₂) ≤ 1) :
    IsONBasis ℬ fun i : {i : ι // i ≠ i₂} =>
      if (i : ι) = i₁ then e i₁ + e i₂ else e i :=
  sorry

end L2

/-! ## Parsec 1620: comparison of projections and the normal form

**162I** (dils.tex:4708): introduction — nothing to formalize. -/

section NormalForm

variable {ℬ : Type u}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

variable (ℬ) in
/-- A von Neumann algebra is a **factor** when its centre is `ℂ1`
(**162II**). -/
def IsFactor : Prop :=
  ∀ z : ℬ, IsCentral ℬ z → ∃ c : ℂ, z = algebraMap ℂ ℬ c

/-- The Murray–von Neumann preorder `p ≲ q` on projections: `u* u = p` and
`u u* ≤ q` for some `u` (dils.tex:4708, recalled from vn.tex 83II). -/
def MvNLe (p q : ℬ) : Prop :=
  ∃ u : ℬ, star u * u = p ∧ u * star u ≤ q

/-- **162II** (`total-mv-order`, dils.tex:4717, Proposition): in a factor,
any two projections are comparable: `p ≲ q` or `q ≲ p`.

**162III** is the proof — not converted. -/
theorem total_mv_order [VonNeumannAlgebra ℬ] (hF : IsFactor ℬ) (p q : ℬ)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    MvNLe p q ∨ MvNLe q p :=
  sorry

variable {X : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X]

/-- **162IV** (`selfdual-normalish-form`, dils.tex:4747, Theorem): every
self-dual Hilbert ℬ-module over a factor `ℬ` is isomorphic to
`ℓ²((1)_{α∈κ})` for an infinite cardinal `κ`, or to `ℓ²((1,…,1,p))` for
some `n ∈ ℕ` and projection `p`.  Stated through bases (cf. **161II**):
`X` has an orthonormal basis `(eᵢ)` such that either `⟨eᵢ,eᵢ⟩ = 1` for all
`i`, or the basis is finite and `⟨eᵢ,eᵢ⟩ = 1` for all but (at most) one
index.

**162V**–**162VII** are the proof; **162VIII** (dils.tex:4908, discussion
of non-uniqueness of κ) — not converted. -/
theorem selfdual_normalish_form [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hF : IsFactor ℬ) (hX : SelfDual ℬ X) :
    ∃ (ι : Type v) (e : ι → X), IsONBasis ℬ e ∧
      ((∀ i, inner ℬ (e i) (e i) = 1) ∨
        (Finite ι ∧ ∃ i₀ : ι, ∀ i, i ≠ i₀ → inner ℬ (e i) (e i) = 1)) :=
  sorry

end NormalForm

/-! ## Parsec 1630: the completion is determined by its universal property

**163I** (dils.tex:4927): introduction; **163III** is the proof — not
converted. -/

section CompletionDefining

variable {ℬ : Type u} {V : Type v}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [AddCommGroup V] [Module ℂ V] [SMul ℬ V]

/-- **163II** (`selfdual-compl-defining`, dils.tex:4935, Proposition),
uniqueness half: two self-dual completions of the same 𝒷-module with
𝒷-valued inner product (each has the universal property by **151Ia**) are
isomorphic by a unique inner-product-preserving module isomorphism
commuting with the embeddings. -/
theorem selfdual_compl_defining_unique [VonNeumannAlgebra ℬ]
    (B : BInner ℬ V) (E₁ E₂ : SelfDualCompletion.{u, v, v} B) :
    ∃! U : E₁.X → E₂.X,
      (∃ C : ℝ, IsBoundedModuleMap (cstarBInner ℬ E₁.X)
        (cstarBInner ℬ E₂.X) C U) ∧
      Function.Bijective U ∧
      (∀ x y : E₁.X, inner ℬ (U x) (U y) = inner ℬ x y) ∧
      ∀ v : V, U (E₁.η v) = E₂.η v :=
  sorry

/-- **163II** (`selfdual-compl-defining`, dils.tex:4935, Proposition),
moreover-clause: if an inner-product-preserving module map `η : V → X`
into a self-dual Hilbert ℬ-module has the universal property (every
bounded module map `V → Y` into a self-dual `Y` factors uniquely through
`η`), then the image of `η` is ultranorm dense. -/
theorem selfdual_compl_defining_dense [VonNeumannAlgebra ℬ]
    (B : BInner ℬ V) {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [SMul ℬ X] [CStarModule ℬ X] [CompleteSpace X] (hX : SelfDual ℬ X)
    (η : V → X) (hadd : ∀ v w, η (v + w) = η v + η w)
    (hsmulc : ∀ (c : ℂ) v, η (c • v) = c • η v)
    (hsmul : ∀ (b : ℬ) v, η (b • v) = b • η v)
    (hinner : ∀ v w, inner ℬ (η v) (η w) = B.inner v w)
    (huniv : ∀ (Y : Type v) (_ : NormedAddCommGroup Y) (_ : NormedSpace ℂ Y)
      (_ : SMul ℬ Y) (_ : CStarModule ℬ Y) (_ : CompleteSpace Y),
      SelfDual ℬ Y → ∀ (C : ℝ) (T : V → Y),
        IsBoundedModuleMap B (cstarBInner ℬ Y) C T →
        ∃! T' : X → Y,
          (∃ C' : ℝ, IsBoundedModuleMap (cstarBInner ℬ X)
            (cstarBInner ℬ Y) C' T') ∧ ∀ v, T' (η v) = T v) :
    UnDense (inner ℬ) (Set.range η) :=
  sorry

end CompletionDefining

/-! ## The von Neumann algebra tensor product interface

NOTE(proc-dep): axiomatization of thesis A's tensor product of von Neumann
algebras (proc.tex 108II, label `tensor`), used by parsecs 1640–1670. -/

section VNTensor

variable {𝒜 ℬ 𝒞 : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]

variable (𝒜 ℬ) in
/-- An np-functional on `𝒞` is a *product functional* for a bilinear map
`t : 𝒜 × ℬ → 𝒞` when it is of the form `ω ⊗ ξ` on the image of `t`. -/
def IsProductFunctional (t : 𝒜 → ℬ → 𝒞) (Ω : NPFunctional 𝒞) : Prop :=
  ∃ (ω : NPFunctional 𝒜) (ξ : NPFunctional ℬ),
    ∀ (a : 𝒜) (b : ℬ), Ω (t a b) = ω a * ξ b

/-- The interface of the tensor product `𝒞 = 𝒜 ⊗ ℬ` of von Neumann
algebras (proc.tex 108II, `tensor`): an miu-bilinear map
`t : 𝒜 × ℬ → 𝒞` whose image generates `𝒞` as a von Neumann algebra and
whose product np-functionals are separating. -/
structure IsVNTensor (t : 𝒜 → ℬ → 𝒞) : Prop where
  add_left : ∀ (a a' : 𝒜) (b : ℬ), t (a + a') b = t a b + t a' b
  add_right : ∀ (a : 𝒜) (b b' : ℬ), t a (b + b') = t a b + t a b'
  smul_complex : ∀ (c : ℂ) (a : 𝒜) (b : ℬ), t (c • a) b = c • t a b
  mul : ∀ (a a' : 𝒜) (b b' : ℬ), t a b * t a' b' = t (a * a') (b * b')
  one : t 1 1 = 1
  star : ∀ (a : 𝒜) (b : ℬ), star (t a b) = t (star a) (star b)
  generates : wstar 𝒞 (Set.range fun p : 𝒜 × ℬ => t p.1 p.2) = ⊤
  separating : ∀ z : 𝒞, 0 ≤ z →
    (∀ Ω : NPFunctional 𝒞, IsProductFunctional 𝒜 ℬ t Ω → Ω z = 0) → z = 0

end VNTensor

/-! ## Parsec 1640: the self-dual exterior tensor product

**164I** (dils.tex:4987): introduction — nothing to formalize. -/

section ExtTensor

variable {𝒜 ℬ 𝒞 : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]
  {X Y : Type u}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒜 X] [CStarModule 𝒜 X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul ℬ Y] [CStarModule ℬ Y]

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), the data:
a **self-dual exterior tensor product** of a self-dual Hilbert 𝒜-module
`X` and a self-dual Hilbert ℬ-module `Y` over the von Neumann tensor
product `𝒞 = 𝒜 ⊗ ℬ` (given by `t`): a self-dual Hilbert 𝒞-module `Z`
with a bilinear `η : X × Y → Z` satisfying
`η(xa, yb) = (a ⊗ b)·η(x,y)` and
`⟨η(x,y), η(x',y')⟩ = ⟨x,x'⟩ ⊗ ⟨y,y'⟩`, whose image spans an
ultranorm-dense submodule, and which is universal among bounded
`𝒜 ⊙ ℬ`-bilinear maps into self-dual Hilbert 𝒞-modules. -/
structure ExtTensor (t : 𝒜 → ℬ → 𝒞) (ht : IsVNTensor t)
    (X Y : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒜 X]
    [CStarModule 𝒜 X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul ℬ Y]
    [CStarModule ℬ Y] : Type (u + 1) where
  /-- The carrier `X ⊗ Y`. -/
  Z : Type u
  [nacg : NormedAddCommGroup Z]
  [nsp : NormedSpace ℂ Z]
  [smul : SMul 𝒞 Z]
  [cstarMod : CStarModule 𝒞 Z]
  [complete : CompleteSpace Z]
  /-- `X ⊗ Y` is self dual. -/
  selfDual : SelfDual 𝒞 Z
  /-- The bilinear map `η(x, y) = x ⊗ y`. -/
  η : X → Y → Z
  η_add_left : ∀ (x x' : X) (y : Y), η (x + x') y = η x y + η x' y
  η_add_right : ∀ (x : X) (y y' : Y), η x (y + y') = η x y + η x y'
  η_smul_complex : ∀ (c : ℂ) (x : X) (y : Y), η (c • x) y = c • η x y
  /-- `η(xa, yb) = (a ⊗ b) η(x,y)` (mirrored). -/
  η_smul : ∀ (a : 𝒜) (b : ℬ) (x : X) (y : Y),
    η (a • x) (b • y) = t a b • η x y
  /-- `⟨x ⊗ y, x' ⊗ y'⟩ = ⟨x,x'⟩ ⊗ ⟨y,y'⟩`. -/
  η_inner : ∀ (x x' : X) (y y' : Y),
    inner 𝒞 (η x y) (η x' y') = t (inner 𝒜 x x') (inner ℬ y y')
  /-- Universal property: bounded `𝒜 ⊙ ℬ`-bilinear maps into self-dual
  Hilbert 𝒞-modules factor uniquely through `η`. -/
  univ : ∀ (W : Type u) (_ : NormedAddCommGroup W) (_ : NormedSpace ℂ W)
    (_ : SMul 𝒞 W) (_ : CStarModule 𝒞 W) (_ : CompleteSpace W),
    SelfDual 𝒞 W →
    ∀ T : X → Y → W,
      (∀ (x x' : X) (y : Y), T (x + x') y = T x y + T x' y) →
      (∀ (x : X) (y y' : Y), T x (y + y') = T x y + T x y') →
      (∀ (a : 𝒜) (b : ℬ) (x : X) (y : Y),
        T (a • x) (b • y) = t a b • T x y) →
      (∃ C : ℝ, ∀ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
        ‖∑ i, T (x i) (y i)‖ ^ 2 ≤
          C * ‖∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))‖) →
      ∃! T' : Z → W,
        (∃ C' : ℝ, IsBoundedModuleMap (cstarBInner 𝒞 Z) (cstarBInner 𝒞 W)
          C' T') ∧ ∀ (x : X) (y : Y), T' (η x y) = T x y

attribute [instance] ExtTensor.nacg ExtTensor.nsp ExtTensor.smul
  ExtTensor.cstarMod ExtTensor.complete

variable {t : 𝒜 → ℬ → 𝒞} {ht : IsVNTensor t}

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), existence:
for self-dual `X`, `Y` over von Neumann algebras the self-dual exterior
tensor product exists.

**164III**–**164VIII** (construction via `ℓ²((pᵢⱼ))` and its proof,
including `ext-tensor-dfn-eta`, `ext-tensor-preserves-inner-prod`,
injectivity of `η`, `ultranorm-dense-tensor-base`) are proof steps — not
converted separately. -/
theorem univprop_ext_tensor [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) :
    Nonempty (ExtTensor t ht X Y) :=
  sorry

/-- **164IX** (`ext-tensor-uniqueness`, dils.tex:5286, Uniqueness — stated
in **164II** as "up-to-isomorphism unique"): two self-dual exterior tensor
products are isomorphic by a unique inner-product-preserving module
isomorphism commuting with the embeddings. -/
theorem ext_tensor_uniqueness [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y)
    (E₁ E₂ : ExtTensor t ht X Y) :
    ∃! U : E₁.Z → E₂.Z,
      (∃ C : ℝ, IsBoundedModuleMap (cstarBInner 𝒞 E₁.Z)
        (cstarBInner 𝒞 E₂.Z) C U) ∧
      Function.Bijective U ∧
      (∀ z z' : E₁.Z, inner 𝒞 (U z) (U z') = inner 𝒞 z z') ∧
      ∀ (x : X) (y : Y), U (E₁.η x y) = E₂.η x y :=
  sorry

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), property 1:
the (span of the) image of `η` is ultranorm dense in `X ⊗ Y`. -/
theorem ext_tensor_dense [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y) :
    UnDense (inner 𝒞)
      {z : E.Z | ∃ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
        z = ∑ i, E.η (x i) (y i)} :=
  sorry

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), property 2a:
for orthonormal bases `(eᵢ)` of `X` and `(dⱼ)` of `Y`, the family
`(eᵢ ⊗ dⱼ)` is an orthonormal basis of `X ⊗ Y`. -/
theorem ext_tensor_basis [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    {ι κ : Type u} (e : ι → X) (d : κ → Y)
    (he : IsONBasis 𝒜 e) (hd : IsONBasis ℬ d) :
    IsONBasis 𝒞 fun p : ι × κ => E.η (e p.1) (d p.2) :=
  sorry

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), property 2b:
the linear span of the `|(eᵢa) ⊗ (dⱼb)⟩⟨e_k ⊗ d_l|` is ultraweakly dense
in `𝒞ᵃ(X ⊗ Y)`.

**164X**–**164XI** are the proof; **164XII** (Examples) — not
converted. -/
theorem ext_tensor_ketbra_dense [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    {ι κ : Type u} (e : ι → X) (d : κ → Y)
    (he : IsONBasis 𝒜 e) (hd : IsONBasis ℬ d) (T : Ba 𝒞 E.Z) :
    ∃ approx : Finset (ι × κ) → Ba 𝒞 E.Z,
      (∀ s, approx s ∈ Submodule.span ℂ
        {S : Ba 𝒞 E.Z | ∃ (i k : ι) (j l : κ) (a : 𝒜) (b : ℬ),
          S.1 = mketbra (E.η (a • e i) (b • d j)) (E.η (e k) (d l))}) ∧
      UWTendsto approx atTop T :=
  sorry

/-! ## Parsec 1650: 𝒷ᵃ(X) ⊗ 𝒷ᵃ(Y) ≅ 𝒷ᵃ(X ⊗ Y)

**165I** (dils.tex:5407): introduction; **165II** (Setting) — nothing to
formalize. -/

/-- **165III** (`dfn-tensor-of-hilbmod-maps`, dils.tex:5426, Proposition):
for `S ∈ 𝒜ᵃ(X)` and `T ∈ ℬᵃ(Y)` there is a unique operator
`S ⊗ T ∈ 𝒞ᵃ(X ⊗ Y)` with `(S ⊗ T)(x ⊗ y) = (Sx) ⊗ (Ty)`.

**165IV** is the proof — not converted. -/
theorem dfn_tensor_of_hilbmod_maps [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] [VonNeumannAlgebra 𝒞] [CompleteSpace X]
    [CompleteSpace Y] (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y)
    (E : ExtTensor t ht X Y) (S : Ba 𝒜 X) (T : Ba ℬ Y) :
    ∃! R : Ba 𝒞 E.Z,
      ∀ (x : X) (y : Y), R.1 (E.η x y) = E.η (S.1 x) (T.1 y) :=
  sorry

/-- **165V** (`hilbmod-tensor-ketbra`, dils.tex:5506, Exercise): the rules
for `⊗` of module operators: (1) `|x₁⟩⟨x₂| ⊗ |y₁⟩⟨y₂| = |x₁⊗y₁⟩⟨x₂⊗y₂|`;
(2) `1 ⊗ 1 = 1`; (3) `(S ⊗ T)(S' ⊗ T') = SS' ⊗ TT'`;
(4) `(S ⊗ T)* = S* ⊗ T*`.  (Stated for operators characterized by their
values on elementary tensors, as in **165III**.) -/
theorem hilbmod_tensor_ketbra [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    (S S' : Ba 𝒜 X) (T T' : Ba ℬ Y) (R R' R'' : Ba 𝒞 E.Z)
    (hR : ∀ x y, R.1 (E.η x y) = E.η (S.1 x) (T.1 y))
    (hR' : ∀ x y, R'.1 (E.η x y) = E.η (S'.1 x) (T'.1 y))
    (hR'' : ∀ x y, R''.1 (E.η x y) = E.η ((S * S').1 x) ((T * T').1 y)) :
    (∀ (x₁ x₂ : X) (y₁ y₂ : Y),
      (∀ x y, R.1 (E.η x y) =
          E.η ((mketbra x₁ x₂ : X →L[ℂ] X) x) ((mketbra y₁ y₂) y)) →
        R.1 = mketbra (E.η x₁ y₁) (E.η x₂ y₂)) ∧
    ((∀ x y, R.1 (E.η x y) = E.η x y) → R = 1) ∧
    R * R' = R'' ∧
    (∀ x y, (star R).1 (E.η x y) = E.η ((star S).1 x) ((star T).1 y)) :=
  sorry

/-- **165VI** (`ba-ext-tensor-pres`, dils.tex:5531, Theorem): there is an
nmiu-isomorphism `𝒜ᵃ(X) ⊗ ℬᵃ(Y) ≅ 𝒞ᵃ(X ⊗ Y)` sending `S ⊗ T` to
`S ⊗ T`; stated as: the bilinear map `Θ(S,T) = S ⊗ T` exhibits
`𝒞ᵃ(X ⊗ Y)` as the von Neumann tensor product of `𝒜ᵃ(X)` and `ℬᵃ(Y)`.

**165VII**–**165X** are the proof — not converted. -/
theorem ba_ext_tensor_pres [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    (Θ : Ba 𝒜 X → Ba ℬ Y → Ba 𝒞 E.Z)
    (hΘ : ∀ (S : Ba 𝒜 X) (T : Ba ℬ Y) (x : X) (y : Y),
      (Θ S T).1 (E.η x y) = E.η (S.1 x) (T.1 y)) :
    IsVNTensor Θ :=
  sorry

/-! ## Parsec 1660: ultranorm continuity of the exterior tensor product

**166I** (dils.tex:5625): introduction; **166III**, **166V**, **166VII**
are proofs — not converted. -/

/-- **166II** (`ultranorm-continuity-ext-tensor`, dils.tex:5630, Lemma): if
`x_α → x` and `y_α → y` ultranorm for norm-bounded nets, then
`x_α ⊗ y_α → x ⊗ y` ultranorm. -/
theorem ultranorm_continuity_ext_tensor [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] [VonNeumannAlgebra 𝒞] [CompleteSpace X]
    [CompleteSpace Y] (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y)
    (E : ExtTensor t ht X Y) {ι : Type u} {l : Filter ι}
    (x : ι → X) (x₀ : X) (y : ι → Y) (y₀ : Y)
    (hxb : ∃ M : ℝ, ∀ i, ‖x i‖ ≤ M) (hyb : ∃ M : ℝ, ∀ i, ‖y i‖ ≤ M)
    (hx : UnTendsto (inner 𝒜) x l x₀) (hy : UnTendsto (inner ℬ) y l y₀) :
    UnTendsto (inner 𝒞) (fun i => E.η (x i) (y i)) l (E.η x₀ y₀) :=
  sorry

/-- **166IV** (`exttensor-dense-subsets`, dils.tex:5669, Lemma): for
ultranorm-dense submodules `U ⊆ X` and `V ⊆ Y`, the linear span of
`U ⊗ V = {u ⊗ v}` is ultranorm dense in `X ⊗ Y`. -/
theorem exttensor_dense_subsets [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    (U : Set X) (V : Set Y)
    (hU : UnDense (inner 𝒜) U) (hV : UnDense (inner ℬ) V)
    (hUsub : ∀ u ∈ U, ∀ u' ∈ U, u + u' ∈ U)
    (hUsmul : ∀ (a : 𝒜), ∀ u ∈ U, a • u ∈ U)
    (hVsub : ∀ v ∈ V, ∀ v' ∈ V, v + v' ∈ V)
    (hVsmul : ∀ (b : ℬ), ∀ v ∈ V, b • v ∈ V) :
    UnDense (inner 𝒞)
      {z : E.Z | ∃ (n : ℕ) (u : Fin n → X) (v : Fin n → Y),
        (∀ i, u i ∈ U) ∧ (∀ i, v i ∈ V) ∧ z = ∑ i, E.η (u i) (v i)} :=
  sorry

end ExtTensor

/-- **166VI** (`dilationspace-dense-subset`, dils.tex:5695, Lemma): for an
ncp-map `φ : 𝒜 → ℬ` between von Neumann algebras with ultrastrongly dense
∗-subalgebras `𝒜' ⊆ 𝒜`, `ℬ' ⊆ ℬ`, the linear span of
`{a ⊗ b : a ∈ 𝒜', b ∈ ℬ'}` is ultranorm dense in `𝒜 ⊗_φ ℬ`. -/
theorem dilationspace_dense_subset {𝒜 ℬ : Type u}
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (A' : StarSubalgebra ℂ 𝒜) (B' : StarSubalgebra ℂ ℬ)
    (hA : UnDense (mulInner 𝒜) (A' : Set 𝒜))
    (hB : UnDense (mulInner ℬ) (B' : Set ℬ)) :
    UnDense (inner ℬ)
      {z : M.X | ∃ (n : ℕ) (a : Fin n → 𝒜) (b : Fin n → ℬ),
        (∀ i, a i ∈ A') ∧ (∀ i, b i ∈ B') ∧
        z = ∑ i, M.tprod (a i) (b i)} :=
  sorry

/-! ## Parsec 1670: the tensor product of Paschke dilations -/

section PaschkeTensor

variable {𝒜₁ 𝒜₂ 𝒜₁₂ ℬ₁ ℬ₂ ℬ₁₂ P₁₂ : Type u}
  [CStarAlgebra 𝒜₁] [PartialOrder 𝒜₁] [StarOrderedRing 𝒜₁]
  [CStarAlgebra 𝒜₂] [PartialOrder 𝒜₂] [StarOrderedRing 𝒜₂]
  [CStarAlgebra 𝒜₁₂] [PartialOrder 𝒜₁₂] [StarOrderedRing 𝒜₁₂]
  [CStarAlgebra ℬ₁] [PartialOrder ℬ₁] [StarOrderedRing ℬ₁]
  [CStarAlgebra ℬ₂] [PartialOrder ℬ₂] [StarOrderedRing ℬ₂]
  [CStarAlgebra ℬ₁₂] [PartialOrder ℬ₁₂] [StarOrderedRing ℬ₁₂]
  [CStarAlgebra P₁₂] [PartialOrder P₁₂] [StarOrderedRing P₁₂]

/-- **167I** (`paschke-tensor`, dils.tex:5746, Theorem), main claim: if
`(𝒫ᵢ, ϱᵢ, hᵢ)` is a Paschke dilation of the ncp-map `φᵢ : 𝒜ᵢ → ℬᵢ`
(i = 1,2), then `(𝒫₁ ⊗ 𝒫₂, ϱ₁ ⊗ ϱ₂, h₁ ⊗ h₂)` is a Paschke dilation of
`φ₁ ⊗ φ₂`.  (The tensor products of algebras are given through the
`IsVNTensor` interface, and the tensor products of maps through their
characterizing values on elementary tensors.)

**167II**–**167VI** are the proof — not converted. -/
theorem paschke_tensor
    (tA : 𝒜₁ → 𝒜₂ → 𝒜₁₂) (htA : IsVNTensor tA)
    (tB : ℬ₁ → ℬ₂ → ℬ₁₂) (htB : IsVNTensor tB)
    (φ₁ : NCPMap 𝒜₁ ℬ₁) (φ₂ : NCPMap 𝒜₂ ℬ₂)
    (D₁ : PaschkeTriple 𝒜₁ ℬ₁) (D₂ : PaschkeTriple 𝒜₂ ℬ₂)
    (h₁ : IsPaschkeDilationOf D₁ ⇑φ₁) (h₂ : IsPaschkeDilationOf D₂ ⇑φ₂)
    (tP : D₁.P → D₂.P → P₁₂) (htP : IsVNTensor tP)
    (vnP : VonNeumannAlgebra P₁₂)
    (Φ : NCPMap 𝒜₁₂ ℬ₁₂)
    (hΦ : ∀ (a₁ : 𝒜₁) (a₂ : 𝒜₂), Φ (tA a₁ a₂) = tB (φ₁ a₁) (φ₂ a₂))
    (R : NMIUMap 𝒜₁₂ P₁₂)
    (hR : ∀ (a₁ : 𝒜₁) (a₂ : 𝒜₂), R (tA a₁ a₂) = tP (D₁.ρ a₁) (D₂.ρ a₂))
    (H : NCPMap P₁₂ ℬ₁₂)
    (hH : ∀ (c₁ : D₁.P) (c₂ : D₂.P),
      H (tP c₁ c₂) = tB (D₁.h c₁) (D₂.h c₂)) :
    IsPaschkeDilationOf ⟨P₁₂, vnP, R, H⟩ ⇑Φ :=
  sorry

/-- **167I** (`paschke-tensor`, dils.tex:5746, Theorem), furthermore-claim
(dils.tex:5754): the dilation spaces satisfy
`(𝒜₁ ⊗_{φ₁} ℬ₁) ⊗ (𝒜₂ ⊗_{φ₂} ℬ₂) ≅ (𝒜₁ ⊗ 𝒜₂) ⊗_{φ₁⊗φ₂} (ℬ₁ ⊗ ℬ₂)`,
via the map determined on elementary tensors. -/
theorem paschke_tensor_module
    [VonNeumannAlgebra 𝒜₁] [VonNeumannAlgebra 𝒜₂] [VonNeumannAlgebra 𝒜₁₂]
    [VonNeumannAlgebra ℬ₁] [VonNeumannAlgebra ℬ₂] [VonNeumannAlgebra ℬ₁₂]
    (tA : 𝒜₁ → 𝒜₂ → 𝒜₁₂) (htA : IsVNTensor tA)
    (tB : ℬ₁ → ℬ₂ → ℬ₁₂) (htB : IsVNTensor tB)
    (φ₁ : NCPMap 𝒜₁ ℬ₁) (φ₂ : NCPMap 𝒜₂ ℬ₂)
    (M₁ : PaschkeModule φ₁) (M₂ : PaschkeModule φ₂)
    (Φ : NCPMap 𝒜₁₂ ℬ₁₂)
    (hΦ : ∀ (a₁ : 𝒜₁) (a₂ : 𝒜₂), Φ (tA a₁ a₂) = tB (φ₁ a₁) (φ₂ a₂))
    (M₁₂ : PaschkeModule Φ)
    (E : ExtTensor tB htB M₁.X M₂.X) :
    ∃ U : E.Z → M₁₂.X,
      (∃ C : ℝ, IsBoundedModuleMap (cstarBInner ℬ₁₂ E.Z)
        (cstarBInner ℬ₁₂ M₁₂.X) C U) ∧
      Function.Bijective U ∧
      (∀ z z' : E.Z, inner ℬ₁₂ (U z) (U z') = inner ℬ₁₂ z z') ∧
      ∀ (a₁ : 𝒜₁) (b₁ : ℬ₁) (a₂ : 𝒜₂) (b₂ : ℬ₂),
        U (E.η (M₁.tprod a₁ b₁) (M₂.tprod a₂ b₂)) =
          M₁₂.tprod (tA a₁ a₂) (tB b₁ b₂) :=
  sorry

end PaschkeTensor

end Theses.B.Dils
