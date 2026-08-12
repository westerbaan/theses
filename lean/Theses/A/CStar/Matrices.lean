/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 1: C*-algebras — cstar.tex, lines 4959–5872.

  §Matrices over C*-algebras
    parsec 320:  Hilbert 𝒜-modules, Cauchy–Schwarz, the C*-algebra B^a(X)
    parsec 330:  the C*-algebra M_N(𝒜) of matrices over a C*-algebra,
                 positive matrices, entrywise application of maps
    parsec 340:  complete positivity: M_N f, examples, positive maps out of
                 or into commutative C*-algebras are cp, the cp
                 Cauchy–Schwarz, Russo–Dye for cp-maps, Choi's lemma
    parsec 341:  unitaries, Russo–Dye, ‖f‖ = ‖f(1)‖ for positive maps

Statements only; every proof is `sorry`.  See CONVENTIONS.md for the
numbering (**34V** = parsec 340, point 50) and naming conventions.
-/
import Theses.A.CStar.Representation

open scoped ComplexOrder ComplexInnerProductSpace ComplexStarModule CStarAlgebra
  WithCStarModule ENNReal unitInterval
open Filter Topology

namespace Theses.A.CStar

/-! ## Parsec 320: Hilbert 𝒜-modules

**31I** (cstar.tex:4961): introduction — nothing to formalize.

**32I** (`chilb-basic`, cstar.tex:4981, Definition): an *𝒜-valued inner
product* on an 𝒜-module `X`, definiteness, *pre-Hilbert 𝒜-module*, *Hilbert
𝒜-module* — in Mathlib the class `CStarModule 𝒜 X` (which also bundles the
norm of **32IX**), completeness being `[CompleteSpace X]`.  Adjointness of a
pair of maps between pre-Hilbert 𝒜-modules is defined here; the space
`B^a(X, Y)` of adjointable bounded module maps is treated through the
predicates below (cf. **32XIII**). -/

section HilbertModules

variable (𝒜 : Type*) {X Y Z : Type*} [CStarAlgebra 𝒜]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒜 X] [CStarModule 𝒜 X]
  [NormedAddCommGroup Y] [Module ℂ Y] [SMul 𝒜 Y] [CStarModule 𝒜 Y]
  [NormedAddCommGroup Z] [Module ℂ Z] [SMul 𝒜 Z] [CStarModule 𝒜 Z]

/-- **32I** (`chilb-basic`, cstar.tex:4981, Definition): a map `T : X → Y`
between pre-Hilbert 𝒜-modules is *adjoint to* `S : Y → X` when
`⟨Tx, y⟩ = ⟨x, Sy⟩` for all `x, y`. -/
def ModuleAdjointTo (T : X → Y) (S : Y → X) : Prop :=
  ∀ (x : X) (y : Y), inner 𝒜 (T x) y = inner 𝒜 x (S y)

/-- **32I** (`chilb-basic`, cstar.tex:4981, Definition): a map between
pre-Hilbert 𝒜-modules is *adjointable* when it is adjoint to some map. -/
def ModuleAdjointable (T : X → Y) : Prop :=
  ∃ S : Y → X, ModuleAdjointTo 𝒜 T S

variable {𝒜}

/-- **32I** (`chilb-basic`, cstar.tex:4981, Definition), embedded claim: a
map is adjoint to at most one map, denoted `T*`. -/
theorem moduleAdjointTo_unique (T : X → Y) (S S' : Y → X)
    (h : ModuleAdjointTo 𝒜 T S) (h' : ModuleAdjointTo 𝒜 T S') : S = S' :=
  sorry

/-- **32I** (`chilb-basic`, cstar.tex:4981, Definition), embedded claim: an
adjointable map is automatically linear and a module map. -/
theorem moduleAdjointable_linear (T : X → Y) (hT : ModuleAdjointable 𝒜 T) :
    (∀ x x' : X, T (x + x') = T x + T x') ∧
      (∀ (c : ℂ) (x : X), T (c • x) = c • T x) ∧
      ∀ (a : 𝒜) (x : X), T (a • x) = a • T x :=
  sorry

/-! **32II** (cstar.tex:5038, Example): `𝒜^N` with
`⟨x, y⟩ = ∑ₙ xₙ* yₙ` is a Hilbert 𝒜-module — Mathlib:
`WithCStarModule 𝒜 (Fin N → 𝒜)` (notation `C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜)`) with its
`CStarModule` instance. -/

/-- **32III** (cstar.tex:5044, Exercise), part 1: if `T` is adjoint to `S`
then `S` is adjoint to `T` (so `T** = T`). -/
theorem moduleAdjointTo_symm (T : X → Y) (S : Y → X)
    (h : ModuleAdjointTo 𝒜 T S) : ModuleAdjointTo 𝒜 S T :=
  sorry

/-- **32III** (cstar.tex:5044, Exercise), part 2: `(T + T')* = T* + T'*` and
`(λT)* = λ̄ T*`. -/
theorem moduleAdjointTo_add_smul (T T' : X → Y) (S S' : Y → X) (c : ℂ)
    (h : ModuleAdjointTo 𝒜 T S) (h' : ModuleAdjointTo 𝒜 T' S') :
    ModuleAdjointTo 𝒜 (fun x => T x + T' x) (fun y => S y + S' y) ∧
      ModuleAdjointTo 𝒜 (fun x => c • T x)
        (fun y => (starRingEnd ℂ) c • S y) :=
  sorry

/-- **32III** (cstar.tex:5044, Exercise), part 3: `ST` is adjoint to
`T* S*`, i.e. `(ST)* = T* S*`. -/
theorem moduleAdjointTo_comp (T : X → Y) (S : Y → Z) (T' : Y → X)
    (S' : Z → Y) (hT : ModuleAdjointTo 𝒜 T T') (hS : ModuleAdjointTo 𝒜 S S') :
    ModuleAdjointTo 𝒜 (S ∘ T) (T' ∘ S') :=
  sorry

end HilbertModules

/-- **32IV** (cstar.tex:5059, Exercise), part 1: `J = {f ∈ C[0,1] : f(0)=0}`
is a closed (right) ideal of `C[0,1]`, and thus a Hilbert `C[0,1]`-module
with `⟨f, g⟩ = f* g`. -/
theorem paschke_ideal_closed :
    IsClosed {f : C(unitInterval, ℂ) | f 0 = 0} :=
  sorry

/-- **32IV** (cstar.tex:5059, Exercise), part 2: the inclusion `J → C[0,1]`
is a bounded module map with no adjoint: there is no `b ∈ J` with
`⟨b, a⟩ = a` for all `a ∈ J` (so, unlike for Hilbert spaces (**5XI**), a
bounded module map between Hilbert 𝒜-modules need not be adjointable;
**32V**, Remark, on self-dual modules is not converted). -/
theorem paschke_inclusion_no_adjoint :
    ¬∃ b : C(unitInterval, ℂ), b 0 = 0 ∧
      ∀ a : C(unitInterval, ℂ), a 0 = 0 → star b * a = a :=
  sorry

section CauchySchwarz

variable {𝒜 : Type*} {X Y : Type*} [CStarAlgebra 𝒜]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒜 X] [CStarModule 𝒜 X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul 𝒜 Y] [CStarModule 𝒜 Y]

/-- **32VI** (`chilb-cs`, cstar.tex:5096, Proposition (Cauchy–Schwarz)):
`⟨x,y⟩ ⟨y,x⟩ ≤ ‖⟨y,y⟩‖ ⟨x,x⟩` for an 𝒜-valued inner product.  (**32VII**,
Remark: the norm sign cannot be removed; not converted.  Mathlib:
`CStarModule.inner_mul_inner_swap_le`.) -/
theorem chilb_cs (x y : X) :
    inner 𝒜 x y * inner 𝒜 y x ≤ ‖inner 𝒜 y y‖ • inner 𝒜 x x :=
  sorry

/-- **32IX** (`chilb-norm-basic`, cstar.tex:5161, Exercise), part 1:
`‖x‖ = ‖⟨x,x⟩‖^{1/2}` is a norm on a pre-Hilbert 𝒜-module `X` — in Mathlib
this is the bundled norm of the `CStarModule` class
(`CStarModule.norm_eq_sqrt_norm_inner_self`), recorded here. -/
theorem chilb_norm_basic_1 (x : X) :
    ‖x‖ = Real.sqrt ‖inner 𝒜 x x‖ :=
  sorry

/-- **32IX** (`chilb-norm-basic`, cstar.tex:5161, Exercise), part 2:
`‖x·b‖ ≤ ‖x‖ ‖b‖` (here in left-action notation `b • x`) and
`‖⟨x,y⟩‖ ≤ ‖x‖ ‖y‖`. -/
theorem chilb_norm_basic_2 (x y : X) (b : 𝒜) :
    ‖b • x‖ ≤ ‖x‖ * ‖b‖ ∧ ‖inner 𝒜 x y‖ ≤ ‖x‖ * ‖y‖ :=
  sorry

/-- **32X** (`chilb-form-bounded`, cstar.tex:5178, Lemma): for a linear map
`T : X → Y` between pre-Hilbert 𝒜-modules and `B > 0`: `T` is bounded by
`B` iff `‖⟨y, Tx⟩‖ ≤ B ‖y‖ ‖x‖` for all `x, y`. -/
theorem chilb_form_bounded (T : X →ₗ[ℂ] Y) (B : ℝ) (hB : 0 < B) :
    (∀ x : X, ‖T x‖ ≤ B * ‖x‖) ↔
      ∀ (x : X) (y : Y), ‖inner 𝒜 y (T x)‖ ≤ B * ‖y‖ * ‖x‖ :=
  sorry

/-- **32X** (`chilb-form-bounded`, cstar.tex:5178, Lemma), second part: for
an adjointable bounded map, `‖T*‖ = ‖T‖`. -/
theorem chilb_form_bounded_adjoint (T : X →L[ℂ] Y) (S : Y →L[ℂ] X)
    (h : ModuleAdjointTo 𝒜 ⇑T ⇑S) : ‖S‖ = ‖T‖ :=
  sorry

/-- **32XII** (`module-maps-cstar-identity`, cstar.tex:5220, Exercise):
`‖T* T‖ = ‖T‖²` for every adjointable bounded map `T` on a pre-Hilbert
𝒜-module. -/
theorem module_maps_cstar_identity (T S : X →L[ℂ] X)
    (h : ModuleAdjointTo 𝒜 ⇑T ⇑S) : ‖S.comp T‖ = ‖T‖ ^ 2 :=
  sorry

/-- **32XIII** (`bax-cstar`, cstar.tex:5225, Proposition): the adjointable
bounded module maps on a Hilbert 𝒜-module `X` form a C*-algebra `B^a(X)`.
The missing ingredient beyond **4VII** and **32XII** is that `B^a(X)` is
closed in the bounded operators on `X`, which is stated here. -/
theorem bax_cstar [CompleteSpace X] :
    IsClosed {T : X →L[ℂ] X | ModuleAdjointable 𝒜 ⇑T} :=
  sorry

/-- **32XV** (`chilb-vector-states-order-separating`, cstar.tex:5268,
Exercise), part 1 — the vector functionals `⟨x, (·) x⟩` on `B^a(X)` are
order separating; consequently, for an adjointable operator `T` with adjoint
`S`: `T` is self-adjoint (`T = T*`) iff `⟨x, Tx⟩` is self-adjoint for all
`x` in the unit ball. -/
theorem chilb_vector_states_1 [CompleteSpace X] (T S : X →L[ℂ] X)
    (h : ModuleAdjointTo 𝒜 ⇑T ⇑S) :
    T = S ↔ ∀ x : X, ‖x‖ ≤ 1 → IsSelfAdjoint (inner 𝒜 x (T x)) :=
  sorry

/-- **32XV** (`chilb-vector-states-order-separating`, cstar.tex:5268,
Exercise), part 2: `0 ≤ T` in `B^a(X)` — i.e. `T = R* R` for some
adjointable bounded `R` — iff `0 ≤ ⟨x, Tx⟩` for all `x`. -/
theorem chilb_vector_states_2 [CompleteSpace X] (T : X →L[ℂ] X)
    (hT : ModuleAdjointable 𝒜 ⇑T) :
    (∀ x : X, 0 ≤ inner 𝒜 x (T x)) ↔
      ∃ R R' : X →L[ℂ] X, ModuleAdjointTo 𝒜 ⇑R ⇑R' ∧ T = R'.comp R :=
  sorry

/-- **32XV** (`chilb-vector-states-order-separating`, cstar.tex:5268,
Exercise), part 3: `‖T‖ = sup_{‖x‖ ≤ 1} ‖⟨x, Tx⟩‖` for self-adjoint `T`. -/
theorem chilb_vector_states_3 [CompleteSpace X] (T : X →L[ℂ] X)
    (h : ModuleAdjointTo 𝒜 ⇑T ⇑T) :
    ‖T‖ = ⨆ x : {x : X // ‖x‖ ≤ 1}, ‖inner 𝒜 (x : X) (T x)‖ :=
  sorry

/-- **32XVI** (cstar.tex:5292, Corollary): `T* T` is positive in `B^a(X)`
for every adjointable bounded `T : X → Y` between Hilbert 𝒜-modules — via
**32XV**: `0 ≤ ⟨x, (T*T) x⟩` for all `x`. -/
theorem chilb_adjoint_mul_self_nonneg [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[ℂ] Y) (S : Y →L[ℂ] X) (h : ModuleAdjointTo 𝒜 ⇑T ⇑S) (x : X) :
    0 ≤ inner 𝒜 x ((S.comp T) x) :=
  sorry

end CauchySchwarz

/-! ## Parsec 330: matrices over a C*-algebra -/

section Matrices

variable {𝒜 ℬ : Type*} [CStarAlgebra 𝒜] [CStarAlgebra ℬ]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
variable {N : ℕ}

/-- **33I** (`cstar-matrices`, cstar.tex:5307, Exercise), part 1: an
`N×N`-matrix `A` over `𝒜` gives a bounded module map on `𝒜^N` (Mathlib:
`CStarMatrix.toCLM`), adjoint to the one of its conjugate transpose. -/
theorem cstar_matrices_1 (A : CStarMatrix (Fin N) (Fin N) 𝒜) :
    ModuleAdjointTo 𝒜 ⇑(CStarMatrix.toCLM A) ⇑(CStarMatrix.toCLM (star A)) :=
  sorry

/-- **33I** (`cstar-matrices`, cstar.tex:5307, Exercise), part 2:
`A ↦ toCLM A` is a linear bijection between the `N×N`-matrices over `𝒜`
and the adjointable bounded module maps on `𝒜^N`. -/
theorem cstar_matrices_2 :
    Function.Injective
      (CStarMatrix.toCLM (A := 𝒜) (m := Fin N) (n := Fin N)) ∧
    ∀ T : C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜) →L[ℂ] C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜),
      (∀ (a : 𝒜) (x : C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜)), T (a • x) = a • T x) →
      ModuleAdjointable 𝒜 ⇑T →
      ∃ A : CStarMatrix (Fin N) (Fin N) 𝒜, CStarMatrix.toCLM A = T :=
  sorry

/-- **33I** (`cstar-matrices`, cstar.tex:5307, Exercise), part 3: the
assignment `A ↦ toCLM A` is multiplicative up to the order of composition
(Mathlib's `toCLM` acts by `vecMul`, hence lands in the opposite algebra:
`CStarMatrix.toCLMNonUnitalAlgHom`). -/
theorem cstar_matrices_3 (A B : CStarMatrix (Fin N) (Fin N) 𝒜) :
    CStarMatrix.toCLM (A * B) =
      (CStarMatrix.toCLM B).comp (CStarMatrix.toCLM A) :=
  sorry

/-- **33I** (`cstar-matrices`, cstar.tex:5307, Exercise), part 4: the
`N×N`-matrices over a C*-algebra `𝒜` form a C*-algebra `M_N(𝒜)` — in
Mathlib the instance `CStarMatrix.instCStarAlgebra` on
`CStarMatrix (Fin N) (Fin N) 𝒜`. -/
noncomputable example : CStarAlgebra (CStarMatrix (Fin N) (Fin N) 𝒜) :=
  inferInstance

section MatrixOrder

variable [PartialOrder (CStarMatrix (Fin N) (Fin N) 𝒜)]
  [StarOrderedRing (CStarMatrix (Fin N) (Fin N) 𝒜)]

/-- **33II** (`when-a-matrix-over-a-cstar-algebra-is-positive`,
cstar.tex:5339, Exercise), part 1: an `N×N`-matrix `A` over `𝒜` is positive
iff `0 ≤ ∑_{i,j} aᵢ* Aᵢⱼ aⱼ` for all `a₁, …, a_N ∈ 𝒜`. -/
theorem cstar_matrix_positive_iff (A : CStarMatrix (Fin N) (Fin N) 𝒜) :
    0 ≤ A ↔ ∀ a : Fin N → 𝒜, 0 ≤ ∑ i, ∑ j, star (a i) * A i j * a j :=
  sorry

/-- **33II** (`when-a-matrix-over-a-cstar-algebra-is-positive`,
cstar.tex:5339, Exercise), part 2: the Gram matrix `(⟨xᵢ, xⱼ⟩)ᵢⱼ` of vectors
of a pre-Hilbert 𝒜-module is positive. -/
theorem cstar_matrix_gram_nonneg {X : Type*} [NormedAddCommGroup X]
    [Module ℂ X] [SMul 𝒜 X] [CStarModule 𝒜 X] (x : Fin N → X) :
    0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => inner 𝒜 (x i) (x j)) :=
  sorry

/-- **33II** (`when-a-matrix-over-a-cstar-algebra-is-positive`,
cstar.tex:5339, Exercise), part 3: the matrix `(aᵢ* aⱼ)ᵢⱼ` is positive for
all `a₁, …, a_N ∈ 𝒜`. -/
theorem cstar_matrix_star_mul_nonneg (a : Fin N → 𝒜) :
    0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j) :=
  sorry

end MatrixOrder

/-- **33III** (`mnf`, cstar.tex:5358, Exercise), parts 1–2: applying a
linear map `f : 𝒜 → ℬ` entrywise to matrices gives a linear map
`M_N f : M_N(𝒜) → M_N(ℬ)` (Mathlib: `CStarMatrix.mapₗ`, unbundled
`CStarMatrix.map`), which is unital when `f` is, multiplicative when `f` is,
and involution preserving when `f` is. -/
theorem mnf_inherits (f : 𝒜 →ₗ[ℂ] ℬ) :
    (f 1 = 1 → (1 : CStarMatrix (Fin N) (Fin N) 𝒜).map ⇑f = 1) ∧
    (IsMultiplicativeMap f → ∀ A B : CStarMatrix (Fin N) (Fin N) 𝒜,
      (A * B).map ⇑f = A.map ⇑f * B.map ⇑f) ∧
    (IsInvolutionPreserving f → ∀ A : CStarMatrix (Fin N) (Fin N) 𝒜,
      (star A).map ⇑f = star (A.map ⇑f)) :=
  sorry

/-- **33III** (`mnf`, cstar.tex:5358, Exercise), part 3: `M_N f` need not be
positive when `f` is: the transpose map on `M₂` is positive but `M₂` of it
is not.  (That `M_N f` need not be bounded uniformly in `N` when `f` is
bounded is not converted.) -/
theorem mnf_not_positive :
    ∃ f : CStarMatrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ,
      IsPositiveMap f ∧
      ¬∀ A : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin 2) (Fin 2) ℂ),
        0 ≤ A → 0 ≤ A.map ⇑f :=
  sorry

/-! ## Parsec 340: completely positive maps -/

/-- **34II** (`n-pos`, cstar.tex:5407, Lemma): for a linear map
`f : 𝒜 → ℬ` between C*-algebras and `N ∈ ℕ` the following are equivalent:
(1) `M_N f` is positive; (2) `∑_{i,j} bᵢ* f(aᵢ* aⱼ) bⱼ ≥ 0` for all
`a ∈ 𝒜^N`, `b ∈ ℬ^N`; (3) the matrix `(f(aᵢ* aⱼ))ᵢⱼ` is positive for all
`a ∈ 𝒜^N`. -/
theorem n_pos (f : 𝒜 →ₗ[ℂ] ℬ) (N : ℕ) :
    List.TFAE [
      ∀ A : CStarMatrix (Fin N) (Fin N) 𝒜, 0 ≤ A → 0 ≤ A.map ⇑f,
      ∀ (a : Fin N → 𝒜) (b : Fin N → ℬ),
        0 ≤ ∑ i, ∑ j, star (b i) * f (star (a i) * a j) * b j,
      ∀ a : Fin N → 𝒜,
        0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => f (star (a i) * a j))] :=
  sorry

/-- **34IV** (`cp`, cstar.tex:5448, Exercise), part 1: a linear map `f`
between C*-algebras is completely positive iff `M_N f` is positive for every
`N` iff `(f(aᵢ* aⱼ))ᵢⱼ ≥ 0` for every `N` and `a ∈ 𝒜^N`.  (Mathlib's
bundled cp maps `𝒜 →CP ℬ` are defined by the first of these conditions.) -/
theorem cp_iff (f : 𝒜 →ₗ[ℂ] ℬ) :
    List.TFAE [
      IsCompletelyPositiveMap f,
      ∀ (N : ℕ) (A : CStarMatrix (Fin N) (Fin N) 𝒜), 0 ≤ A → 0 ≤ A.map ⇑f,
      ∀ (N : ℕ) (a : Fin N → 𝒜),
        0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => f (star (a i) * a j))] :=
  sorry

/-- **34IV** (`cp`, cstar.tex:5448, Exercise), part 2: the composition of
cp-maps is completely positive. -/
theorem cp_comp {𝒞 : Type*} [CStarAlgebra 𝒞] [PartialOrder 𝒞]
    [StarOrderedRing 𝒞] (f : 𝒜 →ₗ[ℂ] ℬ) (g : ℬ →ₗ[ℂ] 𝒞)
    (hf : IsCompletelyPositiveMap f) (hg : IsCompletelyPositiveMap g) :
    IsCompletelyPositiveMap (g.comp f) :=
  sorry

/-- **34IV** (`cp`, cstar.tex:5448, Exercise), part 3: every mi-map is
completely positive. -/
theorem cp_of_mi (f : 𝒜 →ₗ[ℂ] ℬ) (hm : IsMultiplicativeMap f)
    (hi : IsInvolutionPreserving f) : IsCompletelyPositiveMap f :=
  sorry

/-- **34V** (`ad-cp`, cstar.tex:5463, Exercise), part 1: the map
`b ↦ a* b a : 𝒜 → 𝒜` is completely positive for every `a ∈ 𝒜`. -/
theorem ad_cp_1 (a : 𝒜) :
    IsCompletelyPositiveMap
      ((LinearMap.mulLeft ℂ (star a)).comp (LinearMap.mulRight ℂ a)) :=
  sorry

/-- The map `T ↦ S* T S : B(H) → B(K)` of a bounded operator `S : K → H`
between Hilbert spaces, as a linear map (for **34V**, part 2). -/
noncomputable def conjOperator {H K : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (S : K →L[ℂ] H) :
    (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K) where
  toFun T := (ContinuousLinearMap.adjoint S).comp (T.comp S)
  map_add' T T' := by
    ext x
    simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_smul' c T := by
    ext x
    simp

/-- **34V** (`ad-cp`, cstar.tex:5463, Exercise), part 2: the map
`T ↦ S* T S : B^a(X) → B^a(Y)` is completely positive for every adjointable
`S : Y → X` — stated here, as in **34V** part 3, for Hilbert spaces (the
thesis states it for Hilbert 𝒜-modules, whose algebras `B^a(X)` are not
separate types in this formalization, cf. **32XIII**). -/
theorem ad_cp_2 {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (S : K →L[ℂ] H) :
    IsCompletelyPositiveMap (conjOperator S) :=
  sorry

/-- **34V** (`ad-cp`, cstar.tex:5463, Exercise), part 3: the vector
functional `T ↦ ⟨x, Tx⟩ : B(H) → ℂ` is completely positive. -/
theorem ad_cp_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (x : H) :
    IsCompletelyPositiveMap (vectorFunctional x) :=
  sorry

/-- **34VI** (`cstar-product-4`, cstar.tex:5486, Exercise), part 1: the
direct sum `⊕ᵢ 𝒜ᵢ` is the product in `CStar_cpsu`: every family of cpsu-maps
`fᵢ : ℬ → 𝒜ᵢ` factors uniquely through the projections by a cpsu-map.
(Complete positivity and subunitality of the mediating map `g` are spelled
out, since Mathlib does not register a unital C*-algebra instance on
`lp 𝒜 ∞` in the non-commutative case.) -/
theorem cstar_product_4 {ι : Type*} {𝒜f : ι → Type*}
    [∀ i, CStarAlgebra (𝒜f i)] [∀ i, Nontrivial (𝒜f i)]
    [∀ i, PartialOrder (𝒜f i)] [∀ i, StarOrderedRing (𝒜f i)]
    [PartialOrder (lp 𝒜f ∞)] [StarOrderedRing (lp 𝒜f ∞)]
    {ℬ : Type*} [CStarAlgebra ℬ]
    [PartialOrder ℬ] [StarOrderedRing ℬ] (f : ∀ i, ℬ →ₗ[ℂ] 𝒜f i)
    (hcp : ∀ i, IsCompletelyPositiveMap (f i))
    (hsu : ∀ i, Subunital ⇑(f i)) :
    ∃! g : ℬ →ₗ[ℂ] lp 𝒜f ∞,
      (∀ (n : ℕ) (a : Fin n → ℬ) (c : Fin n → lp 𝒜f ∞),
        0 ≤ ∑ i, ∑ j, star (c i) * g (star (a i) * a j) * c j) ∧
      g 1 ≤ 1 ∧
      ∀ (i : ι) (b : ℬ), (g b : ∀ i, 𝒜f i) i = f i b :=
  sorry

/-! **34VI** (`cstar-product-4`, cstar.tex:5486, Exercise), part 2: the
equaliser of miu-maps `f, g : 𝒜 → ℬ` in `CStar_cpsu` is (the inclusion of)
the C*-subalgebra `{a : f(a) = g(a)}` — which is a closed subalgebra by
**20aII** (`cstar_equaliser_1`); the universal property amounts to: every
cpsu-map `h : 𝒞 → 𝒜` with `f ∘ h = g ∘ h` corestricts to it, which is
set-theoretically immediate.  Not converted beyond **20aII**. -/

/-- **34VII** (`ccstar-pos-mat`, cstar.tex:5504, Lemma): for a commutative
C*-algebra `𝒜`, the matrices of the form `∑ₖ aₖ Bₖ` with `aₖ ∈ 𝒜₊` and
`Bₖ ∈ M_N(ℂ)₊` are norm dense in `M_N(𝒜)₊`. -/
theorem ccstar_pos_mat {𝒜 : Type*} [CommCStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] (N : ℕ)
    [PartialOrder (CStarMatrix (Fin N) (Fin N) 𝒜)]
    [StarOrderedRing (CStarMatrix (Fin N) (Fin N) 𝒜)] :
    closure {A : CStarMatrix (Fin N) (Fin N) 𝒜 |
        ∃ (K : ℕ) (a : Fin K → 𝒜) (B : Fin K → CStarMatrix (Fin N) (Fin N) ℂ),
          (∀ k, 0 ≤ a k) ∧ (∀ k, 0 ≤ B k) ∧
          A = ∑ k, CStarMatrix.ofMatrix (Matrix.of fun i j => B k i j • a k)} =
      {A : CStarMatrix (Fin N) (Fin N) 𝒜 | 0 ≤ A} :=
  sorry

/-- **34IX** (`cp-commutative`, cstar.tex:5563, Proposition), case 1: a
positive map into a commutative C*-algebra is completely positive. -/
theorem cp_commutative_cod {𝒞 : Type*} [CommCStarAlgebra 𝒞] [PartialOrder 𝒞]
    [StarOrderedRing 𝒞] (f : 𝒜 →ₗ[ℂ] 𝒞) (hf : IsPositiveMap f) :
    IsCompletelyPositiveMap f :=
  sorry

/-- **34IX** (`cp-commutative`, cstar.tex:5563, Proposition), case 2: a
positive map out of a commutative C*-algebra is completely positive. -/
theorem cp_commutative_dom {𝒞 : Type*} [CommCStarAlgebra 𝒞] [PartialOrder 𝒞]
    [StarOrderedRing 𝒞] (f : 𝒞 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) :
    IsCompletelyPositiveMap f :=
  sorry

/-- **34XII** (`cstar-positive-2x2matrix`, cstar.tex:5592, Lemma): for a
positive 2×2 matrix `[[p, a], [a*, q]]` over `𝒜` we have `a* a ≤ ‖p‖ q` and
`a a* ≤ ‖q‖ p` (in particular `a = 0` when `p = 0` or `q = 0`). -/
theorem cstar_positive_2x2matrix
    [PartialOrder (CStarMatrix (Fin 2) (Fin 2) 𝒜)]
    [StarOrderedRing (CStarMatrix (Fin 2) (Fin 2) 𝒜)]
    (A : CStarMatrix (Fin 2) (Fin 2) 𝒜) (hA : 0 ≤ A) :
    star (A 0 1) * A 0 1 ≤ ‖A 0 0‖ • A 1 1 ∧
      A 0 1 * star (A 0 1) ≤ ‖A 1 1‖ • A 0 0 :=
  sorry

/-- **34XIV** (`cp-cs`, cstar.tex:5629, Lemma): for a positive map
`f : 𝒜 → ℬ` such that `M₂ f` is positive (expressed by condition 2 of
**34II**), and `a, b ∈ 𝒜`:
`f(a* b) f(b* a) ≤ ‖f(b* b)‖ f(a* a)`. -/
theorem cp_cs (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f)
    (h2 : ∀ (a : Fin 2 → 𝒜) (b : Fin 2 → ℬ),
      0 ≤ ∑ i, ∑ j, star (b i) * f (star (a i) * a j) * b j)
    (a b : 𝒜) :
    f (star a * b) * f (star b * a) ≤ ‖f (star b * b)‖ • f (star a * a) :=
  sorry

/-- **34XVI** (`cp-russo-dye`, cstar.tex:5655, Corollary): `‖f‖ = ‖f(1)‖`
for every cp-map `f : 𝒜 → ℬ` between C*-algebras, i.e.
`‖f(a)‖ ≤ ‖f(1)‖ ‖a‖` for all `a` (the reverse bound is trivial). -/
theorem cp_russo_dye (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsCompletelyPositiveMap f)
    (a : 𝒜) : ‖f a‖ ≤ ‖f 1‖ * ‖a‖ :=
  sorry

/-- **34XVIII** (`choi`, cstar.tex:5674, Lemma (Choi)), part 1:
`f(a)* f(a) ≤ f(a* a)` for every cpu-map `f : 𝒜 → ℬ` and `a ∈ 𝒜`. -/
theorem choi_1 (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsCompletelyPositiveMap f)
    (hu : f 1 = 1) (a : 𝒜) :
    star (f a) * f a ≤ f (star a * a) :=
  sorry

/-- **34XVIII** (`choi`, cstar.tex:5674, Lemma (Choi)), part 2: if
`f(a* a) = f(a)* f(a)` for a cpu-map `f` and some `a`, then
`f(b a) = f(b) f(a)` for all `b ∈ 𝒜`. -/
theorem choi_2 (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsCompletelyPositiveMap f)
    (hu : f 1 = 1) (a : 𝒜) (ha : f (star a * a) = star (f a) * f a) (b : 𝒜) :
    f (b * a) = f b * f a :=
  sorry

/-! ## Parsec 341 (34a): Russo–Dye

**34aI** (cstar.tex:5724): introduction — nothing to formalize. -/

/-- **34aII** (`normal-russo-dye`, cstar.tex:5751, Lemma):
`‖f(a)‖ ≤ ‖f(1)‖ ‖a‖` for every p-map `f : 𝒜 → ℬ` and *normal* `a ∈ 𝒜`. -/
theorem normal_russo_dye (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) (a : 𝒜)
    (ha : IsStarNormal a) : ‖f a‖ ≤ ‖f 1‖ * ‖a‖ :=
  sorry

/-! **34aIV** (`cstar-unitary`, cstar.tex:5766, Definition): an element `u`
of a C*-algebra is *unitary* when `u* u = 1 = u u*` — Mathlib's submonoid
`unitary 𝒜` (membership `u ∈ unitary 𝒜`). -/

/-- **34aV** (cstar.tex:5773, Exercise), part 1: every `λ ∈ ℂ` with
`|λ| = 1` is unitary in `𝒜`; in particular `1` is. -/
theorem unitary_basic_1 (z : ℂ) (hz : ‖z‖ = 1) :
    algebraMap ℂ 𝒜 z ∈ unitary 𝒜 :=
  sorry

/-- **34aV** (cstar.tex:5773, Exercise), part 2: a unitary `u` is invertible
with inverse `u*`, and `u*` is unitary. -/
theorem unitary_basic_2 (u : 𝒜) (hu : u ∈ unitary 𝒜) :
    IsUnit u ∧ Ring.inverse u = star u ∧ star u ∈ unitary 𝒜 :=
  sorry

/-- **34aV** (cstar.tex:5773, Exercise), part 3: the product of unitaries is
unitary. -/
theorem unitary_basic_3 (u v : 𝒜) (hu : u ∈ unitary 𝒜) (hv : v ∈ unitary 𝒜) :
    u * v ∈ unitary 𝒜 :=
  sorry

/-- **34aV** (cstar.tex:5773, Exercise), part 4: every unitary is normal;
and a normal `a` is unitary iff `Re(a)² + Im(a)² = 1`. -/
theorem unitary_basic_4 (a : 𝒜) :
    (a ∈ unitary 𝒜 → IsStarNormal a) ∧
      (IsStarNormal a →
        (a ∈ unitary 𝒜 ↔ (ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2 = 1)) :=
  sorry

/-- **34aV** (cstar.tex:5773, Exercise), part 5: every self-adjoint `a` with
`‖a‖ ≤ 1` is the real part of some unitary (e.g. `u = a + i√(1-a²)`). -/
theorem unitary_basic_5 (a : 𝒜) (ha : IsSelfAdjoint a) (h1 : ‖a‖ ≤ 1) :
    ∃ u ∈ unitary 𝒜, a = (ℜ u : 𝒜) :=
  sorry

/-- **34aV** (cstar.tex:5773, Exercise), part 6: every invertible `a` can be
written `a = u √(a* a)` with `u` unitary (a variation on the polar
decomposition, cf. vn.tex 82I). -/
theorem unitary_basic_6 (a : 𝒜) (ha : IsUnit a) :
    ∃ u ∈ unitary 𝒜, a = u * CFC.sqrt (star a * a) :=
  sorry

/-- **34aVI** (cstar.tex:5812, Exercise), part 1: every invertible `a` with
`‖a‖ ≤ 2` is the sum of two unitaries. -/
theorem sum_of_unitaries_1 (a : 𝒜) (ha : IsUnit a) (h2 : ‖a‖ ≤ 2) :
    ∃ u ∈ unitary 𝒜, ∃ v ∈ unitary 𝒜, a = u + v :=
  sorry

/-- **34aVI** (cstar.tex:5812, Exercise), part 2: `u + a` is the sum of two
unitaries for unitary `u` and `‖a‖ < 1`. -/
theorem sum_of_unitaries_2 (u a : 𝒜) (hu : u ∈ unitary 𝒜) (ha : ‖a‖ < 1) :
    ∃ v ∈ unitary 𝒜, ∃ w ∈ unitary 𝒜, u + a = v + w :=
  sorry

/-- **34aVI** (cstar.tex:5812, Exercise), part 3: every `a` with `‖a‖ < N`
is the sum of `N + 2` unitaries.  (Part 4 of the exercise, to prove the
following theorem, is **34aVII**.) -/
theorem sum_of_unitaries_3 (a : 𝒜) (N : ℕ) (hN : ‖a‖ < N) :
    ∃ u : Fin (N + 2) → 𝒜, (∀ i, u i ∈ unitary 𝒜) ∧ a = ∑ i, u i :=
  sorry

/-- **34aVII** (`russo-dye`, cstar.tex:5842, Theorem (Russo–Dye)): every
element `a` of a C*-algebra with `‖a‖ < 1 - 2/N` for some natural number `N`
can be written as `a = (u₁ + ⋯ + u_N)/N` for some unitaries `u₁, …, u_N`.
(Hence the convex combinations of unitaries are norm dense in the closed
unit ball.) -/
theorem russo_dye (a : 𝒜) (N : ℕ) (hN : ‖a‖ < 1 - 2 / N) :
    ∃ u : Fin N → 𝒜, (∀ i, u i ∈ unitary 𝒜) ∧
      a = ((N : ℂ))⁻¹ • ∑ i, u i :=
  sorry

/-- **34aVIII** (`russo-dye-cor`, cstar.tex:5850, Corollary): the operator
norm of a positive map `f : 𝒜 → ℬ` between C*-algebras is `‖f‖ = ‖f(1)‖`,
i.e. `‖f(a)‖ ≤ ‖f(1)‖ ‖a‖` for all `a`. -/
theorem russo_dye_cor (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) (a : 𝒜) :
    ‖f a‖ ≤ ‖f 1‖ * ‖a‖ :=
  sorry

end Matrices

end Theses.A.CStar
