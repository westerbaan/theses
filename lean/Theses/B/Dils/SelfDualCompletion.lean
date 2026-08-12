/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 2622–3526.

  parsec 1500:  the self-dual completion of a module with 𝒷-valued inner
                product
  parsec 1510:  its universal property
  parsec 1520:  𝒷-sesquilinear forms on self-dual modules; 𝒷ᵃ(X) is a von
                Neumann algebra
  parsec 1530:  ad_T is (n)cp

Statements only; every proof is `sorry`.  See `HilbertModules.lean` for the
conventions (Mathlib's left-action mirror of the thesis's right modules;
the ultranorm uniformity encoded through `UnTendsto`/`UnCauchy`/`UnDense`).

This file also introduces the *type* `Ba 𝒷 X` of adjointable bounded
operators on a Hilbert 𝒷-module.  Its C*-algebra structure (**143IV**) and
its canonical order are genuine theorems of the thesis whose proofs are out
of scope here; they are provided as `sorry`-instances so that `𝒷ᵃ(X)` can
appear as an algebra in later statements (notably the Paschke dilation).
-/
import Theses.B.Dils.HilbertModules

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra WithCStarModule
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u v w

namespace Theses.B.Dils

/-! ## The C*-algebra `𝒷ᵃ(X)` as a type -/

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
instance: `𝒷ᵃ(X)` is a C*-algebra for a Hilbert 𝒷-module `X`.
FIXME(sorry-instance): the C*-structure (composition, adjoint as involution,
operator norm, closedness `hilbmod_cstar`) is deferred. -/
noncomputable instance Ba.instCStarAlgebra : CStarAlgebra (Ba 𝒷 X) :=
  sorry

/-- The canonical (Loewner) partial order of the C*-algebra `𝒷ᵃ(X)`
(cf. **144I**).  FIXME(sorry-instance): deferred. -/
noncomputable instance Ba.instPartialOrder : PartialOrder (Ba 𝒷 X) :=
  sorry

/-- The canonical order of `𝒷ᵃ(X)` makes it a star-ordered ring
(cf. **144I**).  FIXME(sorry-instance): deferred. -/
noncomputable instance Ba.instStarOrderedRing : StarOrderedRing (Ba 𝒷 X) :=
  sorry

end BaDef

/-! ## Parsec 1500: the self-dual completion

**150I** (dils.tex:2624): introduction — nothing to formalize.
**150III**–**150XV** (fast nets, the uniform space `N`, the uniformity on
`V̄`, the module structure, extending the seminorms, the transfinite
induction on compatible extensions, self-duality) are the proof of
**150II** — not converted. -/

section Completion

variable {𝒷 : Type u} {V : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [AddCommGroup V] [Module ℂ V] [SMul 𝒷 V]

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

/-- **150II** (`dils-completion`, dils.tex:2632, Theorem), the data: a
**self-dual completion** of a 𝒷-module `V` with 𝒷-valued inner product
`B`: a self-dual Hilbert 𝒷-module `X` together with a 𝒷-linear
inner-product-preserving `η : V → X` whose image is ultranorm dense. -/
structure SelfDualCompletion (B : BInner 𝒷 V) : Type (max u (v + 1) (w + 1))
    where
  /-- The carrier of the completion. -/
  X : Type w
  [nacg : NormedAddCommGroup X]
  [mod : NormedSpace ℂ X]
  [smul : SMul 𝒷 X]
  [cstarMod : CStarModule 𝒷 X]
  [complete : CompleteSpace X]
  /-- `X` is self dual. -/
  selfDual : SelfDual 𝒷 X
  /-- The embedding `η : V → X`. -/
  η : V → X
  η_add : ∀ v w : V, η (v + w) = η v + η w
  η_smul_complex : ∀ (c : ℂ) (v : V), η (c • v) = c • η v
  η_smul : ∀ (b : 𝒷) (v : V), η (b • v) = b • η v
  /-- `η` preserves the inner product: `[v,w] = ⟨η v, η w⟩`. -/
  η_inner : ∀ v w : V, inner 𝒷 (η v) (η w) = B.inner v w
  /-- The image of `η` is ultranorm dense in `X`. -/
  dense : UnDense (inner 𝒷) (Set.range η)

attribute [instance] SelfDualCompletion.nacg SelfDualCompletion.mod
  SelfDualCompletion.smul SelfDualCompletion.cstarMod
  SelfDualCompletion.complete

/-- **150II** (`dils-completion`, dils.tex:2632, Theorem): for a von
Neumann algebra `𝒷`, every 𝒷-module `V` with (possibly indefinite)
𝒷-valued inner product has a self-dual completion. -/
theorem dils_completion [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 V) :
    Nonempty (SelfDualCompletion.{u, v, max u v} B) :=
  sorry

/-! ## Parsec 1510: the universal property of the completion

**151I** (dils.tex:3249): introduction — nothing to formalize.
**151II** is the proof of **151Ia** — not converted. -/

/-- **151Ia** (`selfdual-completion-univ`, dils.tex:3254, Lemma): let
`η : V → X` be an inner-product-preserving 𝒷-linear map into a self-dual
Hilbert 𝒷-module with ultranorm dense image (e.g. a self-dual completion,
**150II**).  Then for every bounded 𝒷-linear `T : V → Y` into a self-dual
Hilbert 𝒷-module `Y` there is a unique bounded 𝒷-linear `T̂ : X → Y` with
`T̂ ∘ η = T` (moreover `‖T̂‖ = ‖T‖`). -/
theorem selfdual_completion_univ [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 V)
    (E : SelfDualCompletion.{u, v, w} B) {Y : Type w}
    [NormedAddCommGroup Y] [Module ℂ Y] [SMul 𝒷 Y] [CStarModule 𝒷 Y]
    [CompleteSpace Y] (hY : SelfDual 𝒷 Y) (C : ℝ) (T : V → Y)
    (hT : IsBoundedModuleMap B (cstarBInner 𝒷 Y) C T) :
    ∃! T' : E.X → Y,
      (∃ C' : ℝ, IsBoundedModuleMap (cstarBInner 𝒷 E.X) (cstarBInner 𝒷 Y)
        C' T') ∧ ∀ v : V, T' (E.η v) = T v :=
  sorry

end Completion

/-! ## Parsec 1520: sesquilinear forms and 𝒷ᵃ(X) for self-dual X

**152I** (dils.tex:3320): introduction; **152III**/**152IV** (Example) —
nothing to formalize.  **152VI** is the proof of **152V**;
**152XI**–**152XIII** the proof of **152X** — not converted. -/

section SelfDualBa

variable {𝒷 : Type u} {X Y : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]
  [NormedAddCommGroup Y] [Module ℂ Y] [SMul 𝒷 Y] [CStarModule 𝒷 Y]

/-- **152II** (dils.tex:3325, Definition): a sesquilinear form `B` on a
normed 𝒷-module is **bounded** (by `r`) when `‖B(x,y)‖ ≤ r ‖x‖ ‖y‖`. -/
def IsBoundedBSesq (r : ℝ) (B : X → X → 𝒷) : Prop :=
  IsBSesquilinear B ∧ ∀ x y : X, ‖B x y‖ ≤ r * ‖x‖ * ‖y‖

/-- **152V** (`hilbmod-sesquilinear-forms`, dils.tex:3343, Proposition):
on a self-dual Hilbert 𝒷-module every bounded 𝒷-sesquilinear form is
`⟨·, T ·⟩` for a unique adjointable bounded operator `T`. -/
theorem hilbmod_sesquilinear_forms [CompleteSpace X] (hX : SelfDual 𝒷 X)
    (r : ℝ) (B : X → X → 𝒷) (hB : IsBoundedBSesq r B) :
    ∃! T : X →L[ℂ] X, ModuleAdjointable 𝒷 ⇑T ∧
      ∀ x y : X, B x y = inner 𝒷 x (T y) :=
  sorry

/-- **152VIII** (`hilbmod-adjoint-exists`, dils.tex:3388, Exercise): a
bounded 𝒷-linear map `T : X → Y` between Hilbert 𝒷-modules with `X` self
dual is adjointable. -/
theorem hilbmod_adjoint_exists [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒷 X) (T : X →L[ℂ] Y)
    (hmod : ∀ (b : 𝒷) (x : X), T (b • x) = b • T x) :
    ∃ S : Y →L[ℂ] X, ModuleAdjointTo 𝒷 ⇑T ⇑S :=
  sorry

end SelfDualBa

section FixedOnV

variable {𝒷 : Type u} {V : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [AddCommGroup V] [Module ℂ V] [SMul 𝒷 V]

/-- **152IX** (`hilmod-fixed-on-V`, dils.tex:3394, Exercise), part 1: for a
self-dual completion `η : V → X`, the vector states `⟨η v, (·) η v⟩` are
order separating on `𝒷ᵃ(X)`: an adjointable `T` is positive iff
`⟨η v, T (η v)⟩ ≥ 0` for all `v ∈ V`. -/
theorem hilmod_fixed_on_V [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 V)
    (E : SelfDualCompletion.{u, v, w} B) (T : E.X →L[ℂ] E.X)
    (hT : ModuleAdjointable 𝒷 ⇑T) :
    IsPositiveOp 𝒷 T ↔ ∀ v : V, 0 ≤ inner 𝒷 (E.η v) (T (E.η v)) :=
  sorry

/-- **152IX** (`hilmod-fixed-on-V`, dils.tex:3394, Exercise), part 2:
consequently adjointable operators agreeing on the vector states of the
dense image are equal: `S = T` iff `⟨η v, T (η v)⟩ = ⟨η v, S (η v)⟩` for
all `v ∈ V`. -/
theorem hilmod_fixed_on_V_eq [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 V)
    (E : SelfDualCompletion.{u, v, w} B) (T S : E.X →L[ℂ] E.X)
    (hT : ModuleAdjointable 𝒷 ⇑T) (hS : ModuleAdjointable 𝒷 ⇑S)
    (h : ∀ v : V, inner 𝒷 (E.η v) (T (E.η v)) =
      inner 𝒷 (E.η v) (S (E.η v))) :
    T = S :=
  sorry

end FixedOnV

section BaVN

variable {𝒷 : Type u} {X Y : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]
  [NormedAddCommGroup Y] [Module ℂ Y] [SMul 𝒷 Y] [CStarModule 𝒷 Y]

/-- **152X** (dils.tex:3409, Theorem): for a self-dual Hilbert 𝒷-module
`X` over a von Neumann algebra `𝒷`, the algebra `𝒷ᵃ(X)` is a von Neumann
algebra (bounded directed suprema exist and the vector states are
separating normal states). -/
theorem ba_vonNeumannAlgebra [VonNeumannAlgebra 𝒷] [CompleteSpace X]
    (hX : SelfDual 𝒷 X) : VonNeumannAlgebra (Ba 𝒷 X) :=
  sorry

/-! ## Parsec 1530: `ad_T` -/

/-- **153I** (`hilbmod-ad-ncp`, dils.tex:3487, Proposition), part 1: for an
adjointable bounded module map `T : X → Y` (with adjoint `T'`) between
Hilbert 𝒷-modules, the map `ad_T : 𝒷ᵃ(Y) → 𝒷ᵃ(X)`, `ad_T(S) = T* S T`,
is completely positive.

**153II** is the proof — not converted. -/
theorem hilbmod_ad_cp [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[ℂ] Y) (T' : Y →L[ℂ] X) (hT : ModuleAdjointTo 𝒷 ⇑T ⇑T') :
    ∃ ad : Ba 𝒷 Y →ₗ[ℂ] Ba 𝒷 X,
      (∀ S : Ba 𝒷 Y, (ad S).1 = T'.comp (S.1.comp T)) ∧
      IsCompletelyPositiveMap ad :=
  sorry

/-- **153I** (`hilbmod-ad-ncp`, dils.tex:3487, Proposition), part 2: if `X`
and `Y` are moreover self-dual, then `ad_T` is normal, i.e. an ncp-map.

**153III** is the proof — not converted. -/
theorem hilbmod_ad_ncp [VonNeumannAlgebra 𝒷] [CompleteSpace X]
    [CompleteSpace Y] (hX : SelfDual 𝒷 X) (hY : SelfDual 𝒷 Y)
    (T : X →L[ℂ] Y) (T' : Y →L[ℂ] X) (hT : ModuleAdjointTo 𝒷 ⇑T ⇑T') :
    ∃ ad : NCPMap (Ba 𝒷 Y) (Ba 𝒷 X),
      ∀ S : Ba 𝒷 Y, (ad S).1 = T'.comp (S.1.comp T) :=
  sorry

end BaVN

/-- **153IV** (`hilbmod-adj-vector-ncp`, dils.tex:3517, Exercise): for a
C*-algebra `𝒜` (here: von Neumann algebra, so that normality makes sense)
and `a₁, …, aₙ ∈ 𝒜`, the map `φ : 𝒜 → Mₙ𝒜`, `φ(d) = (aᵢ* d aⱼ)ᵢⱼ`, is an
ncp-map. -/
theorem hilbmod_adj_vector_ncp {𝒜 : Type u} [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜] {n : ℕ}
    [PartialOrder (CStarMatrix (Fin n) (Fin n) 𝒜)]
    [StarOrderedRing (CStarMatrix (Fin n) (Fin n) 𝒜)]
    (a : Fin n → 𝒜) :
    ∃ φ : 𝒜 →ₗ[ℂ] CStarMatrix (Fin n) (Fin n) 𝒜,
      (∀ (d : 𝒜) (i j : Fin n), φ d i j = star (a i) * d * a j) ∧
      IsCompletelyPositiveMap φ ∧ PreservesDirSups ⇑φ :=
  sorry

end Theses.B.Dils
