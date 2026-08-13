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

/-- Definiteness of the 𝒷-valued inner product, in the second argument.
(A copy of the `private` `Theses.A.CStar.eq_of_inner_right_eq`.) -/
private theorem eq_of_binner_right {a b : X}
    (h : ∀ x : X, inner 𝒷 x a = inner 𝒷 x b) : a = b := by
  have h0 : inner 𝒷 (a - b) (a - b) = (0 : 𝒷) := by
    rw [CStarModule.inner_sub_right, h (a - b), sub_self]
  exact sub_eq_zero.mp (CStarModule.inner_self.mp h0)

/-- A map adjoint to a bounded module map is automatically linear and
bounded (cstar.tex 32X), hence may be taken to be a bounded operator. -/
private theorem exists_clm_adjoint {T : X →L[ℂ] X}
    (h : ModuleAdjointable 𝒷 ⇑T) :
    ∃ S : X →L[ℂ] X, ModuleAdjointTo 𝒷 ⇑T ⇑S := by
  obtain ⟨S, hS⟩ := h
  have hS' : ∀ x y : X, inner 𝒷 (T x) y = inner 𝒷 x (S y) := hS
  have hadd : ∀ y z, S (y + z) = S y + S z := fun y z =>
    eq_of_binner_right (𝒷 := 𝒷) fun x => by
      simp only [← hS', CStarModule.inner_add_right]
  have hsmul : ∀ (c : ℂ) (y : X), S (c • y) = c • S y := fun c y =>
    eq_of_binner_right (𝒷 := 𝒷) fun x => by
      simp only [← hS', CStarModule.inner_smul_right_complex]
  set Sl : X →ₗ[ℂ] X :=
    { toFun := S, map_add' := hadd, map_smul' := fun c y => hsmul c y } with hSl
  have hpos : (0 : ℝ) < ‖T‖ + 1 := by positivity
  have hbound : ∀ y : X, ‖Sl y‖ ≤ (‖T‖ + 1) * ‖y‖ := by
    refine (Theses.A.CStar.chilb_form_bounded (𝒜 := 𝒷) Sl (‖T‖ + 1) hpos).mpr ?_
    intro x y
    show ‖inner 𝒷 y (S x)‖ ≤ _
    rw [← hS' y x]
    calc ‖inner 𝒷 (T y) x‖ ≤ ‖T y‖ * ‖x‖ := CStarModule.norm_inner_le X
      _ ≤ (‖T‖ + 1) * ‖y‖ * ‖x‖ := by
          have h1 : ‖T y‖ ≤ (‖T‖ + 1) * ‖y‖ := by
            have h2 := T.le_opNorm y
            have h3 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
            nlinarith
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg x)
  exact ⟨Sl.mkContinuous (‖T‖ + 1) hbound, hS⟩

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
  (exists_clm_adjoint (T := (T : X →L[ℂ] X)) T.2).choose

private theorem baAdj_spec (T : baSubalgebra 𝒷 X) :
    ModuleAdjointTo 𝒷 ⇑(T : X →L[ℂ] X) ⇑(baAdj T) :=
  (exists_clm_adjoint (T := (T : X →L[ℂ] X)) T.2).choose_spec

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
