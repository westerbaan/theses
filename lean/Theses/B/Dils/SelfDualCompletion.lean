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

The type `Ba 𝒷 X` of adjointable bounded operators on a Hilbert 𝒷-module,
together with its C*-algebra structure (**143IV**) and canonical order, now
lives in `HilbertModules.lean` (right after 143IV), where the positive and
negative parts that 144I needs are available.  Those instances are **proved**,
not asserted: they are built from `baSubalgebra` (32III), `moduleAdjointTo_unique`,
`module_maps_cstar_identity` (32XII) and `bax_cstar` (32XIII).
-/
import Theses.B.Dils.HilbertModules

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra WithCStarModule
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u v w

namespace Theses.B.Dils

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
      ∀ x y : X, B x y = inner 𝒷 x (T y) := by
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  obtain ⟨hsesq, hbd⟩ := hB
  -- only `SMul 𝒷 X` is assumed, so `1 • y = y` has to be derived
  have hone : ∀ y : X, (1 : 𝒷) • y = y := fun y =>
    eq_of_inner_right_eq (𝒜 := 𝒷) fun x => by
      rw [CStarModule.inner_op_smul_right, one_mul]
  have hleft : ∀ (β : 𝒷) (x y : X), B (β • x) y = B x y * star β := fun β x y => by
    have h := hsesq.smul_op β 1 x y
    rwa [hone, one_mul] at h
  have hright : ∀ (b : 𝒷) (x y : X), B x (b • y) = b * B x y := fun b x y => by
    have h := hsesq.smul_op 1 b x y
    rwa [hone, star_one, mul_one] at h
  -- self-duality, packaged as a representation theorem for bounded 𝒷-linear
  -- functionals given by their components
  have hrep : ∀ (C : ℝ) (F : X → 𝒷), (∀ x x' : X, F (x + x') = F x + F x') →
      (∀ (c : ℂ) (x : X), F (c • x) = c • F x) →
      (∀ (b : 𝒷) (x : X), F (b • x) = b * F x) →
      (∀ x : X, ‖F x‖ ≤ C * ‖x‖) → ∃ t : X, ∀ x : X, F x = inner 𝒷 t x := by
    intro C F hadd hsmul hmod hbound
    exact hX { toFun := F, map_add' := hadd, map_smul' := hsmul } hmod ⟨C, hbound⟩
  -- (a) `x ↦ B(x,y)*` is bounded and 𝒷-linear, so `B(x,y) = ⟨x, t_y⟩`
  have hA : ∀ y : X, ∃ t : X, ∀ x : X, B x y = inner 𝒷 x t := by
    intro y
    obtain ⟨t, ht⟩ := hrep (r * ‖y‖) (fun x => star (B x y))
      (fun x x' => by rw [hsesq.add_left, star_add])
      (fun c x => by rw [hsesq.smul_left_complex, star_smul]; simp)
      (fun b x => by rw [hleft, star_mul, star_star])
      (fun x => by
        rw [norm_star]
        calc ‖B x y‖ ≤ r * ‖x‖ * ‖y‖ := hbd x y
          _ = r * ‖y‖ * ‖x‖ := by ring)
    exact ⟨t, fun x => by
      rw [← CStarModule.star_inner (A := 𝒷) t x, ← ht x, star_star]⟩
  -- (b) `x ↦ B(y,x)` is bounded and 𝒷-linear, so `B(y,x) = ⟨s_y, x⟩`
  have hBrep : ∀ y : X, ∃ s : X, ∀ x : X, B y x = inner 𝒷 s x := fun y =>
    hrep (r * ‖y‖) (fun x => B y x) (fun x x' => hsesq.add_right y x x')
      (fun c x => hsesq.smul_right_complex c y x) (fun b x => hright b y x)
      (fun x => by
        calc ‖B y x‖ ≤ r * ‖y‖ * ‖x‖ := hbd y x
          _ = r * ‖y‖ * ‖x‖ := rfl)
  choose T0 hT0 using hA
  choose S hS using hBrep
  -- `T0` is ℂ-linear, by definiteness of the inner product
  have hTadd : ∀ y y' : X, T0 (y + y') = T0 y + T0 y' := fun y y' =>
    eq_of_inner_right_eq (𝒜 := 𝒷) fun x => by
      rw [← hT0, CStarModule.inner_add_right, ← hT0, ← hT0, hsesq.add_right]
  have hTsmul : ∀ (c : ℂ) (y : X), T0 (c • y) = c • T0 y := fun c y =>
    eq_of_inner_right_eq (𝒜 := 𝒷) fun x => by
      rw [← hT0, CStarModule.inner_smul_right_complex, ← hT0,
        hsesq.smul_right_complex]
  -- `‖T0 x‖² = ‖⟨T0 x, T0 x⟩‖ = ‖B (T0 x, x)‖ ≤ r ‖T0 x‖ ‖x‖`
  set r' : ℝ := max r 0 with hr'
  have hr'0 : (0 : ℝ) ≤ r' := le_max_right _ _
  have hTbound : ∀ x : X, ‖T0 x‖ ≤ r' * ‖x‖ := by
    intro x
    have hsq : ‖T0 x‖ ^ 2 = ‖(inner 𝒷 (T0 x) (T0 x) : 𝒷)‖ := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷) (x := T0 x),
        Real.sq_sqrt (norm_nonneg _)]
    have hle : ‖T0 x‖ ^ 2 ≤ r' * (‖T0 x‖ * ‖x‖) := by
      rw [hsq, ← hT0 x (T0 x)]
      calc ‖B (T0 x) x‖ ≤ r * ‖T0 x‖ * ‖x‖ := hbd _ _
        _ ≤ r' * (‖T0 x‖ * ‖x‖) := by
            have : r * (‖T0 x‖ * ‖x‖) ≤ r' * (‖T0 x‖ * ‖x‖) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            linarith [this, mul_assoc r ‖T0 x‖ ‖x‖]
    rcases eq_or_lt_of_le (norm_nonneg (T0 x)) with h0 | h0
    · rw [← h0]; positivity
    · nlinarith [norm_nonneg x]
  set Tl : X →ₗ[ℂ] X :=
    { toFun := T0, map_add' := hTadd, map_smul' := fun c y => hTsmul c y } with hTl
  refine ⟨Tl.mkContinuous r' hTbound, ⟨⟨S, fun x y => ?_⟩, fun x y => hT0 y x⟩,
    fun T' hT' => ?_⟩
  · change inner 𝒷 (T0 x) y = inner 𝒷 x (S y)
    rw [← CStarModule.star_inner (A := 𝒷) y (T0 x), ← hT0 x y, hS y x,
      CStarModule.star_inner]
  · ext y
    exact eq_of_inner_right_eq (𝒜 := 𝒷) fun x =>
      (hT'.2 x y).symm.trans (hT0 y x)

/-- **152VIII** (`hilbmod-adjoint-exists`, dils.tex:3388, Exercise): a
bounded 𝒷-linear map `T : X → Y` between Hilbert 𝒷-modules with `X` self
dual is adjointable. -/
theorem hilbmod_adjoint_exists [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒷 X) (T : X →L[ℂ] Y)
    (hmod : ∀ (b : 𝒷) (x : X), T (b • x) = b • T x) :
    ∃ S : Y →L[ℂ] X, ModuleAdjointTo 𝒷 ⇑T ⇑S := by
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  let _ : NormedSpace ℂ Y := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  -- for each `y` the functional `τ_y = ⟨y, T ·⟩` is bounded and 𝒷-linear,
  -- so self-duality of `X` represents it as `⟨t, ·⟩`
  have hτ : ∀ y : Y, ∃ t : X, ∀ x : X, inner 𝒷 y (T x) = inner 𝒷 t x := by
    intro y
    refine hX { toFun := fun x => inner 𝒷 y (T x), map_add' := ?_, map_smul' := ?_ }
      (fun b x => ?_) ⟨‖y‖ * ‖T‖, fun x => ?_⟩
    · intro x x'
      simp [CStarModule.inner_add_right]
    · intro c x
      simp [CStarModule.inner_smul_right_complex]
    · show inner 𝒷 y (T (b • x)) = b * inner 𝒷 y (T x)
      rw [hmod, CStarModule.inner_op_smul_right]
    · show ‖inner 𝒷 y (T x)‖ ≤ ‖y‖ * ‖T‖ * ‖x‖
      calc ‖inner 𝒷 y (T x)‖ ≤ ‖y‖ * ‖T x‖ := CStarModule.norm_inner_le Y
        _ ≤ ‖y‖ * (‖T‖ * ‖x‖) :=
            mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg y)
        _ = ‖y‖ * ‖T‖ * ‖x‖ := by ring
  choose S hS using hτ
  -- `S` is the adjoint of `T`
  have hadj : ∀ (x : X) (y : Y), inner 𝒷 (T x) y = inner 𝒷 x (S y) := by
    intro x y
    rw [← CStarModule.star_inner (A := 𝒷) y (T x), hS y x,
      CStarModule.star_inner]
  -- hence linear and bounded
  have hadd : ∀ y y' : Y, S (y + y') = S y + S y' := fun y y' =>
    eq_of_inner_right_eq (𝒜 := 𝒷) fun x => by
      simp only [← hadj, CStarModule.inner_add_right]
  have hsmul : ∀ (c : ℂ) (y : Y), S (c • y) = c • S y := fun c y =>
    eq_of_inner_right_eq (𝒜 := 𝒷) fun x => by
      simp only [← hadj, CStarModule.inner_smul_right_complex]
  set Sl : Y →ₗ[ℂ] X :=
    { toFun := S, map_add' := hadd, map_smul' := fun c y => hsmul c y } with hSl
  have hpos : (0 : ℝ) < ‖T‖ + 1 := by positivity
  have hbound : ∀ y : Y, ‖Sl y‖ ≤ (‖T‖ + 1) * ‖y‖ := by
    refine (Theses.A.CStar.chilb_form_bounded (𝒜 := 𝒷) Sl (‖T‖ + 1) hpos).mpr ?_
    intro y x
    show ‖inner 𝒷 x (S y)‖ ≤ _
    rw [← hadj x y]
    calc ‖inner 𝒷 (T x) y‖ ≤ ‖T x‖ * ‖y‖ := CStarModule.norm_inner_le Y
      _ ≤ (‖T‖ + 1) * ‖x‖ * ‖y‖ := by
          have h1 : ‖T x‖ ≤ (‖T‖ + 1) * ‖x‖ := by
            have h2 := T.le_opNorm x
            have h3 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
            nlinarith
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg y)
  exact ⟨Sl.mkContinuous (‖T‖ + 1) hbound, hadj⟩

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
    IsPositiveOp 𝒷 T ↔ ∀ v : V, 0 ≤ inner 𝒷 (E.η v) (T (E.η v)) := by
  -- **144I** on both sides; the image of `η` is ultranorm dense, so the
  -- vector states it supplies already determine positivity
  refine ⟨fun h v => (hilbmod_ordersep T hT).mp h _, fun hv => ?_⟩
  refine (hilbmod_ordersep T hT).mpr
    (unDense_inner_nonneg (Set.range E.η) E.dense T
      (moduleAdjointable_linear (𝒜 := 𝒷) ⇑T hT).2.2 ?_)
  rintro _ ⟨v, rfl⟩
  exact hv v

/-- **152IX** (`hilmod-fixed-on-V`, dils.tex:3394, Exercise), part 2:
consequently adjointable operators agreeing on the vector states of the
dense image are equal: `S = T` iff `⟨η v, T (η v)⟩ = ⟨η v, S (η v)⟩` for
all `v ∈ V`. -/
theorem hilmod_fixed_on_V_eq [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 V)
    (E : SelfDualCompletion.{u, v, w} B) (T S : E.X →L[ℂ] E.X)
    (hT : ModuleAdjointable 𝒷 ⇑T) (hS : ModuleAdjointable 𝒷 ⇑S)
    (h : ∀ v : V, inner 𝒷 (E.η v) (T (E.η v)) =
      inner 𝒷 (E.η v) (S (E.η v))) :
    T = S := by
  set U : E.X →L[ℂ] E.X := T - S with hU
  obtain ⟨T', hT'⟩ := hT
  obtain ⟨S', hS'⟩ := hS
  -- `U = T - S` is adjointable, hence 𝒷-linear
  have hUadj : ModuleAdjointable 𝒷 ⇑U := by
    refine ⟨fun y => T' y - S' y, fun x y => ?_⟩
    change inner 𝒷 (T x - S x) y = inner 𝒷 x (T' y - S' y)
    rw [CStarModule.inner_sub_left, CStarModule.inner_sub_right, hT' x y, hS' x y]
  obtain ⟨-, -, hUmod⟩ := moduleAdjointable_linear (𝒜 := 𝒷) ⇑U hUadj
  -- `U` is bounded as a module map, hence `‖U z‖_ω ≤ C ‖z‖_ω`
  set C : ℝ := ‖U‖ + 1 with hC
  have hC0 : (0 : ℝ) ≤ C := by positivity
  have hbdd : IsBoundedModuleMap (cstarBInner 𝒷 E.X) (cstarBInner 𝒷 E.X) C ⇑U :=
    { add := fun x y => map_add U x y
      smul_complex := fun c x => map_smul U c x
      smul := hUmod
      bound := fun x => by
        change Real.sqrt ‖(inner 𝒷 (U x) (U x) : 𝒷)‖
          ≤ C * Real.sqrt ‖(inner 𝒷 x x : 𝒷)‖
        rw [← CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷),
          ← CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷)]
        have := U.le_opNorm x
        have h0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
        nlinarith }
  have hUsem : ∀ (ω : NPFunctional 𝒷) (z : E.X),
      unSeminorm ω (inner 𝒷) (U z) ≤ C * unSeminorm ω (inner 𝒷) z := fun ω z =>
    unSeminorm_boundedModuleMap_le _ _ C hC0 _ hbdd ω z
  -- on the dense image `U` has vanishing diagonal
  have hdense : ∀ v : V, (inner 𝒷 (E.η v) (U (E.η v)) : 𝒷) = 0 := fun v => by
    change inner 𝒷 (E.η v) (T (E.η v) - S (E.η v)) = 0
    rw [CStarModule.inner_sub_right, h v, sub_self]
  -- hence everywhere, by ultranorm density and Cauchy-Schwarz for `‖·‖_ω`
  have hdiag : ∀ x : E.X, (inner 𝒷 x (U x) : 𝒷) = 0 := by
    intro x
    refine np_separating _ fun ω => ?_
    set M : ℝ := unSeminorm ω (inner 𝒷) x with hM
    set N : ℝ := unSeminorm ω (inner 𝒷) (U x) with hN
    have hM0 : (0 : ℝ) ≤ M := unSeminorm_nonneg _ _ _
    have hN0 : (0 : ℝ) ≤ N := unSeminorm_nonneg _ _ _
    have key : ∀ ε : ℝ, 0 < ε → ‖ω (inner 𝒷 x (U x))‖ ≤ ε * (N + (M + 1) * C) := by
      intro ε hε
      set ε' : ℝ := min ε 1 with hε'
      have hε'0 : 0 < ε' := lt_min hε one_pos
      obtain ⟨d, ⟨v, rfl⟩, hd⟩ :=
        E.dense x 1 (fun _ => ω) ε' hε'0
      have ht : unSeminorm ω (inner 𝒷) (x - E.η v) ≤ ε' := hd 0
      have ht0 : (0 : ℝ) ≤ unSeminorm ω (inner 𝒷) (x - E.η v) :=
        unSeminorm_nonneg _ _ _
      -- `⟨x,Ux⟩ = ⟨x-d, Ux⟩ + ⟨d, U(x-d)⟩ + ⟨d, Ud⟩`, and the last term is `0`
      have hsplit : (inner 𝒷 x (U x) : 𝒷)
          = inner 𝒷 (x - E.η v) (U x) + inner 𝒷 (E.η v) (U (x - E.η v))
            + inner 𝒷 (E.η v) (U (E.η v)) := by
        rw [map_sub U, CStarModule.inner_sub_right, CStarModule.inner_sub_left]
        abel
      have hadd : ω (inner 𝒷 (x - E.η v) (U x) + inner 𝒷 (E.η v) (U (x - E.η v)))
          = ω (inner 𝒷 (x - E.η v) (U x))
            + ω (inner 𝒷 (E.η v) (U (x - E.η v))) :=
        map_add ω.toPositiveLinearMap _ _
      rw [hsplit, hdense v, add_zero, hadd]
      -- the two Cauchy-Schwarz estimates
      have hcs1 : ‖ω (inner 𝒷 (x - E.η v) (U x))‖
          ≤ unSeminorm ω (inner 𝒷) (x - E.η v) * N :=
        unSeminorm_inner_le ω (cstarBInner 𝒷 E.X) _ _
      have hdM : unSeminorm ω (inner 𝒷) (E.η v) ≤ M + ε' := by
        have htri := unSeminorm_add_le ω (cstarBInner 𝒷 E.X) x (E.η v - x)
        simp only [show (cstarBInner 𝒷 E.X).inner = (inner 𝒷 : E.X → E.X → 𝒷)
          from rfl, add_sub_cancel] at htri
        have hneg : E.η v - x = -(x - E.η v) := by abel
        have hsymm : unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (E.η v - x)
            = unSeminorm ω (inner 𝒷) (x - E.η v) := by
          rw [unSeminorm, unSeminorm, hneg, CStarModule.inner_neg_left,
            CStarModule.inner_neg_right, neg_neg]
        rw [hsymm] at htri
        linarith [ht]
      have hcs2 : ‖ω (inner 𝒷 (E.η v) (U (x - E.η v)))‖
          ≤ unSeminorm ω (inner 𝒷) (E.η v) * (C * unSeminorm ω (inner 𝒷) (x - E.η v)) := by
        refine (unSeminorm_inner_le ω (cstarBInner 𝒷 E.X) _ _).trans ?_
        exact mul_le_mul_of_nonneg_left (hUsem ω _) (unSeminorm_nonneg _ _ _)
      have hεle : ε' ≤ ε := min_le_left _ _
      have hε1 : ε' ≤ 1 := min_le_right _ _
      have hdM0 : (0 : ℝ) ≤ unSeminorm ω (inner 𝒷) (E.η v) := unSeminorm_nonneg _ _ _
      have htε : unSeminorm ω (inner 𝒷) (x - E.η v) ≤ ε := ht.trans hεle
      have h1 : ‖ω (inner 𝒷 (x - E.η v) (U x))‖ ≤ ε * N :=
        hcs1.trans (mul_le_mul_of_nonneg_right htε hN0)
      have h2 : ‖ω (inner 𝒷 (E.η v) (U (x - E.η v)))‖ ≤ ε * ((M + 1) * C) := by
        refine hcs2.trans ?_
        have hD : unSeminorm ω (inner 𝒷) (E.η v) ≤ M + 1 := by linarith
        have hCt : C * unSeminorm ω (inner 𝒷) (x - E.η v) ≤ C * ε :=
          mul_le_mul_of_nonneg_left htε hC0
        calc unSeminorm ω (inner 𝒷) (E.η v) * (C * unSeminorm ω (inner 𝒷) (x - E.η v))
            ≤ (M + 1) * (C * unSeminorm ω (inner 𝒷) (x - E.η v)) :=
              mul_le_mul_of_nonneg_right hD (by positivity)
          _ ≤ (M + 1) * (C * ε) := mul_le_mul_of_nonneg_left hCt (by linarith)
          _ = ε * ((M + 1) * C) := by ring
      calc ‖ω (inner 𝒷 (x - E.η v) (U x)) + ω (inner 𝒷 (E.η v) (U (x - E.η v)))‖
          ≤ ‖ω (inner 𝒷 (x - E.η v) (U x))‖
              + ‖ω (inner 𝒷 (E.η v) (U (x - E.η v)))‖ := norm_add_le _ _
        _ ≤ ε * (N + (M + 1) * C) := by linarith
    -- letting `ε ↓ 0`
    by_contra hne
    have hpos : 0 < ‖ω (inner 𝒷 x (U x))‖ := norm_pos_iff.mpr hne
    have hK : (0 : ℝ) < N + (M + 1) * C + 1 := by nlinarith
    have := key (‖ω (inner 𝒷 x (U x))‖ / (2 * (N + (M + 1) * C + 1)))
      (by positivity)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
    nlinarith
  -- polarization: a sesquilinear form with vanishing diagonal vanishes
  have hsesq : IsBSesquilinear (fun x y : E.X => (inner 𝒷 x (U y) : 𝒷)) :=
    { add_left := fun x y z => by
        simp only [CStarModule.inner_add_left]
      add_right := fun x y z => by
        simp only [map_add U, CStarModule.inner_add_right]
      smul_op := fun β b x y => by
        simp only [hUmod, CStarModule.inner_op_smul_left,
          CStarModule.inner_op_smul_right, mul_assoc]
      smul_left_complex := fun c x y => by
        simp only [CStarModule.inner_smul_left_complex]
        rfl
      smul_right_complex := fun c x y => by
        simp only [map_smul U, CStarModule.inner_smul_right_complex] }
  have hzero : ∀ x y : E.X, (inner 𝒷 x (U y) : 𝒷) = 0 := by
    intro x y
    rw [hilbmod_polarization _ hsesq x y]
    simp only [hdiag, smul_zero, Finset.sum_const_zero]
  have hUz : U = 0 := by
    ext y
    refine eq_of_inner_right_eq (𝒜 := 𝒷) fun x => ?_
    rw [hzero x y]
    simp
  rwa [hU, sub_eq_zero] at hUz

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

/-- Positivity in `𝒷ᵃ(X)` from the vector states: if `⟨x, Zx⟩ ≥ 0` for all
`x`, then `0 ≤ Z` in the C*-order of `𝒷ᵃ(X)`.  This is **144I**
`hilbmod_ordersep` transported from `IsPositiveOp` to the type `Ba 𝒷 X`
(adjoints being unique, `R* = R'` and so `Z = R* R ≥ 0`). -/
private theorem ba_nonneg_of_vector [CompleteSpace X] (Z : Ba 𝒷 X)
    (h : ∀ x : X, 0 ≤ inner 𝒷 x (Z.1 x)) : 0 ≤ Z := by
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  obtain ⟨R, R', hRR', hZ⟩ := (hilbmod_ordersep Z.1 Z.2).mpr h
  let r : Ba 𝒷 X := ⟨R, ⟨R', hRR'⟩⟩
  have hstar : ((star r : Ba 𝒷 X)).1 = R' := by
    have h1 : ModuleAdjointTo 𝒷 (⇑R : X → X) ⇑((star r : Ba 𝒷 X)).1 :=
      baSubalgebra_star_spec r
    exact DFunLike.coe_injective
      (moduleAdjointTo_unique (𝒜 := 𝒷) (⇑R) _ _ h1 hRR')
  have hzz : Z = (star r * r : Ba 𝒷 X) := by
    refine Subtype.ext (ContinuousLinearMap.ext fun x => ?_)
    change Z.1 x = ((star r : Ba 𝒷 X)).1 ((r : Ba 𝒷 X).1 x)
    rw [hZ, hstar]
    rfl
  rw [hzz]
  exact star_mul_self_nonneg r

/-- **153I** (`hilbmod-ad-ncp`, dils.tex:3487, Proposition), part 1: for an
adjointable bounded module map `T : X → Y` (with adjoint `T'`) between
Hilbert 𝒷-modules, the map `ad_T : 𝒷ᵃ(Y) → 𝒷ᵃ(X)`, `ad_T(S) = T* S T`,
is completely positive.

**153II** is the author's proof, transcribed here for part 1. -/
theorem hilbmod_ad_cp [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[ℂ] Y) (T' : Y →L[ℂ] X) (hT : ModuleAdjointTo 𝒷 ⇑T ⇑T') :
    ∃ ad : Ba 𝒷 Y →ₗ[ℂ] Ba 𝒷 X,
      (∀ S : Ba 𝒷 Y, (ad S).1 = T'.comp (S.1.comp T)) ∧
      IsCompletelyPositiveMap ad := by
  -- dils.tex:3495 (**153II**), transcribed: `∑ᵢⱼ Bⱼ* T* Aⱼ* Aᵢ T Bᵢ =
  -- (∑ᵢ Aᵢ T Bᵢ)* (∑ⱼ Aⱼ T Bⱼ) ≥ 0`, checked on vector states (**144I**).
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  let _ : NormedSpace ℂ Y := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  have hTsymm : ModuleAdjointTo 𝒷 (⇑T' : Y → X) ⇑T :=
    moduleAdjointTo_unique (𝒜 := 𝒷) _ _ _ (moduleAdjointTo_symm (𝒜 := 𝒷) _ _ hT)
      (moduleAdjointTo_symm (𝒜 := 𝒷) _ _ hT) ▸
      moduleAdjointTo_symm (𝒜 := 𝒷) _ _ hT
  -- `T' ∘ S ∘ T` is adjointable, with adjoint `T' ∘ S* ∘ T`
  have hmem : ∀ S : Ba 𝒷 Y, ModuleAdjointable 𝒷 ⇑(T'.comp (S.1.comp T)) := by
    intro S
    obtain ⟨S', hS'⟩ := S.2
    refine ⟨fun x => T' (S' (T x)), fun x x' => ?_⟩
    change inner 𝒷 (T' (S.1 (T x))) x' = inner 𝒷 x (T' (S' (T x')))
    rw [hTsymm (S.1 (T x)) x', hS' (T x) (T x'), ← hT x (S' (T x'))]
  set ad : Ba 𝒷 Y →ₗ[ℂ] Ba 𝒷 X :=
    { toFun := fun S => ⟨T'.comp (S.1.comp T), hmem S⟩
      map_add' := fun S S' => Subtype.ext (by
        refine ContinuousLinearMap.ext fun x => ?_
        change T' ((S + S').1 (T x)) = T' (S.1 (T x)) + T' (S'.1 (T x))
        change T' (S.1 (T x) + S'.1 (T x)) = _
        rw [map_add])
      map_smul' := fun c S => Subtype.ext (by
        refine ContinuousLinearMap.ext fun x => ?_
        change T' ((c • S).1 (T x)) = c • T' (S.1 (T x))
        change T' (c • S.1 (T x)) = _
        rw [map_smul]) } with had
  refine ⟨ad, fun S => rfl, ?_⟩
  intro n A B
  -- the vector-state computation of dils.tex:3495
  refine ba_nonneg_of_vector _ fun x => ?_
  set C : Fin n → Y := fun i => (A i).1 (T ((B i).1 x)) with hC
  -- the coercion `𝒷ᵃ(X) → B(X)` is additive, so it commutes with the sums
  let val : Ba 𝒷 X →+ (X →L[ℂ] X) :=
    { toFun := fun S => S.1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hvalSum : ∀ f : Fin n → Fin n → Ba 𝒷 X,
      ((∑ i, ∑ j, f i j : Ba 𝒷 X)).1 x = ∑ i, ∑ j, ((f i j).1 x) := by
    intro f
    have h : ((∑ i, ∑ j, f i j : Ba 𝒷 X)).1 = ∑ i, ∑ j, (f i j).1 := by
      change val _ = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_sum val _ _
    rw [h]
    simp
  -- `⟨x, Bᵢ* T* Aᵢ* Aⱼ T Bⱼ x⟩ = ⟨AᵢTBᵢx, AⱼTBⱼx⟩`
  have hterm : ∀ i j : Fin n,
      (inner 𝒷 x
        (((star (B i) * ad (star (A i) * A j) * B j : Ba 𝒷 X)).1 x) : 𝒷)
        = inner 𝒷 (C i) (C j) := by
    intro i j
    have hBi : ModuleAdjointTo 𝒷 (⇑((B i).1) : X → X)
        ⇑((star (B i) : Ba 𝒷 X)).1 := baSubalgebra_star_spec (B i)
    have hAi : ModuleAdjointTo 𝒷 (⇑((A i).1) : Y → Y)
        ⇑((star (A i) : Ba 𝒷 Y)).1 := baSubalgebra_star_spec (A i)
    change (inner 𝒷 x
      (((star (B i) : Ba 𝒷 X)).1
        (T' (((star (A i) : Ba 𝒷 Y)).1 ((A j).1 (T ((B j).1 x)))))) : 𝒷) = _
    rw [← hBi x _, ← hT ((B i).1 x) _, ← hAi (T ((B i).1 x)) _]
  rw [hvalSum]
  simp only [CStarModule.inner_sum_right, hterm]
  -- `∑ᵢⱼ ⟨Cᵢ,Cⱼ⟩ = ⟨∑ᵢ Cᵢ, ∑ⱼ Cⱼ⟩ ≥ 0`
  have hgram : ∑ i, ∑ j, (inner 𝒷 (C i) (C j) : 𝒷)
      = inner 𝒷 (∑ i, C i) (∑ j, C j) := by
    rw [CStarModule.inner_sum_left]
    exact Finset.sum_congr rfl fun i _ => (CStarModule.inner_sum_right).symm
  rw [hgram]
  exact CStarModule.inner_self_nonneg

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

section AdjVector

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  {n : ℕ}

set_option linter.unusedSectionVars false

/-- The functional `P ↦ ∑ᵢⱼ cᵢ* Pᵢⱼ cⱼ` whose positivity for all `c`
characterises positivity of a matrix (**33II**.1
`cstar_matrix_positive_iff`); packaged as an additive map so that it can be
pushed through finite sums of matrices. -/
private def conjFun (c : Fin n → 𝒜) : CStarMatrix (Fin n) (Fin n) 𝒜 →+ 𝒜 where
  toFun P := ∑ i, ∑ j, star (c i) * P i j * c j
  map_zero' := by simp
  map_add' P Q := by
    simp only [CStarMatrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

private theorem conjFun_apply (c : Fin n → 𝒜) (P : CStarMatrix (Fin n) (Fin n) 𝒜) :
    conjFun c P = ∑ i, ∑ j, star (c i) * P i j * c j := rfl

/-- `∑ᵢⱼ Gᵢ* d Hⱼ = (∑ᵢ Gᵢ)* d (∑ⱼ Hⱼ)`. -/
private theorem sum_star_mul_mul_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → 𝒜) (H : κ → 𝒜) (d : 𝒜) :
    ∑ i, ∑ j, star (G i) * d * H j = star (∑ i, G i) * d * ∑ j, H j := by
  rw [star_sum, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

/-- `∑ₖₗ zₖ* zₗ = (∑ₖ zₖ)* (∑ₗ zₗ)`, hence positive. -/
private theorem sum_star_mul_sum' {ι : Type*} [Fintype ι] (z : ι → 𝒜) :
    ∑ k, ∑ l, star (z k) * z l = star (∑ k, z k) * ∑ l, z l := by
  rw [star_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm

/-- **153IV** (`hilbmod-adj-vector-ncp`, dils.tex:3517, Exercise): for a
C*-algebra `𝒜` (here: von Neumann algebra, so that normality makes sense)
and `a₁, …, aₙ ∈ 𝒜`, the map `φ : 𝒜 → Mₙ𝒜`, `φ(d) = (aᵢ* d aⱼ)ᵢⱼ`, is an
ncp-map.

The author's solution routes through **153I** `hilbmod_ad_ncp` (`φ = ad_T`
for the row vector `T : 𝒜ⁿ → 𝒜`, `(bᵢ)ᵢ ↦ ∑ᵢ bᵢaᵢ`), which is still open
here — it waits on **152X**.  So this is a direct argument instead: by
**33II**.1 both claims reduce to the scalar identity
`∑ᵢⱼ cᵢ* φ(d)ᵢⱼ cⱼ = v* d v` with `v = ∑ᵢ aᵢcᵢ`, after which complete
positivity is the observation that the corresponding double sum is a square
`w* w`, and normality is **44VIII** `ad_normal` for `v`. -/
theorem hilbmod_adj_vector_ncp {𝒜 : Type u} [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜] {n : ℕ}
    [PartialOrder (CStarMatrix (Fin n) (Fin n) 𝒜)]
    [StarOrderedRing (CStarMatrix (Fin n) (Fin n) 𝒜)]
    (a : Fin n → 𝒜) :
    ∃ φ : 𝒜 →ₗ[ℂ] CStarMatrix (Fin n) (Fin n) 𝒜,
      (∀ (d : 𝒜) (i j : Fin n), φ d i j = star (a i) * d * a j) ∧
      IsCompletelyPositiveMap φ ∧ PreservesDirSups ⇑φ := by
  classical
  set φ : 𝒜 →ₗ[ℂ] CStarMatrix (Fin n) (Fin n) 𝒜 :=
    { toFun := fun d => CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * d * a j)
      map_add' := by
        intro x y; ext i j
        show star (a i) * (x + y) * a j = star (a i) * x * a j + star (a i) * y * a j
        noncomm_ring
      map_smul' := by
        intro r x; ext i j
        show star (a i) * (r • x) * a j = r • (star (a i) * x * a j)
        rw [mul_smul_comm, smul_mul_assoc] } with hφdef
  have hentry : ∀ (d : 𝒜) (i j : Fin n), φ d i j = star (a i) * d * a j := fun _ _ _ => rfl
  -- `φ(d)` conjugated by two matrices collapses to a single `ad`-expression
  have hgen : ∀ (M N : CStarMatrix (Fin n) (Fin n) 𝒜) (c : Fin n → 𝒜) (d : 𝒜),
      conjFun c (star M * φ d * N)
        = star (∑ i, ∑ s, a s * (M s i * c i)) * d * ∑ j, ∑ t, a t * (N t j * c j) := by
    intro M N c d
    have hij : ∀ i j : Fin n, star (c i) * (star M * φ d * N) i j * c j
        = star (∑ s, a s * (M s i * c i)) * d * ∑ t, a t * (N t j * c j) := by
      intro i j
      have hA : star (c i) * (star M * φ d * N) i j * c j
          = ∑ s, ∑ t, star (a s * (M s i * c i)) * d * (a t * (N t j * c j)) := by
        rw [mul_assoc (star M) (φ d) N, CStarMatrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [CStarMatrix.star_apply, CStarMatrix.mul_apply, Finset.mul_sum, Finset.mul_sum,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hentry]
        simp only [star_mul]
        noncomm_ring
      rw [hA]
      exact sum_star_mul_mul_sum _ _ d
    rw [conjFun_apply]
    simp only [hij]
    exact sum_star_mul_mul_sum _ _ d
  -- the special case `M = N = 1`: `∑ᵢⱼ cᵢ* φ(d)ᵢⱼ cⱼ = v* d v` with `v = ∑ᵢ aᵢcᵢ`
  have hcollapse : ∀ (c : Fin n → 𝒜) (d : 𝒜),
      conjFun c (φ d) = star (∑ i, a i * c i) * d * ∑ j, a j * c j := by
    intro c d
    have hij : ∀ i j : Fin n, star (c i) * φ d i j * c j
        = star (a i * c i) * d * (a j * c j) := by
      intro i j; rw [hentry]; simp only [star_mul]; noncomm_ring
    rw [conjFun_apply]
    simp only [hij]
    exact sum_star_mul_mul_sum _ _ d
  refine ⟨φ, hentry, ?_, ?_⟩
  · -- complete positivity
    intro m x B
    refine (cstar_matrix_positive_iff _).mpr fun c => ?_
    set V : Fin m → 𝒜 := fun k => ∑ i, ∑ s, a s * ((B k) s i * c i) with hV
    have hpush : ∑ i, ∑ j,
        star (c i) * (∑ k, ∑ l, star (B k) * φ (star (x k) * x l) * B l) i j * c j
        = ∑ k, ∑ l, star (x k * V k) * (x l * V l) := by
      rw [← conjFun_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hgen (B k) (B l) c (star (x k) * x l)]
      simp only [star_mul]
      noncomm_ring
    rw [hpush, sum_star_mul_sum']
    exact star_mul_self_nonneg _
  · -- normality
    intro D s hne hdir hlub
    have hbdd : BddAbove D := ⟨s, hlub.1⟩
    have hDh : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, hbdd⟩
    have hs : s = dirSup D hDh := hlub.unique (isLUB_dirSup D hDh)
    -- `φ` is positive, hence monotone
    have hpos : ∀ e : 𝒜, 0 ≤ e → 0 ≤ φ e := by
      intro e he
      refine (cstar_matrix_positive_iff _).mpr fun c => ?_
      rw [← conjFun_apply, hcollapse]
      exact star_left_conjugate_nonneg he _
    have hmono : ∀ e e' : 𝒜, e ≤ e' → φ e ≤ φ e' := by
      intro e e' h
      rw [← sub_nonneg] at h ⊢
      rw [← map_sub]
      exact hpos _ h
    refine ⟨?_, ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      exact hmono _ _ (Subtype.coe_le_coe.mpr (hlub.1 hd))
    · intro Mub hMub
      rw [← sub_nonneg]
      refine (cstar_matrix_positive_iff _).mpr fun c => ?_
      set v : 𝒜 := ∑ i, a i * c i with hv
      have hub : star v * ↑(dirSup D hDh) * v ≤ conjFun c Mub := by
        refine (ad_normal v D hDh).2 ?_
        rintro _ ⟨d, hd, rfl⟩
        have h0 : (0 : CStarMatrix (Fin n) (Fin n) 𝒜) ≤ Mub - φ ↑d :=
          sub_nonneg.mpr (hMub ⟨d, hd, rfl⟩)
        have h1 := (cstar_matrix_positive_iff _).mp h0 c
        rw [← conjFun_apply, map_sub, hcollapse] at h1
        exact sub_nonneg.mp h1
      rw [← conjFun_apply, map_sub, hcollapse, ← hv, ← hs] at *
      exact sub_nonneg.mpr hub

end AdjVector

end Theses.B.Dils
