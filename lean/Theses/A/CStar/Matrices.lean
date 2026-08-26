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

**All statements of parsecs 320–341 are proved** (the last two, **34VII**
`ccstar_pos_mat` and **34IX**.2 `cp_commutative_dom`, in session 74).
See CONVENTIONS.md for the numbering (**34V** = parsec 340, point 50) and
naming conventions.
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

/-- Definiteness of the 𝒜-valued inner product, in the first argument. -/
private theorem eq_of_inner_left_eq {W : Type*} [NormedAddCommGroup W]
    [Module ℂ W] [SMul 𝒜 W] [CStarModule 𝒜 W] {a b : W}
    (h : ∀ y : W, inner 𝒜 a y = inner 𝒜 b y) : a = b := by
  have h0 : inner 𝒜 (a - b) (a - b) = (0 : 𝒜) := by
    rw [CStarModule.inner_sub_left, h (a - b), sub_self]
  exact sub_eq_zero.mp (CStarModule.inner_self.mp h0)

/-- Definiteness of the 𝒜-valued inner product, in the second argument. -/
theorem eq_of_inner_right_eq {W : Type*} [NormedAddCommGroup W]
    [Module ℂ W] [SMul 𝒜 W] [CStarModule 𝒜 W] {a b : W}
    (h : ∀ x : W, inner 𝒜 x a = inner 𝒜 x b) : a = b := by
  have h0 : inner 𝒜 (a - b) (a - b) = (0 : 𝒜) := by
    rw [CStarModule.inner_sub_right, h (a - b), sub_self]
  exact sub_eq_zero.mp (CStarModule.inner_self.mp h0)

/-- **32I** (`chilb-basic`, cstar.tex:4981, Definition), embedded claim: a
map is adjoint to at most one map, denoted `T*`. -/
theorem moduleAdjointTo_unique (T : X → Y) (S S' : Y → X)
    (h : ModuleAdjointTo 𝒜 T S) (h' : ModuleAdjointTo 𝒜 T S') : S = S' := by
  funext y
  exact eq_of_inner_right_eq fun x => ((h x y).symm.trans (h' x y))

/-- **32I** (`chilb-basic`, cstar.tex:4981, Definition), embedded claim: an
adjointable map is automatically linear and a module map. -/
theorem moduleAdjointable_linear (T : X → Y) (hT : ModuleAdjointable 𝒜 T) :
    (∀ x x' : X, T (x + x') = T x + T x') ∧
      (∀ (c : ℂ) (x : X), T (c • x) = c • T x) ∧
      ∀ (a : 𝒜) (x : X), T (a • x) = a • T x := by
  obtain ⟨S, hS⟩ := hT
  have hS' : ∀ (x : X) (y : Y), inner 𝒜 (T x) y = inner 𝒜 x (S y) := hS
  refine ⟨fun x x' => eq_of_inner_left_eq (𝒜 := 𝒜) fun y => ?_,
    fun c x => eq_of_inner_left_eq (𝒜 := 𝒜) fun y => ?_,
    fun a x => eq_of_inner_left_eq (𝒜 := 𝒜) fun y => ?_⟩
  · simp [hS']
  · simp [hS']
  · simp [hS']

/-! **32II** (cstar.tex:5038, Example): `𝒜^N` with
`⟨x, y⟩ = ∑ₙ xₙ* yₙ` is a Hilbert 𝒜-module — Mathlib:
`WithCStarModule 𝒜 (Fin N → 𝒜)` (notation `C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜)`) with its
`CStarModule` instance. -/

/-- **32III** (cstar.tex:5044, Exercise), part 1: if `T` is adjoint to `S`
then `S` is adjoint to `T` (so `T** = T`). -/
theorem moduleAdjointTo_symm (T : X → Y) (S : Y → X)
    (h : ModuleAdjointTo 𝒜 T S) : ModuleAdjointTo 𝒜 S T := by
  intro y x
  rw [← CStarModule.star_inner (A := 𝒜) x (S y), ← h x y,
    CStarModule.star_inner]

/-- **32III** (cstar.tex:5044, Exercise), part 2: `(T + T')* = T* + T'*` and
`(λT)* = λ̄ T*`. -/
theorem moduleAdjointTo_add_smul (T T' : X → Y) (S S' : Y → X) (c : ℂ)
    (h : ModuleAdjointTo 𝒜 T S) (h' : ModuleAdjointTo 𝒜 T' S') :
    ModuleAdjointTo 𝒜 (fun x => T x + T' x) (fun y => S y + S' y) ∧
      ModuleAdjointTo 𝒜 (fun x => c • T x)
        (fun y => (starRingEnd ℂ) c • S y) := by
  have h₁ : ∀ (x : X) (y : Y), inner 𝒜 (T x) y = inner 𝒜 x (S y) := h
  have h₂ : ∀ (x : X) (y : Y), inner 𝒜 (T' x) y = inner 𝒜 x (S' y) := h'
  constructor
  · intro x y
    simp [h₁, h₂]
  · intro x y
    simp [h₁]

/-- **32III** (cstar.tex:5044, Exercise), part 3: `ST` is adjoint to
`T* S*`, i.e. `(ST)* = T* S*`. -/
theorem moduleAdjointTo_comp (T : X → Y) (S : Y → Z) (T' : Y → X)
    (S' : Z → Y) (hT : ModuleAdjointTo 𝒜 T T') (hS : ModuleAdjointTo 𝒜 S S') :
    ModuleAdjointTo 𝒜 (S ∘ T) (T' ∘ S') := by
  intro x z
  simp only [Function.comp_apply]
  rw [hS (T x) z, hT x (S' z)]

end HilbertModules

/-- **32IV** (cstar.tex:5166, Exercise), part 1: `J = {f ∈ C[0,1] : f(0)=0}`
is closed.  That it is an *ideal* is `paschke_ideal` below, and the Hilbert
`C[0,1]`-module structure `⟨f, g⟩ = f* g` that the exercise then puts on `J`
is `PaschkeJ` further below.

*Class 1 — faithful.*  Solution `parsec-320.40` gets closedness from `J`
being "the kernel of the map miu-map `f ↦ f(0) : C[0,1] → ℂ`", and that is
the route here: the kernel of `ContinuousMap.evalStarAlgHom` is the preimage
of the closed set `{0}` under a continuous map. -/
theorem paschke_ideal_closed :
    IsClosed {f : C(unitInterval, ℂ) | f 0 = 0} := by
  have hker : {f : C(unitInterval, ℂ) | f 0 = 0}
      = ContinuousMap.evalStarAlgHom ℂ ℂ (0 : unitInterval) ⁻¹' {0} := rfl
  rw [hker]
  exact isClosed_singleton.preimage (continuous_eval_const (0 : unitInterval))

/-- **32IV** (cstar.tex:5166, Exercise), part 1, the ideal clause:
`J = {f ∈ C[0,1] : f(0)=0}` is a (two-sided, hence right) ideal of `C[0,1]`,
and it is closed.

*Class 1 — faithful.*  This is solution `parsec-320.40`'s reading of `J`: the
kernel of evaluation at `0`.  Closedness is `paschke_ideal_closed`. -/
theorem paschke_ideal :
    ∃ J : Ideal C(unitInterval, ℂ),
      (J : Set C(unitInterval, ℂ)) = {f : C(unitInterval, ℂ) | f 0 = 0} ∧
      IsClosed (J : Set C(unitInterval, ℂ)) := by
  refine ⟨{ carrier := {f : C(unitInterval, ℂ) | f 0 = 0}
            add_mem' := fun {f g} hf hg => by
              simp only [Set.mem_setOf_eq] at hf hg ⊢
              simp [hf, hg]
            zero_mem' := by simp
            smul_mem' := fun c {f} hf => by
              simp only [Set.mem_setOf_eq] at hf ⊢
              simp [hf] }, rfl, paschke_ideal_closed⟩

/-- **32IV** (cstar.tex:5166, Exercise), part 2: the inclusion `J → C[0,1]`
is a bounded module map with no adjoint: there is no `b ∈ J` with
`⟨b, a⟩ = a` for all `a ∈ J` (so, unlike for Hilbert spaces (**5XI**), a
bounded module map between Hilbert 𝒜-modules need not be adjointable;
**32V**, Remark, on self-dual modules is not converted). -/
theorem paschke_inclusion_no_adjoint :
    ¬∃ b : C(unitInterval, ℂ), b 0 = 0 ∧
      ∀ a : C(unitInterval, ℂ), a 0 = 0 → star b * a = a := by
  rintro ⟨b, hb0, hb⟩
  -- the coordinate function `t ↦ t` lies in `J`
  set c : C(unitInterval, ℂ) := ⟨fun t => ((t : ℝ) : ℂ), by fun_prop⟩ with hc
  have hc0 : c 0 = 0 := by simp [hc]
  have key := hb c hc0
  -- hence `b` is constantly `1` away from `0`
  have hpt : ∀ t : unitInterval, (t : ℝ) ≠ 0 → b t = 1 := by
    intro t ht
    have h1 := congrArg (fun f : C(unitInterval, ℂ) => f t) key
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, hc,
      ContinuousMap.coe_mk] at h1
    have h2 : star (b t) = 1 := by
      have hne : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
      exact mul_right_cancel₀ hne (h1.trans (one_mul _).symm)
    simpa using congrArg star h2
  -- but `b` is continuous and `b 0 = 0`
  have hu : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ∈ unitInterval := by
    intro n
    refine Set.mem_Icc.mpr ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  set u : ℕ → unitInterval := fun n => ⟨1 / ((n : ℝ) + 1), hu n⟩ with hud
  have hlim : Filter.Tendsto u Filter.atTop (nhds (0 : unitInterval)) := by
    rw [tendsto_subtype_rng]
    simpa [hud] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hcont : Filter.Tendsto (fun n => b (u n)) Filter.atTop (nhds (b 0)) :=
    (b.continuous.tendsto 0).comp hlim
  have hone : ∀ n, b (u n) = 1 := by
    intro n
    refine hpt (u n) ?_
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simpa [hud] using this.ne'
  rw [funext hone, hb0] at hcont
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hcont)

/-! ### `J` as a Hilbert `C[0,1]`-module, and the inclusion as a module map

**32IV** asks for `J` itself: that it is a closed right ideal "and thus a
Hilbert `C[0,1]`-module", and that "the inclusion `T : J → C[0,1]` is a
bounded module map, which has no adjoint".  The two theorems above state the
closed-ideal half and the exercise's own *route* to non-adjointability (no
`b ∈ J` with `⟨b,a⟩ = a`); what follows carries `J` as a type, so that the
Hilbert-module clause and the non-adjointability of `T` can be stated as the
exercise states them.

Mathlib's `CStarModule` convention is `⟪x, y⟫ = y x*` where the thesis writes
`⟨x, y⟩ = x* y`; on the *commutative* `C[0,1]` the two agree. -/

/-- **32IV** (cstar.tex:5166, Exercise): `J = {f ∈ C[0,1] : f(0) = 0}`, as a
`ℂ`-submodule of `C[0,1]` — the carrier of the ideal `paschke_ideal`, in the
form that gives it a type with a norm. -/
noncomputable def paschkeJ : Submodule ℂ C(unitInterval, ℂ) where
  carrier := {f : C(unitInterval, ℂ) | f 0 = 0}
  add_mem' := by intro a b ha hb; simp_all
  zero_mem' := by simp
  smul_mem' := by intro c a ha; simp_all

/-- **32IV** (cstar.tex:5166, Exercise): the type `J`. -/
noncomputable abbrev PaschkeJ := ↥paschkeJ

/-- `J` is a right ideal, so `C[0,1]` acts on it. -/
noncomputable instance : SMul C(unitInterval, ℂ) PaschkeJ where
  smul a x := ⟨a * (x : C(unitInterval, ℂ)),
    show (a * (x : C(unitInterval, ℂ))) 0 = 0 by
      rw [ContinuousMap.mul_apply, show (x : C(unitInterval, ℂ)) 0 = 0 from x.2,
        mul_zero]⟩

/-- **32IV** (cstar.tex:5166, Exercise), part 1, closing clause: `J` carries
the `C[0,1]`-valued inner product `⟨f, g⟩ = f* g` of a pre-Hilbert
`C[0,1]`-module.  Every axiom is inherited from `C[0,1]` as a module over
itself, the ideal property being what keeps `f* g` and `a·f` inside `J`. -/
noncomputable instance : CStarModule C(unitInterval, ℂ) PaschkeJ where
  inner x y := (y : C(unitInterval, ℂ)) * star (x : C(unitInterval, ℂ))
  inner_add_right := by
    intro x y z
    show ((y : C(unitInterval, ℂ)) + (z : C(unitInterval, ℂ))) * _ = _
    ring
  inner_self_nonneg := by intro x; exact mul_star_self_nonneg _
  inner_self := by
    intro x
    show (x : C(unitInterval, ℂ)) * star (x : C(unitInterval, ℂ)) = 0 ↔ _
    rw [CStarRing.mul_star_self_eq_zero_iff]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  inner_op_smul_right := by
    intro a x y
    show ((a • y : PaschkeJ) : C(unitInterval, ℂ)) * _ = a * ((y : C(unitInterval, ℂ)) * _)
    show a * (y : C(unitInterval, ℂ)) * _ = _
    rw [mul_assoc]
  inner_smul_right_complex := by
    intro z x y
    show ((z • y : PaschkeJ) : C(unitInterval, ℂ)) * _ = z • ((y : C(unitInterval, ℂ)) * _)
    show (z • (y : C(unitInterval, ℂ))) * _ = _
    rw [smul_mul_assoc]
  star_inner := by
    intro x y
    show star ((y : C(unitInterval, ℂ)) * star (x : C(unitInterval, ℂ)))
      = (x : C(unitInterval, ℂ)) * star (y : C(unitInterval, ℂ))
    rw [star_mul, star_star, mul_comm]
  norm_eq_sqrt_norm_inner_self := by
    intro x
    show ‖x‖ = Real.sqrt ‖(x : C(unitInterval, ℂ)) * star (x : C(unitInterval, ℂ))‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity),
      show ‖x‖ = ‖(x : C(unitInterval, ℂ))‖ from rfl]
    simpa [sq] using
      Eq.symm <| CStarRing.norm_self_mul_star (x := (x : C(unitInterval, ℂ)))

/-- `J` is closed in the complete `C[0,1]`, hence complete. -/
noncomputable instance : CompleteSpace PaschkeJ :=
  (show IsClosed ((paschkeJ : Set C(unitInterval, ℂ))) from
    paschke_ideal_closed).completeSpace_coe

/-- **32IV** (cstar.tex:5166, Exercise), part 1, closing clause: `J` is a
*Hilbert* `C[0,1]`-module — a pre-Hilbert module, and complete, which it is
because it is closed in `C[0,1]`. -/
noncomputable example : CStarModule C(unitInterval, ℂ) PaschkeJ := inferInstance

example : CompleteSpace PaschkeJ := inferInstance

/-- **32IV** (cstar.tex:5166, Exercise), part 2: the inclusion
`T : J → C[0,1]`, as a bounded (indeed contractive) linear map. -/
noncomputable def paschkeInclusion : PaschkeJ →L[ℂ] C(unitInterval, ℂ) :=
  paschkeJ.subtypeL

@[simp] theorem paschkeInclusion_apply (x : PaschkeJ) :
    paschkeInclusion x = (x : C(unitInterval, ℂ)) := rfl

/-- **32IV** (cstar.tex:5166, Exercise), part 2, as the Exercise states it:
the inclusion `T : J → C[0,1]` is a bounded module map — boundedness is
carried by its `→L[ℂ]` type, and the module-map clause is the first conjunct
— **which has no adjoint**.

*Class 1 — faithful.*  This is the Exercise's own parenthetical: "for if `T`
had an adjoint `T*`, then `⟨T*1, a⟩ = ⟨1, Ta⟩ = a` for all `a ∈ J`", which
is exactly the situation `paschke_inclusion_no_adjoint` rules out, with
`b := T*(1)`. -/
theorem paschke_inclusion_not_adjointable :
    (∀ (a : C(unitInterval, ℂ)) (x : PaschkeJ),
        paschkeInclusion (a • x) = a • paschkeInclusion x) ∧
      ¬ ModuleAdjointable C(unitInterval, ℂ) ⇑paschkeInclusion := by
  refine ⟨fun a x => rfl, ?_⟩
  rintro ⟨S, hS⟩
  -- `b := T*(1)` lies in `J`
  refine paschke_inclusion_no_adjoint
    ⟨(S 1 : C(unitInterval, ℂ)), (S 1).2, fun a ha => ?_⟩
  -- `⟨T a, 1⟩ = ⟨a, T* 1⟩` reads `1 · a* = b · a*`, i.e. `a* = b a*`
  have h := hS ⟨a, ha⟩ 1
  show (star (S 1 : C(unitInterval, ℂ))) * a = a
  have h2 : (1 : C(unitInterval, ℂ)) * star a
      = (S 1 : C(unitInterval, ℂ)) * star a := h
  have h' : star a = (S 1 : C(unitInterval, ℂ)) * star a := by rwa [one_mul] at h2
  calc (star (S 1 : C(unitInterval, ℂ))) * a
      = star ((S 1 : C(unitInterval, ℂ)) * star a) := by
        rw [star_mul, star_star, mul_comm]
    _ = star (star a) := by rw [← h']
    _ = a := star_star a

section AValuedInner

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
variable {X : Type*} [AddCommGroup X] [Module ℂ X] [SMul 𝒜 X]

/-- **32I** (`chilb-basic`, cstar.tex:4981, Definition): an *𝒜-valued inner
product* on an 𝒜-module `X` — `⟨x, ·⟩` a module map, `⟨x,x⟩ ≥ 0`, and
`⟨x,y⟩ = ⟨y,x⟩*`.  Definiteness is **not** required (32I calls a definite one
a *pre-Hilbert 𝒜-module*), and `X` carries no norm.  This is the setting of
**32VI**, which is stated "for every inner product on a right 𝒜-module `X`".

The arguments are in Mathlib's order, `f x y = ⟨y, x⟩` of the thesis, so that
the fields are literally those of `CStarModule` minus definiteness
(`inner_self`) and minus the norm (`norm_eq_sqrt_norm_inner_self`); the
thesis's right action `y · a` is `a* • y` here (cf. the convention note on
`chilb_cs`). -/
structure IsAValuedInner (𝒜 : Type*) {X : Type*} [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [AddCommGroup X] [Module ℂ X] [SMul 𝒜 X]
    (f : X → X → 𝒜) : Prop where
  /-- `⟨x, ·⟩` is additive. -/
  add_right : ∀ x y z, f x (y + z) = f x y + f x z
  /-- `⟨x, ·⟩` is a module map. -/
  smul_right : ∀ (a : 𝒜) (x y : X), f x (a • y) = a * f x y
  /-- `⟨x, ·⟩` is ℂ-linear. -/
  smul_right_complex : ∀ (c : ℂ) (x y : X), f x (c • y) = c • f x y
  /-- `⟨x,x⟩ ≥ 0`. -/
  self_nonneg : ∀ x, 0 ≤ f x x
  /-- `⟨x,y⟩ = ⟨y,x⟩*`. -/
  star_symm : ∀ x y, star (f x y) = f y x

attribute [local instance] InnerProductSpace.Core.toPreInner'

/-- The thesis's observation inside the proof of **32VI** (**32VIII**): for a
state `ω` of `𝒜`, the map `(u,v) ↦ ω(⟨u,v⟩)` is a complex-valued inner
product on `X` — *possibly indefinite*, so a `PreInnerProductSpace.Core`, the
setting of **4XV** in `A/CStar/Basic`. -/
private noncomputable def stateCore {f : X → X → 𝒜} (hf : IsAValuedInner 𝒜 f)
    (ω : 𝒜 →ₗ[ℂ] ℂ) (hω : IsState ω) : PreInnerProductSpace.Core ℂ X where
  inner u v := ω (f u v)
  conj_inner_symm u v := by
    have hi : IsInvolutionPreserving ω := cstar_p_implies_i ω hω.1
    have h := hi (f v u)
    rw [hf.star_symm] at h
    simpa [Complex.star_def] using h.symm
  re_inner_nonneg u := (Complex.le_def.mp (hω.1 _ (hf.self_nonneg u))).1
  add_left u v z := by
    have h : f (u + v) z = f u z + f v z := by
      rw [← hf.star_symm z (u + v), hf.add_right z u v, star_add, hf.star_symm,
        hf.star_symm]
    show ω (f (u + v) z) = ω (f u z) + ω (f v z)
    rw [h, map_add]
  smul_left u v r := by
    have h : f (r • u) v = (starRingEnd ℂ) r • f u v := by
      rw [← hf.star_symm v (r • u), hf.smul_right_complex, star_smul, hf.star_symm]
      rfl
    show ω (f (r • u) v) = (starRingEnd ℂ) r * ω (f u v)
    rw [h, map_smul, smul_eq_mul]

/-- Cauchy–Schwarz for the scalar inner product `ω(⟨·,·⟩)` — **4XV**.1 in
`A/CStar/Basic`, which the thesis's proof of **32VI** cites by name. -/
private theorem state_cs {f : X → X → 𝒜} (hf : IsAValuedInner 𝒜 f)
    (ω : 𝒜 →ₗ[ℂ] ℂ) (hω : IsState ω) (u v : X) :
    ‖ω (f u v)‖ ^ 2 ≤ RCLike.re (ω (f u u)) * RCLike.re (ω (f v v)) :=
  inner_product_basic_1 (V := X) (c := stateCore hf ω hω) u v

/-- **32VI** (`chilb-cs`, cstar.tex:5096, Proposition (Cauchy–Schwarz)), in
the generality the Proposition states it: `⟨x,y⟩⟨y,x⟩ ≤ ‖⟨y,y⟩‖ ⟨x,x⟩` for
*every* 𝒜-valued inner product on an 𝒜-module `X` — definite or not, and
with no norm on `X`.  (`chilb_cs` below is the special case of a
`CStarModule`, which is where the rest of the file uses it.)

*Class 1 — faithful.*  The proof is **32VIII**'s, step for step.  The states
of `𝒜` are order separating (**22VIII**.2), so it suffices to show
`ω(⟨x,y⟩⟨y,x⟩) ≤ ‖⟨y,y⟩‖ ω(⟨x,x⟩)` for each state `ω`; `(u,v) ↦ ω(⟨u,v⟩)` is
a (possibly indefinite) complex inner product, and Cauchy–Schwarz for it
(**4XV**.1) at the pair `(y⟨y,x⟩, x)` gives
`ω(⟨x,y⟩⟨y,x⟩)² ≤ ω(⟨x,x⟩) ω(⟨x,y⟩⟨y,y⟩⟨y,x⟩)`, whose right factor is at most
`‖⟨y,y⟩‖ ω(⟨x,y⟩⟨y,x⟩)` because `⟨y,y⟩ ≤ ‖⟨y,y⟩‖` (**9X**.2).  The conclusion
follows, "also when `ω(⟨x,y⟩⟨y,x⟩) = 0`". -/
theorem chilb_cs_general {f : X → X → 𝒜} (hf : IsAValuedInner 𝒜 f) (x y : X) :
    f y x * f x y ≤ ‖f y y‖ • f x x := by
  set p := f y x with hp
  set q := f x y with hq
  have hsq : star q = p := hf.star_symm x y
  have hsp : star p = q := hf.star_symm y x
  -- `⟨x,y⟩⟨y,x⟩ = q* q` is positive, and `⟨x, y⟨y,x⟩⟩ = ⟨x,y⟩⟨y,x⟩`
  have hpq0 : (0 : 𝒜) ≤ p * q := by rw [← hsq]; exact star_mul_self_nonneg q
  set z : X := p • y with hz
  have hzx : f z x = p * q := by
    rw [← hf.star_symm x z, hz, hf.smul_right, ← hq, star_mul, hsp, hsq]
  have hzy : f z y = f y y * q := by
    rw [← hf.star_symm y z, hz, hf.smul_right, star_mul, hsp,
      (IsSelfAdjoint.of_nonneg (hf.self_nonneg y)).star_eq]
  have hzz : f z z = p * f y y * q := by
    rw [hz, hf.smul_right, ← hz, hzy, ← mul_assoc]
  -- `⟨z,z⟩ = ⟨x,y⟩⟨y,y⟩⟨y,x⟩ ≤ ‖⟨y,y⟩‖ ⟨x,y⟩⟨y,x⟩`, since `⟨y,y⟩ ≤ ‖⟨y,y⟩‖`
  have hzzle : f z z ≤ ‖f y y‖ • (p * q) := by
    have h1 : f y y ≤ ‖f y y‖ • (1 : 𝒜) := by
      have h := (cstar_positive_2 (f y y)
        (IsSelfAdjoint.of_nonneg (hf.self_nonneg y))).2.2
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), ← Algebra.algebraMap_eq_smul_one]
      exact h
    have h2 := star_left_conjugate_le_conjugate h1 q
    rw [hsq] at h2
    calc f z z = p * f y y * q := hzz
      _ ≤ p * (‖f y y‖ • (1 : 𝒜)) * q := h2
      _ = ‖f y y‖ • (p * q) := by rw [mul_smul_comm, smul_mul_assoc, mul_one]
  -- the states are order separating (**22VIII**.2), so one state at a time
  rw [← sub_nonneg]
  refine (states_order_separating_2 (𝒜 := 𝒜) _).mpr ?_
  rintro ⟨ω, hω⟩
  show (0 : ℂ) ≤ ω (‖f y y‖ • f x x - p * q)
  have hmono : ∀ a b : 𝒜, a ≤ b → ω a ≤ ω b := by
    intro a b hab
    have h := hω.1 _ (sub_nonneg.mpr hab)
    rw [map_sub] at h
    exact sub_nonneg.mp h
  have hsmul : ∀ (r : ℝ) (a : 𝒜), ω (r • a) = (r : ℂ) * ω a := by
    intro r a
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, smul_eq_mul]
    rfl
  have hT : (0 : ℂ) ≤ ω (p * q) := hω.1 _ hpq0
  have hS : (0 : ℂ) ≤ ω (f x x) := hω.1 _ (hf.self_nonneg x)
  set T : ℝ := RCLike.re (ω (p * q)) with hTdef
  set S : ℝ := RCLike.re (ω (f x x)) with hSdef
  have hT0 : 0 ≤ T := (Complex.le_def.mp hT).1
  have hS0 : 0 ≤ S := (Complex.le_def.mp hS).1
  have hTim : (ω (p * q)).im = 0 := ((Complex.le_def.mp hT).2).symm
  have hSim : (ω (f x x)).im = 0 := ((Complex.le_def.mp hS).2).symm
  have hTnorm : ‖ω (p * q)‖ = T := by
    rw [hTdef]
    conv_rhs => rw [Complex.eq_coe_norm_of_nonneg hT]
    simp
  -- Cauchy–Schwarz for `ω(⟨·,·⟩)` (**4XV**.1) at `(y⟨y,x⟩, x)`
  have hcs := state_cs hf ω hω z x
  rw [hzx, hTnorm] at hcs
  have hzzω : RCLike.re (ω (f z z)) ≤ ‖f y y‖ * T := by
    have h := hmono _ _ hzzle
    rw [hsmul] at h
    have h1 := (Complex.le_def.mp h).1
    simpa [hTdef] using h1
  have hM0 : (0 : ℝ) ≤ ‖f y y‖ := norm_nonneg _
  have hle : T ≤ ‖f y y‖ * S := by
    have hsq : T ^ 2 ≤ (‖f y y‖ * T) * S := le_trans hcs (by nlinarith [hS0])
    rcases eq_or_lt_of_le hT0 with h0 | h0
    · rw [← h0]; positivity
    · nlinarith
  rw [map_sub, hsmul, sub_nonneg]
  refine Complex.le_def.mpr ⟨?_, ?_⟩
  · simpa [hTdef, hSdef, hSim] using hle
  · simp [hTim, hSim]

end AValuedInner

section CauchySchwarz

variable {𝒜 : Type*} {X Y : Type*} [CStarAlgebra 𝒜]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒜 X] [CStarModule 𝒜 X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul 𝒜 Y] [CStarModule 𝒜 Y]

/-- **32VI** (`chilb-cs`, cstar.tex:5096, Proposition (Cauchy–Schwarz)):
`⟨x,y⟩ ⟨y,x⟩ ≤ ‖⟨y,y⟩‖ ⟨x,x⟩`, for the 𝒜-valued inner product of a
`CStarModule` — the case the rest of this file uses.  The Proposition itself,
for *every* 𝒜-valued inner product on an 𝒜-module (definite or not, with no
norm on `X`), is `chilb_cs_general` above, of which this is the immediate
corollary: the fields of `IsAValuedInner` are those of `CStarModule` minus
definiteness and minus the norm.  (**32VII**, Remark: the norm sign cannot be
removed; not converted.)

**Convention.** The thesis uses *right* 𝒜-modules with `⟨x, y·b⟩ = ⟨x,y⟩ b`,
whereas Mathlib's `CStarModule` uses the opposite convention `⟪x, a•y⟫ =
a ⟪x,y⟫`, so that `⟪x,y⟫_Mathlib = ⟨y,x⟩_thesis`.  The Lean statement below is
therefore the thesis's inequality with the arguments swapped.  Stated without
the swap it is *false*: for `𝒜 = M₂(ℂ)`, `X = C⋆ᵐᵒᵈ(𝒜,𝒜)`, `x = e₁₁`,
`y = e₂₁` it would assert `e₂₂ ≤ e₁₁`. -/
theorem chilb_cs (x y : X) :
    inner 𝒜 y x * inner 𝒜 x y ≤ ‖inner 𝒜 y y‖ • inner 𝒜 x x :=
  chilb_cs_general (𝒜 := 𝒜)
    { add_right := fun _ _ _ => CStarModule.inner_add_right
      smul_right := fun _ _ _ => CStarModule.inner_op_smul_right
      smul_right_complex := fun _ _ _ => CStarModule.inner_smul_right_complex
      self_nonneg := fun _ => CStarModule.inner_self_nonneg
      star_symm := fun u v => CStarModule.star_inner u v } x y

/-- **32IX** (`chilb-norm-basic`, cstar.tex:5161, Exercise), part 1, the
defining equation: `‖x‖ = ‖⟨x,x⟩‖^{1/2}` — in Mathlib this is the bundled
norm of the `CStarModule` class
(`CStarModule.norm_eq_sqrt_norm_inner_self`), recorded here.  That this
*defines a norm* — the three axioms the exercise asks one to verify — is
`chilb_norm_basic_1_norm` below. -/
theorem chilb_norm_basic_1 (x : X) :
    ‖x‖ = Real.sqrt ‖inner 𝒜 x x‖ :=
  CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒜) x

/-- **32IX** (`chilb-norm-basic`, cstar.tex:5161, Exercise), part 1: the
quantity `‖x‖ = ‖⟨x,x⟩‖^{1/2}` really *is* a norm — definiteness,
ℂ-homogeneity and the triangle inequality, the three clauses spelled out in
solution `parsec-320.90`(1).

Each is read off Mathlib's `CStarModule.normedSpaceCore`, which derives them
from the inner-product axioms alone (its `norm_triangle` field is proved from
Cauchy–Schwarz **32VI**, as the solution's is); they are *not* taken from the
ambient `NormedAddCommGroup X` instance. -/
theorem chilb_norm_basic_1_norm :
    (∀ x : X, Real.sqrt ‖inner 𝒜 x x‖ = 0 ↔ x = 0) ∧
      (∀ (c : ℂ) (x : X), Real.sqrt ‖inner 𝒜 (c • x) (c • x)‖
        = ‖c‖ * Real.sqrt ‖inner 𝒜 x x‖) ∧
      (∀ x y : X, Real.sqrt ‖inner 𝒜 (x + y) (x + y)‖
        ≤ Real.sqrt ‖inner 𝒜 x x‖ + Real.sqrt ‖inner 𝒜 y y‖) := by
  simp only [← CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒜)]
  exact ⟨(CStarModule.normedSpaceCore (A := 𝒜) (E := X)).norm_eq_zero_iff,
    (CStarModule.normedSpaceCore (A := 𝒜) (E := X)).norm_smul,
    CStarModule.norm_triangle 𝒜⟩

/-- **32IX** (`chilb-norm-basic`, cstar.tex:5161, Exercise), part 2:
`‖x·b‖ ≤ ‖x‖ ‖b‖` (here in left-action notation `b • x`) and
`‖⟨x,y⟩‖ ≤ ‖x‖ ‖y‖`.

Both clauses run solution `parsec-320.90`(2).  The second is the solution's
Cauchy–Schwarz argument: `‖⟨x,y⟩‖² = ‖⟨x,y⟩⟨y,x⟩‖ ≤ ‖ ‖⟨y,y⟩‖ ⟨x,x⟩ ‖ =
‖y‖²‖x‖²`, the middle step by **32VI** `chilb_cs` and `positive-basic-2`
(`CStarAlgebra.norm_le_norm_of_nonneg_of_le`).  It is *not* handed to
`CStarModule.norm_inner_le`, which would close it without using **32VI** at
all — and **32VI** has no other consumer in parsec 320. -/
theorem chilb_norm_basic_2 (x y : X) (b : 𝒜) :
    ‖b • x‖ ≤ ‖x‖ * ‖b‖ ∧ ‖inner 𝒜 x y‖ ≤ ‖x‖ * ‖y‖ := by
  refine ⟨?_, ?_⟩
  · have h : inner 𝒜 (b • x) (b • x) = b * inner 𝒜 x x * star b := by
      rw [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right]
    have hb : ‖b * inner 𝒜 x x * star b‖ ≤ (‖x‖ * ‖b‖) ^ 2 := by
      refine (norm_mul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
      rw [norm_star, ← CStarModule.norm_sq_eq (A := 𝒜) (x := x)]
      ring_nf
      exact le_rfl
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒜) (b • x), h]
    calc Real.sqrt ‖b * inner 𝒜 x x * star b‖
        ≤ Real.sqrt ((‖x‖ * ‖b‖) ^ 2) := Real.sqrt_le_sqrt hb
      _ = ‖x‖ * ‖b‖ := Real.sqrt_sq (by positivity)
  · -- Cauchy–Schwarz (**32VI**): `⟨x,y⟩⟨y,x⟩ ≤ ‖⟨y,y⟩‖ ⟨x,x⟩`
    have hcs := chilb_cs (𝒜 := 𝒜) x y
    have hnn : (0 : 𝒜) ≤ inner 𝒜 y x * inner 𝒜 x y := by
      rw [← CStarModule.star_inner (A := 𝒜) x y]
      exact star_mul_self_nonneg _
    have h1 : ‖inner 𝒜 x y‖ ^ 2 = ‖inner 𝒜 y x * inner 𝒜 x y‖ := by
      rw [← CStarModule.star_inner (A := 𝒜) x y, CStarRing.norm_star_mul_self, sq]
    have h2 : ‖inner 𝒜 y x * inner 𝒜 x y‖ ≤ ‖(‖inner 𝒜 y y‖ • inner 𝒜 x x : 𝒜)‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le hnn hcs
    have h3 : ‖(‖inner 𝒜 y y‖ • inner 𝒜 x x : 𝒜)‖ = ‖y‖ ^ 2 * ‖x‖ ^ 2 := by
      rw [norm_smul, ← CStarModule.norm_sq_eq (A := 𝒜) (x := x),
        ← CStarModule.norm_sq_eq (A := 𝒜) (x := y)]
      simp
    nlinarith [norm_nonneg (inner 𝒜 x y : 𝒜), norm_nonneg x, norm_nonneg y,
      mul_nonneg (norm_nonneg x) (norm_nonneg y)]

/-- The nontrivial half of **32X**: a bound on the sesquilinear form bounds
the map. -/
private theorem norm_le_of_inner_bound {T : X → Y} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ (x : X) (y : Y), ‖inner 𝒜 y (T x)‖ ≤ B * ‖y‖ * ‖x‖) (x : X) :
    ‖T x‖ ≤ B * ‖x‖ := by
  have h1 := h x (T x)
  rw [← CStarModule.norm_sq_eq (A := 𝒜) (x := T x)] at h1
  rcases eq_or_lt_of_le (norm_nonneg (T x)) with h0 | h0
  · rw [← h0]
    exact mul_nonneg hB (norm_nonneg x)
  · nlinarith [norm_nonneg x]

/-- **32X** (`chilb-form-bounded`, cstar.tex:5178, Lemma): for a linear map
`T : X → Y` between pre-Hilbert 𝒜-modules and `B > 0`: `T` is bounded by
`B` iff `‖⟨y, Tx⟩‖ ≤ B ‖y‖ ‖x‖` for all `x, y`. -/
theorem chilb_form_bounded (T : X →ₗ[ℂ] Y) (B : ℝ) (hB : 0 < B) :
    (∀ x : X, ‖T x‖ ≤ B * ‖x‖) ↔
      ∀ (x : X) (y : Y), ‖inner 𝒜 y (T x)‖ ≤ B * ‖y‖ * ‖x‖ := by
  refine ⟨fun h x y => ?_, fun h => norm_le_of_inner_bound hB.le h⟩
  calc ‖inner 𝒜 y (T x)‖ ≤ ‖y‖ * ‖T x‖ := (chilb_norm_basic_2 _ _ 0).2
    _ ≤ ‖y‖ * (B * ‖x‖) := by gcongr; exact h x
    _ = B * ‖y‖ * ‖x‖ := by ring

private theorem norm_adjoint_le (T : X →L[ℂ] Y) (S : Y →L[ℂ] X)
    (h : ModuleAdjointTo 𝒜 ⇑T ⇑S) : ‖S‖ ≤ ‖T‖ := by
  refine S.opNorm_le_bound (norm_nonneg T) fun y => ?_
  refine norm_le_of_inner_bound (𝒜 := 𝒜) (T := ⇑S) (norm_nonneg T)
    (fun y' x' => ?_) y
  rw [← h x' y']
  calc ‖inner 𝒜 (T x') y'‖ ≤ ‖T x'‖ * ‖y'‖ := (chilb_norm_basic_2 _ _ 0).2
    _ ≤ ‖T‖ * ‖x'‖ * ‖y'‖ :=
        mul_le_mul_of_nonneg_right (T.le_opNorm x') (norm_nonneg y')

/-- **32X** (`chilb-form-bounded`, cstar.tex:5178, Lemma), second part: for
an adjointable bounded map, `‖T*‖ = ‖T‖`. -/
theorem chilb_form_bounded_adjoint (T : X →L[ℂ] Y) (S : Y →L[ℂ] X)
    (h : ModuleAdjointTo 𝒜 ⇑T ⇑S) : ‖S‖ = ‖T‖ :=
  le_antisymm (norm_adjoint_le T S h)
    (norm_adjoint_le S T (moduleAdjointTo_symm T S h))

/-- **32X** (`chilb-form-bounded`, cstar.tex:5178, Lemma), the "moreover" the
Lemma itself draws: if `T : X → Y` is a bounded module map and `S : Y → X` is
merely a *map* adjoint to it, then `S` is automatically bounded — it is a
continuous linear map — and `‖T*‖ = ‖T‖`.

`chilb_form_bounded_adjoint` above assumes the adjoint is already continuous
and proves only the norm equality; this is the Lemma's own statement, in which
boundedness of `T*` is a conclusion.

*Class 1 — faithful.*  The thesis's argument: `‖⟨x, T*y⟩‖ = ‖⟨Tx, y⟩‖ ≤
‖T‖‖x‖‖y‖`, so the first part of **32X** bounds `T*` by `‖T‖`; linearity of
`T*` is definiteness of the inner product, as in **32I**. -/
theorem exists_clm_adjointTo_norm {T : X →L[ℂ] Y} {S : Y → X}
    (h : ModuleAdjointTo 𝒜 ⇑T S) :
    ∃ S' : Y →L[ℂ] X, (∀ y : Y, S' y = S y) ∧ ‖S'‖ = ‖T‖ := by
  have h' : ∀ (x : X) (y : Y), inner 𝒜 (T x) y = inner 𝒜 x (S y) := h
  have hbound : ∀ (y : Y) (x : X), ‖inner 𝒜 x (S y)‖ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
    intro y x
    rw [← h' x y]
    calc ‖inner 𝒜 (T x) y‖ ≤ ‖T x‖ * ‖y‖ := (chilb_norm_basic_2 _ _ 0).2
      _ ≤ ‖T‖ * ‖x‖ * ‖y‖ :=
          mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg y)
  have hnorm : ∀ y : Y, ‖S y‖ ≤ ‖T‖ * ‖y‖ :=
    fun y => norm_le_of_inner_bound (𝒜 := 𝒜) (X := Y) (Y := X) (norm_nonneg T) hbound y
  have hadd : ∀ y z : Y, S (y + z) = S y + S z := fun y z =>
    eq_of_inner_right_eq (𝒜 := 𝒜) fun x => by
      simp only [← h', CStarModule.inner_add_right]
  have hsmul : ∀ (c : ℂ) (y : Y), S (c • y) = c • S y := fun c y =>
    eq_of_inner_right_eq (𝒜 := 𝒜) fun x => by
      simp only [← h', CStarModule.inner_smul_right_complex]
  refine ⟨LinearMap.mkContinuous
    { toFun := S, map_add' := hadd, map_smul' := fun c y => hsmul c y } ‖T‖ hnorm,
    fun _ => rfl, chilb_form_bounded_adjoint T _ h⟩

/-- **32XII** (`module-maps-cstar-identity`, cstar.tex:5220, Exercise):
`‖T* T‖ = ‖T‖²` for every adjointable bounded map `T` on a pre-Hilbert
𝒜-module. -/
theorem module_maps_cstar_identity (T S : X →L[ℂ] X)
    (h : ModuleAdjointTo 𝒜 ⇑T ⇑S) : ‖S.comp T‖ = ‖T‖ ^ 2 := by
  have hS : ‖S‖ = ‖T‖ := chilb_form_bounded_adjoint T S h
  refine le_antisymm ?_ ?_
  · calc ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ := S.opNorm_comp_le T
      _ = ‖T‖ ^ 2 := by rw [hS]; ring
  · have key : ∀ x : X, ‖T x‖ ≤ Real.sqrt ‖S.comp T‖ * ‖x‖ := by
      intro x
      have h1 : ‖T x‖ ^ 2 ≤ ‖S.comp T‖ * ‖x‖ ^ 2 := by
        rw [CStarModule.norm_sq_eq (A := 𝒜) (x := T x), h x (T x)]
        calc ‖inner 𝒜 x (S (T x))‖ ≤ ‖x‖ * ‖S (T x)‖ := (chilb_norm_basic_2 _ _ 0).2
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

/-- A map adjoint to a bounded module map is automatically linear and bounded
(by **32X**), so it may be taken to be a continuous linear map. -/
theorem exists_clm_adjointTo {T : X →L[ℂ] X} {S : X → X}
    (h : ModuleAdjointTo 𝒜 ⇑T S) : ∃ S' : X →L[ℂ] X, ModuleAdjointTo 𝒜 ⇑T ⇑S' := by
  have h' : ∀ x y : X, inner 𝒜 (T x) y = inner 𝒜 x (S y) := h
  have hbound : ∀ y x : X, ‖inner 𝒜 x (S y)‖ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
    intro y x
    rw [← h x y]
    calc ‖inner 𝒜 (T x) y‖ ≤ ‖T x‖ * ‖y‖ := (chilb_norm_basic_2 _ _ 0).2
      _ ≤ ‖T‖ * ‖x‖ * ‖y‖ :=
          mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg y)
  have hnorm : ∀ y, ‖S y‖ ≤ ‖T‖ * ‖y‖ :=
    fun y => norm_le_of_inner_bound (norm_nonneg T) hbound y
  have hadd : ∀ y z, S (y + z) = S y + S z := fun y z =>
    eq_of_inner_right_eq (𝒜 := 𝒜) fun x => by
      simp only [← h', CStarModule.inner_add_right]
  have hsmul : ∀ (c : ℂ) (y), S (c • y) = c • S y := fun c y =>
    eq_of_inner_right_eq (𝒜 := 𝒜) fun x => by
      simp only [← h', CStarModule.inner_smul_right_complex]
  exact ⟨LinearMap.mkContinuous
    { toFun := S, map_add' := hadd, map_smul' := fun c y => hsmul c y } ‖T‖ hnorm, h⟩

/-- **32XIII** (`bax-cstar`, cstar.tex:5225, Proposition): the adjointable
bounded module maps on a Hilbert 𝒜-module `X` form a C*-algebra `B^a(X)`.
The missing ingredient beyond **4VII** and **32XII** is that `B^a(X)` is
closed in the bounded operators on `X`, which is stated here. -/
theorem bax_cstar [CompleteSpace X] :
    IsClosed {T : X →L[ℂ] X | ModuleAdjointable 𝒜 ⇑T} := by
  refine IsSeqClosed.isClosed fun Tn T hmem hlim => ?_
  have hadj : ∀ n, ∃ S : X →L[ℂ] X, ModuleAdjointTo 𝒜 ⇑(Tn n) ⇑S := fun n => by
    obtain ⟨S, hS⟩ := hmem n
    exact exists_clm_adjointTo hS
  choose Sn hSn using hadj
  have hSn' : ∀ (n : ℕ) (x y : X), inner 𝒜 (Tn n x) y = inner 𝒜 x (Sn n y) := hSn
  -- `‖S_m - S_n‖ = ‖T_m - T_n‖` by **32X**, so `(S_n)` is Cauchy
  have hdiff : ∀ m n, ‖Sn m - Sn n‖ = ‖Tn m - Tn n‖ := fun m n =>
    chilb_form_bounded_adjoint (𝒜 := 𝒜) (Tn m - Tn n) (Sn m - Sn n) fun x y => by
      simp only [sub_apply, CStarModule.inner_sub_left,
        CStarModule.inner_sub_right, hSn']
  have hcauchy : CauchySeq Sn := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq ε hε
    exact ⟨N, fun m hm n hn => by
      simpa only [dist_eq_norm, hdiff] using hN m hm n hn⟩
  obtain ⟨S, hS⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨⇑S, fun x y => ?_⟩
  have hb : ∀ n : ℕ, ‖inner 𝒜 (T x) y - inner 𝒜 x (S y)‖
      ≤ ‖T - Tn n‖ * ‖x‖ * ‖y‖ + ‖x‖ * (‖Sn n - S‖ * ‖y‖) := by
    intro n
    have e : inner 𝒜 (T x) y - inner 𝒜 x (S y)
        = inner 𝒜 ((T - Tn n) x) y + inner 𝒜 x ((Sn n - S) y) := by
      simp only [sub_apply, CStarModule.inner_sub_left,
        CStarModule.inner_sub_right, hSn' n x y]
      abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · calc ‖inner 𝒜 ((T - Tn n) x) y‖ ≤ ‖(T - Tn n) x‖ * ‖y‖ := (chilb_norm_basic_2 _ _ 0).2
        _ ≤ ‖T - Tn n‖ * ‖x‖ * ‖y‖ := by
            gcongr
            exact (T - Tn n).le_opNorm x
    · calc ‖inner 𝒜 x ((Sn n - S) y)‖ ≤ ‖x‖ * ‖(Sn n - S) y‖ := (chilb_norm_basic_2 _ _ 0).2
        _ ≤ ‖x‖ * (‖Sn n - S‖ * ‖y‖) := by
            gcongr
            exact (Sn n - S).le_opNorm y
  have hcT : Filter.Tendsto (fun _ : ℕ => T) Filter.atTop (nhds T) := tendsto_const_nhds
  have hcS : Filter.Tendsto (fun _ : ℕ => S) Filter.atTop (nhds S) := tendsto_const_nhds
  have h1 : Filter.Tendsto (fun n => ‖T - Tn n‖) Filter.atTop (nhds 0) := by
    simpa using (hcT.sub hlim).norm
  have h2 : Filter.Tendsto (fun n => ‖Sn n - S‖) Filter.atTop (nhds 0) := by
    simpa using (hS.sub hcS).norm
  have h0 : Filter.Tendsto
      (fun n => ‖T - Tn n‖ * ‖x‖ * ‖y‖ + ‖x‖ * (‖Sn n - S‖ * ‖y‖))
      Filter.atTop (nhds 0) := by
    simpa using ((h1.mul tendsto_const_nhds).mul tendsto_const_nhds).add
      (tendsto_const_nhds.mul (h2.mul tendsto_const_nhds))
  have hle := le_of_tendsto_of_tendsto' tendsto_const_nhds h0 hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))

/-- **32XV** (`chilb-vector-states-order-separating`, cstar.tex:5375,
Exercise), part 1 — the vector functionals `⟨x, (·) x⟩` on `B^a(X)` are
order separating; consequently, for an adjointable operator `T` with adjoint
`S`: `T` is self-adjoint (`T = T*`) iff `⟨x, Tx⟩` is self-adjoint for all
`x` in the unit ball. -/
theorem chilb_vector_states_1 [CompleteSpace X] (T S : X →L[ℂ] X)
    (h : ModuleAdjointTo 𝒜 ⇑T ⇑S) :
    T = S ↔ ∀ x : X, ‖x‖ ≤ 1 → IsSelfAdjoint (inner 𝒜 x (T x)) := by
  constructor
  · rintro rfl x -
    change star (inner 𝒜 x (T x)) = inner 𝒜 x (T x)
    rw [CStarModule.star_inner]
    exact h x x
  · intro hx
    set U : X →L[ℂ] X := T - S with hU
    have key : ∀ w : X, ‖w‖ ≤ 1 → inner 𝒜 w (U w) = (0 : 𝒜) := by
      intro w hw
      have h1 := (hx w hw).star_eq
      rw [CStarModule.star_inner, h w w] at h1
      simp [hU, CStarModule.inner_sub_right, h1]
    have hQ : ∀ z : X, inner 𝒜 z (U z) = (0 : 𝒜) := by
      intro z
      rcases eq_or_ne z 0 with rfl | hz
      · simp
      · have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
        set c : ℂ := ((‖z‖⁻¹ : ℝ) : ℂ) with hc
        have hcn : ‖c‖ = ‖z‖⁻¹ := by
          rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hnorm : ‖c • z‖ ≤ 1 := by
          rw [(CStarModule.normedSpaceCore 𝒜 (E := X)).norm_smul c z, hcn,
            inv_mul_cancel₀ hzn]
        have hk := key _ hnorm
        rw [map_smul, CStarModule.inner_smul_right_complex,
          CStarModule.inner_smul_left_complex, smul_smul] at hk
        have hne : c * star c ≠ 0 := by
          rw [hc]
          simp [Complex.ext_iff, hzn]
        rcases smul_eq_zero.mp hk with h4 | h4
        · exact absurd h4 hne
        · exact h4
    have hB : ∀ x y : X, inner 𝒜 x (U y) = (0 : 𝒜) := by
      intro x y
      have e1 : inner 𝒜 y (U x) + inner 𝒜 x (U y) = (0 : 𝒜) := by
        have := hQ (x + y)
        simpa [map_add, hQ x, hQ y] using this
      have e2 : -(Complex.I • (inner 𝒜 y (U x) : 𝒜))
          + Complex.I • (inner 𝒜 x (U y) : 𝒜) = 0 := by
        have := hQ (x + Complex.I • y)
        simpa [map_add, hQ x, hQ y, smul_smul] using this
      have hyx : (inner 𝒜 y (U x) : 𝒜) = -inner 𝒜 x (U y) := by
        rw [eq_neg_iff_add_eq_zero]; exact e1
      rw [hyx, smul_neg, neg_neg, ← add_smul] at e2
      rcases smul_eq_zero.mp e2 with h4 | h4
      · exact absurd h4 (by norm_num [Complex.ext_iff])
      · exact h4
    have hzero : ∀ y : X, U y = 0 := fun y => CStarModule.inner_self.mp (hB (U y) y)
    ext y
    have hy := hzero y
    rw [hU] at hy
    simpa [sub_eq_zero] using hy

/-! ### `B^a(X)` as a C*-algebra

**32XIII** (`bax_cstar`) shows that the adjointable bounded module maps form a
*closed* subalgebra of the bounded operators on `X`; combined with **32III**
(the adjoint is an involution, and behaves well under sums, scalars and
composites) and **32XII** (the C*-identity) that makes `B^a(X)` a C*-algebra.
The block below packages exactly that: the subalgebra `Bax 𝒜 X` of `X →L[ℂ] X`
carrying a `CStarAlgebra` structure whose involution is `T ↦ T*`, together with
its spectral order.  It is the setting in which the proofs of **32XV**.2 and
**32XV**.3 run. -/

section Bax

variable (𝒜 X) in
/-- `B^a(X)`: the adjointable bounded module maps on `X`, as a subalgebra of
`X →L[ℂ] X` (**32XIII**). -/
private def Bax : Subalgebra ℂ (X →L[ℂ] X) where
  carrier := {T | ModuleAdjointable 𝒜 ⇑T}
  mul_mem' := by
    rintro T S ⟨T', hT⟩ ⟨S', hS⟩
    exact ⟨S' ∘ T', moduleAdjointTo_comp (⇑S) (⇑T) S' T' hS hT⟩
  one_mem' := ⟨id, fun _ _ => rfl⟩
  add_mem' := by
    rintro T S ⟨T', hT⟩ ⟨S', hS⟩
    exact ⟨fun y => T' y + S' y, (moduleAdjointTo_add_smul _ _ _ _ 0 hT hS).1⟩
  zero_mem' := ⟨fun _ => 0, fun _ _ => by simp⟩
  algebraMap_mem' c := ⟨fun y => star c • y, fun x y => by
    simp only [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.one_apply,
      CStarModule.inner_smul_left_complex, CStarModule.inner_smul_right_complex]⟩

private theorem bax_norm_coe (T : Bax 𝒜 X) : ‖T‖ = ‖(T : X →L[ℂ] X)‖ := rfl

private theorem bax_exists_adjoint (T : Bax 𝒜 X) :
    ∃ S : X →L[ℂ] X, ModuleAdjointTo 𝒜 ⇑(T : X →L[ℂ] X) ⇑S := by
  obtain ⟨S, hS⟩ := T.2
  exact exists_clm_adjointTo hS

private noncomputable instance : Star (Bax 𝒜 X) where
  star T := ⟨Classical.choose (bax_exists_adjoint T),
    ⟨_, moduleAdjointTo_symm _ _ (Classical.choose_spec (bax_exists_adjoint T))⟩⟩

/-- The involution of `Bax 𝒜 X` is the adjoint. -/
private theorem bax_star_spec (T : Bax 𝒜 X) :
    ModuleAdjointTo 𝒜 ⇑(T : X →L[ℂ] X) ⇑((star T : Bax 𝒜 X) : X →L[ℂ] X) :=
  Classical.choose_spec (bax_exists_adjoint T)

private theorem bax_star_eq {T S : Bax 𝒜 X}
    (h : ModuleAdjointTo 𝒜 ⇑(T : X →L[ℂ] X) ⇑(S : X →L[ℂ] X)) : star T = S :=
  Subtype.ext (DFunLike.coe_injective
    (moduleAdjointTo_unique _ _ _ (bax_star_spec T) h))

private noncomputable instance : StarRing (Bax 𝒜 X) where
  star_involutive T := bax_star_eq (moduleAdjointTo_symm _ _ (bax_star_spec T))
  star_mul T S := bax_star_eq (moduleAdjointTo_comp (⇑(S : X →L[ℂ] X)) (⇑(T : X →L[ℂ] X))
    (⇑((star S : Bax 𝒜 X) : X →L[ℂ] X)) (⇑((star T : Bax 𝒜 X) : X →L[ℂ] X))
    (bax_star_spec S) (bax_star_spec T))
  star_add T S :=
    bax_star_eq (moduleAdjointTo_add_smul _ _ _ _ 0 (bax_star_spec T) (bax_star_spec S)).1

private instance : StarModule ℂ (Bax 𝒜 X) where
  star_smul c T :=
    bax_star_eq (moduleAdjointTo_add_smul _ _ _ _ c (bax_star_spec T) (bax_star_spec T)).2

private instance : CStarRing (Bax 𝒜 X) where
  norm_mul_self_le T := by
    have h : ‖(star T * T : Bax 𝒜 X)‖ = ‖T‖ ^ 2 :=
      module_maps_cstar_identity (𝒜 := 𝒜) (T : X →L[ℂ] X)
        ((star T : Bax 𝒜 X) : X →L[ℂ] X) (bax_star_spec T)
    rw [h, sq]

private instance [CompleteSpace X] : CompleteSpace (Bax 𝒜 X) :=
  (bax_cstar (𝒜 := 𝒜) (X := X)).completeSpace_coe

private noncomputable instance [CompleteSpace X] : CStarAlgebra (Bax 𝒜 X) where

/-- **32XIII** (`bax-cstar`, cstar.tex:5210, Proposition): `𝓑^a(X)` *is* a
C*-algebra, for `X` a Hilbert 𝒜-module.  `bax_cstar` above is the single
ingredient the thesis's proof (**32XIV**) has to supply — closedness in
`X →L[ℂ] X`; the involution is the adjoint (**32III**) and the C*-identity is
**32XII**, and the instances just above assemble them.  (Same rendering as
**33I**.4 for `M_N(𝒜)`.) -/
noncomputable example [CompleteSpace X] : CStarAlgebra (Bax 𝒜 X) := inferInstance

private noncomputable instance [CompleteSpace X] : PartialOrder (Bax 𝒜 X) :=
  CStarAlgebra.spectralOrder _

private instance [CompleteSpace X] : StarOrderedRing (Bax 𝒜 X) :=
  CStarAlgebra.spectralOrderedRing _


/-- `⟨x, (S* U S) x⟩ = ⟨Sx, U (Sx)⟩` in `B^a(X)`. -/
private theorem bax_inner_conj (S U : Bax 𝒜 X) (x : X) :
    inner 𝒜 x (((star S * U * S : Bax 𝒜 X) : X →L[ℂ] X) x)
      = inner 𝒜 ((S : X →L[ℂ] X) x) ((U : X →L[ℂ] X) ((S : X →L[ℂ] X) x)) :=
  (bax_star_spec S x _).symm

/-- `⟨x, (S* S) x⟩ = ⟨Sx, Sx⟩` in `B^a(X)`. -/
private theorem bax_inner_star_mul (S : Bax 𝒜 X) (x : X) :
    inner 𝒜 x (((star S * S : Bax 𝒜 X) : X →L[ℂ] X) x)
      = inner 𝒜 ((S : X →L[ℂ] X) x) ((S : X →L[ℂ] X) x) :=
  (bax_star_spec S x _).symm

/-- One half of **32XV**.2 inside `B^a(X)`: a positive operator has positive
vector functionals. -/
private theorem bax_inner_nonneg [CompleteSpace X] {U : Bax 𝒜 X} (hU : 0 ≤ U) (x : X) :
    0 ≤ inner 𝒜 x ((U : X →L[ℂ] X) x) := by
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hU
  rw [hR, bax_inner_star_mul]
  exact CStarModule.inner_self_nonneg

/-- `a⁻ a a⁻ = -(a⁻)³` for self-adjoint `a` (the negative part absorbs the
positive part).  The first half of the negative-part argument of **32XV**.2. -/
private theorem negPart_conj_aux {M : Type*} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] {a : M} (hsa : IsSelfAdjoint a) :
    a⁻ * a * a⁻ = -(a⁻ * a⁻ * a⁻) := by
  conv_lhs => arg 1; arg 2; rw [← CFC.posPart_sub_negPart a hsa]
  rw [mul_sub, sub_mul, CFC.negPart_mul_posPart, zero_mul, zero_sub]

/-- A self-adjoint element whose negative part cubes to zero is positive.  The
second half of the negative-part argument of **32XV**.2. -/
private theorem nonneg_of_negPart_cube {M : Type*} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] {a : M} (hsa : IsSelfAdjoint a) (h3 : a⁻ * a⁻ * a⁻ = 0) :
    0 ≤ a := by
  have hsab : IsSelfAdjoint (a⁻) := (CFC.negPart_nonneg a).isSelfAdjoint
  have h4 : star (a⁻ * a⁻) * (a⁻ * a⁻) = 0 := by
    rw [star_mul, hsab.star_eq]
    calc a⁻ * a⁻ * (a⁻ * a⁻) = a⁻ * (a⁻ * a⁻ * a⁻) := by noncomm_ring
      _ = 0 := by rw [h3, mul_zero]
  have hbb : a⁻ * a⁻ = 0 := CStarRing.star_mul_self_eq_zero_iff _ |>.mp h4
  have hb : a⁻ = 0 := by
    refine CStarRing.star_mul_self_eq_zero_iff _ |>.mp ?_
    rw [hsab.star_eq, hbb]
  exact CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero.mpr ⟨hsa, hb⟩

end Bax

/-- **32XV** (`chilb-vector-states-order-separating`, cstar.tex:5375,
Exercise), part 2: `0 ≤ T` in `B^a(X)` — i.e. `T = R* R` for some
adjointable bounded `R` — iff `0 ≤ ⟨x, Tx⟩` for all `x`. -/
theorem chilb_vector_states_2 [CompleteSpace X] (T : X →L[ℂ] X)
    (hT : ModuleAdjointable 𝒜 ⇑T) :
    (∀ x : X, 0 ≤ inner 𝒜 x (T x)) ↔
      ∃ R R' : X →L[ℂ] X, ModuleAdjointTo 𝒜 ⇑R ⇑R' ∧ T = R'.comp R := by
  constructor
  · intro hpos
    let a : Bax 𝒜 X := ⟨T, hT⟩
    -- `T` is self-adjoint by part 1
    have hsa : IsSelfAdjoint a :=
      Subtype.ext ((chilb_vector_states_1 (𝒜 := 𝒜) T _ (bax_star_spec a)).mpr
        fun x _ => (hpos x).isSelfAdjoint).symm
    -- write the negative part of `a` as `N = u²` and put `v = u³`, so that
    -- `N³ = v* v`
    have hNn : (0 : Bax 𝒜 X) ≤ a⁻ := CFC.negPart_nonneg a
    have hNsa : star (a⁻ : Bax 𝒜 X) = a⁻ := hNn.isSelfAdjoint.star_eq
    obtain ⟨u, hunn, huu⟩ : ∃ u : Bax 𝒜 X, 0 ≤ u ∧ u * u = a⁻ :=
      ⟨CFC.sqrt _, CFC.sqrt_nonneg _, CFC.sqrt_mul_sqrt_self _ hNn⟩
    have husa : star u = u := hunn.isSelfAdjoint.star_eq
    obtain ⟨v, hvsa, hv⟩ : ∃ v : Bax 𝒜 X, star v = v ∧
        star v * v = (a⁻ : Bax 𝒜 X) * a⁻ * a⁻ := by
      have h1 : star (u * u * u) = u * u * u := by
        simp only [star_mul, husa]; noncomm_ring
      exact ⟨u * u * u, h1, by rw [h1, ← huu]; noncomm_ring⟩
    -- `⟨x, (N a N) x⟩ = ⟨Nx, a (Nx)⟩ ≥ 0`, while `N a N = -N³ = -(v* v)`
    have hvzero : ∀ x : X, (v : X →L[ℂ] X) x = 0 := by
      intro x
      have h1 : (0 : 𝒜) ≤ inner 𝒜 x ((((a⁻ : Bax 𝒜 X) * a * a⁻ : Bax 𝒜 X) : X →L[ℂ] X) x) := by
        rw [show ((a⁻ : Bax 𝒜 X) * a * a⁻ : Bax 𝒜 X) = star (a⁻ : Bax 𝒜 X) * a * a⁻ by
          rw [hNsa], bax_inner_conj]
        exact hpos _
      rw [negPart_conj_aux hsa, ← hv] at h1
      have h2 : inner 𝒜 ((v : X →L[ℂ] X) x) ((v : X →L[ℂ] X) x) ≤ (0 : 𝒜) := by
        rw [← bax_inner_star_mul v x]
        simpa using h1
      exact CStarModule.inner_self.mp
        (le_antisymm h2 CStarModule.inner_self_nonneg)
    have hcube : (a⁻ : Bax 𝒜 X) * a⁻ * a⁻ = 0 := by
      have hv0 : v = 0 := Subtype.ext (ContinuousLinearMap.ext hvzero)
      rw [← hv, hv0, star_zero, mul_zero]
    obtain ⟨R, hR⟩ :=
      CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (nonneg_of_negPart_cube hsa hcube)
    exact ⟨(R : X →L[ℂ] X), ((star R : Bax 𝒜 X) : X →L[ℂ] X), bax_star_spec R,
      congrArg (fun z : Bax 𝒜 X => (z : X →L[ℂ] X)) hR⟩
  · rintro ⟨R, R', h, rfl⟩ x
    rw [ContinuousLinearMap.coe_comp, Function.comp_apply, ← h x (R x)]
    exact CStarModule.inner_self_nonneg

/-- Solution `parsec-320.150`(3)'s own lemma: "`ab = 0 ⟹ a√b = 0` for all
self-adjoint `a` and positive `b` from a C*-algebra `𝒜`, because
`‖a√b‖² = ‖aba‖ = 0` when `ab = 0`".  It is what carries `T∓ T± = 0` to
`T∓ T±^ε = 0` for the dyadic exponents `ε`. -/
private theorem mul_sqrt_eq_zero_of_mul_eq_zero {M : Type*} [CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] {x y : M} (hx : IsSelfAdjoint x)
    (hy : 0 ≤ y) (h : x * y = 0) : x * CFC.sqrt y = 0 := by
  have hs : star (CFC.sqrt y) = CFC.sqrt y := (CFC.sqrt_nonneg y).isSelfAdjoint.star_eq
  have hxy : (x * CFC.sqrt y) * star (x * CFC.sqrt y) = 0 := by
    rw [star_mul, hs, hx.star_eq]
    calc x * CFC.sqrt y * (CFC.sqrt y * x) = x * (CFC.sqrt y * CFC.sqrt y) * x := by
          noncomm_ring
      _ = x * y * x := by rw [CFC.sqrt_mul_sqrt_self y hy]
      _ = 0 := by rw [h, zero_mul]
  have hn : ‖x * CFC.sqrt y‖ * ‖x * CFC.sqrt y‖ = 0 := by
    rw [← CStarRing.norm_self_mul_star, hxy, norm_zero]
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (x * CFC.sqrt y)])

/-- `0 ≤ c • z` for a nonnegative *real* scalar `c`, written with the `ℂ`-action
that a C*-algebra carries.  (Used only for the "scaling down `T`" step of
**32XV**.3.) -/
private theorem real_smul_nonneg {M : Type*} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] {z : M} (hz : 0 ≤ z) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ (c : ℂ) • z := by
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hz
  refine CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr
    ⟨((Real.sqrt c : ℝ) : ℂ) • b, ?_⟩
  rw [star_smul, smul_mul_smul_comm]
  congr 1
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hc]

set_option maxHeartbeats 800000 in
/-- The heart of **32XV**.3, in the shape solution `parsec-320.150`(3) gives
it, for a *contraction* `a` split as `a = ±(p − q)` with `p, q ≥ 0`, `qp = 0`
(so `p, q` are the positive and negative part, in one order or the other):

  `‖p‖ ≤ sup_{y ∈ (X)_{≤1}} ‖⟨p^ε y, a p^ε y⟩‖`  for every dyadic `ε > 0`.

The solution's chain, step for step.  Only the exponents `ε = 2⁻ⁿ` are used —
they are dyadic and cofinal in `(0,∞)` downwards, which is all the final
supremum needs.  `q p^ε = 0` comes from `q p = 0` by
`mul_sqrt_eq_zero_of_mul_eq_zero`, iterated; hence `a p^ε = ± p p^ε` and
`⟨p^ε y, a p^ε y⟩ = ±⟨√p p^ε y, √p p^ε y⟩`, whose norm is `‖√p p^ε y‖²`; the
vectors `p^ε y` are in the unit ball because `‖p‖ ≤ 1`; so
`‖√p p^ε‖² ≤ M`, and `‖√p p^ε‖² = ‖p^{1+2ε}‖ = ‖p‖^{1+2ε}`.  Letting `ε ↓ 0`
gives `‖p‖ ≤ M`. -/
private theorem norm_le_of_vector_bound [CompleteSpace X] (a p q : Bax 𝒜 X)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hqp : q * p = 0)
    (hpq : a = p - q ∨ a = q - p) (hp1 : ‖p‖ ≤ 1) (M : ℝ)
    (hM : ∀ x : X, ‖x‖ ≤ 1 → ‖inner 𝒜 x ((a : X →L[ℂ] X) x)‖ ≤ M) :
    ‖p‖ ≤ M := by
  have hM0 : 0 ≤ M := by simpa using hM 0 (by simp)
  -- `p^ε` for the dyadic exponents `ε = 2⁻ⁿ`
  set e : ℕ → NNReal := fun n => (1 / 2 : NNReal) ^ n with he
  have hepos : ∀ n, 0 < e n := fun n => by rw [he]; positivity
  set pe : ℕ → Bax 𝒜 X := fun n => p ^ e n with hpe
  have hpen : ∀ n, 0 ≤ pe n := fun _ => CFC.nnrpow_nonneg
  have hpe0 : pe 0 = p := by
    rw [hpe]
    simpa [he] using CFC.nnrpow_one p hp
  have hpesucc : ∀ n, pe (n + 1) = CFC.sqrt (pe n) := by
    intro n
    show p ^ e (n + 1) = CFC.sqrt (p ^ e n)
    rw [CFC.sqrt_nnrpow]
    congr 1
    simp only [he, pow_succ]
    ring
  -- `T∓ T±^ε = 0`
  have hqpe : ∀ n, q * pe n = 0 := by
    intro n
    induction n with
    | zero => rw [hpe0]; exact hqp
    | succ n ih =>
        rw [hpesucc n]
        exact mul_sqrt_eq_zero_of_mul_eq_zero hq.isSelfAdjoint (hpen n) ih
  have hpeq : ∀ n, pe n * q = 0 := by
    intro n
    have h := congrArg star (hqpe n)
    rwa [star_mul, (hpen n).isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
      star_zero] at h
  -- `‖p^ε‖ = ‖p‖^ε ≤ 1`
  have hnormpe : ∀ n, ‖pe n‖ = ‖p‖ ^ ((e n : ℝ)) := fun n =>
    CFC.norm_nnrpow p (hepos n) hp
  have hpe1 : ∀ n, ‖pe n‖ ≤ 1 := by
    intro n
    rw [hnormpe n]
    exact Real.rpow_le_one (norm_nonneg p) hp1 (e n).coe_nonneg
  -- `S n := √p · p^ε`, so that `(S n)* (S n) = p^{1+2ε}`
  set S : ℕ → Bax 𝒜 X := fun n => CFC.sqrt p * pe n with hSdef
  have hSS : ∀ n, star (S n) * S n = p ^ (1 + 2 * e n) := by
    intro n
    have hsq : star (CFC.sqrt p) = CFC.sqrt p := (CFC.sqrt_nonneg p).isSelfAdjoint.star_eq
    rw [hSdef, star_mul, hsq, (hpen n).isSelfAdjoint.star_eq]
    have h1 : pe n * CFC.sqrt p * (CFC.sqrt p * pe n) = pe n * p * pe n := by
      calc pe n * CFC.sqrt p * (CFC.sqrt p * pe n)
          = pe n * (CFC.sqrt p * CFC.sqrt p) * pe n := by noncomm_ring
        _ = pe n * p * pe n := by rw [CFC.sqrt_mul_sqrt_self p hp]
    rw [h1, hpe]
    have h2 : p ^ e n * p * p ^ e n = p ^ (e n + 1 + e n) := by
      rw [CFC.nnrpow_add (by exact add_pos (hepos n) one_pos) (hepos n),
        CFC.nnrpow_add (hepos n) one_pos, CFC.nnrpow_one p hp]
    rw [h2]
    congr 1
    ring
  have hnormS : ∀ n, ‖S n‖ * ‖S n‖ = ‖p‖ ^ ((1 : ℝ) + 2 * (e n : ℝ)) := by
    intro n
    rw [← CStarRing.norm_star_mul_self, hSS n,
      CFC.norm_nnrpow p (by exact add_pos one_pos (by positivity)) hp]
    push_cast
    ring_nf
  -- the solution's estimate at the exponent `ε = 2⁻ⁿ`
  have hbound : ∀ n, ‖p‖ ^ ((1 : ℝ) + 2 * (e n : ℝ)) ≤ M := by
    intro n
    have hy : ∀ y : X, ‖y‖ ≤ 1 → ‖(S n : X →L[ℂ] X) y‖ ^ 2 ≤ M := by
      intro y hy1
      -- `x := p^ε y` lies in the unit ball
      have hx1 : ‖(pe n : X →L[ℂ] X) y‖ ≤ 1 := by
        refine ((pe n : X →L[ℂ] X).le_opNorm y).trans ?_
        rw [← bax_norm_coe]
        calc ‖pe n‖ * ‖y‖ ≤ 1 * 1 := by
              exact mul_le_mul (hpe1 n) hy1 (norm_nonneg y) zero_le_one
          _ = 1 := one_mul 1
      -- `p^ε a p^ε = ± (S n)* (S n)`
      have hconj : (pe n) * a * (pe n) = star (S n) * S n ∨
          (pe n) * a * (pe n) = -(star (S n) * S n) := by
        have h1 : pe n * p * pe n = star (S n) * S n := by
          rw [hSS n, hpe]
          have h2 : p ^ e n * p * p ^ e n = p ^ (e n + 1 + e n) := by
            rw [CFC.nnrpow_add (by exact add_pos (hepos n) one_pos) (hepos n),
              CFC.nnrpow_add (hepos n) one_pos, CFC.nnrpow_one p hp]
          rw [h2]
          congr 1
          ring
        rcases hpq with hpq | hpq
        · refine Or.inl ?_
          rw [hpq, mul_sub, sub_mul, hpeq n, zero_mul, sub_zero, h1]
        · refine Or.inr ?_
          rw [hpq, mul_sub, sub_mul, hpeq n, zero_mul, zero_sub, h1]
      -- `⟨p^ε y, a p^ε y⟩ = ±⟨S n y, S n y⟩`
      have hinner : ‖inner 𝒜 ((pe n : X →L[ℂ] X) y)
          ((a : X →L[ℂ] X) ((pe n : X →L[ℂ] X) y))‖
          = ‖(S n : X →L[ℂ] X) y‖ ^ 2 := by
        have hstar : (star (pe n) : Bax 𝒜 X) = pe n := (hpen n).isSelfAdjoint.star_eq
        have hcj := bax_inner_conj (pe n) a y
        rw [hstar] at hcj
        have hss := bax_inner_star_mul (S n) y
        have hnrm : ‖inner 𝒜 ((S n : X →L[ℂ] X) y) ((S n : X →L[ℂ] X) y)‖
            = ‖(S n : X →L[ℂ] X) y‖ ^ 2 :=
          (CStarModule.norm_sq_eq (A := 𝒜) (x := (S n : X →L[ℂ] X) y)).symm
        rw [← hcj]
        rcases hconj with hconj | hconj <;> rw [hconj]
        · rw [hss, hnrm]
        · rw [show ((-(star (S n) * S n) : Bax 𝒜 X) : X →L[ℂ] X)
            = -((star (S n) * S n : Bax 𝒜 X) : X →L[ℂ] X) from rfl]
          simp only [neg_apply, CStarModule.inner_neg_right]
          rw [norm_neg, hss, hnrm]
      rw [← hinner]
      exact hM _ hx1
    -- hence `‖S n‖² ≤ M`
    have hSbound : ‖S n‖ ≤ Real.sqrt M := by
      rw [bax_norm_coe]
      refine (S n : X →L[ℂ] X).opNorm_le_bound (Real.sqrt_nonneg M) fun y => ?_
      rcases eq_or_ne y 0 with rfl | hy0
      · simp
      have hyn : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy0
      have hu : ‖((‖y‖⁻¹ : ℝ) : ℂ) • y‖ ≤ 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
          inv_mul_cancel₀ hyn.ne']
      have h := hy _ hu
      rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0:ℝ) < ‖y‖⁻¹), mul_pow, inv_pow] at h
      have h2 : ‖(S n : X →L[ℂ] X) y‖ ^ 2 ≤ M * ‖y‖ ^ 2 := by
        rw [inv_mul_le_iff₀ (by positivity)] at h
        linarith
      have h3 : ‖(S n : X →L[ℂ] X) y‖ ≤ Real.sqrt (M * ‖y‖ ^ 2) := by
        calc ‖(S n : X →L[ℂ] X) y‖ = Real.sqrt (‖(S n : X →L[ℂ] X) y‖ ^ 2) :=
              (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ _ := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_mul hM0, Real.sqrt_sq (norm_nonneg y)] at h3
    have := mul_le_mul hSbound hSbound (norm_nonneg _) (Real.sqrt_nonneg M)
    rw [hnormS n] at this
    calc ‖p‖ ^ ((1 : ℝ) + 2 * (e n : ℝ)) ≤ Real.sqrt M * Real.sqrt M := this
      _ = M := Real.mul_self_sqrt hM0
  -- "upon taking the supremum over all dyadic `ε > 0`"
  rcases eq_or_lt_of_le (norm_nonneg p) with h0 | h0
  · rw [← h0]; exact hM0
  have hexp : Filter.Tendsto (fun n : ℕ => (1 : ℝ) + 2 * (e n : ℝ))
      Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun n : ℕ => ((e n : ℝ))) Filter.atTop (nhds 0) := by
      have : ∀ n : ℕ, ((e n : ℝ)) = (1 / 2 : ℝ) ^ n := by
        intro n; rw [he]; push_cast; ring
      rw [funext this]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using (tendsto_const_nhds.add (h1.const_mul 2))
  have htend : Filter.Tendsto (fun n : ℕ => ‖p‖ ^ ((1 : ℝ) + 2 * (e n : ℝ)))
      Filter.atTop (nhds (‖p‖ ^ (1 : ℝ))) :=
    (Real.continuousAt_const_rpow h0.ne').tendsto.comp hexp
  have := le_of_tendsto htend (Filter.Eventually.of_forall hbound)
  rwa [Real.rpow_one] at this

set_option maxHeartbeats 400000 in
/-- **32XV** (`chilb-vector-states-order-separating`, cstar.tex:5375,
Exercise), part 3: `‖T‖ = sup_{‖x‖ ≤ 1} ‖⟨x, Tx⟩‖` for self-adjoint `T`.

*Class 1 — faithful.*  Solution `parsec-320.150`(3): the bound
`sup ≤ ‖T‖` is **32IX**.2; for the other direction the solution scales `T`
down so that `‖T‖ ≤ 1`, recalls `‖T‖ = ‖T⁺‖ ∨ ‖T⁻‖` (**24II**.4), and tests
with the vectors `T±^ε y`, `y ∈ (X)_{≤1}` and `ε > 0` dyadic — see
`norm_le_of_vector_bound`, which is that chain. -/
theorem chilb_vector_states_3 [CompleteSpace X] (T : X →L[ℂ] X)
    (h : ModuleAdjointTo 𝒜 ⇑T ⇑T) :
    ‖T‖ = ⨆ x : {x : X // ‖x‖ ≤ 1}, ‖inner 𝒜 (x : X) (T x)‖ := by
  haveI : Nonempty {x : X // ‖x‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  obtain ⟨a, ha⟩ : ∃ a : Bax 𝒜 X, (a : X →L[ℂ] X) = T := ⟨⟨T, ⟨⇑T, h⟩⟩, rfl⟩
  have hsa : IsSelfAdjoint a := bax_star_eq (by rw [ha]; exact h)
  have hanorm : ‖a‖ = ‖T‖ := by rw [bax_norm_coe, ha]
  set F : {x : X // ‖x‖ ≤ 1} → ℝ := fun x => ‖inner 𝒜 (x : X) (T x)‖ with hF
  -- the supremum is bounded by `‖T‖` (**32IX**.2)
  have hb : ∀ x : {x : X // ‖x‖ ≤ 1}, F x ≤ ‖T‖ := by
    intro x
    calc F x ≤ ‖(x : X)‖ * ‖T (x : X)‖ := (chilb_norm_basic_2 _ _ 0).2
      _ ≤ 1 * (‖T‖ * 1) := by
          gcongr
          · exact x.2
          · exact (T.le_opNorm (x : X)).trans (by nlinarith [norm_nonneg T, x.2])
      _ = ‖T‖ := by ring
  have hbdd : BddAbove (Set.range F) := ⟨‖T‖, by rintro _ ⟨x, rfl⟩; exact hb x⟩
  have hMle : (⨆ x : {x : X // ‖x‖ ≤ 1}, F x) ≤ ‖T‖ := ciSup_le hb
  set M : ℝ := ⨆ x : {x : X // ‖x‖ ≤ 1}, F x with hM
  have hM0 : 0 ≤ M := by
    have := le_ciSup hbdd (⟨0, by simp⟩ : {x : X // ‖x‖ ≤ 1})
    simpa [hF] using this
  have hMb : ∀ x : X, ‖x‖ ≤ 1 → ‖inner 𝒜 x ((a : X →L[ℂ] X) x)‖ ≤ M := by
    intro x hx
    rw [ha]
    exact le_ciSup hbdd (⟨x, hx⟩ : {x : X // ‖x‖ ≤ 1})
  refine le_antisymm ?_ hMle
  -- **24II**.4: `‖T‖ = ‖T⁺‖ ∨ ‖T⁻‖`, so it suffices to bound both parts
  have hsplit : (a⁺ : Bax 𝒜 X) - a⁻ = a := CFC.posPart_sub_negPart a hsa
  have hmax : ‖a‖ = max ‖(a⁺ : Bax 𝒜 X)‖ ‖(a⁻ : Bax 𝒜 X)‖ := cstar_pos_neg_part_4 a hsa
  -- "by scaling down `T` if necessary we may assume WLOG that `‖T‖ ≤ 1`"
  have hgen : ∀ r s : Bax 𝒜 X, 0 ≤ r → 0 ≤ s → s * r = 0 →
      (a = r - s ∨ a = s - r) → ‖r‖ ≤ ‖a‖ → ‖r‖ ≤ M := by
    intro r s hr hs hsr hrs hra
    rcases eq_or_lt_of_le (norm_nonneg a) with h0 | h0
    · have : ‖r‖ = 0 := le_antisymm (hra.trans h0.symm.le) (norm_nonneg r)
      rw [this]
      exact hM0
    set c : ℝ := ‖a‖⁻¹ with hc
    have hcpos : 0 < c := inv_pos.mpr h0
    have hsmul : ∀ z : Bax 𝒜 X, ‖(c : ℂ) • z‖ = c * ‖z‖ := by
      intro z
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
    have hcoe : ∀ (z : Bax 𝒜 X) (x : X),
        (((c : ℂ) • z : Bax 𝒜 X) : X →L[ℂ] X) x = (c : ℂ) • ((z : X →L[ℂ] X) x) := by
      intro z x
      rfl
    have hkey := norm_le_of_vector_bound ((c : ℂ) • a) ((c : ℂ) • r) ((c : ℂ) • s)
      (real_smul_nonneg hr hcpos.le) (real_smul_nonneg hs hcpos.le)
      (by rw [smul_mul_smul_comm, hsr, smul_zero])
      (by
        rcases hrs with hrs | hrs
        · exact Or.inl (by rw [hrs, smul_sub])
        · exact Or.inr (by rw [hrs, smul_sub]))
      (by rw [hsmul, hc, inv_mul_le_iff₀ h0, mul_one]; exact hra)
      (c * M)
      (by
        intro x hx
        rw [hcoe, CStarModule.inner_smul_right_complex, norm_smul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hcpos]
        exact mul_le_mul_of_nonneg_left (hMb x hx) hcpos.le)
    rw [hsmul] at hkey
    exact le_of_mul_le_mul_left (by linarith) hcpos
  have h1 : ‖(a⁺ : Bax 𝒜 X)‖ ≤ M :=
    hgen _ _ (CFC.posPart_nonneg a) (CFC.negPart_nonneg a) (CFC.negPart_mul_posPart a)
      (Or.inl hsplit.symm) (by rw [hmax]; exact le_max_left _ _)
  have h2 : ‖(a⁻ : Bax 𝒜 X)‖ ≤ M :=
    hgen _ _ (CFC.negPart_nonneg a) (CFC.posPart_nonneg a) (CFC.posPart_mul_negPart a)
      (Or.inr hsplit.symm) (by rw [hmax]; exact le_max_right _ _)
  calc ‖T‖ = ‖a‖ := hanorm.symm
    _ = max ‖(a⁺ : Bax 𝒜 X)‖ ‖(a⁻ : Bax 𝒜 X)‖ := hmax
    _ ≤ M := max_le h1 h2

/-- **32XVI** (cstar.tex:5292, Corollary): `T* T` is positive in `B^a(X)`
for every adjointable bounded `T : X → Y` between Hilbert 𝒜-modules.  The
first conjunct is the immediate computation `⟨x, T*Tx⟩ = ⟨Tx, Tx⟩ ≥ 0`; the
second is positivity in `B^a(X)` itself (in the form used in **32XV**.2),
obtained from it by **32XV**.2. -/
theorem chilb_adjoint_mul_self_nonneg [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[ℂ] Y) (S : Y →L[ℂ] X) (h : ModuleAdjointTo 𝒜 ⇑T ⇑S) :
    (∀ x : X, 0 ≤ inner 𝒜 x ((S.comp T) x)) ∧
      ∃ R R' : X →L[ℂ] X, ModuleAdjointTo 𝒜 ⇑R ⇑R' ∧ S.comp T = R'.comp R := by
  have hpos : ∀ x : X, 0 ≤ inner 𝒜 x ((S.comp T) x) := by
    intro x
    rw [ContinuousLinearMap.coe_comp', Function.comp_apply, ← h x (T x)]
    exact CStarModule.inner_self_nonneg
  have hadj : ModuleAdjointable 𝒜 ⇑(S.comp T) :=
    ⟨⇑S ∘ ⇑T, moduleAdjointTo_comp (⇑T) (⇑S) (⇑S) (⇑T) h (moduleAdjointTo_symm _ _ h)⟩
  exact ⟨hpos, (chilb_vector_states_2 (S.comp T) hadj).mp hpos⟩

end CauchySchwarz

/-! ## Parsec 330: matrices over a C*-algebra -/

section Matrices

variable {𝒜 ℬ : Type*} [CStarAlgebra 𝒜] [CStarAlgebra ℬ]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
variable {N : ℕ}

/-- A double sum `∑_{i,j} dᵢ* dⱼ` is a square `(∑ᵢ dᵢ)* (∑ⱼ dⱼ)`, hence
positive.  This is the workhorse behind the elementary complete positivity
proofs below. -/
private theorem sum_star_mul_sum {R : Type*} [NonUnitalSemiring R]
    [StarRing R] {n : ℕ} (d : Fin n → R) :
    ∑ i, ∑ j, star (d i) * d j = star (∑ i, d i) * ∑ j, d j := by
  rw [star_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

/-! The three parts of **33I** are about *rectangular* matrices: erratum
`parsec-330.10` corrects the exercise's "`N×M`" to "`M×N`", so an `M×N`-matrix
`A` gives a bounded module map `𝒜^N → 𝒜^M`, and `A ↦ Ā` is a linear bijection
onto `𝓑^a(𝒜^N, 𝒜^M)`.  Mathlib's `CStarMatrix.toCLM` acts by `vecMul`, so it
sends an `M×N`-matrix to a map `𝒜^M → 𝒜^N`; that is the thesis's assignment
composed with transposition of the index types, and it is why the composition
order is reversed in part 3.  We state all three parts over the two index sets
`Fin M`, `Fin N` in Mathlib's convention. -/

/-- **33I** (`cstar-matrices`, cstar.tex:5307, Exercise), part 1: an
`M×N`-matrix `A` over `𝒜` gives a bounded module map between `𝒜^M` and `𝒜^N`
(Mathlib: `CStarMatrix.toCLM`, a `→L[ℂ]`, so boundedness is part of the
object), adjoint to the one of its conjugate transpose `Ā`. -/
theorem cstar_matrices_1 {M : ℕ} (A : CStarMatrix (Fin M) (Fin N) 𝒜) :
    ModuleAdjointTo 𝒜 ⇑(CStarMatrix.toCLM A) ⇑(CStarMatrix.toCLM (Matrix.conjTranspose A)) :=
  fun _ _ => (CStarMatrix.inner_toCLM_conjTranspose_right (M := A)).symm

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- **33I** (`cstar-matrices`, cstar.tex:5307, Exercise), part 2:
`A ↦ toCLM A` is a *linear* bijection between the `M×N`-matrices over `𝒜`
and the adjointable bounded module maps `𝒜^M → 𝒜^N`.  Linearity is the first
clause, injectivity the second, surjectivity the third. -/
theorem cstar_matrices_2 {M : ℕ} :
    (∀ (c : ℂ) (A B : CStarMatrix (Fin M) (Fin N) 𝒜),
        CStarMatrix.toCLM (c • A + B)
          = c • CStarMatrix.toCLM A + CStarMatrix.toCLM B) ∧
    Function.Injective
      (CStarMatrix.toCLM (A := 𝒜) (m := Fin M) (n := Fin N)) ∧
    ∀ T : C⋆ᵐᵒᵈ(𝒜, Fin M → 𝒜) →L[ℂ] C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜),
      (∀ (a : 𝒜) (x : C⋆ᵐᵒᵈ(𝒜, Fin M → 𝒜)), T (a • x) = a • T x) →
      ModuleAdjointable 𝒜 ⇑T →
      ∃ A : CStarMatrix (Fin M) (Fin N) 𝒜, CStarMatrix.toCLM A = T := by
  classical
  -- injectivity: "simply apply `A̲` to the vector `eₙ` … to see that
  -- `0 = A̲(eₙ) = (A_{mn})ₘ`" (solution `parsec-330.10`(2))
  have hinj : Function.Injective
      (CStarMatrix.toCLM (A := 𝒜) (m := Fin M) (n := Fin N)) := by
    intro A B hAB
    ext i j
    have h := congrArg (fun T : C⋆ᵐᵒᵈ(𝒜, Fin M → 𝒜) →L[ℂ] C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜) =>
      T ((WithCStarModule.equiv 𝒜 (Fin M → 𝒜)).symm (Pi.single i (1 : 𝒜))) j) hAB
    simpa only [CStarMatrix.toCLM_apply_single_apply, one_mul] using h
  refine ⟨fun c A B => by rw [map_add, map_smul], hinj, fun T hT _ => ?_⟩
  have hsum : ∀ (g : Fin M → C⋆ᵐᵒᵈ(𝒜, Fin M → 𝒜)) (k : Fin M),
      (∑ i, g i) k = ∑ i, g i k := fun g k => Finset.sum_apply k Finset.univ g
  have hsum' : ∀ (g : Fin M → C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜)) (k : Fin N),
      (∑ i, g i) k = ∑ i, g i k := fun g k => Finset.sum_apply k Finset.univ g
  set b : Fin M → C⋆ᵐᵒᵈ(𝒜, Fin M → 𝒜) :=
    fun i => (WithCStarModule.equiv 𝒜 (Fin M → 𝒜)).symm (Pi.single i 1) with hb
  have hbk : ∀ i k : Fin M, b i k = if k = i then 1 else 0 := by
    intro i k
    rw [hb]
    simp [WithCStarModule.equiv_symm_pi_apply, Pi.single_apply]
  refine ⟨CStarMatrix.ofMatrix fun i j => T (b i) j, ?_⟩
  have hv : ∀ v : C⋆ᵐᵒᵈ(𝒜, Fin M → 𝒜), v = ∑ i, v i • b i := by
    intro v
    ext k
    rw [hsum]
    simp only [WithCStarModule.smul_apply, hbk, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_eq_single k (fun i _ hik => by simp [Ne.symm hik]) (by simp)]
    simp
  ext v j
  rw [CStarMatrix.toCLM_apply_eq_sum]
  conv_rhs => rw [hv v]
  rw [map_sum, hsum']
  simp only [hT, WithCStarModule.smul_apply, WithCStarModule.equiv_symm_pi_apply,
    CStarMatrix.ofMatrix_apply, Matrix.of_apply, smul_eq_mul]
  rfl

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- **33I** (`cstar-matrices`, cstar.tex:5307, Exercise), part 3: for an
`M×N`-matrix `A` and an `N×K`-matrix `B` the assignment `A ↦ toCLM A` is
multiplicative up to the order of composition (Mathlib's `toCLM` acts by
`vecMul`, hence reverses composition). -/
theorem cstar_matrices_3 {M K : ℕ} (A : CStarMatrix (Fin M) (Fin N) 𝒜)
    (B : CStarMatrix (Fin N) (Fin K) 𝒜) :
    CStarMatrix.toCLM (A * B) =
      (CStarMatrix.toCLM B).comp (CStarMatrix.toCLM A) := by
  -- the solution's computation, entry by entry:
  -- `∑ₖ vₖ (AB)ₖⱼ = ∑ₖ ∑ₘ vₖ (Aₖₘ Bₘⱼ) = ∑ₘ (∑ₖ vₖ Aₖₘ) Bₘⱼ`
  ext v j
  simp only [CStarMatrix.toCLM_apply_eq_sum, ContinuousLinearMap.coe_comp,
    Function.comp_apply, WithCStarModule.equiv_symm_pi_apply, CStarMatrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- **33I** (`cstar-matrices`, cstar.tex:5307, Exercise), part 4: the
`N×N`-matrices over a C*-algebra `𝒜` form a C*-algebra `M_N(𝒜)` — in
Mathlib the instance `CStarMatrix.instCStarAlgebra` on
`CStarMatrix (Fin N) (Fin N) 𝒜`. -/
noncomputable example : CStarAlgebra (CStarMatrix (Fin N) (Fin N) 𝒜) :=
  inferInstance

/-- `0 ≤ a` in a C*-algebra gives `a = b* b`.  Stated for an abstract C*-algebra
because Mathlib's typeclass search cannot find the continuous functional calculus
instances for `CStarMatrix` directly (there are two syntactically distinct routes
to `Algebra ℝ (CStarMatrix n n 𝒜)`); going through an abstract `M` sidesteps this. -/
private theorem exists_star_mul_self {M : Type*} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] {a : M} (ha : 0 ≤ a) : ∃ b, a = star b * b :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha

section MatrixOrder

variable [PartialOrder (CStarMatrix (Fin N) (Fin N) 𝒜)]
  [StarOrderedRing (CStarMatrix (Fin N) (Fin N) 𝒜)]

/-- Cauchy--Schwarz **32VI** for the 𝒜-valued inner product `(v,w) ↦ ⟨v, Aw⟩`
on `𝒜^N` determined by a positive matrix `A`, evaluated at the standard basis:
`Aᵢⱼ Aⱼᵢ ≤ ‖Aⱼⱼ‖ Aᵢᵢ`.

This is the opening move of the thesis's proofs of both **33III**.3
(solution `parsec-330.30`(3)) and **34XII** (`cstar.tex:5717`): "since
`(v,w) ↦ ⟨v,Aw⟩` gives an 𝒜-valued inner product on `𝒜²`, Cauchy--Schwarz
gives …", applied at `v, w ∈ {(1,0), (0,1)}`.

A merely *positive* `A` gives a form that is only semi-definite, which
Mathlib's `CStarModule` — a normed object, so definite — cannot carry.
Writing `A = C* C` (`exists_star_mul_self`) realises the thesis's form inside
the honest Hilbert module `C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜)`: with `uₖ := C* eₖ` one has
`⟨u_j, u_i⟩ = Aᵢⱼ`, so `A` is the Gram matrix of the `uₖ` (the converse of
**33II**.2), and the inequality is **32VI** `chilb_cs` at `u_i, u_j`. -/
private theorem pos_matrix_cs {A : CStarMatrix (Fin N) (Fin N) 𝒜} (hA : 0 ≤ A)
    (i j : Fin N) : A i j * A j i ≤ ‖A j j‖ • A i i := by
  classical
  obtain ⟨C, rfl⟩ := exists_star_mul_self hA
  set u : Fin N → C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜) := fun k =>
    CStarMatrix.toCLM (star C)
      ((WithCStarModule.equiv 𝒜 (Fin N → 𝒜)).symm (Pi.single k (1 : 𝒜))) with hu
  have hentry : ∀ k l : Fin N,
      (star C * C : CStarMatrix (Fin N) (Fin N) 𝒜) k l = inner 𝒜 (u l) (u k) := by
    intro k l
    have h := CStarMatrix.mul_entry_mul_eq_inner_toCLM
      (M := (star C * C : CStarMatrix (Fin N) (Fin N) 𝒜)) (i := k) (j := l) 1 1
    rw [one_mul, star_one, mul_one] at h
    rw [h, cstar_matrices_3 (star C) C]
    have hCC : Matrix.conjTranspose (star C : CStarMatrix (Fin N) (Fin N) 𝒜) = C := by
      rw [show Matrix.conjTranspose (star C : CStarMatrix (Fin N) (Fin N) 𝒜)
        = star (star C) from rfl, star_star]
    have := CStarMatrix.inner_toCLM_conjTranspose_right
      (M := (star C : CStarMatrix (Fin N) (Fin N) 𝒜))
      (v := (WithCStarModule.equiv 𝒜 (Fin N → 𝒜)).symm (Pi.single l (1 : 𝒜)))
      (w := u k)
    rw [hCC] at this
    rw [ContinuousLinearMap.comp_apply]
    exact this
  rw [hentry i j, hentry j i, hentry j j, hentry i i]
  exact chilb_cs (u i) (u j)

/-- **33II** (`when-a-matrix-over-a-cstar-algebra-is-positive`,
cstar.tex:5339, Exercise), part 1: an `N×N`-matrix `A` over `𝒜` is positive
iff `0 ≤ ∑_{i,j} aᵢ* Aᵢⱼ aⱼ` for all `a₁, …, a_N ∈ 𝒜`.

This is the route the exercise's hint prescribes: transport the question to
`𝓑^a(𝒜^N)` along **33I** and apply **32XV**.2 there.  The transport is
`cstar_matrices_1` (the adjoint of `Ā` is `A*`), `cstar_matrices_2`
(injectivity and surjectivity of `A ↦ Ā`) and `cstar_matrices_3` (`A ↦ Ā`
is multiplicative — up to the order of composition, Mathlib's `toCLM` acting
by `vecMul`), which together turn `0 ≤ A` — that is, `A = B B*` — into
`Ā = R* R` for an adjointable `R`.  The vector functional of `Ā` at `x`
is the exercise's sum at `aᵢ = xᵢ*`.  Neither half needs the self-adjointness
of `A` to be established by hand. -/
theorem cstar_matrix_positive_iff (A : CStarMatrix (Fin N) (Fin N) 𝒜) :
    0 ≤ A ↔ ∀ a : Fin N → 𝒜, 0 ≤ ∑ i, ∑ j, star (a i) * A i j * a j := by
  have hct : ∀ B : CStarMatrix (Fin N) (Fin N) 𝒜,
      (Matrix.conjTranspose B : CStarMatrix (Fin N) (Fin N) 𝒜) = star B := fun _ => rfl
  -- **33I**: `0 ≤ A` iff `Ā` is of the form `R* R` in `𝓑^a(𝒜^N)`
  have hop : (0 ≤ A) ↔ ∃ R R' : C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜) →L[ℂ] C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜),
      ModuleAdjointTo 𝒜 ⇑R ⇑R' ∧ CStarMatrix.toCLM A = R'.comp R := by
    constructor
    · intro hA
      obtain ⟨B, rfl⟩ := exists_star_mul_self hA
      exact ⟨CStarMatrix.toCLM (star B), CStarMatrix.toCLM B,
        by simpa [hct] using cstar_matrices_1 (star B), cstar_matrices_3 (star B) B⟩
    · rintro ⟨R, R', hadj, heq⟩
      obtain ⟨B, hB⟩ := (cstar_matrices_2 (𝒜 := 𝒜) (M := N) (N := N)).2.2 R
        (moduleAdjointable_linear (𝒜 := 𝒜) ⇑R ⟨⇑R', hadj⟩).2.2 ⟨⇑R', hadj⟩
      have hadj' : ModuleAdjointTo 𝒜 ⇑(CStarMatrix.toCLM B) ⇑R' := by rw [hB]; exact hadj
      have hR' : ⇑R' = ⇑(CStarMatrix.toCLM (star B)) :=
        moduleAdjointTo_unique _ _ _ hadj' (by simpa [hct] using cstar_matrices_1 B)
      have hA : CStarMatrix.toCLM A = CStarMatrix.toCLM (B * star B) := by
        rw [heq, cstar_matrices_3 B (star B), ← hB]
        exact congrArg (fun f => ContinuousLinearMap.comp f (CStarMatrix.toCLM B))
          (DFunLike.coe_injective hR')
      rw [CStarMatrix.toCLM_injective hA]
      exact mul_star_self_nonneg B
  -- the vector functional of `Ā` at `x` is the exercise's sum at `aᵢ = xᵢ*`
  have hinner : ∀ x : C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜),
      (inner 𝒜 x (CStarMatrix.toCLM A x) : 𝒜)
        = ∑ i, ∑ j, star (star (x i)) * A i j * star (x j) := by
    intro x
    simp only [CStarMatrix.toCLM_apply_eq_sum, WithCStarModule.pi_inner,
      WithCStarModule.equiv_symm_pi_apply, WithCStarModule.inner_def, star_star,
      Finset.sum_mul]
    rw [Finset.sum_comm]
  -- **32XV**.2: the vector functionals of `𝓑^a(𝒜^N)` are order separating
  rw [hop, ← chilb_vector_states_2 (𝒜 := 𝒜) (X := C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜))
    (CStarMatrix.toCLM A) ⟨_, cstar_matrices_1 A⟩]
  constructor
  · intro h a
    have h2 := h ((WithCStarModule.equiv 𝒜 (Fin N → 𝒜)).symm fun i => star (a i))
    rw [hinner] at h2
    simpa using h2
  · intro h x
    rw [hinner]
    exact h fun i => star (x i)

/-- **33II** (`when-a-matrix-over-a-cstar-algebra-is-positive`,
cstar.tex:5339, Exercise), part 2: the Gram matrix `(⟨xᵢ, xⱼ⟩)ᵢⱼ` of vectors
of a pre-Hilbert 𝒜-module is positive.

**Convention.** As in `chilb_cs`, `⟪x,y⟫_Mathlib = ⟨y,x⟩_thesis`, so the
thesis's Gram matrix `(⟨xᵢ,xⱼ⟩)ᵢⱼ` is `fun i j => inner 𝒜 (x j) (x i)` here.
Written the other way round it is the *block transpose* of the thesis's matrix,
and block transposition does not preserve positivity — that is precisely
**33III**.3 (`mnf_not_positive`) — so the unswapped statement is *false*:
for `𝒜 = M₂(ℂ)`, `x₁ = e₁₁`, `x₂ = e₂₁` it is the transposition permutation
matrix in `M₂(M₂(ℂ)) ≅ M₄(ℂ)`, which has eigenvalue `−1`. -/
theorem cstar_matrix_gram_nonneg {X : Type*} [NormedAddCommGroup X]
    [Module ℂ X] [SMul 𝒜 X] [CStarModule 𝒜 X] (x : Fin N → X) :
    0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => inner 𝒜 (x j) (x i)) := by
  rw [cstar_matrix_positive_iff]
  intro a
  have key : ∑ i, ∑ j, star (a i) * (CStarMatrix.ofMatrix
        (Matrix.of fun i j => (inner 𝒜 (x j) (x i) : 𝒜))) i j * a j
      = inner 𝒜 (∑ k, star (a k) • x k) (∑ k, star (a k) • x k) := by
    simp only [CStarModule.inner_sum_left, CStarModule.inner_sum_right,
      CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right, star_star,
      CStarMatrix.ofMatrix_apply, Matrix.of_apply, mul_assoc, Finset.mul_sum]
  rw [key]
  exact CStarModule.inner_self_nonneg

/-- **33II** (`when-a-matrix-over-a-cstar-algebra-is-positive`,
cstar.tex:5339, Exercise), part 3: the matrix `(aᵢ* aⱼ)ᵢⱼ` is positive for
all `a₁, …, a_N ∈ 𝒜`.

As the solution says, this is part 2 for `X = 𝒜` — the C*-algebra as a Hilbert
module over itself, `⟨a,b⟩ = a* b`.  In Mathlib's opposite convention
`⟪x,y⟫ = y x*` (`WithCStarModule.inner_def`), so the vectors to feed part 2
are `xᵢ = aᵢ*`. -/
theorem cstar_matrix_star_mul_nonneg (a : Fin N → 𝒜) :
    0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j) := by
  have h := cstar_matrix_gram_nonneg (𝒜 := 𝒜) (X := 𝒜) fun i => star (a i)
  simpa only [WithCStarModule.inner_def, star_star] using h

end MatrixOrder

section MatBilin

/-- `∑ᵢ∑ⱼ∑ₖ = ∑ₖ∑ᵢ∑ⱼ`. -/
private theorem sum_comm₃' {N : ℕ} {M : Type*} [AddCommMonoid M]
    (h : Fin N → Fin N → Fin N → M) :
    ∑ i, ∑ j, ∑ k, h i j k = ∑ k, ∑ i, ∑ j, h i j k := by
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]

/-- `∑ᵢ∑ⱼ∑ₖ∑ₗ = ∑ₖ∑ₗ∑ᵢ∑ⱼ`. -/
private theorem sum_comm₄' {N : ℕ} {M : Type*} [AddCommMonoid M]
    (h : Fin N → Fin N → Fin N → Fin N → M) :
    ∑ i, ∑ j, ∑ k, ∑ l, h i j k l = ∑ k, ∑ l, ∑ i, ∑ j, h i j k l := by
  rw [sum_comm₃' (fun i j k => ∑ l, h i j k l)]
  exact Finset.sum_congr rfl fun k _ => sum_comm₃' (fun i j l => h i j k l)

/-- A positive matrix over a C*-algebra is `X* X`, entrywise
`Mᵢⱼ = ∑ₖ Xₖᵢ* Xₖⱼ`. -/
private theorem exists_star_repr_of_nonneg {𝒞 : Type*} [CStarAlgebra 𝒞]
    [PartialOrder 𝒞] [StarOrderedRing 𝒞] {N : ℕ}
    (M : CStarMatrix (Fin N) (Fin N) 𝒞) (hM : 0 ≤ M) :
    ∃ X : Fin N → Fin N → 𝒞, ∀ i j, M i j = ∑ k, star (X k i) * X k j := by
  obtain ⟨Y, hY⟩ := exists_star_mul_self hM
  refine ⟨fun k i => Y k i, fun i j => ?_⟩
  rw [hY, CStarMatrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [CStarMatrix.star_apply]

/-- **113II** (`bilinear-cp`, proc.tex) together with **113IV**, in the
unbundled form in which thesis B's `IsVNTensor` (dils.tex 165II) supplies
its data: `M_N t` sends a pair of positive matrices to a positive one.
**No `ℂ`-homogeneity of `t` is used** — only additivity in each slot,
multiplicativity and involution preservation — which is exactly what
`IsVNTensor` has: the positivity clause that an earlier revision proposed
to *add* to it is derivable, so no ruling is outstanding here.  (That
revision deferred to `QUESTIONS.md` B5, which was deleted as resolved on
2026-08-16 — the question no longer exists.  Nor is one needed: von Neumann
algebras are C*-algebras, mi-bilinear maps are automatically
`ℂ`-homogeneous, and `IsVNTensor` needs the generality it has.)

Lives here rather than in `A/Proc/Tensor.lean` (where it was first proved)
because its content is about matrices over C*-algebras and it is needed by
`B/Dils`, which imports this file but not `A/Proc`.  (The earlier pointer
to `QUESTIONS.md` D3 dangles for the same reason; D3 was deleted the same
day.) -/
theorem matBilin_nonneg_of_mi {𝒜' ℬ' 𝒞 : Type*} [CStarAlgebra 𝒜']
    [PartialOrder 𝒜'] [StarOrderedRing 𝒜'] [CStarAlgebra ℬ'] [PartialOrder ℬ']
    [StarOrderedRing ℬ'] [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]
    (t : 𝒜' → ℬ' → 𝒞)
    (hl : ∀ (a a' : 𝒜') (b : ℬ'), t (a + a') b = t a b + t a' b)
    (hr : ∀ (a : 𝒜') (b b' : ℬ'), t a (b + b') = t a b + t a b')
    (hmul : ∀ (a a' : 𝒜') (b b' : ℬ'), t a b * t a' b' = t (a * a') (b * b'))
    (hstar : ∀ (a : 𝒜') (b : ℬ'), star (t a b) = t (star a) (star b))
    {N : ℕ} (M : CStarMatrix (Fin N) (Fin N) 𝒜')
    (M' : CStarMatrix (Fin N) (Fin N) ℬ') (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (c : Fin N → 𝒞) :
    0 ≤ ∑ i, ∑ j, star (c i) * t (M i j) (M' i j) * c j := by
  have hsl : ∀ {n : ℕ} (x : Fin n → 𝒜') (y : ℬ'),
      t (∑ k, x k) y = ∑ k, t (x k) y := fun {n} x y =>
    map_sum (AddMonoidHom.mk' (fun a => t a y) fun a a' => hl a a' y) x Finset.univ
  have hsr : ∀ {n : ℕ} (x : 𝒜') (y : Fin n → ℬ'),
      t x (∑ k, y k) = ∑ k, t x (y k) := fun {n} x y =>
    map_sum (AddMonoidHom.mk' (fun b => t x b) fun b b' => hr x b b') y Finset.univ
  -- the argument of **113II**, for `t`
  have hcp : ∀ {n : ℕ} (a : Fin n → 𝒜') (b : Fin n → ℬ') (d : Fin n → 𝒞),
      0 ≤ ∑ i, ∑ j,
        star (d i) * t (star (a i) * a j) (star (b i) * b j) * d j := by
    intro n a b d
    have key : ∀ i j : Fin n,
        star (d i) * t (star (a i) * a j) (star (b i) * b j) * d j
          = star (t (a i) (b i) * d i) * (t (a j) (b j) * d j) := by
      intro i j
      rw [← hmul (star (a i)) (a j) (star (b i)) (b j), ← hstar (a i) (b i),
        star_mul, mul_assoc, mul_assoc, mul_assoc]
    calc (0 : 𝒞)
        ≤ star (∑ i, t (a i) (b i) * d i) * (∑ i, t (a i) (b i) * d i) :=
          star_mul_self_nonneg _
      _ = ∑ i, ∑ j,
            star (d i) * t (star (a i) * a j) (star (b i) * b j) * d j := by
          rw [star_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => (key i j).symm
  obtain ⟨X, hX⟩ := exists_star_repr_of_nonneg M hM
  obtain ⟨Y, hY⟩ := exists_star_repr_of_nonneg M' hM'
  have hrw : ∑ i, ∑ j, star (c i) * t (M i j) (M' i j) * c j
      = ∑ k, ∑ l, ∑ i, ∑ j, star (c i) *
          t (star (X k i) * X k j) (star (Y l i) * Y l j) * c j := by
    rw [← sum_comm₄' (fun i j k l => star (c i) *
      t (star (X k i) * X k j) (star (Y l i) * Y l j) * c j)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hb : t (M i j) (M' i j)
        = ∑ k, ∑ l, t (star (X k i) * X k j) (star (Y l i) * Y l j) := by
      rw [hX i j, hY i j, hsl]
      exact Finset.sum_congr rfl fun k _ => hsr _ _
    rw [hb, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hrw]
  exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
    hcp (fun i => X k i) (fun i => Y l i) c

end MatBilin

/-- **33III** (`mnf`, cstar.tex:5358, Exercise), part 1: applying a linear
map `f : 𝒜 → ℬ` entrywise to matrices gives a *linear* map
`M_N f : M_N(𝒜) → M_N(ℬ)`.  Mathlib bundles it as `CStarMatrix.mapₗ`; the
statements below use the unbundled `CStarMatrix.map`, so linearity is
recorded here in the form it takes there. -/
theorem mnf_linear (f : 𝒜 →ₗ[ℂ] ℬ) (c : ℂ) (A B : CStarMatrix (Fin N) (Fin N) 𝒜) :
    (c • A + B).map ⇑f = c • A.map ⇑f + B.map ⇑f := by
  have h : ∀ M : CStarMatrix (Fin N) (Fin N) 𝒜,
      M.map ⇑f = CStarMatrix.mapₗ (R := ℂ) (S := ℂ) f M := fun _ => rfl
  rw [h, h, h, map_add, map_smul]

/-- **33III** (`mnf`, cstar.tex:5358, Exercise), part 2: `M_N f` is unital
when `f` is, multiplicative when `f` is, and involution preserving when `f`
is.  (Part 1, that `M_N f` is linear, is `mnf_linear` above.) -/
theorem mnf_inherits (f : 𝒜 →ₗ[ℂ] ℬ) :
    (f 1 = 1 → (1 : CStarMatrix (Fin N) (Fin N) 𝒜).map ⇑f = 1) ∧
    (IsMultiplicativeMap f → ∀ A B : CStarMatrix (Fin N) (Fin N) 𝒜,
      (A * B).map ⇑f = A.map ⇑f * B.map ⇑f) ∧
    (IsInvolutionPreserving f → ∀ A : CStarMatrix (Fin N) (Fin N) 𝒜,
      (star A).map ⇑f = star (A.map ⇑f)) := by
  refine ⟨fun hu => ?_, fun hm A B => ?_, fun hi A => ?_⟩
  · ext i j
    simp only [CStarMatrix.map_apply, CStarMatrix.one_apply]
    split_ifs with h <;> simp [hu]
  · have hm' : ∀ a b : 𝒜, f (a * b) = f a * f b := hm
    ext i j
    simp only [CStarMatrix.map_apply, CStarMatrix.mul_apply, map_sum, hm']
  · have hi' : ∀ a : 𝒜, f (star a) = star (f a) := hi
    ext i j
    simp only [CStarMatrix.map_apply, CStarMatrix.star_apply, hi']

/-- Transposition on `M₂(ℂ)`, as a `ℂ`-linear map. -/
private def transposeM2 :
    CStarMatrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ where
  toFun M := CStarMatrix.ofMatrix (Matrix.of fun i j => M j i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem transposeM2_apply (M : CStarMatrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    transposeM2 M i j = M j i := rfl

/-- Transposition is positive: if `A = B* B` then `Aᵀ = C* C` for the entrywise
conjugate `C` of `B` (this uses only commutativity of `ℂ`, no spectral theory). -/
private theorem transposeM2_pos : IsPositiveMap transposeM2 := by
  intro A hA
  obtain ⟨B, rfl⟩ := exists_star_mul_self hA
  have h : transposeM2 (star B * B)
      = star (CStarMatrix.ofMatrix (Matrix.of fun i j => star (B i j)))
        * CStarMatrix.ofMatrix (Matrix.of fun i j => star (B i j)) := by
    ext i j
    rw [transposeM2_apply, CStarMatrix.mul_apply, CStarMatrix.mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [CStarMatrix.star_apply, CStarMatrix.ofMatrix_apply, Matrix.of_apply, star_star]
    exact mul_comm _ _
  rw [h]
  exact star_mul_self_nonneg _

private def e01M2 : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix !![0, 1; 0, 0]

/-- **33III** (`mnf`, cstar.tex:5358, Exercise), part 3, first clause:
`M_N f` need not be positive when `f` is: the transpose map on `M₂` is
positive but `M₂` of it is not.  (The exercise's second clause, that `M_n f`
*is* bounded by `n²‖f‖` when `f` is bounded — the form erratum
`parsec-330.30` gives it — is `mnf_bounded` below.)

*Class 1 — faithful.*  This is solution `parsec-330.30`(3).  The solution's
map is `j_𝒜 : a ↦ a, 𝒜ᵒᵖ → 𝒜`, and it shows `M₂ j_𝒜` is positive iff `𝒜` is
commutative.  Since the statement fixes the domain to be `M₂(ℂ)` and not a
type synonym for its opposite, `j_𝒜` is transported here along the canonical
isomorphism `M₂(ℂ)ᵒᵖ ≅ M₂(ℂ)`, which is transposition: `transposeM2` *is*
`j_{M₂(ℂ)}`.

The argument is then the solution's own, step for step.  Given `a`, the
matrix `[[1, b], [b*, b* b]]` over the domain is positive by **33II**.3
(`cstar_matrix_star_mul_nonneg` at the vector `(1, b)`), where `b := aᵀ`; if
`M₂ j` were positive its image `[[1, a], [a*, a a*]]` would be positive too,
and Cauchy–Schwarz for the inner product `⟨v,w⟩ = v* A w` on `𝒜²` — here
`pos_matrix_cs` — gives `a* a ≤ ‖1‖ (a a*) = a a*`.  As the solution notes,
applying this to `a*` as well turns the inequality into `a* a = a a*`, so
every element of `M₂(ℂ)` would be normal.  It is not: `e₀₁* e₀₁ = e₁₁` while
`e₀₁ e₀₁* = e₀₀`. -/
theorem mnf_not_positive :
    ∃ f : CStarMatrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ,
      IsPositiveMap f ∧
      ¬∀ A : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin 2) (Fin 2) ℂ),
        0 ≤ A → 0 ≤ A.map ⇑f := by
  refine ⟨transposeM2, transposeM2_pos, ?_⟩
  intro hpos
  -- the solution's inequality `a* a ≤ ‖1‖ (a a*)`, for every `a`
  have hle : ∀ a : CStarMatrix (Fin 2) (Fin 2) ℂ, star a * a ≤ a * star a := by
    intro a
    set b : CStarMatrix (Fin 2) (Fin 2) ℂ := transposeM2 a with hb
    set G : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
      CStarMatrix.ofMatrix (Matrix.of fun i j =>
        star ((![1, b] : Fin 2 → CStarMatrix (Fin 2) (Fin 2) ℂ) i)
          * (![1, b] : Fin 2 → CStarMatrix (Fin 2) (Fin 2) ℂ) j) with hG
    -- `[[1, b], [b*, b* b]]` is positive by **33II**.3
    have hGpos : (0 : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin 2) (Fin 2) ℂ)) ≤ G :=
      cstar_matrix_star_mul_nonneg _
    -- its image under `M₂ j` is `[[1, a], [a*, a a*]]`
    have h00 : (G.map ⇑transposeM2) 0 0 = 1 := by
      ext i j
      simp [hG, CStarMatrix.map_apply, CStarMatrix.ofMatrix_apply, transposeM2_apply,
        CStarMatrix.one_apply, eq_comm]
    have h01 : (G.map ⇑transposeM2) 0 1 = a := by
      ext i j
      simp [hG, hb, CStarMatrix.map_apply, CStarMatrix.ofMatrix_apply, transposeM2_apply]
    have h10 : (G.map ⇑transposeM2) 1 0 = star a := by
      ext i j
      simp [hG, hb, CStarMatrix.map_apply, CStarMatrix.ofMatrix_apply, transposeM2_apply,
        CStarMatrix.star_apply]
    have h11 : (G.map ⇑transposeM2) 1 1 = a * star a := by
      ext i j
      rw [CStarMatrix.map_apply, hG]
      simp only [CStarMatrix.ofMatrix_apply, Matrix.of_apply, Matrix.cons_val_one,
        transposeM2_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply]
      exact Finset.sum_congr rfl fun k _ => mul_comm (star (a j k)) (a i k)
    -- `‖1‖ (a a*) = a a*`
    have hsm : ‖(G.map ⇑transposeM2) 0 0‖ • (G.map ⇑transposeM2) 1 1 = a * star a := by
      rw [h00, h11, norm_one]
      exact one_smul ℝ _
    -- Cauchy--Schwarz for `⟨v,w⟩ = v* A w` on `𝒜²`, at the standard basis
    have hcs := pos_matrix_cs (hpos _ hGpos) 1 0
    rw [h10, h01] at hcs
    exact le_of_le_of_eq hcs hsm
  -- "we not only have `a* a ≤ a a*`, but also `a a* ≤ a* a`, and whence `a* a = a a*`"
  have heq : ∀ a : CStarMatrix (Fin 2) (Fin 2) ℂ, star a * a = a * star a := fun a =>
    le_antisymm (hle a) (by simpa using hle (star a))
  -- but `e₀₁* e₀₁ = e₁₁ ≠ e₀₀ = e₀₁ e₀₁*`
  have hcontra := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) ℂ => M 0 0) (heq e01M2)
  simp [e01M2, CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two,
    CStarMatrix.ofMatrix_apply] at hcontra

/-- The norm of a matrix over a C*-algebra is at most the sum of the norms of
its entries.  (Mathlib proves exactly this inside the private
`antilipschitzWith_toMatrixAux`; it is not exported, so it is repeated here.) -/
private theorem cstarMatrix_norm_le_sum {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) ℬ) :
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [CStarMatrix.toCLM_apply_eq_sum, Finset.sum_mul]
  apply WithCStarModule.pi_norm_le_sum_norm _ |>.trans
  gcongr with j _
  rw [WithCStarModule.equiv_symm_pi_apply]
  apply norm_sum_le _ _ |>.trans
  gcongr with i _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact WithCStarModule.norm_apply_le_norm v i

/-- **33III** (`mnf`, cstar.tex:5358, Exercise), part 3, second clause, in the
form given by erratum `parsec-330.30`: `M_N f` is bounded by `N²‖f‖` when `f`
is bounded.

*Class 2 — different route.*  Solution `parsec-330.30` predates the erratum
and proves nothing about this clause; the argument here is the obvious one —
the norm of a matrix is at most the sum of the `N²` norms of its entries, each
of which is at most `‖f‖‖A‖` by `CStarMatrix.norm_entry_le_norm`. -/
theorem mnf_bounded (f : 𝒜 →L[ℂ] ℬ) (A : CStarMatrix (Fin N) (Fin N) 𝒜) :
    ‖A.map ⇑f‖ ≤ (N : ℝ) ^ 2 * ‖f‖ * ‖A‖ := by
  refine (cstarMatrix_norm_le_sum _).trans ?_
  have hentry : ∀ i j : Fin N, ‖(A.map ⇑f) i j‖ ≤ ‖f‖ * ‖A‖ := by
    intro i j
    rw [CStarMatrix.map_apply]
    refine (f.le_opNorm _).trans ?_
    exact mul_le_mul_of_nonneg_left CStarMatrix.norm_entry_le_norm (norm_nonneg f)
  calc ∑ j : Fin N, ∑ i : Fin N, ‖(A.map ⇑f) i j‖
      ≤ ∑ _j : Fin N, ∑ _i : Fin N, ‖f‖ * ‖A‖ :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hentry i j
    _ = (N : ℝ) ^ 2 * ‖f‖ * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

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
        0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => f (star (a i) * a j))] := by
  tfae_have 1 → 3 := fun h1 a => h1 _ (cstar_matrix_star_mul_nonneg a)
  tfae_have 3 → 2 := fun h3 a b => (cstar_matrix_positive_iff _).mp (h3 a) b
  tfae_have 2 → 1 := by
    intro h2 A hA
    rw [cstar_matrix_positive_iff]
    intro b
    obtain ⟨C, hC⟩ := exists_star_mul_self hA
    have hAij : ∀ i j, A i j = ∑ m, star (C m i) * C m j := by
      intro i j
      rw [hC, CStarMatrix.mul_apply]
      simp [CStarMatrix.star_apply]
    have hstep : ∑ i, ∑ j, star (b i) * (A.map ⇑f) i j * b j
        = ∑ i, ∑ j, ∑ m, star (b i) * f (star (C m i) * C m j) * b j := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [CStarMatrix.map_apply, hAij i j, map_sum, Finset.mul_sum, Finset.sum_mul]
    have hswap : ∑ m, ∑ i, ∑ j, star (b i) * f (star (C m i) * C m j) * b j
        = ∑ i, ∑ j, ∑ m, star (b i) * f (star (C m i) * C m j) * b j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [hstep, ← hswap]
    exact Finset.sum_nonneg fun m _ => h2 (fun i => C m i) b
  tfae_finish

/-- **34IV** (`cp`, cstar.tex:5448, Exercise), part 1: a linear map `f`
between C*-algebras is completely positive iff `M_N f` is positive for every
`N` iff `(f(aᵢ* aⱼ))ᵢⱼ ≥ 0` for every `N` and `a ∈ 𝒜^N`.  (Mathlib's
bundled cp maps `𝒜 →CP ℬ` are defined by the first of these conditions.) -/
theorem cp_iff (f : 𝒜 →ₗ[ℂ] ℬ) :
    List.TFAE [
      IsCompletelyPositiveMap f,
      ∀ (N : ℕ) (A : CStarMatrix (Fin N) (Fin N) 𝒜), 0 ≤ A → 0 ≤ A.map ⇑f,
      ∀ (N : ℕ) (a : Fin N → 𝒜),
        0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => f (star (a i) * a j))] := by
  tfae_have 1 → 2 := fun h1 N => (n_pos f N).out 1 0 |>.mp (h1 N)
  tfae_have 2 → 3 := fun h2 N => (n_pos f N).out 0 2 |>.mp (h2 N)
  tfae_have 3 → 1 := fun h3 N => (n_pos f N).out 2 1 |>.mp (h3 N)
  tfae_finish

/-- **34IV** (`cp`, cstar.tex:5448, Exercise), part 2: the composition of
cp-maps is completely positive. -/
theorem cp_comp {𝒞 : Type*} [CStarAlgebra 𝒞] [PartialOrder 𝒞]
    [StarOrderedRing 𝒞] (f : 𝒜 →ₗ[ℂ] ℬ) (g : ℬ →ₗ[ℂ] 𝒞)
    (hf : IsCompletelyPositiveMap f) (hg : IsCompletelyPositiveMap g) :
    IsCompletelyPositiveMap (g.comp f) := by
  have hf' : ∀ (N : ℕ) (A : CStarMatrix (Fin N) (Fin N) 𝒜), 0 ≤ A → 0 ≤ A.map ⇑f :=
    (cp_iff f).out 0 1 |>.mp hf
  have hg' : ∀ (N : ℕ) (A : CStarMatrix (Fin N) (Fin N) ℬ), 0 ≤ A → 0 ≤ A.map ⇑g :=
    (cp_iff g).out 0 1 |>.mp hg
  refine (cp_iff (g.comp f)).out 1 0 |>.mp fun N A hA => ?_
  exact hg' N _ (hf' N A hA)

/-- **34IV** (`cp`, cstar.tex:5448, Exercise), part 3: every mi-map is
completely positive.

The exercise's hint is "`M_N f` is a mi-map too": that is **33III**.2
(`mnf_inherits`), and a mi-map is positive by **25II**.2
(`astara_pos_basic_2_mi`), so `M_N f` is positive for every `N`, which is
part 1 (`cp_iff`) of this same exercise. -/
theorem cp_of_mi (f : 𝒜 →ₗ[ℂ] ℬ) (hm : IsMultiplicativeMap f)
    (hi : IsInvolutionPreserving f) : IsCompletelyPositiveMap f := by
  refine (cp_iff f).out 1 0 |>.mp fun N A hA => ?_
  have hmi := mnf_inherits (N := N) f
  have hM : IsPositiveMap (CStarMatrix.mapₗ (R := ℂ) (S := ℂ) (n := Fin N) f) :=
    astara_pos_basic_2_mi _ (fun x y => hmi.2.1 hm x y) fun x => hmi.2.2 hi x
  exact hM A hA

/-- **34V** (`ad-cp`, cstar.tex:5463, Exercise), part 1: the map
`b ↦ a* b a : 𝒜 → 𝒜` is completely positive for every `a ∈ 𝒜`. -/
theorem ad_cp_1 (a : 𝒜) :
    IsCompletelyPositiveMap
      ((LinearMap.mulLeft ℂ (star a)).comp (LinearMap.mulRight ℂ a)) := by
  intro n c b
  have h : ∀ i j : Fin n, star (b i) *
      ((LinearMap.mulLeft ℂ (star a)).comp (LinearMap.mulRight ℂ a))
        (star (c i) * c j) * b j
      = star (c i * a * b i) * (c j * a * b j) := by
    intro i j
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, star_mul, star_star]
    simp [mul_assoc]
  simp_rw [h, sum_star_mul_sum]
  exact star_mul_self_nonneg _

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
    IsCompletelyPositiveMap (conjOperator S) := by
  intro n T R
  set d : Fin n → (K →L[ℂ] H) := fun i => (T i).comp (S.comp (R i)) with hd
  have key : ∀ i j : Fin n,
      star (R i) * conjOperator S (star (T i) * T j) * R j
        = (ContinuousLinearMap.adjoint (d i)).comp (d j) := by
    intro i j
    simp only [hd, conjOperator, LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
  simp_rw [key]
  have hsum : ∑ i, ∑ j, (ContinuousLinearMap.adjoint (d i)).comp (d j)
      = (ContinuousLinearMap.adjoint (∑ i, d i)).comp (∑ j, d j) := by
    ext v
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply, map_sum]
    exact Finset.sum_comm
  rw [hsum]
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.isPositive_adjoint_comp_self _)

section AdCPModule

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒜 X] [CStarModule 𝒜 X]
  [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul 𝒜 Y] [CStarModule 𝒜 Y]
  [CompleteSpace Y]

/-- The converse half of **32XV**.2 inside `B^a(X)`: an operator with
positive vector functionals is positive.  (`bax_inner_nonneg` above is the
other half.) -/
private theorem bax_nonneg_of_inner {U : Bax 𝒜 X}
    (h : ∀ x : X, 0 ≤ inner 𝒜 x ((U : X →L[ℂ] X) x)) : 0 ≤ U := by
  obtain ⟨R, R', hRR', hU⟩ := (chilb_vector_states_2 (U : X →L[ℂ] X) U.2).mp h
  set A : Bax 𝒜 X := ⟨R, ⟨⇑R', hRR'⟩⟩ with hA
  have hstar : ((star A : Bax 𝒜 X) : X →L[ℂ] X) = R' :=
    ContinuousLinearMap.ext fun x =>
      congrFun (moduleAdjointTo_unique (𝒜 := 𝒜) ⇑R _ _ (bax_star_spec A) hRR') x
  have hUA : U = star A * A := by
    refine Subtype.ext ?_
    show (U : X →L[ℂ] X) = ((star A : Bax 𝒜 X) : X →L[ℂ] X) * (A : X →L[ℂ] X)
    rw [hstar, hU]
    rfl
  rw [hUA]
  exact star_mul_self_nonneg _

/-- **34V** (`ad-cp`, cstar.tex:5463, Exercise), part 2: the map
`T ↦ S* T S : 𝓑^a(X) → 𝓑^a(Y)` of an adjointable bounded module map
`S : Y → X` between Hilbert 𝒜-modules, as a linear map. -/
noncomputable def conjModule (S : Y →L[ℂ] X) (S' : X →L[ℂ] Y)
    (hS : ModuleAdjointTo 𝒜 ⇑S ⇑S') : Bax 𝒜 X →ₗ[ℂ] Bax 𝒜 Y where
  toFun T := ⟨S'.comp ((T : X →L[ℂ] X).comp S), by
    refine ⟨⇑S' ∘ (⇑((star T : Bax 𝒜 X) : X →L[ℂ] X) ∘ ⇑S), ?_⟩
    have h1 : ModuleAdjointTo 𝒜 (⇑S' ∘ ⇑(T : X →L[ℂ] X))
        (⇑((star T : Bax 𝒜 X) : X →L[ℂ] X) ∘ ⇑S) :=
      moduleAdjointTo_comp (⇑(T : X →L[ℂ] X)) (⇑S') _ (⇑S)
        (bax_star_spec T) (moduleAdjointTo_symm _ _ hS)
    exact moduleAdjointTo_comp (⇑S) (⇑S' ∘ ⇑(T : X →L[ℂ] X)) (⇑S') _ hS h1⟩
  map_add' T T' := by
    refine Subtype.ext (ContinuousLinearMap.ext fun y => ?_)
    simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_smul' c T := by
    refine Subtype.ext (ContinuousLinearMap.ext fun y => ?_)
    simp

@[simp] theorem conjModule_apply (S : Y →L[ℂ] X) (S' : X →L[ℂ] Y)
    (hS : ModuleAdjointTo 𝒜 ⇑S ⇑S') (T : Bax 𝒜 X) (y : Y) :
    ((conjModule S S' hS T : Bax 𝒜 Y) : Y →L[ℂ] Y) y
      = S' ((T : X →L[ℂ] X) (S y)) := rfl

/-- **34V** (`ad-cp`, cstar.tex:5463, Exercise), part 2, as the Exercise
states it: `T ↦ S* T S : 𝓑^a(X) → 𝓑^a(Y)` is completely positive for every
adjointable operator `S : Y → X` between **Hilbert 𝒜-modules**.  (`ad_cp_2`
below is the Hilbert-space case `𝒜 = ℂ`, which is what the rest of the tree
uses.)

*Class 1 — faithful.*  The computation of solution `parsec-340.50`(2): with
`dᵢ := Tᵢ S Rᵢ : Y → X`, the sum `∑ᵢⱼ Rᵢ* S* Tᵢ* Tⱼ S Rⱼ` has vector
functionals `⟨y, ∑ᵢⱼ …⟩ = ⟨∑ᵢ dᵢ y, ∑ⱼ dⱼ y⟩ ≥ 0`, and positivity in
`𝓑^a(Y)` follows by **32XV**.2. -/
theorem ad_cp_2_module (S : Y →L[ℂ] X) (S' : X →L[ℂ] Y)
    (hS : ModuleAdjointTo 𝒜 ⇑S ⇑S') :
    IsCompletelyPositiveMap (conjModule S S' hS) := by
  intro n T R
  set d : Fin n → (Y →L[ℂ] X) :=
    fun i => ((T i : X →L[ℂ] X).comp S).comp ((R i : Y →L[ℂ] Y)) with hd
  refine bax_nonneg_of_inner fun y => ?_
  have key : ∀ i j : Fin n,
      inner 𝒜 y (((star (R i) * conjModule S S' hS (star (T i) * T j) * R j :
          Bax 𝒜 Y) : Y →L[ℂ] Y) y)
        = inner 𝒜 (d i y) (d j y) := by
    intro i j
    have e1 : ((star (R i) * conjModule S S' hS (star (T i) * T j) * R j :
        Bax 𝒜 Y) : Y →L[ℂ] Y) y
        = ((star (R i) : Bax 𝒜 Y) : Y →L[ℂ] Y)
            (S' (((star (T i) : Bax 𝒜 X) : X →L[ℂ] X)
              ((T j : X →L[ℂ] X) (S (((R j : Bax 𝒜 Y) : Y →L[ℂ] Y) y))))) := rfl
    rw [e1, ← bax_star_spec (R i), ← hS, ← bax_star_spec (T i)]
    rfl
  have hsum : ((∑ i, ∑ j, star (R i) * conjModule S S' hS (star (T i) * T j) * R j :
      Bax 𝒜 Y) : Y →L[ℂ] Y) y
      = ∑ i, ∑ j, ((star (R i) * conjModule S S' hS (star (T i) * T j) * R j :
        Bax 𝒜 Y) : Y →L[ℂ] Y) y := by
    push_cast
    simp
  rw [hsum, CStarModule.inner_sum_right]
  simp_rw [CStarModule.inner_sum_right]
  simp_rw [key]
  simp_rw [← CStarModule.inner_sum_right]
  rw [← CStarModule.inner_sum_left]
  exact CStarModule.inner_self_nonneg

end AdCPModule

/-- **34V** (`ad-cp`, cstar.tex:5463, Exercise), part 3: the vector
functional `T ↦ ⟨x, Tx⟩ : B(H) → ℂ` is completely positive. -/
theorem ad_cp_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (x : H) :
    IsCompletelyPositiveMap (vectorFunctional x) := by
  intro n T c
  have key : ∀ i j : Fin n,
      star (c i) * vectorFunctional x (star (T i) * T j) * c j
        = inner ℂ (c i • T i x) (c j • T j x) := by
    intro i j
    rw [vectorFunctional_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right,
      inner_smul_left, inner_smul_right]
    simp only [RCLike.star_def]
    ring
  simp_rw [key, ← inner_sum, ← sum_inner]
  exact CStarModule.inner_self_nonneg

/-- An element of `⊕ᵢ 𝒜ᵢ = lp 𝒜 ∞` with positive coordinates is positive: the
coordinatewise square roots are again uniformly bounded, since
`‖√(xᵢ)‖ = ‖xᵢ‖^{1/2} ≤ ‖x‖^{1/2}`. -/
private theorem lp_infty_nonneg {ι : Type*} {𝒜f : ι → Type*}
    [∀ i, CStarAlgebra (𝒜f i)] [∀ i, PartialOrder (𝒜f i)]
    [∀ i, StarOrderedRing (𝒜f i)]
    [PartialOrder (lp 𝒜f ∞)] [StarOrderedRing (lp 𝒜f ∞)]
    (x : lp 𝒜f ∞) (h : ∀ i, 0 ≤ (x : ∀ i, 𝒜f i) i) : 0 ≤ x := by
  have hsa : ∀ i, star (CFC.sqrt ((x : ∀ i, 𝒜f i) i)) = CFC.sqrt ((x : ∀ i, 𝒜f i) i) :=
    fun i => (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have hnorm : ∀ i, ‖CFC.sqrt ((x : ∀ i, 𝒜f i) i)‖ = Real.sqrt ‖(x : ∀ i, 𝒜f i) i‖ := by
    intro i
    have h2 : ‖CFC.sqrt ((x : ∀ i, 𝒜f i) i)‖ * ‖CFC.sqrt ((x : ∀ i, 𝒜f i) i)‖
        = ‖(x : ∀ i, 𝒜f i) i‖ := by
      rw [← CStarRing.norm_star_mul_self, hsa i, CFC.sqrt_mul_sqrt_self _ (h i)]
    rw [← h2, Real.sqrt_mul_self (norm_nonneg _)]
  have hmem : Memℓp (fun i => CFC.sqrt ((x : ∀ i, 𝒜f i) i)) ∞ := by
    refine memℓp_infty_iff.mpr ⟨Real.sqrt ‖x‖, ?_⟩
    rintro y ⟨i, rfl⟩
    change ‖CFC.sqrt ((x : ∀ i, 𝒜f i) i)‖ ≤ Real.sqrt ‖x‖
    rw [hnorm i]
    exact Real.sqrt_le_sqrt (lp.norm_apply_le_norm ENNReal.top_ne_zero x i)
  have hx : x = star (⟨_, hmem⟩ : lp 𝒜f ∞) * ⟨_, hmem⟩ := by
    refine lp.ext (funext fun i => ?_)
    rw [lp.infty_coeFn_mul, Pi.mul_apply, lp.coeFn_star, Pi.star_apply]
    exact (by rw [hsa i, CFC.sqrt_mul_sqrt_self _ (h i)] : _ = (x : ∀ i, 𝒜f i) i).symm
  rw [hx]
  exact star_mul_self_nonneg _

/-- **34VI** (`cstar-product-4`, cstar.tex:5486, Exercise), part 1: the
direct sum `⊕ᵢ 𝒜ᵢ` is the product in `CStar_cpsu`: every family of cpsu-maps
`fᵢ : ℬ → 𝒜ᵢ` factors uniquely through the projections by a cpsu-map.
(Complete positivity and subunitality of the mediating map `g` are spelled
out, since Mathlib does not register a unital C*-algebra instance on
`lp 𝒜 ∞` in the non-commutative case.)

That the projections are themselves cpsu — the other half of the universal
property — is `cstar_product_4_proj` below.  Part 2 of the exercise, that the
equaliser of two miu-maps in `CStar_cpsu` is the obvious one, is not
converted; solution `parsec-340.60` is `\TODO{}`, so the thesis gives no
proof for either part. -/
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
      ∀ (i : ι) (b : ℬ), (g b : ∀ i, 𝒜f i) i = f i b := by
  -- `‖fᵢ(b)‖ ≤ 2 ‖fᵢ(1)‖ ‖b‖ ≤ 2 ‖b‖` by **20II**, so `b ↦ (fᵢ(b))ᵢ` lands in `⊕ᵢ 𝒜ᵢ`
  have hf1 : ∀ i, ‖f i 1‖ ≤ 1 := by
    intro i
    have hp : IsPositiveMap (f i) := astara_pos_basic_2_cp (f i) (hcp i)
    have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le (hp 1 zero_le_one) (hsu i)
    rwa [CStarRing.norm_one] at h
  have hb : ∀ (b : ℬ) (i : ι), ‖f i b‖ ≤ 2 * ‖b‖ := by
    intro b i
    calc ‖f i b‖ ≤ 2 * ‖f i 1‖ * ‖b‖ :=
          weak_russo_dye_2 (f i) (astara_pos_basic_2_cp (f i) (hcp i)) b
      _ ≤ 2 * 1 * ‖b‖ := by gcongr; exact hf1 i
      _ = 2 * ‖b‖ := by ring
  have hmem : ∀ b : ℬ, Memℓp (fun i => f i b) ∞ := fun b =>
    memℓp_infty_iff.mpr ⟨2 * ‖b‖, by rintro y ⟨i, rfl⟩; exact hb b i⟩
  set g : ℬ →ₗ[ℂ] lp 𝒜f ∞ :=
    { toFun := fun b => ⟨fun i => f i b, hmem b⟩
      map_add' := fun b b' => by
        refine lp.ext (funext fun i => ?_)
        rw [lp.coeFn_add]
        exact map_add (f i) b b'
      map_smul' := fun z b => by
        refine lp.ext (funext fun i => ?_)
        rw [lp.coeFn_smul]
        exact map_smul (f i) z b } with hgdef
  have hgi : ∀ (i : ι) (b : ℬ), (g b : ∀ i, 𝒜f i) i = f i b := fun _ _ => rfl
  refine ⟨g, ⟨fun n a c => ?_, ?_, hgi⟩, fun g' hg' => ?_⟩
  · refine lp_infty_nonneg _ fun i => ?_
    have hco : ((∑ k, ∑ l, star (c k) * g (star (a k) * a l) * c l : lp 𝒜f ∞) :
        ∀ i, 𝒜f i) i
        = ∑ k, ∑ l, star ((c k : ∀ i, 𝒜f i) i) * f i (star (a k) * a l)
            * (c l : ∀ i, 𝒜f i) i := by
      simp only [lp.coeFn_sum, Finset.sum_apply, lp.infty_coeFn_mul, lp.coeFn_star,
        Pi.mul_apply, Pi.star_apply, hgi]
    rw [hco]
    exact hcp i n a fun k => (c k : ∀ i, 𝒜f i) i
  · rw [← sub_nonneg]
    refine lp_infty_nonneg _ fun i => ?_
    rw [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_one, Pi.one_apply, hgi]
    exact sub_nonneg.mpr (hsu i)
  · obtain ⟨-, -, hg'i⟩ := hg'
    refine LinearMap.ext fun b => lp.ext (funext fun i => ?_)
    rw [hg'i i b, hgi i b]

/-! **34VI** (`cstar-product-4`, cstar.tex:5486, Exercise), part 2: the
equaliser of miu-maps `f, g : 𝒜 → ℬ` in `CStar_cpsu` is (the inclusion of)
the C*-subalgebra `{a : f(a) = g(a)}` — which is a closed subalgebra by
**20aII** (`cstar_equaliser_1`); the universal property amounts to: every
cpsu-map `h : 𝒞 → 𝒜` with `f ∘ h = g ∘ h` corestricts to it, which is
set-theoretically immediate.  Not converted beyond **20aII**. -/

section CCStarPosMat

/-- **34VI** (`cstar-product-4`, cstar.tex:5486, Exercise), part 1, the
projections: the coordinate maps `π_i : ⊕ⱼ 𝒜ⱼ → 𝒜ᵢ` are miu-maps, hence
cpsu (indeed cpu).  Together with `cstar_product_4` above this says that
`⊕ᵢ 𝒜ᵢ`
*with these projections* is the product in `CStar_cpsu`; they are the same
projections as in **20aII**, being given by `x ↦ x i`.

*Class 1 — faithful.*  Multiplicativity, involution preservation and
unitality are read off the pointwise operations on `lp 𝒜f ∞`, and complete
positivity then follows by **34IX**.1 `cp_of_mi`. -/
theorem cstar_product_4_proj {ι : Type*} {𝒜f : ι → Type*}
    [∀ i, CStarAlgebra (𝒜f i)] [∀ i, Nontrivial (𝒜f i)]
    [∀ i, PartialOrder (𝒜f i)] [∀ i, StarOrderedRing (𝒜f i)]
    [PartialOrder (lp 𝒜f ∞)] [StarOrderedRing (lp 𝒜f ∞)] (i : ι) :
    ∃ π : lp 𝒜f ∞ →ₗ[ℂ] 𝒜f i,
      (∀ x : lp 𝒜f ∞, π x = (x : ∀ j, 𝒜f j) i) ∧
      IsMultiplicativeMap π ∧ IsInvolutionPreserving π ∧ π 1 = 1 ∧
      IsCompletelyPositiveMap π ∧ Subunital ⇑π := by
  set π : lp 𝒜f ∞ →ₗ[ℂ] 𝒜f i :=
    { toFun := fun x => (x : ∀ j, 𝒜f j) i
      map_add' := fun x y => by rw [lp.coeFn_add]; rfl
      map_smul' := fun c x => by rw [lp.coeFn_smul]; rfl } with hπ
  have hm : IsMultiplicativeMap π := fun x y => by
    show ((x * y : lp 𝒜f ∞) : ∀ j, 𝒜f j) i = _
    rw [lp.infty_coeFn_mul]; rfl
  have hi : IsInvolutionPreserving π := fun x => by
    show ((star x : lp 𝒜f ∞) : ∀ j, 𝒜f j) i = _
    rw [lp.coeFn_star]; rfl
  have hu : π 1 = 1 := by
    show ((1 : lp 𝒜f ∞) : ∀ j, 𝒜f j) i = 1
    rw [lp.infty_coeFn_one]; rfl
  exact ⟨π, fun _ => rfl, hm, hi, hu, cp_of_mi π hm hi, le_of_eq hu⟩

/-- An element of a commutative C*-algebra is positive as soon as every character
maps it to a nonnegative complex number: by Gelfand duality it is `star g * g`
for the continuous function `g = √(φ ↦ φ x)`. -/
private theorem nonneg_of_forall_character {𝒞 : Type*} [CommCStarAlgebra 𝒞]
    [PartialOrder 𝒞] [StarOrderedRing 𝒞] {x : 𝒞}
    (h : ∀ φ : WeakDual.characterSpace ℂ 𝒞, 0 ≤ φ x) : 0 ≤ x := by
  set e := gelfandStarTransform 𝒞 with he
  set G : C(WeakDual.characterSpace ℂ 𝒞, ℂ) := e x with hG
  have hGφ : ∀ φ, G φ = φ x := fun φ => rfl
  set g : C(WeakDual.characterSpace ℂ 𝒞, ℂ) :=
    ⟨fun φ => (Real.sqrt (G φ).re : ℂ),
      Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (Complex.continuous_re.comp G.continuous))⟩ with hg
  have hgx : star g * g = e x := by
    ext φ
    have h1 : (0 : ℝ) ≤ (G φ).re := by rw [hGφ]; exact (Complex.nonneg_iff.mp (h φ)).1
    have h2 : (G φ) = (((G φ).re : ℝ) : ℂ) := by
      rw [hGφ]; exact Complex.eq_re_of_ofReal_le (r := 0) (by simpa using h φ)
    simp only [hg, ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.coe_mk,
      RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt h1]
    exact h2.symm
  have hx : x = star (e.symm g) * e.symm g := by
    rw [← map_star, ← map_mul, hgx, StarAlgEquiv.symm_apply_apply]
  rw [hx]
  exact star_mul_self_nonneg _

/-- A simple tensor `a ⊗ B` of positives is positive. -/
private theorem tensor_nonneg {𝒟 : Type*} [CStarAlgebra 𝒟] [PartialOrder 𝒟]
    [StarOrderedRing 𝒟] {n : ℕ}
    [PartialOrder (CStarMatrix (Fin n) (Fin n) 𝒟)]
    [StarOrderedRing (CStarMatrix (Fin n) (Fin n) 𝒟)]
    {a : 𝒟} (ha : 0 ≤ a) {B : CStarMatrix (Fin n) (Fin n) ℂ} (hB : 0 ≤ B) :
    0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => B i j • a) := by
  obtain ⟨x, rfl⟩ := exists_star_mul_self ha
  obtain ⟨C, rfl⟩ := exists_star_mul_self hB
  set M : CStarMatrix (Fin n) (Fin n) 𝒟 :=
    CStarMatrix.ofMatrix (Matrix.of fun i j => C i j • x) with hM
  have h : CStarMatrix.ofMatrix
      (Matrix.of fun i j => (star C * C) i j • (star x * x)) = star M * M := by
    ext i j
    rw [CStarMatrix.mul_apply, CStarMatrix.ofMatrix_apply, Matrix.of_apply]
    simp only [CStarMatrix.star_apply, hM, CStarMatrix.ofMatrix_apply, Matrix.of_apply,
      CStarMatrix.mul_apply, Finset.sum_smul, star_smul, RCLike.star_def]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_smul_comm]
  rw [h]
  exact star_mul_self_nonneg M


section Comm

variable {𝒞 : Type*} [CommCStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]

/-- Characters are positive. -/
private theorem character_nonneg (φ : WeakDual.characterSpace ℂ 𝒞) {x : 𝒞} (hx : 0 ≤ x) :
    0 ≤ φ x := by
  obtain ⟨y, rfl⟩ := exists_star_mul_self hx
  have hs : φ (star y) = star (φ y) := by
    have := congrFun (congrArg (fun (F : C(WeakDual.characterSpace ℂ 𝒞, ℂ)) => F.toFun)
      (map_star (gelfandStarTransform 𝒞) y)) φ
    exact this
  rw [map_mul, hs]
  exact star_mul_self_nonneg _

private theorem character_conj (φ : WeakDual.characterSpace ℂ 𝒞) (x : 𝒞) :
    φ (star x) = star (φ x) :=
  congrFun (congrArg (fun (F : C(WeakDual.characterSpace ℂ 𝒞, ℂ)) => F.toFun)
    (map_star (gelfandStarTransform 𝒞) x)) φ

variable {n : ℕ} [PartialOrder (CStarMatrix (Fin n) (Fin n) 𝒞)]
  [StarOrderedRing (CStarMatrix (Fin n) (Fin n) 𝒞)]

/-- A matrix over a commutative C*-algebra is positive iff it is pointwise positive
on the character space. -/
private theorem matrix_nonneg_iff_character (A : CStarMatrix (Fin n) (Fin n) 𝒞) :
    0 ≤ A ↔ ∀ (φ : WeakDual.characterSpace ℂ 𝒞) (v : Fin n → ℂ),
      0 ≤ ∑ i, ∑ j, star (v i) * φ (A i j) * v j := by
  rw [cstar_matrix_positive_iff]
  constructor
  · intro h φ v
    have hv := h (fun i => algebraMap ℂ 𝒞 (v i))
    have := character_nonneg φ hv
    rw [map_sum] at this
    simp only [map_sum, map_mul, character_conj, AlgHomClass.commutes] at this
    exact this
  · intro h a
    refine nonneg_of_forall_character fun φ => ?_
    have := h φ (fun i => φ (a i))
    rw [map_sum]
    simp only [map_sum, map_mul, character_conj]
    exact this

end Comm


open WithCStarModule CStarMatrix Finset in
/-- The C*-matrix norm is at most the sum of the norms of the entries.  (Mathlib
proves this inside a `private` lemma of `Analysis/CStarAlgebra/CStarMatrix.lean`;
the proof is repeated here because it is not exported.) -/
private theorem norm_le_sum_norm_entry {n : ℕ} {𝒟 : Type*} [CStarAlgebra 𝒟] [PartialOrder 𝒟]
    [StarOrderedRing 𝒟] (M : CStarMatrix (Fin n) (Fin n) 𝒟) :
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [toCLM_apply_eq_sum, Finset.sum_mul]
  apply pi_norm_le_sum_norm _ |>.trans
  gcongr with i _
  simp only [equiv_symm_pi_apply]
  apply norm_sum_le _ _ |>.trans
  gcongr with j _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact norm_apply_le_norm v j


section Approx

private theorem cstarMatrix_sum_apply {𝒟 : Type*} [CStarAlgebra 𝒟] {n K : ℕ}
    (s : Finset (Fin K)) (M : Fin K → CStarMatrix (Fin n) (Fin n) 𝒟) (i j : Fin n) :
    (∑ k ∈ s, M k) i j = ∑ k ∈ s, M k i j := by
  classical
  induction s using Finset.induction with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl



variable {𝒞 : Type*} [CommCStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]

/-- In a commutative C*-algebra the norm is the sup over the character space.
(The isometry is **27XVIII**.1 `gelfand_representation_isometry`, not
Mathlib's `gelfandTransform_isometry`: the latter reaches the character space
through maximal *ring* ideals, the route **16VIII** rejects.) -/
private theorem norm_le_of_forall_character {x : 𝒞} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : WeakDual.characterSpace ℂ 𝒞, ‖φ x‖ ≤ C) : ‖x‖ ≤ C := by
  have hiso : ‖WeakDual.gelfandTransform ℂ 𝒞 x‖ = ‖x‖ :=
    gelfand_representation_isometry x
  rw [← hiso, ContinuousMap.norm_le _ hC]
  exact h

variable {n : ℕ} [PartialOrder (CStarMatrix (Fin n) (Fin n) 𝒞)]
  [StarOrderedRing (CStarMatrix (Fin n) (Fin n) 𝒞)]

private theorem exists_approx (A : CStarMatrix (Fin n) (Fin n) 𝒞) (hA : 0 ≤ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (K : ℕ) (a : Fin K → 𝒞) (B : Fin K → CStarMatrix (Fin n) (Fin n) ℂ),
      (∀ k, 0 ≤ a k) ∧ (∀ k, 0 ≤ B k) ∧
      ‖A - ∑ k, CStarMatrix.ofMatrix (Matrix.of fun i j => B k i j • a k)‖ ≤ ε := by
  classical
  set X := WeakDual.characterSpace ℂ 𝒞 with hX
  set δ : ℝ := ε / (n * n + 1) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  set F : Fin n → Fin n → C(X, ℂ) := fun i j => gelfandStarTransform 𝒞 (A i j) with hF
  have hFφ : ∀ i j (φ : X), F i j φ = φ (A i j) := fun _ _ _ => rfl
  set U : X → Set X := fun x => ⋂ i, ⋂ j, {φ : X | ‖F i j φ - F i j x‖ < δ} with hU
  have hUopen : ∀ x, IsOpen (U x) := by
    intro x
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact isOpen_lt (by fun_prop) continuous_const
  have hUmem : ∀ x, x ∈ U x := by
    intro x
    simp only [hU, Set.mem_iInter, Set.mem_setOf_eq, sub_self, norm_zero]
    exact fun _ _ => hδ0
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hUmem x⟩)
  -- a partition of unity subordinate to the finite subcover
  obtain ⟨pu, hpu⟩ := PartitionOfUnity.exists_isSubordinate (ι := {x // x ∈ t})
    (isClosed_univ (X := X)) (fun k => U k.1) (fun k => hUopen k.1) (by
      intro x _
      obtain ⟨y, hyt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
      exact Set.mem_iUnion.mpr ⟨⟨y, hyt⟩, hxU⟩)
  obtain ⟨K, ⟨e⟩⟩ : ∃ K : ℕ, Nonempty (Fin K ≃ {x // x ∈ t}) :=
    ⟨_, ⟨(Fintype.equivFin _).symm⟩⟩
  set cf : Fin K → C(X, ℂ) := fun k =>
    ⟨fun φ => ((pu (e k) φ : ℝ) : ℂ),
      Complex.continuous_ofReal.comp (pu (e k)).continuous⟩ with hcf
  set g : Fin K → 𝒞 := fun k => (gelfandStarTransform 𝒞).symm (cf k) with hg
  set Bm : Fin K → CStarMatrix (Fin n) (Fin n) ℂ := fun k =>
    CStarMatrix.ofMatrix (Matrix.of fun i j => F i j (e k).1) with hBm
  have hgφ : ∀ (k : Fin K) (φ : X), φ (g k) = ((pu (e k) φ : ℝ) : ℂ) := by
    intro k φ
    have h := StarAlgEquiv.apply_symm_apply (gelfandStarTransform 𝒞) (cf k)
    exact congrFun (congrArg (fun (G : C(X, ℂ)) => G.toFun) h) φ
  have hBmij : ∀ (k : Fin K) (i j : Fin n), Bm k i j = (e k).1 (A i j) := fun _ _ _ => rfl
  have hsum1 : ∀ φ : X, ∑ k : Fin K, pu (e k) φ = 1 := by
    intro φ
    rw [Equiv.sum_comp e (fun i => pu i φ), ← finsum_eq_sum_of_fintype]
    exact pu.sum_eq_one (Set.mem_univ φ)
  refine ⟨K, g, Bm, ?_, ?_, ?_⟩
  · intro k
    refine nonneg_of_forall_character fun φ => ?_
    rw [hgφ k φ]
    simpa using pu.nonneg (e k) φ
  · intro k
    rw [cstar_matrix_positive_iff]
    intro v
    simp only [hBmij]
    exact (matrix_nonneg_iff_character A).mp hA (e k).1 v
  · have hentry : ∀ i j : Fin n,
        ‖(A - ∑ k : Fin K,
            CStarMatrix.ofMatrix (Matrix.of fun i j => Bm k i j • g k)) i j‖ ≤ δ := by
      intro i j
      refine norm_le_of_forall_character hδ0.le fun φ => ?_
      have hij : (A - ∑ k : Fin K,
          CStarMatrix.ofMatrix (Matrix.of fun i j => Bm k i j • g k)) i j
          = A i j - ∑ k : Fin K, Bm k i j • g k := by
        rw [CStarMatrix.sub_apply, cstarMatrix_sum_apply]
        rfl
      rw [hij, map_sub, map_sum]
      have hterm : ∀ k : Fin K,
          φ (Bm k i j • g k) = ((pu (e k) φ : ℝ) : ℂ) * (F i j (e k).1) := by
        intro k
        rw [map_smul, hgφ k φ, smul_eq_mul, hBmij k i j, mul_comm]
        rfl
      simp only [hterm]
      have hAij : φ (A i j) = F i j φ := rfl
      have hkey : φ (A i j) - ∑ k : Fin K, ((pu (e k) φ : ℝ) : ℂ) * (F i j (e k).1)
          = ∑ k : Fin K, ((pu (e k) φ : ℝ) : ℂ) * (F i j φ - F i j (e k).1) := by
        have h1 : (∑ k : Fin K, ((pu (e k) φ : ℝ) : ℂ)) = 1 := by
          rw [← Complex.ofReal_sum, hsum1 φ, Complex.ofReal_one]
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul, hAij]
      rw [hkey]
      calc ‖∑ k : Fin K, ((pu (e k) φ : ℝ) : ℂ) * (F i j φ - F i j (e k).1)‖
          ≤ ∑ k : Fin K, ‖((pu (e k) φ : ℝ) : ℂ) * (F i j φ - F i j (e k).1)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ k : Fin K, pu (e k) φ * δ := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (pu.nonneg (e k) φ)]
            rcases eq_or_ne (pu (e k) φ) 0 with h0 | h0
            · rw [h0]; simp
            · refine mul_le_mul_of_nonneg_left ?_ (pu.nonneg (e k) φ)
              have hmem : φ ∈ U (e k).1 := hpu (e k) (subset_tsupport _ (show φ ∈ Function.support (pu (e k)) from h0))
              exact le_of_lt (Set.mem_iInter.mp (Set.mem_iInter.mp hmem i) j)
        _ = δ := by rw [← Finset.sum_mul, hsum1 φ, one_mul]
    calc ‖A - ∑ k : Fin K, CStarMatrix.ofMatrix (Matrix.of fun i j => Bm k i j • g k)‖
        ≤ ∑ _j : Fin n, ∑ _i : Fin n, δ := by
          refine le_trans (norm_le_sum_norm_entry _) ?_
          gcongr with j _ i _
          exact hentry i j
      _ ≤ ε := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hpos : (0:ℝ) < (n:ℝ) * n + 1 := by positivity
          have hre : (n:ℝ) * ((n:ℝ) * (ε / ((n:ℝ) * n + 1)))
              = ((n:ℝ) * n * ε) / ((n:ℝ) * n + 1) := by ring
          rw [hδ, hre, div_le_iff₀ hpos]
          nlinarith [hε.le]

end Approx

end CCStarPosMat

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
      {A : CStarMatrix (Fin N) (Fin N) 𝒜 | 0 ≤ A} := by
  refine Set.Subset.antisymm ?_ ?_
  · have hcl : IsClosed {A : CStarMatrix (Fin N) (Fin N) 𝒜 | 0 ≤ A} :=
      CStarAlgebra.isClosed_nonneg
    refine hcl.closure_subset_iff.mpr ?_
    rintro A ⟨K, a, B, ha, hB, rfl⟩
    exact Finset.sum_nonneg (s := (Finset.univ : Finset (Fin K)))
      (f := fun k => CStarMatrix.ofMatrix (Matrix.of fun i j => B k i j • a k))
      (fun k _ => tensor_nonneg (ha k) (hB k))
  · intro A hA
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨K, a, B, ha, hB, hnorm⟩ := exists_approx A hA (half_pos hε)
    refine ⟨_, ⟨K, a, B, ha, hB, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    linarith

section CPDom

variable {𝒞 : Type*} [CommCStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]

private theorem gen_mem (f : 𝒞 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) {n : ℕ}
    (b : Fin n → ℬ) (c : 𝒞) (hc : 0 ≤ c) (B : CStarMatrix (Fin n) (Fin n) ℂ) (hB : 0 ≤ B) :
    0 ≤ ∑ i, ∑ j, star (b i) * f ((B i j) • c) * b j := by
  obtain ⟨d, hd⟩ := exists_star_mul_self (hf c hc)
  obtain ⟨C, rfl⟩ := exists_star_mul_self hB
  have hexp : ∀ i j : Fin n, star (b i) * f (((star C * C) i j) • c) * b j
      = ∑ l, ((starRingEnd ℂ) (C l i) * C l j) • (star (d * b i) * (d * b j)) := by
    intro i j
    rw [map_smul, mul_smul_comm, smul_mul_assoc, hd]
    have hCC : (star C * C) i j = ∑ l, (starRingEnd ℂ) (C l i) * C l j := by
      rw [CStarMatrix.mul_apply]
      exact Finset.sum_congr rfl fun l _ => rfl
    rw [hCC, Finset.sum_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    rw [star_mul]
    noncomm_ring
  have hsum : ∑ i, ∑ j, star (b i) * f (((star C * C) i j) • c) * b j
      = ∑ l, star (∑ i, (C l i) • (d * b i)) * (∑ j, (C l j) • (d * b j)) := by
    have hswap : ∀ G : Fin n → Fin n → Fin n → ℬ,
        ∑ i, ∑ j, ∑ l, G i j l = ∑ l, ∑ i, ∑ j, G i j l := by
      intro G
      calc ∑ i, ∑ j, ∑ l, G i j l = ∑ i, ∑ l, ∑ j, G i j l :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ l, ∑ i, ∑ j, G i j l := Finset.sum_comm
    simp only [hexp]
    rw [hswap]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
    rfl
  rw [hsum]
  exact Finset.sum_nonneg fun l _ => star_mul_self_nonneg _

private theorem sum_comm3 {M : Type*} [AddCommMonoid M] {n K : ℕ}
    (G : Fin n → Fin n → Fin K → M) :
    ∑ i, ∑ j, ∑ l, G i j l = ∑ l, ∑ i, ∑ j, G i j l := by
  calc ∑ i, ∑ j, ∑ l, G i j l = ∑ i, ∑ l, ∑ j, G i j l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ j, G i j l := Finset.sum_comm


end CPDom

/-- **34IX** (`cp-commutative`, cstar.tex:5563, Proposition), case 1: a
positive map into a commutative C*-algebra is completely positive. -/
theorem cp_commutative_cod {𝒞 : Type*} [CommCStarAlgebra 𝒞] [PartialOrder 𝒞]
    [StarOrderedRing 𝒞] (f : 𝒜 →ₗ[ℂ] 𝒞) (hf : IsPositiveMap f) :
    IsCompletelyPositiveMap f := by
  intro n a b
  refine nonneg_of_forall_character fun φ => ?_
  -- `ω(∑ᵢⱼ bᵢ* f(aᵢ* aⱼ) bⱼ) = ω(f(c* c))` for `c = ∑ᵢ ω(bᵢ) aᵢ`
  set c : 𝒜 := ∑ i, φ (b i) • a i with hc
  have hcc : (star c * c : 𝒜)
      = ∑ i, ∑ j, (star (φ (b i)) * φ (b j)) • (star (a i) * a j) := by
    rw [hc, star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hkey : φ (∑ i, ∑ j, star (b i) * f (star (a i) * a j) * b j) = φ (f (star c * c)) := by
    rw [hcc]
    simp only [map_sum, map_smul, smul_eq_mul, map_mul, map_star, RCLike.star_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hkey]
  obtain ⟨w, hw⟩ := exists_star_mul_self (hf _ (star_mul_self_nonneg c))
  rw [hw, map_mul, map_star]
  exact star_mul_self_nonneg _

/-- **34IX** (`cp-commutative`, cstar.tex:5563, Proposition), case 2: a
positive map out of a commutative C*-algebra is completely positive. -/
theorem cp_commutative_dom {𝒞 : Type*} [CommCStarAlgebra 𝒞] [PartialOrder 𝒞]
    [StarOrderedRing 𝒞] (f : 𝒞 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) :
    IsCompletelyPositiveMap f := by
  intro n a b
  letI : PartialOrder (CStarMatrix (Fin n) (Fin n) 𝒞) :=
    CStarAlgebra.spectralOrder (CStarMatrix (Fin n) (Fin n) 𝒞)
  letI : StarOrderedRing (CStarMatrix (Fin n) (Fin n) 𝒞) :=
    CStarAlgebra.spectralOrderedRing (CStarMatrix (Fin n) (Fin n) 𝒞)
  have hfc : Continuous (f : 𝒞 → ℬ) := by
    have h := (f.mkContinuous (2 * ‖f 1‖) (fun x => weak_russo_dye_2 f hf x)).continuous
    exact h
  have hentry : ∀ i j : Fin n,
      Continuous (fun M : CStarMatrix (Fin n) (Fin n) 𝒞 => M i j) := by
    intro i j
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun M M' => ?_)
    simp only [NNReal.coe_one, one_mul]
    rw [dist_eq_norm, dist_eq_norm, ← CStarMatrix.sub_apply]
    exact CStarMatrix.norm_entry_le_norm
  have hΦ : Continuous (fun M : CStarMatrix (Fin n) (Fin n) 𝒞 =>
      ∑ i, ∑ j, star (b i) * f (M i j) * b j) := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (continuous_const.mul (hfc.comp (hentry i j))).mul continuous_const
  have hclosed : IsClosed {M : CStarMatrix (Fin n) (Fin n) 𝒞 |
      0 ≤ ∑ i, ∑ j, star (b i) * f (M i j) * b j} :=
    (CStarAlgebra.isClosed_nonneg (A := ℬ)).preimage hΦ
  have hgen : {A : CStarMatrix (Fin n) (Fin n) 𝒞 |
        ∃ (K : ℕ) (c : Fin K → 𝒞) (B : Fin K → CStarMatrix (Fin n) (Fin n) ℂ),
          (∀ k, 0 ≤ c k) ∧ (∀ k, 0 ≤ B k) ∧
          A = ∑ k, CStarMatrix.ofMatrix (Matrix.of fun i j => B k i j • c k)}
      ⊆ {M : CStarMatrix (Fin n) (Fin n) 𝒞 |
        0 ≤ ∑ i, ∑ j, star (b i) * f (M i j) * b j} := by
    rintro M ⟨K, c, B, hc, hB, rfl⟩
    have hMij : ∀ i j : Fin n,
        (∑ k, CStarMatrix.ofMatrix (Matrix.of fun i j => B k i j • c k) :
          CStarMatrix (Fin n) (Fin n) 𝒞) i j = ∑ k, (B k i j) • c k := by
      intro i j
      rw [cstarMatrix_sum_apply]
      rfl
    show 0 ≤ _
    simp only [hMij, map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [sum_comm3 (fun i j k => star (b i) * f ((B k i j) • c k) * b j)]
    exact Finset.sum_nonneg fun k _ => gen_mem f hf b (c k) (hc k) (B k) (hB k)
  have hmem : (CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j) :
      CStarMatrix (Fin n) (Fin n) 𝒞) ∈ closure {A : CStarMatrix (Fin n) (Fin n) 𝒞 |
        ∃ (K : ℕ) (c : Fin K → 𝒞) (B : Fin K → CStarMatrix (Fin n) (Fin n) ℂ),
          (∀ k, 0 ≤ c k) ∧ (∀ k, 0 ≤ B k) ∧
          A = ∑ k, CStarMatrix.ofMatrix (Matrix.of fun i j => B k i j • c k)} := by
    rw [ccstar_pos_mat n]
    exact cstar_matrix_star_mul_nonneg a
  exact hclosed.closure_subset_iff.mpr hgen hmem


/-- **34XII** (`cstar-positive-2x2matrix`, cstar.tex:5704, Lemma), the two
inequalities: for a positive 2×2 matrix `A ≡ [[p, a], [a*, q]]` over `𝒜` we
have `a* a ≤ ‖p‖ q` and `a a* ≤ ‖q‖ p`.  The Lemma's closing "in particular"
— if `p = 0` or `q = 0` then `a = a* = 0` — is
`cstar_positive_2x2matrix_eq_zero` below.

*Class 1 — faithful.*  This is the Lemma's own proof **34XIII**: "since
`(x,y) ↦ ⟨x,Ay⟩` gives an 𝒜-valued inner product on `𝒜²`,
`a a* = ⟨(1,0),A(0,1)⟩⟨(0,1),A(1,0)⟩ ≤ ‖⟨(0,1),A(0,1)⟩‖⟨(1,0),A(1,0)⟩ = ‖q‖p`
by Cauchy–Schwarz (see `chilb-cs`)", and "by a similar reasoning, we get
`a* a ≤ ‖p‖ q`" — the second inequality being the first with the two basis
vectors interchanged.  Both are `pos_matrix_cs`, which is exactly that
Cauchy–Schwarz step (**32VI** `chilb_cs` for the inner product `⟨x,Ay⟩`) at
the standard basis of `𝒜²`. -/
theorem cstar_positive_2x2matrix
    [PartialOrder (CStarMatrix (Fin 2) (Fin 2) 𝒜)]
    [StarOrderedRing (CStarMatrix (Fin 2) (Fin 2) 𝒜)]
    (A : CStarMatrix (Fin 2) (Fin 2) 𝒜) (hA : 0 ≤ A) :
    star (A 0 1) * A 0 1 ≤ ‖A 0 0‖ • A 1 1 ∧
      A 0 1 * star (A 0 1) ≤ ‖A 1 1‖ • A 0 0 := by
  have h10 : A 1 0 = star (A 0 1) := by
    conv_lhs => rw [← hA.isSelfAdjoint.star_eq]
    rw [CStarMatrix.star_apply]
  refine ⟨?_, ?_⟩
  · -- `a* a = ⟨(0,1),A(1,0)⟩⟨(1,0),A(0,1)⟩ ≤ ‖⟨(1,0),A(1,0)⟩‖ ⟨(0,1),A(0,1)⟩ = ‖p‖ q`
    have h := pos_matrix_cs hA 1 0
    rwa [h10] at h
  · -- `a a* = ⟨(1,0),A(0,1)⟩⟨(0,1),A(1,0)⟩ ≤ ‖⟨(0,1),A(0,1)⟩‖ ⟨(1,0),A(1,0)⟩ = ‖q‖ p`
    have h := pos_matrix_cs hA 0 1
    rwa [h10] at h

/-- **34XII** (`cstar-positive-2x2matrix`, cstar.tex:5704, Lemma), the closing
clause: for a positive 2×2 matrix `A ≡ [[p, a], [a*, q]]` over `𝒜`, if `p = 0`
or `q = 0` then `a = a* = 0`.

*Class 1 — faithful.*  This is the Lemma's own "in particular", read off the
two inequalities: `p = 0` kills the right-hand side of `a* a ≤ ‖p‖ q`, so
`a* a = 0` and hence `a = 0`; `q = 0` kills that of `a a* ≤ ‖q‖ p`.  It is
what the thesis uses to finish Choi's Lemma, and **34XVIII** `choi_2` below
now uses it for exactly that. -/
theorem cstar_positive_2x2matrix_eq_zero
    [PartialOrder (CStarMatrix (Fin 2) (Fin 2) 𝒜)]
    [StarOrderedRing (CStarMatrix (Fin 2) (Fin 2) 𝒜)]
    (A : CStarMatrix (Fin 2) (Fin 2) 𝒜) (hA : 0 ≤ A)
    (h : A 0 0 = 0 ∨ A 1 1 = 0) : A 0 1 = 0 ∧ A 1 0 = 0 := by
  obtain ⟨h1, h2⟩ := cstar_positive_2x2matrix A hA
  have h10 : A 1 0 = star (A 0 1) := by
    conv_lhs => rw [← hA.isSelfAdjoint.star_eq]
    rw [CStarMatrix.star_apply]
  have hfin : A 0 1 = 0 → A 0 1 = 0 ∧ A 1 0 = 0 :=
    fun h => ⟨h, by rw [h10, h, star_zero]⟩
  rcases h with hp | hq
  · refine hfin (CStarRing.star_mul_self_eq_zero_iff (A 0 1) |>.mp ?_)
    refine le_antisymm ?_ (star_mul_self_nonneg _)
    rw [hp, norm_zero, zero_smul] at h1
    exact h1
  · refine hfin (CStarRing.mul_star_self_eq_zero_iff (A 0 1) |>.mp ?_)
    refine le_antisymm ?_ (mul_star_self_nonneg _)
    rw [hq, norm_zero, zero_smul] at h2
    exact h2

/-- **34XIV** (`cp-cs`, cstar.tex:5629, Lemma): for a positive map
`f : 𝒜 → ℬ` such that `M₂ f` is positive (expressed by condition 2 of
**34II**), and `a, b ∈ 𝒜`:
`f(a* b) f(b* a) ≤ ‖f(b* b)‖ f(a* a)`. -/
theorem cp_cs (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f)
    (h2 : ∀ (a : Fin 2 → 𝒜) (b : Fin 2 → ℬ),
      0 ≤ ∑ i, ∑ j, star (b i) * f (star (a i) * a j) * b j)
    (a b : 𝒜) :
    f (star a * b) * f (star b * a) ≤ ‖f (star b * b)‖ • f (star a * a) := by
  have hi : ∀ x : 𝒜, f (star x) = star (f x) := cstar_p_implies_i f hf
  have hT : ∀ v : Fin 2 → 𝒜,
      0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => f (star (v i) * v j)) :=
    (n_pos f 2).out 1 2 |>.mp h2
  have h := (cstar_positive_2x2matrix _ (hT ![a, b])).2
  have hstar : star (f (star a * b)) = f (star b * a) := by
    have hx := hi (star a * b)
    rw [star_mul, star_star] at hx
    exact hx.symm
  simpa [hstar, CStarMatrix.ofMatrix_apply, Matrix.of_apply] using h

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- A linear map `f : 𝒜 → ℬ` satisfying `‖f(a)‖ ≤ ‖f(1)‖‖a‖`, packaged as a
*continuous* linear map so that it has an operator norm at all.  This is the
device that makes the equalities `‖f‖ = ‖f(1)‖` of **34XVI** and **34aVIII**
expressible: a bare `𝒜 →ₗ[ℂ] ℬ` carries no norm. -/
noncomputable def unitalBoundCLM (f : 𝒜 →ₗ[ℂ] ℬ)
    (h : ∀ a : 𝒜, ‖f a‖ ≤ ‖f 1‖ * ‖a‖) : 𝒜 →L[ℂ] ℬ :=
  f.mkContinuous ‖f 1‖ h

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- The operator norm of `unitalBoundCLM f h` is exactly `‖f(1)‖`: the bound
gives `≤`, and evaluating at `1` gives `≥`. -/
theorem norm_unitalBoundCLM (f : 𝒜 →ₗ[ℂ] ℬ)
    (h : ∀ a : 𝒜, ‖f a‖ ≤ ‖f 1‖ * ‖a‖) : ‖unitalBoundCLM f h‖ = ‖f 1‖ := by
  refine le_antisymm (f.mkContinuous_norm_le (norm_nonneg _) h) ?_
  have hle := (unitalBoundCLM f h).le_opNorm 1
  rcases subsingleton_or_nontrivial 𝒜 with _ | _
  · rw [Subsingleton.elim (1 : 𝒜) 0, map_zero, norm_zero]
    exact norm_nonneg _
  · simpa [unitalBoundCLM] using hle

/-- **34XVI** (`cp-russo-dye`, cstar.tex:5655, Corollary), the substantial
half: `‖f(a)‖ ≤ ‖f(1)‖ ‖a‖` for every cp-map `f : 𝒜 → ℬ` between C*-algebras.
The Corollary's equality `‖f‖ = ‖f(1)‖` itself is `cp_russo_dye_norm` below,
which adds the reverse bound. -/
theorem cp_russo_dye (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsCompletelyPositiveMap f)
    (a : 𝒜) : ‖f a‖ ≤ ‖f 1‖ * ‖a‖ := by
  have hp : IsPositiveMap f := astara_pos_basic_2_cp f hf
  -- a positive map is norm-bounded by `‖f 1‖` on positive elements
  have hpos : ∀ x : 𝒜, 0 ≤ x → ‖f x‖ ≤ ‖f 1‖ * ‖x‖ := by
    intro x hx
    have h1 : x ≤ algebraMap ℂ 𝒜 ((‖x‖ : ℝ) : ℂ) := by
      have h := IsSelfAdjoint.le_algebraMap_norm_self (.of_nonneg hx)
      rwa [algebraMap_real_eq] at h
    have h2 : f x ≤ ((‖x‖ : ℝ) : ℂ) • f 1 := by
      have hd : 0 ≤ f (algebraMap ℂ 𝒜 ((‖x‖ : ℝ) : ℂ) - x) :=
        hp _ (sub_nonneg.mpr h1)
      rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul] at hd
      exact sub_nonneg.mp hd
    calc ‖f x‖ ≤ ‖((‖x‖ : ℝ) : ℂ) • f 1‖ :=
          CStarAlgebra.norm_le_norm_of_nonneg_of_le (hp x hx) h2
      _ = ‖f 1‖ * ‖x‖ := by rw [norm_smul]; simp [mul_comm]
  -- the cp Cauchy–Schwarz inequality with `(1, a)`
  have hcs := cp_cs f hp (hf 2) 1 a
  simp only [star_one, one_mul, mul_one] at hcs
  have hnn : 0 ≤ f a * f (star a) := by
    rw [cstar_p_implies_i f hp a]
    exact mul_star_self_nonneg _
  have hn1 : ‖f a * f (star a)‖ ≤ ‖‖f (star a * a)‖ • f 1‖ :=
    CStarAlgebra.norm_le_norm_of_nonneg_of_le hnn hcs
  rw [cstar_p_implies_i f hp a, CStarRing.norm_self_mul_star, norm_smul,
    norm_norm] at hn1
  have hn2 : ‖f (star a * a)‖ ≤ ‖f 1‖ * (‖a‖ * ‖a‖) := by
    have h := hpos (star a * a) (star_mul_self_nonneg a)
    rwa [CStarRing.norm_star_mul_self] at h
  have hsq : ‖f a‖ ^ 2 ≤ (‖f 1‖ * ‖a‖) ^ 2 := by
    calc ‖f a‖ ^ 2 = ‖f a‖ * ‖f a‖ := pow_two _
      _ ≤ ‖f (star a * a)‖ * ‖f 1‖ := hn1
      _ ≤ (‖f 1‖ * (‖a‖ * ‖a‖)) * ‖f 1‖ :=
          mul_le_mul_of_nonneg_right hn2 (norm_nonneg _)
      _ = (‖f 1‖ * ‖a‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg (f a)) (by positivity) two_ne_zero).mp hsq

/-- **34XVI** (`cp-russo-dye`, cstar.tex:5655, Corollary), the equality the
Corollary actually states: the operator norm of a cp-map `f : 𝒜 → ℬ` is
`‖f‖ = ‖f(1)‖`.  `cp_russo_dye` above is the substantial half `‖f‖ ≤ ‖f(1)‖`;
the reverse bound `‖f(1)‖ ≤ ‖f‖‖1‖ = ‖f‖` is the evaluation at `1`. -/
theorem cp_russo_dye_norm (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsCompletelyPositiveMap f) :
    ‖unitalBoundCLM f (cp_russo_dye f hf)‖ = ‖f 1‖ :=
  norm_unitalBoundCLM f _

/-- **34XVIII** (`choi`, cstar.tex:5674, Lemma (Choi)), part 1:
`f(a)* f(a) ≤ f(a* a)` for every cpu-map `f : 𝒜 → ℬ` and `a ∈ 𝒜`. -/
theorem choi_1 (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsCompletelyPositiveMap f)
    (hu : f 1 = 1) (a : 𝒜) :
    star (f a) * f a ≤ f (star a * a) := by
  rcases subsingleton_or_nontrivial ℬ with _ | _
  · exact le_of_eq (Subsingleton.elim _ _)
  · have hp : IsPositiveMap f := astara_pos_basic_2_cp f hf
    have hi : ∀ b : 𝒜, f (star b) = star (f b) := cstar_p_implies_i f hp
    have := cp_cs f hp (hf 2) a 1
    simpa [hi a, hu] using this

/-- **34XVIII** (`choi`, cstar.tex:5674, Lemma (Choi)), part 2: if
`f(a* a) = f(a)* f(a)` for a cpu-map `f` and some `a`, then
`f(b a) = f(b) f(a)` for all `b ∈ 𝒜`. -/
theorem choi_2 (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsCompletelyPositiveMap f)
    (hu : f 1 = 1) (a : 𝒜) (ha : f (star a * a) = star (f a) * f a) (b : 𝒜) :
    f (b * a) = f b * f a := by
  have hp : IsPositiveMap f := astara_pos_basic_2_cp f hf
  have hi : ∀ x : 𝒜, f (star x) = star (f x) := cstar_p_implies_i f hp
  -- The thesis's `(M₂f)(A)* (M₂f)(A) ≤ (M₂f)(A*A)` for `A = ![![a,c],![0,0]]`,
  -- spelled out entrywise: the matrix `(f(xᵢ* xⱼ) - f(xᵢ)* f(xⱼ))ᵢⱼ` is positive.
  have key : ∀ c : 𝒜, f (star c * a) = star (f c) * f a := by
    intro c
    set v : Fin 2 → 𝒜 := ![a, c] with hv
    set M : CStarMatrix (Fin 2) (Fin 2) ℬ := CStarMatrix.ofMatrix
      (Matrix.of fun i j => f (star (v i) * v j) - star (f (v i)) * f (v j)) with hM
    have hMpos : 0 ≤ M := by
      rw [cstar_matrix_positive_iff]
      intro d
      have hS := hf 3 ![1, a, c] ![-(f a * d 0 + f c * d 1), d 0, d 1]
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, star_one, one_mul,
        mul_one, hu, hi, star_neg, neg_mul, mul_neg, star_add, star_mul, star_star] at hS
      refine le_of_le_of_eq hS ?_
      simp only [hM, hv, Fin.sum_univ_two, CStarMatrix.ofMatrix_apply, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_sub, sub_mul]
      noncomm_ring
    have h00 : M 0 0 = 0 := by
      simp only [hM, hv, CStarMatrix.ofMatrix_apply, Matrix.of_apply, Matrix.cons_val_zero]
      rw [ha, sub_self]
    -- The thesis finishes with the "in particular" clause of **34XII**: the
    -- `(0,0)` entry of this positive matrix vanishes, so its off-diagonal does.
    have h10 := (cstar_positive_2x2matrix_eq_zero M hMpos (Or.inl h00)).2
    simp only [hM, hv, CStarMatrix.ofMatrix_apply, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, sub_eq_zero] at h10
    exact h10
  have := key (star b)
  rwa [star_star, hi b, star_star] at this

/-! ## Parsec 341 (34a): Russo–Dye

**34aI** (cstar.tex:5724): introduction — nothing to formalize. -/

/-- **34aII** (`normal-russo-dye`, cstar.tex:5751, Lemma):
`‖f(a)‖ ≤ ‖f(1)‖ ‖a‖` for every p-map `f : 𝒜 → ℬ` and *normal* `a ∈ 𝒜`.

*Class 1 — faithful.*  The Lemma's own three-line proof (cstar.tex:5757):
`a` being normal, the C*-subalgebra `C*(a)` it generates is commutative by
**28II**.2, so the restriction of `f` to `C*(a)` is completely positive by
**34IX**.2 `cp_commutative_dom`, and **34XVI** `cp_russo_dye` applies to it.
Positivity transfers to the restriction because `0 ≤ x` in `C*(a)` makes
`x = y* y` there, hence in `𝒜`.

Until this repair the proof ran the **34VII** partition-of-unity
approximation directly on `a` — tent functions on `spec(a)` fed through the
continuous functional calculus — because `cp_commutative_dom` was still
`sorry` when it was written.  It has been proved since; that premise had
expired, and the thesis's route costs 150 lines less.  (The two private
auxiliaries `norm_sum_smul_le_aux` and `norm_sum_smul_le_of_nonneg`, which
existed only to serve the approximation, went with it.) -/
theorem normal_russo_dye (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) (a : 𝒜)
    (ha : IsStarNormal a) : ‖f a‖ ≤ ‖f 1‖ * ‖a‖ := by
  -- `C*(a)`, commutative because `a` is normal
  let S := StarAlgebra.elemental ℂ a
  let _ : PartialOrder S := CStarAlgebra.spectralOrder S
  have _ : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  -- the restriction of `f` to `C*(a)`, still positive
  let g : S →ₗ[ℂ] ℬ := f ∘ₗ (S.subtype : S →ₐ[ℂ] 𝒜).toLinearMap
  have hga : ∀ x : S, g x = f (x : 𝒜) := fun _ => rfl
  have hgpos : IsPositiveMap g := by
    intro x hx
    obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
    have hxy : (x : 𝒜) = star (y : 𝒜) * (y : 𝒜) := by rw [hy]; push_cast; rfl
    rw [hga, hxy]
    exact hf _ (star_mul_self_nonneg _)
  -- **34IX**.2 and then **34XVI**
  have h := cp_russo_dye g (cp_commutative_dom g hgpos)
    ⟨a, StarAlgebra.elemental.self_mem ℂ a⟩
  rw [hga, hga] at h
  simpa using h

/-! **34aIV** (`cstar-unitary`, cstar.tex:5766, Definition): an element `u`
of a C*-algebra is *unitary* when `u* u = 1 = u u*` — Mathlib's submonoid
`unitary 𝒜` (membership `u ∈ unitary 𝒜`). -/

/-- **34aV** (cstar.tex:5773, Exercise), part 1: every `λ ∈ ℂ` with
`|λ| = 1` is unitary in `𝒜`; in particular `1` is. -/
theorem unitary_basic_1 (z : ℂ) (hz : ‖z‖ = 1) :
    algebraMap ℂ 𝒜 z ∈ unitary 𝒜 := by
  have hz1 : star z * z = (1 : ℂ) := by
    rw [RCLike.star_def, RCLike.conj_mul, hz]
    norm_num
  have hz2 : z * star z = (1 : ℂ) := by rw [mul_comm]; exact hz1
  have key : star (algebraMap ℂ 𝒜 z) = algebraMap ℂ 𝒜 (star z) :=
    (algebraMap_star_comm z).symm
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩ <;> rw [key, ← map_mul]
  · rw [hz1, map_one]
  · rw [hz2, map_one]

/-- **34aV** (cstar.tex:5773, Exercise), part 2: a unitary `u` is invertible
with inverse `u*`, and `u*` is unitary. -/
theorem unitary_basic_2 (u : 𝒜) (hu : u ∈ unitary 𝒜) :
    IsUnit u ∧ Ring.inverse u = star u ∧ star u ∈ unitary 𝒜 := by
  have hus : u * star u = 1 := Unitary.mul_star_self_of_mem hu
  have hu' : IsUnit u := ⟨⟨u, star u, hus, Unitary.star_mul_self_of_mem hu⟩, rfl⟩
  refine ⟨hu', ?_, Unitary.star_mem hu⟩
  calc Ring.inverse u = Ring.inverse u * (u * star u) := by rw [hus, mul_one]
    _ = Ring.inverse u * u * star u := (mul_assoc _ _ _).symm
    _ = star u := by rw [Ring.inverse_mul_cancel u hu', one_mul]

/-- **34aV** (cstar.tex:5773, Exercise), part 3: the product of unitaries is
unitary. -/
theorem unitary_basic_3 (u v : 𝒜) (hu : u ∈ unitary 𝒜) (hv : v ∈ unitary 𝒜) :
    u * v ∈ unitary 𝒜 :=
  mul_mem hu hv

/-- **34aV** (cstar.tex:5773, Exercise), part 4: every unitary is normal;
and a normal `a` is unitary iff `Re(a)² + Im(a)² = 1`. -/
theorem unitary_basic_4 (a : 𝒜) :
    (a ∈ unitary 𝒜 → IsStarNormal a) ∧
      (IsStarNormal a →
        (a ∈ unitary 𝒜 ↔ (ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2 = 1)) := by
  refine ⟨isStarNormal_of_mem_unitary, fun ha => ?_⟩
  haveI : IsStarNormal a := ha
  have key : star a * a = (ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2 := by
    rw [star_mul_self_eq_realPart_sq_add_imaginaryPart_sq a, sq, sq]
  have hcomm : a * star a = star a * a := ha.star_comm_self.eq.symm
  rw [Unitary.mem_iff, hcomm, key, and_self]

/-- **34aV** (cstar.tex:5773, Exercise), part 5: every self-adjoint `a` with
`‖a‖ ≤ 1` is the real part of some unitary (e.g. `u = a + i√(1-a²)`). -/
theorem unitary_basic_5 (a : 𝒜) (ha : IsSelfAdjoint a) (h1 : ‖a‖ ≤ 1) :
    ∃ u ∈ unitary 𝒜, a = (ℜ u : 𝒜) := by
  have hsq : 0 ≤ 1 - a ^ 2 := by
    have h2 : a ^ 2 ≤ algebraMap ℂ 𝒜 ((‖a ^ 2‖ : ℝ) : ℂ) := by
      have h := IsSelfAdjoint.le_algebraMap_norm_self (ha.pow 2)
      rwa [algebraMap_real_eq] at h
    have h3 : ‖a ^ 2‖ ≤ 1 := by
      calc ‖a ^ 2‖ = ‖a * a‖ := by rw [sq]
        _ ≤ ‖a‖ * ‖a‖ := norm_mul_le _ _
        _ ≤ 1 := mul_le_one₀ h1 (norm_nonneg a) h1
    have h4 : algebraMap ℂ 𝒜 ((‖a ^ 2‖ : ℝ) : ℂ) ≤ (1 : 𝒜) := by
      simpa using algebraMap_ofReal_mono (𝒜 := 𝒜) h3
    exact sub_nonneg.mpr (h2.trans h4)
  set b : 𝒜 := CFC.sqrt (1 - a ^ 2) with hbdef
  have hbnn : 0 ≤ b := CFC.sqrt_nonneg _
  have hbsa : IsSelfAdjoint b := .of_nonneg hbnn
  have hbb : b * b = 1 - a ^ 2 := CFC.sqrt_mul_sqrt_self _ hsq
  have hcomm : Commute b a := by
    rw [hbdef, CFC.sqrt_eq_cfc]
    exact Commute.cfc_nnreal
      ((Commute.one_left a).sub_left ((Commute.refl a).pow_left 2)) NNReal.sqrt
  refine ⟨a + Complex.I • b, ?_, ?_⟩
  · have hRe : (ℜ (a + Complex.I • b) : 𝒜) = a := by
      rw [map_add, realPart_I_smul, hbsa.imaginaryPart]
      simp [ha.coe_realPart]
    have hIm : (ℑ (a + Complex.I • b) : 𝒜) = b := by
      rw [map_add, imaginaryPart_I_smul, ha.imaginaryPart]
      simp [hbsa.coe_realPart]
    have hn : IsStarNormal (a + Complex.I • b) :=
      isStarNormal_iff_commute_realPart_imaginaryPart.mpr
        (by rw [hRe, hIm]; exact hcomm.symm)
    rw [(unitary_basic_4 (a + Complex.I • b)).2 hn, hRe, hIm, sq b, hbb]
    abel
  · rw [map_add, realPart_I_smul, hbsa.imaginaryPart]
    simp [ha.coe_realPart]

/-- **34aV** (cstar.tex:5773, Exercise), part 6: every invertible `a` can be
written `a = u √(a* a)` with `u` unitary (a variation on the polar
decomposition, cf. vn.tex 82I). -/
theorem unitary_basic_6 (a : 𝒜) (ha : IsUnit a) :
    ∃ u ∈ unitary 𝒜, a = u * CFC.sqrt (star a * a) := by
  set h : 𝒜 := CFC.sqrt (star a * a) with hh
  have hnn : 0 ≤ star a * a := star_mul_self_nonneg a
  have hhh : h * h = star a * a := CFC.sqrt_mul_sqrt_self _ hnn
  have hsa : IsSelfAdjoint h := .of_nonneg (CFC.sqrt_nonneg _)
  have hunit : IsUnit h := by
    rw [← isUnit_mul_self_iff, hhh]
    exact ha.star.mul ha
  set k : 𝒜 := Ring.inverse h with hk
  have hkh : k * h = 1 := Ring.inverse_mul_cancel h hunit
  have hhk : h * k = 1 := Ring.mul_inverse_cancel h hunit
  have hksa : star k = k := by rw [hk, ← Ring.inverse_star, hsa.star_eq]
  refine ⟨a * k, Unitary.mem_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · calc star (a * k) * (a * k) = k * (star a * a) * k := by
          rw [star_mul, hksa]; noncomm_ring
      _ = (k * h) * (h * k) := by rw [← hhh]; noncomm_ring
      _ = 1 := by rw [hkh, hhk, one_mul]
  · have hkk : k * k = Ring.inverse (star a * a) := by
      rw [← hhh, Ring.inverse_mul (Or.inl hunit)]
    calc a * k * star (a * k) = a * (k * k) * star a := by
          rw [star_mul, hksa]; noncomm_ring
      _ = a * (Ring.inverse a * Ring.inverse (star a)) * star a := by
          rw [hkk, Ring.inverse_mul (Or.inr ha)]
      _ = (a * Ring.inverse a) * (Ring.inverse (star a) * star a) := by noncomm_ring
      _ = 1 := by
          rw [Ring.mul_inverse_cancel a ha, Ring.inverse_mul_cancel _ ha.star, one_mul]
  · rw [mul_assoc, hkh, mul_one]

/-- **34aVI** (cstar.tex:5812, Exercise), part 1: every invertible `a` with
`‖a‖ ≤ 2` is the sum of two unitaries. -/
theorem sum_of_unitaries_1 (a : 𝒜) (ha : IsUnit a) (h2 : ‖a‖ ≤ 2) :
    ∃ u ∈ unitary 𝒜, ∃ v ∈ unitary 𝒜, a = u + v := by
  obtain ⟨w, hw, haw⟩ := unitary_basic_6 a ha
  set h : 𝒜 := CFC.sqrt (star a * a) with hh
  have hnn : 0 ≤ h := CFC.sqrt_nonneg _
  have hsa : IsSelfAdjoint h := .of_nonneg hnn
  have hhh : h * h = star a * a :=
    CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg a)
  have hnorm : ‖h‖ ≤ 2 := by
    have e1 : ‖h‖ * ‖h‖ = ‖a‖ * ‖a‖ := by
      rw [← CStarRing.norm_star_mul_self (x := h), hsa.star_eq, hhh,
        CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg h, norm_nonneg a]
  have hcsa : IsSelfAdjoint ((2 : ℝ)⁻¹ • h) :=
    IsSelfAdjoint.smul (IsSelfAdjoint.all _) hsa
  have hcnorm : ‖(2 : ℝ)⁻¹ • h‖ ≤ 1 := by
    rw [norm_smul]
    simp only [norm_inv, Real.norm_ofNat]
    linarith
  obtain ⟨u, hu, hcu⟩ := unitary_basic_5 _ hcsa hcnorm
  have hsum : u + star u = h := by
    have h1 : (2 : ℝ)⁻¹ • (u + star u) = (2 : ℝ)⁻¹ • h := by
      rw [← realPart_apply_coe, ← hcu]
    have h3 := congrArg (fun x : 𝒜 => (2 : ℝ) • x) h1
    simpa [smul_smul] using h3
  refine ⟨w * u, mul_mem hw hu, w * star u, mul_mem hw (Unitary.star_mem hu), ?_⟩
  rw [haw, ← hsum, mul_add]

/-- **34aVI** (cstar.tex:5812, Exercise), part 2: `u + a` is the sum of two
unitaries for unitary `u` and `‖a‖ < 1`. -/
theorem sum_of_unitaries_2 (u a : 𝒜) (hu : u ∈ unitary 𝒜) (ha : ‖a‖ < 1) :
    ∃ v ∈ unitary 𝒜, ∃ w ∈ unitary 𝒜, u + a = v + w := by
  rcases subsingleton_or_nontrivial 𝒜 with _ | _
  · exact ⟨1, one_mem _, 1, one_mem _, Subsingleton.elim _ _⟩
  have hbn : ‖star u * a‖ < 1 := by
    rwa [CStarRing.norm_mem_unitary_mul a (Unitary.star_mem hu)]
  have hunit : IsUnit (1 + star u * a) := by
    have h := isUnit_one_sub_of_norm_lt_one (x := -(star u * a)) (by simpa using hbn)
    simpa using h
  have hnorm : ‖(1 : 𝒜) + star u * a‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [CStarRing.norm_one]
    linarith
  obtain ⟨v, hv, w, hw, hvw⟩ := sum_of_unitaries_1 _ hunit hnorm
  refine ⟨u * v, mul_mem hu hv, u * w, mul_mem hu hw, ?_⟩
  rw [← mul_add, ← hvw, mul_add, mul_one, ← mul_assoc,
    Unitary.mul_star_self_of_mem hu, one_mul]

/-- **34aVI** (cstar.tex:5812, Exercise), part 3: every `a` with `‖a‖ < N`
is the sum of `N + 2` unitaries.  (Part 4 of the exercise, to prove the
following theorem, is **34aVII**.) -/
theorem sum_of_unitaries_3 (a : 𝒜) (N : ℕ) (hN : ‖a‖ < N) :
    ∃ u : Fin (N + 2) → 𝒜, (∀ i, u i ∈ unitary 𝒜) ∧ a = ∑ i, u i := by
  rcases subsingleton_or_nontrivial 𝒜 with _ | _
  · exact ⟨fun _ => 1, fun _ => one_mem _, Subsingleton.elim _ _⟩
  have aux : ∀ (k : ℕ) (c b : 𝒜), c ∈ unitary 𝒜 → ‖b‖ < 1 →
      ∃ u : Fin (k + 1) → 𝒜, (∀ i, u i ∈ unitary 𝒜) ∧ c + k • b = ∑ i, u i := by
    intro k
    induction k with
    | zero => exact fun c b hc _ => ⟨fun _ => c, fun _ => hc, by simp⟩
    | succ k ih =>
      intro c b hc hb
      obtain ⟨v, hv, w, hw, hvw⟩ := sum_of_unitaries_2 c b hc hb
      obtain ⟨u, hu, hsum⟩ := ih v b hv hb
      refine ⟨Fin.snoc u w, ?_, ?_⟩
      · refine Fin.lastCases ?_ ?_
        · simpa using hw
        · intro j; simpa using hu j
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [← hsum, succ_nsmul,
          show v + k • b + w = v + w + k • b from by abel, ← hvw]
        abel
  set b : 𝒜 := ((N : ℝ) + 1)⁻¹ • (a - 1) with hbdef
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hb : ‖b‖ < 1 := by
    have h1 : ‖a - 1‖ < (N : ℝ) + 1 := by
      refine (norm_sub_le _ _).trans_lt ?_
      rw [CStarRing.norm_one]
      linarith
    rw [hbdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos]
    rw [inv_mul_lt_one₀ hpos]
    linarith
  obtain ⟨u, hu, hsum⟩ := aux (N + 1) 1 b (one_mem _) hb
  refine ⟨u, hu, ?_⟩
  rw [← hsum, hbdef, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  push_cast
  rw [mul_inv_cancel₀ hpos.ne', one_smul]
  abel

/-- **34aVII** (`russo-dye`, cstar.tex:5842, Theorem (Russo–Dye)): every
element `a` of a C*-algebra with `‖a‖ < 1 - 2/N` for some natural number
`N > 0` can be written as `a = (u₁ + ⋯ + u_N)/N` for some unitaries
`u₁, …, u_N`.  (Hence the convex combinations of unitaries are norm dense in
the closed unit ball.)

`N > 0` is **erratum 341.70**.  It is needed in Lean for a reason of pure
notation — `2 / (0 : ℝ) = 0`, so at `N = 0` the hypothesis would degenerate
to `‖a‖ < 1` and the conclusion to `a = 0`.  The erratum made the thesis's
intent (`N ≥ 1`) explicit, and cstar.tex now prints "for some natural
number `N > 0`", so the hypothesis here matches the source as it stands. -/
theorem russo_dye (a : 𝒜) (N : ℕ) (hN0 : 0 < N) (hN : ‖a‖ < 1 - 2 / N) :
    ∃ u : Fin N → 𝒜, (∀ i, u i ∈ unitary 𝒜) ∧
      a = ((N : ℂ))⁻¹ • ∑ i, u i :=
  by
    -- `N ≤ 2` is vacuous: there `1 - 2/N ≤ 0 ≤ ‖a‖`.
    have hN3 : 3 ≤ N := by
      by_contra hlt
      push_neg at hlt
      interval_cases N <;>
        · norm_num at hN
          linarith [norm_nonneg a]
    obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M + 2 := ⟨N - 2, by omega⟩
    have hcast : ((M + 2 : ℕ) : ℝ) = (M : ℝ) + 2 := by push_cast; ring
    have hpos : (0 : ℝ) < (M : ℝ) + 2 := by positivity
    rw [hcast] at hN
    -- `‖Na‖ = N‖a‖ < N - 2 = M`, so **34aVI**.3 writes `Na` as a sum of
    -- `M + 2 = N` unitaries.
    have hkey : ‖a‖ * ((M : ℝ) + 2) < (M : ℝ) :=
      calc ‖a‖ * ((M : ℝ) + 2) < (1 - 2 / ((M : ℝ) + 2)) * ((M : ℝ) + 2) :=
            mul_lt_mul_of_pos_right hN hpos
        _ = (M : ℝ) := by field_simp; ring
    have hb : ‖((M + 2 : ℕ) : ℂ) • a‖ < (M : ℕ) := by
      rw [norm_smul, Complex.norm_natCast, hcast]
      linarith [hkey]
    obtain ⟨u, hu, hsum⟩ := sum_of_unitaries_3 (((M + 2 : ℕ) : ℂ) • a) M hb
    have hne : ((M + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact ⟨u, hu, by rw [← hsum, smul_smul, inv_mul_cancel₀ hne, one_smul]⟩

/-- **34aVIII** (`russo-dye-cor`, cstar.tex:5850, Corollary), the substantial
half: `‖f(a)‖ ≤ ‖f(1)‖ ‖a‖` for every positive map `f : 𝒜 → ℬ` between
C*-algebras.  The Corollary's equality `‖f‖ = ‖f(1)‖` itself is
`russo_dye_cor_norm` below, which adds the reverse bound.

*Class 1 — faithful.*  The thesis's own limit argument: by **34aVII**
`russo_dye` every `x` with `‖x‖ < 1` is a mean `(u₁+⋯+u_N)/N` of unitaries,
each of which is normal of norm `1`, so **34aII** gives `‖f(x)‖ ≤ ‖f(1)‖`;
rescaling and letting the radius tend to `‖a‖` gives the statement.  (The
thesis approximates a norm-`≤ 1` element by such means; we rescale instead,
which needs no completeness of the set of means.) -/
theorem russo_dye_cor (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) (a : 𝒜) :
    ‖f a‖ ≤ ‖f 1‖ * ‖a‖ := by
  rcases subsingleton_or_nontrivial 𝒜 with _ | _
  · rw [Subsingleton.elim a 0, map_zero, norm_zero]; positivity
  -- Russo–Dye: on the open unit ball, `‖f(x)‖ ≤ ‖f(1)‖`
  have key : ∀ x : 𝒜, ‖x‖ < 1 → ‖f x‖ ≤ ‖f 1‖ := by
    intro x hx
    have h1x : (0 : ℝ) < 1 - ‖x‖ := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / (1 - ‖x‖))
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    have hN0 : 0 < N := by exact_mod_cast hNpos
    have hNx : ‖x‖ < 1 - 2 / N := by
      rw [div_lt_iff₀ h1x] at hN
      have : (2 : ℝ) / N < 1 - ‖x‖ := by rw [div_lt_iff₀ hNpos]; linarith
      linarith
    obtain ⟨u, hu, hxu⟩ := russo_dye x N hN0 hNx
    have hunit : ∀ i, ‖f (u i)‖ ≤ ‖f 1‖ := by
      intro i
      have h := normal_russo_dye f hf (u i) (isStarNormal_of_mem_unitary (hu i))
      rwa [CStarRing.norm_of_mem_unitary (hu i), mul_one] at h
    have hsum : ‖f (∑ i, u i)‖ ≤ (N : ℝ) * ‖f 1‖ := by
      rw [map_sum]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖f (u i)‖ ≤ ∑ _i : Fin N, ‖f 1‖ := Finset.sum_le_sum fun i _ => hunit i
        _ = (N : ℝ) * ‖f 1‖ := by simp
    rw [hxu, map_smul, norm_smul, norm_inv, Complex.norm_natCast]
    rw [inv_mul_le_iff₀ hNpos]
    exact hsum.trans (le_of_eq (by ring))
  have step : ∀ r : ℝ, ‖a‖ < r → ‖f a‖ ≤ r * ‖f 1‖ := by
    intro r hr
    have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (norm_nonneg a) hr
    have h1 : ‖((r : ℂ))⁻¹ • a‖ < 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
        inv_mul_lt_one₀ hr0]
      exact hr
    have h2 := key _ h1
    rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, inv_mul_le_iff₀ hr0] at h2
    exact h2
  rcases eq_or_lt_of_le (norm_nonneg (f 1)) with hK | hK
  · have h := step (‖a‖ + 1) (by linarith)
    rw [← hK] at h
    simp only [mul_zero] at h
    rw [← hK]
    simpa using h
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hpos : 0 < ε / ‖f 1‖ := div_pos hε hK
    have h := step (‖a‖ + ε / ‖f 1‖) (by linarith)
    refine h.trans (le_of_eq ?_)
    field_simp

/-- **34aVIII** (`russo-dye-cor`, cstar.tex:5850, Corollary), the equality the
Corollary actually states: the operator norm of a positive map `f : 𝒜 → ℬ` is
`‖f‖ = ‖f(1)‖`.  `russo_dye_cor` above is the half `‖f‖ ≤ ‖f(1)‖`; the reverse
bound `‖f(1)‖ ≤ ‖f‖‖1‖ = ‖f‖` is the evaluation at `1`. -/
theorem russo_dye_cor_norm (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) :
    ‖unitalBoundCLM f (russo_dye_cor f hf)‖ = ‖f 1‖ :=
  norm_unitalBoundCLM f _

end Matrices

end Theses.A.CStar
