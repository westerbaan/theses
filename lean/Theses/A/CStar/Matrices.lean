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

/-- Definiteness of the 𝒜-valued inner product, in the first argument. -/
private theorem eq_of_inner_left_eq {W : Type*} [NormedAddCommGroup W]
    [Module ℂ W] [SMul 𝒜 W] [CStarModule 𝒜 W] {a b : W}
    (h : ∀ y : W, inner 𝒜 a y = inner 𝒜 b y) : a = b := by
  have h0 : inner 𝒜 (a - b) (a - b) = (0 : 𝒜) := by
    rw [CStarModule.inner_sub_left, h (a - b), sub_self]
  exact sub_eq_zero.mp (CStarModule.inner_self.mp h0)

/-- Definiteness of the 𝒜-valued inner product, in the second argument. -/
private theorem eq_of_inner_right_eq {W : Type*} [NormedAddCommGroup W]
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

/-- **32IV** (cstar.tex:5059, Exercise), part 1: `J = {f ∈ C[0,1] : f(0)=0}`
is a closed (right) ideal of `C[0,1]`, and thus a Hilbert `C[0,1]`-module
with `⟨f, g⟩ = f* g`. -/
theorem paschke_ideal_closed :
    IsClosed {f : C(unitInterval, ℂ) | f 0 = 0} :=
  isClosed_eq (continuous_eval_const 0) continuous_const

/-- **32IV** (cstar.tex:5059, Exercise), part 2: the inclusion `J → C[0,1]`
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

section CauchySchwarz

variable {𝒜 : Type*} {X Y : Type*} [CStarAlgebra 𝒜]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒜 X] [CStarModule 𝒜 X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul 𝒜 Y] [CStarModule 𝒜 Y]

/-- **32VI** (`chilb-cs`, cstar.tex:5096, Proposition (Cauchy–Schwarz)):
`⟨x,y⟩ ⟨y,x⟩ ≤ ‖⟨y,y⟩‖ ⟨x,x⟩` for an 𝒜-valued inner product.  (**32VII**,
Remark: the norm sign cannot be removed; not converted.  Mathlib:
`CStarModule.inner_mul_inner_swap_le`.)

**Convention.** The thesis uses *right* 𝒜-modules with `⟨x, y·b⟩ = ⟨x,y⟩ b`,
whereas Mathlib's `CStarModule` uses the opposite convention `⟪x, a•y⟫ =
a ⟪x,y⟫`, so that `⟪x,y⟫_Mathlib = ⟨y,x⟩_thesis`.  The Lean statement below is
therefore the thesis's inequality with the arguments swapped.  Stated without
the swap it is *false*: for `𝒜 = M₂(ℂ)`, `X = C⋆ᵐᵒᵈ(𝒜,𝒜)`, `x = e₁₁`,
`y = e₂₁` it would assert `e₂₂ ≤ e₁₁`. -/
theorem chilb_cs (x y : X) :
    inner 𝒜 y x * inner 𝒜 x y ≤ ‖inner 𝒜 y y‖ • inner 𝒜 x x := by
  have h := CStarModule.inner_mul_inner_swap_le (A := 𝒜) (x := y) (y := x)
  rwa [CStarModule.norm_sq_eq (A := 𝒜) (x := y)] at h

/-- **32IX** (`chilb-norm-basic`, cstar.tex:5161, Exercise), part 1:
`‖x‖ = ‖⟨x,x⟩‖^{1/2}` is a norm on a pre-Hilbert 𝒜-module `X` — in Mathlib
this is the bundled norm of the `CStarModule` class
(`CStarModule.norm_eq_sqrt_norm_inner_self`), recorded here. -/
theorem chilb_norm_basic_1 (x : X) :
    ‖x‖ = Real.sqrt ‖inner 𝒜 x x‖ :=
  CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒜) x

/-- **32IX** (`chilb-norm-basic`, cstar.tex:5161, Exercise), part 2:
`‖x·b‖ ≤ ‖x‖ ‖b‖` (here in left-action notation `b • x`) and
`‖⟨x,y⟩‖ ≤ ‖x‖ ‖y‖`. -/
theorem chilb_norm_basic_2 (x y : X) (b : 𝒜) :
    ‖b • x‖ ≤ ‖x‖ * ‖b‖ ∧ ‖inner 𝒜 x y‖ ≤ ‖x‖ * ‖y‖ := by
  refine ⟨?_, CStarModule.norm_inner_le X⟩
  have h : inner 𝒜 (b • x) (b • x) = b * inner 𝒜 x x * star b := by
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
  calc ‖inner 𝒜 y (T x)‖ ≤ ‖y‖ * ‖T x‖ := CStarModule.norm_inner_le Y
    _ ≤ ‖y‖ * (B * ‖x‖) := by gcongr; exact h x
    _ = B * ‖y‖ * ‖x‖ := by ring

private theorem norm_adjoint_le (T : X →L[ℂ] Y) (S : Y →L[ℂ] X)
    (h : ModuleAdjointTo 𝒜 ⇑T ⇑S) : ‖S‖ ≤ ‖T‖ := by
  refine S.opNorm_le_bound (norm_nonneg T) fun y => ?_
  refine norm_le_of_inner_bound (𝒜 := 𝒜) (T := ⇑S) (norm_nonneg T)
    (fun y' x' => ?_) y
  rw [← h x' y']
  calc ‖inner 𝒜 (T x') y'‖ ≤ ‖T x'‖ * ‖y'‖ := CStarModule.norm_inner_le Y
    _ ≤ ‖T‖ * ‖x'‖ * ‖y'‖ :=
        mul_le_mul_of_nonneg_right (T.le_opNorm x') (norm_nonneg y')

/-- **32X** (`chilb-form-bounded`, cstar.tex:5178, Lemma), second part: for
an adjointable bounded map, `‖T*‖ = ‖T‖`. -/
theorem chilb_form_bounded_adjoint (T : X →L[ℂ] Y) (S : Y →L[ℂ] X)
    (h : ModuleAdjointTo 𝒜 ⇑T ⇑S) : ‖S‖ = ‖T‖ :=
  le_antisymm (norm_adjoint_le T S h)
    (norm_adjoint_le S T (moduleAdjointTo_symm T S h))

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
        calc ‖inner 𝒜 x (S (T x))‖ ≤ ‖x‖ * ‖S (T x)‖ := CStarModule.norm_inner_le X
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
    0 ≤ inner 𝒜 x ((S.comp T) x) := by
  rw [ContinuousLinearMap.coe_comp', Function.comp_apply, ← h x (T x)]
  exact CStarModule.inner_self_nonneg

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

/-- **33I** (`cstar-matrices`, cstar.tex:5307, Exercise), part 1: an
`N×N`-matrix `A` over `𝒜` gives a bounded module map on `𝒜^N` (Mathlib:
`CStarMatrix.toCLM`), adjoint to the one of its conjugate transpose. -/
theorem cstar_matrices_1 (A : CStarMatrix (Fin N) (Fin N) 𝒜) :
    ModuleAdjointTo 𝒜 ⇑(CStarMatrix.toCLM A) ⇑(CStarMatrix.toCLM (star A)) :=
  fun _ _ => (CStarMatrix.inner_toCLM_conjTranspose_right (M := A)).symm

/-- **33I** (`cstar-matrices`, cstar.tex:5307, Exercise), part 2:
`A ↦ toCLM A` is a linear bijection between the `N×N`-matrices over `𝒜`
and the adjointable bounded module maps on `𝒜^N`. -/
theorem cstar_matrices_2 :
    Function.Injective
      (CStarMatrix.toCLM (A := 𝒜) (m := Fin N) (n := Fin N)) ∧
    ∀ T : C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜) →L[ℂ] C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜),
      (∀ (a : 𝒜) (x : C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜)), T (a • x) = a • T x) →
      ModuleAdjointable 𝒜 ⇑T →
      ∃ A : CStarMatrix (Fin N) (Fin N) 𝒜, CStarMatrix.toCLM A = T := by
  classical
  refine ⟨CStarMatrix.toCLM_injective, fun T hT _ => ?_⟩
  have hsum : ∀ (g : Fin N → C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜)) (k : Fin N),
      (∑ i, g i) k = ∑ i, g i k := fun g k => Finset.sum_apply k Finset.univ g
  set b : Fin N → C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜) :=
    fun i => (WithCStarModule.equiv 𝒜 (Fin N → 𝒜)).symm (Pi.single i 1) with hb
  have hbk : ∀ i k : Fin N, b i k = if k = i then 1 else 0 := by
    intro i k
    rw [hb]
    simp [WithCStarModule.equiv_symm_pi_apply, Pi.single_apply]
  refine ⟨CStarMatrix.ofMatrix fun i j => T (b i) j, ?_⟩
  have hv : ∀ v : C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜), v = ∑ i, v i • b i := by
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
  rw [map_sum, hsum]
  simp only [hT, WithCStarModule.smul_apply, WithCStarModule.equiv_symm_pi_apply,
    CStarMatrix.ofMatrix_apply, Matrix.of_apply, smul_eq_mul]
  rfl

/-- **33I** (`cstar-matrices`, cstar.tex:5307, Exercise), part 3: the
assignment `A ↦ toCLM A` is multiplicative up to the order of composition
(Mathlib's `toCLM` acts by `vecMul`, hence lands in the opposite algebra:
`CStarMatrix.toCLMNonUnitalAlgHom`). -/
theorem cstar_matrices_3 (A B : CStarMatrix (Fin N) (Fin N) 𝒜) :
    CStarMatrix.toCLM (A * B) =
      (CStarMatrix.toCLM B).comp (CStarMatrix.toCLM A) := by
  have h := map_mul (CStarMatrix.toCLMNonUnitalAlgHom (A := 𝒜) (n := Fin N)) A B
  simp only [CStarMatrix.toCLMNonUnitalAlgHom_eq_toCLM, ← MulOpposite.op_mul] at h
  exact MulOpposite.op_injective h

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
    0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => inner 𝒜 (x j) (x i)) :=
  sorry

/-- **33II** (`when-a-matrix-over-a-cstar-algebra-is-positive`,
cstar.tex:5339, Exercise), part 3: the matrix `(aᵢ* aⱼ)ᵢⱼ` is positive for
all `a₁, …, a_N ∈ 𝒜`. -/
theorem cstar_matrix_star_mul_nonneg (a : Fin N → 𝒜) :
    0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j) := by
  obtain _ | n := N
  · have h : (CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j) :
        CStarMatrix (Fin 0) (Fin 0) 𝒜) = 0 := by
      ext i _
      exact i.elim0
    rw [h]
  · set M : CStarMatrix (Fin (n + 1)) (Fin (n + 1)) 𝒜 :=
      CStarMatrix.ofMatrix (Matrix.of fun k i => if k = 0 then a i else 0) with hM
    have h : CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j)
        = star M * M := by
      ext i j
      rw [CStarMatrix.mul_apply]
      simp [hM, CStarMatrix.star_apply, apply_ite star, ite_zero_mul_ite_zero]
    rw [h]
    exact star_mul_self_nonneg M

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
    (hi : IsInvolutionPreserving f) : IsCompletelyPositiveMap f := by
  have hm' : ∀ x y : 𝒜, f (x * y) = f x * f y := hm
  have hi' : ∀ x : 𝒜, f (star x) = star (f x) := hi
  intro n a b
  have h : ∀ i j : Fin n, star (b i) * f (star (a i) * a j) * b j
      = star (f (a i) * b i) * (f (a j) * b j) := by
    intro i j
    rw [hm', hi', star_mul]
    simp [mul_assoc]
  simp_rw [h, sum_star_mul_sum]
  exact star_mul_self_nonneg _

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
