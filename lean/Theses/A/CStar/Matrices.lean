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

All statements of parsecs 320–341 are proved except two: **34VII**
`ccstar_pos_mat` and the **34IX**.2 `cp_commutative_dom` that depends on it.
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

/-- A map adjoint to a bounded module map is automatically linear and bounded
(by **32X**), so it may be taken to be a continuous linear map. -/
theorem exists_clm_adjointTo {T : X →L[ℂ] X} {S : X → X}
    (h : ModuleAdjointTo 𝒜 ⇑T S) : ∃ S' : X →L[ℂ] X, ModuleAdjointTo 𝒜 ⇑T ⇑S' := by
  have h' : ∀ x y : X, inner 𝒜 (T x) y = inner 𝒜 x (S y) := h
  have hbound : ∀ y x : X, ‖inner 𝒜 x (S y)‖ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
    intro y x
    rw [← h x y]
    calc ‖inner 𝒜 (T x) y‖ ≤ ‖T x‖ * ‖y‖ := CStarModule.norm_inner_le X
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
    · calc ‖inner 𝒜 ((T - Tn n) x) y‖ ≤ ‖(T - Tn n) x‖ * ‖y‖ := CStarModule.norm_inner_le X
        _ ≤ ‖T - Tn n‖ * ‖x‖ * ‖y‖ := by
            gcongr
            exact (T - Tn n).le_opNorm x
    · calc ‖inner 𝒜 x ((Sn n - S) y)‖ ≤ ‖x‖ * ‖(Sn n - S) y‖ := CStarModule.norm_inner_le X
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

/-- **32XV** (`chilb-vector-states-order-separating`, cstar.tex:5268,
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
positive part).  Cf. `exists_negPart` below, of which this is the first half;
it is repeated here because that lemma is stated further down the file. -/
private theorem negPart_conj_aux {M : Type*} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] {a : M} (hsa : IsSelfAdjoint a) :
    a⁻ * a * a⁻ = -(a⁻ * a⁻ * a⁻) := by
  conv_lhs => arg 1; arg 2; rw [← CFC.posPart_sub_negPart a hsa]
  rw [mul_sub, sub_mul, CFC.negPart_mul_posPart, zero_mul, zero_sub]

/-- A self-adjoint element whose negative part cubes to zero is positive.  Cf.
`exists_negPart` below, of which this is the second half. -/
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

/-- **32XV** (`chilb-vector-states-order-separating`, cstar.tex:5268,
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

set_option maxHeartbeats 400000 in
/-- **32XV** (`chilb-vector-states-order-separating`, cstar.tex:5268,
Exercise), part 3: `‖T‖ = sup_{‖x‖ ≤ 1} ‖⟨x, Tx⟩‖` for self-adjoint `T`. -/
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
    calc F x ≤ ‖(x : X)‖ * ‖T (x : X)‖ := CStarModule.norm_inner_le X
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
  refine le_antisymm ?_ hMle
  -- The heart of the matter: `‖p‖ ≤ M` whenever `p = s²` with `s* a s = ± p* p`
  -- for a self-adjoint `s`, since then `‖⟨s x, a (s x)⟩‖ = ‖p x‖²` while
  -- `‖s x‖ ≤ ‖s‖ ‖x‖` and `‖s‖² = ‖p‖`.
  have key : ∀ p s : Bax 𝒜 X, star s = s → s * s = p →
      (star s * a * s = star p * p ∨ star s * a * s = -(star p * p)) → ‖p‖ ≤ M := by
    intro p s hssa hsp hcase
    have hns : ‖s‖ ^ 2 = ‖p‖ := by
      have hn : ‖star s * s‖ = ‖s‖ * ‖s‖ := CStarRing.norm_star_mul_self
      rw [hssa, hsp] at hn
      rw [sq, ← hn]
    rcases eq_or_lt_of_le (norm_nonneg s) with h0 | h0
    · have hp0 : ‖p‖ = 0 := by rw [← hns, ← h0]; ring
      rw [hp0]; exact hM0
    have hquad : ∀ x : X, ‖(p : X →L[ℂ] X) x‖ ^ 2 ≤ M * ‖p‖ * ‖x‖ ^ 2 := by
      intro x
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (‖s‖ * ‖x‖)⁻¹ := ⟨_, rfl⟩
      have hcpos : 0 < c := by rw [hc]; positivity
      obtain ⟨y, hy⟩ : ∃ y : X, y = (s : X →L[ℂ] X) x := ⟨_, rfl⟩
      have hyn : ‖y‖ ≤ ‖s‖ * ‖x‖ := by
        rw [hy, bax_norm_coe]
        exact (s : X →L[ℂ] X).le_opNorm x
      have hw : ‖(c : ℂ) • y‖ ≤ 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos, hc,
          inv_mul_le_iff₀ (by positivity)]
        simpa using hyn
      have hle := le_ciSup hbdd (⟨(c : ℂ) • y, hw⟩ : {x : X // ‖x‖ ≤ 1})
      -- `⟨cy, T(cy)⟩ = c² ⟨y, T y⟩ = ± c² ⟨p x, p x⟩`
      have he1 : inner 𝒜 ((c : ℂ) • y) (T ((c : ℂ) • y))
          = ((c : ℂ) * (c : ℂ)) • inner 𝒜 y (T y) := by
        rw [map_smul, CStarModule.inner_smul_right_complex,
          CStarModule.inner_smul_left_complex, smul_smul, Complex.star_def,
          Complex.conj_ofReal]
      have he2 : inner 𝒜 y (T y) = inner 𝒜 x (((star s * a * s : Bax 𝒜 X) : X →L[ℂ] X) x) := by
        rw [bax_inner_conj, ← hy, ha]
      have he3 : ‖inner 𝒜 x (((star p * p : Bax 𝒜 X) : X →L[ℂ] X) x)‖
          = ‖(p : X →L[ℂ] X) x‖ ^ 2 := by
        rw [bax_inner_star_mul, ← CStarModule.norm_sq_eq (A := 𝒜)]
      have he4 : ‖inner 𝒜 y (T y)‖ = ‖(p : X →L[ℂ] X) x‖ ^ 2 := by
        rw [he2]
        rcases hcase with hcase | hcase <;> rw [hcase] <;> simpa using he3
      have he5 : F (⟨(c : ℂ) • y, hw⟩ : {x : X // ‖x‖ ≤ 1})
          = c ^ 2 * ‖(p : X →L[ℂ] X) x‖ ^ 2 := by
        rw [hF]
        simp only
        rw [he1, norm_smul, he4, ← Complex.ofReal_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
        ring
      rw [he5] at hle
      have hcc : c ^ 2 * (‖s‖ * ‖x‖) ^ 2 = 1 := by
        rw [hc, ← mul_pow, inv_mul_cancel₀ (by positivity), one_pow]
      calc ‖(p : X →L[ℂ] X) x‖ ^ 2
          = c ^ 2 * ‖(p : X →L[ℂ] X) x‖ ^ 2 * (‖s‖ * ‖x‖) ^ 2 := by
            rw [mul_comm (c ^ 2) _, mul_assoc, hcc, mul_one]
        _ ≤ M * (‖s‖ * ‖x‖) ^ 2 := by
            exact mul_le_mul_of_nonneg_right hle (by positivity)
        _ = M * ‖p‖ * ‖x‖ ^ 2 := by rw [mul_pow, ← hns]; ring
    -- hence `‖p‖² ≤ M ‖p‖`, so `‖p‖ ≤ M`
    have hop : ‖p‖ ≤ Real.sqrt (M * ‖p‖) := by
      rw [bax_norm_coe]
      refine (p : X →L[ℂ] X).opNorm_le_bound (Real.sqrt_nonneg _) fun x => ?_
      calc ‖(p : X →L[ℂ] X) x‖ = Real.sqrt (‖(p : X →L[ℂ] X) x‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (M * ‖p‖ * ‖x‖ ^ 2) := Real.sqrt_le_sqrt (hquad x)
        _ = Real.sqrt (M * ‖p‖) * ‖x‖ := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
    nlinarith [Real.sq_sqrt (mul_nonneg hM0 (norm_nonneg p)), norm_nonneg p,
      Real.sqrt_nonneg (M * ‖p‖)]
  -- apply `key` to the positive and to the negative part of `a`
  have hpq : (a⁺ : Bax 𝒜 X) * a⁻ = 0 := CFC.posPart_mul_negPart a
  have hqp : (a⁻ : Bax 𝒜 X) * a⁺ = 0 := CFC.negPart_mul_posPart a
  have hsplit : (a⁺ : Bax 𝒜 X) - a⁻ = a := CFC.posPart_sub_negPart a hsa
  have hkey1 : ‖(a⁺ : Bax 𝒜 X)‖ ≤ M := by
    obtain ⟨s, hsnn, hss⟩ : ∃ s : Bax 𝒜 X, 0 ≤ s ∧ s * s = a⁺ :=
      ⟨CFC.sqrt _, CFC.sqrt_nonneg _, CFC.sqrt_mul_sqrt_self _ (CFC.posPart_nonneg a)⟩
    have hssa : star s = s := hsnn.isSelfAdjoint.star_eq
    have hsq : s * (a⁻ : Bax 𝒜 X) = 0 := by
      refine CStarRing.star_mul_self_eq_zero_iff _ |>.mp ?_
      rw [star_mul, hssa, (CFC.negPart_nonneg a).isSelfAdjoint.star_eq]
      calc (a⁻ : Bax 𝒜 X) * s * (s * a⁻) = a⁻ * (s * s) * a⁻ := by noncomm_ring
        _ = 0 := by rw [hss, hqp, zero_mul]
    refine key _ s hssa hss (Or.inl ?_)
    have e1 : star s * a * s = s * ((a⁺ : Bax 𝒜 X) - a⁻) * s := by rw [hssa, hsplit]
    rw [e1, mul_sub, sub_mul, hsq, zero_mul, sub_zero,
      (CFC.posPart_nonneg a).isSelfAdjoint.star_eq, ← hss]
    noncomm_ring
  have hkey2 : ‖(a⁻ : Bax 𝒜 X)‖ ≤ M := by
    obtain ⟨s, hsnn, hss⟩ : ∃ s : Bax 𝒜 X, 0 ≤ s ∧ s * s = a⁻ :=
      ⟨CFC.sqrt _, CFC.sqrt_nonneg _, CFC.sqrt_mul_sqrt_self _ (CFC.negPart_nonneg a)⟩
    have hssa : star s = s := hsnn.isSelfAdjoint.star_eq
    have hsp : s * (a⁺ : Bax 𝒜 X) = 0 := by
      refine CStarRing.star_mul_self_eq_zero_iff _ |>.mp ?_
      rw [star_mul, hssa, (CFC.posPart_nonneg a).isSelfAdjoint.star_eq]
      calc (a⁺ : Bax 𝒜 X) * s * (s * a⁺) = a⁺ * (s * s) * a⁺ := by noncomm_ring
        _ = 0 := by rw [hss, hpq, zero_mul]
    refine key _ s hssa hss (Or.inr ?_)
    have e1 : star s * a * s = s * ((a⁺ : Bax 𝒜 X) - a⁻) * s := by rw [hssa, hsplit]
    rw [e1, mul_sub, sub_mul, hsp, zero_mul, zero_sub,
      (CFC.negPart_nonneg a).isSelfAdjoint.star_eq, ← hss]
    noncomm_ring
  calc ‖T‖ = ‖a‖ := hanorm.symm
    _ = max ‖(a⁺ : Bax 𝒜 X)‖ ‖(a⁻ : Bax 𝒜 X)‖ := hsa.norm_eq_max_norm_posPart_negPart
    _ ≤ M := max_le hkey1 hkey2

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

/-- `0 ≤ a` in a C*-algebra gives `a = b* b`.  Stated for an abstract C*-algebra
because Mathlib's typeclass search cannot find the continuous functional calculus
instances for `CStarMatrix` directly (there are two syntactically distinct routes
to `Algebra ℝ (CStarMatrix n n 𝒜)`); going through an abstract `M` sidesteps this. -/
private theorem exists_star_mul_self {M : Type*} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] {a : M} (ha : 0 ≤ a) : ∃ b, a = star b * b :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha

/-- The negative part `b = a⁻` of a self-adjoint `a`, in the only form needed
below: `b a b = -b³`, and `a` is positive as soon as `b³` vanishes.  Again stated
for an abstract C*-algebra `M`, see `exists_star_mul_self`. -/
private theorem exists_negPart {M : Type*} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] {a : M} (hsa : IsSelfAdjoint a) :
    ∃ b : M, 0 ≤ b ∧ b * a * b = -(b * b * b) ∧ (b * b * b = 0 → 0 ≤ a) := by
  refine ⟨a⁻, CFC.negPart_nonneg a, ?_, ?_⟩
  · conv_lhs => arg 1; arg 2; rw [← CFC.posPart_sub_negPart a hsa]
    rw [mul_sub, sub_mul, CFC.negPart_mul_posPart, zero_mul, zero_sub]
  · intro h3
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

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- An anti-self-adjoint `𝒜`-valued matrix `d` (`dᵢⱼ* = -dⱼᵢ`) whose sesquilinear
form vanishes identically is zero.  This is the polarisation step behind the
self-adjointness half of **33II**.1. -/
private theorem sesq_eq_zero {d : Fin N → Fin N → 𝒜} (hd : ∀ i j, star (d i j) = -d j i)
    (h : ∀ a : Fin N → 𝒜, ∑ i, ∑ j, star (a i) * d i j * a j = 0) (p q : Fin N) :
    d p q = 0 := by
  classical
  have hsingle : ∀ (p q : Fin N) (x y : 𝒜),
      ∑ i, ∑ j, star ((Pi.single p x : Fin N → 𝒜) i) * d i j * (Pi.single q y : Fin N → 𝒜) j
        = star x * d p q * y := by
    intro p q x y
    simp [Pi.single_apply, apply_ite star, ite_mul, mul_ite]
  have hbil : ∀ u v : Fin N → 𝒜, ∑ i, ∑ j, star ((u + v) i) * d i j * (u + v) j
      = ((∑ i, ∑ j, star (u i) * d i j * u j) + ∑ i, ∑ j, star (u i) * d i j * v j)
        + ((∑ i, ∑ j, star (v i) * d i j * u j) + ∑ i, ∑ j, star (v i) * d i j * v j) := by
    intro u v
    simp only [Pi.add_apply, star_add, add_mul, mul_add, Finset.sum_add_distrib]
    abel
  have hdiag : ∀ r, d r r = 0 := by
    intro r
    have := h (Pi.single r 1)
    rw [hsingle r r 1 1] at this
    simpa using this
  have key : ∀ (p q : Fin N) (x y : 𝒜), star x * d p q * y + star y * d q p * x = 0 := by
    intro p q x y
    have := h (Pi.single p x + Pi.single q y)
    rw [hbil, hsingle p p x x, hsingle p q x y, hsingle q p y x, hsingle q q y y,
      hdiag p, hdiag q] at this
    simpa using this
  have hqp : d q p = -star (d p q) := by rw [hd p q]; rw [neg_neg]
  have hsa : ∀ x y : 𝒜, star (star x * d p q * y) = star x * d p q * y := by
    intro x y
    have hk := key p q x y
    have he : star y * d q p * x = -star (star x * d p q * y) := by
      rw [hqp, star_mul, star_mul, star_star]
      noncomm_ring
    rw [he] at hk
    exact (add_neg_eq_zero.mp hk).symm
  have h1 : star (d p q) = d p q := by simpa using hsa 1 1
  have h2 := hsa 1 (Complex.I • (1 : 𝒜))
  rw [star_one, one_mul, mul_smul_comm, mul_one, star_smul, h1, Complex.star_def,
    Complex.conj_I] at h2
  have h3 : ((-Complex.I) - Complex.I) • d p q = 0 := by rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 (by norm_num [Complex.ext_iff])
  · exact h4

section MatrixOrder

variable [PartialOrder (CStarMatrix (Fin N) (Fin N) 𝒜)]
  [StarOrderedRing (CStarMatrix (Fin N) (Fin N) 𝒜)]

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder (CStarMatrix (Fin N) (Fin N) 𝒜)]
  [StarOrderedRing (CStarMatrix (Fin N) (Fin N) 𝒜)] in
/-- The `(k,l)` entry of `M* A M`. -/
private theorem conj_apply (M A : CStarMatrix (Fin N) (Fin N) 𝒜) (k l : Fin N) :
    (star M * A * M) k l = ∑ i, ∑ j, star (M i k) * A i j * M j l := by
  rw [CStarMatrix.mul_apply]
  simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The diagonal entries of a positive matrix are positive. -/
private theorem diag_nonneg {B : CStarMatrix (Fin N) (Fin N) 𝒜} (hB : 0 ≤ B) (k : Fin N) :
    0 ≤ B k k := by
  obtain ⟨C, rfl⟩ := exists_star_mul_self hB
  rw [CStarMatrix.mul_apply]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [CStarMatrix.star_apply]
  exact star_mul_self_nonneg _

/-- A column of a positive matrix vanishes as soon as its diagonal entry does. -/
private theorem col_eq_zero {B : CStarMatrix (Fin N) (Fin N) 𝒜} (hB : 0 ≤ B)
    {k : Fin N} (h : B k k = 0) (i : Fin N) : B i k = 0 := by
  obtain ⟨C, rfl⟩ := exists_star_mul_self hB
  have hC : ∀ m, C m k = 0 := by
    intro m
    rw [CStarMatrix.mul_apply] at h
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => by
      rw [CStarMatrix.star_apply]; exact star_mul_self_nonneg (C m k))).mp h m (Finset.mem_univ m)
    rw [CStarMatrix.star_apply] at this
    exact CStarRing.star_mul_self_eq_zero_iff _ |>.mp this
  rw [CStarMatrix.mul_apply]
  simp [CStarMatrix.star_apply, hC]

/-- A positive matrix with vanishing diagonal is zero. -/
private theorem eq_zero_of_diag_eq_zero {B : CStarMatrix (Fin N) (Fin N) 𝒜} (hB : 0 ≤ B)
    (h : ∀ k, B k k = 0) : B = 0 := by
  ext i j
  exact col_eq_zero hB (h j) i

/-- **33II** (`when-a-matrix-over-a-cstar-algebra-is-positive`,
cstar.tex:5339, Exercise), part 1: an `N×N`-matrix `A` over `𝒜` is positive
iff `0 ≤ ∑_{i,j} aᵢ* Aᵢⱼ aⱼ` for all `a₁, …, a_N ∈ 𝒜`. -/
theorem cstar_matrix_positive_iff (A : CStarMatrix (Fin N) (Fin N) 𝒜) :
    0 ≤ A ↔ ∀ a : Fin N → 𝒜, 0 ≤ ∑ i, ∑ j, star (a i) * A i j * a j := by
  constructor
  · intro hA a
    rcases isEmpty_or_nonempty (Fin N) with _ | ⟨⟨k⟩⟩
    · simp
    · set M : CStarMatrix (Fin N) (Fin N) 𝒜 := CStarMatrix.ofMatrix (Matrix.of fun i _ => a i)
        with hM
      have hMe : ∀ i j : Fin N, M i j = a i := fun _ _ => rfl
      have h2 := diag_nonneg (star_left_conjugate_nonneg hA M) k
      rw [conj_apply] at h2
      simpa only [hMe] using h2
  · intro h
    have hsa : IsSelfAdjoint A := by
      have hstar : ∀ a : Fin N → 𝒜, star (∑ i, ∑ j, star (a i) * A i j * a j)
          = ∑ i, ∑ j, star (a i) * star (A j i) * a j := by
        intro a
        simp only [star_sum, star_mul, star_star, mul_assoc]
        exact Finset.sum_comm
      have hzero : ∀ a : Fin N → 𝒜,
          ∑ i, ∑ j, star (a i) * (A i j - star (A j i)) * a j = 0 := by
        intro a
        have hd : (∑ i, ∑ j, star (a i) * A i j * a j)
            - (∑ i, ∑ j, star (a i) * star (A j i) * a j) = 0 := by
          rw [← hstar a, (h a).isSelfAdjoint.star_eq, sub_self]
        rw [← hd]
        simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
      have hd : ∀ i j : Fin N,
          star (A i j - star (A j i)) = -(A j i - star (A i j)) := by
        intro i j
        rw [star_sub, star_star]
        abel
      change star A = A
      ext i j
      rw [CStarMatrix.star_apply]
      exact (sub_eq_zero.mp (sesq_eq_zero hd hzero i j)).symm
    obtain ⟨B, hB0, hBAB, hfin⟩ := exists_negPart hsa
    have hBsa : star B = B := hB0.isSelfAdjoint.star_eq
    have hB3 : 0 ≤ B * B * B := by
      have := star_left_conjugate_nonneg hB0 B
      rwa [hBsa] at this
    refine hfin (eq_zero_of_diag_eq_zero hB3 fun k => ?_)
    have hx : 0 ≤ (B * A * B) k k := by
      have := h (fun i => B i k)
      rw [← conj_apply B A k k, hBsa] at this
      exact this
    have hsum : (B * A * B) k k + (B * B * B) k k = 0 := by
      rw [hBAB]
      simp
    have hneg : (B * B * B) k k = -((B * A * B) k k) := eq_neg_of_add_eq_zero_right hsum
    exact le_antisymm (hneg ▸ neg_nonpos.mpr hx) (diag_nonneg hB3 k)

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
`IsVNTensor` has.  (See `QUESTIONS.md` B5: the positivity clause it
proposes to *add* is derivable.)

Lives here rather than in `A/Proc/Tensor.lean` (where it was first proved)
because its content is about matrices over C*-algebras and it is needed by
`B/Dils`, which imports this file but not `A/Proc`; see `QUESTIONS.md` D3. -/
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

private def e00M2 : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix !![1, 0; 0, 0]
private def e01M2 : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix !![0, 1; 0, 0]
private def e10M2 : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix !![0, 0; 1, 0]

/-- `star witnessM2 * witnessM2` is the maximally entangled projection
`(eᵢⱼ)ᵢⱼ ∈ M₂(M₂(ℂ))`, whose partial transpose is the swap and hence not positive. -/
private def witnessM2 : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
  CStarMatrix.ofMatrix !![e00M2, e01M2; 0, 0]

/-- **33III** (`mnf`, cstar.tex:5358, Exercise), part 3: `M_N f` need not be
positive when `f` is: the transpose map on `M₂` is positive but `M₂` of it
is not.  (That `M_N f` need not be bounded uniformly in `N` when `f` is
bounded is not converted.) -/
theorem mnf_not_positive :
    ∃ f : CStarMatrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ,
      IsPositiveMap f ∧
      ¬∀ A : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin 2) (Fin 2) ℂ),
        0 ≤ A → 0 ≤ A.map ⇑f := by
  refine ⟨transposeM2, transposeM2_pos, ?_⟩
  intro hpos
  have hA0 : (0 : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin 2) (Fin 2) ℂ))
      ≤ star witnessM2 * witnessM2 := star_mul_self_nonneg _
  have hS := (cstar_matrix_positive_iff ((star witnessM2 * witnessM2).map ⇑transposeM2)).mp
    (hpos _ hA0) ![e10M2, -e00M2]
  have hval : ∑ i, ∑ j, star ((![e10M2, -e00M2] : Fin 2 → CStarMatrix (Fin 2) (Fin 2) ℂ) i)
      * ((star witnessM2 * witnessM2).map ⇑transposeM2) i j
      * (![e10M2, -e00M2] : Fin 2 → CStarMatrix (Fin 2) (Fin 2) ℂ) j
      = -(e00M2 + e00M2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [witnessM2, e00M2, e01M2, e10M2, Fin.sum_univ_two, CStarMatrix.mul_apply,
        CStarMatrix.star_apply, CStarMatrix.map_apply, transposeM2_apply,
        CStarMatrix.ofMatrix_apply]
  rw [hval] at hS
  have h00 : (0 : CStarMatrix (Fin 2) (Fin 2) ℂ) ≤ e00M2 := by
    have h : e00M2 = star e00M2 * e00M2 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [e00M2, CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two,
          CStarMatrix.ofMatrix_apply]
    rw [h]
    exact star_mul_self_nonneg _
  have hz : e00M2 + e00M2 = 0 :=
    le_antisymm (by simpa using neg_nonneg.mp hS) (add_nonneg h00 h00)
  have hcontra := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) ℂ => M 0 0) hz
  simp [e00M2, CStarMatrix.ofMatrix_apply] at hcontra

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
      A 0 1 * star (A 0 1) ≤ ‖A 1 1‖ • A 0 0 := by
  have h10 : A 1 0 = star (A 0 1) := by
    conv_lhs => rw [← hA.isSelfAdjoint.star_eq]
    rw [CStarMatrix.star_apply]
  have hE : ∀ x y : 𝒜, 0 ≤ star x * A 0 0 * x + star x * A 0 1 * y
      + (star y * star (A 0 1) * x + star y * A 1 1 * y) := by
    intro x y
    have := (cstar_matrix_positive_iff A).mp hA ![x, y]
    simpa [Fin.sum_univ_two, h10] using this
  have main : ∀ p a q : 𝒜, 0 ≤ p → 0 < ‖p‖ →
      (∀ x y : 𝒜, 0 ≤ star x * p * x + star x * a * y
        + (star y * star a * x + star y * q * y)) →
      star a * a ≤ ‖p‖ • q := by
    intro p a q hp hs hE'
    have hcomp := hE' (-a) (‖p‖ • (1 : 𝒜))
    have heq : star (-a) * p * (-a) + star (-a) * a * (‖p‖ • (1 : 𝒜))
        + (star (‖p‖ • (1 : 𝒜)) * star a * (-a)
          + star (‖p‖ • (1 : 𝒜)) * q * (‖p‖ • (1 : 𝒜)))
        = star a * p * a - (‖p‖ • (star a * a) + ‖p‖ • (star a * a))
          + (‖p‖ * ‖p‖) • q := by
      simp only [star_neg, star_smul, star_trivial, star_one, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one, neg_mul, mul_neg, neg_neg, smul_neg, smul_smul]
      abel
    rw [heq] at hcomp
    have hconj : star a * p * a ≤ ‖p‖ • (star a * a) :=
      CStarAlgebra.star_left_conjugate_le_norm_smul hp.isSelfAdjoint
    have hstep : (0 : 𝒜) ≤ ‖p‖ • (star a * a)
        - (‖p‖ • (star a * a) + ‖p‖ • (star a * a)) + (‖p‖ * ‖p‖) • q :=
      hcomp.trans (by gcongr)
    have h4 : ‖p‖ • (star a * a) ≤ ‖p‖ • (‖p‖ • q) := by
      rw [smul_smul]
      have e : ‖p‖ • (star a * a) - (‖p‖ • (star a * a) + ‖p‖ • (star a * a))
          + (‖p‖ * ‖p‖) • q = (‖p‖ * ‖p‖) • q - ‖p‖ • (star a * a) := by abel
      rw [e, sub_nonneg] at hstep
      exact hstep
    have h5 := smul_le_smul_of_nonneg_left h4 (le_of_lt (inv_pos.mpr hs))
    rwa [smul_smul, smul_smul, inv_mul_cancel₀ hs.ne', one_smul, one_smul] at h5
  constructor
  · rcases eq_or_lt_of_le (norm_nonneg (A 0 0)) with hs | hs
    · have hp0 : A 0 0 = 0 := norm_eq_zero.mp hs.symm
      have h01 : A 0 1 = 0 := by
        have hz := col_eq_zero hA hp0 (1 : Fin 2)
        rw [h10] at hz
        exact star_eq_zero.mp hz
      rw [h01, ← hs]
      simp
    · exact main _ _ _ (diag_nonneg hA 0) hs hE
  · rcases eq_or_lt_of_le (norm_nonneg (A 1 1)) with hs | hs
    · have hq0 : A 1 1 = 0 := norm_eq_zero.mp hs.symm
      have h01 : A 0 1 = 0 := col_eq_zero hA hq0 (0 : Fin 2)
      rw [h01, ← hs]
      simp
    · have := main (A 1 1) (star (A 0 1)) (A 0 0) (diag_nonneg hA 1) hs
        (fun x y => by
          have h := hE y x
          rw [star_star]
          have e : star x * A 1 1 * x + star x * star (A 0 1) * y
              + (star y * A 0 1 * x + star y * A 0 0 * y)
              = star y * A 0 0 * y + star y * A 0 1 * x
                + (star x * star (A 0 1) * y + star x * A 1 1 * x) := by abel
          rw [e]
          exact h)
      rwa [star_star] at this

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
    have h10 := col_eq_zero hMpos h00 1
    simp only [hM, hv, CStarMatrix.ofMatrix_apply, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, sub_eq_zero] at h10
    exact h10
  have := key (star b)
  rwa [star_star, hi b, star_star] at this

/-! ## Parsec 341 (34a): Russo–Dye

**34aI** (cstar.tex:5724): introduction — nothing to formalize. -/

/-- Auxiliary for **34aII**, over a `Fintype`: a *positive combination*
`∑ₖ λₖ pₖ` of positive elements has `‖∑ₖ λₖ pₖ‖ ≤ (maxₖ |λₖ|) ‖∑ₖ pₖ‖`.

This is **34XVI** `cp_russo_dye` applied to the positive map
`c ↦ ∑ₖ cₖ pₖ` out of the (commutative, finite-dimensional) C*-algebra
`ι → ℂ`, whose complete positivity is immediate: `∑ᵢⱼ bᵢ* φ(c̄ᵢcⱼ) bⱼ`
regroups as `∑ₖ dₖ* pₖ dₖ` with `dₖ = ∑ᵢ cᵢ(k) bᵢ`.  So this is the one
instance of **34IX**.2 (`cp_commutative_dom`, still `sorry`) that the
Russo–Dye argument needs, and it needs no approximation. -/
private theorem norm_sum_smul_le_aux {ι : Type*} [Fintype ι] (p : ι → ℬ)
    (hp : ∀ k, 0 ≤ p k) (l : ι → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ k, ‖l k‖ ≤ M) :
    ‖∑ k, l k • p k‖ ≤ M * ‖∑ k, p k‖ := by
  set φ : (ι → ℂ) →ₗ[ℂ] ℬ :=
    { toFun := fun c => ∑ k, c k • p k
      map_add' := by intro c d; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro r c; simp [smul_smul, Finset.smul_sum] } with hφ
  have hφa : ∀ c : ι → ℂ, φ c = ∑ k, c k • p k := fun c => rfl
  have hφ1 : φ 1 = ∑ k, p k := by simp [hφa]
  have hcp : IsCompletelyPositiveMap φ := by
    intro n a b
    have key : ∀ i j : Fin n, star (b i) * φ (star (a i) * a j) * b j
        = ∑ k, star (a i k • b i) * p k * (a j k • b j) := by
      intro i j
      rw [hφa, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.mul_apply, Pi.star_apply, star_smul, RCLike.star_def,
        smul_mul_assoc, mul_smul_comm, smul_smul]
      ring_nf
    calc ∑ i, ∑ j, star (b i) * φ (star (a i) * a j) * b j
        = ∑ i, ∑ j, ∑ k, star (a i k • b i) * p k * (a j k • b j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j
      _ = ∑ i, ∑ k, ∑ j, star (a i k • b i) * p k * (a j k • b j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, star (a i k • b i) * p k * (a j k • b j) := Finset.sum_comm
      _ = ∑ k, star (∑ i, a i k • b i) * p k * (∑ j, a j k • b j) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [star_sum, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ ≥ 0 := by
          refine Finset.sum_nonneg fun k _ => ?_
          obtain ⟨q, hq⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hp k)
          rw [hq]
          have e : star (∑ i, a i k • b i) * (star q * q) * (∑ j, a j k • b j)
              = star (q * ∑ i, a i k • b i) * (q * ∑ i, a i k • b i) := by
            rw [star_mul]; noncomm_ring
          rw [e]
          exact star_mul_self_nonneg _
  have h := cp_russo_dye φ hcp l
  rw [hφ1, hφa] at h
  refine h.trans ?_
  have hl : ‖l‖ ≤ M := by rw [pi_norm_le_iff_of_nonneg hM0]; exact hM
  calc ‖∑ k, p k‖ * ‖l‖ ≤ ‖∑ k, p k‖ * M :=
        mul_le_mul_of_nonneg_left hl (norm_nonneg _)
    _ = M * ‖∑ k, p k‖ := mul_comm _ _

/-- Auxiliary for **34aII**, the `Finset` form of `norm_sum_smul_le_aux`. -/
private theorem norm_sum_smul_le_of_nonneg {ι : Type*} (s : Finset ι) (p : ι → ℬ)
    (hp : ∀ k ∈ s, 0 ≤ p k) (l : ι → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ k ∈ s, ‖l k‖ ≤ M) :
    ‖∑ k ∈ s, l k • p k‖ ≤ M * ‖∑ k ∈ s, p k‖ := by
  rw [← Finset.sum_coe_sort s fun k => l k • p k, ← Finset.sum_coe_sort s p]
  exact norm_sum_smul_le_aux (fun k : {x // x ∈ s} => p k) (fun k => hp k k.2)
    (fun k : {x // x ∈ s} => l k) M hM0 fun k => hM k k.2

/-- **34aII** (`normal-russo-dye`, cstar.tex:5751, Lemma):
`‖f(a)‖ ≤ ‖f(1)‖ ‖a‖` for every p-map `f : 𝒜 → ℬ` and *normal* `a ∈ 𝒜`.

*Class 2 — different route.*  The thesis restricts `f` to the commutative
C*-subalgebra `C*(a)` and invokes **34IX**.2 (`cp_commutative_dom`, a
positive map out of a commutative C*-algebra is cp) and then **34XVI**
`cp_russo_dye`.  `cp_commutative_dom` is still `sorry`, and its own proof
needs **34VII** `ccstar-pos-mat` — a partition-of-unity approximation on the
Gelfand spectrum.  We run that approximation *directly on `a`* instead,
where it is explicit: cover the compact `spec(a) ⊆ ℂ` by finitely many
`δ`-balls centred at points `λ` of the spectrum, turn the tent functions
`max(0, δ − |z − λ|)` into a partition of unity `ψ_λ` by dividing by their
sum, and put `g_λ := ψ_λ(a)` through the continuous functional calculus.
Then `g_λ ≥ 0`, `∑ g_λ = 1`, `‖a − ∑ λ g_λ‖ ≤ δ`, and the approximant is
handled by `norm_sum_smul_le_of_nonneg`, which is the only instance of
`cp_commutative_dom` involved and is elementary.  No Gelfand duality and no
Urysohn lemma are needed. -/
theorem normal_russo_dye (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) (a : 𝒜)
    (ha : IsStarNormal a) : ‖f a‖ ≤ ‖f 1‖ * ‖a‖ := by
  rcases subsingleton_or_nontrivial 𝒜 with _ | _
  · rw [Subsingleton.elim a 0, map_zero, norm_zero]
    positivity
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set C : ℝ := 2 * ‖f 1‖ + 1 with hC
  have hCpos : 0 < C := by positivity
  set δ : ℝ := ε / C with hδ
  have hδpos : 0 < δ := div_pos hε hCpos
  -- a finite subcover of the spectrum by `δ`-balls centred in the spectrum
  have hcov : spectrum ℂ a ⊆ ⋃ lam : spectrum ℂ a, Metric.ball (lam : ℂ) δ := fun z hz =>
    Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self hδpos⟩
  obtain ⟨S, hS⟩ := (spectrum.isCompact a).elim_finite_subcover
    (fun lam : spectrum ℂ a => Metric.ball (lam : ℂ) δ) (fun _ => Metric.isOpen_ball) hcov
  -- the tent functions and the partition of unity they induce
  set φ : spectrum ℂ a → ℂ → ℝ := fun lam z => max 0 (δ - dist z (lam : ℂ)) with hφdef
  set Φ : ℂ → ℝ := fun z => ∑ lam ∈ S, φ lam z with hΦdef
  have hφnn : ∀ lam z, 0 ≤ φ lam z := fun _ _ => le_max_left _ _
  have hφsupp : ∀ lam z, φ lam z * dist z (lam : ℂ) ≤ φ lam z * δ := by
    intro lam z
    rcases le_or_gt δ (dist z (lam : ℂ)) with h | h
    · have : φ lam z = 0 := max_eq_left (by linarith)
      simp [this]
    · exact mul_le_mul_of_nonneg_left h.le (hφnn lam z)
  have hφcont : ∀ lam, Continuous (φ lam) := fun lam =>
    continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have hΦcont : Continuous Φ := continuous_finsetSum _ fun lam _ => hφcont lam
  have hΦpos : ∀ z ∈ spectrum ℂ a, 0 < Φ z := by
    intro z hz
    obtain ⟨lam, hlamS, hlam⟩ := Set.mem_iUnion₂.mp (hS hz)
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun lam => φ lam z)
      (fun i _ => hφnn i z) hlamS)
    have : dist z (lam : ℂ) < δ := Metric.mem_ball.mp hlam
    simp only [hφdef]
    exact lt_max_of_lt_right (by linarith)
  set ψ : spectrum ℂ a → ℂ → ℂ := fun lam z => ((φ lam z / Φ z : ℝ) : ℂ) with hψdef
  have hψcont : ∀ lam, ContinuousOn (ψ lam) (spectrum ℂ a) := fun lam =>
    Complex.continuous_ofReal.comp_continuousOn
      ((hφcont lam).continuousOn.div hΦcont.continuousOn fun z hz => (hΦpos z hz).ne')
  have hψnn : ∀ lam, ∀ z ∈ spectrum ℂ a, 0 ≤ ψ lam z := by
    intro lam z hz
    simp only [hψdef]
    exact Complex.zero_le_real.mpr (div_nonneg (hφnn lam z) (hΦpos z hz).le)
  have hψsum : ∀ z ∈ spectrum ℂ a, ∑ lam ∈ S, ψ lam z = 1 := by
    intro z hz
    simp only [hψdef, ← Complex.ofReal_sum, ← Finset.sum_div]
    rw [div_self (hΦpos z hz).ne']
    norm_num
  -- transport it into `𝒜` by the continuous functional calculus
  set g : spectrum ℂ a → 𝒜 := fun lam => cfc (ψ lam) a with hgdef
  have hgnn : ∀ lam, 0 ≤ g lam := fun lam => cfc_nonneg (hψnn lam)
  have hgsum : ∑ lam ∈ S, g lam = 1 := by
    rw [hgdef, ← cfc_sum _ a S fun lam _ => hψcont lam]
    rw [cfc_congr (g := 1) (fun z hz => by simpa [Finset.sum_apply] using hψsum z hz)]
    exact cfc_one ℂ a
  set b : 𝒜 := ∑ lam ∈ S, (lam : ℂ) • g lam with hbdef
  have hmulcont : ∀ lam : spectrum ℂ a,
      ContinuousOn (fun z => (lam : ℂ) * ψ lam z) (spectrum ℂ a) := fun lam =>
    continuousOn_const.mul (hψcont lam)
  have hsumcont : ContinuousOn (fun z => ∑ lam ∈ S, (lam : ℂ) * ψ lam z) (spectrum ℂ a) :=
    continuousOn_finsetSum _ fun lam _ => hmulcont lam
  have hbcfc : b = cfc (fun z => ∑ lam ∈ S, (lam : ℂ) * ψ lam z) a := by
    have he : (fun z => ∑ lam ∈ S, (lam : ℂ) * ψ lam z)
        = ∑ lam ∈ S, (fun z => (lam : ℂ) * ψ lam z) := by
      ext z; simp [Finset.sum_apply]
    rw [hbdef, he, cfc_sum _ a S fun lam _ => hmulcont lam]
    exact Finset.sum_congr rfl fun lam _ => (cfc_const_mul _ _ _ (hψcont lam)).symm
  have hnorm : ‖a - b‖ ≤ δ := by
    have hab : a - b = cfc (fun z => z - ∑ lam ∈ S, (lam : ℂ) * ψ lam z) a := by
      rw [cfc_sub (fun x : ℂ => x) (fun z => ∑ lam ∈ S, (lam : ℂ) * ψ lam z) a
          continuousOn_id hsumcont, cfc_id' ℂ a, ← hbcfc]
    rw [hab]
    refine norm_cfc_le hδpos.le fun z hz => ?_
    have key : z - ∑ lam ∈ S, (lam : ℂ) * ψ lam z = ∑ lam ∈ S, ψ lam z * (z - (lam : ℂ)) := by
      have h1 : ∑ lam ∈ S, ψ lam z * (z - (lam : ℂ))
          = (∑ lam ∈ S, ψ lam z) * z - ∑ lam ∈ S, (lam : ℂ) * ψ lam z := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun lam _ => by ring
      rw [h1, hψsum z hz, one_mul]
    rw [key]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ lam ∈ S, ‖ψ lam z * (z - (lam : ℂ))‖ ≤ (φ lam z / Φ z) * δ := by
      intro lam _
      rw [norm_mul]
      have h1 : ‖ψ lam z‖ = φ lam z / Φ z := by
        simp only [hψdef, Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg (div_nonneg (hφnn lam z) (hΦpos z hz).le)
      have h2 : ‖z - (lam : ℂ)‖ = dist z (lam : ℂ) := (dist_eq_norm z _).symm
      rw [h1, h2, div_mul_eq_mul_div, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (hφsupp lam z) (hΦpos z hz).le
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, ← Finset.sum_div, div_self (hΦpos z hz).ne', one_mul]
  -- the two halves of the estimate
  have hfb : ‖f b‖ ≤ ‖a‖ * ‖f 1‖ := by
    have hfbe : f b = ∑ lam ∈ S, (lam : ℂ) • f (g lam) := by
      rw [hbdef, map_sum]; exact Finset.sum_congr rfl fun lam _ => map_smul f _ _
    have h := norm_sum_smul_le_of_nonneg S (fun lam => f (g lam))
      (fun lam _ => hf _ (hgnn lam)) (fun lam => (lam : ℂ)) ‖a‖ (norm_nonneg a)
      (fun lam _ => spectrum.norm_le_norm_of_mem lam.2)
    rw [show ∑ lam ∈ S, f (g lam) = f 1 from by rw [← map_sum, hgsum]] at h
    rw [hfbe]; exact h
  have hfab : ‖f a - f b‖ ≤ 2 * ‖f 1‖ * δ := by
    rw [← map_sub]
    exact (weak_russo_dye_2 f hf _).trans
      (by nlinarith [hnorm, norm_nonneg (f 1), norm_nonneg (a - b)])
  have hlast : 2 * ‖f 1‖ * δ ≤ ε := by
    rw [hδ]
    have : C * (ε / C) = ε := by field_simp
    nlinarith [div_nonneg hε.le hCpos.le, norm_nonneg (f 1)]
  calc ‖f a‖ = ‖f b + (f a - f b)‖ := by rw [show f b + (f a - f b) = f a from by abel]
    _ ≤ ‖f b‖ + ‖f a - f b‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖f 1‖ + 2 * ‖f 1‖ * δ := add_le_add hfb hfab
    _ ≤ ‖f 1‖ * ‖a‖ + ε := by rw [mul_comm ‖a‖ ‖f 1‖]; linarith

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
to `‖a‖ < 1` and the conclusion to `a = 0` — and the erratum makes the
thesis's intent ("for some natural number `N`", meaning `N ≥ 1`) explicit. -/
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

/-- **34aVIII** (`russo-dye-cor`, cstar.tex:5850, Corollary): the operator
norm of a positive map `f : 𝒜 → ℬ` between C*-algebras is `‖f‖ = ‖f(1)‖`,
i.e. `‖f(a)‖ ≤ ‖f(1)‖ ‖a‖` for all `a`.

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

end Matrices

end Theses.A.CStar
