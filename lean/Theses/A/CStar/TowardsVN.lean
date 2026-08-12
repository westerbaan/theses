/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 1: C*-algebras — cstar.tex, lines 5873–6652.

  §Towards von Neumann Algebras
    Directed Suprema    (parsec 350: uniform boundedness, Hellinger–Toeplitz;
                         parsec 360: self-dual Hilbert 𝒜-modules, bounded forms;
                         parsec 370: the weak operator topology, suprema of
                         bounded directed sets of self-adjoint operators)
    Normal Functionals  (parsec 380: normal functionals on B(H);
                         parsec 390: orthonormal bases, and the theorem that
                         every normal positive functional on B(H) is a sum of
                         vector functionals)
    parsec 400: closing remarks (nothing to formalize).

Statements only; every proof is `sorry`.  See CONVENTIONS.md for the
numbering (**35II** = parsec 350, point 20) and naming conventions.
-/
import Theses.Common

open scoped ComplexOrder ComplexInnerProductSpace lp
open Filter Topology

namespace Theses.A.CStar

/-! ## Parsec 350: Directed suprema — uniform boundedness and Hellinger–Toeplitz

**35I** (cstar.tex:5875): introduction — B(H) has suprema of norm-bounded
directed sets of self-adjoint operators, the vector functionals preserve them,
and every functional preserving them is a sum of vector functionals (39IX
below).  Nothing to formalize. -/

section UniformBoundedness

variable {𝒳 𝒴 : Type*} [NormedAddCommGroup 𝒳] [NormedSpace ℂ 𝒳]
  [NormedAddCommGroup 𝒴] [NormedSpace ℂ 𝒴]

/-- **35II** (`pub`, cstar.tex:5903, Theorem (Uniform Boundedness)): a family
`F` of bounded linear maps from a complete normed vector space `𝒳` to a normed
vector space `𝒴` is bounded, `sup_T ‖T‖ < ∞`, provided that `sup_T ‖T x‖ < ∞`
for every `x ∈ 𝒳`.  Mathlib: `banach_steinhaus`. -/
theorem pub [CompleteSpace 𝒳] {ι : Type*} (F : ι → 𝒳 →L[ℂ] 𝒴)
    (h : ∀ x : 𝒳, BddAbove (Set.range fun i => ‖F i x‖)) :
    BddAbove (Set.range fun i => ‖F i‖) :=
  sorry

end UniformBoundedness

section HilbertModules

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
variable {X Y : Type*}
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒜 X] [CStarModule 𝒜 X]
  [NormedAddCommGroup Y] [Module ℂ Y] [SMul 𝒜 Y] [CStarModule 𝒜 Y]

/-- **35VI** (`hellinger-toeplitz`, cstar.tex:5958, Theorem): an adjointable
map `T : X → Y` between pre-Hilbert 𝒜-modules (here: `CStarModule`s over a
C*-algebra `𝒜`) is bounded — together with its adjoint — as soon as either `X`
or `Y` is complete (by symmetry we state the case that the domain `X` is
complete).  The special case `𝒜 = ℂ`, `X = Y` a Hilbert space is the classical
Hellinger–Toeplitz theorem (**35VIII**); Mathlib:
`LinearMap.IsSymmetric.continuous`. -/
theorem hellinger_toeplitz [CompleteSpace X] (T : X →ₗ[ℂ] Y) (S : Y →ₗ[ℂ] X)
    (adj : ∀ (x : X) (y : Y), inner 𝒜 (T x) y = inner 𝒜 x (S y)) :
    Continuous (⇑T) ∧ Continuous (⇑S) :=
  sorry

/-! **35VIII** (cstar.tex:5989, Remark): the Hellinger–Toeplitz theorem —
every symmetric operator on a Hilbert space is bounded — is the special case
of **35VI** noted in its doc comment; not converted separately.

**35IX** (`hellinger-toeplitz-needs-complete`, cstar.tex:5997, Example):
completeness may not be dropped in **35VI**: on the incomplete inner product
space `c₀₀` of finitely supported sequences, `T α = (n αₙ)ₙ` is symmetric but
unbounded.  Skipped: stating the counterexample requires either constructing
`c₀₀` or an unwieldy existential over types with instances; neither yields a
crisp claim. -/

/-! ## Parsec 360: Self-dual Hilbert modules and bounded forms -/

variable (𝒜) in
/-- Auxiliary notion for **36I**/**36IV**/**36V** (the thesis introduces
(bounded) module maps between Hilbert 𝒜-modules in its section on Hilbert
C*-modules): a ℂ-linear map `T : X → Y` between pre-Hilbert 𝒜-modules is a
*bounded module map* when it is 𝒜-linear (`T (a • x) = a • T x`) and bounded
(equivalently, continuous). -/
def IsBoundedModuleMap (T : X →ₗ[ℂ] Y) : Prop :=
  (∀ (a : 𝒜) (x : X), T (a • x) = a • T x) ∧ Continuous (⇑T)

variable (𝒜 X) in
/-- **36I** (`self-dual`, cstar.tex:6011, Definition): a Hilbert 𝒜-module `X`
is *self-dual* when every bounded module map `r : X → 𝒜` is of the form
`⟪y, ·⟫` for some `y ∈ X`.  (**36II**: by Riesz' representation theorem —
Mathlib's `InnerProductSpace.toDual` — every Hilbert space is self-dual.) -/
def SelfDual : Prop :=
  ∀ r : X →ₗ[ℂ] 𝒜, IsBoundedModuleMap 𝒜 r → ∃ y : X, ∀ x : X, r x = inner 𝒜 y x

/-- **36III** (cstar.tex:6022, Exercise): for a C*-algebra `𝒜` the Hilbert
𝒜-module `𝒜^N` of `N`-tuples (Mathlib: the type synonym
`WithCStarModule 𝒜 (Fin N → 𝒜)`, notation `C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜)`) is
self-dual. -/
theorem selfDual_pi (𝒜 : Type*) [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] (N : ℕ) :
    SelfDual 𝒜 (WithCStarModule 𝒜 (Fin N → 𝒜)) :=
  sorry

variable (𝒜) in
/-- **36IV** (`chilb-form`, cstar.tex:6027, Definition): a *(bounded) form* on
Hilbert 𝒜-modules `X` and `Y` is a map `[·,·] : X × Y → 𝒜` such that
`[x, ·] : Y → 𝒜` and `[·, y]* : X → 𝒜` are (bounded) module maps for all
`x ∈ X` and `y ∈ Y`.  (Since `B` is a bare function, the module-map conditions
are phrased as the existence of linear maps agreeing with it.) -/
structure IsBoundedForm (B : X → Y → 𝒜) : Prop where
  bddModuleMap_right : ∀ x : X,
    ∃ r : Y →ₗ[ℂ] 𝒜, IsBoundedModuleMap 𝒜 r ∧ ∀ y : Y, r y = B x y
  bddModuleMap_left_star : ∀ y : Y,
    ∃ r : X →ₗ[ℂ] 𝒜, IsBoundedModuleMap 𝒜 r ∧ ∀ x : X, r x = star (B x y)

/-- **36V** (`chilb-form-representation`, cstar.tex:6038, Proposition): for
every bounded form `[·,·] : X × Y → 𝒜` on self-dual Hilbert 𝒜-modules `X` and
`Y` there is a unique adjointable bounded module map `T : X → Y` with
`[x, y] = ⟪T x, y⟫` for all `x ∈ X`, `y ∈ Y`. -/
theorem chilb_form_representation (hX : SelfDual 𝒜 X) (hY : SelfDual 𝒜 Y)
    {B : X → Y → 𝒜} (hB : IsBoundedForm 𝒜 B) :
    ∃! T : X →ₗ[ℂ] Y, IsBoundedModuleMap 𝒜 T ∧
      (∃ S : Y →ₗ[ℂ] X, ∀ (x : X) (y : Y), inner 𝒜 (T x) y = inner 𝒜 x (S y)) ∧
      ∀ (x : X) (y : Y), B x y = inner 𝒜 (T x) y :=
  sorry

end HilbertModules

/-! ## Parsec 370: The weak operator topology and directed suprema in B(H)

**37I** (cstar.tex:6066): "another consequence of 35II is this" — nothing to
formalize. -/

section BH

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **37II** (`hilb-weakly-bounded-complete`, cstar.tex:6070, Proposition):
given a net `(y_α)_α` in a Hilbert space `H` for which `⟪y_α, x⟫` is Cauchy
*and bounded* for every `x ∈ H`, there is a unique `y ∈ H` with
`⟪y, x⟫ = lim_α ⟪y_α, x⟫` for all `x ∈ H`.  (**37IV**, Remark, not converted:
boundedness may not be omitted.) -/
theorem hilb_weakly_bounded_complete {ι : Type*} {l : Filter ι} [l.NeBot]
    (y : ι → H)
    (hcauchy : ∀ x : H, Cauchy (l.map fun α => ⟪y α, x⟫))
    (hbdd : ∀ x : H, BddAbove (Set.range fun α => ‖⟪y α, x⟫‖)) :
    ∃! z : H, ∀ x : H, Tendsto (fun α => ⟪y α, x⟫) l (𝓝 ⟪z, x⟫) :=
  sorry

/-! **37V** (`swot`, cstar.tex:6140, Definition):

1. the *weak operator topology (WOT)* on B(H) is the least topology making
   `T ↦ ⟪x, T x⟫ : B(H) → ℂ` continuous for every `x ∈ H`.  In Mathlib the
   type copy `H →WOT[ℂ] H` (`ContinuousLinearMapWOT`) carries the weak
   operator topology (defined there via all maps `T ↦ y (T x)` with `y` in the
   dual — equivalent to the thesis's diagonal definition by polarization); the
   inclusion is `ContinuousLinearMapWOT.ofCLM`, and net convergence is
   characterized by
   `ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto`.

2. the *strong operator topology (SOT)* on B(H) is the least topology making
   `T ↦ ‖T x‖` continuous for every `x ∈ H` (net convergence: `‖T_α x - T x‖ →
   0` pointwise); it is only mentioned for comparison (**37VI**, Remark) and
   not used in the thesis, so we do not formalize it. -/

/-- **37V** (`swot`, cstar.tex:6140, Definition), part 1, embedded claim: a
net `(T_α)_α` converges to `T` in B(H) with respect to the weak operator
topology (Mathlib: `H →WOT[ℂ] H`) if and only if `⟪x, T_α x⟫ → ⟪x, T x⟫` for
every `x ∈ H` (the thesis's diagonal condition; equivalent to Mathlib's
`ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto` by
polarization). -/
theorem swot_tendsto_iff {ι : Type*} {l : Filter ι} (T : ι → H →L[ℂ] H)
    (T₀ : H →L[ℂ] H) :
    Tendsto (fun α => ContinuousLinearMapWOT.ofCLM (T α)) l
        (𝓝 (ContinuousLinearMapWOT.ofCLM T₀)) ↔
      ∀ x : H, Tendsto (fun α => ⟪x, T α x⟫) l (𝓝 ⟪x, T₀ x⟫) :=
  sorry

/-- **37VII** (`bh-wot-bounded-complete`, cstar.tex:6180, Lemma): if
`(T_α)_α` is a net of bounded operators on a Hilbert space `H` such that
`⟪x, T_α x⟫` is Cauchy and bounded for every `x ∈ H`, then `(T_α)_α`
WOT-converges to some bounded operator `T ∈ B(H)`. -/
theorem bh_wot_bounded_complete {ι : Type*} {l : Filter ι} [l.NeBot]
    (T : ι → H →L[ℂ] H)
    (hcauchy : ∀ x : H, Cauchy (l.map fun α => ⟪x, T α x⟫))
    (hbdd : ∀ x : H, BddAbove (Set.range fun α => ‖⟪x, T α x⟫‖)) :
    ∃ T₀ : H →L[ℂ] H,
      Tendsto (fun α => ContinuousLinearMapWOT.ofCLM (T α)) l
        (𝓝 (ContinuousLinearMapWOT.ofCLM T₀)) :=
  sorry

/-- **37IX** (`hilb-suprema`, cstar.tex:6223, Proposition), part 1: an upwards
directed set `D` of self-adjoint operators on a Hilbert space `H` with
`sup_{T ∈ D} ⟪x, T x⟫ < ∞` for all `x ∈ H` — viewed as the net `(T)_{T ∈ D}`
indexed by itself — converges in the weak operator topology to some
self-adjoint `T' ∈ B(H)`. -/
theorem hilb_suprema_1 (D : Set (selfAdjoint (H →L[ℂ] H)))
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (hbdd : ∀ x : H,
      BddAbove ((fun T : selfAdjoint (H →L[ℂ] H) => ⟪x, (T : H →L[ℂ] H) x⟫) '' D)) :
    ∃ T' : selfAdjoint (H →L[ℂ] H),
      Tendsto (fun T : D => ContinuousLinearMapWOT.ofCLM ((T.1 : H →L[ℂ] H)))
        atTop (𝓝 (ContinuousLinearMapWOT.ofCLM (T' : H →L[ℂ] H))) :=
  sorry

/-- **37IX** (`hilb-suprema`, cstar.tex:6223, Proposition), part 2: the WOT
limit `T'` of such a directed set `D` (cf. `hilb_suprema_1`) is the supremum
of `D` among the self-adjoint operators. -/
theorem hilb_suprema_2 (D : Set (selfAdjoint (H →L[ℂ] H)))
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (hbdd : ∀ x : H,
      BddAbove ((fun T : selfAdjoint (H →L[ℂ] H) => ⟪x, (T : H →L[ℂ] H) x⟫) '' D))
    (T' : selfAdjoint (H →L[ℂ] H))
    (hT' : Tendsto (fun T : D => ContinuousLinearMapWOT.ofCLM ((T.1 : H →L[ℂ] H)))
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM (T' : H →L[ℂ] H)))) :
    IsLUB D T' :=
  sorry

/-- **37IX** (`hilb-suprema`, cstar.tex:6223, Proposition), part 3: for the
WOT limit `T'` of such a directed set `D` one has
`⟪x, T' x⟫ = sup_{T ∈ D} ⟪x, T x⟫` for all `x ∈ H` (stated as an `IsLUB` in ℂ
with the order from `ComplexOrder`). -/
theorem hilb_suprema_3 (D : Set (selfAdjoint (H →L[ℂ] H)))
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (hbdd : ∀ x : H,
      BddAbove ((fun T : selfAdjoint (H →L[ℂ] H) => ⟪x, (T : H →L[ℂ] H) x⟫) '' D))
    (T' : selfAdjoint (H →L[ℂ] H))
    (hT' : Tendsto (fun T : D => ContinuousLinearMapWOT.ofCLM ((T.1 : H →L[ℂ] H)))
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM (T' : H →L[ℂ] H))))
    (x : H) :
    IsLUB ((fun T : selfAdjoint (H →L[ℂ] H) => ⟪x, (T : H →L[ℂ] H) x⟫) '' D)
      ⟪x, (T' : H →L[ℂ] H) x⟫ :=
  sorry

/-- **37XI** (cstar.tex:6281, Definition), well-definedness claim: every
nonempty norm-bounded directed subset `D` of the self-adjoint part of B(H)
has a supremum there (this repackages **37IX**: norm-boundedness gives the
pointwise bounds `sup_{T ∈ D} ⟪x, T x⟫ < ∞`). -/
theorem exists_isLUB_of_normBounded_directed (D : Set (selfAdjoint (H →L[ℂ] H)))
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (hbdd : ∃ C : ℝ, ∀ T ∈ D, ‖(T : H →L[ℂ] H)‖ ≤ C) :
    ∃ s : selfAdjoint (H →L[ℂ] H), IsLUB D s :=
  sorry

/-- **37XI** (cstar.tex:6281, Definition): the supremum `⋁ D` of a nonempty
norm-bounded directed subset `D` of the self-adjoint part of B(H), which
exists by **37IX** (`exists_isLUB_of_normBounded_directed`). -/
noncomputable def bhSup (D : Set (selfAdjoint (H →L[ℂ] H)))
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧
      ∃ C : ℝ, ∀ T ∈ D, ‖(T : H →L[ℂ] H)‖ ≤ C) :
    selfAdjoint (H →L[ℂ] H) :=
  (exists_isLUB_of_normBounded_directed D h.1 h.2.1 h.2.2).choose

/-- **37XI** (cstar.tex:6281, Definition): `⋁ D` is the least upper bound of
`D`. -/
theorem isLUB_bhSup (D : Set (selfAdjoint (H →L[ℂ] H)))
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧
      ∃ C : ℝ, ∀ T ∈ D, ‖(T : H →L[ℂ] H)‖ ≤ C) :
    IsLUB D (bhSup D h) :=
  (exists_isLUB_of_normBounded_directed D h.1 h.2.1 h.2.2).choose_spec

/-! ## Parsec 380: Normal functionals on B(H) -/

/-- **38I** (`bh-normal`, cstar.tex:6292, Definition): a positive functional
`ω : B(H) → ℂ` is *normal* when `ω (⋁ D) = ⋁_{T ∈ D} ω T` for every bounded
directed subset `D` of the self-adjoint part of B(H).  This is precisely
`Theses.PreservesDirSups` from `Theses.Common` (specialized to `A = B(H)`,
where every nonempty bounded directed set of self-adjoint elements actually
has a supremum, by **37IX**); the *normal positive functionals* on B(H) are
`Theses.NPFunctional (H →L[ℂ] H)`.

**38Ia** (`bh-normal-abbreviation`, cstar.tex:6300, Notation): "n" abbreviates
"normal": np-map, npu-map, … — cf. `Theses.NPFunctional`; not converted
separately. -/
abbrev BHNormal (ω : (H →L[ℂ] H) → ℂ) : Prop :=
  PreservesDirSups ω

/-- **38II** (cstar.tex:6307, Example): all vector functionals `⟪x, (·) x⟫` on
B(H) are normal, by **37IX**. -/
theorem vector_functional_normal (x : H) :
    BHNormal (fun T : H →L[ℂ] H => ⟪x, T x⟫) :=
  sorry

/-- **38III** (`bh-normal-effects`, cstar.tex:6312, Exercise): a positive
functional `ω : B(H) → ℂ` is normal provided it preserves suprema of directed
sets of *effects* (self-adjoint `T` with `0 ≤ T ≤ 1`). -/
theorem bh_normal_effects (ω : (H →L[ℂ] H) →ₚ[ℂ] ℂ)
    (h : ∀ (D : Set (selfAdjoint (H →L[ℂ] H))) (s : selfAdjoint (H →L[ℂ] H)),
      D.Nonempty → DirectedOn (· ≤ ·) D →
      (∀ T ∈ D, 0 ≤ (T : H →L[ℂ] H) ∧ (T : H →L[ℂ] H) ≤ 1) →
      IsLUB D s →
      IsLUB ((fun d : selfAdjoint (H →L[ℂ] H) => ω (d : H →L[ℂ] H)) '' D)
        (ω (s : H →L[ℂ] H))) :
    BHNormal (⇑ω) :=
  sorry

/-- **38IV** (`bh-functional-lemma`, cstar.tex:6321, Lemma), part 1
(convergence): for a sequence `x₁, x₂, …` in a Hilbert space `H` with
`∑ₙ ‖xₙ‖² < ∞` and any `T ∈ B(H)`, the sum `∑ₙ ⟪xₙ, T xₙ⟫` converges. -/
theorem bh_functional_lemma_1 (x : ℕ → H) (hx : Summable fun n => ‖x n‖ ^ 2)
    (T : H →L[ℂ] H) :
    Summable fun n => ⟪x n, T (x n)⟫ :=
  sorry

/-- **38IV** (`bh-functional-lemma`, cstar.tex:6321, Lemma), part 2: every
sequence `x₁, x₂, …` in a Hilbert space `H` with `∑ₙ ‖xₙ‖² < ∞` gives an
np-map (normal positive functional) `ω : B(H) → ℂ` defined by
`ω T = ∑ₙ ⟪xₙ, T xₙ⟫`. -/
theorem bh_functional_lemma_2 (x : ℕ → H) (hx : Summable fun n => ‖x n‖ ^ 2) :
    ∃ ω : NPFunctional (H →L[ℂ] H),
      ∀ T : H →L[ℂ] H, ω T = ∑' n, ⟪x n, T (x n)⟫ :=
  sorry

/-- The vector functional `⟪x, (·) x⟫ : B(H) → ℂ` bundled as a continuous
linear functional (auxiliary for **38VI**). -/
noncomputable def vectorFunctionalCLM (x : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H x)

omit [CompleteSpace H] in
@[simp]
theorem vectorFunctionalCLM_apply (x : H) (T : H →L[ℂ] H) :
    vectorFunctionalCLM x T = ⟪x, T x⟫ :=
  rfl

/-- **38VI** (`vector-functional-convergence`, cstar.tex:6366, Exercise),
part 1: for a family `(x_α)_α` in a Hilbert space `H`, `∑_α ‖x_α‖² < ∞` if and
only if `∑_α ⟪x_α, (·) x_α⟫` converges with respect to the operator norm to
some bounded functional on B(H). -/
theorem vector_functional_convergence_1 {ι : Type*} (x : ι → H) :
    (Summable fun α => ‖x α‖ ^ 2) ↔
      ∃ φ : (H →L[ℂ] H) →L[ℂ] ℂ, HasSum (fun α => vectorFunctionalCLM (x α)) φ :=
  sorry

/-- **38VI** (`vector-functional-convergence`, cstar.tex:6366, Exercise),
part 2: for a net `(x_α)_α` in a Hilbert space `H` and `x ∈ H`, `x_α → x` if
and only if `⟪x_α, (·) x_α⟫` operator-norm converges to `⟪x, (·) x⟫`.

(Note: the "if" direction as literally stated in the thesis fails for phases —
the constant net `x_α = i • x` with `x ≠ 0` induces the same vector functional
as `x` — so, as stated, this direction presumably intends convergence up to
phase; we nonetheless record the thesis's claim verbatim.) -/
theorem vector_functional_convergence_2 {ι : Type*} {l : Filter ι} [l.NeBot]
    (x : ι → H) (x₀ : H) :
    Tendsto x l (𝓝 x₀) ↔
      Tendsto (fun α => vectorFunctionalCLM (x α)) l (𝓝 (vectorFunctionalCLM x₀)) :=
  sorry

/-! ## Parsec 390: Orthonormal bases and the normality theorem for B(H)

**39I** (cstar.tex:6392): introduction to the final project — every normal
positive functional on B(H) is `∑ₙ ⟪xₙ, (·) xₙ⟫`; nothing to formalize. -/

/-- **39II** (cstar.tex:6403, Definition): a subset `E` of a Hilbert space is
*orthonormal* if `⟪e, e'⟫ = 0` for distinct `e, e' ∈ E` and `⟪e, e⟫ = 1` for
`e ∈ E` (Mathlib: `Orthonormal ℂ ((↑) : E → H)`); a *maximal* orthonormal
subset is called an *orthonormal basis* (cf. Mathlib's `HilbertBasis`, and
`exists_hilbertBasis`; **39III**, Remark: every Hilbert space has one, by
Zorn's lemma — not converted separately). -/
def IsOrthonormalBasis (E : Set H) : Prop :=
  Orthonormal ℂ ((↑) : E → H) ∧
    ∀ E' : Set H, E ⊆ E' → Orthonormal ℂ ((↑) : E' → H) → E' = E

/-- **39IV** (`orthonormal`, cstar.tex:6427, Proposition), part 1 (Bessel's
inequality): for an orthonormal subset `E` of a Hilbert space `H` and `x ∈ H`,
`∑_{e ∈ E} |⟪e, x⟫|² ≤ ‖x‖²` (the sum in particular converges).  Mathlib:
`Orthonormal.tsum_inner_products_le`. -/
theorem orthonormal_1 (E : Set H) (hE : Orthonormal ℂ ((↑) : E → H)) (x : H) :
    (Summable fun e : E => ‖⟪(e : H), x⟫‖ ^ 2) ∧
      ∑' e : E, ‖⟪(e : H), x⟫‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  sorry

/-- **39IV** (`orthonormal`, cstar.tex:6427, Proposition), part 2: for an
orthonormal subset `E` and `x ∈ H`, the sum `∑_{e ∈ E} ⟪e, x⟫ e` converges in
`H`. -/
theorem orthonormal_2 (E : Set H) (hE : Orthonormal ℂ ((↑) : E → H)) (x : H) :
    ∃ y : H, HasSum (fun e : E => ⟪(e : H), x⟫ • (e : H)) y :=
  sorry

/-- **39IV** (`orthonormal`, cstar.tex:6427, Proposition), part 3: if `E` is a
maximal orthonormal subset (an orthonormal basis), then
`∑_{e ∈ E} ⟪e, x⟫ e = x` for every `x ∈ H`. -/
theorem orthonormal_3 (E : Set H) (hE : IsOrthonormalBasis E) (x : H) :
    HasSum (fun e : E => ⟪(e : H), x⟫ • (e : H)) x :=
  sorry

/-- **39IV** (`orthonormal`, cstar.tex:6427, Proposition), part 4 (Parseval's
identity): if `E` is an orthonormal basis, then
`∑_{e ∈ E} |⟪e, x⟫|² = ‖x‖²` for every `x ∈ H`. -/
theorem orthonormal_4 (E : Set H) (hE : IsOrthonormalBasis E) (x : H) :
    HasSum (fun e : E => ‖⟪(e : H), x⟫‖ ^ 2) (‖x‖ ^ 2) :=
  sorry

/-- The rank-one operator `|x⟩⟨y| : z ↦ ⟪y, z⟫ • x` (**4XIX**, `ketbra`,
cstar.tex:671; re-declared privately from `Theses.A.CStar.Basic`, which this
file does not import). -/
private noncomputable def ketbra (x y : H) : H →L[ℂ] H :=
  (innerSL ℂ y).smulRight x

/-- **39VI** (`sum-ketbras`, cstar.tex:6500, Exercise), part 1: for an
orthonormal basis `E` of a Hilbert space `H`, `∑_{e ∈ E} |e⟩⟨e|` converges to
`1` in the weak operator topology. -/
theorem sum_ketbras_1 (E : Set H) (hE : IsOrthonormalBasis E) :
    HasSum (fun e : E => ContinuousLinearMapWOT.ofCLM (ketbra (e : H) (e : H)))
      (ContinuousLinearMapWOT.ofCLM (1 : H →L[ℂ] H)) :=
  sorry

/-- **39VI** (`sum-ketbras`, cstar.tex:6500, Exercise), part 2:
`∑_{e ∈ E} |e⟩⟨e| = 1` also in the sense that the directed set of partial sums
`∑_{e ∈ F} |e⟩⟨e|` over finite `F ⊆ E` has `1` as its supremum in B(H). -/
theorem sum_ketbras_2 (E : Set H) (hE : IsOrthonormalBasis E) :
    IsLUB {S : H →L[ℂ] H | ∃ F : Finset E, S = ∑ e ∈ F, ketbra (e : H) (e : H)}
      1 :=
  sorry

/-- **39VI** (`sum-ketbras`, cstar.tex:6500, Exercise), part 3: consequently
`ω 1 = ∑_{e ∈ E} ω (|e⟩⟨e|)` for every np-map `ω : B(H) → ℂ`. -/
theorem sum_ketbras_3 (E : Set H) (hE : IsOrthonormalBasis E)
    (ω : NPFunctional (H →L[ℂ] H)) :
    HasSum (fun e : E => ω (ketbra (e : H) (e : H))) (ω 1) :=
  sorry

/-- **39VII** (`bh-np-lemma`, cstar.tex:6521, Lemma): for a Hilbert space `H`
with orthonormal basis `E`, a normal positive functional `ω : B(H) → ℂ`, and
`A ∈ B(H)`, `ω A = ∑_{e, e' ∈ E} ⟪e, A e'⟫ ω (|e⟩⟨e'|)`. -/
theorem bh_np_lemma (E : Set H) (hE : IsOrthonormalBasis E)
    (ω : NPFunctional (H →L[ℂ] H)) (A : H →L[ℂ] H) :
    HasSum
      (fun p : E × E => ⟪(p.1 : H), A (p.2 : H)⟫ * ω (ketbra (p.1 : H) (p.2 : H)))
      (ω A) :=
  sorry

/-- **39IX** (`bh-np`, cstar.tex:6567, Theorem): every normal positive
functional `ω : B(H) → ℂ` on a Hilbert space `H` is of the form
`ω = ∑ₙ ⟪xₙ, (·) xₙ⟫` for some sequence `x₁, x₂, … ∈ H` with
`∑ₙ ‖xₙ‖² = ‖ω‖` (for a positive functional `‖ω‖ = ω 1`, which is how the
norm condition is stated here). -/
theorem bh_np (ω : NPFunctional (H →L[ℂ] H)) :
    ∃ x : ℕ → H,
      (∀ T : H →L[ℂ] H, HasSum (fun n => ⟪x n, T (x n)⟫) (ω T)) ∧
      HasSum (fun n => ((‖x n‖ ^ 2 : ℝ) : ℂ)) (ω 1) :=
  sorry

end BH

/-! **40I** (cstar.tex:6625): closing remarks of the chapter — nothing to
formalize. -/

end Theses.A.CStar
