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
    BddAbove (Set.range fun i => ‖F i‖) := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := F) (fun x => by
    obtain ⟨C, hC⟩ := h x
    exact ⟨C, fun i => hC (Set.mem_range_self i)⟩)
  exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC i⟩

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
  by
    intro r hr
    -- the standard "basis" `e i = (0, …, 1, …, 0)` of `𝒜^N`
    set e : Fin N → WithCStarModule 𝒜 (Fin N → 𝒜) :=
      fun i => (WithCStarModule.equiv 𝒜 _).symm (Pi.single i 1) with he
    refine ⟨(WithCStarModule.equiv 𝒜 _).symm fun i => star (r (e i)), fun x => ?_⟩
    have hdecomp : ∑ i, (x i) • e i = x := by
      ext j
      have hsum : (∑ i, (x i) • e i) j = ∑ i, ((x i) • e i) j := by
        have h := map_sum (WithCStarModule.linearEquiv ℂ 𝒜 (Fin N → 𝒜))
          (fun i => (x i) • e i) Finset.univ
        calc (∑ i, (x i) • e i) j
            = (WithCStarModule.linearEquiv ℂ 𝒜 (Fin N → 𝒜) (∑ i, (x i) • e i)) j := rfl
          _ = (∑ i, WithCStarModule.linearEquiv ℂ 𝒜 (Fin N → 𝒜) ((x i) • e i)) j := by
              rw [h]
          _ = ∑ i, ((x i) • e i) j := Finset.sum_apply _ _ _
      rw [hsum]
      simp only [he, WithCStarModule.smul_apply, WithCStarModule.equiv_symm_pi_apply,
        Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb])
        (fun h => absurd (Finset.mem_univ j) h)]
      simp
    calc r x = r (∑ i, (x i) • e i) := by rw [hdecomp]
      _ = ∑ i, (x i) * r (e i) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => hr.1 _ _
      _ = inner 𝒜 ((WithCStarModule.equiv 𝒜 _).symm fun i => star (r (e i))) x := by
          rw [WithCStarModule.pi_inner]
          exact Finset.sum_congr rfl fun i _ => by
            simp [WithCStarModule.inner_def]

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
    ∃! z : H, ∀ x : H, Tendsto (fun α => ⟪y α, x⟫) l (𝓝 ⟪z, x⟫) := by
  classical
  have hlim : ∀ x : H, ∃ c : ℂ, Tendsto (fun α => ⟪y α, x⟫) l (𝓝 c) := fun x =>
    CompleteSpace.complete (hcauchy x)
  choose φ hφ using hlim
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun α => ‖innerSL ℂ (y α)‖) :=
    pub _ fun x => by simpa using hbdd x
  have hCle : ∀ α, ‖y α‖ ≤ C := fun α => by
    simpa using hC (Set.mem_range_self α)
  have hbound : ∀ x : H, ‖φ x‖ ≤ C * ‖x‖ := by
    intro x
    refine le_of_tendsto (hφ x).norm (Eventually.of_forall fun α => ?_)
    calc ‖⟪y α, x⟫‖ ≤ ‖y α‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ C * ‖x‖ := by gcongr; exact hCle α
  have hadd : ∀ x x' : H, φ (x + x') = φ x + φ x' := by
    intro x x'
    refine tendsto_nhds_unique (hφ (x + x')) ?_
    simpa [inner_add_right] using (hφ x).add (hφ x')
  have hsmul : ∀ (c : ℂ) (x : H), φ (c • x) = c • φ x := by
    intro c x
    refine tendsto_nhds_unique (hφ (c • x)) ?_
    simpa [inner_smul_right] using (hφ x).const_smul c
  let φL : H →ₗ[ℂ] ℂ := { toFun := φ, map_add' := hadd, map_smul' := hsmul }
  let φC : H →L[ℂ] ℂ := φL.mkContinuous C hbound
  refine ⟨(InnerProductSpace.toDual ℂ H).symm φC, fun x => ?_, ?_⟩
  · have : ⟪(InnerProductSpace.toDual ℂ H).symm φC, x⟫ = φ x :=
      InnerProductSpace.toDual_symm_apply
    rw [this]
    exact hφ x
  · intro z hz
    refine ext_inner_right ℂ fun x => ?_
    rw [InnerProductSpace.toDual_symm_apply]
    exact tendsto_nhds_unique (hz x) (hφ x)

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

/-- The polarization identity in the form used to pass between the thesis's
diagonal description of the weak operator topology and Mathlib's:
`⟪y, S x⟫` is a fixed linear combination of the four diagonal values
`⟪z, S z⟫`, `z ∈ {x ± y, x ± i y}`.  (Auxiliary.) -/
private theorem inner_polarization (S : H →L[ℂ] H) (x y : H) : ⟪y, S x⟫ =
    (⟪x + y, S (x + y)⟫ - ⟪x - y, S (x - y)⟫ +
      Complex.I * ⟪x + Complex.I • y, S (x + Complex.I • y)⟫ -
      Complex.I * ⟪x - Complex.I • y, S (x - Complex.I • y)⟫) / 4 := by
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

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
      ∀ x : H, Tendsto (fun α => ⟪x, T α x⟫) l (𝓝 ⟪x, T₀ x⟫) := by
  have key := fun (S : H →L[ℂ] H) (x y : H) => inner_polarization S x y
  constructor
  · intro h x
    simpa using ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp h x x
  · intro h
    rw [ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto]
    intro x y
    simp only [ContinuousLinearMapWOT.ofCLM_apply]
    rw [key T₀ x y]
    refine Filter.Tendsto.congr (fun α => (key (T α) x y).symm) ?_
    exact ((((h (x + y)).sub (h (x - y))).add
      ((h (x + Complex.I • y)).const_mul Complex.I)).sub
      ((h (x - Complex.I • y)).const_mul Complex.I)).div_const 4

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
        (𝓝 (ContinuousLinearMapWOT.ofCLM T₀)) := by
  classical
  -- the diagonal values converge
  have hd : ∀ x : H, ∃ c : ℂ, Tendsto (fun α => ⟪x, T α x⟫) l (𝓝 c) :=
    fun x => CompleteSpace.complete (hcauchy x)
  choose d hdlim using hd
  -- hence, by polarization, so do all matrix coefficients
  have hfull : ∀ x y : H, Tendsto (fun α => ⟪y, T α x⟫) l
      (𝓝 ((d (x + y) - d (x - y) + Complex.I * d (x + Complex.I • y) -
        Complex.I * d (x - Complex.I • y)) / 4)) := by
    intro x y
    refine Filter.Tendsto.congr (fun α => (inner_polarization (T α) x y).symm) ?_
    exact ((((hdlim (x + y)).sub (hdlim (x - y))).add
      ((hdlim (x + Complex.I • y)).const_mul Complex.I)).sub
      ((hdlim (x - Complex.I • y)).const_mul Complex.I)).div_const 4
  -- and all matrix coefficients are bounded
  have habs : ∀ A B C D : ℂ,
      ‖(A - B + Complex.I * C - Complex.I * D) / 4‖ ≤ (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) / 4 := by
    intro A B C D
    have e1 : ‖A - B + Complex.I * C - Complex.I * D‖ ≤
        ‖A - B + Complex.I * C‖ + ‖Complex.I * D‖ := norm_sub_le _ _
    have e2 : ‖A - B + Complex.I * C‖ ≤ ‖A - B‖ + ‖Complex.I * C‖ := norm_add_le _ _
    have e3 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
    have e4 : ‖Complex.I * C‖ = ‖C‖ := by simp
    have e5 : ‖Complex.I * D‖ = ‖D‖ := by simp
    have e6 : ‖(A - B + Complex.I * C - Complex.I * D) / 4‖
        = ‖A - B + Complex.I * C - Complex.I * D‖ / 4 := by
      rw [norm_div]; norm_num
    rw [e6]
    linarith
  have hbdd2 : ∀ x y : H, BddAbove (Set.range fun α => ‖⟪y, T α x⟫‖) := by
    intro x y
    obtain ⟨b1, hb1⟩ := hbdd (x + y)
    obtain ⟨b2, hb2⟩ := hbdd (x - y)
    obtain ⟨b3, hb3⟩ := hbdd (x + Complex.I • y)
    obtain ⟨b4, hb4⟩ := hbdd (x - Complex.I • y)
    refine ⟨(b1 + b2 + b3 + b4) / 4, ?_⟩
    rintro _ ⟨α, rfl⟩
    dsimp only
    rw [inner_polarization (T α) x y]
    refine (habs _ _ _ _).trans ?_
    have h1 := hb1 (Set.mem_range_self α)
    have h2 := hb2 (Set.mem_range_self α)
    have h3 := hb3 (Set.mem_range_self α)
    have h4 := hb4 (Set.mem_range_self α)
    linarith
  have hconj : ∀ (x y : H) (α : ι), ‖⟪T α x, y⟫‖ = ‖⟪y, T α x⟫‖ := by
    intro x y α
    rw [← inner_conj_symm (T α x) y, RCLike.norm_conj]
  -- the net `(T α x)` converges weakly, for every `x`
  have hxlim : ∀ x : H, ∃! z : H, ∀ y : H, Tendsto (fun α => ⟪T α x, y⟫) l (𝓝 ⟪z, y⟫) := by
    intro x
    refine hilb_weakly_bounded_complete (fun α => T α x) (fun y => ?_) (fun y => ?_)
    · have h0 : Tendsto (fun α => ⟪T α x, y⟫) l
          (𝓝 (star ((d (x + y) - d (x - y) + Complex.I * d (x + Complex.I • y) -
            Complex.I * d (x - Complex.I • y)) / 4))) :=
        Filter.Tendsto.congr (fun α => inner_conj_symm (T α x) y) (hfull x y).star
      exact h0.cauchy_map
    · obtain ⟨b, hb⟩ := hbdd2 x y
      refine ⟨b, ?_⟩
      rintro _ ⟨α, rfl⟩
      dsimp only
      rw [hconj x y α]
      exact hb (Set.mem_range_self α)
  choose S hS _huniq using hxlim
  have hSadd : ∀ x x' : H, S (x + x') = S x + S x' := by
    intro x x'
    refine ext_inner_right ℂ fun y => ?_
    rw [inner_add_left]
    refine tendsto_nhds_unique (hS (x + x') y) ?_
    simpa [inner_add_left] using (hS x y).add (hS x' y)
  have hSsmul : ∀ (c : ℂ) (x : H), S (c • x) = c • S x := by
    intro c x
    refine ext_inner_right ℂ fun y => ?_
    rw [inner_smul_left]
    refine tendsto_nhds_unique (hS (c • x) y) ?_
    simpa [inner_smul_left, mul_comm] using (hS x y).const_mul (starRingEnd ℂ c)
  -- uniform boundedness gives a common bound on `‖T α‖`
  have hptbdd : ∀ x : H, BddAbove (Set.range fun α => ‖T α x‖) := by
    intro x
    have h := pub (fun α => innerSL ℂ (T α x)) (fun y => by
      obtain ⟨b, hb⟩ := hbdd2 x y
      refine ⟨b, ?_⟩
      rintro _ ⟨α, rfl⟩
      simpa [hconj x y α] using hb (Set.mem_range_self α))
    simpa using h
  obtain ⟨C, hCb⟩ := pub T hptbdd
  have hTle : ∀ α, ‖T α‖ ≤ C := fun α => hCb (Set.mem_range_self α)
  have hCnn : 0 ≤ C := by
    obtain ⟨α⟩ := Filter.nonempty_of_neBot l
    exact (norm_nonneg (T α)).trans (hTle α)
  have hSb : ∀ x : H, ‖S x‖ ≤ C * ‖x‖ := by
    intro x
    have hlim : ‖⟪S x, S x⟫‖ ≤ C * ‖x‖ * ‖S x‖ := by
      refine le_of_tendsto (hS x (S x)).norm (Eventually.of_forall fun α => ?_)
      calc ‖⟪T α x, S x⟫‖ ≤ ‖T α x‖ * ‖S x‖ := norm_inner_le_norm _ _
        _ ≤ (C * ‖x‖) * ‖S x‖ := by
            gcongr
            exact ((T α).le_opNorm x).trans (by gcongr; exact hTle α)
    have hnorm : ‖⟪S x, S x⟫‖ = ‖S x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; simp
    rw [hnorm] at hlim
    rcases eq_or_lt_of_le (norm_nonneg (S x)) with h | h
    · rw [← h]
      exact mul_nonneg hCnn (norm_nonneg x)
    · nlinarith
  let SL : H →ₗ[ℂ] H := { toFun := S, map_add' := hSadd, map_smul' := hSsmul }
  refine ⟨SL.mkContinuous C hSb, ?_⟩
  rw [ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto]
  intro x y
  simp only [ContinuousLinearMapWOT.ofCLM_apply]
  have h2 : ⟪y, SL.mkContinuous C hSb x⟫ = ⟪y, S x⟫ := rfl
  rw [h2, ← inner_conj_symm y (S x)]
  exact Filter.Tendsto.congr (fun α => inner_conj_symm y (T α x)) ((hS x y).star)

/-- Symmetry of the real part of the inner product.  (Auxiliary.) -/
private theorem re_inner_comm (x y : H) : (⟪x, y⟫ : ℂ).re = (⟪y, x⟫ : ℂ).re := by
  have h : (⟪x, y⟫ : ℂ) = starRingEnd ℂ ⟪y, x⟫ := (inner_conj_symm x y).symm
  rw [h, Complex.conj_re]

/-- For a self-adjoint operator the diagonal values `⟪x, T x⟫` are real.
(Auxiliary for **37IX**.) -/
private theorem inner_self_ofReal_re {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (x : H) :
    (((⟪x, T x⟫).re : ℝ) : ℂ) = ⟪x, T x⟫ := by
  refine Complex.conj_eq_iff_re.mp ?_
  rw [inner_conj_symm]
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT x x
  simpa using hsym

/-- Monotonicity of the diagonal values. (Auxiliary for **37IX**.) -/
private theorem re_inner_mono {S T : H →L[ℂ] H} (h : S ≤ T) (x : H) :
    (⟪x, S x⟫).re ≤ (⟪x, T x⟫).re := by
  have h0 : (0 : H →L[ℂ] H) ≤ T - S := sub_nonneg.mpr h
  have hp := (ContinuousLinearMap.isPositive_iff_complex (T - S)).mp
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp h0) x
  have h2 : (0 : ℝ) ≤ (⟪(T - S) x, x⟫).re := by simpa using hp.2
  rw [ContinuousLinearMap.sub_apply, inner_sub_left] at h2
  simp only [Complex.sub_re] at h2
  rw [re_inner_comm x (S x), re_inner_comm x (T x)]
  linarith

/-- Conversely, a self-adjoint operator dominating another one on the diagonal
dominates it.  (Auxiliary for **37IX**.) -/
private theorem le_of_re_inner {S T : H →L[ℂ] H} (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (h : ∀ x, (⟪x, S x⟫).re ≤ (⟪x, T x⟫).re) : S ≤ T := by
  have hTS : IsSelfAdjoint (T - S) := hT.sub hS
  rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive,
    ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hre : (((⟪x, (T - S) x⟫).re : ℝ) : ℂ) = ⟪x, (T - S) x⟫ := inner_self_ofReal_re hTS x
  have hcomm : (⟪(T - S) x, x⟫ : ℂ) = ⟪x, (T - S) x⟫ := by
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hTS x x
    simpa using hsym
  have hnn : (0 : ℝ) ≤ (⟪x, (T - S) x⟫).re := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right]
    simp only [Complex.sub_re]
    linarith [h x]
  rw [hcomm]
  exact ⟨by simpa using hre, by simpa using hnn⟩

/-- The diagonal values `⟪x, T x⟫` of a self-adjoint operator are real.
(Auxiliary for **37IX**.) -/
private theorem inner_self_im_eq_zero (S : selfAdjoint (H →L[ℂ] H)) (x : H) :
    (⟪x, (S : H →L[ℂ] H) x⟫).im = 0 := by
  rw [← inner_self_ofReal_re S.2 x]
  simp

/-- For a WOT-convergent net of self-adjoint operators the (real) diagonal
values converge to those of the limit.  (Auxiliary for **37IX**.) -/
private theorem re_diag_tendsto_of_wot {D : Set (selfAdjoint (H →L[ℂ] H))}
    {T' : selfAdjoint (H →L[ℂ] H)}
    (hT' : Tendsto (fun T : D => ContinuousLinearMapWOT.ofCLM ((T.1 : H →L[ℂ] H)))
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM (T' : H →L[ℂ] H)))) (x : H) :
    Tendsto (fun T : D => (⟪x, (T.1 : H →L[ℂ] H) x⟫).re) atTop
      (𝓝 (⟪x, (T' : H →L[ℂ] H) x⟫).re) :=
  (Complex.continuous_re.tendsto _).comp ((swot_tendsto_iff _ _).mp hT' x)

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
        atTop (𝓝 (ContinuousLinearMapWOT.ofCLM (T' : H →L[ℂ] H))) := by
  classical
  obtain ⟨d₀, hd₀⟩ := hne
  have : Nonempty D := ⟨⟨d₀, hd₀⟩⟩
  have : IsDirectedOrder D := directedOn_iff_isDirectedOrder.mp hdir
  have hreal : ∀ (x : H) (S : selfAdjoint (H →L[ℂ] H)),
      (((⟪x, (S : H →L[ℂ] H) x⟫).re : ℝ) : ℂ) = ⟪x, (S : H →L[ℂ] H) x⟫ :=
    fun x S => inner_self_ofReal_re S.2 x
  have hmono : ∀ x : H, Monotone fun T : D => (⟪x, (T.1 : H →L[ℂ] H) x⟫).re :=
    fun x _ _ hST => re_inner_mono hST x
  have hbddR : ∀ x : H, BddAbove (Set.range fun T : D => (⟪x, (T.1 : H →L[ℂ] H) x⟫).re) := by
    intro x
    obtain ⟨c, hc⟩ := hbdd x
    refine ⟨c.re, ?_⟩
    rintro _ ⟨T, rfl⟩
    exact (RCLike.le_iff_re_im.mp (hc ⟨T.1, T.2, rfl⟩)).1
  have htendR : ∀ x : H, Tendsto (fun T : D => (⟪x, (T.1 : H →L[ℂ] H) x⟫).re) atTop
      (𝓝 (⨆ T : D, (⟪x, (T.1 : H →L[ℂ] H) x⟫).re)) :=
    fun x => tendsto_atTop_ciSup (hmono x) (hbddR x)
  have htendC : ∀ x : H, Tendsto (fun T : D => ⟪x, (T.1 : H →L[ℂ] H) x⟫) atTop
      (𝓝 (((⨆ T : D, (⟪x, (T.1 : H →L[ℂ] H) x⟫).re : ℝ) : ℂ))) := fun x =>
    Filter.Tendsto.congr (fun T => hreal x T.1)
      ((Complex.continuous_ofReal.tendsto _).comp (htendR x))
  -- the *cofinal tail* above `d₀`, on which the net is norm-bounded
  obtain ⟨F, hFdef⟩ : ∃ F : D → selfAdjoint (H →L[ℂ] H),
      ∀ T, F T = if (⟨d₀, hd₀⟩ : D) ≤ T then T.1 else d₀ := ⟨_, fun _ => rfl⟩
  have hFpos : ∀ T : D, (⟨d₀, hd₀⟩ : D) ≤ T → F T = T.1 := fun T h => by
    rw [hFdef T]; simp [h]
  have hFneg : ∀ T : D, ¬ ((⟨d₀, hd₀⟩ : D) ≤ T) → F T = d₀ := fun T h => by
    rw [hFdef T]; simp [h]
  have hFev : ∀ᶠ T in (atTop : Filter D), F T = T.1 := by
    filter_upwards [eventually_ge_atTop (⟨d₀, hd₀⟩ : D)] with T hT using hFpos T hT
  have hFtendC : ∀ x : H, Tendsto (fun T : D => ⟪x, (F T : H →L[ℂ] H) x⟫) atTop
      (𝓝 (((⨆ T : D, (⟪x, (T.1 : H →L[ℂ] H) x⟫).re : ℝ) : ℂ))) := by
    intro x
    refine (htendC x).congr' ?_
    filter_upwards [hFev] with T hT
    rw [hT]
  have hFcauchy : ∀ x : H, Cauchy (atTop.map fun T : D => ⟪x, (F T : H →L[ℂ] H) x⟫) :=
    fun x => (hFtendC x).cauchy_map
  have hFnbdd : ∀ x : H, BddAbove (Set.range fun T : D => ‖⟪x, (F T : H →L[ℂ] H) x⟫‖) := by
    intro x
    obtain ⟨c, hc⟩ := hbddR x
    refine ⟨|(⟪x, (d₀ : H →L[ℂ] H) x⟫).re| + |c|, ?_⟩
    rintro _ ⟨T, rfl⟩
    have hnorm : ‖⟪x, (F T : H →L[ℂ] H) x⟫‖ = |(⟪x, (F T : H →L[ℂ] H) x⟫).re| := by
      conv_lhs => rw [← hreal x (F T)]
      exact RCLike.norm_ofReal _
    have hlow : (⟪x, (d₀ : H →L[ℂ] H) x⟫).re ≤ (⟪x, (F T : H →L[ℂ] H) x⟫).re := by
      by_cases h : (⟨d₀, hd₀⟩ : D) ≤ T
      · rw [hFpos T h]; exact re_inner_mono h x
      · rw [hFneg T h]
    have hup : (⟪x, (F T : H →L[ℂ] H) x⟫).re ≤ c := by
      by_cases h : (⟨d₀, hd₀⟩ : D) ≤ T
      · rw [hFpos T h]; exact hc (Set.mem_range_self T)
      · rw [hFneg T h]; exact hc (Set.mem_range_self (⟨d₀, hd₀⟩ : D))
    simp only [hnorm, abs_le]
    have h1 := neg_abs_le (⟪x, (d₀ : H →L[ℂ] H) x⟫).re
    have h2 := le_abs_self c
    have h3 := abs_nonneg c
    have h4 := abs_nonneg (⟪x, (d₀ : H →L[ℂ] H) x⟫).re
    constructor <;> linarith
  obtain ⟨T₀, hT₀⟩ := bh_wot_bounded_complete (fun T : D => (F T : H →L[ℂ] H))
    hFcauchy hFnbdd
  have hdiag : ∀ x : H, Tendsto (fun T : D => ⟪x, (F T : H →L[ℂ] H) x⟫) atTop (𝓝 ⟪x, T₀ x⟫) :=
    (swot_tendsto_iff (fun T : D => (F T : H →L[ℂ] H)) T₀).mp hT₀
  have hT₀val : ∀ x : H,
      (⟪x, T₀ x⟫ : ℂ) = ((⨆ T : D, (⟪x, (T.1 : H →L[ℂ] H) x⟫).re : ℝ) : ℂ) :=
    fun x => tendsto_nhds_unique (hdiag x) (hFtendC x)
  have hsa : IsSelfAdjoint T₀ := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
      LinearMap.isSymmetric_iff_inner_map_self_real]
    intro v
    have h2 : (⟪T₀ v, v⟫ : ℂ) = ((⨆ T : D, (⟪v, (T.1 : H →L[ℂ] H) v⟫).re : ℝ) : ℂ) := by
      rw [← inner_conj_symm (T₀ v) v, hT₀val v, Complex.conj_ofReal]
    simp only [ContinuousLinearMap.coe_coe]
    rw [h2, Complex.conj_ofReal]
  refine ⟨⟨T₀, hsa⟩, ?_⟩
  refine hT₀.congr' ?_
  filter_upwards [hFev] with T hT
  rw [hT]

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
    IsLUB D T' := by
  obtain ⟨d₀, hd₀⟩ := hne
  have : Nonempty D := ⟨⟨d₀, hd₀⟩⟩
  have : IsDirectedOrder D := directedOn_iff_isDirectedOrder.mp hdir
  constructor
  · intro S hS
    rw [← Subtype.coe_le_coe]
    refine le_of_re_inner S.2 T'.2 fun x => ?_
    refine ge_of_tendsto (re_diag_tendsto_of_wot hT' x) ?_
    filter_upwards [eventually_ge_atTop (⟨S, hS⟩ : D)] with T hT
    exact re_inner_mono hT x
  · intro S hS
    rw [← Subtype.coe_le_coe]
    refine le_of_re_inner T'.2 S.2 fun x => ?_
    refine le_of_tendsto (re_diag_tendsto_of_wot hT' x) (Eventually.of_forall fun T => ?_)
    exact re_inner_mono (hS T.2) x

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
      ⟪x, (T' : H →L[ℂ] H) x⟫ := by
  obtain ⟨d₀, hd₀⟩ := hne
  have : Nonempty D := ⟨⟨d₀, hd₀⟩⟩
  have : IsDirectedOrder D := directedOn_iff_isDirectedOrder.mp hdir
  constructor
  · rintro _ ⟨S, hS, rfl⟩
    rw [Complex.le_def]
    refine ⟨?_, by rw [inner_self_im_eq_zero S, inner_self_im_eq_zero T']⟩
    refine ge_of_tendsto (re_diag_tendsto_of_wot hT' x) ?_
    filter_upwards [eventually_ge_atTop (⟨S, hS⟩ : D)] with T hT
    exact re_inner_mono hT x
  · intro c hc
    have hcim : c.im = 0 := by
      have h := Complex.le_def.mp (hc ⟨d₀, hd₀, rfl⟩)
      rw [← h.2, inner_self_im_eq_zero d₀]
    rw [Complex.le_def]
    refine ⟨?_, by rw [inner_self_im_eq_zero T', hcim]⟩
    refine le_of_tendsto (re_diag_tendsto_of_wot hT' x) (Eventually.of_forall fun T => ?_)
    exact (Complex.le_def.mp (hc ⟨T.1, T.2, rfl⟩)).1

/-- **37XI** (cstar.tex:6281, Definition), well-definedness claim: every
nonempty norm-bounded directed subset `D` of the self-adjoint part of B(H)
has a supremum there (this repackages **37IX**: norm-boundedness gives the
pointwise bounds `sup_{T ∈ D} ⟪x, T x⟫ < ∞`). -/
theorem exists_isLUB_of_normBounded_directed (D : Set (selfAdjoint (H →L[ℂ] H)))
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (hbdd : ∃ C : ℝ, ∀ T ∈ D, ‖(T : H →L[ℂ] H)‖ ≤ C) :
    ∃ s : selfAdjoint (H →L[ℂ] H), IsLUB D s := by
  obtain ⟨C, hC⟩ := hbdd
  have hb : ∀ x : H,
      BddAbove ((fun T : selfAdjoint (H →L[ℂ] H) => ⟪x, (T : H →L[ℂ] H) x⟫) '' D) := by
    intro x
    refine ⟨((C * ‖x‖ ^ 2 : ℝ) : ℂ), ?_⟩
    rintro _ ⟨T, hT, rfl⟩
    rw [Complex.le_def]
    refine ⟨?_, by rw [inner_self_im_eq_zero T, Complex.ofReal_im]⟩
    rw [Complex.ofReal_re]
    calc (⟪x, (T : H →L[ℂ] H) x⟫).re ≤ ‖⟪x, (T : H →L[ℂ] H) x⟫‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖(T : H →L[ℂ] H) x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (C * ‖x‖) := by
          gcongr
          exact ((T : H →L[ℂ] H).le_opNorm x).trans (by gcongr; exact hC T hT)
      _ = C * ‖x‖ ^ 2 := by ring
  obtain ⟨T', hT'⟩ := hilb_suprema_1 D hne hdir hb
  exact ⟨T', hilb_suprema_2 D hne hdir hb T' hT'⟩

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
    BHNormal (fun T : H →L[ℂ] H => ⟪x, T x⟫) := by
  intro D s hne hdir hlub
  have hb : ∀ y : H,
      BddAbove ((fun T : selfAdjoint (H →L[ℂ] H) => ⟪y, (T : H →L[ℂ] H) y⟫) '' D) := by
    intro y
    refine ⟨⟪y, (s : H →L[ℂ] H) y⟫, ?_⟩
    rintro _ ⟨T, hT, rfl⟩
    rw [Complex.le_def]
    exact ⟨re_inner_mono (Subtype.coe_le_coe.mpr (hlub.1 hT)) y,
      by rw [inner_self_im_eq_zero T, inner_self_im_eq_zero s]⟩
  obtain ⟨T', hT'⟩ := hilb_suprema_1 D hne hdir hb
  have h3 := hilb_suprema_3 D hne hdir hb T' hT' x
  rwa [(hilb_suprema_2 D hne hdir hb T' hT').unique hlub] at h3

/-- An operator whose diagonal values are all real is self-adjoint.
(Auxiliary for **38III**.) -/
private theorem isSelfAdjoint_of_re_diag {T : H →L[ℂ] H}
    (h : ∀ x : H, (((⟪x, T x⟫).re : ℝ) : ℂ) = ⟪x, T x⟫) : IsSelfAdjoint T := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
    LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  have h2 : (⟪T v, v⟫ : ℂ) = (((⟪v, T v⟫).re : ℝ) : ℂ) := by
    rw [← inner_conj_symm (T v) v, ← h v, Complex.conj_ofReal, Complex.ofReal_re]
  simp only [ContinuousLinearMap.coe_coe]
  rw [h2, Complex.conj_ofReal]

/-- Multiplication by a nonnegative real is monotone for the order on `ℂ`.
(Auxiliary for **38III**.) -/
private theorem ofReal_mul_le_ofReal_mul {r : ℝ} (hr : 0 ≤ r) {z w : ℂ} (h : z ≤ w) :
    (r : ℂ) * z ≤ (r : ℂ) * w := by
  rw [Complex.le_def] at h ⊢
  refine ⟨?_, ?_⟩
  · rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left h.1 hr
  · rw [Complex.im_ofReal_mul, Complex.im_ofReal_mul, h.2]

/-- Bound on the diagonal values of a bounded operator.  (Auxiliary for
**38III**.) -/
private theorem re_inner_le_norm_mul (T : H →L[ℂ] H) (x : H) :
    (⟪x, T x⟫).re ≤ ‖T‖ * ‖x‖ ^ 2 := by
  calc (⟪x, T x⟫).re ≤ ‖⟪x, T x⟫‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) := by gcongr; exact T.le_opNorm _
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

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
    BHNormal (⇑ω) := by
  intro D s hne hdir hlub
  obtain ⟨d₀, hd₀⟩ := hne
  set M : ℝ := ‖(s : H →L[ℂ] H) - (d₀ : H →L[ℂ] H)‖ + 1 with hMdef
  have hM : 0 < M := by positivity
  -- the affine rescaling `a ↦ M⁻¹ (a - d₀)` and its diagonal values
  have hdiag : ∀ (r : ℝ) (a b : H →L[ℂ] H) (x : H),
      ⟪x, (((r : ℝ) : ℂ) • (a - b)) x⟫ = ((r : ℝ) : ℂ) * (⟪x, a x⟫ - ⟪x, b x⟫) := by
    intro r a b x
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, inner_smul_right,
      inner_sub_right]
  have hdiagre : ∀ (r : ℝ) (a b : H →L[ℂ] H) (x : H),
      (⟪x, (((r : ℝ) : ℂ) • (a - b)) x⟫).re = r * ((⟪x, a x⟫).re - (⟪x, b x⟫).re) := by
    intro r a b x
    rw [hdiag, Complex.re_ofReal_mul, Complex.sub_re]
  have hsaSub : ∀ (r : ℝ) (a b : selfAdjoint (H →L[ℂ] H)),
      IsSelfAdjoint (((r : ℝ) : ℂ) • ((a : H →L[ℂ] H) - (b : H →L[ℂ] H))) := by
    intro r a b
    refine isSelfAdjoint_of_re_diag fun x => ?_
    obtain ⟨u, hu⟩ : ∃ u : ℝ, (⟪x, (a : H →L[ℂ] H) x⟫ : ℂ) = (u : ℂ) :=
      ⟨_, (inner_self_ofReal_re a.2 x).symm⟩
    obtain ⟨v, hv⟩ : ∃ v : ℝ, (⟪x, (b : H →L[ℂ] H) x⟫ : ℂ) = (v : ℂ) :=
      ⟨_, (inner_self_ofReal_re b.2 x).symm⟩
    rw [hdiag, hu, hv]
    norm_num
  have hsaAdd : ∀ (r : ℝ) (a b : selfAdjoint (H →L[ℂ] H)),
      IsSelfAdjoint (((r : ℝ) : ℂ) • (a : H →L[ℂ] H) + (b : H →L[ℂ] H)) := by
    intro r a b
    refine isSelfAdjoint_of_re_diag fun x => ?_
    obtain ⟨u, hu⟩ : ∃ u : ℝ, (⟪x, (a : H →L[ℂ] H) x⟫ : ℂ) = (u : ℂ) :=
      ⟨_, (inner_self_ofReal_re a.2 x).symm⟩
    obtain ⟨v, hv⟩ : ∃ v : ℝ, (⟪x, (b : H →L[ℂ] H) x⟫ : ℂ) = (v : ℂ) :=
      ⟨_, (inner_self_ofReal_re b.2 x).symm⟩
    rw [ContinuousLinearMap.add_apply, inner_add_right, ContinuousLinearMap.smul_apply,
      inner_smul_right, hu, hv]
    norm_num
  set g : selfAdjoint (H →L[ℂ] H) → selfAdjoint (H →L[ℂ] H) := fun a =>
    ⟨((M⁻¹ : ℝ) : ℂ) • ((a : H →L[ℂ] H) - (d₀ : H →L[ℂ] H)), hsaSub M⁻¹ a d₀⟩ with hgdef
  have hMinv : (0 : ℝ) < M⁻¹ := by positivity
  -- `g` is an order isomorphism of the self-adjoint part
  have hgmono : ∀ a b : selfAdjoint (H →L[ℂ] H), a ≤ b ↔ g a ≤ g b := by
    intro a b
    constructor
    · intro hab
      rw [← Subtype.coe_le_coe]
      refine le_of_re_inner (hsaSub M⁻¹ a d₀) (hsaSub M⁻¹ b d₀) fun x => ?_
      rw [hdiagre, hdiagre]
      have h1 := re_inner_mono (Subtype.coe_le_coe.mpr hab) x
      nlinarith
    · intro hab
      rw [← Subtype.coe_le_coe]
      refine le_of_re_inner a.2 b.2 fun x => ?_
      have h1 := re_inner_mono (Subtype.coe_le_coe.mpr hab) x
      rw [hdiagre, hdiagre] at h1
      nlinarith
  have hgsurj : ∀ t : selfAdjoint (H →L[ℂ] H), ∃ u, g u = t := by
    intro t
    refine ⟨⟨((M : ℝ) : ℂ) • (t : H →L[ℂ] H) + (d₀ : H →L[ℂ] H), hsaAdd M t d₀⟩, ?_⟩
    apply Subtype.ext
    change ((M⁻¹ : ℝ) : ℂ) • ((((M : ℝ) : ℂ) • (t : H →L[ℂ] H) + (d₀ : H →L[ℂ] H))
      - (d₀ : H →L[ℂ] H)) = (t : H →L[ℂ] H)
    rw [add_sub_cancel_right, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hM.ne',
      Complex.ofReal_one, one_smul]
  -- the cofinal tail above `d₀` has the same supremum
  have hD₀dir : DirectedOn (· ≤ ·) {d ∈ D | d₀ ≤ d} := by
    rintro a ⟨haD, ha0⟩ b ⟨hbD, _⟩
    obtain ⟨c, hcD, hac, hbc⟩ := hdir a haD b hbD
    exact ⟨c, ⟨hcD, ha0.trans hac⟩, hac, hbc⟩
  have hD₀lub : IsLUB {d ∈ D | d₀ ≤ d} s := by
    constructor
    · rintro a ⟨haD, _⟩
      exact hlub.1 haD
    · intro t ht
      refine hlub.2 fun a haD => ?_
      obtain ⟨c, hcD, hac, h0c⟩ := hdir a haD d₀ hd₀
      exact hac.trans (ht ⟨hcD, h0c⟩)
  -- the rescaled tail is a directed set of effects with supremum `g s`
  have hEne : (g '' {d ∈ D | d₀ ≤ d}).Nonempty :=
    ⟨g d₀, Set.mem_image_of_mem g ⟨hd₀, le_refl _⟩⟩
  have hEdir : DirectedOn (· ≤ ·) (g '' {d ∈ D | d₀ ≤ d}) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hD₀dir a ha b hb
    exact ⟨g c, Set.mem_image_of_mem g hc, (hgmono a c).mp hac, (hgmono b c).mp hbc⟩
  have hEeff : ∀ T ∈ g '' {d ∈ D | d₀ ≤ d},
      0 ≤ (T : H →L[ℂ] H) ∧ (T : H →L[ℂ] H) ≤ 1 := by
    rintro _ ⟨a, ⟨haD, ha0⟩, rfl⟩
    have h1 := re_inner_mono (Subtype.coe_le_coe.mpr ha0)
    have h2 := re_inner_mono (Subtype.coe_le_coe.mpr (hlub.1 haD))
    constructor
    · refine le_of_re_inner (star_zero _) (hsaSub M⁻¹ a d₀) fun x => ?_
      rw [hdiagre]
      simp only [ContinuousLinearMap.zero_apply, inner_zero_right, Complex.zero_re]
      nlinarith [h1 x]
    · refine le_of_re_inner (hsaSub M⁻¹ a d₀) (star_one _) fun x => ?_
      rw [hdiagre]
      have h3 : (⟪x, ((s : H →L[ℂ] H) - (d₀ : H →L[ℂ] H)) x⟫).re ≤ (M - 1) * ‖x‖ ^ 2 := by
        simpa [hMdef] using re_inner_le_norm_mul ((s : H →L[ℂ] H) - (d₀ : H →L[ℂ] H)) x
      rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re] at h3
      have h4 : (⟪x, (1 : H →L[ℂ] H) x⟫).re = ‖x‖ ^ 2 := by
        simpa using inner_self_eq_norm_sq (𝕜 := ℂ) x
      have h5 : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
      have h6 : M⁻¹ * M = 1 := inv_mul_cancel₀ hM.ne'
      rw [h4]
      nlinarith [h2 x]
  have hElub : IsLUB (g '' {d ∈ D | d₀ ≤ d}) (g s) := by
    constructor
    · rintro _ ⟨a, ha, rfl⟩
      exact (hgmono a s).mp (hD₀lub.1 ha)
    · intro t ht
      obtain ⟨u, rfl⟩ := hgsurj t
      exact (hgmono s u).mp
        (hD₀lub.2 fun a ha => (hgmono a u).mpr (ht (Set.mem_image_of_mem g ha)))
  have hkey := h (g '' {d ∈ D | d₀ ≤ d}) (g s) hEne hEdir hEeff hElub
  -- transport back along `ω (g a) = M⁻¹ (ω a - ω d₀)`
  have hωg : ∀ a : selfAdjoint (H →L[ℂ] H),
      ω ((g a : H →L[ℂ] H)) =
        ((M⁻¹ : ℝ) : ℂ) * (ω (a : H →L[ℂ] H) - ω (d₀ : H →L[ℂ] H)) := by
    intro a
    change ω (((M⁻¹ : ℝ) : ℂ) • ((a : H →L[ℂ] H) - (d₀ : H →L[ℂ] H))) = _
    rw [map_smul, map_sub, smul_eq_mul]
  constructor
  · rintro _ ⟨a, haD, rfl⟩
    exact OrderHomClass.mono ω (Subtype.coe_le_coe.mpr (hlub.1 haD))
  · intro c hc
    have hub : ((M⁻¹ : ℝ) : ℂ) * (c - ω (d₀ : H →L[ℂ] H)) ∈
        upperBounds ((fun d : selfAdjoint (H →L[ℂ] H) => ω (d : H →L[ℂ] H)) ''
          (g '' {d ∈ D | d₀ ≤ d})) := by
      rintro _ ⟨_, ⟨a, ⟨haD, _⟩, rfl⟩, rfl⟩
      change ω ((g a : H →L[ℂ] H)) ≤ _
      rw [hωg a]
      exact ofReal_mul_le_ofReal_mul hMinv.le
        (sub_le_sub_right (hc (Set.mem_image_of_mem _ haD)) _)
    have h7 := hkey.2 hub
    rw [hωg s] at h7
    have h8 := ofReal_mul_le_ofReal_mul (le_of_lt hM) h7
    have h9 : ∀ z : ℂ, ((M : ℝ) : ℂ) * (((M⁻¹ : ℝ) : ℂ) * z) = z := by
      intro z
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hM.ne', Complex.ofReal_one,
        one_mul]
    rw [h9, h9] at h8
    exact (sub_le_sub_iff_right _).mp h8

/-- **38IV** (`bh-functional-lemma`, cstar.tex:6321, Lemma), part 1
(convergence): for a sequence `x₁, x₂, …` in a Hilbert space `H` with
`∑ₙ ‖xₙ‖² < ∞` and any `T ∈ B(H)`, the sum `∑ₙ ⟪xₙ, T xₙ⟫` converges. -/
theorem bh_functional_lemma_1 (x : ℕ → H) (hx : Summable fun n => ‖x n‖ ^ 2)
    (T : H →L[ℂ] H) :
    Summable fun n => ⟪x n, T (x n)⟫ := by
  refine Summable.of_norm_bounded (hx.mul_left ‖T‖) fun n => ?_
  calc ‖⟪x n, T (x n)⟫‖ ≤ ‖x n‖ * ‖T (x n)‖ := norm_inner_le_norm _ _
    _ ≤ ‖x n‖ * (‖T‖ * ‖x n‖) := by gcongr; exact T.le_opNorm _
    _ = ‖T‖ * ‖x n‖ ^ 2 := by ring

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
      ∃ φ : (H →L[ℂ] H) →L[ℂ] ℂ, HasSum (fun α => vectorFunctionalCLM (x α)) φ := by
  classical
  have hnorm : ∀ α, ‖vectorFunctionalCLM (x α)‖ ≤ ‖x α‖ ^ 2 := by
    intro α
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun T => ?_
    calc ‖vectorFunctionalCLM (x α) T‖ = ‖⟪x α, T (x α)⟫‖ := rfl
      _ ≤ ‖x α‖ * ‖T (x α)‖ := norm_inner_le_norm _ _
      _ ≤ ‖x α‖ * (‖T‖ * ‖x α‖) := by gcongr; exact T.le_opNorm _
      _ = ‖x α‖ ^ 2 * ‖T‖ := by ring
  have hone : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    simpa [ContinuousLinearMap.one_def] using
      (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ H‖ ≤ 1)
  have hsum1 : ∀ G : Finset ι,
      ((∑ α ∈ G, vectorFunctionalCLM (x α)) 1 : ℂ) = ((∑ α ∈ G, ‖x α‖ ^ 2 : ℝ) : ℂ) := by
    intro G
    rw [ContinuousLinearMap.sum_apply]
    push_cast
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [vectorFunctionalCLM_apply, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
    simp
  have hle : ∀ G : Finset ι,
      (∑ α ∈ G, ‖x α‖ ^ 2 : ℝ) ≤ ‖∑ α ∈ G, vectorFunctionalCLM (x α)‖ := by
    intro G
    have h1 : ‖((∑ α ∈ G, vectorFunctionalCLM (x α)) 1 : ℂ)‖ ≤
        ‖∑ α ∈ G, vectorFunctionalCLM (x α)‖ * ‖(1 : H →L[ℂ] H)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    rw [hsum1 G, Complex.norm_real, Real.norm_eq_abs] at h1
    have h2 : (0 : ℝ) ≤ ∑ α ∈ G, ‖x α‖ ^ 2 := Finset.sum_nonneg fun α _ => by positivity
    have h3 : (0 : ℝ) ≤ ‖∑ α ∈ G, vectorFunctionalCLM (x α)‖ := norm_nonneg _
    rw [abs_of_nonneg h2] at h1
    nlinarith
  constructor
  · intro hs
    exact ⟨_, (Summable.of_norm_bounded hs hnorm).hasSum⟩
  · rintro ⟨φ, hφ⟩
    obtain ⟨F₀, hF₀⟩ := Filter.eventually_atTop.mp
      (hφ.eventually (Metric.ball_mem_nhds φ one_pos))
    refine summable_of_sum_le (c := ‖φ‖ + 1) (fun α => by positivity) fun F => ?_
    calc (∑ α ∈ F, ‖x α‖ ^ 2) ≤ ∑ α ∈ F ∪ F₀, ‖x α‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
            fun α _ _ => by positivity
      _ ≤ ‖∑ α ∈ F ∪ F₀, vectorFunctionalCLM (x α)‖ := hle _
      _ ≤ ‖φ‖ + 1 := by
          have hb := hF₀ (F ∪ F₀) Finset.subset_union_right
          have hd : ‖(∑ α ∈ F ∪ F₀, vectorFunctionalCLM (x α)) - φ‖ < 1 := by
            simpa [dist_eq_norm] using hb
          have := norm_sub_norm_le (∑ α ∈ F ∪ F₀, vectorFunctionalCLM (x α)) φ
          linarith

/-- **38VI** (`vector-functional-convergence`, cstar.tex:6461, Exercise),
part 2: for a net `(x_α)_α` in a Hilbert space `H` and `x ∈ H`, if `x_α → x`
then `⟪x_α, (·) x_α⟫` operator-norm converges to `⟪x, (·) x⟫`.

(The converse was stated in an earlier version of the thesis and is false: the
constant net `x_α = i • x` with `x ≠ 0` induces the same vector functional as
`x`.  Erratum `parsec-380.60` drops it, together with its hint; the direction
below is the only one used later on.) -/
theorem vector_functional_convergence_2 {ι : Type*} {l : Filter ι} [l.NeBot]
    (x : ι → H) (x₀ : H) (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun α => vectorFunctionalCLM (x α)) l (𝓝 (vectorFunctionalCLM x₀)) := by
  -- The thesis publishes no solution for parsec 380, so this argument is ours.
  -- The estimate is the polarisation-free one: split the difference of the two
  -- vector functionals as `⟪y-x, T y⟫ + ⟪x, T (y-x)⟫`, so that it is bounded by
  -- `‖y - x‖ (‖y‖ + ‖x‖)` uniformly in `‖T‖ ≤ 1`.
  have key : ∀ y : H, ‖vectorFunctionalCLM y - vectorFunctionalCLM x₀‖
      ≤ ‖y - x₀‖ * (‖y‖ + ‖x₀‖) := by
    intro y
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun T => ?_
    have hsplit : (vectorFunctionalCLM y - vectorFunctionalCLM x₀) T
        = ⟪y - x₀, T y⟫ + ⟪x₀, T (y - x₀)⟫ := by
      simp only [ContinuousLinearMap.sub_apply, vectorFunctionalCLM_apply,
        inner_sub_left, map_sub, inner_sub_right]
      ring
    rw [hsplit]
    have b1 : ‖⟪y - x₀, T y⟫‖ ≤ ‖y - x₀‖ * (‖T‖ * ‖y‖) :=
      (norm_inner_le_norm _ _).trans <|
        mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg _)
    have b2 : ‖⟪x₀, T (y - x₀)⟫‖ ≤ ‖x₀‖ * (‖T‖ * ‖y - x₀‖) :=
      (norm_inner_le_norm _ _).trans <|
        mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    calc ‖⟪y - x₀, T y⟫ + ⟪x₀, T (y - x₀)⟫‖
        ≤ ‖⟪y - x₀, T y⟫‖ + ‖⟪x₀, T (y - x₀)⟫‖ := norm_add_le _ _
      _ ≤ ‖y - x₀‖ * (‖T‖ * ‖y‖) + ‖x₀‖ * (‖T‖ * ‖y - x₀‖) := add_le_add b1 b2
      _ = ‖y - x₀‖ * (‖y‖ + ‖x₀‖) * ‖T‖ := by ring
  -- `‖x_α - x₀‖ → 0` while `‖x_α‖ + ‖x₀‖ → 2‖x₀‖`, so the bound tends to `0`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun α => norm_nonneg _) (fun α => key (x α)) ?_
  have h1 : Tendsto (fun α => ‖x α - x₀‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hx
  have h2 : Tendsto (fun α => ‖x α‖ + ‖x₀‖) l (𝓝 (‖x₀‖ + ‖x₀‖)) :=
    (hx.norm).add tendsto_const_nhds
  simpa using h1.mul h2

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
  ⟨hE.inner_products_summable x, hE.tsum_inner_products_le x⟩

/-- **39IV** (`orthonormal`, cstar.tex:6427, Proposition), part 2: for an
orthonormal subset `E` and `x ∈ H`, the sum `∑_{e ∈ E} ⟪e, x⟫ e` converges in
`H`. -/
theorem orthonormal_2 (E : Set H) (hE : Orthonormal ℂ ((↑) : E → H)) (x : H) :
    ∃ y : H, HasSum (fun e : E => ⟪(e : H), x⟫ • (e : H)) y := by
  have hmem : Memℓp (fun e : E => (⟪(e : H), x⟫ : ℂ)) 2 :=
    memℓp_gen (by simpa using hE.inner_products_summable x)
  have hs := hE.orthogonalFamily.summable_of_lp ⟨_, hmem⟩
  simp only [LinearIsometry.toSpanSingleton_apply] at hs
  exact ⟨_, hs.hasSum⟩

/-- **39IV** (`orthonormal`, cstar.tex:6427, Proposition), part 3: if `E` is a
maximal orthonormal subset (an orthonormal basis), then
`∑_{e ∈ E} ⟪e, x⟫ e = x` for every `x ∈ H`. -/
theorem orthonormal_3 (E : Set H) (hE : IsOrthonormalBasis E) (x : H) :
    HasSum (fun e : E => ⟪(e : H), x⟫ • (e : H)) x := by
  have hsp : (Submodule.span ℂ (Set.range ((↑) : E → H)))ᗮ = ⊥ := by
    have h := (maximal_orthonormal_iff_orthogonalComplement_eq_bot hE.1).mp
      (fun u hu hu' => hE.2 u hu hu')
    simpa [Subtype.range_coe] using h
  have hb := (HilbertBasis.mkOfOrthogonalEqBot hE.1 hsp).hasSum_repr x
  simpa [HilbertBasis.repr_apply_apply, HilbertBasis.coe_mkOfOrthogonalEqBot] using hb

/-- **39IV** (`orthonormal`, cstar.tex:6427, Proposition), part 4 (Parseval's
identity): if `E` is an orthonormal basis, then
`∑_{e ∈ E} |⟪e, x⟫|² = ‖x‖²` for every `x ∈ H`. -/
theorem orthonormal_4 (E : Set H) (hE : IsOrthonormalBasis E) (x : H) :
    HasSum (fun e : E => ‖⟪(e : H), x⟫‖ ^ 2) (‖x‖ ^ 2) := by
  have h := (orthonormal_3 E hE x).mapL (innerSL ℂ x)
  simp only [innerSL_apply_apply] at h
  have key : ∀ e : E, ⟪x, ⟪(e : H), x⟫ • (e : H)⟫ = ((‖⟪(e : H), x⟫‖ ^ 2 : ℝ) : ℂ) := by
    intro e
    rw [inner_smul_right, ← inner_conj_symm x (e : H), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  have hx : ⟪x, x⟫ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hx] at h
  simp only [key] at h
  exact_mod_cast h

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
      (ContinuousLinearMapWOT.ofCLM (1 : H →L[ℂ] H)) := by
  have key : ∀ (s : Finset E) (z : H),
      (∑ e ∈ s, ContinuousLinearMapWOT.ofCLM (ketbra (e : H) (e : H))) z
        = ∑ e ∈ s, ⟪(e : H), z⟫ • (e : H) := by
    classical
    intro s z
    induction s using Finset.induction with
    | empty => simp
    | insert e s he ih =>
        rw [Finset.sum_insert he, Finset.sum_insert he, ContinuousLinearMapWOT.add_apply, ih]
        simp [ketbra]
  rw [HasSum, ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto]
  intro x y
  have h := (orthonormal_3 E hE x).mapL (innerSL ℂ y)
  simpa [key, inner_sum, ContinuousLinearMapWOT.ofCLM_apply, HasSum] using h

/-- **39VI** (`sum-ketbras`, cstar.tex:6500, Exercise), part 2:
`∑_{e ∈ E} |e⟩⟨e| = 1` also in the sense that the directed set of partial sums
`∑_{e ∈ F} |e⟩⟨e|` over finite `F ⊆ E` has `1` as its supremum in B(H). -/
theorem sum_ketbras_2 (E : Set H) (hE : IsOrthonormalBasis E) :
    IsLUB {S : H →L[ℂ] H | ∃ F : Finset E, S = ∑ e ∈ F, ketbra (e : H) (e : H)}
      1 := by
  classical
  have hket : ∀ (F : Finset E) (x : H),
      (∑ e ∈ F, ketbra (e : H) (e : H)) x = ∑ e ∈ F, ⟪(e : H), x⟫ • (e : H) := by
    intro F x
    induction F using Finset.induction with
    | empty => simp
    | insert e s he ih =>
        rw [Finset.sum_insert he, Finset.sum_insert he, ContinuousLinearMap.add_apply, ih]
        simp [ketbra]
  have hinner : ∀ (F : Finset E) (x : H),
      ⟪x, (∑ e ∈ F, ketbra (e : H) (e : H)) x⟫
        = ((∑ e ∈ F, ‖⟪(e : H), x⟫‖ ^ 2 : ℝ) : ℂ) := by
    intro F x
    rw [hket F x, inner_sum]
    push_cast
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [inner_smul_right, ← inner_conj_symm x (e : H), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    norm_cast
  have hsa : ∀ F : Finset E, IsSelfAdjoint (∑ e ∈ F, ketbra (e : H) (e : H)) := by
    intro F
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    simp only [ContinuousLinearMap.coe_coe, hket]
    rw [sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [inner_smul_left, inner_smul_right, ← inner_conj_symm x (e : H)]
    ring
  have hone : ∀ x : H, (⟪x, (1 : H →L[ℂ] H) x⟫).re = ‖x‖ ^ 2 := by
    intro x
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) x
  constructor
  · rintro S ⟨F, rfl⟩
    refine le_of_re_inner (hsa F) (star_one _) fun x => ?_
    rw [hinner F x, hone x, Complex.ofReal_re]
    exact hE.1.sum_inner_products_le x
  · intro T hT
    have h0 : (0 : H →L[ℂ] H) ≤ T := by
      have h := hT (⟨(∅ : Finset E), by simp⟩ :
        (0 : H →L[ℂ] H) ∈ {S : H →L[ℂ] H | ∃ F : Finset E, S = ∑ e ∈ F, ketbra (e : H) (e : H)})
      exact h
    have hTsa : IsSelfAdjoint T :=
      ((ContinuousLinearMap.nonneg_iff_isPositive T).mp h0).isSelfAdjoint
    refine le_of_re_inner (star_one _) hTsa fun x => ?_
    rw [hone x]
    refine hasSum_le_of_sum_le (orthonormal_4 E hE x) fun F => ?_
    have hle := re_inner_mono (hT (⟨F, rfl⟩ :
      (∑ e ∈ F, ketbra (e : H) (e : H)) ∈
        {S : H →L[ℂ] H | ∃ F : Finset E, S = ∑ e ∈ F, ketbra (e : H) (e : H)})) x
    rw [hinner F x, Complex.ofReal_re] at hle
    exact hle

/-- The action of a finite sum of `|e⟩⟨e|`.  (Auxiliary for **39VI**.) -/
private theorem ketbra_sum_apply {E : Set H} (F : Finset E) (x : H) :
    (∑ e ∈ F, ketbra (e : H) (e : H)) x = ∑ e ∈ F, ⟪(e : H), x⟫ • (e : H) := by
  classical
  induction F using Finset.induction with
  | empty => simp
  | insert e s he ih =>
      rw [Finset.sum_insert he, Finset.sum_insert he, ContinuousLinearMap.add_apply, ih]
      simp [ketbra]

/-- The diagonal values of a finite sum of `|e⟩⟨e|`.  (Auxiliary for **39VI**.) -/
private theorem ketbra_sum_inner {E : Set H} (F : Finset E) (x : H) :
    ⟪x, (∑ e ∈ F, ketbra (e : H) (e : H)) x⟫ = ((∑ e ∈ F, ‖⟪(e : H), x⟫‖ ^ 2 : ℝ) : ℂ) := by
  rw [ketbra_sum_apply F x, inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [inner_smul_right, ← inner_conj_symm x (e : H), Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  norm_cast

/-- A finite sum of `|e⟩⟨e|` is self-adjoint.  (Auxiliary for **39VI**.) -/
private theorem ketbra_sum_isSelfAdjoint {E : Set H} (F : Finset E) :
    IsSelfAdjoint (∑ e ∈ F, ketbra (e : H) (e : H)) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe, ketbra_sum_apply]
  rw [sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [inner_smul_left, inner_smul_right, ← inner_conj_symm x (e : H)]
  ring

/-- The finite sums of `|e⟩⟨e|` increase with the index set.  (Auxiliary for
**39VI**.) -/
private theorem ketbra_sum_mono {E : Set H} {F G : Finset E} (h : F ⊆ G) :
    (∑ e ∈ F, ketbra (e : H) (e : H)) ≤ ∑ e ∈ G, ketbra (e : H) (e : H) :=
  le_of_re_inner (ketbra_sum_isSelfAdjoint F) (ketbra_sum_isSelfAdjoint G) fun x => by
    rw [ketbra_sum_inner, ketbra_sum_inner, Complex.ofReal_re, Complex.ofReal_re]
    exact Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => by positivity

/-- **39VI** (`sum-ketbras`, cstar.tex:6500, Exercise), part 3: consequently
`ω 1 = ∑_{e ∈ E} ω (|e⟩⟨e|)` for every np-map `ω : B(H) → ℂ`. -/
theorem sum_ketbras_3 (E : Set H) (hE : IsOrthonormalBasis E)
    (ω : NPFunctional (H →L[ℂ] H)) :
    HasSum (fun e : E => ω (ketbra (e : H) (e : H))) (ω 1) := by
  classical
  have hmapsum : ∀ F : Finset E,
      ω (∑ e ∈ F, ketbra (e : H) (e : H)) = ∑ e ∈ F, ω (ketbra (e : H) (e : H)) :=
    fun F => map_sum ω.toPositiveLinearMap _ F
  have hωnn : ∀ T : H →L[ℂ] H, 0 ≤ T → 0 ≤ ω T :=
    fun _ hT => ω.toPositiveLinearMap.map_nonneg hT
  have hone : IsSelfAdjoint (1 : H →L[ℂ] H) := star_one _
  have hketnn : ∀ e : E, (0 : H →L[ℂ] H) ≤ ketbra (e : H) (e : H) := by
    intro e
    simpa using ketbra_sum_mono (F := (∅ : Finset E)) (G := {e}) (by simp)
  -- the directed set of finite partial sums, in the self-adjoint part of B(H)
  set f : Finset E → selfAdjoint (H →L[ℂ] H) := fun F =>
    ⟨∑ e ∈ F, ketbra (e : H) (e : H), ketbra_sum_isSelfAdjoint F⟩ with hf
  have hne : (Set.range f).Nonempty := ⟨f ∅, Set.mem_range_self _⟩
  have hdir : DirectedOn (· ≤ ·) (Set.range f) := by
    rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
    exact ⟨f (F ∪ G), Set.mem_range_self _,
      Subtype.coe_le_coe.mp (ketbra_sum_mono Finset.subset_union_left),
      Subtype.coe_le_coe.mp (ketbra_sum_mono Finset.subset_union_right)⟩
  have hlub : IsLUB (Set.range f) (⟨1, hone⟩ : selfAdjoint (H →L[ℂ] H)) := by
    constructor
    · rintro _ ⟨F, rfl⟩
      exact Subtype.coe_le_coe.mp ((sum_ketbras_2 E hE).1 ⟨F, rfl⟩)
    · intro t ht
      refine Subtype.coe_le_coe.mp ((sum_ketbras_2 E hE).2 ?_)
      rintro S ⟨F, rfl⟩
      exact Subtype.coe_le_coe.mpr (ht (Set.mem_range_self F))
  have hnormal := ω.preservesDirSups' (Set.range f) ⟨1, hone⟩ hne hdir hlub
  -- the summands are nonnegative reals
  have hre : ∀ e : E, ((((ω (ketbra (e : H) (e : H))).re : ℝ)) : ℂ)
      = ω (ketbra (e : H) (e : H)) := by
    intro e
    have h := Complex.le_def.mp (hωnn _ (hketnn e))
    exact Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr h.2.symm)
  have hnn : ∀ e : E, 0 ≤ (ω (ketbra (e : H) (e : H))).re :=
    fun e => (Complex.le_def.mp (hωnn _ (hketnn e))).1
  have hre1 : ((((ω (1 : H →L[ℂ] H)).re : ℝ)) : ℂ) = ω 1 := by
    have h := Complex.le_def.mp (hωnn 1 zero_le_one)
    exact Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr h.2.symm)
  -- the partial sums of the real parts have `(ω 1).re` as least upper bound
  have hsumre : ∀ F : Finset E,
      ((∑ e ∈ F, (ω (ketbra (e : H) (e : H))).re : ℝ) : ℂ)
        = ω (∑ e ∈ F, ketbra (e : H) (e : H)) := by
    intro F
    rw [hmapsum F]
    push_cast
    exact Finset.sum_congr rfl fun e _ => hre e
  have hlubR : IsLUB (Set.range fun F : Finset E => ∑ e ∈ F, (ω (ketbra (e : H) (e : H))).re)
      ((ω (1 : H →L[ℂ] H)).re) := by
    constructor
    · rintro _ ⟨F, rfl⟩
      rw [← Complex.real_le_real, hsumre F, hre1]
      exact hnormal.1 ⟨f F, Set.mem_range_self F, rfl⟩
    · intro c hc
      rw [← Complex.real_le_real, hre1]
      refine hnormal.2 ?_
      rintro _ ⟨_, ⟨F, rfl⟩, rfl⟩
      change ω (∑ e ∈ F, ketbra (e : H) (e : H)) ≤ (c : ℂ)
      rw [← hsumre F, Complex.real_le_real]
      exact hc (Set.mem_range_self F)
  have hR := hasSum_of_isLUB_of_nonneg _ hnn hlubR
  have h2 : HasSum (fun e : E => (((ω (ketbra (e : H) (e : H))).re : ℝ) : ℂ))
      ((((ω (1 : H →L[ℂ] H)).re : ℝ)) : ℂ) := Complex.hasSum_ofReal.mpr hR
  simpa only [hre, hre1] using h2

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
