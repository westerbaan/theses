/-
The bounded-operator core of the Rieffel–van Daele approach to modular theory.

**This file has no thesis counterpart.**  It is pure machinery, built to support
the Rieffel–van Daele route to the commutation theorem
`(M ⊗̄ N)' = M' ⊗̄ N'` described in `docs/COMMUTATION-THEOREM.md`; nothing in
either thesis corresponds to it, and nothing else in the tree depends on it yet.

Reference: Marc A. Rieffel and Alfons van Daele, *A bounded operator approach to
Tomita–Takesaki theory*, Pacific J. Math. **69** (1977) 187–221 (open access at
msp.org).  In their parametrisation `Δ = (2 − R)R⁻¹`, `a = (R/2)^{1/2}` and
`b = ((2 − R)/2)^{1/2}`, so that `Δ^{1/2} = b a⁻¹` on `ran a`; that operator is
what is built here.

## Main definitions

* `Theses.RvD.IsModularPair a b`: `a b : ℋ →L[ℂ] ℋ` are positive, commuting and
  injective, with `a * a + b * b = 1`.
* `Theses.RvD.opRatio a b ha`: the densely defined operator `b a⁻¹`, with domain
  `ran a` and `a ζ ↦ b ζ`.  Morally `Δ^{1/2}`.

## Main results

* `IsModularPair.isSelfAdjoint`, `.inner_nonneg`, `.injective_apply`, `.dense_range`
  (**Lemma A**): `D = D_{a,b}` is a positive, injective, self-adjoint operator with dense
  range.  The engine is `IsModularPair.unitary_add_smul`: `b ± i a` is unitary because the
  cross terms cancel, so `D ± i` maps `ran a` onto `ℋ`
  (`IsModularPair.exists_apply_add_smul`).
* `IsCommutingPair.isModularPair` (**Lemma B**, the *normalisation lemma*): commuting
  positive injective `c d` with **no** normalisation are turned into a modular pair
  `(c̃, d̃) = (normFst c d, normSnd c d)` with `c̃ h = c`, `d̃ h = d`, where
  `h = sqrtSumSq c d = (c² + d²)^{1/2}`; `IsCommutingPair.D_apply` says
  `D_{c̃,d̃}(cζ) = dζ`.  Because the graph of `D_{c̃,d̃}` is the image of `ℋ` under the
  isometry `η ↦ (c̃ η, d̃ η)` and is closed, `IsCommutingPair.hasCore` shows that `c(E)`
  is a core for every dense subspace `E`.  This exhibits the closure explicitly, so no
  deficiency-index criterion is needed downstream.
* `IsModularPair.resolvent_apply` and `IsModularPair.resolvent_unique` (**Lemma C**):
  `(1 + D²) a² = 1` with `1 + D²` injective, i.e. `(1 + D²)⁻¹ = a²` as an
  everywhere-defined bounded operator.  Hence `IsModularPair.eq_of_sq_eq`: two modular
  pairs with `a₁² = a₂²` coincide, by uniqueness of the *bounded* positive square root.
  This replaces uniqueness of unbounded positive square roots, which is unavailable.
* `IsModularPair.eq_one_of_comp` and `IsModularPair.eq_one_of_eq_compPMap` (**Lemma D**,
  polar rigidity): if `V` is unitary and `D_{a₂,b₂} = V · D_{a₁,b₁}` (domains included)
  then `V = 1`, `a₁ = a₂` and `b₁ = b₂`.

None of this needs a Borel functional calculus, projection-valued measures, or the
spectral theorem for unbounded operators — the point of the Rieffel–van Daele
parametrisation is that `Δ^{1/2}` is `b a⁻¹` for *bounded* `a, b`.
-/
import Mathlib

set_option linter.unusedSectionVars false

open scoped ComplexOrder InnerProductSpace LinearPMap

namespace Theses.RvD

variable {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

/-! ## Preliminaries on bounded operators -/

/-- Two continuous linear maps that agree on a dense set are equal. -/
theorem clm_ext_of_dense {S : Set ℋ} (hS : Dense S) {f g : ℋ →L[ℂ] ℋ}
    (h : Set.EqOn (f : ℋ → ℋ) (g : ℋ → ℋ) S) : f = g :=
  DFunLike.coe_injective (Continuous.ext_on hS f.continuous g.continuous h)

/-- Positivity of a bounded operator can be checked on a dense set.  Over `ℂ` the quadratic
form alone determines positivity, so no separate self-adjointness check is needed. -/
theorem nonneg_of_dense {S : Set ℋ} (hS : Dense S) {f : ℋ →L[ℂ] ℋ}
    (hpos : ∀ x ∈ S, (0 : ℂ) ≤ ⟪f x, x⟫_ℂ) : 0 ≤ f := by
  have hre : Continuous fun y : ℋ => (⟪f y, y⟫_ℂ).re := by fun_prop
  have him : Continuous fun y : ℋ => (⟪f y, y⟫_ℂ).im := by fun_prop
  have hcl : IsClosed {y : ℋ | (0 : ℂ) ≤ ⟪f y, y⟫_ℂ} := by
    have hset : {y : ℋ | (0 : ℂ) ≤ ⟪f y, y⟫_ℂ}
        = {y : ℋ | 0 ≤ (⟪f y, y⟫_ℂ).re} ∩ {y : ℋ | (0 : ℝ) = (⟪f y, y⟫_ℂ).im} := by
      ext y; simp [Complex.le_def]
    rw [hset]
    exact (isClosed_le continuous_const hre).inter (isClosed_eq continuous_const him)
  have hall : ∀ x, (0 : ℂ) ≤ ⟪f x, x⟫_ℂ := by
    intro x
    have hsub := hcl.closure_subset_iff.2 hpos
    rw [hS.closure_eq] at hsub
    exact hsub (Set.mem_univ x)
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hx := hall x
  rw [Complex.le_def] at hx
  refine ⟨?_, by simpa using hx.1⟩
  simp [Complex.ext_iff, ← hx.2]

/-- A positive injective bounded operator has dense range. -/
theorem dense_range_of_nonneg_injective {a : ℋ →L[ℂ] ℋ} (ha : 0 ≤ a)
    (hinj : Function.Injective a) :
    Dense ((LinearMap.range (a : ℋ →ₗ[ℂ] ℋ) : Submodule ℂ ℋ) : Set ℋ) := by
  have hsa : IsSelfAdjoint a := ((ContinuousLinearMap.nonneg_iff_isPositive a).1 ha).isSelfAdjoint
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_orthogonal] at hx
  have h1 : ⟪a (a x), x⟫_ℂ = 0 := hx _ ⟨a x, rfl⟩
  have h2 : ⟪a x, a x⟫_ℂ = 0 := by
    rw [← h1]
    exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa) (a x) x).symm
  exact hinj (by simpa using inner_self_eq_zero.1 h2)

/-- Commuting bounded operators commute pointwise. -/
theorem commute_apply {u v : ℋ →L[ℂ] ℋ} (huv : Commute u v) (ζ : ℋ) : u (v ζ) = v (u ζ) := by
  have h : (u * v) ζ = (v * u) ζ := by rw [huv.eq]
  exact h

/-- The inner-product form of self-adjointness, in the shape used below. -/
theorem inner_of_nonneg {a : ℋ →L[ℂ] ℋ} (ha : 0 ≤ a) (x y : ℋ) : ⟪a x, y⟫_ℂ = ⟪x, a y⟫_ℂ :=
  ((ContinuousLinearMap.nonneg_iff_isPositive a).1 ha).isSymmetric x y

/-! ## Modular pairs -/

/-- `(a, b)` is a **modular pair** on the Hilbert space `ℋ` when `a` and `b` are positive,
commuting and injective bounded operators with `a² + b² = 1`.  In the Rieffel–van Daele
parametrisation `Δ = (2 − R)R⁻¹` one takes `a = (R/2)^{1/2}` and `b = ((2 − R)/2)^{1/2}`. -/
structure IsModularPair (a b : ℋ →L[ℂ] ℋ) : Prop where
  nonneg_fst : 0 ≤ a
  nonneg_snd : 0 ≤ b
  commute : Commute a b
  injective_fst : Function.Injective a
  injective_snd : Function.Injective b
  sq_add_sq : a * a + b * b = 1

/-- The densely defined operator `b a⁻¹`: its domain is `ran a` and it sends `a ζ` to `b ζ`.
Morally `Δ^{1/2}` in the Rieffel–van Daele parametrisation. -/
noncomputable def opRatio (a b : ℋ →L[ℂ] ℋ) (ha : Function.Injective (a : ℋ →ₗ[ℂ] ℋ)) :
    ℋ →ₗ.[ℂ] ℋ where
  domain := LinearMap.range (a : ℋ →ₗ[ℂ] ℋ)
  toFun := (b : ℋ →ₗ[ℂ] ℋ) ∘ₗ (LinearEquiv.ofInjective (a : ℋ →ₗ[ℂ] ℋ) ha).symm.toLinearMap

@[simp]
theorem opRatio_domain (a b : ℋ →L[ℂ] ℋ) (ha : Function.Injective (a : ℋ →ₗ[ℂ] ℋ)) :
    (opRatio a b ha).domain = LinearMap.range (a : ℋ →ₗ[ℂ] ℋ) := rfl

theorem mem_opRatio_domain (a b : ℋ →L[ℂ] ℋ) (ha : Function.Injective (a : ℋ →ₗ[ℂ] ℋ))
    (ζ : ℋ) : a ζ ∈ (opRatio a b ha).domain := ⟨ζ, rfl⟩

@[simp]
theorem opRatio_apply (a b : ℋ →L[ℂ] ℋ) (ha : Function.Injective (a : ℋ →ₗ[ℂ] ℋ)) (ζ : ℋ) :
    opRatio a b ha ⟨a ζ, mem_opRatio_domain a b ha ζ⟩ = b ζ := by
  show b ((LinearEquiv.ofInjective (a : ℋ →ₗ[ℂ] ℋ) ha).symm ⟨a ζ, _⟩) = b ζ
  congr 1
  rw [LinearEquiv.symm_apply_eq]
  exact Subtype.ext rfl

/-- The value of `opRatio a b` at any element of its domain, given a preimage. -/
theorem opRatio_apply' (a b : ℋ →L[ℂ] ℋ) (ha : Function.Injective (a : ℋ →ₗ[ℂ] ℋ))
    (x : (opRatio a b ha).domain) (ζ : ℋ) (hζ : a ζ = (x : ℋ)) :
    opRatio a b ha x = b ζ := by
  have : x = ⟨a ζ, mem_opRatio_domain a b ha ζ⟩ := Subtype.ext hζ.symm
  rw [this, opRatio_apply]

namespace IsModularPair

variable {a b : ℋ →L[ℂ] ℋ}

theorem isSelfAdjoint_fst (h : IsModularPair a b) : IsSelfAdjoint a :=
  ((ContinuousLinearMap.nonneg_iff_isPositive a).1 h.nonneg_fst).isSelfAdjoint

theorem isSelfAdjoint_snd (h : IsModularPair a b) : IsSelfAdjoint b :=
  ((ContinuousLinearMap.nonneg_iff_isPositive b).1 h.nonneg_snd).isSelfAdjoint

/-- The operator `D_{a,b}`, morally `b a⁻¹`, i.e. `Δ^{1/2}`. -/
noncomputable def D (h : IsModularPair a b) : ℋ →ₗ.[ℂ] ℋ := opRatio a b h.injective_fst

theorem D_apply (h : IsModularPair a b) (ζ : ℋ) :
    h.D ⟨a ζ, mem_opRatio_domain a b h.injective_fst ζ⟩ = b ζ :=
  opRatio_apply a b h.injective_fst ζ

theorem D_apply' (h : IsModularPair a b) (x : h.D.domain) (ζ : ℋ) (hζ : a ζ = (x : ℋ)) :
    h.D x = b ζ :=
  opRatio_apply' a b h.injective_fst x ζ hζ

theorem D_domain (h : IsModularPair a b) :
    h.D.domain = LinearMap.range (a : ℋ →ₗ[ℂ] ℋ) := rfl

theorem mem_D_domain (h : IsModularPair a b) (ζ : ℋ) : a ζ ∈ h.D.domain :=
  mem_opRatio_domain a b h.injective_fst ζ

/-- `ran a` is dense, so `D_{a,b}` is densely defined. -/
theorem dense_domain (h : IsModularPair a b) : Dense (h.D.domain : Set ℋ) :=
  dense_range_of_nonneg_injective h.nonneg_fst h.injective_fst

/-! ### `b ± i a` is unitary -/

/-- The key computation of Rieffel–van Daele: `(b + εa)*(b + εa) = b² + a² = 1` when `ε² = -1`
and `ε* = -ε`.  The cross terms cancel precisely because `a` and `b` commute. -/
theorem unitary_add_smul (h : IsModularPair a b) {ε : ℂ} (hε : ε * ε = -1)
    (hεs : star ε = -ε) : (b + ε • a) ∈ unitary (ℋ →L[ℂ] ℋ) := by
  have expand : ∀ μ ν : ℂ, (b + μ • a) * (b + ν • a)
      = (b * b + (μ * ν) • (a * a)) + (ν • (b * a) + μ • (a * b)) := by
    intro μ ν
    simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_add, smul_smul]
    module
  have hstar : star (b + ε • a) = b + (-ε) • a := by
    rw [star_add, star_smul, hεs, h.isSelfAdjoint_snd.star_eq, h.isSelfAdjoint_fst.star_eq]
  have hcross : ∀ μ : ℂ, μ • (b * a) + (-μ) • (a * b) = 0 := by
    intro μ; rw [h.commute.eq]; module
  have hbase : b * b + a * a = 1 := by rw [add_comm]; exact h.sq_add_sq
  have hmul1 : ((-ε) * ε) = 1 := by rw [neg_mul, hε]; ring
  have hmul2 : (ε * (-ε)) = 1 := by rw [mul_neg, hε]; ring
  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩
  · rw [hstar, expand, hmul1, hcross, one_smul, add_zero, hbase]
  · rw [hstar, expand, hmul2, one_smul]
    rw [show (-ε) • (b * a) + ε • (a * b) = 0 by rw [h.commute.eq]; module, add_zero, hbase]

/-- `(D ± i)` maps `ran a` onto all of `ℋ`: this is the surjectivity that upgrades symmetry
to self-adjointness. -/
theorem exists_apply_add_smul (h : IsModularPair a b) {ε : ℂ} (hε : ε * ε = -1)
    (hεs : star ε = -ε) (ξ : ℋ) : ∃ x : h.D.domain, h.D x + ε • (x : ℋ) = ξ := by
  have hu := h.unitary_add_smul hε hεs
  set u : ℋ →L[ℂ] ℋ := b + ε • a with hu_def
  refine ⟨⟨a (star u ξ), h.mem_D_domain _⟩, ?_⟩
  rw [h.D_apply (star u ξ)]
  have : b (star u ξ) + ε • a (star u ξ) = (u * star u) ξ := by
    simp [hu_def]
  rw [this, Unitary.mul_star_self_of_mem hu]
  simp

/-! ### Self-adjointness, positivity, injectivity -/

/-- `D_{a,b}` is symmetric: `⟪bζ, aη⟫ = ⟪abζ, η⟫ = ⟪baζ, η⟫ = ⟪aζ, bη⟫`. -/
theorem isFormalAdjoint (h : IsModularPair a b) : h.D.IsFormalAdjoint h.D := by
  rintro ⟨x, ζ, rfl⟩ ⟨y, η, rfl⟩
  rw [h.D_apply' _ ζ rfl, h.D_apply' _ η rfl]
  show ⟪b ζ, a η⟫_ℂ = ⟪a ζ, b η⟫_ℂ
  rw [← inner_of_nonneg h.nonneg_fst (b ζ) η, ← inner_of_nonneg h.nonneg_snd (a ζ) η]
  have hc : a (b ζ) = b (a ζ) := by
    calc a (b ζ) = (a * b) ζ := rfl
      _ = (b * a) ζ := by rw [h.commute.eq]
      _ = b (a ζ) := rfl
  rw [hc]

/-- **Lemma A.** `D_{a,b}` is self-adjoint.  Symmetry plus surjectivity of `D ± i`:
if `η ∈ dom D*`, pick `η₀ ∈ dom D` with `(D+i)η₀ = (D*+i)η`; then `η - η₀ ∈ ker(D*+i)`,
which is orthogonal to the (full) range of `D - i`, hence zero. -/
theorem isSelfAdjoint (h : IsModularPair a b) : _root_.IsSelfAdjoint h.D := by
  have hdense := h.dense_domain
  have hsym := h.isFormalAdjoint
  have hle : h.D ≤ h.D† := hsym.le_adjoint hdense
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := h.D) hdense
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hIs : star Complex.I = -Complex.I := by simp
  have hnI : (-Complex.I) * (-Complex.I) = -1 := by rw [neg_mul_neg]; exact Complex.I_mul_I
  have hnIs : star (-Complex.I) = -(-Complex.I) := by simp
  have key : ∀ η : (h.D†).domain,
      ∃ y : h.D.domain, (y : ℋ) = (η : ℋ) ∧ h.D† η = h.D y := by
    intro η
    obtain ⟨η₀, hη₀⟩ := h.exists_apply_add_smul hI hIs (h.D† η + Complex.I • (η : ℋ))
    have hη₀' : ((η₀ : ℋ)) ∈ (h.D†).domain := hle.1 η₀.2
    have hDη₀ : h.D† ⟨(η₀ : ℋ), hη₀'⟩ = h.D η₀ := (hle.2 rfl).symm
    have hkey : h.D† η = h.D η₀ + Complex.I • (η₀ : ℋ) - Complex.I • (η : ℋ) := by
      rw [eq_sub_iff_add_eq]; exact hη₀.symm
    set v : ℋ := (η : ℋ) - (η₀ : ℋ) with hv_def
    have hvmem : v ∈ (h.D†).domain := Submodule.sub_mem _ η.2 hη₀'
    have hDv : h.D† ⟨v, hvmem⟩ = (-Complex.I) • v := by
      have hsplit : (⟨v, hvmem⟩ : (h.D†).domain) = η - ⟨(η₀ : ℋ), hη₀'⟩ := Subtype.ext rfl
      rw [hsplit, LinearPMap.map_sub, hDη₀, hkey, hv_def]
      module
    have horth : ∀ y : h.D.domain, ⟪v, h.D y + (-Complex.I) • (y : ℋ)⟫_ℂ = 0 := by
      intro y
      have hy := hfa ⟨v, hvmem⟩ y
      rw [hDv] at hy
      have h1 : ⟪(-Complex.I) • v, (y : ℋ)⟫_ℂ = Complex.I * ⟪v, (y : ℋ)⟫_ℂ := by
        rw [inner_smul_left]; simp
      rw [h1] at hy
      rw [inner_add_right, inner_smul_right, ← hy]
      ring
    obtain ⟨y, hy⟩ := h.exists_apply_add_smul hnI hnIs v
    have hvv : ⟪v, v⟫_ℂ = 0 := by nth_rewrite 2 [← hy]; exact horth y
    have hηη₀ : (η : ℋ) = (η₀ : ℋ) := sub_eq_zero.1 (hv_def ▸ inner_self_eq_zero.1 hvv)
    refine ⟨η₀, hηη₀.symm, ?_⟩
    rw [hkey, hηη₀]
    module
  have hge : (h.D†).domain ≤ h.D.domain ∧
      ∀ ⦃x : (h.D†).domain⦄ ⦃y : h.D.domain⦄, (x : ℋ) = (y : ℋ) → h.D† x = h.D y := by
    constructor
    · intro x hx
      obtain ⟨y, hy1, -⟩ := key ⟨x, hx⟩
      have : (y : ℋ) = x := hy1
      exact this ▸ y.2
    · intro x y hxy
      obtain ⟨z, hz1, hz2⟩ := key x
      rw [hz2]
      exact congrArg _ (Subtype.ext (hz1.trans hxy))
  exact le_antisymm hge hle

/-- `D_{a,b}` is a positive operator: `⟪D aζ, aζ⟫ = ⟪abζ, ζ⟫ ≥ 0`, `ab` being a product of
commuting positives. -/
theorem inner_nonneg (h : IsModularPair a b) (x : h.D.domain) : 0 ≤ ⟪h.D x, (x : ℋ)⟫_ℂ := by
  obtain ⟨x, ζ, rfl⟩ := x
  rw [h.D_apply' _ ζ rfl]
  have hab : (0 : ℋ →L[ℂ] ℋ) ≤ a * b := Commute.mul_nonneg h.nonneg_fst h.nonneg_snd h.commute
  have := ((ContinuousLinearMap.nonneg_iff_isPositive (a * b)).1 hab).inner_nonneg_left ζ
  calc (0:ℂ) ≤ ⟪(a * b) ζ, ζ⟫_ℂ := this
    _ = ⟪b ζ, a ζ⟫_ℂ := (inner_of_nonneg h.nonneg_fst (b ζ) ζ)
    _ = ⟪b ζ, (⟨(a : ℋ →ₗ[ℂ] ℋ) ζ, _⟩ : h.D.domain)⟫_ℂ := rfl

/-- `D_{a,b}` is injective. -/
theorem injective_apply (h : IsModularPair a b) (x : h.D.domain) (hx : h.D x = 0) :
    (x : ℋ) = 0 := by
  obtain ⟨x, ζ, rfl⟩ := x
  rw [h.D_apply' _ ζ rfl] at hx
  have : ζ = 0 := h.injective_snd (by simpa using hx)
  simp [this]

/-- The range of `D_{a,b}` is `ran b`, which is dense. -/
theorem range_eq (h : IsModularPair a b) :
    (Set.range fun x : h.D.domain => h.D x) = Set.range (b : ℋ → ℋ) := by
  ext w
  constructor
  · rintro ⟨⟨x, ζ, rfl⟩, rfl⟩
    exact ⟨ζ, (h.D_apply' _ ζ rfl).symm⟩
  · rintro ⟨ζ, rfl⟩
    exact ⟨⟨a ζ, h.mem_D_domain ζ⟩, h.D_apply ζ⟩

/-- `D_{a,b}` has dense range. -/
theorem dense_range (h : IsModularPair a b) : Dense (Set.range fun x : h.D.domain => h.D x) := by
  rw [h.range_eq]
  exact dense_range_of_nonneg_injective h.nonneg_snd h.injective_snd

/-- `D_{a,b}` is a closed operator. -/
theorem isClosed (h : IsModularPair a b) : h.D.IsClosed := h.isSelfAdjoint.isClosed

/-! ### Lemma C: recovery of `a²` as `(1 + D²)⁻¹` -/

/-- `D(a²η) = b(aη) = a(bη)`, so `a²η` lies in the domain of `D²`. -/
theorem mem_domain_D_sq (h : IsModularPair a b) (η : ℋ) :
    (h.D ⟨a (a η), h.mem_D_domain (a η)⟩ : ℋ) ∈ h.D.domain := by
  rw [h.D_apply' _ (a η) rfl]
  exact ⟨b η, commute_apply h.commute η⟩

/-- **Lemma C.**  `(1 + D²) a² = 1`: the bounded operator `a²` is an everywhere-defined
inverse of `1 + D²`. -/
theorem resolvent_apply (h : IsModularPair a b) (η : ℋ) :
    a (a η) + (h.D ⟨(h.D ⟨a (a η), h.mem_D_domain (a η)⟩ : ℋ), h.mem_domain_D_sq η⟩ : ℋ) = η := by
  have h1 : (h.D ⟨a (a η), h.mem_D_domain (a η)⟩ : ℋ) = a (b η) := by
    rw [h.D_apply' _ (a η) rfl]; exact (commute_apply h.commute η).symm
  have h2 : (h.D ⟨(h.D ⟨a (a η), h.mem_D_domain (a η)⟩ : ℋ), h.mem_domain_D_sq η⟩ : ℋ)
      = b (b η) := h.D_apply' _ (b η) h1.symm
  rw [h2]
  calc a (a η) + b (b η) = (a * a + b * b) η := rfl
    _ = (1 : ℋ →L[ℂ] ℋ) η := by rw [h.sq_add_sq]
    _ = η := rfl

/-- `1 + D²` is injective: `⟪(1+D²)η, η⟫ = ‖η‖² + ‖Dη‖²`. -/
theorem resolvent_unique (h : IsModularPair a b) {x y : h.D.domain}
    {hx : (h.D x : ℋ) ∈ h.D.domain} {hy : (h.D y : ℋ) ∈ h.D.domain}
    (heq : (x : ℋ) + (h.D ⟨(h.D x : ℋ), hx⟩ : ℋ) = (y : ℋ) + (h.D ⟨(h.D y : ℋ), hy⟩ : ℋ)) :
    (x : ℋ) = (y : ℋ) := by
  have hDw : (h.D (x - y) : ℋ) = (h.D x : ℋ) - (h.D y : ℋ) := LinearPMap.map_sub _ _ _
  have hwmem : (h.D (x - y) : ℋ) ∈ h.D.domain := by
    rw [hDw]; exact Submodule.sub_mem _ hx hy
  have hsplit : (⟨(h.D (x - y) : ℋ), hwmem⟩ : h.D.domain)
      = ⟨(h.D x : ℋ), hx⟩ - ⟨(h.D y : ℋ), hy⟩ := Subtype.ext hDw
  have hzero : ((x - y : h.D.domain) : ℋ) + (h.D ⟨(h.D (x - y) : ℋ), hwmem⟩ : ℋ) = 0 := by
    rw [hsplit, LinearPMap.map_sub]
    have hxy : ((x - y : h.D.domain) : ℋ) = (x : ℋ) - (y : ℋ) := rfl
    rw [hxy]
    rw [sub_add_sub_comm, heq, sub_self]
  have hip : ⟪((x - y : h.D.domain) : ℋ), ((x - y : h.D.domain) : ℋ)⟫_ℂ
      + ⟪(h.D (x - y) : ℋ), (h.D (x - y) : ℋ)⟫_ℂ = 0 := by
    have hsym := h.isFormalAdjoint ⟨(h.D (x - y) : ℋ), hwmem⟩ (x - y)
    have : ⟪((x - y : h.D.domain) : ℋ) + (h.D ⟨(h.D (x - y) : ℋ), hwmem⟩ : ℋ),
        ((x - y : h.D.domain) : ℋ)⟫_ℂ = 0 := by rw [hzero]; simp
    rw [inner_add_left] at this
    rw [← this, hsym]
  have hre := congrArg RCLike.re hip
  simp only [map_add, inner_self_eq_norm_sq, map_zero] at hre
  have hw : ((x - y : h.D.domain) : ℋ) = 0 := by
    have h1 : ‖((x - y : h.D.domain) : ℋ)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖((x - y : h.D.domain) : ℋ)‖, sq_nonneg ‖(h.D (x - y) : ℋ)‖]
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1
  have hsub : (x : ℋ) - (y : ℋ) = 0 := hw
  exact sub_eq_zero.1 hsub

/-- **Lemma C, the consequence.**  Two modular pairs with the same `a²` coincide.  This is
uniqueness of the *bounded* positive square root, which replaces uniqueness of unbounded
positive square roots. -/
theorem eq_of_sq_eq {a₁ b₁ a₂ b₂ : ℋ →L[ℂ] ℋ} (h₁ : IsModularPair a₁ b₁)
    (h₂ : IsModularPair a₂ b₂) (hsq : a₁ * a₁ = a₂ * a₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have ha : a₁ = a₂ := by
    have e1 : CFC.sqrt (a₁ * a₁) = a₁ := CFC.sqrt_mul_self a₁ h₁.nonneg_fst
    have e2 : CFC.sqrt (a₂ * a₂) = a₂ := CFC.sqrt_mul_self a₂ h₂.nonneg_fst
    rw [← e1, ← e2, hsq]
  have hb : b₁ * b₁ = b₂ * b₂ := by
    have e1 : b₁ * b₁ = 1 - a₁ * a₁ := by rw [← h₁.sq_add_sq]; abel
    have e2 : b₂ * b₂ = 1 - a₂ * a₂ := by rw [← h₂.sq_add_sq]; abel
    rw [e1, e2, hsq]
  refine ⟨ha, ?_⟩
  have e1 : CFC.sqrt (b₁ * b₁) = b₁ := CFC.sqrt_mul_self b₁ h₁.nonneg_snd
  have e2 : CFC.sqrt (b₂ * b₂) = b₂ := CFC.sqrt_mul_self b₂ h₂.nonneg_snd
  rw [← e1, ← e2, hb]

/-- `η ↦ (aη, bη)` is an isometry: `‖aη‖² + ‖bη‖² = ‖η‖²`. -/
theorem norm_sq_add_norm_sq (h : IsModularPair a b) (ζ : ℋ) :
    ‖a ζ‖ ^ 2 + ‖b ζ‖ ^ 2 = ‖ζ‖ ^ 2 := by
  have hip : ⟪a ζ, a ζ⟫_ℂ + ⟪b ζ, b ζ⟫_ℂ = ⟪ζ, ζ⟫_ℂ := by
    rw [← inner_of_nonneg h.nonneg_fst (a ζ) ζ, ← inner_of_nonneg h.nonneg_snd (b ζ) ζ,
      ← inner_add_left]
    congr 1
    calc a (a ζ) + b (b ζ) = (a * a + b * b) ζ := rfl
      _ = (1 : ℋ →L[ℂ] ℋ) ζ := by rw [h.sq_add_sq]
      _ = ζ := rfl
  have := congrArg RCLike.re hip
  simpa only [map_add, inner_self_eq_norm_sq] using this

/-! ### Lemma D: polar rigidity -/

/-- If `D₂ = V·D₁` with `D₁`, `D₂` self-adjoint, then `V·D₁ = D₁·V*`; in particular `V*`
preserves `dom D₁`.  This is the domain bookkeeping behind `D₁² = D₂²`. -/
theorem star_mem_domain {a₁ b₁ a₂ b₂ : ℋ →L[ℂ] ℋ} (h₁ : IsModularPair a₁ b₁)
    (h₂ : IsModularPair a₂ b₂) {V : ℋ →L[ℂ] ℋ}
    (hdom : h₂.D.domain = h₁.D.domain)
    (hap : ∀ (x : h₂.D.domain) (y : h₁.D.domain),
      (x : ℋ) = (y : ℋ) → (h₂.D x : ℋ) = V (h₁.D y))
    (z : h₁.D.domain) :
    ∃ hz : (star V) (z : ℋ) ∈ h₁.D.domain,
      (h₁.D ⟨(star V) (z : ℋ), hz⟩ : ℋ) = V (h₁.D z) := by
  have hdense := h₁.dense_domain
  have hsa : h₁.D† = h₁.D := h₁.isSelfAdjoint
  have hdomeq : (h₁.D†).domain = h₁.D.domain := by rw [hsa]
  have hz2 : (z : ℋ) ∈ h₂.D.domain := by rw [hdom]; exact z.2
  have hcomp : ∀ x : h₁.D.domain,
      ⟪V (h₁.D z), (x : ℋ)⟫_ℂ = ⟪(star V) (z : ℋ), (h₁.D x : ℋ)⟫_ℂ := by
    intro x
    have hx2 : (x : ℋ) ∈ h₂.D.domain := by rw [hdom]; exact x.2
    have e1 : ⟪(star V) (z : ℋ), (h₁.D x : ℋ)⟫_ℂ = ⟪(z : ℋ), V (h₁.D x)⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ContinuousLinearMap.adjoint_inner_left V (h₁.D x) (z : ℋ)
    have e2 : V (h₁.D x) = (h₂.D ⟨(x : ℋ), hx2⟩ : ℋ) := (hap ⟨(x : ℋ), hx2⟩ x rfl).symm
    have e3 : ⟪(z : ℋ), (h₂.D ⟨(x : ℋ), hx2⟩ : ℋ)⟫_ℂ
        = ⟪(h₂.D ⟨(z : ℋ), hz2⟩ : ℋ), (x : ℋ)⟫_ℂ :=
      (h₂.isFormalAdjoint ⟨(z : ℋ), hz2⟩ ⟨(x : ℋ), hx2⟩).symm
    have e4 : (h₂.D ⟨(z : ℋ), hz2⟩ : ℋ) = V (h₁.D z) := hap _ z rfl
    rw [e1, e2, e3, e4]
  have hmem : (star V) (z : ℋ) ∈ (h₁.D†).domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨V (h₁.D z), hcomp⟩
  have hval : h₁.D† ⟨(star V) (z : ℋ), hmem⟩ = V (h₁.D z) :=
    LinearPMap.adjoint_apply_eq hdense _ hcomp
  have hmem' : (star V) (z : ℋ) ∈ h₁.D.domain := hdomeq.le hmem
  refine ⟨hmem', ?_⟩
  have hle : h₁.D† ≤ h₁.D := le_of_eq hsa
  have htr : h₁.D† ⟨(star V) (z : ℋ), hmem⟩ = h₁.D ⟨(star V) (z : ℋ), hmem'⟩ := hle.2 rfl
  rw [← htr, hval]

/-- **Lemma D (polar rigidity).**  If `V` is unitary, `(a₁,b₁)` and `(a₂,b₂)` are modular
pairs, and `D_{a₂,b₂} = V · D_{a₁,b₁}` — equality of operators, domains included, which is
exactly the pair of hypotheses `hdom` and `hap` — then `V = 1`, `a₁ = a₂` and `b₁ = b₂`. -/
theorem eq_one_of_comp {a₁ b₁ a₂ b₂ : ℋ →L[ℂ] ℋ} (h₁ : IsModularPair a₁ b₁)
    (h₂ : IsModularPair a₂ b₂) {V : ℋ →L[ℂ] ℋ} (hV : V ∈ unitary (ℋ →L[ℂ] ℋ))
    (hdom : h₂.D.domain = h₁.D.domain)
    (hap : ∀ (x : h₂.D.domain) (y : h₁.D.domain),
      (x : ℋ) = (y : ℋ) → (h₂.D x : ℋ) = V (h₁.D y)) :
    V = 1 ∧ a₁ = a₂ ∧ b₁ = b₂ := by
  have hsq : a₁ * a₁ = a₂ * a₂ := by
    refine ContinuousLinearMap.ext fun η => ?_
    -- the resolvent of `D₁` applied to `η`, computed in two ways
    set ζ : ℋ := a₂ (a₂ η) with hζdef
    have hζ2 : ζ ∈ h₂.D.domain := h₂.mem_D_domain (a₂ η)
    have hζ1 : ζ ∈ h₁.D.domain := by rw [← hdom]; exact hζ2
    set ν : ℋ := (h₂.D ⟨ζ, hζ2⟩ : ℋ) with hνdef
    have hν2 : ν ∈ h₂.D.domain := h₂.mem_domain_D_sq η
    have hν1 : ν ∈ h₁.D.domain := by rw [← hdom]; exact hν2
    have hνV : ν = V (h₁.D ⟨ζ, hζ1⟩) := hap ⟨ζ, hζ2⟩ ⟨ζ, hζ1⟩ rfl
    obtain ⟨hz, hzval⟩ := star_mem_domain h₁ h₂ hdom hap ⟨ν, hν1⟩
    have hstarν : (star V) ν = (h₁.D ⟨ζ, hζ1⟩ : ℋ) := by
      rw [hνV]
      calc (star V) (V (h₁.D ⟨ζ, hζ1⟩)) = (star V * V) (h₁.D ⟨ζ, hζ1⟩) := rfl
        _ = (1 : ℋ →L[ℂ] ℋ) (h₁.D ⟨ζ, hζ1⟩) := by rw [Unitary.star_mul_self_of_mem hV]
        _ = (h₁.D ⟨ζ, hζ1⟩ : ℋ) := rfl
    have hy : (h₁.D ⟨ζ, hζ1⟩ : ℋ) ∈ h₁.D.domain := hstarν ▸ hz
    have hstep : (h₁.D ⟨(h₁.D ⟨ζ, hζ1⟩ : ℋ), hy⟩ : ℋ) = (h₂.D ⟨ν, hν2⟩ : ℋ) := by
      have e0 : (⟨(h₁.D ⟨ζ, hζ1⟩ : ℋ), hy⟩ : h₁.D.domain)
          = ⟨(star V) ν, hz⟩ := Subtype.ext hstarν.symm
      rw [e0, hzval]
      exact (hap ⟨ν, hν2⟩ ⟨ν, hν1⟩ rfl).symm
    have hres2 : ζ + (h₁.D ⟨(h₁.D ⟨ζ, hζ1⟩ : ℋ), hy⟩ : ℋ) = η := by
      rw [hstep]; exact h₂.resolvent_apply η
    have hres1 : a₁ (a₁ η)
        + (h₁.D ⟨(h₁.D ⟨a₁ (a₁ η), h₁.mem_D_domain (a₁ η)⟩ : ℋ), h₁.mem_domain_D_sq η⟩ : ℋ)
        = η := h₁.resolvent_apply η
    show a₁ (a₁ η) = ζ
    exact h₁.resolvent_unique (x := ⟨a₁ (a₁ η), h₁.mem_D_domain (a₁ η)⟩) (y := ⟨ζ, hζ1⟩)
      (hx := h₁.mem_domain_D_sq η) (hy := hy) (by rw [hres1, hres2])
  obtain ⟨ha, hb⟩ := eq_of_sq_eq h₁ h₂ hsq
  refine ⟨?_, ha, hb⟩
  have hVone : ∀ ζ : ℋ, V (b₁ ζ) = b₁ ζ := by
    intro ζ
    have hx : a₂ ζ ∈ h₂.D.domain := h₂.mem_D_domain ζ
    have hy : a₁ ζ ∈ h₁.D.domain := h₁.mem_D_domain ζ
    have hcast : ((⟨a₂ ζ, hx⟩ : h₂.D.domain) : ℋ) = ((⟨a₁ ζ, hy⟩ : h₁.D.domain) : ℋ) := by
      show a₂ ζ = a₁ ζ
      rw [ha]
    have heq := hap ⟨a₂ ζ, hx⟩ ⟨a₁ ζ, hy⟩ hcast
    rw [h₂.D_apply' _ ζ rfl, h₁.D_apply' _ ζ rfl] at heq
    rw [← hb] at heq
    exact heq.symm
  refine clm_ext_of_dense (dense_range_of_nonneg_injective h₁.nonneg_snd h₁.injective_snd) ?_
  rintro _ ⟨ζ, rfl⟩
  exact hVone ζ

/-- Lemma D, stated as a literal equality of partially defined operators
`D_{a₂,b₂} = V ∘ D_{a₁,b₁}`. -/
theorem eq_one_of_eq_compPMap {a₁ b₁ a₂ b₂ : ℋ →L[ℂ] ℋ} (h₁ : IsModularPair a₁ b₁)
    (h₂ : IsModularPair a₂ b₂) {V : ℋ →L[ℂ] ℋ} (hV : V ∈ unitary (ℋ →L[ℂ] ℋ))
    (hVD : h₂.D = LinearMap.compPMap (V : ℋ →ₗ[ℂ] ℋ) h₁.D) : V = 1 ∧ a₁ = a₂ ∧ b₁ = b₂ := by
  have hdom : h₂.D.domain = h₁.D.domain := by rw [hVD]; rfl
  have hap : ∀ (x : h₂.D.domain) (y : h₁.D.domain),
      (x : ℋ) = (y : ℋ) → (h₂.D x : ℋ) = V (h₁.D y) := by
    intro x y hxy
    have hle : h₂.D ≤ LinearMap.compPMap (V : ℋ →ₗ[ℂ] ℋ) h₁.D := le_of_eq hVD
    have hx' : (x : ℋ) ∈ (LinearMap.compPMap (V : ℋ →ₗ[ℂ] ℋ) h₁.D).domain := by
      rw [← hVD]; exact x.2
    have h1 := hle.2 (x := x) (y := ⟨(x : ℋ), hx'⟩) rfl
    rw [h1, LinearMap.compPMap_apply]
    have h2 : (⟨(x : ℋ), hx'⟩ : h₁.D.domain) = y := Subtype.ext hxy
    have h3 : (h₁.D ⟨(x : ℋ), hx'⟩ : ℋ) = (h₁.D y : ℋ) := by rw [h2]
    exact congrArg (fun w : ℋ => V w) h3
  exact eq_one_of_comp h₁ h₂ hV hdom hap

end IsModularPair

/-! ## The normalisation lemma

Given commuting positive injective `c d` with **no** normalisation, put
`h := (c² + d²)^{1/2}`.  Since `‖cζ‖² + ‖dζ‖² = ‖hζ‖²`, the assignments `hζ ↦ cζ` and
`hζ ↦ dζ` are contractive on the dense subspace `ran h`, so they extend to bounded operators
`c̃, d̃` forming a modular pair with `c̃ h = c`, `d̃ h = d`.  This exhibits the closure of
`cζ ↦ dζ` explicitly. -/

/-- `c d : ℋ →L[ℂ] ℋ` positive, commuting and injective — with **no** normalisation. -/
structure IsCommutingPair (c d : ℋ →L[ℂ] ℋ) : Prop where
  nonneg_fst : 0 ≤ c
  nonneg_snd : 0 ≤ d
  commute : Commute c d
  injective_fst : Function.Injective c
  injective_snd : Function.Injective d

/-- The normalising operator `h = (c² + d²)^{1/2}`. -/
noncomputable def sqrtSumSq (c d : ℋ →L[ℂ] ℋ) : ℋ →L[ℂ] ℋ := CFC.sqrt (c * c + d * d)

/-- The contraction `c̃` determined by `c̃ h = c`. -/
noncomputable def normFst (c d : ℋ →L[ℂ] ℋ) : ℋ →L[ℂ] ℋ :=
  LinearMap.extendOfNorm (c : ℋ →ₗ[ℂ] ℋ) ((sqrtSumSq c d : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ)

/-- The contraction `d̃` determined by `d̃ h = d`. -/
noncomputable def normSnd (c d : ℋ →L[ℂ] ℋ) : ℋ →L[ℂ] ℋ :=
  LinearMap.extendOfNorm (d : ℋ →ₗ[ℂ] ℋ) ((sqrtSumSq c d : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ)

namespace IsCommutingPair

variable {c d : ℋ →L[ℂ] ℋ}

theorem symm (p : IsCommutingPair c d) : IsCommutingPair d c :=
  ⟨p.nonneg_snd, p.nonneg_fst, p.commute.symm, p.injective_snd, p.injective_fst⟩

theorem isSelfAdjoint_fst (p : IsCommutingPair c d) : IsSelfAdjoint c :=
  ((ContinuousLinearMap.nonneg_iff_isPositive c).1 p.nonneg_fst).isSelfAdjoint

theorem isSelfAdjoint_snd (p : IsCommutingPair c d) : IsSelfAdjoint d :=
  ((ContinuousLinearMap.nonneg_iff_isPositive d).1 p.nonneg_snd).isSelfAdjoint

theorem nonneg_sumSq (p : IsCommutingPair c d) : (0 : ℋ →L[ℂ] ℋ) ≤ c * c + d * d := by
  have h1 : (0 : ℋ →L[ℂ] ℋ) ≤ c * c := by
    nth_rewrite 1 [← p.isSelfAdjoint_fst.star_eq]; exact star_mul_self_nonneg c
  have h2 : (0 : ℋ →L[ℂ] ℋ) ≤ d * d := by
    nth_rewrite 1 [← p.isSelfAdjoint_snd.star_eq]; exact star_mul_self_nonneg d
  exact add_nonneg h1 h2

theorem sqrtSumSq_nonneg (c d : ℋ →L[ℂ] ℋ) : (0 : ℋ →L[ℂ] ℋ) ≤ sqrtSumSq c d :=
  CFC.sqrt_nonneg _

theorem sqrtSumSq_mul_self (p : IsCommutingPair c d) :
    sqrtSumSq c d * sqrtSumSq c d = c * c + d * d :=
  CFC.sqrt_mul_sqrt_self _ p.nonneg_sumSq

theorem commute_sqrtSumSq_fst (p : IsCommutingPair c d) : Commute (sqrtSumSq c d) c :=
  Commute.cfcₙ_nnreal
    (Commute.add_left (Commute.mul_left (Commute.refl c) (Commute.refl c))
      (Commute.mul_left p.commute.symm p.commute.symm)) NNReal.sqrt

theorem commute_sqrtSumSq_snd (p : IsCommutingPair c d) : Commute (sqrtSumSq c d) d :=
  Commute.cfcₙ_nnreal
    (Commute.add_left (Commute.mul_left p.commute p.commute)
      (Commute.mul_left (Commute.refl d) (Commute.refl d))) NNReal.sqrt

/-- `‖cζ‖² + ‖dζ‖² = ‖hζ‖²`: this is why `hζ ↦ cζ` is contractive. -/
theorem norm_sqrtSumSq_sq (p : IsCommutingPair c d) (ζ : ℋ) :
    ‖sqrtSumSq c d ζ‖ ^ 2 = ‖c ζ‖ ^ 2 + ‖d ζ‖ ^ 2 := by
  have hip : ⟪sqrtSumSq c d ζ, sqrtSumSq c d ζ⟫_ℂ = ⟪c ζ, c ζ⟫_ℂ + ⟪d ζ, d ζ⟫_ℂ := by
    rw [← inner_of_nonneg (sqrtSumSq_nonneg c d) (sqrtSumSq c d ζ) ζ,
      ← inner_of_nonneg p.nonneg_fst (c ζ) ζ, ← inner_of_nonneg p.nonneg_snd (d ζ) ζ,
      ← inner_add_left]
    congr 1
    calc sqrtSumSq c d (sqrtSumSq c d ζ) = (sqrtSumSq c d * sqrtSumSq c d) ζ := rfl
      _ = (c * c + d * d) ζ := by rw [p.sqrtSumSq_mul_self]
      _ = c (c ζ) + d (d ζ) := rfl
  have := congrArg RCLike.re hip
  simpa only [map_add, inner_self_eq_norm_sq] using this

theorem norm_fst_le (p : IsCommutingPair c d) (ζ : ℋ) : ‖c ζ‖ ≤ ‖sqrtSumSq c d ζ‖ := by
  have h := p.norm_sqrtSumSq_sq ζ
  nlinarith [norm_nonneg (c ζ), norm_nonneg (d ζ), norm_nonneg (sqrtSumSq c d ζ)]

theorem norm_snd_le (p : IsCommutingPair c d) (ζ : ℋ) : ‖d ζ‖ ≤ ‖sqrtSumSq c d ζ‖ := by
  have h := p.norm_sqrtSumSq_sq ζ
  nlinarith [norm_nonneg (c ζ), norm_nonneg (d ζ), norm_nonneg (sqrtSumSq c d ζ)]

theorem injective_sqrtSumSq (p : IsCommutingPair c d) : Function.Injective (sqrtSumSq c d) := by
  intro x y hxy
  have hζ : sqrtSumSq c d (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h1 : ‖c (x - y)‖ ≤ 0 := by
    have := p.norm_fst_le (x - y); rwa [hζ, norm_zero] at this
  have h2 : c (x - y) = c 0 := by rw [map_zero]; exact norm_le_zero_iff.1 h1
  exact sub_eq_zero.1 (p.injective_fst h2)

theorem denseRange_sqrtSumSq (p : IsCommutingPair c d) : DenseRange (sqrtSumSq c d) :=
  dense_range_of_nonneg_injective (sqrtSumSq_nonneg c d) p.injective_sqrtSumSq

theorem denseRange_sqrtSumSq_sq (p : IsCommutingPair c d) :
    Dense (Set.range ⇑(sqrtSumSq c d * sqrtSumSq c d)) := by
  refine dense_range_of_nonneg_injective ?_ ?_
  · rw [p.sqrtSumSq_mul_self]; exact p.nonneg_sumSq
  · exact p.injective_sqrtSumSq.comp p.injective_sqrtSumSq

/-! ### The two contractions `c̃` and `d̃` -/

theorem normFst_apply (p : IsCommutingPair c d) (ζ : ℋ) :
    normFst c d (sqrtSumSq c d ζ) = c ζ :=
  LinearMap.extendOfNorm_eq (f := (c : ℋ →ₗ[ℂ] ℋ)) p.denseRange_sqrtSumSq
    ⟨1, by simpa using p.norm_fst_le⟩ ζ

theorem normSnd_apply (p : IsCommutingPair c d) (ζ : ℋ) :
    normSnd c d (sqrtSumSq c d ζ) = d ζ :=
  LinearMap.extendOfNorm_eq (f := (d : ℋ →ₗ[ℂ] ℋ)) p.denseRange_sqrtSumSq
    ⟨1, by simpa using p.norm_snd_le⟩ ζ

/-- `c̃ h = c`. -/
theorem normFst_mul (p : IsCommutingPair c d) : normFst c d * sqrtSumSq c d = c :=
  ContinuousLinearMap.ext fun ζ => p.normFst_apply ζ

/-- `d̃ h = d`. -/
theorem normSnd_mul (p : IsCommutingPair c d) : normSnd c d * sqrtSumSq c d = d :=
  ContinuousLinearMap.ext fun ζ => p.normSnd_apply ζ

/-- `h c̃ = c`; in particular `c̃` commutes with `h`. -/
theorem mul_normFst (p : IsCommutingPair c d) : sqrtSumSq c d * normFst c d = c := by
  refine clm_ext_of_dense p.denseRange_sqrtSumSq ?_
  rintro _ ⟨ζ, rfl⟩
  show sqrtSumSq c d (normFst c d (sqrtSumSq c d ζ)) = c (sqrtSumSq c d ζ)
  rw [p.normFst_apply ζ]
  exact commute_apply p.commute_sqrtSumSq_fst ζ

/-- `h d̃ = d`. -/
theorem mul_normSnd (p : IsCommutingPair c d) : sqrtSumSq c d * normSnd c d = d := by
  refine clm_ext_of_dense p.denseRange_sqrtSumSq ?_
  rintro _ ⟨ζ, rfl⟩
  show sqrtSumSq c d (normSnd c d (sqrtSumSq c d ζ)) = d (sqrtSumSq c d ζ)
  rw [p.normSnd_apply ζ]
  exact commute_apply p.commute_sqrtSumSq_snd ζ

theorem injective_normFst (p : IsCommutingPair c d) : Function.Injective (normFst c d) := by
  intro x y hxy
  refine p.injective_fst ?_
  have h1 : (sqrtSumSq c d * normFst c d) x = (sqrtSumSq c d * normFst c d) y := by
    show sqrtSumSq c d (normFst c d x) = sqrtSumSq c d (normFst c d y)
    rw [hxy]
  rwa [p.mul_normFst] at h1

theorem injective_normSnd (p : IsCommutingPair c d) : Function.Injective (normSnd c d) := by
  intro x y hxy
  refine p.injective_snd ?_
  have h1 : (sqrtSumSq c d * normSnd c d) x = (sqrtSumSq c d * normSnd c d) y := by
    show sqrtSumSq c d (normSnd c d x) = sqrtSumSq c d (normSnd c d y)
    rw [hxy]
  rwa [p.mul_normSnd] at h1

theorem nonneg_normFst (p : IsCommutingPair c d) : (0 : ℋ →L[ℂ] ℋ) ≤ normFst c d := by
  refine nonneg_of_dense p.denseRange_sqrtSumSq ?_
  rintro _ ⟨ζ, rfl⟩
  rw [p.normFst_apply ζ, ← inner_of_nonneg (sqrtSumSq_nonneg c d) (c ζ) ζ]
  have hpos : (0 : ℋ →L[ℂ] ℋ) ≤ sqrtSumSq c d * c :=
    Commute.mul_nonneg (sqrtSumSq_nonneg c d) p.nonneg_fst p.commute_sqrtSumSq_fst
  exact ((ContinuousLinearMap.nonneg_iff_isPositive _).1 hpos).inner_nonneg_left ζ

theorem nonneg_normSnd (p : IsCommutingPair c d) : (0 : ℋ →L[ℂ] ℋ) ≤ normSnd c d := by
  refine nonneg_of_dense p.denseRange_sqrtSumSq ?_
  rintro _ ⟨ζ, rfl⟩
  rw [p.normSnd_apply ζ, ← inner_of_nonneg (sqrtSumSq_nonneg c d) (d ζ) ζ]
  have hpos : (0 : ℋ →L[ℂ] ℋ) ≤ sqrtSumSq c d * d :=
    Commute.mul_nonneg (sqrtSumSq_nonneg c d) p.nonneg_snd p.commute_sqrtSumSq_snd
  exact ((ContinuousLinearMap.nonneg_iff_isPositive _).1 hpos).inner_nonneg_left ζ

theorem commute_norm (p : IsCommutingPair c d) : Commute (normFst c d) (normSnd c d) := by
  refine clm_ext_of_dense p.denseRange_sqrtSumSq_sq ?_
  rintro _ ⟨ζ, rfl⟩
  show normFst c d (normSnd c d (sqrtSumSq c d (sqrtSumSq c d ζ)))
      = normSnd c d (normFst c d (sqrtSumSq c d (sqrtSumSq c d ζ)))
  rw [p.normSnd_apply (sqrtSumSq c d ζ), p.normFst_apply (sqrtSumSq c d ζ)]
  have e1 : d (sqrtSumSq c d ζ) = sqrtSumSq c d (d ζ) :=
    commute_apply p.commute_sqrtSumSq_snd.symm ζ
  have e2 : c (sqrtSumSq c d ζ) = sqrtSumSq c d (c ζ) :=
    commute_apply p.commute_sqrtSumSq_fst.symm ζ
  rw [e1, e2, p.normFst_apply (d ζ), p.normSnd_apply (c ζ)]
  exact commute_apply p.commute ζ

theorem normSq_add_normSq (p : IsCommutingPair c d) :
    normFst c d * normFst c d + normSnd c d * normSnd c d = 1 := by
  refine clm_ext_of_dense p.denseRange_sqrtSumSq_sq ?_
  rintro _ ⟨ζ, rfl⟩
  have e1 : c (sqrtSumSq c d ζ) = sqrtSumSq c d (c ζ) :=
    commute_apply p.commute_sqrtSumSq_fst.symm ζ
  have e2 : d (sqrtSumSq c d ζ) = sqrtSumSq c d (d ζ) :=
    commute_apply p.commute_sqrtSumSq_snd.symm ζ
  show normFst c d (normFst c d (sqrtSumSq c d (sqrtSumSq c d ζ)))
      + normSnd c d (normSnd c d (sqrtSumSq c d (sqrtSumSq c d ζ)))
      = sqrtSumSq c d (sqrtSumSq c d ζ)
  rw [p.normFst_apply (sqrtSumSq c d ζ), p.normSnd_apply (sqrtSumSq c d ζ), e1, e2,
    p.normFst_apply (c ζ), p.normSnd_apply (d ζ)]
  calc c (c ζ) + d (d ζ) = (c * c + d * d) ζ := rfl
    _ = (sqrtSumSq c d * sqrtSumSq c d) ζ := by rw [p.sqrtSumSq_mul_self]
    _ = sqrtSumSq c d (sqrtSumSq c d ζ) := rfl

/-- **Lemma B(a).**  `(c̃, d̃)` is a modular pair. -/
theorem isModularPair (p : IsCommutingPair c d) : IsModularPair (normFst c d) (normSnd c d) :=
  ⟨p.nonneg_normFst, p.nonneg_normSnd, p.commute_norm, p.injective_normFst, p.injective_normSnd,
    p.normSq_add_normSq⟩

theorem mem_domain (p : IsCommutingPair c d) (ζ : ℋ) : c ζ ∈ p.isModularPair.D.domain :=
  ⟨sqrtSumSq c d ζ, p.normFst_apply ζ⟩

/-- **Lemma B(b).**  `D_{c̃,d̃}(cζ) = dζ`. -/
theorem D_apply (p : IsCommutingPair c d) (ζ : ℋ) :
    p.isModularPair.D ⟨c ζ, p.mem_domain ζ⟩ = d ζ := by
  rw [p.isModularPair.D_apply' _ (sqrtSumSq c d ζ) (p.normFst_apply ζ), p.normSnd_apply ζ]

/-- **Lemma B(c).**  For every dense subspace `E ⊆ ℋ`, the image `c(E)` is a core for
`D_{c̃,d̃}`.  The graph of `D_{c̃,d̃}` is the image of `ℋ` under the isometry
`η ↦ (c̃ η, d̃ η)`; the graph of the restriction to `c(E)` is the image of `h(E)`, which is
dense because `h` is bounded with dense range.  Since the graph of `D_{c̃,d̃}` is closed
(self-adjointness), no deficiency-index criterion is needed. -/
theorem hasCore (p : IsCommutingPair c d) {E : Submodule ℂ ℋ} (hE : Dense (E : Set ℋ)) :
    p.isModularPair.D.HasCore (E.map (c : ℋ →ₗ[ℂ] ℋ)) := by
  set D := p.isModularPair.D with hD
  set S : Submodule ℂ ℋ := E.map (c : ℋ →ₗ[ℂ] ℋ) with hSdef
  have hSle : S ≤ D.domain := by
    rintro _ ⟨ξ, -, rfl⟩
    exact p.mem_domain ξ
  refine ⟨hSle, ?_⟩
  have hres_le : D.domRestrict S ≤ D := LinearPMap.domRestrict_le
  have hDclosed : D.IsClosed := p.isModularPair.isClosed
  have hcl : (D.domRestrict S).IsClosable := hDclosed.isClosable.leIsClosable hres_le
  refine LinearPMap.eq_of_eq_graph ?_
  rw [← hcl.graph_closure_eq_closure_graph]
  refine SetLike.ext' ?_
  rw [Submodule.topologicalClosure_coe]
  -- the continuous map `Ψ η = (c̃ η, d̃ η)`
  set Ψ : ℋ → ℋ × ℋ := fun η => (normFst c d η, normSnd c d η) with hΨdef
  have hΨcont : Continuous Ψ := by fun_prop
  -- `h(E)` is dense
  have him : (sqrtSumSq c d) '' (closure (E : Set ℋ)) ⊆ closure ((sqrtSumSq c d) '' (E : Set ℋ)) :=
    image_closure_subset_closure_image (sqrtSumSq c d).continuous
  have hrange : Set.range ⇑(sqrtSumSq c d) ⊆ closure ((sqrtSumSq c d) '' (E : Set ℋ)) := by
    rintro _ ⟨ζ, rfl⟩
    exact him ⟨ζ, by rw [hE.closure_eq]; trivial, rfl⟩
  have hdense : closure ((sqrtSumSq c d) '' (E : Set ℋ)) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← p.denseRange_sqrtSumSq.closure_eq]
    calc closure (Set.range ⇑(sqrtSumSq c d))
        ⊆ closure (closure ((sqrtSumSq c d) '' (E : Set ℋ))) := closure_mono hrange
      _ = _ := closure_closure
  -- the graph of the restriction contains `Ψ (h(E))`
  have hsub : Ψ '' ((sqrtSumSq c d) '' (E : Set ℋ)) ⊆ ((D.domRestrict S).graph : Set (ℋ × ℋ)) := by
    rintro _ ⟨_, ⟨ξ, hξ, rfl⟩, rfl⟩
    have hcξ : c ξ ∈ S ⊓ D.domain := ⟨⟨ξ, hξ, rfl⟩, p.mem_domain ξ⟩
    refine (LinearPMap.mem_graph_iff' _).2 ⟨⟨c ξ, hcξ⟩, ?_⟩
    have hval : (D.domRestrict S) ⟨c ξ, hcξ⟩ = D ⟨c ξ, p.mem_domain ξ⟩ :=
      LinearPMap.domRestrict_apply rfl
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · show c ξ = normFst c d (sqrtSumSq c d ξ)
      exact (p.normFst_apply ξ).symm
    · show (D.domRestrict S) ⟨c ξ, hcξ⟩ = normSnd c d (sqrtSumSq c d ξ)
      rw [hval]
      exact p.isModularPair.D_apply' _ (sqrtSumSq c d ξ) (p.normFst_apply ξ)
  apply Set.Subset.antisymm
  · have h1 : ((D.domRestrict S).graph : Set (ℋ × ℋ)) ⊆ (D.graph : Set (ℋ × ℋ)) :=
      LinearPMap.le_graph_of_le hres_le
    calc closure ((D.domRestrict S).graph : Set (ℋ × ℋ))
        ⊆ closure (D.graph : Set (ℋ × ℋ)) := closure_mono h1
      _ = _ := hDclosed.closure_eq
  · rintro ⟨x, y⟩ hxy
    obtain ⟨z, hz⟩ := (LinearPMap.mem_graph_iff' D).1 hxy
    obtain ⟨η, hη⟩ := z.2
    have hzval : D z = normSnd c d η := p.isModularPair.D_apply' z η hη
    have hpt : (x, y) = Ψ η := by
      rw [← hz, hΨdef]
      exact Prod.ext hη.symm hzval
    rw [hpt]
    have : Ψ '' (closure ((sqrtSumSq c d) '' (E : Set ℋ)))
        ⊆ closure (Ψ '' ((sqrtSumSq c d) '' (E : Set ℋ))) :=
      image_closure_subset_closure_image hΨcont
    have hmem : Ψ η ∈ closure (Ψ '' ((sqrtSumSq c d) '' (E : Set ℋ))) :=
      this ⟨η, by rw [hdense]; trivial, rfl⟩
    exact closure_mono hsub hmem

end IsCommutingPair

end Theses.RvD
