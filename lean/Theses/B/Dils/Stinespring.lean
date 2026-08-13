/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 2–1266.

  parsec 1350:  GNS' and Stinespring's theorem (statements)
  parsec 1360:  completion of an inner product space into a Hilbert space
  parsec 1370:  proof of Stinespring's theorem (proof steps, not converted)
  parsec 1380:  nmiu-maps between type I factors, Kraus decomposition,
                essential uniqueness of purification
  parsec 1390:  normal Stinespring dilations, their universal property
  parsec 1400:  Paschke dilations: definition, Stinespring is Paschke,
                uniqueness, basic properties

Statements only; every proof is `sorry`.  See CONVENTIONS.md for the
numbering (**135II** = parsec 1350, point 20) and naming conventions.

Conventions specific to this file: all von Neumann algebras and Hilbert
spaces live in a single universe `u`; the ncp-maps `φ : 𝒜 → B(H)` of the
thesis are represented either by a bare linear map plus
`IsCompletelyPositiveMap`/`PreservesDirSups` (following
`Theses.A.CStar.Matrices`) or by the bundled `Theses.NCPMap`;
`ad_V = conjOperator V` is from `Theses.A.CStar.Matrices`.
-/
import Theses.Common
import Theses.A.CStar.Matrices
import Theses.A.VN.Projections

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra WithCStarModule
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u v

namespace Theses.B.Dils

/-! ## Parsec 1350: GNS' and Stinespring

**135I** (dils.tex:5): introduction — nothing to formalize. -/

section GNSStinespring

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **135II** (`dils-gns`, dils.tex:15, Theorem (GNS')): for each pu-map
`ω : 𝒜 → ℂ` from a C*-algebra `𝒜` there is a Hilbert space `ℋ`, an miu-map
`ϱ : 𝒜 → B(ℋ)` and a vector `x ∈ ℋ` such that `ω = h ∘ ϱ` where
`h(T) = ⟪x, Tx⟫`. -/
theorem dils_gns (ω : 𝒜 →ₗ[ℂ] ℂ) (hp : IsPositiveMap ω) (hu : ω 1 = 1) :
    ∃ (ℋ : Type u) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (ϱ : MIUMap 𝒜 (ℋ →L[ℂ] ℋ)) (x : ℋ),
      ∀ a : 𝒜, ω a = ⟪x, ϱ a x⟫ :=
  sorry

/-- **135IV** (`stinespring-theorem`, dils.tex:37, Theorem (Stinespring)):
for every cp-map `φ : 𝒜 → B(ℋ)` from a C*-algebra `𝒜` to the bounded
operators on a Hilbert space `ℋ` there are a Hilbert space `𝒦`, an miu-map
`ϱ : 𝒜 → B(𝒦)` and a bounded operator `V : ℋ → 𝒦` with
`φ = ad_V ∘ ϱ`, i.e. `φ(a) = V* ϱ(a) V`. -/
theorem stinespring (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) (hφ : IsCompletelyPositiveMap φ) :
    ∃ (𝒦 : Type u) (_ : NormedAddCommGroup 𝒦) (_ : InnerProductSpace ℂ 𝒦)
      (_ : CompleteSpace 𝒦) (ϱ : MIUMap 𝒜 (𝒦 →L[ℂ] 𝒦)) (V : H →L[ℂ] 𝒦),
      ∀ a : 𝒜, φ a = conjOperator V (ϱ a) :=
  sorry

/-- **135IV** (`stinespring-theorem`, dils.tex:37, Theorem (Stinespring)),
part 1: if moreover `φ` is unital, the dilation can be chosen with `V` an
isometry. -/
theorem stinespring_unital (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H))
    (hφ : IsCompletelyPositiveMap φ) (hu : φ 1 = 1) :
    ∃ (𝒦 : Type u) (_ : NormedAddCommGroup 𝒦) (_ : InnerProductSpace ℂ 𝒦)
      (_ : CompleteSpace 𝒦) (ϱ : MIUMap 𝒜 (𝒦 →L[ℂ] 𝒦)) (V : H →L[ℂ] 𝒦),
      Isometry V ∧ ∀ a : 𝒜, φ a = conjOperator V (ϱ a) :=
  sorry

/-- **135IV** (`stinespring-theorem`, dils.tex:37, Theorem (Stinespring)),
part 2: if `𝒜` is a von Neumann algebra and `φ` is normal, then the
representation `ϱ` can be chosen normal as well (an nmiu-map).

**135V**, **135VI** (`overview-dils`): discussion and overview — nothing to
formalize. -/
theorem stinespring_normal [VonNeumannAlgebra 𝒜] (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H))
    (hφ : IsCompletelyPositiveMap φ) (hn : PreservesDirSups ⇑φ) :
    ∃ (𝒦 : Type u) (_ : NormedAddCommGroup 𝒦) (_ : InnerProductSpace ℂ 𝒦)
      (_ : CompleteSpace 𝒦) (ϱ : NMIUMap 𝒜 (𝒦 →L[ℂ] 𝒦)) (V : H →L[ℂ] 𝒦),
      ∀ a : 𝒜, φ a = conjOperator V (ϱ a) :=
  sorry

end GNSStinespring

/-! ## Parsec 1360: completion into a Hilbert space

**136I** (dils.tex:218): introduction — nothing to formalize.
**136III**–**136VII** are the proof of **136II** — not converted. -/

/-- **136II** (`prop-complete-into-hilbert-space`, dils.tex:238,
Proposition): let `V` be a complex vector space with a (not necessarily
definite) inner product, here a positive conjugate-symmetric sesquilinear
form `B`.  There is a Hilbert space `ℋ` and a bounded (automatic here)
linear map `η : V → ℋ` with `B v w = ⟪η v, η w⟫` and dense image.
(Cf. `inner_product_completion`, cstar.tex 30V, which assumes definiteness.) -/
theorem prop_complete_into_hilbert_space (V : Type v) [AddCommGroup V]
    [Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hsymm : ∀ v w : V, B w v = starRingEnd ℂ (B v w))
    (hpos : ∀ v : V, 0 ≤ (B v v).re) :
    ∃ (ℋ : Type v) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (η : V →ₗ[ℂ] ℋ),
      (∀ v w : V, (⟪η v, η w⟫ : ℂ) = B v w) ∧ DenseRange η := by
  -- The author's proof (dils.tex:250) builds `ℋ` by hand from fast Cauchy
  -- sequences, i.e. re-develops the metric completion; we instead use
  -- Mathlib's: `B` makes `V` a *semi*-inner-product space, its separation
  -- quotient is an inner product space, and its completion is a Hilbert
  -- space.  (Divergence (2): the same construction, taken off the shelf.)
  let core : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => B x y
      conj_inner_symm := fun x y => (hsymm y x).symm
      re_inner_nonneg := hpos
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  let _ : SeminormedAddCommGroup V :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ) (F := V) (c := core)
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore core
  refine ⟨UniformSpace.Completion (SeparationQuotient V), inferInstance, inferInstance,
    inferInstance,
    ((UniformSpace.Completion.toComplL : SeparationQuotient V →L[ℂ]
        UniformSpace.Completion (SeparationQuotient V)).comp
      (SeparationQuotient.mkCLM ℂ V)).toLinearMap, fun v w => ?_, ?_⟩
  · change (⟪((SeparationQuotient.mk v : SeparationQuotient V) :
        UniformSpace.Completion (SeparationQuotient V)),
      ((SeparationQuotient.mk w : SeparationQuotient V) :
        UniformSpace.Completion (SeparationQuotient V))⟫ : ℂ) = B v w
    rw [UniformSpace.Completion.inner_coe, SeparationQuotient.inner_mk_mk]
    rfl
  · exact UniformSpace.Completion.denseRange_coe.comp
      SeparationQuotient.surjective_mk.denseRange
      (UniformSpace.Completion.continuous_coe _)

/-! ## Parsec 1370: proof of Stinespring's theorem

**137I**–**137VII** (dils.tex:397–585) are the proof of **135IV**
(`dils-proof-stinespring` and its sub-points, including the extension lemma
`stinespring-extend-operator`) — proof steps, not converted.
**137VIII** (dils.tex:586, Remark) — not converted. -/

/-! ## The Hilbert space tensor product

Infrastructure for parsec 1380: the completed tensor product `H ⊗ K` of
Hilbert spaces (Mathlib: the inner product space `H ⊗[ℂ] K` and its
`UniformSpace.Completion`), and the operator `a ⊗ b` on it.  (The Hilbert
space tensor product is developed in thesis A, proc.tex parsecs 1090–1100,
which is not yet formalized; we use Mathlib's ingredients directly.) -/

section HilbTensor

variable (H K : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- The Hilbert space tensor product `H ⊗ K`: the completion of the
algebraic tensor product `H ⊗[ℂ] K` with the inner product
`⟪x ⊗ y, x' ⊗ y'⟫ = ⟪x, x'⟫ ⟪y, y'⟫`. -/
noncomputable abbrev hilbTensor : Type u :=
  UniformSpace.Completion (TensorProduct ℂ H K)

variable {H K}

/-- The canonical image of an elementary tensor `x ⊗ y` in `hilbTensor H K`. -/
noncomputable def hilbTensorMk (x : H) (y : K) : hilbTensor H K :=
  ((x ⊗ₜ[ℂ] y : TensorProduct ℂ H K) : hilbTensor H K)

/-- The operator `a ⊗ b` on `hilbTensor H K`, for bounded operators
`a : H → H` and `b : K → K` — the continuous extension of
`TensorProduct.map`, obtained as `TensorProduct.mapL` followed by
`LinearMap.extendOfNorm` along the dense range into the completion.  Its
characterizing property is `tensorCLM_mk` below. -/
noncomputable def tensorCLM (a : H →L[ℂ] H) (b : K →L[ℂ] K) :
    hilbTensor H K →L[ℂ] hilbTensor H K :=
  LinearMap.extendOfNorm
    (((UniformSpace.Completion.toComplL :
          TensorProduct ℂ H K →L[ℂ] hilbTensor H K).comp
        (TensorProduct.mapL a b)).toLinearMap)
    ((UniformSpace.Completion.toComplL :
        TensorProduct ℂ H K →L[ℂ] hilbTensor H K).toLinearMap)

set_option linter.unusedSectionVars false in
/-- Characterizing property of `tensorCLM`:
`(a ⊗ b) (x ⊗ y) = (a x) ⊗ (b y)`. -/
theorem tensorCLM_mk (a : H →L[ℂ] H) (b : K →L[ℂ] K) (x : H) (y : K) :
    tensorCLM a b (hilbTensorMk x y) = hilbTensorMk (a x) (b y) := by
  have hdense : DenseRange
      ⇑((UniformSpace.Completion.toComplL :
          TensorProduct ℂ H K →L[ℂ] hilbTensor H K).toLinearMap) := by
    simpa [UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.denseRange_coe (α := TensorProduct ℂ H K))
  have hnorm : ∃ C : ℝ, ∀ z : TensorProduct ℂ H K,
      ‖(((UniformSpace.Completion.toComplL :
            TensorProduct ℂ H K →L[ℂ] hilbTensor H K).comp
          (TensorProduct.mapL a b)).toLinearMap) z‖ ≤
        C * ‖((UniformSpace.Completion.toComplL :
            TensorProduct ℂ H K →L[ℂ] hilbTensor H K).toLinearMap) z‖ := by
    refine ⟨‖a‖ * ‖b‖, fun z => ?_⟩
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
      Function.comp_apply,
      UniformSpace.Completion.coe_toComplL, UniformSpace.Completion.norm_coe]
    calc ‖TensorProduct.mapL a b z‖ ≤ ‖TensorProduct.mapL a b‖ * ‖z‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖a‖ * ‖b‖ * ‖z‖ :=
          mul_le_mul_of_nonneg_right (TensorProduct.norm_mapL_le a b) (norm_nonneg _)
  change LinearMap.extendOfNorm _ _
    ((UniformSpace.Completion.toComplL :
      TensorProduct ℂ H K →L[ℂ] hilbTensor H K).toLinearMap (x ⊗ₜ[ℂ] y)) = _
  rw [LinearMap.extendOfNorm_eq hdense hnorm]
  rfl

end HilbTensor

/-! ## Parsec 1380: consequences of Stinespring

**138I** (dils.tex:597): introduction — nothing to formalize.
**138III**–**138V** are the proof of **138II** — not converted. -/

section TypeI

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **138II** (`nmiu-between-type-I`, dils.tex:608, Proposition): every
non-zero nmiu-map `ϱ : B(ℋ) → B(𝒦)` between the bounded operators on
Hilbert spaces is of the form `ϱ(a) = U* (a ⊗ 1) U` for some Hilbert space
`𝒦'` and unitary `U : 𝒦 → ℋ ⊗ 𝒦'`. -/
theorem nmiu_between_type_I (ϱ : NMIUMap (H →L[ℂ] H) (K →L[ℂ] K))
    (hnz : ∃ a, ϱ a ≠ 0) :
    ∃ (K' : Type u) (_ : NormedAddCommGroup K') (_ : InnerProductSpace ℂ K')
      (_ : CompleteSpace K') (U : K →L[ℂ] hilbTensor H K'),
      (ContinuousLinearMap.adjoint U).comp U = 1 ∧
      U.comp (ContinuousLinearMap.adjoint U) = 1 ∧
      ∀ a : H →L[ℂ] H, ϱ a = conjOperator U (tensorCLM a 1) :=
  sorry

/-- **138VI** (`typei-inner-auto`, dils.tex:719, Corollary): the
nmiu-isomorphisms `B(ℋ) → B(𝒦)` are precisely the maps `ad_U` for a unitary
`U : 𝒦 → ℋ`. -/
theorem typei_inner_auto (ϱ : NMIUMap (H →L[ℂ] H) (K →L[ℂ] K)) :
    Function.Bijective ⇑ϱ ↔
      ∃ U : K →L[ℂ] H,
        (ContinuousLinearMap.adjoint U).comp U = 1 ∧
        U.comp (ContinuousLinearMap.adjoint U) = 1 ∧
        ∀ a : H →L[ℂ] H, ϱ a = conjOperator U a :=
  sorry

/-- **138VII** (`physics-stinespring`, dils.tex:725, Exercise*): for every
ncp-map `φ : B(ℋ) → B(𝒦)` there are a Hilbert space `𝒦'` and a bounded
operator `V : 𝒦 → ℋ ⊗ 𝒦'` such that `φ(a) = V* (a ⊗ 1) V`.

(The second half — every quantum channel on trace-class operators is of the
form `Φ(ϱ) = Tr_{𝒦'}[U* (ϱ ⊗ |v₀⟩⟨v₀|) U]` — is not converted: trace-class
operators are not yet available in this formalization.) -/
theorem physics_stinespring (φ : NCPMap (H →L[ℂ] H) (K →L[ℂ] K)) :
    ∃ (K' : Type u) (_ : NormedAddCommGroup K') (_ : InnerProductSpace ℂ K')
      (_ : CompleteSpace K') (V : K →L[ℂ] hilbTensor H K'),
      ∀ a : H →L[ℂ] H, φ a = conjOperator V (tensorCLM a 1) :=
  sorry

/-- **138VIII** (`kraus-exercise`, dils.tex:742, Exercise* (Kraus'
decomposition)): every ncp-map `φ : B(ℋ) → B(𝒦)` is of the form
`φ(a) = ∑ᵢ Vᵢ* a Vᵢ` for bounded operators `Vᵢ : 𝒦 → ℋ` whose partial sums
`∑ᵢ Vᵢ* Vᵢ` are bounded, the sum converging ultraweakly. -/
theorem kraus_decomposition (φ : NCPMap (H →L[ℂ] H) (K →L[ℂ] K)) :
    ∃ (ι : Type u) (V : ι → (K →L[ℂ] H)),
      (∃ M : ℝ, ∀ s : Finset ι, ‖∑ i ∈ s, conjOperator (V i) 1‖ ≤ M) ∧
      ∀ a : H →L[ℂ] H,
        UWTendsto (fun s : Finset ι => ∑ i ∈ s, conjOperator (V i) a)
          atTop (φ a) :=
  sorry

/-- **138VIII** (`kraus-exercise`, dils.tex:742, Exercise*), finite
dimensional case: for finite-dimensional `ℋ` and `𝒦` the number of Kraus
operators can be chosen `≤ dim ℋ · dim 𝒦`. -/
theorem kraus_decomposition_findim [FiniteDimensional ℂ H]
    [FiniteDimensional ℂ K] (φ : NCPMap (H →L[ℂ] H) (K →L[ℂ] K)) :
    ∃ n : ℕ, n ≤ Module.finrank ℂ H * Module.finrank ℂ K ∧
      ∃ V : Fin n → (K →L[ℂ] H),
        ∀ a : H →L[ℂ] H, φ a = ∑ i, conjOperator (V i) a :=
  sorry

end TypeI

/-! ## Parsec 1390: normal Stinespring dilations -/

section NormalStinespring

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **139I** (dils.tex:778, Definition): a **normal Stinespring dilation**
of an ncp-map `φ : 𝒜 → B(ℋ)` (here: of the bare map `⇑φ`): a triple
`(𝒦, ϱ, V)` with `𝒦` a Hilbert space, `ϱ : 𝒜 → B(𝒦)` an nmiu-map and
`V : ℋ → 𝒦` a bounded operator with `φ = ad_V ∘ ϱ`. -/
structure StinespringDilation (φ : 𝒜 → (H →L[ℂ] H)) : Type (u + 1) where
  /-- The dilating Hilbert space `𝒦`. -/
  K : Type u
  [nacg : NormedAddCommGroup K]
  [ips : InnerProductSpace ℂ K]
  [cs : CompleteSpace K]
  /-- The normal representation `ϱ : 𝒜 → B(𝒦)`. -/
  ρ : NMIUMap 𝒜 (K →L[ℂ] K)
  /-- The bounded operator `V : ℋ → 𝒦`. -/
  V : H →L[ℂ] K
  /-- `φ = ad_V ∘ ϱ`. -/
  eq : ∀ a : 𝒜, φ a = conjOperator V (ρ a)

attribute [instance] StinespringDilation.nacg StinespringDilation.ips
  StinespringDilation.cs

/-- **139I** (dils.tex:778, Definition), continued: a Stinespring dilation
`(𝒦, ϱ, V)` is **minimal** if the linear span of
`ϱ(𝒜)Vℋ = {ϱ(a)Vx : a ∈ 𝒜, x ∈ ℋ}` is dense in `𝒦`. -/
def StinespringDilation.Minimal {φ : 𝒜 → (H →L[ℂ] H)}
    (D : StinespringDilation φ) : Prop :=
  Dense (Submodule.span ℂ
    {k : D.K | ∃ (a : 𝒜) (x : H), k = D.ρ a (D.V x)} : Set D.K)

/-- **139I** (dils.tex:778, Definition), embedded claims: every ncp-map
`φ : 𝒜 → B(ℋ)` has a normal Stinespring dilation (by **135IV**), and (by
restricting an arbitrary dilation to the closure of the span of `ϱ(𝒜)Vℋ`)
even a minimal one. -/
theorem exists_minimal_stinespringDilation [VonNeumannAlgebra 𝒜]
    (φ : NCPMap 𝒜 (H →L[ℂ] H)) :
    ∃ D : StinespringDilation ⇑φ, D.Minimal :=
  sorry

/-- **139III** (`dils-univlemma`, dils.tex:823, Lemma): for nmiu-maps
`ϱ : 𝒜 → ℬ`, `ϱ' : 𝒜 → 𝒞` between von Neumann algebras and an ncp-map
`σ : 𝒞 → ℬ` with `σ ∘ ϱ' = ϱ` we have
`σ(ϱ'(a₁) c ϱ'(a₂)) = ϱ(a₁) σ(c) ϱ(a₂)`.

**139II** (dils.tex:805): discussion — nothing to formalize.
**139IV** is the proof — not converted. -/
theorem dils_univlemma {ℬ 𝒞 : Type u}
    [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]
    (ϱ : NMIUMap 𝒜 ℬ) (ϱ' : NMIUMap 𝒜 𝒞) (σ : NCPMap 𝒞 ℬ)
    (h : ∀ a, σ (ϱ' a) = ϱ a) (a₁ a₂ : 𝒜) (c : 𝒞) :
    σ (ϱ' a₁ * c * ϱ' a₂) = ϱ a₁ * σ c * ϱ a₂ := by
  -- dils.tex:833 (**139IV**), transcribed.
  set f : 𝒞 →ₗ[ℂ] ℬ := σ.toCompletelyPositiveMap.toLinearMap with hf
  have hfc : ∀ x : 𝒞, f x = σ x := fun _ => rfl
  have hcp : IsCompletelyPositiveMap f :=
    (cp_iff f).out 1 0 |>.mp fun N M hM =>
      σ.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hu : f 1 = 1 := by
    have h1 : σ (ϱ' (1 : 𝒜)) = ϱ 1 := h 1
    rw [show (ϱ' (1 : 𝒜)) = 1 from map_one ϱ'.toStarAlgHom,
      show (ϱ (1 : 𝒜)) = 1 from map_one ϱ.toStarAlgHom] at h1
    exact h1
  have hp : IsPositiveMap f := astara_pos_basic_2_cp f hcp
  have hi : ∀ x : 𝒞, f (star x) = star (f x) := cstar_p_implies_i f hp
  -- `σ(ϱ'(a)* ϱ'(a)) = σ(ϱ'(a* a)) = ϱ(a* a) = ϱ(a)* ϱ(a) = σ(ϱ'(a))* σ(ϱ'(a))`,
  -- so Choi's lemma **34XVIII**.2 applies at `ϱ'(a)`.
  have hmulR : ∀ (a : 𝒜) (x : 𝒞), σ (x * ϱ' a) = σ x * ϱ a := by
    intro a x
    have hkey : f (star (ϱ' a) * ϱ' a) = star (f (ϱ' a)) * f (ϱ' a) := by
      rw [show star (ϱ' a) * ϱ' a = ϱ' (star a * a) by
        rw [show (ϱ' (star a * a)) = ϱ' (star a) * ϱ' a from
            map_mul ϱ'.toStarAlgHom _ _,
          show (ϱ' (star a)) = star (ϱ' a) from map_star ϱ'.toStarAlgHom _]]
      rw [hfc, hfc, h, h, show (ϱ (star a * a)) = ϱ (star a) * ϱ a from
        map_mul ϱ.toStarAlgHom _ _, show (ϱ (star a)) = star (ϱ a) from
        map_star ϱ.toStarAlgHom _]
    have := choi_2 f hcp hu (ϱ' a) hkey x
    rw [hfc, hfc, hfc, h] at this
    exact this
  -- taking adjoints: `σ(ϱ'(a) x) = ϱ(a) σ(x)`
  have hmulL : ∀ (a : 𝒜) (x : 𝒞), σ (ϱ' a * x) = ϱ a * σ x := by
    intro a x
    have h1 := hmulR (star a) (star x)
    rw [show (ϱ' (star a)) = star (ϱ' a) from map_star ϱ'.toStarAlgHom _,
      show (ϱ (star a)) = star (ϱ a) from map_star ϱ.toStarAlgHom _,
      ← star_mul, ← hfc, ← hfc, hi, hi] at h1
    have h2 := congrArg star h1
    rw [star_star] at h2
    rwa [star_mul, star_star, star_star, hfc] at h2
  rw [hmulR, hmulL]

/-! ### Infrastructure for **139V**

The author's proof of **139V** works with formal sums `∑ᵢ ϱ(aᵢ)Vxᵢ`; we
package these as the image of the algebraic tensor product `𝒜 ⊗ ℋ` under
the linear map `sdMap` below, which lets the norm identity of dils.tex:895
be stated as `‖sdMap D t‖ = ‖sdMap D' t‖` and the mediating isometry be
obtained from `LinearMap.extendOfNorm`. -/

section UnivStinespring

variable {φ : 𝒜 → (H →L[ℂ] H)}

/-- Auxiliary for **139V**: the linear map `𝒜 ⊗ ℋ → 𝒦`, `a ⊗ x ↦ ϱ(a)Vx`,
of a Stinespring dilation; its range is the linear span of `ϱ(𝒜)Vℋ`. -/
private noncomputable def sdMap (D : StinespringDilation φ) :
    TensorProduct ℂ 𝒜 H →ₗ[ℂ] D.K :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ (fun (a : 𝒜) (x : H) => D.ρ a (D.V x))
    (fun a b x => by
      rw [show D.ρ (a + b) = D.ρ a + D.ρ b from map_add D.ρ.toStarAlgHom a b]
      rfl)
    (fun c a x => by
      rw [show D.ρ (c • a) = c • D.ρ a from map_smul D.ρ.toStarAlgHom c a]
      rfl)
    (fun a x y => by rw [map_add, map_add])
    (fun c a x => by rw [map_smul, map_smul])

private theorem sdMap_tmul (D : StinespringDilation φ) (a : 𝒜) (x : H) :
    sdMap D (a ⊗ₜ[ℂ] x) = D.ρ a (D.V x) := rfl

/-- The inner product of two elementary tensors depends only on `φ`
(dils.tex:895): `⟪ϱ(a)Vx, ϱ(b)Vy⟫ = ⟪x, φ(a*b)y⟫`. -/
private theorem sdMap_inner_tmul (D : StinespringDilation φ) (a b : 𝒜)
    (x y : H) :
    (⟪sdMap D (a ⊗ₜ[ℂ] x), sdMap D (b ⊗ₜ[ℂ] y)⟫ : ℂ)
      = ⟪x, φ (star a * b) y⟫ := by
  rw [sdMap_tmul, sdMap_tmul, ← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint,
    show star (D.ρ a) = D.ρ (star a) from (map_star D.ρ.toStarAlgHom a).symm,
    show D.ρ (star a) (D.ρ b (D.V y)) = D.ρ (star a * b) (D.V y) from by
      rw [show D.ρ (star a * b) = D.ρ (star a) * D.ρ b from
        map_mul D.ρ.toStarAlgHom _ _]; rfl,
    ← ContinuousLinearMap.adjoint_inner_right, D.eq]
  rfl

/-- Consequently two Stinespring dilations of the same map give the same
inner products on `𝒜 ⊗ ℋ`. -/
private theorem sdMap_inner_eq (D D' : StinespringDilation φ)
    (s t : TensorProduct ℂ 𝒜 H) :
    (⟪sdMap D s, sdMap D t⟫ : ℂ) = ⟪sdMap D' s, sdMap D' t⟫ := by
  induction s with
  | zero => simp
  | add s₁ s₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | tmul a x =>
    induction t with
    | zero => simp
    | add t₁ t₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | tmul b y => rw [sdMap_inner_tmul, sdMap_inner_tmul]

private theorem sdMap_norm_eq (D D' : StinespringDilation φ)
    (t : TensorProduct ℂ 𝒜 H) : ‖sdMap D' t‖ = ‖sdMap D t‖ := by
  have h := sdMap_inner_eq D D' t t
  have h1 : ‖sdMap D t‖ ^ 2 = ‖sdMap D' t‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
    exact congrArg Complex.re h
  nlinarith [norm_nonneg (sdMap D t), norm_nonneg (sdMap D' t)]

private theorem sdMap_range (D : StinespringDilation φ) :
    LinearMap.range (sdMap D) =
      Submodule.span ℂ {k : D.K | ∃ (a : 𝒜) (x : H), k = D.ρ a (D.V x)} := by
  rw [LinearMap.range_eq_map, ← TensorProduct.span_tmul_eq_top ℂ 𝒜 H,
    Submodule.map_span]
  congr 1
  ext k
  constructor
  · rintro ⟨_, ⟨a, x, rfl⟩, rfl⟩
    exact ⟨a, x, rfl⟩
  · rintro ⟨a, x, rfl⟩
    exact ⟨a ⊗ₜ[ℂ] x, ⟨a, x, rfl⟩, rfl⟩

private theorem sdMap_denseRange {D : StinespringDilation φ}
    (hmin : D.Minimal) : DenseRange (sdMap D) := by
  have h : Set.range (sdMap D) = (Submodule.span ℂ
      {k : D.K | ∃ (a : 𝒜) (x : H), k = D.ρ a (D.V x)} : Set D.K) := by
    rw [show Set.range (sdMap D)
      = ((LinearMap.range (sdMap D) : Submodule ℂ D.K) : Set D.K) from rfl,
      sdMap_range]
  rw [DenseRange, h]
  exact hmin

end UnivStinespring

/-- **139V** (`dils-univ-stinespring`, dils.tex:863, Proposition): if
`(𝒦, ϱ, V)` and `(𝒦', ϱ', V')` are normal Stinespring dilations of the same
ncp-map `φ : 𝒜 → B(ℋ)` and `(𝒦, ϱ, V)` is minimal, then there is a unique
isometry `S : 𝒦 → 𝒦'` with `SV = V'` and `ϱ = ad_S ∘ ϱ'`.

**139VI**–**139VIII** are the proof — not converted. -/
theorem dils_univ_stinespring (φ : NCPMap 𝒜 (H →L[ℂ] H))
    (D D' : StinespringDilation ⇑φ) (hmin : D.Minimal) :
    ∃! S : D.K →L[ℂ] D'.K,
      Isometry S ∧ S.comp D.V = D'.V ∧
        ∀ a : 𝒜, D.ρ a = conjOperator S (D'.ρ a) := by
  have hdense : DenseRange (sdMap D) := sdMap_denseRange hmin
  have hbound : ∃ C : ℝ, ∀ t, ‖sdMap D' t‖ ≤ C * ‖sdMap D t‖ :=
    ⟨1, fun t => by rw [one_mul, sdMap_norm_eq D D' t]⟩
  -- `‖∑ᵢ ϱ(aᵢ)Vxᵢ‖ = ‖∑ᵢ ϱ'(aᵢ)V'xᵢ‖` (dils.tex:895) gives the isometry
  set S : D.K →L[ℂ] D'.K := LinearMap.extendOfNorm (sdMap D') (sdMap D) with hSdef
  have hSt : ∀ t, S (sdMap D t) = sdMap D' t :=
    fun t => LinearMap.extendOfNorm_eq hdense hbound t
  have hSnorm : ∀ k : D.K, ‖S k‖ = ‖k‖ := fun k =>
    hdense.induction_on k (isClosed_eq (by fun_prop) (by fun_prop))
      (fun t => by rw [hSt, sdMap_norm_eq D D' t])
  have hSinner : ∀ k l : D.K, (⟪S k, S l⟫ : ℂ) = ⟪k, l⟫ :=
    (LinearIsometry.mk S.toLinearMap hSnorm).inner_map_map
  have hSadj : ∀ k : D.K, ContinuousLinearMap.adjoint S (S k) = k := by
    intro k
    refine ext_inner_left ℂ fun v => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, hSinner]
  -- `SV = V'`, since `V x = ϱ(1)Vx`
  have hV : ∀ x : H, sdMap D ((1 : 𝒜) ⊗ₜ[ℂ] x) = D.V x := by
    intro x
    rw [sdMap_tmul, show D.ρ (1 : 𝒜) = 1 from map_one D.ρ.toStarAlgHom]
    rfl
  have hV' : ∀ x : H, sdMap D' ((1 : 𝒜) ⊗ₜ[ℂ] x) = D'.V x := by
    intro x
    rw [sdMap_tmul, show D'.ρ (1 : 𝒜) = 1 from map_one D'.ρ.toStarAlgHom]
    rfl
  have hSV : S.comp D.V = D'.V := by
    refine ContinuousLinearMap.ext fun x => ?_
    rw [ContinuousLinearMap.comp_apply, ← hV, hSt, hV']
  -- `S ϱ(a) = ϱ'(a) S` (dils.tex:917)
  have hkey : ∀ (a : 𝒜) (t : TensorProduct ℂ 𝒜 H),
      S (D.ρ a (sdMap D t)) = D'.ρ a (sdMap D' t) := by
    intro a t
    induction t with
    | zero => simp
    | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul b x =>
      rw [sdMap_tmul, sdMap_tmul,
        show D.ρ a (D.ρ b (D.V x)) = sdMap D ((a * b) ⊗ₜ[ℂ] x) from by
          rw [sdMap_tmul, show D.ρ (a * b) = D.ρ a * D.ρ b from
            map_mul D.ρ.toStarAlgHom _ _]; rfl,
        hSt, sdMap_tmul,
        show D'.ρ (a * b) = D'.ρ a * D'.ρ b from map_mul D'.ρ.toStarAlgHom _ _]
      rfl
  have hintw : ∀ (a : 𝒜) (k : D.K), S (D.ρ a k) = D'.ρ a (S k) := fun a k =>
    hdense.induction_on k (isClosed_eq (by fun_prop) (by fun_prop))
      (fun t => by rw [hkey a t, hSt])
  have hρ : ∀ a : 𝒜, D.ρ a = conjOperator S (D'.ρ a) := by
    intro a
    refine ContinuousLinearMap.ext fun k => ?_
    change D.ρ a k = ContinuousLinearMap.adjoint S ((D'.ρ a).comp S k)
    rw [ContinuousLinearMap.comp_apply, ← hintw a k, hSadj]
  refine ⟨S, ⟨AddMonoidHomClass.isometry_of_norm S hSnorm, hSV, hρ⟩, ?_⟩
  -- Uniqueness.  Any `T` as in the statement already satisfies
  -- `T ϱ(a)Vx = ϱ'(a)V'x`, which pins it down on the dense span.
  rintro T ⟨hTiso, hTV, hTρ⟩
  have hTnorm : ∀ k : D.K, ‖T k‖ = ‖k‖ := fun k => by
    simpa using hTiso.dist_eq k 0
  have hTinner : ∀ k l : D.K, (⟪T k, T l⟫ : ℂ) = ⟪k, l⟫ :=
    (LinearIsometry.mk T.toLinearMap hTnorm).inner_map_map
  have hTtmul : ∀ t : TensorProduct ℂ 𝒜 H, T (sdMap D t) = sdMap D' t := by
    intro t
    induction t with
    | zero => simp
    | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul b x =>
      set y : D'.K := sdMap D' (b ⊗ₜ[ℂ] x) with hy
      set u : D.K := sdMap D (b ⊗ₜ[ℂ] x) with hu
      -- `u = T* y`: indeed `ϱ(b)Vx = T*ϱ'(b)T V x = T*ϱ'(b)V'x`
      have hTu : ContinuousLinearMap.adjoint T y = u := by
        have h1 : D.ρ b (D.V x) =
            ContinuousLinearMap.adjoint T ((D'.ρ b) (T (D.V x))) := by
          have := hTρ b
          have h2 := congrArg (fun (P : D.K →L[ℂ] D.K) => P (D.V x)) this
          simpa [conjOperator] using h2
        rw [hu, hy, sdMap_tmul, sdMap_tmul, h1,
          show T (D.V x) = D'.V x from by
            rw [← hTV]; rfl]
      -- `‖y − T u‖² = ⟪y,y⟫ − ⟪u,u⟫ = 0` by the norm identity
      have hyy : (⟪y, y⟫ : ℂ) = ⟪u, u⟫ :=
        sdMap_inner_eq D' D (b ⊗ₜ[ℂ] x) (b ⊗ₜ[ℂ] x)
      have hzero : (⟪y - T u, y - T u⟫ : ℂ) = 0 := by
        rw [inner_sub_sub_self]
        rw [show (⟪T u, y⟫ : ℂ) = ⟪u, u⟫ from by
              rw [← ContinuousLinearMap.adjoint_inner_right, hTu],
          show (⟪y, T u⟫ : ℂ) = ⟪u, u⟫ from by
              rw [← ContinuousLinearMap.adjoint_inner_left, hTu],
          hTinner, hyy]
        ring
      exact (sub_eq_zero.mp (inner_self_eq_zero.mp hzero)).symm
  refine ContinuousLinearMap.ext fun k => ?_
  refine hdense.induction_on k (isClosed_eq (by fun_prop) (by fun_prop))
    fun t => ?_
  rw [hTtmul t, hSt]

/-- **139IX** (`exc-chris-univ-prop`, dils.tex:945, Exercise*): the
universal property **139V** makes the minimal Stinespring dilation a
universal arrow, i.e. the inclusion `Rep → Rep_cp` (of normal
representations into ncpu-maps `φ : 𝒜 → B(ℋ)` with morphisms
`(m, S) : φ → φ'` given by an nmiu-map `m` and an isometry `S` with
`φ = ad_S ∘ φ' ∘ m`) has a left adjoint.  Stated as: for every ncpu-map `φ`
there is a normal representation `ψ : 𝒜 → B(𝒦)` and a morphism
`(id, S₀) : φ → ψ` through which every morphism from `φ` to a normal
representation factors uniquely.

**139IXa** (Remarks), **139X**: discussion — nothing to formalize. -/
theorem exc_chris_univ_prop [VonNeumannAlgebra 𝒜]
    (φ : NCPMap 𝒜 (H →L[ℂ] H)) (hu : φ 1 = 1) :
    ∃ (𝒦 : Type u) (_ : NormedAddCommGroup 𝒦) (_ : InnerProductSpace ℂ 𝒦)
      (_ : CompleteSpace 𝒦) (ψ : NMIUMap 𝒜 (𝒦 →L[ℂ] 𝒦)) (S₀ : H →L[ℂ] 𝒦),
      Isometry S₀ ∧ (∀ a, φ a = conjOperator S₀ (ψ a)) ∧
      ∀ (𝒜' K' : Type u) (_ : CStarAlgebra 𝒜') (_ : PartialOrder 𝒜')
        (_ : StarOrderedRing 𝒜') (_ : NormedAddCommGroup K')
        (_ : InnerProductSpace ℂ K') (_ : CompleteSpace K')
        (ψ' : NMIUMap 𝒜' (K' →L[ℂ] K')) (m : NMIUMap 𝒜 𝒜') (S : H →L[ℂ] K'),
        Isometry S → (∀ a, φ a = conjOperator S (ψ' (m a))) →
        ∃! p : NMIUMap 𝒜 𝒜' × (𝒦 →L[ℂ] K'),
          (∀ a, p.1 a = m a) ∧ Isometry p.2 ∧ p.2.comp S₀ = S ∧
            ∀ a, ψ a = conjOperator p.2 (ψ' (p.1 a)) :=
  sorry

end NormalStinespring

section EssUniq

variable {H K K' : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

/-- **139XI** (`ess-uniq-pur`, dils.tex:998, Exercise* (Essential uniqueness
of purification)): if `V, W : 𝒦 → ℋ ⊗ 𝒦'` are bounded operators with
`V*(a ⊗ 1)V = φ(a) = W*(a ⊗ 1)W` for all `a ∈ B(ℋ)`, then `V = (1 ⊗ U) W`
for some unitary `U : 𝒦' → 𝒦'`. -/
theorem ess_uniq_pur (φ : NCPMap (H →L[ℂ] H) (K →L[ℂ] K))
    (V W : K →L[ℂ] hilbTensor H K')
    (hV : ∀ a : H →L[ℂ] H, φ a = conjOperator V (tensorCLM a 1))
    (hW : ∀ a : H →L[ℂ] H, φ a = conjOperator W (tensorCLM a 1)) :
    ∃ U : K' →L[ℂ] K',
      (ContinuousLinearMap.adjoint U).comp U = 1 ∧
      U.comp (ContinuousLinearMap.adjoint U) = 1 ∧
      V = (tensorCLM 1 U).comp W :=
  sorry

end EssUniq

/-! ## Parsec 1400: Paschke dilations

**140I** (dils.tex:1027): introduction — nothing to formalize. -/

section Paschke

variable {𝒜 ℬ : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **140II** (`def-paschke`, dils.tex:1049, Definition), the data: a
**Paschke triple** over von Neumann algebras `𝒜`, `ℬ`: a von Neumann
algebra `𝒫` with an nmiu-map `ϱ : 𝒜 → 𝒫` and an ncp-map `h : 𝒫 → ℬ`.
(The von Neumann algebra structure is carried as a proof field `vn` so that
triples can be written down in statements; all algebras live in one
universe `u`, over which the universal property below quantifies.) -/
structure PaschkeTriple (𝒜 ℬ : Type u)
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ] :
    Type (u + 1) where
  /-- The dilating von Neumann algebra `𝒫`. -/
  P : Type u
  [pc : CStarAlgebra P]
  [pp : PartialOrder P]
  [ps : StarOrderedRing P]
  /-- `𝒫` is a von Neumann algebra. -/
  vn : VonNeumannAlgebra P
  /-- The nmiu-part `ϱ : 𝒜 → 𝒫`. -/
  ρ : NMIUMap 𝒜 P
  /-- The ncp-part `h : 𝒫 → ℬ`. -/
  h : NCPMap P ℬ

attribute [instance] PaschkeTriple.pc PaschkeTriple.pp PaschkeTriple.ps

/-- **140II** (`def-paschke`, dils.tex:1049, Definition): a Paschke triple
`(𝒫, ϱ, h)` is a **Paschke dilation** of an ncp-map `φ : 𝒜 → ℬ` when
`φ = h ∘ ϱ` and for every triple `(𝒫', ϱ', h')` with `φ = h' ∘ ϱ'` there is
a unique mediating ncp-map `σ : 𝒫' → 𝒫` with `σ ∘ ϱ' = ϱ` and
`h ∘ σ = h'`. -/
def IsPaschkeDilationOf (D : PaschkeTriple 𝒜 ℬ) (φ : 𝒜 → ℬ) : Prop :=
  (∀ a, D.h (D.ρ a) = φ a) ∧
  ∀ D' : PaschkeTriple 𝒜 ℬ, (∀ a, D'.h (D'.ρ a) = φ a) →
    ∃! σ : NCPMap D'.P D.P,
      (∀ a, σ (D'.ρ a) = D.ρ a) ∧ ∀ c, D.h (σ c) = D'.h c

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **140III** (`stinespring-is-paschke`, dils.tex:1074, Theorem): if
`(𝒦, ϱ, V)` is a minimal normal Stinespring dilation of an ncp-map
`φ : 𝒜 → B(ℋ)`, then `(B(𝒦), ϱ, ad_V)` is a Paschke dilation of `φ`.

**140IV**–**140VI** are the proof — not converted. -/
theorem stinespring_is_paschke [VonNeumannAlgebra 𝒜]
    (φ : NCPMap 𝒜 (H →L[ℂ] H)) (D : StinespringDilation ⇑φ)
    (hmin : D.Minimal) :
    ∃ (vnK : VonNeumannAlgebra (D.K →L[ℂ] D.K))
      (h : NCPMap (D.K →L[ℂ] D.K) (H →L[ℂ] H)),
      (∀ T, h T = conjOperator D.V T) ∧
      IsPaschkeDilationOf ⟨D.K →L[ℂ] D.K, vnK, D.ρ, h⟩ ⇑φ :=
  sorry

/-- **140VIII** (`paschke-unique-up-to-iso`, dils.tex:1176, Lemma): two
Paschke dilations `(𝒫₁, ϱ₁, h₁)`, `(𝒫₂, ϱ₂, h₂)` of the same ncp-map `φ`
are related by a unique nmiu-isomorphism `ϑ : 𝒫₁ → 𝒫₂` with `ϑ ∘ ϱ₁ = ϱ₂`
and `h₂ ∘ ϑ = h₁`.

**140VII** (dils.tex:1157): discussion; **140IX** is the proof — not
converted. -/
theorem paschke_unique_up_to_iso (φ : 𝒜 → ℬ) (D₁ D₂ : PaschkeTriple 𝒜 ℬ)
    (h₁ : IsPaschkeDilationOf D₁ φ) (h₂ : IsPaschkeDilationOf D₂ φ) :
    ∃! ϑ : NMIUMap D₁.P D₂.P,
      Function.Bijective ⇑ϑ ∧ (∀ a, ϑ (D₁.ρ a) = D₂.ρ a) ∧
        ∀ c, D₂.h (ϑ c) = D₁.h c :=
  sorry

/-! ### Infrastructure: the identity ncp-map

`Theses.A.Proc.Measurement` has these (as `isLUB_val_of_isLUB`,
`preservesDirSups_id`, `exists_ncpId`), but `Theses.A.Proc` is not in this
chapter's import path, so the three short proofs are repeated here. -/

/-- The supremum of a nonempty set of self-adjoint elements computed in
`sa(A)` is its supremum in `A`. -/
private theorem isLUB_val_of_isLUB {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {D : Set (selfAdjoint A)}
    {s : selfAdjoint A} (hne : D.Nonempty) (h : IsLUB D s) :
    IsLUB (Subtype.val '' D) ((s : selfAdjoint A) : A) := by
  obtain ⟨d₀, hd₀⟩ := hne
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact Subtype.coe_le_coe.mpr (h.1 hd)
  · have hu0 : ((d₀ : selfAdjoint A) : A) ≤ u := hu ⟨d₀, hd₀, rfl⟩
    have husa : IsSelfAdjoint u := by
      have hd : IsSelfAdjoint (u - ((d₀ : selfAdjoint A) : A)) :=
        IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hu0)
      simpa using hd.add d₀.2
    have hub : (⟨u, husa⟩ : selfAdjoint A) ∈ upperBounds D :=
      fun e he => hu ⟨e, he, rfl⟩
    exact h.2 hub

/-- The identity map is normal. -/
private theorem preservesDirSups_id {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :
    PreservesDirSups (fun a : A => a) := fun _ _ hne _ hlub =>
  isLUB_val_of_isLUB hne hlub

/-- The identity map is an ncp-map. -/
private theorem exists_ncpId (A : Type*) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : ∃ f : NCPMap A A, ∀ a : A, f a = a :=
  ⟨{ toCompletelyPositiveMap :=
       { toLinearMap := LinearMap.id
         map_cstarMatrix_nonneg' := fun _ _ hM => by simpa using hM }
     preservesDirSups' := preservesDirSups_id }, fun _ => rfl⟩

/-- Multiplication by a positive real is an order isomorphism of a
C*-algebra (auxiliary for `exists_ncpSmul`). -/
private theorem smul_le_smul_iff_pos {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {l : ℝ} (hl : 0 < l) (x y : A) :
    (l : ℂ) • x ≤ (l : ℂ) • y ↔ x ≤ y := by
  have main : ∀ (m : ℝ), 0 ≤ m → ∀ u v : A, u ≤ v → (m : ℂ) • u ≤ (m : ℂ) • v := by
    intro m hm u v huv
    have h0 : (0 : A) ≤ (m : ℂ) • (v - u) :=
      cstar_positive_1 _ (sub_nonneg.mpr huv) m hm
    rw [smul_sub] at h0
    rwa [← sub_nonneg]
  refine ⟨fun h => ?_, main l hl.le x y⟩
  have h' := main l⁻¹ (inv_nonneg.mpr hl.le) _ _ h
  rwa [smul_smul, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hl.ne',
    Complex.ofReal_one, one_smul, one_smul] at h'

/-- A positive real multiple of an ncp-map is an ncp-map. -/
private theorem exists_ncpSmul {A B : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : NCPMap A B) {l : ℝ} (hl : 0 < l) :
    ∃ g : NCPMap A B, ∀ a, g a = (l : ℂ) • f a := by
  refine ⟨{ toCompletelyPositiveMap :=
              { toLinearMap := (l : ℂ) • (f.toCompletelyPositiveMap.toLinearMap)
                map_cstarMatrix_nonneg' := fun k M hM => ?_ }
            preservesDirSups' := ?_ }, fun _ => rfl⟩
  · have h1 : (0 : CStarMatrix (Fin k) (Fin k) B)
        ≤ M.map f.toCompletelyPositiveMap.toLinearMap :=
      f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' k M hM
    have h2 : M.map ((l : ℂ) • f.toCompletelyPositiveMap.toLinearMap)
        = (l : ℂ) • M.map f.toCompletelyPositiveMap.toLinearMap := rfl
    rw [h2]
    exact cstar_positive_1 _ h1 l hl.le
  · intro D s hne hdir hlub
    have h := f.preservesDirSups' D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      exact (smul_le_smul_iff_pos hl _ _).mpr (h.1 ⟨d, hd, rfl⟩)
    · intro u hu
      have hu' : (l : ℂ)⁻¹ • u ∈ upperBounds ((fun d : selfAdjoint A => f d) '' D) := by
        rintro _ ⟨d, hd, rfl⟩
        have := hu ⟨d, hd, rfl⟩
        have hle : (l : ℂ) • (f d) ≤ (l : ℂ) • ((l : ℂ)⁻¹ • u) := by
          rwa [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hl.ne'), one_smul]
        exact (smul_le_smul_iff_pos hl _ _).mp hle
      have := h.2 hu'
      have hle : (l : ℂ) • f s ≤ (l : ℂ) • ((l : ℂ)⁻¹ • u) :=
        (smul_le_smul_iff_pos hl _ _).mpr this
      rwa [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hl.ne'), one_smul] at hle

/-- **140X** (`paschke-basics`, dils.tex:1204, Exercise), part 1:
`(ℬ, ϱ, id)` is a Paschke dilation of an nmiu-map `ϱ : 𝒜 → ℬ`. -/
theorem paschke_basics_1 (vnB : VonNeumannAlgebra ℬ) (ϱ : NMIUMap 𝒜 ℬ) :
    ∃ h : NCPMap ℬ ℬ, (∀ b, h b = b) ∧
      IsPaschkeDilationOf ⟨ℬ, vnB, ϱ, h⟩ ⇑ϱ := by
  obtain ⟨idB, hid⟩ := exists_ncpId ℬ
  -- `bsols.tex`, solution `paschke-basics`.1: "clearly `σ ≡ h'` fits the bill"
  refine ⟨idB, hid, fun a => hid _, fun D' hD' => ⟨D'.h, ⟨hD', fun c => hid _⟩, ?_⟩⟩
  rintro σ ⟨-, hσ⟩
  refine DFunLike.ext _ _ fun c => ?_
  have h := hσ c
  rwa [hid] at h

/-- **140X** (`paschke-basics`, dils.tex:1204, Exercise), part 2: if
`(𝒫, ϱ, h)` is a Paschke dilation (of some map), then `(𝒫, id, h)` is a
Paschke dilation of `h`. -/
theorem paschke_basics_2 (φ : 𝒜 → ℬ) (D : PaschkeTriple 𝒜 ℬ)
    (hD : IsPaschkeDilationOf D φ) :
    ∃ ι : NMIUMap D.P D.P, (∀ c, ι c = c) ∧
      IsPaschkeDilationOf ⟨D.P, D.vn, ι, D.h⟩ ⇑D.h :=
  sorry

/-- **140X** (`paschke-basics`, dils.tex:1204, Exercise), part 3: if
`(𝒫ᵢ, ϱᵢ, hᵢ)` is a Paschke dilation of `φᵢ : 𝒜 → ℬᵢ` (i = 1,2), then
`(𝒫₁ ⊕ 𝒫₂, ⟨ϱ₁, ϱ₂⟩, h₁ ⊕ h₂)` is a Paschke dilation of `⟨φ₁, φ₂⟩ : 𝒜 →
ℬ₁ ⊕ ℬ₂`.  (The direct sums are represented abstractly: von Neumann
algebras `ℬp`, `𝒫p` whose nmiu projections `πᵢ`, `pᵢ` pair bijectively
into the set-theoretic product, avoiding instance diamonds on product
types.) -/
theorem paschke_basics_3 {ℬ₁ ℬ₂ ℬp : Type u}
    [CStarAlgebra ℬ₁] [PartialOrder ℬ₁] [StarOrderedRing ℬ₁]
    [CStarAlgebra ℬ₂] [PartialOrder ℬ₂] [StarOrderedRing ℬ₂]
    [CStarAlgebra ℬp] [PartialOrder ℬp] [StarOrderedRing ℬp]
    (φ₁ : 𝒜 → ℬ₁) (φ₂ : 𝒜 → ℬ₂) (φ : 𝒜 → ℬp)
    (D₁ : PaschkeTriple 𝒜 ℬ₁) (D₂ : PaschkeTriple 𝒜 ℬ₂)
    (D : PaschkeTriple 𝒜 ℬp)
    (h₁ : IsPaschkeDilationOf D₁ φ₁) (h₂ : IsPaschkeDilationOf D₂ φ₂)
    (π₁ : NMIUMap ℬp ℬ₁) (π₂ : NMIUMap ℬp ℬ₂)
    (hπ : Function.Bijective fun b : ℬp => (π₁ b, π₂ b))
    (p₁ : NMIUMap D.P D₁.P) (p₂ : NMIUMap D.P D₂.P)
    (hp : Function.Bijective fun c : D.P => (p₁ c, p₂ c))
    (hφ : ∀ a, π₁ (φ a) = φ₁ a ∧ π₂ (φ a) = φ₂ a)
    (hρ : ∀ a, p₁ (D.ρ a) = D₁.ρ a ∧ p₂ (D.ρ a) = D₂.ρ a)
    (hh : ∀ c, π₁ (D.h c) = D₁.h (p₁ c) ∧ π₂ (D.h c) = D₂.h (p₂ c)) :
    IsPaschkeDilationOf D φ :=
  sorry

/-- **140X** (`paschke-basics`, dils.tex:1204, Exercise), part 4: if
`(𝒫, ϱ, h)` is a Paschke dilation of `φ` and `λ > 0`, then `(𝒫, ϱ, λh)` is
a Paschke dilation of `λφ`.

**140XI** (dils.tex:1236, Examples): forward references to
`paschke-tensor`, `paschke-corner`, `paschke-pure`,
`dils-filter-basics-exercise` — not converted here. -/
theorem paschke_basics_4 (φ : 𝒜 → ℬ) (D : PaschkeTriple 𝒜 ℬ)
    (hD : IsPaschkeDilationOf D φ) (l : ℝ) (hl : 0 < l) :
    ∃ h' : NCPMap D.P ℬ, (∀ c, h' c = (l : ℂ) • D.h c) ∧
      IsPaschkeDilationOf ⟨D.P, D.vn, D.ρ, h'⟩ (fun a => (l : ℂ) • φ a) := by
  -- `bsols.tex`, solution `paschke-basics`.4
  have hlne : ((l : ℂ)) ≠ 0 := by exact_mod_cast hl.ne'
  obtain ⟨h', hh'⟩ := exists_ncpSmul D.h hl
  refine ⟨h', hh', fun a => by rw [hh', hD.1 a], fun D' hD' => ?_⟩
  -- "then `λ⁻¹ h' ∘ ϱ' = φ`", so the original universal property applies
  obtain ⟨k, hk⟩ := exists_ncpSmul D'.h (inv_pos.mpr hl)
  have hk' : ∀ c, D'.h c = (l : ℂ) • k c := by
    intro c
    rw [hk, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hlne, one_smul]
  have hD'' : ∀ a, k (D'.ρ a) = φ a := by
    intro a
    rw [hk, hD' a, smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ hlne, one_smul]
  obtain ⟨σ, ⟨hσ1, hσ2⟩, hσu⟩ :=
    hD.2 ⟨D'.P, D'.vn, D'.ρ, k⟩ hD''
  refine ⟨σ, ⟨hσ1, fun c => ?_⟩, ?_⟩
  · rw [hh', hσ2 c, ← hk' c]
  · rintro τ ⟨hτ1, hτ2⟩
    refine hσu τ ⟨hτ1, fun c => ?_⟩
    have h := hτ2 c
    rw [hh'] at h
    change D.h (τ c) = k c
    rw [hk, ← h, smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ hlne, one_smul]

end Paschke

end Theses.B.Dils
