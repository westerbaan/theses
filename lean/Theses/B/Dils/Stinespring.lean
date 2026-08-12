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
      (∀ v w : V, (⟪η v, η w⟫ : ℂ) = B v w) ∧ DenseRange η :=
  sorry

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
`TensorProduct.map`.  (Definition deferred; only its characterizing property
`tensorCLM_mk` below is used.) -/
noncomputable def tensorCLM (a : H →L[ℂ] H) (b : K →L[ℂ] K) :
    hilbTensor H K →L[ℂ] hilbTensor H K :=
  sorry

/-- Characterizing property of `tensorCLM`:
`(a ⊗ b) (x ⊗ y) = (a x) ⊗ (b y)`. -/
theorem tensorCLM_mk (a : H →L[ℂ] H) (b : K →L[ℂ] K) (x : H) (y : K) :
    tensorCLM a b (hilbTensorMk x y) = hilbTensorMk (a x) (b y) :=
  sorry

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
    σ (ϱ' a₁ * c * ϱ' a₂) = ϱ a₁ * σ c * ϱ a₂ :=
  sorry

/-- **139V** (`dils-univ-stinespring`, dils.tex:863, Proposition): if
`(𝒦, ϱ, V)` and `(𝒦', ϱ', V')` are normal Stinespring dilations of the same
ncp-map `φ : 𝒜 → B(ℋ)` and `(𝒦, ϱ, V)` is minimal, then there is a unique
isometry `S : 𝒦 → 𝒦'` with `SV = V'` and `ϱ = ad_S ∘ ϱ'`.

**139VI**–**139VIII** are the proof — not converted. -/
theorem dils_univ_stinespring (φ : NCPMap 𝒜 (H →L[ℂ] H))
    (D D' : StinespringDilation ⇑φ) (hmin : D.Minimal) :
    ∃! S : D.K →L[ℂ] D'.K,
      Isometry S ∧ S.comp D.V = D'.V ∧
        ∀ a : 𝒜, D.ρ a = conjOperator S (D'.ρ a) :=
  sorry

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

/-- **140X** (`paschke-basics`, dils.tex:1204, Exercise), part 1:
`(ℬ, ϱ, id)` is a Paschke dilation of an nmiu-map `ϱ : 𝒜 → ℬ`. -/
theorem paschke_basics_1 (vnB : VonNeumannAlgebra ℬ) (ϱ : NMIUMap 𝒜 ℬ) :
    ∃ h : NCPMap ℬ ℬ, (∀ b, h b = b) ∧
      IsPaschkeDilationOf ⟨ℬ, vnB, ϱ, h⟩ ⇑ϱ :=
  sorry

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
      IsPaschkeDilationOf ⟨D.P, D.vn, D.ρ, h'⟩ (fun a => (l : ℂ) • φ a) :=
  sorry

end Paschke

end Theses.B.Dils
