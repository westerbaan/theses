/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 3527–4081.

  parsec 1540:  existence of the Paschke dilation via 𝒜 ⊗_φ ℬ
  parsec 1550:  KSGNS
  parsec 1560:  injectivity of the Paschke representation
  parsec 1570:  the order correspondence [0,1]_{ϱ(𝒜)'} ≅ [0,φ]_ncp

Statements only; every proof is `sorry`.  All von Neumann algebras live in
one universe `u` (cf. `Stinespring.lean` for `PaschkeTriple` and
`IsPaschkeDilationOf`); the self-dual Hilbert module `𝒜 ⊗_φ ℬ` and the
algebra `𝒷ᵃ(X)` are as in `SelfDualCompletion.lean`, in the mirrored
(left-action) convention of `HilbertModules.lean`; in particular the inner
product on `𝒜 ⊗_φ ℬ` reads `⟨a ⊗ b, α ⊗ β⟩ = β φ(α* a) b*`, the mirror
image of the thesis's `[a ⊗ b, α ⊗ β] = b* φ(a* α) β`.
-/
import Theses.B.Dils.Stinespring
import Theses.B.Dils.SelfDualCompletion

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra WithCStarModule
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u

namespace Theses.B.Dils

/-! ## Parsec 1540: existence of Paschke dilations

**154I** (dils.tex:3529): introduction — nothing to formalize. -/

section Existence

variable {𝒜 ℬ : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **154II** (`phi-compatible-paschke`, dils.tex:3541, Definition): for an
ncp-map `φ : 𝒜 → ℬ` between von Neumann algebras, a complex bilinear map
`T : 𝒜 × ℬ → X` into a (self-dual) Hilbert ℬ-module is **φ-compatible**
when `T(a, b₁b₂) = T(a, b₁)b₂` (mirrored: `c • T a b = T a (c * b)`) and
for some `r > 0`

  `‖∑ᵢ T(aᵢ, bᵢ)‖² ≤ r ‖∑_{i,j} bᵢ* φ(aᵢ* aⱼ) bⱼ‖`. -/
structure PhiCompatible (φ : 𝒜 → ℬ) {X : Type u} [NormedAddCommGroup X]
    [Module ℂ X] [SMul ℬ X] [CStarModule ℬ X] (T : 𝒜 → ℬ → X) :
    Prop where
  add_left : ∀ (a a' : 𝒜) (b : ℬ), T (a + a') b = T a b + T a' b
  add_right : ∀ (a : 𝒜) (b b' : ℬ), T a (b + b') = T a b + T a b'
  smul_complex : ∀ (c : ℂ) (a : 𝒜) (b : ℬ), T (c • a) b = c • T a b
  smul_action : ∀ (a : 𝒜) (b c : ℬ), c • T a b = T a (c * b)
  bound : ∃ r > (0 : ℝ), ∀ (n : ℕ) (a : Fin n → 𝒜) (b : Fin n → ℬ),
    ‖∑ i, T (a i) (b i)‖ ^ 2 ≤
      r * ‖∑ i, ∑ j, star (b i) * φ (star (a i) * a j) * b j‖

/-- **154III** (`existence-paschke`, dils.tex:3558, Theorem), the data: the
self-dual Hilbert ℬ-module `𝒜 ⊗_φ ℬ` with its φ-compatible bilinear map
`⊗`, the nmiu-map `ϱ : 𝒜 → ℬᵃ(𝒜 ⊗_φ ℬ)` fixed by
`ϱ(a₀)(a ⊗ b) = (a₀a) ⊗ b` and the ncp-map `h(T) = ⟨1 ⊗ 1, T(1 ⊗ 1)⟩`,
together with the universal property of part 1. -/
structure PaschkeModule (φ : NCPMap 𝒜 ℬ) : Type (u + 1) where
  /-- The carrier of `𝒜 ⊗_φ ℬ`. -/
  X : Type u
  [nacg : NormedAddCommGroup X]
  [mod : NormedSpace ℂ X]
  [smul : SMul ℬ X]
  [cstarMod : CStarModule ℬ X]
  [complete : CompleteSpace X]
  /-- `𝒜 ⊗_φ ℬ` is self dual. -/
  selfDual : SelfDual ℬ X
  /-- The bilinear map `⊗ : 𝒜 × ℬ → 𝒜 ⊗_φ ℬ`. -/
  tprod : 𝒜 → ℬ → X
  /-- `⊗` is φ-compatible (part 1). -/
  compat : PhiCompatible ⇑φ tprod
  /-- The inner product is fixed on elementary tensors (mirrored):
  `⟨a ⊗ b, α ⊗ β⟩ = β φ(α* a) b*`. -/
  inner_tprod : ∀ (a a' : 𝒜) (b b' : ℬ),
    inner ℬ (tprod a b) (tprod a' b') = b' * φ (star a' * a) * star b
  /-- Part 1, universal property: every φ-compatible bilinear map into a
  self-dual Hilbert ℬ-module factors uniquely through `⊗` by a bounded
  module map. -/
  univ : ∀ (Y : Type u) (_ : NormedAddCommGroup Y) (_ : Module ℂ Y)
    (_ : SMul ℬ Y) (_ : CStarModule ℬ Y) (_ : CompleteSpace Y),
    SelfDual ℬ Y → ∀ T : 𝒜 → ℬ → Y, PhiCompatible ⇑φ T →
      ∃! T' : X → Y,
        (∃ C : ℝ, IsBoundedModuleMap (cstarBInner ℬ X) (cstarBInner ℬ Y)
          C T') ∧ ∀ a b, T' (tprod a b) = T a b
  /-- Part 2: the nmiu-map `ϱ : 𝒜 → ℬᵃ(𝒜 ⊗_φ ℬ)`. -/
  ρ : NMIUMap 𝒜 (Ba ℬ X)
  /-- `ϱ(a₀)(a ⊗ b) = (a₀ a) ⊗ b`. -/
  ρ_tprod : ∀ (a₀ a : 𝒜) (b : ℬ), (ρ a₀).1 (tprod a b) = tprod (a₀ * a) b
  /-- Part 3: the ncp-map `h : ℬᵃ(𝒜 ⊗_φ ℬ) → ℬ`. -/
  h : NCPMap (Ba ℬ X) ℬ
  /-- `h(T) = ⟨1 ⊗ 1, T (1 ⊗ 1)⟩`. -/
  h_def : ∀ T : Ba ℬ X, h T = inner ℬ (tprod 1 1) (T.1 (tprod 1 1))

attribute [instance] PaschkeModule.nacg PaschkeModule.mod PaschkeModule.smul
  PaschkeModule.cstarMod PaschkeModule.complete

/-- **154III** (`existence-paschke`, dils.tex:3558, Theorem), parts 1–3:
the module `𝒜 ⊗_φ ℬ`, the representation `ϱ` and the vector state `h`
exist. -/
theorem existence_paschke [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) : Nonempty (PaschkeModule φ) :=
  sorry

/-- An adjointable bounded operator on a Hilbert 𝒷-module is a bounded
module map in the sense of **144IV** (`IsBoundedModuleMap`). -/
private theorem ba_isBoundedModuleMap {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X] (T : Ba ℬ X) :
    ∃ C : ℝ, IsBoundedModuleMap (cstarBInner ℬ X) (cstarBInner ℬ X) C ⇑T.1 := by
  obtain ⟨-, -, hmod⟩ := moduleAdjointable_linear (𝒜 := ℬ) ⇑T.1 T.2
  refine ⟨‖T.1‖ + 1, { add := fun x y => map_add T.1 x y
                       smul_complex := fun c x => map_smul T.1 c x
                       smul := hmod
                       bound := fun x => ?_ }⟩
  change Real.sqrt ‖(inner ℬ (T.1 x) (T.1 x) : ℬ)‖
    ≤ (‖T.1‖ + 1) * Real.sqrt ‖(inner ℬ x x : ℬ)‖
  rw [← CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ),
    ← CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ)]
  have h := T.1.le_opNorm x
  have h0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  nlinarith

set_option maxHeartbeats 1000000 in
-- the φ-compatibility bound is a long chain of `Finset` rewrites
/-- **154III** (`existence-paschke`, dils.tex:3558, Theorem), part 2,
uniqueness clause: for each `a₀ ∈ 𝒜` the operator `ϱ(a₀)` is the unique
adjointable operator with `ϱ(a₀)(a ⊗ b) = (a₀a) ⊗ b`. -/
theorem existence_paschke_2 [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ) (a₀ : 𝒜) :
    ∃! T : Ba ℬ M.X, ∀ (a : 𝒜) (b : ℬ),
      T.1 (M.tprod a b) = M.tprod (a₀ * a) b := by
  classical
  set ψ : 𝒜 →ₗ[ℂ] ℬ := φ.toCompletelyPositiveMap.toLinearMap with hψdef
  have hψ : ⇑φ = ⇑ψ := rfl
  have hcp : IsCompletelyPositiveMap ψ :=
    ((cp_iff _).out 1 0).mp fun N A hA =>
      φ.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N A hA
  -- the shifted bilinear map `(a, b) ↦ (a₀a) ⊗ b` is φ-compatible: only the
  -- bound needs an argument, and it is complete positivity of `φ` at the two
  -- families `(a₀aᵢ)` and `(caᵢ)`, where `c* c = K - a₀* a₀` for
  -- `K = ‖a₀‖² + 1`; adding the two gives `S₁ + S₂ = K · S₀`, so
  -- `0 ≤ S₁ ≤ K · S₀`.
  have hcompat : PhiCompatible ⇑φ (fun a b => M.tprod (a₀ * a) b) := by
    obtain ⟨r, hr0, hr⟩ := M.compat.bound
    refine { add_left := fun a a' b => by
               rw [mul_add]; exact M.compat.add_left _ _ _
             add_right := fun a b b' => M.compat.add_right _ _ _
             smul_complex := fun c a b => by
               rw [mul_smul_comm]; exact M.compat.smul_complex _ _ _
             smul_action := fun a b c => M.compat.smul_action _ _ _
             bound := ⟨r * (‖a₀‖ ^ 2 + 1), by positivity, fun n a b => ?_⟩ }
    set K : ℝ := ‖a₀‖ ^ 2 + 1 with hK
    have hK0 : (0 : ℝ) ≤ K := by positivity
    have hcast : ∀ t : ℝ, algebraMap ℝ 𝒜 t = ((t : ℂ)) • (1 : 𝒜) := by
      intro t
      rw [IsScalarTower.algebraMap_apply ℝ ℂ 𝒜, Algebra.algebraMap_eq_smul_one]
      norm_num
    have hnorm2 : ‖star a₀ * a₀‖ = ‖a₀‖ ^ 2 := by
      rw [CStarRing.norm_star_mul_self]; ring
    have hle : star a₀ * a₀ ≤ ((K : ℝ) : ℂ) • (1 : 𝒜) := by
      have h1 := (IsSelfAdjoint.star_mul_self a₀).le_algebraMap_norm_self
      rw [hcast] at h1
      refine h1.trans ?_
      rw [← sub_nonneg, ← sub_smul]
      have h2 : ((K : ℝ) : ℂ) - ((‖star a₀ * a₀‖ : ℝ) : ℂ) = 1 := by
        rw [hnorm2, hK]; push_cast; ring
      rw [h2, one_smul]
      exact zero_le_one
    set c : 𝒜 := CFC.sqrt (((K : ℝ) : ℂ) • (1 : 𝒜) - star a₀ * a₀) with hcdef
    have hcc : star c * c = ((K : ℝ) : ℂ) • (1 : 𝒜) - star a₀ * a₀ := by
      have h0 : (0 : 𝒜) ≤ ((K : ℝ) : ℂ) • (1 : 𝒜) - star a₀ * a₀ := sub_nonneg.mpr hle
      have hsa : star c = c := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
      rw [hsa, hcdef, CFC.sqrt_mul_sqrt_self _ h0]
    -- the three conjugated sums
    set S0 : ℬ := ∑ i, ∑ j, star (b i) * ψ (star (a i) * a j) * b j with hS0def
    set S1 : ℬ := ∑ i, ∑ j, star (b i) * ψ (star (a₀ * a i) * (a₀ * a j)) * b j
      with hS1def
    set S2 : ℬ := ∑ i, ∑ j, star (b i) * ψ (star (c * a i) * (c * a j)) * b j
      with hS2def
    have hS1nn : (0 : ℬ) ≤ S1 := hcp n (fun i => a₀ * a i) b
    have hS2nn : (0 : ℬ) ≤ S2 := hcp n (fun i => c * a i) b
    have hpoint : ∀ i j : Fin n,
        star (b i) * ψ (star (a₀ * a i) * (a₀ * a j)) * b j
          + star (b i) * ψ (star (c * a i) * (c * a j)) * b j
        = ((K : ℝ) : ℂ) • (star (b i) * ψ (star (a i) * a j) * b j) := by
      intro i j
      have hsum : star a₀ * a₀ + star c * c = ((K : ℝ) : ℂ) • (1 : 𝒜) := by
        rw [hcc]; abel
      have h1 : star (a₀ * a i) * (a₀ * a j) + star (c * a i) * (c * a j)
          = ((K : ℝ) : ℂ) • (star (a i) * a j) := by
        calc star (a₀ * a i) * (a₀ * a j) + star (c * a i) * (c * a j)
            = star (a i) * (star a₀ * a₀ + star c * c) * a j := by
              simp only [star_mul]; noncomm_ring
          _ = star (a i) * (((K : ℝ) : ℂ) • (1 : 𝒜)) * a j := by rw [hsum]
          _ = ((K : ℝ) : ℂ) • (star (a i) * a j) := by
              rw [mul_smul_comm, smul_mul_assoc, mul_one]
      rw [← add_mul, ← mul_add, ← map_add ψ, h1, map_smul, mul_smul_comm,
        smul_mul_assoc]
    have hSum : S1 + S2 = ((K : ℝ) : ℂ) • S0 := by
      rw [hS0def, hS1def, hS2def, Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => hpoint i j
    have hS1le : S1 ≤ ((K : ℝ) : ℂ) • S0 := by
      rw [← hSum]
      simpa using add_le_add_left hS2nn S1
    have hnormS1 : ‖S1‖ ≤ K * ‖S0‖ := by
      have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le hS1nn hS1le
      rwa [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK0] at h
    have hkey := hr n (fun i => a₀ * a i) b
    simp only [← hψ] at hS0def hS1def
    calc ‖∑ i, M.tprod (a₀ * a i) (b i)‖ ^ 2
        ≤ r * ‖S1‖ := by rw [hS1def]; simpa [hψ] using hkey
      _ ≤ r * (K * ‖S0‖) := mul_le_mul_of_nonneg_left hnormS1 hr0.le
      _ = r * K * ‖S0‖ := by ring
      _ = r * (‖a₀‖ ^ 2 + 1)
            * ‖∑ i, ∑ j, star (b i) * φ (star (a i) * a j) * b j‖ := by
          rw [hS0def, hK]
  -- part 1 (the universal property) applied to it
  obtain ⟨T', -, hT'uniq⟩ :=
    M.univ M.X inferInstance inferInstance inferInstance inferInstance inferInstance
      M.selfDual _ hcompat
  refine ⟨M.ρ a₀, fun a b => M.ρ_tprod a₀ a b, fun T hT => ?_⟩
  have h1 : ⇑T.1 = T' := hT'uniq _ ⟨ba_isBoundedModuleMap T, fun a b => hT a b⟩
  have h2 : ⇑(M.ρ a₀).1 = T' :=
    hT'uniq _ ⟨ba_isBoundedModuleMap _, fun a b => M.ρ_tprod a₀ a b⟩
  exact Subtype.ext (DFunLike.coe_injective (h1.trans h2.symm))

/-- **154III** (`existence-paschke`, dils.tex:3558, Theorem), part 4
(`paschke-spatial`): universal property of `(ϱ, 1 ⊗ 1)`: for every
nmiu-map `ϱ' : 𝒜 → ℬᵃ(Y)` into the operators on a self-dual Hilbert
ℬ-module `Y` and every `e ∈ Y` with `φ = ⟨e, ϱ'(·) e⟩`, there is a unique
inner-product-preserving module map `S : 𝒜 ⊗_φ ℬ → Y` with
`S(1 ⊗ 1) = e` and `S ϱ(a) = ϱ'(a) S` (equivalently `ad_S ∘ ϱ' = ϱ`). -/
theorem existence_paschke_4 [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ) {Y : Type u}
    [NormedAddCommGroup Y] [Module ℂ Y] [SMul ℬ Y] [CStarModule ℬ Y]
    [CompleteSpace Y] (hY : SelfDual ℬ Y) (e : Y)
    (ϱ' : NMIUMap 𝒜 (Ba ℬ Y))
    (hφ : ∀ a : 𝒜, φ a = inner ℬ e ((ϱ' a).1 e)) :
    ∃! S : M.X → Y,
      (∃ C : ℝ, IsBoundedModuleMap (cstarBInner ℬ M.X) (cstarBInner ℬ Y)
        C S) ∧
      (∀ x y : M.X, inner ℬ (S x) (S y) = inner ℬ x y) ∧
      S (M.tprod 1 1) = e ∧
      ∀ (a : 𝒜) (x : M.X), S ((M.ρ a).1 x) = (ϱ' a).1 (S x) :=
  sorry

/-- **154III** (`existence-paschke`, dils.tex:3558, Theorem), part 5:
`(ℬᵃ(𝒜 ⊗_φ ℬ), ϱ, h)` is a Paschke dilation of `φ`.  (In particular every
ncp-map between von Neumann algebras has a Paschke dilation.)

**154IV**–**154X** are the proof (including **154VIII**
`paschke-uniqueness` and **154IX** `paschke-spatial` as proof steps) — not
converted separately. -/
theorem existence_paschke_5 [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ) :
    IsPaschkeDilationOf
      ⟨Ba ℬ M.X, ba_vonNeumannAlgebra M.selfDual, M.ρ, M.h⟩ ⇑φ :=
  sorry

end Existence

/-! ## Parsec 1550: KSGNS

**155I**, **155III** (dils.tex:3841, 3859): discussion — nothing to
formalize. -/

/-- **155II** (dils.tex:3849, Theorem (KSGNS)): for a cp-map
`φ : 𝒜 → ℬᵃ(X)`, with `𝒜`, `ℬ` C*-algebras and `X` a Hilbert ℬ-module,
there are a Hilbert ℬ-module `Y`, an miu-map `ϱ : 𝒜 → ℬᵃ(Y)` and an
adjointable ℬ-linear `T : X → Y` with `φ = ad_T ∘ ϱ`, i.e.
`φ(a) = T* ϱ(a) T`. -/
theorem ksgns {𝒜 ℬ : Type u}
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    {X : Type u} [NormedAddCommGroup X] [Module ℂ X] [SMul ℬ X]
    [CStarModule ℬ X] [CompleteSpace X]
    (φ : 𝒜 →ₗ[ℂ] Ba ℬ X) (hφ : IsCompletelyPositiveMap φ) :
    ∃ (Y : Type u) (_ : NormedAddCommGroup Y) (_ : Module ℂ Y)
      (_ : SMul ℬ Y) (_ : CStarModule ℬ Y) (_ : CompleteSpace Y)
      (ϱ : MIUMap 𝒜 (Ba ℬ Y)) (T : X →L[ℂ] Y) (T' : Y →L[ℂ] X),
      ModuleAdjointTo ℬ ⇑T ⇑T' ∧
      ∀ a : 𝒜, (φ a).1 = T'.comp (((ϱ a).1).comp T) :=
  sorry

/-! ## Parsec 1560: injectivity of the Paschke representation

**156I** (dils.tex:3868): introduction; **156III** is the proof — not
converted. -/

section Injective

variable {𝒜 ℬ : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **156II** (`paschke-injective`, dils.tex:3875, Theorem), carrier form:
for an ncp-map `φ : 𝒜 → ℬ` with Paschke dilation `(𝒫, ϱ, h)` we have
`⌈ϱ⌉ = ⌈⌈φ⌉⌉` (the carrier of `ϱ` is the central carrier of `φ`); stated
via the characterization used in the proof: for every projection
`p ∈ 𝒜`, `ϱ(p) = 0` iff `φ(a* p a) = 0` for all `a ∈ 𝒜`. -/
theorem paschke_injective_carrier [VonNeumannAlgebra 𝒜]
    (φ : NCPMap 𝒜 ℬ) (D : PaschkeTriple 𝒜 ℬ)
    (hD : IsPaschkeDilationOf D ⇑φ) (p : 𝒜) (hp : IsStarProjection p) :
    D.ρ p = 0 ↔ ∀ a : 𝒜, φ (star a * p * a) = 0 :=
  sorry

/-- **156II** (`paschke-injective`, dils.tex:3875, Theorem): the Paschke
representation `ϱ` is injective if and only if `φ` maps no non-zero
central projection to zero (`⌈⌈φ⌉⌉ = 1`). -/
theorem paschke_injective [VonNeumannAlgebra 𝒜] (φ : NCPMap 𝒜 ℬ)
    (D : PaschkeTriple 𝒜 ℬ) (hD : IsPaschkeDilationOf D ⇑φ) :
    Function.Injective ⇑D.ρ ↔
      ∀ z : 𝒜, IsStarProjection z → IsCentral 𝒜 z → φ z = 0 → z = 0 :=
  sorry

end Injective

/-! ## Parsec 1570: the order correspondence

**157I** (dils.tex:3918): introduction; **157IIIa**, **157V**–**157X** are
discussion and the proof of **157IV** — not converted. -/

section Correspondence

variable {𝒜 ℬ : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **157II** (dils.tex:3927, Definition): for maps `ψ, χ : 𝒜 → ℬ`, `ψ` is
**ncp-below** `χ` (`ψ ≤_ncp χ`) when `χ - ψ` is an ncp-map. -/
def NCPLe (ψ χ : 𝒜 → ℬ) : Prop :=
  ∃ δ : NCPMap 𝒜 ℬ, ∀ a, χ a = ψ a + δ a

/-- **157II** (dils.tex:3927, Definition), continued: the interval
`[0, φ]_ncp` of maps `ψ` with `0 ≤_ncp ψ ≤_ncp φ`. -/
def ncpInterval (φ : 𝒜 → ℬ) : Set (𝒜 → ℬ) :=
  {ψ | NCPLe (fun _ => 0) ψ ∧ NCPLe ψ φ}

/-- **157III** (dils.tex:3940, Definition): for an ncp-map `φ` with Paschke
dilation `(𝒫, ϱ, h)` and `t` in the commutant of `ϱ(𝒜)`, the map
`φ_t = h(t ϱ(·)) : 𝒜 → ℬ`. -/
noncomputable def phiT (D : PaschkeTriple 𝒜 ℬ) (t : D.P) : 𝒜 → ℬ :=
  fun a => D.h (t * D.ρ a)

/-- **157IV** (`paschke-correspondence`, dils.tex:3950, Theorem), part 1:
for `t` in `[0,1]` of the commutant of `ϱ(𝒜)`, the map `φ_t` lies in
`[0, φ]_ncp`. -/
theorem paschke_correspondence_mem [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ) (D : PaschkeTriple 𝒜 ℬ)
    (hD : IsPaschkeDilationOf D ⇑φ) (t : D.P)
    (ht : t ∈ commutant D.P (Set.range ⇑D.ρ)) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    phiT D t ∈ ncpInterval ⇑φ :=
  sorry

/-- **157IV** (`paschke-correspondence`, dils.tex:3950, Theorem), part 2:
`t ↦ φ_t` is an order embedding of `[0,1]_{ϱ(𝒜)'}` into `[0,φ]_ncp`: for
`s, t` in the positive unit interval of the commutant,
`φ_t ≤_ncp φ_s` iff `t ≤ s` (in particular `t ↦ φ_t` is injective and
linear). -/
theorem paschke_correspondence_embedding [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ) (D : PaschkeTriple 𝒜 ℬ)
    (hD : IsPaschkeDilationOf D ⇑φ) (s t : D.P)
    (hs : s ∈ commutant D.P (Set.range ⇑D.ρ)) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht : t ∈ commutant D.P (Set.range ⇑D.ρ)) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    NCPLe (phiT D t) (phiT D s) ↔ t ≤ s :=
  sorry

/-- **157IV** (`paschke-correspondence`, dils.tex:3950, Theorem), part 3:
`t ↦ φ_t` maps `[0,1]_{ϱ(𝒜)'}` *onto* `[0,φ]_ncp`. -/
theorem paschke_correspondence_surjective [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ) (D : PaschkeTriple 𝒜 ℬ)
    (hD : IsPaschkeDilationOf D ⇑φ) (ψ : 𝒜 → ℬ)
    (hψ : ψ ∈ ncpInterval ⇑φ) :
    ∃ t : D.P, t ∈ commutant D.P (Set.range ⇑D.ρ) ∧ 0 ≤ t ∧ t ≤ 1 ∧
      phiT D t = ψ :=
  sorry

end Correspondence

end Theses.B.Dils
