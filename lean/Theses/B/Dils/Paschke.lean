/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 3527–4081.

  parsec 1540:  existence of the Paschke dilation via 𝒜 ⊗_φ ℬ
  parsec 1550:  KSGNS
  parsec 1560:  injectivity of the Paschke representation
  parsec 1570:  the order correspondence [0,1]_{ϱ(𝒜)'} ≅ [0,φ]_ncp

All von Neumann algebras live in one universe `u` (cf. `Stinespring.lean`
for `PaschkeTriple` and `IsPaschkeDilationOf`); the self-dual Hilbert
module `𝒜 ⊗_φ ℬ` and the algebra `𝒷ᵃ(X)` are as in
`SelfDualCompletion.lean`, in the mirrored (left-action) convention of
`HilbertModules.lean`.

**Convention (mirroring).**  Mathlib's `CStarModule ℬ X` is a *left*
ℬ-module with `⟨x, b·y⟩ = b⟨x,y⟩` (for `X = ℬ`: `b • x = bx`,
`⟨x,y⟩ = y x*`).  It is the **conjugate module** of the thesis's right
Hilbert ℬ-modules: the mirror of a right module `(X, ·, [·,·])` is `X` with

  `b • x := x·b*`,  `⟨x,y⟩ := [y,x]`,  and  `c ·̄ x := c̄ x`

— the ℂ-action is *conjugated* too, and that is the part that was missed
until session 15.  (It has to be: `[·,·]` is conjugate-linear in its first
argument and so is Mathlib's `⟨·,·⟩`, so `⟨x,y⟩ = [y,x]` can only be
ℂ-sesquilinear for the conjugated action.)

Consequently the mirror of the thesis's `⊗ : 𝒜 × ℬ → 𝒜 ⊗_φ ℬ` carries a
`star` in **both** arguments,

  `tprod a b  =  (a* ⊗ b*)_thesis`,

which is exactly what makes `tprod` ℂ-linear in `a`
(`PhiCompatible.smul_complex`) and `c • tprod a b = tprod a (c*b)`
(`PhiCompatible.smul_action`).  Substituting `a ↦ a*`, `b ↦ b*` in the
thesis's `[a ⊗ b, α ⊗ β] = b* φ(a* α) β` and in its φ-compatibility bound
gives the two clauses used below:

  `⟨a ⊗ b, a' ⊗ b'⟩ = b' φ(a' a*) b*`,
  `‖∑ᵢ T(aᵢ,bᵢ)‖² ≤ r ‖∑_{i,j} bᵢ φ(aᵢ aⱼ*) bⱼ*‖`.

**Convention (the opposite algebra).**  Because the ℂ-action of the mirror
module is conjugated, so is the ℂ-action of `End(X)`, and the ℂ-*linear*
rendering of the thesis's `ϱ : 𝒜 → 𝒷ᵃ(𝒜 ⊗_φ ℬ)` is the ∗-preserving
**anti**-homomorphism `a₀ ↦ (a ⊗ b ↦ (a a₀) ⊗ b)` (`ρ_tprod`), i.e. an
nmiu-map

  `ρ : 𝒜 → 𝒷ᵃ(𝒜 ⊗_φ ℬ)ᵐᵒᵖ`,

and correspondingly `h : 𝒷ᵃ(𝒜 ⊗_φ ℬ)ᵐᵒᵖ → ℬ`, `h T = ⟨1 ⊗ 1, T(1 ⊗ 1)⟩`.
The `ᵐᵒᵖ` is not cosmetic and cannot be dropped: `𝒜 ≅ 𝒜ᵒᵖ` fails for
general von Neumann algebras (Connes), and in the mirrored convention it is
the *opposite* algebra on which the vector state is completely positive —
for `X = ℬ` one has `𝒷ᵃ(ℬ) = {R_t} ≅ ℬᵐᵒᵖ` with `h(R_t) = t`, so
`h : 𝒷ᵃ(ℬ) → ℬ` is `unop`, which is the transpose on `M₂` and hence
positive but *not* completely positive, while `h : 𝒷ᵃ(ℬ)ᵐᵒᵖ → ℬ` is a
∗-isomorphism.  With these fields `h (ρ a) = φ a` holds on the nose
(`paschkeModule_h_ρ`), so `IsPaschkeDilationOf` (`Stinespring.lean:1179`),
which asks for `h (ρ a) = φ a` with no `star`, is correct as it stands
(ruling of the author, QUESTIONS **D2**).

Two earlier renderings are recorded as machine-checked negative results:
`paschke_inner_conj_forces_zero` (the inner product `b' φ(a'* a) b*`,
i.e. no `star` on the `𝒜`-argument of `tprod`, forces `φ = 0`) and
`paschke_rho_forces_cyclic` (the inner product below together with a `ρ`
into `𝒷ᵃ(X)` rather than `𝒷ᵃ(X)ᵐᵒᵖ` forces `φ` to be cyclic, which fails
for `φ = id` on `M₂`).  Both left `PaschkeModule` uninhabited.  See
`PROVING-LOG.md`, sessions 14–16, and QUESTIONS **D2**.
-/
import Theses.B.Dils.Stinespring
import Theses.B.Dils.SelfDualCompletion

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra WithCStarModule
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u

namespace Theses.B.Dils

/-! ### The opposite of a von Neumann algebra

The `ᵐᵒᵖ` in `PaschkeModule.ρ` makes the Paschke triple of **154III**.5 live
on `𝒷ᵃ(𝒜 ⊗_φ ℬ)ᵐᵒᵖ`.  Mathlib supplies `CStarAlgebra Aᵐᵒᵖ`,
`PartialOrder Aᵐᵒᵖ` (lifted along `unop`) and `StarOrderedRing Aᵐᵒᵖ`; what
is missing is the abstract Kadison definition of `Theses/Common.lean`, and
it transfers because `unop` is an order isomorphism of the self-adjoint
parts and `ω ↦ ω ∘ unop` is a bijection of the np-functionals. -/

section MulOppositeVN

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `unop` as an order isomorphism `selfAdjoint Aᵐᵒᵖ ≃o selfAdjoint A`
(the order of `Aᵐᵒᵖ` is `PartialOrder.lift unop`, so this is the identity
on the underlying relation). -/
def selfAdjointUnop : selfAdjoint Aᵐᵒᵖ ≃o selfAdjoint A where
  toFun x := ⟨MulOpposite.unop x.1, by
    have h := x.2
    rw [selfAdjoint.mem_iff] at h ⊢
    exact congrArg MulOpposite.unop h⟩
  invFun x := ⟨MulOpposite.op x.1, by
    have h := x.2
    rw [selfAdjoint.mem_iff] at h ⊢
    exact congrArg MulOpposite.op h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- np-functionals transfer to the opposite algebra along `unop`. -/
noncomputable def npFunctionalOp (ω : NPFunctional A) : NPFunctional Aᵐᵒᵖ where
  toPositiveLinearMap :=
    PositiveLinearMap.mk₀
      ((ω.toPositiveLinearMap : A →ₗ[ℂ] ℂ).comp
        ((MulOpposite.opLinearEquiv ℂ).symm.toLinearMap : Aᵐᵒᵖ →ₗ[ℂ] A))
      (fun x hx => npFunctional_nonneg ω hx)
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hlub' : IsLUB (selfAdjointUnop '' D) (selfAdjointUnop s) :=
      selfAdjointUnop.isLUB_image'.mpr hlub
    have h := ω.preservesDirSups' (selfAdjointUnop '' D) (selfAdjointUnop s)
      (hne.image _) (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
        exact ⟨selfAdjointUnop z, ⟨z, hz, rfl⟩, hxz, hyz⟩) hlub'
    rw [Set.image_image] at h
    exact h

theorem npFunctionalOp_apply (ω : NPFunctional A) (x : Aᵐᵒᵖ) :
    npFunctionalOp ω x = ω (MulOpposite.unop x) := rfl

/-- The opposite of a von Neumann algebra (in the abstract sense of
**42I**) is again one. -/
instance vonNeumannAlgebra_mulOpposite [VonNeumannAlgebra A] :
    VonNeumannAlgebra Aᵐᵒᵖ where
  isLUB_of_bddAbove_directed D hne hdir hbdd := by
    obtain ⟨b, hb⟩ := hbdd
    obtain ⟨s, hs⟩ := VonNeumannAlgebra.isLUB_of_bddAbove_directed
      (selfAdjointUnop '' D) (hne.image _)
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
        exact ⟨selfAdjointUnop z, ⟨z, hz, rfl⟩, hxz, hyz⟩)
      ⟨selfAdjointUnop b, by rintro _ ⟨x, hx, rfl⟩; exact hb hx⟩
    refine ⟨selfAdjointUnop.symm s, ?_⟩
    have h2 : IsLUB (⇑selfAdjointUnop '' D)
        (selfAdjointUnop (selfAdjointUnop.symm s)) := by
      simpa using hs
    exact selfAdjointUnop.isLUB_image'.mp h2
  np_faithful a ha h := by
    have h0 : MulOpposite.unop a = 0 :=
      VonNeumannAlgebra.np_faithful (MulOpposite.unop a) ha
        (fun ω => h (npFunctionalOp ω))
    exact MulOpposite.unop_injective h0

end MulOppositeVN

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

  `‖∑ᵢ T(aᵢ, bᵢ)‖² ≤ r ‖∑_{i,j} bᵢ* φ(aᵢ* aⱼ) bⱼ‖`

(mirrored: `‖∑ᵢ T(aᵢ,bᵢ)‖² ≤ r ‖∑_{i,j} bᵢ φ(aᵢ aⱼ*) bⱼ*‖`).

**Convention.**  `T_mirrored(a,b) = T_thesis(a*, b*)` (see the Convention
paragraphs at the head of the file), so the thesis's inequality is
substituted into at `aᵢ ↦ aᵢ*`, `bᵢ ↦ bᵢ*`; that is what produces the
`bᵢ φ(aᵢ aⱼ*) bⱼ*` above, whose positivity is complete positivity of `φ`
applied to the families `(aᵢ*)` and `(bᵢ*)`.  Both `star`s must be on the
*outside*: with them on the inside the structure is **uninhabited together
with `PaschkeModule.inner_tprod`** — for `n = 1` the two clauses would read
`‖b φ(aa*) b*‖ ≤ r ‖b* φ(aa*) b‖`, which fails in `M₂` for `φ = id`,
`a = e₀₀`, `b = e₁₀` (left side `‖e₁₁‖ = 1`, right side `0`).  See
`PROVING-LOG.md`, sessions 14 and 16. -/
structure PhiCompatible (φ : 𝒜 → ℬ) {X : Type u} [NormedAddCommGroup X]
    [Module ℂ X] [SMul ℬ X] [CStarModule ℬ X] (T : 𝒜 → ℬ → X) :
    Prop where
  add_left : ∀ (a a' : 𝒜) (b : ℬ), T (a + a') b = T a b + T a' b
  add_right : ∀ (a : 𝒜) (b b' : ℬ), T a (b + b') = T a b + T a b'
  smul_complex : ∀ (c : ℂ) (a : 𝒜) (b : ℬ), T (c • a) b = c • T a b
  smul_action : ∀ (a : 𝒜) (b c : ℬ), c • T a b = T a (c * b)
  bound : ∃ r > (0 : ℝ), ∀ (n : ℕ) (a : Fin n → 𝒜) (b : Fin n → ℬ),
    ‖∑ i, T (a i) (b i)‖ ^ 2 ≤
      r * ‖∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j)‖

set_option maxHeartbeats 1000000 in
-- the φ-compatibility bound is a long chain of `Finset` rewrites
/-- Shifting a φ-compatible map on the right, `(a, b) ↦ T (a a₀) b`, again
gives a φ-compatible map (mirrored: this is the thesis's *left* shift
`(a,b) ↦ T (a₀a) b`).  Only the bound needs an argument, and it is complete
positivity of `φ` at the two families `(aᵢa₀)*` and `(aᵢc)*`, where
`c c* = K − a₀a₀*` for `K = ‖a₀‖² + 1`; adding the two gives
`S₁ + S₂ = K · S₀`, so `0 ≤ S₁ ≤ K · S₀`.

This is what makes `ϱ(a₀)` exist (**154III**.2) and what lets the
intertwining clause of **154III**.4 be checked on elementary tensors. -/
theorem PhiCompatible.mul_right (φ : NCPMap 𝒜 ℬ) {Y : Type u}
    [NormedAddCommGroup Y] [Module ℂ Y] [SMul ℬ Y] [CStarModule ℬ Y]
    {T : 𝒜 → ℬ → Y} (hT : PhiCompatible ⇑φ T) (a₀ : 𝒜) :
    PhiCompatible ⇑φ (fun a b => T (a * a₀) b) := by
  classical
  set ψ : 𝒜 →ₗ[ℂ] ℬ := φ.toCompletelyPositiveMap.toLinearMap with hψdef
  have hψ : ⇑φ = ⇑ψ := rfl
  have hcp : IsCompletelyPositiveMap ψ :=
    ((cp_iff _).out 1 0).mp fun N A hA =>
      φ.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N A hA
  obtain ⟨r, hr0, hr⟩ := hT.bound
  refine { add_left := fun a a' b => by
             rw [add_mul]; exact hT.add_left _ _ _
           add_right := fun a b b' => hT.add_right _ _ _
           smul_complex := fun c a b => by
             rw [smul_mul_assoc]; exact hT.smul_complex _ _ _
           smul_action := fun a b c => hT.smul_action _ _ _
           bound := ⟨r * (‖a₀‖ ^ 2 + 1), by positivity, fun n a b => ?_⟩ }
  set K : ℝ := ‖a₀‖ ^ 2 + 1 with hK
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hcast : ∀ t : ℝ, algebraMap ℝ 𝒜 t = ((t : ℂ)) • (1 : 𝒜) := by
    intro t
    rw [IsScalarTower.algebraMap_apply ℝ ℂ 𝒜, Algebra.algebraMap_eq_smul_one]
    norm_num
  have hnorm2 : ‖a₀ * star a₀‖ = ‖a₀‖ ^ 2 := by
    rw [CStarRing.norm_self_mul_star]; ring
  have hle : a₀ * star a₀ ≤ ((K : ℝ) : ℂ) • (1 : 𝒜) := by
    have h1 := (IsSelfAdjoint.mul_star_self a₀).le_algebraMap_norm_self
    rw [hcast] at h1
    refine h1.trans ?_
    rw [← sub_nonneg, ← sub_smul]
    have h2 : ((K : ℝ) : ℂ) - ((‖a₀ * star a₀‖ : ℝ) : ℂ) = 1 := by
      rw [hnorm2, hK]; push_cast; ring
    rw [h2, one_smul]
    exact zero_le_one
  set c : 𝒜 := CFC.sqrt (((K : ℝ) : ℂ) • (1 : 𝒜) - a₀ * star a₀) with hcdef
  have hcc : c * star c = ((K : ℝ) : ℂ) • (1 : 𝒜) - a₀ * star a₀ := by
    have h0 : (0 : 𝒜) ≤ ((K : ℝ) : ℂ) • (1 : 𝒜) - a₀ * star a₀ := sub_nonneg.mpr hle
    have hsa : star c = c := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
    rw [hsa, hcdef, CFC.sqrt_mul_sqrt_self _ h0]
  -- the three conjugated sums
  set S0 : ℬ := ∑ i, ∑ j, b i * ψ (a i * star (a j)) * star (b j) with hS0def
  set S1 : ℬ := ∑ i, ∑ j, b i * ψ (a i * a₀ * star (a j * a₀)) * star (b j)
    with hS1def
  set S2 : ℬ := ∑ i, ∑ j, b i * ψ (a i * c * star (a j * c)) * star (b j)
    with hS2def
  have hS1nn : (0 : ℬ) ≤ S1 := by
    have h := hcp n (fun i => star (a i * a₀)) (fun i => star (b i))
    simp only [star_star] at h
    exact h
  have hS2nn : (0 : ℬ) ≤ S2 := by
    have h := hcp n (fun i => star (a i * c)) (fun i => star (b i))
    simp only [star_star] at h
    exact h
  have hpoint : ∀ i j : Fin n,
      b i * ψ (a i * a₀ * star (a j * a₀)) * star (b j)
        + b i * ψ (a i * c * star (a j * c)) * star (b j)
      = ((K : ℝ) : ℂ) • (b i * ψ (a i * star (a j)) * star (b j)) := by
    intro i j
    have hsum : a₀ * star a₀ + c * star c = ((K : ℝ) : ℂ) • (1 : 𝒜) := by
      rw [hcc]; abel
    have h1 : a i * a₀ * star (a j * a₀) + a i * c * star (a j * c)
        = ((K : ℝ) : ℂ) • (a i * star (a j)) := by
      calc a i * a₀ * star (a j * a₀) + a i * c * star (a j * c)
          = a i * (a₀ * star a₀ + c * star c) * star (a j) := by
            simp only [star_mul]; noncomm_ring
        _ = a i * (((K : ℝ) : ℂ) • (1 : 𝒜)) * star (a j) := by rw [hsum]
        _ = ((K : ℝ) : ℂ) • (a i * star (a j)) := by
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
  have hkey := hr n (fun i => a i * a₀) b
  simp only [← hψ] at hS0def hS1def
  calc ‖∑ i, T (a i * a₀) (b i)‖ ^ 2
      ≤ r * ‖S1‖ := by rw [hS1def]; simpa [hψ] using hkey
    _ ≤ r * (K * ‖S0‖) := mul_le_mul_of_nonneg_left hnormS1 hr0.le
    _ = r * K * ‖S0‖ := by ring
    _ = r * (‖a₀‖ ^ 2 + 1)
          * ‖∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j)‖ := by
        rw [hS0def, hK]

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
  `⟨a ⊗ b, α ⊗ β⟩ = β φ(α a*) b*`. -/
  inner_tprod : ∀ (a a' : 𝒜) (b b' : ℬ),
    inner ℬ (tprod a b) (tprod a' b') = b' * φ (a' * star a) * star b
  /-- Part 1, universal property: every φ-compatible bilinear map into a
  self-dual Hilbert ℬ-module factors uniquely through `⊗` by a bounded
  module map. -/
  univ : ∀ (Y : Type u) (_ : NormedAddCommGroup Y) (_ : Module ℂ Y)
    (_ : SMul ℬ Y) (_ : CStarModule ℬ Y) (_ : CompleteSpace Y),
    SelfDual ℬ Y → ∀ T : 𝒜 → ℬ → Y, PhiCompatible ⇑φ T →
      ∃! T' : X → Y,
        (∃ C : ℝ, IsBoundedModuleMap (cstarBInner ℬ X) (cstarBInner ℬ Y)
          C T') ∧ ∀ a b, T' (tprod a b) = T a b
  /-- Part 2: the nmiu-map `ϱ : 𝒜 → ℬᵃ(𝒜 ⊗_φ ℬ)ᵐᵒᵖ` (the `ᵐᵒᵖ` is forced
  by the mirroring — see the head of the file). -/
  ρ : NMIUMap 𝒜 (Ba ℬ X)ᵐᵒᵖ
  /-- `ϱ(a₀)(a ⊗ b) = (a a₀) ⊗ b` (mirrored). -/
  ρ_tprod : ∀ (a₀ a : 𝒜) (b : ℬ),
    (ρ a₀).unop.1 (tprod a b) = tprod (a * a₀) b
  /-- Part 3: the ncp-map `h : ℬᵃ(𝒜 ⊗_φ ℬ)ᵐᵒᵖ → ℬ`. -/
  h : NCPMap (Ba ℬ X)ᵐᵒᵖ ℬ
  /-- `h(T) = ⟨1 ⊗ 1, T (1 ⊗ 1)⟩`. -/
  h_def : ∀ T : (Ba ℬ X)ᵐᵒᵖ,
    h T = inner ℬ (tprod 1 1) (T.unop.1 (tprod 1 1))

attribute [instance] PaschkeModule.nacg PaschkeModule.mod PaschkeModule.smul
  PaschkeModule.cstarMod PaschkeModule.complete

/-- **154III**, part 3 on part 2: `h ∘ ϱ = φ`, the first half of
`IsPaschkeDilationOf`.  This is the computation the mirroring had to get
right: `h (ρ a) = ⟨1 ⊗ 1, 1a ⊗ 1⟩ = 1 · φ(a · 1*) · 1* = φ a`, with no
`star` anywhere (QUESTIONS **D2**). -/
theorem paschkeModule_h_ρ (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ) (a : 𝒜) :
    M.h (M.ρ a) = φ a := by
  rw [M.h_def, M.ρ_tprod, M.inner_tprod]
  simp

/-- **Negative result** (kept in the tree; `PROVING-LOG.md` session 15).
Rendering the thesis's `⊗` *without* the `star` on its `𝒜`-argument — i.e.
`⟨a ⊗ b, a' ⊗ b'⟩ = b' φ(a'* a) b*` — is contradictory: that right-hand
side is ℂ-*linear* in `a`, while Mathlib's `⟨·,·⟩` is conjugate-linear in
its first argument and `PhiCompatible.smul_complex` makes `tprod` ℂ-linear
in `a`; comparing the two at `c = i` gives `2i φ(a) = 0`.  A `PaschkeModule`
with that `inner_tprod` is therefore uninhabited for every `φ ≠ 0`. -/
theorem paschke_inner_conj_forces_zero (φ : NCPMap 𝒜 ℬ) {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X]
    (tprod : 𝒜 → ℬ → X)
    (hsmul : ∀ (c : ℂ) (a : 𝒜) (b : ℬ), tprod (c • a) b = c • tprod a b)
    (hinner : ∀ (a a' : 𝒜) (b b' : ℬ),
      inner ℬ (tprod a b) (tprod a' b') = b' * φ (star a' * a) * star b)
    (a : 𝒜) : φ a = 0 := by
  have key : ∀ (c : ℂ) (a a' : 𝒜),
      (c • (φ (star a' * a) : ℬ)) = (starRingEnd ℂ) c • (φ (star a' * a) : ℬ) := by
    intro c a a'
    have h1 : inner ℬ (tprod (c • a) 1) (tprod a' 1)
        = (1 : ℬ) * φ (star a' * (c • a)) * star (1 : ℬ) := hinner _ _ _ _
    have h2 : tprod (c • a) 1 = c • tprod a 1 := hsmul c a 1
    rw [h2, CStarModule.inner_smul_left_complex, hinner] at h1
    have hs : φ (c • (star a' * a)) = c • φ (star a' * a) :=
      map_smul φ.toCompletelyPositiveMap.toLinearMap c _
    simpa [hs] using h1.symm
  have h := key Complex.I a 1
  simp only [star_one, one_mul, Complex.conj_I] at h
  have h3 : ((2 : ℂ) * Complex.I) • (φ a : ℬ) = 0 := by
    rw [two_mul, add_smul]
    nth_rewrite 2 [h]
    simp
  have h4 : ((2 : ℂ) * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  exact (smul_eq_zero.mp h3).resolve_left h4

/-- **Negative result** (kept in the tree; `PROVING-LOG.md` session 15).
With the correct `inner_tprod` `⟨a ⊗ b, a' ⊗ b'⟩ = b' φ(a' a*) b*`, asking
`ρ` to be an nmiu-map into `𝒷ᵃ(X)` rather than into `𝒷ᵃ(X)ᵐᵒᵖ` is
contradictory as well: `ρ_tprod` with `ρ(a₀)(a ⊗ b) = (a₀a) ⊗ b` and
adjointability of `ρ(a₀)` (whose adjoint is `ρ(a₀*)`) force `φ` to be
*cyclic*, which fails already for `φ = id` on `M₂`.  This is why the `ρ`
field lands in `(Ba ℬ X)ᵐᵒᵖ`; see the head of this file. -/
theorem paschke_rho_forces_cyclic (φ : NCPMap 𝒜 ℬ) {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X]
    [CompleteSpace X] (tprod : 𝒜 → ℬ → X)
    (hinner : ∀ (a a' : 𝒜) (b b' : ℬ),
      inner ℬ (tprod a b) (tprod a' b') = b' * φ (a' * star a) * star b)
    (ρ : NMIUMap 𝒜 (Ba ℬ X))
    (hρ : ∀ (a₀ a : 𝒜) (b : ℬ), (ρ a₀).1 (tprod a b) = tprod (a₀ * a) b)
    (a a' a₀ : 𝒜) :
    φ (a' * (star a * star a₀)) = φ (star a₀ * a' * star a) := by
  have hstar : (star (ρ a₀) : Ba ℬ X) = ρ (star a₀) := by
    have hc : ⇑ρ = ⇑ρ.toStarAlgHom := rfl
    have h := map_star ρ.toStarAlgHom a₀
    simpa [hc] using h.symm
  have hadj : ModuleAdjointTo ℬ ⇑(ρ a₀).1 ⇑((star (ρ a₀) : Ba ℬ X)).1 :=
    baSubalgebra_star_spec _
  have h1 := hadj (tprod a 1) (tprod a' 1)
  rw [hstar, hρ, hρ, hinner, hinner] at h1
  simpa [star_mul, mul_assoc] using h1

/-- **154III** (`existence-paschke`, dils.tex:3558, Theorem), parts 1–3:
the module `𝒜 ⊗_φ ℬ`, the representation `ϱ` and the vector state `h`
exist.

The bundle is not vacuous: `paschkeModuleId` exhibits `ℬ` itself as
`ℬ ⊗_id ℬ`, so every field below is jointly satisfiable for a non-zero
`φ`. -/
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

/-- **154III** (`existence-paschke`, dils.tex:3558, Theorem), part 2,
uniqueness clause: for each `a₀ ∈ 𝒜` the operator `ϱ(a₀)` is the unique
adjointable operator with `ϱ(a₀)(a ⊗ b) = (a a₀) ⊗ b` (mirrored). -/
theorem existence_paschke_2 [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ) (a₀ : 𝒜) :
    ∃! T : Ba ℬ M.X, ∀ (a : 𝒜) (b : ℬ),
      T.1 (M.tprod a b) = M.tprod (a * a₀) b := by
  -- part 1 (the universal property) applied to the shifted bilinear map
  obtain ⟨T', -, hT'uniq⟩ :=
    M.univ M.X inferInstance inferInstance inferInstance inferInstance inferInstance
      M.selfDual _ (M.compat.mul_right φ a₀)
  refine ⟨(M.ρ a₀).unop, fun a b => M.ρ_tprod a₀ a b, fun T hT => ?_⟩
  have h1 : ⇑T.1 = T' := hT'uniq _ ⟨ba_isBoundedModuleMap T, fun a b => hT a b⟩
  have h2 : ⇑((M.ρ a₀).unop).1 = T' :=
    hT'uniq _ ⟨ba_isBoundedModuleMap _, fun a b => M.ρ_tprod a₀ a b⟩
  exact Subtype.ext (DFunLike.coe_injective (h1.trans h2.symm))

/-- **154III** (`existence-paschke`, dils.tex:3558, Theorem), part 4
(`paschke-spatial`): universal property of `(ϱ, 1 ⊗ 1)`: for every
nmiu-map `ϱ' : 𝒜 → ℬᵃ(Y)ᵐᵒᵖ` into the operators on a self-dual Hilbert
ℬ-module `Y` and every `e ∈ Y` with `φ = ⟨e, ϱ'(·) e⟩`, there is a unique
inner-product-preserving module map `S : 𝒜 ⊗_φ ℬ → Y` with
`S(1 ⊗ 1) = e` and `S ϱ(a) = ϱ'(a) S` (equivalently `ad_S ∘ ϱ' = ϱ`).

The hypothesis `hφ` is the exact mirror of `h_def` (`ϱ' := ρ`, `e := 1 ⊗ 1`
recovers `paschkeModule_h_ρ`), and `ϱ'` lands in `𝒷ᵃ(Y)ᵐᵒᵖ` for the same
reason `ρ` does.

The proof does not follow the thesis (which goes through
`paschke-uniqueness`, a λ-scaling lemma and a density argument): the
universal property of part 1 is enough on its own, applied four times.
Once to `T(a,b) = b·ϱ'(a)e` — whose Gram matrix is `φ(aⱼ aᵢ*)` on the nose,
so it is φ-compatible with constant `1` — which produces `S`; twice against
`ℬ` itself (self dual by `selfDual_self`) to upgrade
`⟨S(a ⊗ b), S(a' ⊗ b')⟩ = ⟨a ⊗ b, a' ⊗ b'⟩` from elementary tensors to all
of `𝒜 ⊗_φ ℬ`, one variable at a time; and once more, on the shifted map
`PhiCompatible.mul_right`, for the intertwining clause.  Uniqueness is
immediate from `S(a ⊗ b) = b·S(ϱ(a)(1 ⊗ 1))`. -/
theorem existence_paschke_4 [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ) {Y : Type u}
    [NormedAddCommGroup Y] [Module ℂ Y] [SMul ℬ Y] [CStarModule ℬ Y]
    [CompleteSpace Y] (hY : SelfDual ℬ Y) (e : Y)
    (ϱ' : NMIUMap 𝒜 (Ba ℬ Y)ᵐᵒᵖ)
    (hφ : ∀ a : 𝒜, φ a = inner ℬ e ((ϱ' a).unop.1 e)) :
    ∃! S : M.X → Y,
      (∃ C : ℝ, IsBoundedModuleMap (cstarBInner ℬ M.X) (cstarBInner ℬ Y)
        C S) ∧
      (∀ x y : M.X, inner ℬ (S x) (S y) = inner ℬ x y) ∧
      S (M.tprod 1 1) = e ∧
      ∀ (a : 𝒜) (x : M.X),
        S ((M.ρ a).unop.1 x) = (ϱ' a).unop.1 (S x) := by
  classical
  letI : NormedSpace ℂ Y := NormedSpace.ofCore (CStarModule.normedSpaceCore ℬ)
  -- ### the operators `ϱ'(a)`: (anti)multiplicativity, linearity, adjoints
  have hc : ⇑ϱ' = ⇑ϱ'.toStarAlgHom := rfl
  have hAdd : ∀ a a' : 𝒜, ϱ' (a + a') = ϱ' a + ϱ' a' := fun a a' => by
    simpa [hc] using map_add ϱ'.toStarAlgHom a a'
  have hSmul : ∀ (c : ℂ) (a : 𝒜), ϱ' (c • a) = c • ϱ' a := fun c a => by
    simpa [hc] using map_smul ϱ'.toStarAlgHom c a
  have hMul : ∀ a a' : 𝒜, ϱ' (a * a') = ϱ' a * ϱ' a' := fun a a' => by
    simpa [hc] using map_mul ϱ'.toStarAlgHom a a'
  have hOne : ϱ' 1 = 1 := by simpa [hc] using map_one ϱ'.toStarAlgHom
  have hStar : ∀ a : 𝒜, ϱ' (star a) = star (ϱ' a) := fun a => by
    simpa [hc] using map_star ϱ'.toStarAlgHom a
  have hRcomp : ∀ (a a' : 𝒜) (y : Y),
      (ϱ' a').unop.1 ((ϱ' a).unop.1 y) = (ϱ' (a * a')).unop.1 y := by
    intro a a' y
    have h : ((ϱ' (a * a')).unop : Ba ℬ Y)
        = ((ϱ' a').unop : Ba ℬ Y) * ((ϱ' a).unop : Ba ℬ Y) := by
      rw [hMul a a']
      rfl
    rw [h]
    rfl
  have hRlin : ∀ (a : 𝒜) (b : ℬ) (y : Y),
      (ϱ' a).unop.1 (b • y) = b • (ϱ' a).unop.1 y := fun a =>
    (moduleAdjointable_linear (𝒜 := ℬ) ⇑(ϱ' a).unop.1 (ϱ' a).unop.2).2.2
  have hRadj : ∀ (a : 𝒜) (x y : Y),
      inner ℬ ((ϱ' a).unop.1 x) y = inner ℬ x ((ϱ' (star a)).unop.1 y) := by
    intro a x y
    have h : ModuleAdjointTo ℬ ⇑(ϱ' a).unop.1
        ⇑((star (ϱ' a).unop : Ba ℬ Y)).1 := baSubalgebra_star_spec _
    have h2 : (star (ϱ' a).unop : Ba ℬ Y) = (ϱ' (star a)).unop := by
      rw [hStar a]
      rfl
    rw [← h2]
    exact h x y
  -- ### the φ-compatible map `T(a,b) = b · ϱ'(a) e`
  obtain ⟨T, hTdef⟩ : ∃ T : 𝒜 → ℬ → Y, ∀ a b, T a b = b • (ϱ' a).unop.1 e :=
    ⟨fun a b => b • (ϱ' a).unop.1 e, fun _ _ => rfl⟩
  have hgram : ∀ a a' : 𝒜,
      (inner ℬ ((ϱ' a).unop.1 e) ((ϱ' a').unop.1 e) : ℬ) = φ (a' * star a) := by
    intro a a'
    rw [hRadj, hRcomp]
    exact (hφ (a' * star a)).symm
  have hTinner : ∀ (a a' : 𝒜) (b b' : ℬ),
      inner ℬ (T a b) (T a' b') = b' * φ (a' * star a) * star b := by
    intro a a' b b'
    rw [hTdef, hTdef, CStarModule.inner_op_smul_right,
      CStarModule.inner_op_smul_left, hgram, mul_assoc]
  have hTcompat : PhiCompatible ⇑φ T := by
    refine { add_left := fun a a' b => ?_
             add_right := fun a b b' => ?_
             smul_complex := fun c a b => ?_
             smul_action := fun a b c => ?_
             bound := ⟨1, one_pos, fun n a b => ?_⟩ }
    · rw [hTdef, hTdef, hTdef, hAdd a a']
      show b • (((ϱ' a).unop : Ba ℬ Y).1 + ((ϱ' a').unop : Ba ℬ Y).1) e = _
      rw [ContinuousLinearMap.add_apply, op_smul_add]
    · rw [hTdef, hTdef, hTdef, op_add_smul]
    · rw [hTdef, hTdef, hSmul c a]
      show b • (c • ((ϱ' a).unop : Ba ℬ Y).1) e = _
      rw [ContinuousLinearMap.smul_apply, op_smul_comm_complex]
    · rw [hTdef, hTdef, op_mul_smul]
    · have hgramsum : (inner ℬ (∑ i, T (a i) (b i)) (∑ i, T (a i) (b i)) : ℬ)
          = ∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j) :=
        calc (inner ℬ (∑ i, T (a i) (b i)) (∑ i, T (a i) (b i)) : ℬ)
            = ∑ i, ∑ j, (inner ℬ (T (a i) (b i)) (T (a j) (b j)) : ℬ) := by
              rw [CStarModule.inner_sum_left]
              exact Finset.sum_congr rfl fun i _ => CStarModule.inner_sum_right
          _ = ∑ i, ∑ j, b j * φ (a j * star (a i)) * star (b i) :=
              Finset.sum_congr rfl fun i _ =>
                Finset.sum_congr rfl fun j _ => hTinner _ _ _ _
          _ = ∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j) := Finset.sum_comm
      rw [one_mul, CStarModule.norm_sq_eq (A := ℬ), hgramsum]
  -- ### `S`, from the universal property of part 1
  obtain ⟨S, ⟨hSbdd, hStprod⟩, hSuniq⟩ :=
    M.univ Y inferInstance inferInstance inferInstance inferInstance
      inferInstance hY T hTcompat
  have hSone : S (M.tprod 1 1) = e := by
    rw [hStprod, hTdef, hOne]
    show (1 : ℬ) • (1 : Ba ℬ Y).1 e = e
    rw [op_one_smul]
    rfl
  -- ### two families of ℬ-valued module maps on `𝒜 ⊗_φ ℬ`
  have hinnerCompat : ∀ y : M.X,
      PhiCompatible ⇑φ (fun a b => (inner ℬ y (M.tprod a b) : ℬ)) := by
    intro y
    obtain ⟨r, hr0, hr⟩ := M.compat.bound
    refine { add_left := fun a a' b => by
               rw [M.compat.add_left, CStarModule.inner_add_right]
             add_right := fun a b b' => by
               rw [M.compat.add_right, CStarModule.inner_add_right]
             smul_complex := fun c a b => by
               rw [M.compat.smul_complex, CStarModule.inner_smul_right_complex]
             smul_action := fun a b c => by
               rw [← M.compat.smul_action, CStarModule.inner_op_smul_right,
                 smul_eq_mul]
             bound := ⟨r * (‖y‖ ^ 2 + 1), by positivity, fun n a b => ?_⟩ }
    have h1 : (∑ i, (inner ℬ y (M.tprod (a i) (b i)) : ℬ))
        = inner ℬ y (∑ i, M.tprod (a i) (b i)) :=
      CStarModule.inner_sum_right.symm
    rw [h1]
    have h2 := CStarModule.norm_inner_le (A := ℬ) M.X
      (x := y) (y := ∑ i, M.tprod (a i) (b i))
    have h3 := hr n a b
    have h4 : (0 : ℝ)
        ≤ ‖∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j)‖ := norm_nonneg _
    have h5 : (0 : ℝ) ≤ ‖∑ i, M.tprod (a i) (b i)‖ := norm_nonneg _
    have h6 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    have h7 : (0 : ℝ) ≤ ‖(inner ℬ y (∑ i, M.tprod (a i) (b i)) : ℬ)‖ :=
      norm_nonneg _
    calc ‖(inner ℬ y (∑ i, M.tprod (a i) (b i)) : ℬ)‖ ^ 2
        ≤ (‖y‖ * ‖∑ i, M.tprod (a i) (b i)‖) ^ 2 := by nlinarith
      _ = ‖y‖ ^ 2 * ‖∑ i, M.tprod (a i) (b i)‖ ^ 2 := by ring
      _ ≤ ‖y‖ ^ 2 * (r * ‖∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j)‖) := by
          nlinarith [sq_nonneg ‖y‖]
      _ ≤ r * (‖y‖ ^ 2 + 1)
            * ‖∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j)‖ := by
          nlinarith [sq_nonneg ‖y‖, mul_nonneg hr0.le h4]
  have hbddF : ∀ y : M.X, ∃ C : ℝ,
      IsBoundedModuleMap (cstarBInner ℬ M.X) (cstarBInner ℬ ℬ) C
        (fun x => (inner ℬ y x : ℬ)) := by
    intro y
    refine ⟨‖y‖, { add := fun x x' => CStarModule.inner_add_right
                   smul_complex := fun c x =>
                     CStarModule.inner_smul_right_complex
                   smul := fun b x => by
                     rw [CStarModule.inner_op_smul_right, smul_eq_mul]
                   bound := fun x => ?_ }⟩
    rw [cstarBInner_norm, cstarBInner_norm]
    exact CStarModule.norm_inner_le (A := ℬ) M.X
  have hbddG : ∀ y : M.X, ∃ C : ℝ,
      IsBoundedModuleMap (cstarBInner ℬ M.X) (cstarBInner ℬ ℬ) C
        (fun x => (inner ℬ (S y) (S x) : ℬ)) := by
    intro y
    obtain ⟨C, hC⟩ := hSbdd
    refine ⟨‖S y‖ * (|C| + 1),
      { add := fun x x' => by rw [hC.add, CStarModule.inner_add_right]
        smul_complex := fun c x => by
          rw [hC.smul_complex, CStarModule.inner_smul_right_complex]
        smul := fun b x => by
          rw [hC.smul, CStarModule.inner_op_smul_right, smul_eq_mul]
        bound := fun x => ?_ }⟩
    have hb := hC.bound x
    rw [cstarBInner_norm, cstarBInner_norm] at hb
    rw [cstarBInner_norm, cstarBInner_norm]
    have h2 := CStarModule.norm_inner_le (A := ℬ) Y (x := S y) (y := S x)
    have h3 : C ≤ |C| := le_abs_self C
    have h4 : ‖S x‖ ≤ (|C| + 1) * ‖x‖ := by nlinarith [norm_nonneg x]
    calc ‖(inner ℬ (S y) (S x) : ℬ)‖ ≤ ‖S y‖ * ‖S x‖ := h2
      _ ≤ ‖S y‖ * ((|C| + 1) * ‖x‖) := by
          exact mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ = ‖S y‖ * (|C| + 1) * ‖x‖ := by ring
  -- ### `S` preserves inner products
  have hstep1 : ∀ (a' : 𝒜) (b' : ℬ) (x : M.X),
      inner ℬ (S (M.tprod a' b')) (S x) = inner ℬ (M.tprod a' b') x := by
    intro a' b' x
    obtain ⟨F, -, hFuniq⟩ :=
      M.univ ℬ inferInstance inferInstance inferInstance inferInstance
        inferInstance (selfDual_self ℬ) _ (hinnerCompat (M.tprod a' b'))
    have hF1 : (fun x => (inner ℬ (M.tprod a' b') x : ℬ)) = F :=
      hFuniq _ ⟨hbddF _, fun a b => rfl⟩
    have hF2 : (fun x => (inner ℬ (S (M.tprod a' b')) (S x) : ℬ)) = F := by
      refine hFuniq _ ⟨hbddG _, fun a b => ?_⟩
      show (inner ℬ (S (M.tprod a' b')) (S (M.tprod a b)) : ℬ)
        = inner ℬ (M.tprod a' b') (M.tprod a b)
      rw [hStprod, hStprod, hTinner, M.inner_tprod]
    exact (congrFun hF2 x).trans (congrFun hF1 x).symm
  have hinner_pres : ∀ x y : M.X, inner ℬ (S x) (S y) = inner ℬ x y := by
    intro x y
    obtain ⟨F, -, hFuniq⟩ :=
      M.univ ℬ inferInstance inferInstance inferInstance inferInstance
        inferInstance (selfDual_self ℬ) _ (hinnerCompat x)
    have hF1 : (fun z => (inner ℬ x z : ℬ)) = F :=
      hFuniq _ ⟨hbddF _, fun a b => rfl⟩
    have hF2 : (fun z => (inner ℬ (S x) (S z) : ℬ)) = F := by
      refine hFuniq _ ⟨hbddG _, fun a b => ?_⟩
      show (inner ℬ (S x) (S (M.tprod a b)) : ℬ) = inner ℬ x (M.tprod a b)
      rw [← CStarModule.star_inner (S (M.tprod a b)) (S x), hstep1,
        CStarModule.star_inner]
    exact (congrFun hF2 y).trans (congrFun hF1 y).symm
  -- ### the intertwining clause
  have hintertwine : ∀ (a : 𝒜) (x : M.X),
      S ((M.ρ a).unop.1 x) = (ϱ' a).unop.1 (S x) := by
    intro a x
    obtain ⟨G, -, hGuniq⟩ :=
      M.univ Y inferInstance inferInstance inferInstance inferInstance
        inferInstance hY _ (hTcompat.mul_right φ a)
    have hG1 : (fun x => S ((M.ρ a).unop.1 x)) = G := by
      refine hGuniq _ ⟨?_, fun a₁ b => ?_⟩
      · obtain ⟨C₁, hC₁⟩ := ba_isBoundedModuleMap (M.ρ a).unop
        obtain ⟨C₂, hC₂⟩ := hSbdd
        refine ⟨(|C₁| + 1) * (|C₂| + 1),
          { add := fun x x' => by rw [hC₁.add, hC₂.add]
            smul_complex := fun c x => by
              rw [hC₁.smul_complex, hC₂.smul_complex]
            smul := fun b x => by rw [hC₁.smul, hC₂.smul]
            bound := fun x => ?_ }⟩
        have h1 := hC₁.bound x
        have h2 := hC₂.bound ((M.ρ a).unop.1 x)
        rw [cstarBInner_norm, cstarBInner_norm] at h1 h2 ⊢
        have h3 : ‖(M.ρ a).unop.1 x‖ ≤ (|C₁| + 1) * ‖x‖ := by
          nlinarith [norm_nonneg x, le_abs_self C₁]
        have h4 : ‖S ((M.ρ a).unop.1 x)‖ ≤ (|C₂| + 1) * ‖(M.ρ a).unop.1 x‖ := by
          nlinarith [norm_nonneg ((M.ρ a).unop.1 x), le_abs_self C₂]
        calc ‖S ((M.ρ a).unop.1 x)‖ ≤ (|C₂| + 1) * ‖(M.ρ a).unop.1 x‖ := h4
          _ ≤ (|C₂| + 1) * ((|C₁| + 1) * ‖x‖) := by
              refine mul_le_mul_of_nonneg_left h3 ?_
              positivity
          _ = (|C₁| + 1) * (|C₂| + 1) * ‖x‖ := by ring
      · show S ((M.ρ a).unop.1 (M.tprod a₁ b)) = T (a₁ * a) b
        rw [M.ρ_tprod, hStprod]
    have hG2 : (fun x => (ϱ' a).unop.1 (S x)) = G := by
      refine hGuniq _ ⟨?_, fun a₁ b => ?_⟩
      · obtain ⟨C₁, hC₁⟩ := ba_isBoundedModuleMap (ϱ' a).unop
        obtain ⟨C₂, hC₂⟩ := hSbdd
        refine ⟨(|C₁| + 1) * (|C₂| + 1),
          { add := fun x x' => by rw [hC₂.add, hC₁.add]
            smul_complex := fun c x => by
              rw [hC₂.smul_complex, hC₁.smul_complex]
            smul := fun b x => by rw [hC₂.smul, hC₁.smul]
            bound := fun x => ?_ }⟩
        have h1 := hC₂.bound x
        have h2 := hC₁.bound (S x)
        rw [cstarBInner_norm, cstarBInner_norm] at h1 h2 ⊢
        have h3 : ‖S x‖ ≤ (|C₂| + 1) * ‖x‖ := by
          nlinarith [norm_nonneg x, le_abs_self C₂]
        have h4 : ‖(ϱ' a).unop.1 (S x)‖ ≤ (|C₁| + 1) * ‖S x‖ := by
          nlinarith [norm_nonneg (S x), le_abs_self C₁]
        calc ‖(ϱ' a).unop.1 (S x)‖ ≤ (|C₁| + 1) * ‖S x‖ := h4
          _ ≤ (|C₁| + 1) * ((|C₂| + 1) * ‖x‖) := by
              refine mul_le_mul_of_nonneg_left h3 ?_
              positivity
          _ = (|C₁| + 1) * (|C₂| + 1) * ‖x‖ := by ring
      · show (ϱ' a).unop.1 (S (M.tprod a₁ b)) = T (a₁ * a) b
        rw [hStprod, hTdef, hRlin, hRcomp, hTdef]
    exact (congrFun hG1 x).trans (congrFun hG2 x).symm
  -- ### assembling
  refine ⟨S, ⟨hSbdd, hinner_pres, hSone, hintertwine⟩, fun S' hS' => ?_⟩
  obtain ⟨hS'bdd, -, hS'one, hS'int⟩ := hS'
  refine hSuniq _ ⟨hS'bdd, fun a b => ?_⟩
  obtain ⟨C, hC⟩ := hS'bdd
  have h1 : M.tprod a b = b • M.tprod a 1 := by
    rw [M.compat.smul_action, mul_one]
  have h2 : M.tprod a 1 = (M.ρ a).unop.1 (M.tprod 1 1) := by
    rw [M.ρ_tprod, one_mul]
  rw [h1, hC.smul, h2, hS'int, hS'one, hTdef]

/-- **154III** (`existence-paschke`, dils.tex:3558, Theorem), part 5:
`(ℬᵃ(𝒜 ⊗_φ ℬ), ϱ, h)` is a Paschke dilation of `φ`.  (In particular every
ncp-map between von Neumann algebras has a Paschke dilation.)

**154IV**–**154X** are the proof (including **154VIII**
`paschke-uniqueness` and **154IX** `paschke-spatial` as proof steps) — not
converted separately. -/
theorem existence_paschke_5 [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ) :
    IsPaschkeDilationOf
      ⟨(Ba ℬ M.X)ᵐᵒᵖ,
        @vonNeumannAlgebra_mulOpposite (Ba ℬ M.X) _ _ _
          (ba_vonNeumannAlgebra M.selfDual),
        M.ρ, M.h⟩ ⇑φ := by
  -- `h ∘ ϱ = φ` is `paschkeModule_h_ρ`; it is the half that was *false*
  -- before the `ᵐᵒᵖ` repair.  The universal property is **154IV**–**154X**.
  refine ⟨paschkeModule_h_ρ φ M, ?_⟩
  sorry

end Existence

/-! ### Non-vacuity of `PaschkeModule`

`ℬ` itself is `ℬ ⊗_id ℬ`.  This is the check that would have caught both
defects that made the bundle uninhabited (`PhiCompatible.bound`, session 14;
`inner_tprod`/`ρ`, sessions 15–16); `vnTensor_mul_complex` in
`SelfDual.lean` is the model.  It also exhibits the `ᵐᵒᵖ` concretely: the
adjointable operators on `ℬ` (in Mathlib's left-action convention) are the
**right** multiplications, so `t ↦ R_t` is a ∗-isomorphism `ℬ ≅ 𝒷ᵃ(ℬ)ᵐᵒᵖ`
and the vector state `T ↦ ⟨1, T 1⟩` is its inverse — completely positive on
`𝒷ᵃ(ℬ)ᵐᵒᵖ`, and (being `unop`, i.e. the transpose on `M₂`) *not* completely
positive on `𝒷ᵃ(ℬ)`. -/

section Inhabited

variable {ℬ : Type u} [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- Right multiplication `R_t : x ↦ x t` on `ℬ`, viewed as a Hilbert
ℬ-module over itself (Mathlib's `CStarModule ℬ ℬ`: `b • x = bx`,
`⟨x,y⟩ = y x*`), as an adjointable operator; its adjoint is `R_{t*}`. -/
noncomputable def rightMul (t : ℬ) : Ba ℬ ℬ :=
  ⟨(ContinuousLinearMap.mul ℂ ℬ).flip t,
    ⟨(ContinuousLinearMap.mul ℂ ℬ).flip (star t), by
      intro x y
      show (y * star (x * t) : ℬ) = (y * star t) * star x
      rw [star_mul, mul_assoc]⟩⟩

@[simp] theorem rightMul_apply (t x : ℬ) : (rightMul t).1 x = x * t := rfl

/-- `t ↦ R_t` is an **anti**-homomorphism: `R_s R_t = R_{ts}`.  This is the
concrete face of the `ᵐᵒᵖ` in `PaschkeModule.ρ`. -/
theorem rightMul_mul (s t : ℬ) : rightMul s * rightMul t = rightMul (t * s) := by
  refine Subtype.ext (ContinuousLinearMap.ext fun x => ?_)
  show (rightMul s).1 ((rightMul t).1 x) = x * (t * s)
  rw [rightMul_apply, rightMul_apply, mul_assoc]

theorem rightMul_one : rightMul (1 : ℬ) = 1 := by
  refine Subtype.ext (ContinuousLinearMap.ext fun x => ?_)
  show x * (1 : ℬ) = x
  rw [mul_one]

theorem rightMul_star (t : ℬ) : star (rightMul t) = rightMul (star t) := by
  refine Subtype.ext (ContinuousLinearMap.ext fun x => ?_)
  have h1 : ModuleAdjointTo ℬ ⇑(rightMul t).1 ⇑((star (rightMul t) : Ba ℬ ℬ)).1 :=
    baSubalgebra_star_spec _
  have h2 : ModuleAdjointTo ℬ ⇑(rightMul t).1 ⇑(rightMul (star t)).1 := by
    intro x y
    show (y * star (x * t) : ℬ) = (y * star t) * star x
    rw [star_mul, mul_assoc]
  exact congrFun (moduleAdjointTo_unique (𝒜 := ℬ) _ _ _ h1 h2) x

/-- **141III**/**143I** for `X = ℬ`: `t ↦ R_t` is a ∗-isomorphism
`ℬ ≅ 𝒷ᵃ(ℬ)ᵐᵒᵖ`.  Surjectivity is the ℬ-linearity of adjointable operators
(`moduleAdjointable_linear`): `T x = T (x • 1) = x · T 1`. -/
noncomputable def rightMulEquiv : ℬ ≃⋆ₐ[ℂ] (Ba ℬ ℬ)ᵐᵒᵖ where
  toFun t := MulOpposite.op (rightMul t)
  invFun S := S.unop.1 1
  left_inv t := by simp
  right_inv S := by
    refine MulOpposite.unop_injective (Subtype.ext (ContinuousLinearMap.ext fun x => ?_))
    show x * (S.unop.1 1) = S.unop.1 x
    have h := (moduleAdjointable_linear (𝒜 := ℬ) ⇑S.unop.1 S.unop.2).2.2 x 1
    show x * (S.unop.1 1) = S.unop.1 x
    rw [show (x • (1 : ℬ)) = x from by rw [smul_eq_mul, mul_one]] at h
    rw [h, smul_eq_mul]
  map_mul' s t := by
    show MulOpposite.op (rightMul (s * t)) = _
    rw [← MulOpposite.op_mul]
    congr 1
    show rightMul (s * t) = rightMul t * rightMul s
    rw [rightMul_mul]
  map_add' s t := by
    show MulOpposite.op (rightMul (s + t)) = _
    rw [← MulOpposite.op_add]
    congr 1
    refine Subtype.ext (ContinuousLinearMap.ext fun x => ?_)
    show x * (s + t) = x * s + x * t
    rw [mul_add]
  map_smul' c t := by
    show MulOpposite.op (rightMul (c • t)) = _
    rw [← MulOpposite.op_smul]
    congr 1
    refine Subtype.ext (ContinuousLinearMap.ext fun x => ?_)
    show x * (c • t) = c • (x * t)
    rw [mul_smul_comm]
  map_star' t := by
    show MulOpposite.op (rightMul (star t)) = star (MulOpposite.op (rightMul t))
    rw [← MulOpposite.op_star]
    congr 1
    rw [rightMul_star]

@[simp] theorem rightMulEquiv_apply (t : ℬ) :
    rightMulEquiv t = MulOpposite.op (rightMul t) := rfl

@[simp] theorem rightMulEquiv_symm_apply (S : (Ba ℬ ℬ)ᵐᵒᵖ) :
    rightMulEquiv.symm S = S.unop.1 1 := rfl



variable {ℬ : Type u} [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- The identity of a von Neumann algebra as an ncp-map (complete
positivity of a ∗-homomorphism is Mathlib's
`NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass`; normality is
`starAlgEquiv_preservesDirSups`). -/
noncomputable def ncpMapId : NCPMap ℬ ℬ where
  toCompletelyPositiveMap :=
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      (StarAlgHom.id ℂ ℬ : ℬ →⋆ₐ[ℂ] ℬ)
  preservesDirSups' := fun D s hne hdir hlub =>
    starAlgEquiv_preservesDirSups (StarAlgEquiv.refl (R := ℂ) (A := ℬ))
      D s hne hdir hlub

@[simp] theorem ncpMapId_apply (x : ℬ) : (ncpMapId : NCPMap ℬ ℬ) x = x := rfl

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- The Gram sum of the φ-compatibility bound for `φ = id` and
`tprod a b = b·a` collapses: `∑ᵢⱼ bᵢ(aᵢaⱼ*)bⱼ* = v v*` for `v = ∑ᵢ bᵢaᵢ`.
Hence the bound holds with `r = 1`, and it *vanishes* exactly when `v = 0` —
which is what forces the factorisation in `paschkeModuleId.univ`. -/
theorem gram_id_sum (n : ℕ) (a b : Fin n → ℬ) :
    ∑ i, ∑ j, b i * (a i * star (a j)) * star (b j)
      = (∑ i, b i * a i) * star (∑ i, b i * a i) := by
  rw [star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul]
  noncomm_ring

/-- `ϱ = rightMulEquiv` as an nmiu-map `ℬ → 𝒷ᵃ(ℬ)ᵐᵒᵖ`. -/
noncomputable def rightMulNMIU : NMIUMap ℬ (Ba ℬ ℬ)ᵐᵒᵖ where
  toStarAlgHom := (rightMulEquiv (ℬ := ℬ)).toStarAlgHom
  preservesDirSups' := starAlgEquiv_preservesDirSups (rightMulEquiv (ℬ := ℬ))

/-- `h = rightMulEquiv⁻¹` as an ncp-map `𝒷ᵃ(ℬ)ᵐᵒᵖ → ℬ`. -/
noncomputable def rightMulNCP : NCPMap (Ba ℬ ℬ)ᵐᵒᵖ ℬ where
  toCompletelyPositiveMap :=
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      ((rightMulEquiv (ℬ := ℬ)).symm.toStarAlgHom : (Ba ℬ ℬ)ᵐᵒᵖ →⋆ₐ[ℂ] ℬ)
  preservesDirSups' :=
    starAlgEquiv_preservesDirSups (rightMulEquiv (ℬ := ℬ)).symm

@[simp] theorem rightMulNMIU_apply (t : ℬ) :
    rightMulNMIU t = MulOpposite.op (rightMul t) := rfl

@[simp] theorem rightMulNCP_apply (T : (Ba ℬ ℬ)ᵐᵒᵖ) :
    rightMulNCP T = T.unop.1 1 := rfl

set_option maxHeartbeats 800000 in
/-- **Non-vacuity check** for `PaschkeModule`: `ℬ`, with `tprod a b = b·a`,
`ϱ = rightMulEquiv` and `h = rightMulEquiv⁻¹`, is a Paschke module of
`φ = id`.  So `PaschkeModule φ` is inhabited for a non-zero `φ` and the
statements below that quantify over it are not vacuous.

Kept in the tree deliberately: two separate mirroring defects left
`PaschkeModule` *uninhabited* and nine theorems of this file vacuous
(`PROVING-LOG.md`, sessions 14–16), and only a concrete example caught
them. -/
noncomputable def paschkeModuleId : PaschkeModule (ncpMapId (ℬ := ℬ)) where
  X := ℬ
  selfDual := selfDual_self ℬ
  tprod a b := b * a
  compat :=
    { add_left := fun a a' b => by simp [mul_add]
      add_right := fun a b b' => by simp [add_mul]
      smul_complex := fun c a b => by simp [mul_smul_comm]
      smul_action := fun a b c => by simp [smul_eq_mul, mul_assoc]
      bound := ⟨1, one_pos, fun n a b => by
        simp only [ncpMapId_apply, one_mul]
        rw [gram_id_sum, CStarRing.norm_self_mul_star]
        exact le_of_eq (pow_two ‖∑ i, b i * a i‖)⟩ }
  inner_tprod := fun a a' b b' => by
    show (b' * a') * star (b * a) = b' * (a' * star a) * star b
    rw [star_mul]
    noncomm_ring
  univ := by
    intro Y _ _ _ _ _ hY T hT
    have hTzero : ∀ a : ℬ, T a 0 = 0 := by
      intro a
      have h := hT.add_right a 0 0
      rw [add_zero] at h
      have h2 : T a 0 + T a 0 = T a 0 + 0 := by rw [add_zero]; exact h.symm
      exact add_left_cancel h2
    have hTneg : ∀ a b : ℬ, T a (-b) = -T a b := by
      intro a b
      have h := hT.add_right a b (-b)
      rw [add_neg_cancel, hTzero] at h
      exact eq_neg_of_add_eq_zero_right h.symm
    obtain ⟨r, hr0, hr⟩ := hT.bound
    have hkey : ∀ b a : ℬ, T (b * a) 1 = T a b := by
      intro b a
      have h := hr 2 ![b * a, a] ![1, -b]
      simp only [ncpMapId_apply] at h
      rw [gram_id_sum] at h
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] at h
      rw [show ((1 : ℬ) * (b * a) + -b * a) = 0 from by noncomm_ring] at h
      simp only [star_zero, zero_mul, norm_zero, mul_zero] at h
      have h0 : ‖T (b * a) 1 + T a (-b)‖ = 0 := by
        have hnn := norm_nonneg (T (b * a) 1 + T a (-b))
        nlinarith
      have h1 : T (b * a) 1 + T a (-b) = 0 := norm_eq_zero.mp h0
      rw [hTneg, ← sub_eq_add_neg] at h1
      exact sub_eq_zero.mp h1
    have hnormbd : ∀ x : ℬ, ‖T x 1‖ ≤ Real.sqrt r * ‖x‖ := by
      intro x
      have h := hr 1 ![x] ![1]
      simp only [ncpMapId_apply] at h
      rw [gram_id_sum] at h
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
        Matrix.cons_val_zero, one_mul] at h
      rw [CStarRing.norm_self_mul_star] at h
      have h2 := Real.sqrt_le_sqrt h
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hr0.le,
        Real.sqrt_mul_self (norm_nonneg _)] at h2
    refine ⟨fun x => T x 1,
      ⟨⟨Real.sqrt r,
        { add := fun x x' => hT.add_left x x' 1
          smul_complex := fun c x => hT.smul_complex c x 1
          smul := fun b x => by
            show T (b * x) 1 = b • T x 1
            rw [hkey, hT.smul_action, mul_one]
          bound := fun x => by
            rw [cstarBInner_norm, cstarBInner_norm]
            exact hnormbd x }⟩,
       fun a b => hkey b a⟩, ?_⟩
    intro T'' hT''
    funext x
    have h := hT''.2 x 1
    rw [one_mul] at h
    exact h
  ρ := rightMulNMIU
  ρ_tprod := fun a₀ a b => by
    rw [rightMulNMIU_apply]
    show (b * a) * a₀ = b * (a * a₀)
    rw [mul_assoc]
  h := rightMulNCP
  h_def := fun T => by
    rw [rightMulNCP_apply]
    show T.unop.1 1 = (T.unop.1 ((1 : ℬ) * 1)) * star ((1 : ℬ) * 1)
    rw [mul_one, star_one, mul_one]

end Inhabited

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

/-! ### Auxiliary: ncp-maps compose

`Theses/B/Dils/Stinespring.lean` and `Theses/B/Dils/Pure.lean` carry the same
two constructions, both as `private` declarations, so they are repeated here
rather than exported (a merge is noted in those files' headers). -/

/-- An ncp-map, as a positive linear map. -/
private noncomputable def corrPos {P Q : Type u} [CStarAlgebra P] [PartialOrder P]
    [StarOrderedRing P] [CStarAlgebra Q] [PartialOrder Q] [StarOrderedRing Q]
    (f : NCPMap P Q) : P →ₚ[ℂ] Q where
  toLinearMap := f.toCompletelyPositiveMap.toLinearMap
  monotone' := fun x y hxy => by
    have hcp : IsCompletelyPositiveMap f.toCompletelyPositiveMap.toLinearMap :=
      (cp_iff _).out 1 0 |>.mp fun N M hM =>
        f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
    have h := astara_pos_basic_2_cp _ hcp (y - x) (sub_nonneg.mpr hxy)
    rw [map_sub] at h
    exact sub_nonneg.mp h

/-- The composition of two ncp-maps is an ncp-map. -/
private theorem exists_corrComp {P Q R : Type u} [CStarAlgebra P] [PartialOrder P]
    [StarOrderedRing P] [CStarAlgebra Q] [PartialOrder Q] [StarOrderedRing Q]
    [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
    (f : NCPMap Q R) (g : NCPMap P Q) :
    ∃ k : NCPMap P R, ∀ a, k a = f (g a) := by
  have hLgcp : IsCompletelyPositiveMap g.toCompletelyPositiveMap.toLinearMap :=
    (cp_iff _).out 1 0 |>.mp fun N M hM =>
      g.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hLfcp : IsCompletelyPositiveMap f.toCompletelyPositiveMap.toLinearMap :=
    (cp_iff _).out 1 0 |>.mp fun N M hM =>
      f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  exact ⟨{ toCompletelyPositiveMap :=
             { toLinearMap := f.toCompletelyPositiveMap.toLinearMap.comp
                 g.toCompletelyPositiveMap.toLinearMap
               map_cstarMatrix_nonneg' :=
                 (cp_iff _).out 0 1 |>.mp (cp_comp _ _ hLgcp hLfcp) }
           preservesDirSups' :=
             preservesDirSups_pmap_comp (corrPos g) g.preservesDirSups'
               (corrPos f) f.preservesDirSups' },
    fun _ => rfl⟩

/-- **157IV** (`paschke-correspondence`, dils.tex:3950, Theorem), part 1:
for `t` in `[0,1]` of the commutant of `ϱ(𝒜)`, the map `φ_t` lies in
`[0, φ]_ncp`.

The thesis's argument (157V) is transcribed: `√t` again commutes with
`ϱ(𝒜)`, so `φ_t(a) = h(√t ϱ(a) √t)` is the composite of the three ncp-maps
`ϱ`, `ad_{√t}` and `h`; and `φ − φ_t = φ_{1−t}` is ncp by the same argument
applied to `1 − t`. -/
theorem paschke_correspondence_mem [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ) (D : PaschkeTriple 𝒜 ℬ)
    (hD : IsPaschkeDilationOf D ⇑φ) (t : D.P)
    (ht : t ∈ commutant D.P (Set.range ⇑D.ρ)) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    phiT D t ∈ ncpInterval ⇑φ := by
  have : VonNeumannAlgebra D.P := D.vn
  -- `ϱ` as an ncp-map: a ∗-homomorphism is completely positive (**34IV**.3)
  obtain ⟨ρN, hρN⟩ : ∃ ρN : NCPMap 𝒜 D.P, ∀ a, ρN a = D.ρ a := by
    refine ⟨{ toCompletelyPositiveMap :=
                { toLinearMap := (D.ρ.toStarAlgHom : 𝒜 →ₐ[ℂ] D.P).toLinearMap
                  map_cstarMatrix_nonneg' := by
                    refine (cp_iff _).out 0 1 |>.mp (cp_of_mi _ ?_ ?_)
                    · intro x y; exact map_mul D.ρ.toStarAlgHom x y
                    · intro x; exact map_star D.ρ.toStarAlgHom x }
              preservesDirSups' := D.ρ.preservesDirSups' }, fun _ => rfl⟩
  have htc : ∀ a : 𝒜, t * D.ρ a = D.ρ a * t := fun a => (ht _ ⟨a, rfl⟩).symm
  -- the key step: `a ↦ h(s·ϱ(a)) = h(√s ϱ(a) √s)` is ncp
  have key : ∀ s : D.P, 0 ≤ s → (∀ a : 𝒜, s * D.ρ a = D.ρ a * s) →
      ∃ δ : NCPMap 𝒜 ℬ, ∀ a : 𝒜, δ a = D.h (s * D.ρ a) := by
    intro s hs0 hsc
    have hrnn : (0 : D.P) ≤ CFC.sqrt s := CFC.sqrt_nonneg s
    have hrsa : IsSelfAdjoint (CFC.sqrt s) := IsSelfAdjoint.of_nonneg hrnn
    have hr2 : CFC.sqrt s * CFC.sqrt s = s := CFC.sqrt_mul_sqrt_self s hs0
    have hrc : ∀ a : 𝒜, CFC.sqrt s * D.ρ a = D.ρ a * CFC.sqrt s := fun a =>
      (Commute.cfcₙ_nnreal (hsc a) NNReal.sqrt : Commute (CFC.sqrt s) (D.ρ a))
    -- `ad_{√s}` as an ncp-map: **34V**.1 for `cp`, **44VIII** for normality
    obtain ⟨adN, hadN⟩ : ∃ k : NCPMap D.P D.P,
        ∀ x, k x = star (CFC.sqrt s) * x * CFC.sqrt s := by
      refine ⟨{ toCompletelyPositiveMap :=
                  { toLinearMap :=
                      { toFun := fun x => star (CFC.sqrt s) * x * CFC.sqrt s
                        map_add' := fun x y => by noncomm_ring
                        map_smul' := fun c x => by simp }
                    map_cstarMatrix_nonneg' := ?_ }
                preservesDirSups' := ?_ }, fun _ => rfl⟩
      · refine (cp_iff _).out 0 1 |>.mp ?_
        intro n c b
        have h := ad_cp_1 (CFC.sqrt s) n c b
        simpa [mul_assoc] using h
      · intro Dset s' hne hdir hlub
        have hb : BddAbove Dset := ⟨s', hlub.1⟩
        have hsd : dirSup Dset ⟨hne, hdir, hb⟩ = s' :=
          (isLUB_dirSup Dset ⟨hne, hdir, hb⟩).unique hlub
        have h := ad_normal (CFC.sqrt s) Dset ⟨hne, hdir, hb⟩
        rw [hsd] at h
        exact h
    obtain ⟨k, hk⟩ := exists_corrComp D.h adN
    obtain ⟨δ, hδ⟩ := exists_corrComp k ρN
    refine ⟨δ, fun a => ?_⟩
    rw [hδ, hk, hadN, hρN, hrsa.star_eq]
    congr 1
    calc CFC.sqrt s * D.ρ a * CFC.sqrt s
        = CFC.sqrt s * (D.ρ a * CFC.sqrt s) := by rw [mul_assoc]
      _ = CFC.sqrt s * (CFC.sqrt s * D.ρ a) := by rw [← hrc]
      _ = s * D.ρ a := by rw [← mul_assoc, hr2]
  obtain ⟨δ₁, hδ₁⟩ := key t h0 htc
  obtain ⟨δ₂, hδ₂⟩ := key (1 - t) (sub_nonneg.mpr h1)
    (fun a => by rw [sub_mul, mul_sub, one_mul, mul_one, htc a])
  refine ⟨⟨δ₁, fun a => ?_⟩, ⟨δ₂, fun a => ?_⟩⟩
  · rw [zero_add]
    exact (hδ₁ a).symm
  · rw [hδ₂]
    have hadd : (D.h (t * D.ρ a + (1 - t) * D.ρ a) : ℬ)
        = D.h (t * D.ρ a) + D.h ((1 - t) * D.ρ a) :=
      map_add D.h.toCompletelyPositiveMap.toLinearMap _ _
    rw [show t * D.ρ a + (1 - t) * D.ρ a = D.ρ a by noncomm_ring] at hadd
    rw [show (phiT D t a : ℬ) = D.h (t * D.ρ a) from rfl, ← hadd, hD.1 a]

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
