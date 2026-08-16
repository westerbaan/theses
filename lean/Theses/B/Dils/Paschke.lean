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
open scoped TensorProduct
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

/-! ### Maps of the opposite algebras

`op : A → Aᵐᵒᵖ` is a ∗-**anti**-isomorphism, and is *not* completely
positive — for `A = M₂` it is the transpose, the standard counterexample.
But transporting a map on *both* sides, `f ↦ fᵐᵒᵖ`, is: `Mₙ(Aᵐᵒᵖ)` is
∗-isomorphic to `Mₙ(A)ᵐᵒᵖ` by `M ↦ (Mᵀ)ᵒᵖ`, under which `(fᵐᵒᵖ)ₙ` becomes
`(fₙ)ᵐᵒᵖ`.  Concretely, the Gram sum of `fᵐᵒᵖ` at `(aᵢ, bᵢ)` unops to the
Gram sum of `f` at `(aᵢ*, bᵢ*)` with the two summation indices exchanged,
which is all the proof below does.  This is what carries `ad_S` (an ncp-map
of the algebras `𝒷ᵃ(X)`) over to the `ᵐᵒᵖ`s on which `ρ` and `h` live, in
**154III**.5. -/

section MopMaps

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A linear map transported to the opposite algebras. -/
noncomputable def mopLinear (f : A →ₗ[ℂ] B) : Aᵐᵒᵖ →ₗ[ℂ] Bᵐᵒᵖ :=
  (MulOpposite.opLinearEquiv ℂ).toLinearMap.comp
    (f.comp ((MulOpposite.opLinearEquiv ℂ).symm.toLinearMap))

set_option linter.unusedSectionVars false in
@[simp] theorem mopLinear_apply (f : A →ₗ[ℂ] B) (x : Aᵐᵒᵖ) :
    mopLinear f x = MulOpposite.op (f (MulOpposite.unop x)) := rfl

set_option linter.unusedSectionVars false in
theorem mop_nonneg_iff (x : Aᵐᵒᵖ) : (0 : Aᵐᵒᵖ) ≤ x ↔ 0 ≤ MulOpposite.unop x :=
  Iff.rfl

set_option linter.unusedSectionVars false in
theorem isLUB_mop {S : Set B} {t : B} (h : IsLUB S t) :
    IsLUB (MulOpposite.op '' S) (MulOpposite.op t) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact h.1 hx
  · intro u hu
    exact h.2 fun x hx => hu ⟨x, hx, rfl⟩

set_option linter.unusedSectionVars false in
theorem mopLinear_cp (f : A →ₗ[ℂ] B) (hf : IsCompletelyPositiveMap f) :
    IsCompletelyPositiveMap (mopLinear f) := by
  intro n a b
  rw [mop_nonneg_iff]
  have h := hf n (fun i => star (MulOpposite.unop (a i)))
    (fun i => star (MulOpposite.unop (b i)))
  simp only [star_star] at h
  rw [show MulOpposite.unop
      (∑ i, ∑ j, star (b i) * mopLinear f (star (a i) * a j) * b j)
      = ∑ i, ∑ j, MulOpposite.unop (b j) *
          f (MulOpposite.unop (a j) * star (MulOpposite.unop (a i))) *
          star (MulOpposite.unop (b i)) from ?_]
  · rw [Finset.sum_comm]
    exact h
  · simp only [Finset.unop_sum, MulOpposite.unop_mul, MulOpposite.unop_star,
      mopLinear_apply, MulOpposite.unop_op, mul_assoc]

set_option linter.unusedSectionVars false in
theorem mopLinear_normal (f : A →ₗ[ℂ] B) (hf : PreservesDirSups ⇑f) :
    PreservesDirSups ⇑(mopLinear f) := by
  intro D s hne hdir hlub
  have hlub' : IsLUB (selfAdjointUnop '' D) (selfAdjointUnop s) :=
    selfAdjointUnop.isLUB_image'.mpr hlub
  have h := hf (selfAdjointUnop '' D) (selfAdjointUnop s) (hne.image _)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
      exact ⟨selfAdjointUnop z, ⟨z, hz, rfl⟩, hxz, hyz⟩) hlub'
  rw [Set.image_image] at h
  have h2 := isLUB_mop h
  rw [Set.image_image] at h2
  exact h2

/-- An ncp-map transported to the opposite algebras.  Unlike `op` itself
(the transpose on `M₂`), `f ↦ fᵐᵒᵖ` **does** preserve complete positivity:
the Gram sum of `fᵐᵒᵖ` at `(aᵢ, bᵢ)` is the Gram sum of `f` at
`(aᵢ*, bᵢ*)` with the two summation indices exchanged. -/
noncomputable def ncpMop (f : NCPMap A B) : NCPMap Aᵐᵒᵖ Bᵐᵒᵖ where
  toCompletelyPositiveMap :=
    { toLinearMap := mopLinear f.toCompletelyPositiveMap.toLinearMap
      map_cstarMatrix_nonneg' :=
        (cp_iff _).out 0 1 |>.mp (mopLinear_cp _
          ((cp_iff _).out 1 0 |>.mp fun N M hM =>
            f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM)) }
  preservesDirSups' := mopLinear_normal _ f.preservesDirSups'

set_option linter.unusedSectionVars false in
@[simp] theorem ncpMop_apply (f : NCPMap A B) (x : Aᵐᵒᵖ) :
    ncpMop f x = MulOpposite.op (f (MulOpposite.unop x)) := rfl

end MopMaps

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


/-! ### The construction of `𝒜 ⊗_φ ℬ` (**154IV**–**154VI**)

The thesis's own proof of **154III**, transcribed.  `𝒜 ⊙ ℬ` is Mathlib's
`𝒜 ⊗[ℂ] ℬ` carrying the ℬ-action `b·(a ⊗ b') = a ⊗ (b b')` and the
φ-inner product `⟨a ⊗ b, a' ⊗ b'⟩ = b' φ(a' a*) b*` (mirrored, see the head
of the file); **150II** `dils_completion` completes it, **151Ia**
`selfdual_completion_univ` gives part 1, and parts 2 and 3 are built on top.

Note that **no conjugation of the ℂ-action** is needed on `𝒜 ⊙ ℬ` itself:
the mirroring is absorbed entirely into `tprod a b = a ⊗ₜ b` together with
the `star`s in `inner_tprod`, which is what makes the pairing
conjugate-linear in its first argument.

The one step the thesis takes for granted and we do not have is normality of
`ϱ`: dils.tex proves it from **49IV** `mn-vna` (the entrywise `Mₙφ` is
normal, and `M ↦ ∑ᵢⱼ aᵢ* Mᵢⱼ aⱼ` preserves suprema), and **both** halves of
49IV that it uses — `mn_vna_2`'s third clause and `mn_vna_3` — are still
`sorry` in `A/VN/Basic.lean`.  The route here avoids them: the vector form
`d ↦ ∑ᵢⱼ bᵢ φ(aᵢ d aⱼ*) bⱼ*` is written by *double* polarisation
(`gram_polarization`, i.e. **44II** through `mult_polarization`, once in the
`aᵢ` and once in the `bᵢ`) as a ℂ-combination of the np-functionals
`d ↦ ω(w* φ(v* d v) w)`, and `preservesDirSups_of_np_combination` turns that
into normality by reading it off the *convergence* of the monotone nets
rather than off preservation of suprema, which a ℂ-combination does not
enjoy. -/

/-- Right slot of the φ-pairing. -/
noncomputable def ptensR (φ : 𝒜 →ₗ[ℂ] ℬ) (a : 𝒜) (b : ℬ) :
    (𝒜 ⊗[ℂ] ℬ) →ₗ[ℂ] ℬ :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ (fun (a' : 𝒜) (b' : ℬ) => b' * φ (a' * a) * b)
    (fun a₁ a₂ b' => by rw [add_mul, map_add, mul_add, add_mul])
    (fun c a' b' => by rw [smul_mul_assoc, map_smul, mul_smul_comm, smul_mul_assoc])
    (fun a' b₁ b₂ => by rw [add_mul, add_mul])
    (fun c a' b' => by rw [smul_mul_assoc, smul_mul_assoc])

@[simp] theorem ptensR_tmul (φ : 𝒜 →ₗ[ℂ] ℬ) (a a' : 𝒜) (b b' : ℬ) :
    ptensR φ a b (a' ⊗ₜ[ℂ] b') = b' * φ (a' * a) * b := rfl

/-- The ℂ-bilinear pairing `⟨a ⊗ b, a' ⊗ b'⟩ = b' * φ (a' * a) * b`. -/
noncomputable def ptensPair (φ : 𝒜 →ₗ[ℂ] ℬ) :
    (𝒜 ⊗[ℂ] ℬ) →ₗ[ℂ] (𝒜 ⊗[ℂ] ℬ) →ₗ[ℂ] ℬ :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ (fun (a : 𝒜) (b : ℬ) => ptensR φ a b)
    (fun a₁ a₂ b => by
      refine TensorProduct.ext' fun a' b' => ?_
      simp [mul_add, map_add, add_mul])
    (fun c a b => by
      refine TensorProduct.ext' fun a' b' => ?_
      simp [mul_smul_comm, smul_mul_assoc])
    (fun a b₁ b₂ => by
      refine TensorProduct.ext' fun a' b' => ?_
      simp [mul_add])
    (fun c a b => by
      refine TensorProduct.ext' fun a' b' => ?_
      simp [mul_smul_comm])

@[simp] theorem ptensPair_tmul (φ : 𝒜 →ₗ[ℂ] ℬ) (a a' : 𝒜) (b b' : ℬ) :
    ptensPair φ (a ⊗ₜ[ℂ] b) (a' ⊗ₜ[ℂ] b') = b' * φ (a' * a) * b := rfl


/-- Every element of `𝒜 ⊗[ℂ] ℬ` is a finite sum of elementary tensors,
indexed by a `Fin n`. -/
theorem exists_fin_tmul (x : 𝒜 ⊗[ℂ] ℬ) :
    ∃ (n : ℕ) (a : Fin n → 𝒜) (b : Fin n → ℬ), x = ∑ i, a i ⊗ₜ[ℂ] b i := by
  classical
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  refine ⟨S.card, fun i => ((S.equivFin.symm i : 𝒜 × ℬ)).1,
    fun i => ((S.equivFin.symm i : 𝒜 × ℬ)).2, ?_⟩
  rw [← Finset.sum_coe_sort S (fun p : 𝒜 × ℬ => p.1 ⊗ₜ[ℂ] p.2)]
  exact (Fintype.sum_equiv S.equivFin.symm _ _ (fun i => rfl)).symm

/-- ℬ-valued Gram positivity for an ncp-map, in the mirrored (outer-star)
shape used by `PhiCompatible.bound`: `0 ≤ ∑ᵢⱼ bᵢ φ(aᵢaⱼ*)bⱼ*`.  This is
complete positivity of `φ` (`cp_iff … |>.out 1 0`) applied to the families
`(aᵢ*)` and `(bᵢ*)`. -/
theorem phi_gram_nonneg (φ : NCPMap 𝒜 ℬ) {ι : Type*} [Fintype ι]
    (a : ι → 𝒜) (b : ι → ℬ) :
    (0 : ℬ) ≤ ∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j) := by
  classical
  set ψ : 𝒜 →ₗ[ℂ] ℬ := φ.toCompletelyPositiveMap.toLinearMap with hψdef
  have hψ : ⇑φ = ⇑ψ := rfl
  have hcp : IsCompletelyPositiveMap ψ :=
    ((cp_iff _).out 1 0).mp fun N A hA =>
      φ.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N A hA
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he
  have h := hcp (Fintype.card ι) (fun i => star (a (e i))) (fun i => star (b (e i)))
  simp only [star_star] at h
  rw [hψ]
  have h2 : ∑ i, ∑ j, b (e i) * ψ (a (e i) * star (a (e j))) * star (b (e j))
      = ∑ i, ∑ j, b i * ψ (a i * star (a j)) * star (b j) := by
    rw [Fintype.sum_equiv e (fun i => ∑ j, b (e i) * ψ (a (e i) * star (a (e j))) * star (b (e j)))
      (fun i => ∑ j, b i * ψ (a i * star (a j)) * star (b j))]
    intro i
    exact Fintype.sum_equiv e _ _ (fun j => rfl)
  rwa [h2] at h

/-- The right ℬ-action on `𝒜 ⊙ ℬ`, mirrored: `b • (a ⊗ b') = a ⊗ (b b')`. -/
noncomputable local instance ptensSMul : SMul ℬ (𝒜 ⊗[ℂ] ℬ) where
  smul b := LinearMap.lTensor 𝒜 (LinearMap.mulLeft ℂ b)

theorem ptens_smul_tmul (b : ℬ) (a : 𝒜) (b' : ℬ) :
    b • (a ⊗ₜ[ℂ] b') = a ⊗ₜ[ℂ] (b * b') := rfl

@[simp] theorem ptens_smul_zero (b : ℬ) : b • (0 : 𝒜 ⊗[ℂ] ℬ) = 0 :=
  map_zero (LinearMap.lTensor 𝒜 (LinearMap.mulLeft ℂ b))

theorem ptens_smul_add (b : ℬ) (x y : 𝒜 ⊗[ℂ] ℬ) :
    b • (x + y) = b • x + b • y :=
  map_add (LinearMap.lTensor 𝒜 (LinearMap.mulLeft ℂ b)) x y

theorem ptens_smul_sum {ι : Type*} (b : ℬ) (s : Finset ι) (f : ι → 𝒜 ⊗[ℂ] ℬ) :
    b • (∑ i ∈ s, f i) = ∑ i ∈ s, b • f i :=
  map_sum (LinearMap.lTensor 𝒜 (LinearMap.mulLeft ℂ b)) f s

/-- The φ-inner product on `𝒜 ⊙ ℬ` (**154IV**, mirrored):
`⟨a ⊗ b, a' ⊗ b'⟩ = b' φ(a' a*) b*`. -/
noncomputable def ptensBInner (φ : NCPMap 𝒜 ℬ) : BInner ℬ (𝒜 ⊗[ℂ] ℬ) where
  inner x y := ptensPair (φ.toCompletelyPositiveMap.toLinearMap) (star x) y
  inner_add_right x y z := map_add _ _ _
  inner_op_smul_right b x y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b₀ => rw [ptens_smul_tmul]; simp [mul_assoc]
        | add x₁ x₂ h₁ h₂ =>
            rw [star_add, map_add, LinearMap.add_apply, LinearMap.add_apply, h₁, h₂,
              mul_add]
    | add y₁ y₂ h₁ h₂ => rw [ptens_smul_add, map_add, map_add, h₁, h₂, mul_add]
  inner_smul_right_complex c x y := map_smul _ _ _
  star_inner x y := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a' b' =>
            have hst : star (φ (a' * star a)) = φ (a * star a') := by
              rw [← ncp_star φ, star_mul, star_star]
            show star (b' * φ (a' * star a) * star b) = b * φ (a * star a') * star b'
            rw [star_mul, star_mul, star_star, hst, mul_assoc]
        | add y₁ y₂ h₁ h₂ =>
            rw [map_add, star_add, h₁, h₂, star_add, map_add, LinearMap.add_apply]
    | add x₁ x₂ h₁ h₂ =>
        rw [star_add, map_add, LinearMap.add_apply, star_add, h₁, h₂, map_add]
  inner_self_nonneg x := by
    obtain ⟨n, a, b, rfl⟩ := exists_fin_tmul x
    have hexp : ptensPair (φ.toCompletelyPositiveMap.toLinearMap)
        (star (∑ i, a i ⊗ₜ[ℂ] b i)) (∑ i, a i ⊗ₜ[ℂ] b i)
          = ∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j) := by
      rw [star_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      show ptensPair _ (star (a j) ⊗ₜ[ℂ] star (b j)) (a i ⊗ₜ[ℂ] b i) = _
      rw [ptensPair_tmul]
      rfl
    show (0 : ℬ) ≤ ptensPair _ (star (∑ i, a i ⊗ₜ[ℂ] b i)) (∑ i, a i ⊗ₜ[ℂ] b i)
    rw [hexp]
    exact phi_gram_nonneg φ a b

@[simp] theorem ptensBInner_tmul (φ : NCPMap 𝒜 ℬ) (a a' : 𝒜) (b b' : ℬ) :
    (ptensBInner φ).inner (a ⊗ₜ[ℂ] b) (a' ⊗ₜ[ℂ] b') = b' * φ (a' * star a) * star b := rfl

section Carrier

variable [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
  (φ : NCPMap 𝒜 ℬ) (E : SelfDualCompletion.{u, u, u} (ptensBInner φ))

/-- `η` as an additive map, so that it commutes with finite sums. -/
noncomputable def etaHom : (𝒜 ⊗[ℂ] ℬ) →+ E.X where
  toFun := E.η
  map_zero' := by simpa using E.η_smul_complex 0 0
  map_add' := E.η_add

@[simp] theorem etaHom_apply (x : 𝒜 ⊗[ℂ] ℬ) : etaHom φ E x = E.η x := rfl

/-- The elementary tensor `a ⊗ b` of `𝒜 ⊗_φ ℬ` (mirrored). -/
noncomputable def ptprod (a : 𝒜) (b : ℬ) : E.X := E.η (a ⊗ₜ[ℂ] b)

theorem inner_ptprod (a a' : 𝒜) (b b' : ℬ) :
    inner ℬ (ptprod φ E a b) (ptprod φ E a' b') = b' * φ (a' * star a) * star b :=
  E.η_inner _ _

theorem eta_sum {n : ℕ} (a : Fin n → 𝒜) (b : Fin n → ℬ) :
    E.η (∑ i, a i ⊗ₜ[ℂ] b i) = ∑ i, ptprod φ E (a i) (b i) :=
  map_sum (etaHom φ E) _ _

/-- The Gram identity behind the φ-compatibility of `⊗`: with `r = 1` the
bound of **154II** holds with equality. -/
theorem norm_sq_sum_ptprod {n : ℕ} (a : Fin n → 𝒜) (b : Fin n → ℬ) :
    ‖∑ i, ptprod φ E (a i) (b i)‖ ^ 2
      = ‖∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j)‖ := by
  rw [← eta_sum, CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ),
    Real.sq_sqrt (norm_nonneg _), E.η_inner]
  congr 1
  show (ptensBInner φ).inner (∑ i, a i ⊗ₜ[ℂ] b i) (∑ i, a i ⊗ₜ[ℂ] b i) = _
  show ptensPair (φ.toCompletelyPositiveMap.toLinearMap)
      (star (∑ i, a i ⊗ₜ[ℂ] b i)) (∑ i, a i ⊗ₜ[ℂ] b i) = _
  rw [star_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ptensPair _ (star (a j) ⊗ₜ[ℂ] star (b j)) (a i ⊗ₜ[ℂ] b i) = _
  rw [ptensPair_tmul]
  rfl

theorem phiCompatible_ptprod : PhiCompatible ⇑φ (ptprod φ E) where
  add_left a a' b := by
    show E.η ((a + a') ⊗ₜ[ℂ] b) = _
    rw [TensorProduct.add_tmul, E.η_add]; rfl
  add_right a b b' := by
    show E.η (a ⊗ₜ[ℂ] (b + b')) = _
    rw [TensorProduct.tmul_add, E.η_add]; rfl
  smul_complex c a b := by
    show E.η ((c • a) ⊗ₜ[ℂ] b) = _
    rw [← TensorProduct.smul_tmul', E.η_smul_complex]; rfl
  smul_action a b c := by
    show _ = E.η (a ⊗ₜ[ℂ] (c * b))
    rw [← ptens_smul_tmul, E.η_smul]; rfl
  bound := ⟨1, one_pos, fun n a b => by
    rw [one_mul, norm_sq_sum_ptprod]⟩

end Carrier

section Univ

variable [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
  (φ : NCPMap 𝒜 ℬ) (E : SelfDualCompletion.{u, u, u} (ptensBInner φ))

variable {Y : Type u} [NormedAddCommGroup Y] [Module ℂ Y] [SMul ℬ Y]
  [CStarModule ℬ Y]

/-- A φ-compatible map is ℂ-linear in its ℬ-argument as well: `c • b` is
`(c·1)b` and the ℬ-action of `c·1` is the ℂ-action (`op_smul_complex_smul`,
`op_one_smul`). -/
theorem PhiCompatible.smul_complex_right {T : 𝒜 → ℬ → Y}
    (hT : PhiCompatible ⇑φ T) (c : ℂ) (a : 𝒜) (b : ℬ) :
    T a (c • b) = c • T a b := by
  have h : (c • (1 : ℬ)) * b = c • b := by rw [smul_mul_assoc, one_mul]
  rw [← h, ← hT.smul_action, op_smul_complex_smul, op_one_smul]

/-- The linear map `T₀ : 𝒜 ⊙ ℬ → Y` determined by a φ-compatible `T`. -/
noncomputable def phiLift {T : 𝒜 → ℬ → Y} (hT : PhiCompatible ⇑φ T) :
    (𝒜 ⊗[ℂ] ℬ) →ₗ[ℂ] Y :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ T hT.add_left hT.smul_complex hT.add_right
    (fun c a b => hT.smul_complex_right φ c a b)

@[simp] theorem phiLift_tmul {T : 𝒜 → ℬ → Y} (hT : PhiCompatible ⇑φ T)
    (a : 𝒜) (b : ℬ) : phiLift φ hT (a ⊗ₜ[ℂ] b) = T a b := rfl

theorem phiLift_op_smul {T : 𝒜 → ℬ → Y} (hT : PhiCompatible ⇑φ T) (b : ℬ)
    (x : 𝒜 ⊗[ℂ] ℬ) : phiLift φ hT (b • x) = b • phiLift φ hT x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [ptens_smul_zero, map_zero, op_smul_zero]
  | tmul a b' => rw [ptens_smul_tmul, phiLift_tmul, phiLift_tmul, hT.smul_action]
  | add x₁ x₂ h₁ h₂ => rw [ptens_smul_add, map_add, map_add, h₁, h₂, op_smul_add]

/-- The φ-compatibility bound, transported to `T₀` and the φ-inner product:
`T₀` is a bounded module map with constant `√r`. -/
theorem phiLift_bounded {T : 𝒜 → ℬ → Y} (hT : PhiCompatible ⇑φ T) :
    ∃ C : ℝ, 0 ≤ C ∧
      IsBoundedModuleMap (ptensBInner φ) (cstarBInner ℬ Y) C (phiLift φ hT) := by
  obtain ⟨r, hr0, hr⟩ := hT.bound
  refine ⟨Real.sqrt r, Real.sqrt_nonneg _,
    { add := fun x y => map_add _ x y
      smul_complex := fun c x => map_smul _ c x
      smul := fun b x => phiLift_op_smul φ hT b x
      bound := fun x => ?_ }⟩
  obtain ⟨n, a, b, rfl⟩ := exists_fin_tmul x
  have hsum : phiLift φ hT (∑ i, a i ⊗ₜ[ℂ] b i) = ∑ i, T (a i) (b i) := by
    rw [map_sum]; rfl
  have hgram : (ptensBInner φ).inner (∑ i, a i ⊗ₜ[ℂ] b i) (∑ i, a i ⊗ₜ[ℂ] b i)
      = ∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j) := by
    show ptensPair (φ.toCompletelyPositiveMap.toLinearMap)
        (star (∑ i, a i ⊗ₜ[ℂ] b i)) (∑ i, a i ⊗ₜ[ℂ] b i) = _
    rw [star_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    show ptensPair _ (star (a j) ⊗ₜ[ℂ] star (b j)) (a i ⊗ₜ[ℂ] b i) = _
    rw [ptensPair_tmul]
    rfl
  show Real.sqrt ‖(inner ℬ (phiLift φ hT _) (phiLift φ hT _) : ℬ)‖
    ≤ Real.sqrt r * Real.sqrt ‖(ptensBInner φ).inner _ _‖
  rw [← CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ), hgram, ← Real.sqrt_mul hr0.le]
  rw [hsum]
  have h1 := Real.sqrt_le_sqrt (hr n a b)
  rwa [Real.sqrt_sq (norm_nonneg _)] at h1

/-- **154III**, part 1: the universal property of `⊗`. -/
theorem ptprod_univ [CompleteSpace Y] (hY : SelfDual ℬ Y) (T : 𝒜 → ℬ → Y)
    (hT : PhiCompatible ⇑φ T) :
    ∃! T' : E.X → Y,
      (∃ C : ℝ, IsBoundedModuleMap (cstarBInner ℬ E.X) (cstarBInner ℬ Y) C T') ∧
        ∀ a b, T' (ptprod φ E a b) = T a b := by
  obtain ⟨C, hC0, hbdd⟩ := phiLift_bounded φ hT
  obtain ⟨T', ⟨hT'bdd, hT'eta⟩, hT'uniq⟩ :=
    selfdual_completion_univ (ptensBInner φ) E hY C (phiLift φ hT) hbdd
  refine ⟨T', ⟨hT'bdd, fun a b => hT'eta _⟩, ?_⟩
  rintro T'' ⟨hT''bdd, hT''tp⟩
  refine hT'uniq _ ⟨hT''bdd, fun v => ?_⟩
  obtain ⟨n, a, b, rfl⟩ := exists_fin_tmul v
  obtain ⟨C'', hC''⟩ := hT''bdd
  have hadd : ∀ (m : ℕ) (f : Fin m → E.X), T'' (∑ i, f i) = ∑ i, T'' (f i) := by
    intro m f
    have h0 : T'' 0 = 0 := by
      have := hC''.smul_complex 0 0
      simpa using this
    induction m with
    | zero => simpa using h0
    | succ k ih =>
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hC''.add, ih]
  rw [eta_sum, hadd, map_sum]
  exact Finset.sum_congr rfl fun i _ => hT''tp (a i) (b i)

end Univ

section Normality

variable {A B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [VonNeumannAlgebra B]

/-- An np-functional converges along the net of a nonempty directed set of
self-adjoint elements to its value at the supremum.  (The idiom of **44VI**
`vna_supremum_uwlimit`, isolated.) -/
theorem npFunctional_tendsto_of_isLUB (τ : NPFunctional A)
    {D : Set (selfAdjoint A)} {s : selfAdjoint A} [Nonempty D]
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hlub : IsLUB D s) :
    Tendsto (fun d : D => (τ ((d : selfAdjoint A) : A) : ℂ)) atTop (𝓝 (τ (s : A))) := by
  have hτ : IsLUB ((fun d : selfAdjoint A => (τ (d : A) : ℂ)) '' D) (τ (s : A)) :=
    τ.preservesDirSups' D s hne hdir hlub
  have himg : ∀ w ∈ (fun d : selfAdjoint A => (τ (d : A) : ℂ)) '' D, w.im = 0 := by
    rintro w ⟨d, -, rfl⟩
    exact npFunctional_im_eq_zero τ d.2
  have hre := isLUB_re_of_isLUB himg hτ
  have hrange : Complex.re '' ((fun d : selfAdjoint A => (τ (d : A) : ℂ)) '' D) =
      Set.range fun d : D => (τ ((d : selfAdjoint A) : A)).re := by
    rw [← Set.image_comp]
    exact (Set.image_eq_range _ _).trans rfl
  rw [hrange] at hre
  have hmono : Monotone fun d : D => (τ ((d : selfAdjoint A) : A)).re := by
    intro d₁ d₂ hd
    exact (Complex.le_def.mp (τ.toPositiveLinearMap.monotone
      (Subtype.coe_le_coe.mpr hd))).1
  have hlim := tendsto_atTop_isLUB hmono hre
  have hcast : ∀ z : ℂ, z.im = 0 → ((z.re : ℂ)) = z := fun z hz =>
    Complex.ext (by simp) (by simp [hz])
  have h2 := (Complex.continuous_ofReal.tendsto _).comp hlim
  simp only [Function.comp_def] at h2
  rw [hcast _ (npFunctional_im_eq_zero τ s.2)] at h2
  exact h2.congr fun d => hcast _ (npFunctional_im_eq_zero τ (d : selfAdjoint A).2)

/-- A monotone `g : A → ℂ` which is a ℂ-linear combination of np-functionals
is **normal**.

This is the mechanism behind the normality of `ϱ` in **154III**.2: the
vector form `d ↦ ∑ᵢⱼ bᵢ φ(aᵢ d aⱼ*) bⱼ*` is not itself a composite of
np-maps, but polarisation in both `a` and `b` writes it as a ℂ-combination
of the np-functionals `d ↦ ω(w φ(v d v*) w*)`.  Normality is then read off
from convergence of the monotone nets rather than from preservation of
suprema, which a ℂ-combination does not enjoy. -/
theorem preservesDirSups_of_np_combination {ι : Type*} (t : Finset ι)
    (g : A → ℂ) (hmono : ∀ {x y : A}, x ≤ y → g x ≤ g y)
    (c : ι → ℂ) (τ : ι → NPFunctional A)
    (hcomb : ∀ a : A, g a = ∑ k ∈ t, c k * τ k a) :
    PreservesDirSups g := by
  classical
  intro D s hne hdir hlub
  have hub : ∀ w ∈ (fun d : selfAdjoint A => g (d : A)) '' D, w ≤ g (s : A) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hmono (Subtype.coe_le_coe.mpr (hlub.1 hd))
  refine ⟨hub, fun z hz => ?_⟩
  obtain ⟨d₀, hd₀⟩ := hne
  have : Nonempty D := ⟨⟨d₀, hd₀⟩⟩
  have : IsDirectedOrder D := directedOn_iff_isDirectedOrder.mp hdir
  have hg : Tendsto (fun d : D => g ((d : selfAdjoint A) : A)) atTop (𝓝 (g (s : A))) := by
    simp only [hcomb]
    exact tendsto_finsetSum _ fun k _ =>
      Tendsto.const_mul _ (npFunctional_tendsto_of_isLUB (τ k) ⟨d₀, hd₀⟩ hdir hlub)
  have hzd : ∀ d : D, g ((d : selfAdjoint A) : A) ≤ z :=
    fun d => hz ⟨(d : selfAdjoint A), d.2, rfl⟩
  have hre : (g (s : A)).re ≤ z.re := by
    have h1 : Tendsto (fun d : D => (g ((d : selfAdjoint A) : A)).re) atTop
        (𝓝 (g (s : A)).re) := by
      simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp hg
    exact le_of_tendsto h1 (Filter.Eventually.of_forall fun d => (Complex.le_def.mp (hzd d)).1)
  have him : (g (s : A)).im = z.im := by
    have h1 : Tendsto (fun d : D => (g ((d : selfAdjoint A) : A)).im) atTop
        (𝓝 (g (s : A)).im) := by
      simpa [Function.comp_def] using (Complex.continuous_im.tendsto _).comp hg
    exact tendsto_nhds_unique h1
      (tendsto_const_nhds.congr fun d => ((Complex.le_def.mp (hzd d)).2).symm)
  exact Complex.le_def.mpr ⟨hre, him⟩

end Normality

section Rho

variable [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
  (φ : NCPMap 𝒜 ℬ) (E : SelfDualCompletion.{u, u, u} (ptensBInner φ))

/-- The right 𝒜-action on `𝒜 ⊙ ℬ` (mirrored): `a ⊗ b ↦ (a a₀) ⊗ b`. -/
noncomputable def prmul (a₀ : 𝒜) : (𝒜 ⊗[ℂ] ℬ) →ₗ[ℂ] (𝒜 ⊗[ℂ] ℬ) :=
  LinearMap.rTensor ℬ (LinearMap.mulRight ℂ a₀)

@[simp] theorem prmul_tmul (a₀ a : 𝒜) (b : ℬ) :
    prmul a₀ (a ⊗ₜ[ℂ] b) = (a * a₀) ⊗ₜ[ℂ] b := rfl

/-- A bounded module map on a self-dual Hilbert ℬ-module is adjointable
(**152VIII**), hence an element of `𝒷ᵃ(X)`. -/
theorem exists_ba_of_boundedModuleMap {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X] [CompleteSpace X]
    (hX : SelfDual ℬ X) (S : X → X) (C : ℝ)
    (hS : IsBoundedModuleMap (cstarBInner ℬ X) (cstarBInner ℬ X) C S) :
    ∃ R : Ba ℬ X, ∀ x, R.1 x = S x := by
  set Sl : X →ₗ[ℂ] X :=
    { toFun := S, map_add' := hS.add, map_smul' := hS.smul_complex } with hSl
  have hbd : ∀ x, ‖Sl x‖ ≤ max C 0 * ‖x‖ := by
    intro x
    have h := hS.bound x
    rw [cstarBInner_norm, cstarBInner_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  obtain ⟨T', hT'⟩ :=
    hilbmod_adjoint_exists hX (Sl.mkContinuous (max C 0) hbd) hS.smul
  exact ⟨⟨Sl.mkContinuous (max C 0) hbd, ⟨⇑T', hT'⟩⟩, fun x => rfl⟩

/-- **154III**.2, existence: the operator `ϱ(a₀)`. -/
theorem exists_prho (a₀ : 𝒜) :
    ∃ R : Ba ℬ E.X, ∀ (a : 𝒜) (b : ℬ),
      R.1 (ptprod φ E a b) = ptprod φ E (a * a₀) b := by
  obtain ⟨T', ⟨⟨C, hC⟩, hTtp⟩, -⟩ :=
    ptprod_univ φ E E.selfDual _ ((phiCompatible_ptprod φ E).mul_right φ a₀)
  obtain ⟨R, hR⟩ := exists_ba_of_boundedModuleMap E.selfDual T' C hC
  exact ⟨R, fun a b => by rw [hR, hTtp]⟩

/-- Adjointable operators agreeing on all elementary tensors are equal
(**152IX**.2 through the ultranorm-dense image of `η`). -/
theorem ba_ext_ptprod {S R : Ba ℬ E.X}
    (h : ∀ (a : 𝒜) (b : ℬ), S.1 (ptprod φ E a b) = R.1 (ptprod φ E a b)) : S = R := by
  refine Subtype.ext (hilmod_fixed_on_V_eq (ptensBInner φ) E S.1 R.1 S.2 R.2 fun v => ?_)
  obtain ⟨n, a, b, rfl⟩ := exists_fin_tmul v
  rw [eta_sum, map_sum, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => h (a i) (b i))

/-- `ϱ(a₀)` acts on the image of `η` as the right 𝒜-action of `𝒜 ⊙ ℬ`. -/
theorem rho_eta {R : Ba ℬ E.X} {a₀ : 𝒜}
    (hR : ∀ (a : 𝒜) (b : ℬ), R.1 (ptprod φ E a b) = ptprod φ E (a * a₀) b)
    (v : 𝒜 ⊗[ℂ] ℬ) : R.1 (E.η v) = E.η (prmul a₀ v) := by
  obtain ⟨n, a, b, rfl⟩ := exists_fin_tmul v
  rw [eta_sum, map_sum, map_sum]
  refine (Finset.sum_congr rfl fun i _ => hR (a i) (b i)).trans ?_
  exact (eta_sum φ E (fun i => a i * a₀) b).symm

end Rho


section RhoAlgebra

variable [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
  (φ : NCPMap 𝒜 ℬ) (E : SelfDualCompletion.{u, u, u} (ptensBInner φ))

/-- **154III**.2: the operator `ϱ(a₀)` on `𝒜 ⊗_φ ℬ` (mirrored). -/
noncomputable def prho (a₀ : 𝒜) : Ba ℬ E.X := (exists_prho φ E a₀).choose

@[simp] theorem prho_ptprod (a₀ a : 𝒜) (b : ℬ) :
    (prho φ E a₀).1 (ptprod φ E a b) = ptprod φ E (a * a₀) b :=
  (exists_prho φ E a₀).choose_spec a b

theorem prho_eta (a₀ : 𝒜) (v : 𝒜 ⊗[ℂ] ℬ) :
    (prho φ E a₀).1 (E.η v) = E.η (prmul a₀ v) :=
  rho_eta φ E (prho_ptprod φ E a₀) v

theorem prho_one : prho φ E 1 = 1 :=
  ba_ext_ptprod φ E fun a b => by rw [prho_ptprod, mul_one]; rfl

theorem prho_mul (a₀ a₁ : 𝒜) : prho φ E (a₀ * a₁) = prho φ E a₁ * prho φ E a₀ :=
  ba_ext_ptprod φ E fun a b => by
    rw [prho_ptprod]
    show _ = (prho φ E a₁).1 ((prho φ E a₀).1 (ptprod φ E a b))
    rw [prho_ptprod, prho_ptprod, mul_assoc]

theorem prho_add (a₀ a₁ : 𝒜) : prho φ E (a₀ + a₁) = prho φ E a₀ + prho φ E a₁ :=
  ba_ext_ptprod φ E fun a b => by
    rw [prho_ptprod, mul_add]
    show _ = (prho φ E a₀).1 (ptprod φ E a b) + (prho φ E a₁).1 (ptprod φ E a b)
    rw [prho_ptprod, prho_ptprod]
    exact (phiCompatible_ptprod φ E).add_left _ _ _

theorem prho_zero : prho φ E 0 = 0 :=
  ba_ext_ptprod φ E fun a b => by
    rw [prho_ptprod, mul_zero]
    show _ = (0 : E.X)
    have h := (phiCompatible_ptprod φ E).smul_complex 0 0 b
    simpa using h

theorem prho_smul (c : ℂ) (a₀ : 𝒜) : prho φ E (c • a₀) = c • prho φ E a₀ :=
  ba_ext_ptprod φ E fun a b => by
    rw [prho_ptprod, mul_smul_comm]
    show _ = c • (prho φ E a₀).1 (ptprod φ E a b)
    rw [prho_ptprod]
    exact (phiCompatible_ptprod φ E).smul_complex _ _ _

theorem ptensBInner_add_left (φ : NCPMap 𝒜 ℬ) (x x' y : 𝒜 ⊗[ℂ] ℬ) :
    (ptensBInner φ).inner (x + x') y
      = (ptensBInner φ).inner x y + (ptensBInner φ).inner x' y := by
  show ptensPair _ (star (x + x')) y = _
  rw [star_add, map_add, LinearMap.add_apply]
  rfl

theorem ptensBInner_zero_left (φ : NCPMap 𝒜 ℬ) (y : 𝒜 ⊗[ℂ] ℬ) :
    (ptensBInner φ).inner 0 y = 0 := by
  show ptensPair _ (star (0 : 𝒜 ⊗[ℂ] ℬ)) y = 0
  rw [star_zero, map_zero, LinearMap.zero_apply]

theorem ptensBInner_zero_right (φ : NCPMap 𝒜 ℬ) (x : 𝒜 ⊗[ℂ] ℬ) :
    (ptensBInner φ).inner x 0 = 0 := by
  show ptensPair _ (star x) 0 = 0
  rw [map_zero]

/-- The right 𝒜-action is `star`-adjoint for the φ-inner product. -/
theorem ptensBInner_prmul (a₀ : 𝒜) (x y : 𝒜 ⊗[ℂ] ℬ) :
    (ptensBInner φ).inner (prmul a₀ x) y
      = (ptensBInner φ).inner x (prmul (star a₀) y) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, ptensBInner_zero_left, ptensBInner_zero_left]
  | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => rw [map_zero, ptensBInner_zero_right, ptensBInner_zero_right]
      | tmul a' b' =>
          show b' * φ (a' * star (a * a₀)) * star b
            = b' * φ (a' * star a₀ * star a) * star b
          rw [star_mul, ← mul_assoc]
      | add y₁ y₂ h₁ h₂ =>
          show (ptensBInner φ).inner _ (y₁ + y₂) = (ptensBInner φ).inner _ (prmul _ (y₁ + y₂))
          rw [(ptensBInner φ).inner_add_right, map_add,
            (ptensBInner φ).inner_add_right, h₁, h₂]
  | add x₁ x₂ h₁ h₂ =>
      rw [map_add, ptensBInner_add_left, h₁, h₂, ptensBInner_add_left]

theorem prho_star (a₀ : 𝒜) : prho φ E (star a₀) = star (prho φ E a₀) := by
  have hadj : ModuleAdjointTo ℬ ⇑(prho φ E a₀).1
      ⇑((star (prho φ E a₀) : Ba ℬ E.X)).1 := baSubalgebra_star_spec _
  refine Subtype.ext (hilmod_fixed_on_V_eq (ptensBInner φ) E _ _
    (prho φ E (star a₀)).2 (star (prho φ E a₀) : Ba ℬ E.X).2 fun v => ?_)
  rw [← hadj (E.η v) (E.η v), prho_eta, prho_eta, E.η_inner, E.η_inner]
  exact (ptensBInner_prmul φ a₀ v v).symm

end RhoAlgebra
section Polarization

variable [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]

/-- Double polarisation (**44II** twice, through `mult_polarization`): the
off-diagonal Gram term `b φ(u d u'*) b'*` is a ℂ-combination of the
*diagonal* terms `w* φ(v* d v) w`.  This is what makes the vector form of
`ϱ` a combination of np-functionals, and hence normal. -/
theorem gram_polarization (φ : NCPMap 𝒜 ℬ) (u u' : 𝒜) (b b' : ℬ) (d : 𝒜) :
    b * φ (u * d * star u') * star b'
      = ∑ k ∈ Finset.range 4, ∑ l ∈ Finset.range 4,
          ((16 : ℂ)⁻¹ * (Complex.I ^ k * Complex.I ^ l)) •
            (star (Complex.I ^ k • star b + star b') *
              φ (star (Complex.I ^ l • star u + star u') * d
                  * (Complex.I ^ l • star u + star u')) *
              (Complex.I ^ k • star b + star b')) := by
  set ψ : 𝒜 →ₗ[ℂ] ℬ := φ.toCompletelyPositiveMap.toLinearMap with hψdef
  have hψ : ⇑φ = ⇑ψ := rfl
  have hA : u * d * star u' = (4 : ℂ)⁻¹ • ∑ l ∈ Finset.range 4, Complex.I ^ l •
      (star (Complex.I ^ l • star u + star u') * d
        * (Complex.I ^ l • star u + star u')) := by
    have h := mult_polarization (star u) (star u') d
    rwa [star_star] at h
  have hB : ∀ y : ℬ, b * y * star b'
      = (4 : ℂ)⁻¹ • ∑ k ∈ Finset.range 4, Complex.I ^ k •
          (star (Complex.I ^ k • star b + star b') * y
            * (Complex.I ^ k • star b + star b')) := by
    intro y
    have h := mult_polarization (star b) (star b') y
    rwa [star_star] at h
  rw [hB, hA, hψ, map_smul, map_sum]
  simp only [map_smul, smul_mul_assoc, mul_smul_comm, Finset.mul_sum, Finset.sum_mul,
    Finset.smul_sum, smul_smul, ← hψ]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  congr 1
  ring

end Polarization

section Theta

variable [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ)

/-- The vector form of `ϱ` at `η v`: `d ↦ ⟨η v, ϱ(d) (η v)⟩`, computed
inside `𝒜 ⊙ ℬ`. -/
noncomputable def pTheta (v : 𝒜 ⊗[ℂ] ℬ) (d : 𝒜) : ℬ :=
  (ptensBInner φ).inner v (prmul d v)

theorem ptensBInner_sum {n m : ℕ} (a : Fin n → 𝒜) (b : Fin n → ℬ)
    (a' : Fin m → 𝒜) (b' : Fin m → ℬ) :
    (ptensBInner φ).inner (∑ i, a i ⊗ₜ[ℂ] b i) (∑ j, a' j ⊗ₜ[ℂ] b' j)
      = ∑ j, ∑ i, b' j * φ (a' j * star (a i)) * star (b i) := by
  show ptensPair (φ.toCompletelyPositiveMap.toLinearMap)
      (star (∑ i, a i ⊗ₜ[ℂ] b i)) (∑ j, a' j ⊗ₜ[ℂ] b' j) = _
  rw [star_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ptensPair _ (star (a i) ⊗ₜ[ℂ] star (b i)) (a' j ⊗ₜ[ℂ] b' j) = _
  rw [ptensPair_tmul]
  rfl

theorem pTheta_sum {n : ℕ} (a : Fin n → 𝒜) (b : Fin n → ℬ) (d : 𝒜) :
    pTheta φ (∑ i, a i ⊗ₜ[ℂ] b i) d
      = ∑ i, ∑ j, b i * φ (a i * d * star (a j)) * star (b j) := by
  have hprm : prmul d (∑ i, a i ⊗ₜ[ℂ] b i) = ∑ i, (a i * d) ⊗ₜ[ℂ] b i := by
    rw [map_sum]; rfl
  show (ptensBInner φ).inner _ (prmul d _) = _
  rw [hprm, ptensBInner_sum]

theorem pTheta_add (v : 𝒜 ⊗[ℂ] ℬ) (d d' : 𝒜) :
    pTheta φ v (d + d') = pTheta φ v d + pTheta φ v d' := by
  have h : prmul (d + d') v = prmul d v + prmul d' v := by
    have : prmul (𝒜 := 𝒜) (ℬ := ℬ) (d + d') = prmul d + prmul d' := by
      refine TensorProduct.ext' fun a b => ?_
      show (a * (d + d')) ⊗ₜ[ℂ] b = (a * d) ⊗ₜ[ℂ] b + (a * d') ⊗ₜ[ℂ] b
      rw [mul_add, TensorProduct.add_tmul]
    rw [this]; rfl
  show (ptensBInner φ).inner v (prmul (d + d') v) = _
  rw [h, (ptensBInner φ).inner_add_right]
  rfl

theorem pTheta_nonneg (v : 𝒜 ⊗[ℂ] ℬ) {d : 𝒜} (hd : 0 ≤ d) :
    (0 : ℬ) ≤ pTheta φ v d := by
  obtain ⟨n, a, b, rfl⟩ := exists_fin_tmul v
  rw [pTheta_sum]
  set e : 𝒜 := CFC.sqrt d with he
  have hsa : star e = e := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg d)
  have hee : e * e = d := CFC.sqrt_mul_sqrt_self d hd
  have hterm : ∀ i j : Fin n, a i * d * star (a j) = (a i * e) * star (a j * e) := by
    intro i j
    rw [star_mul, hsa, ← hee]
    noncomm_ring
  simp only [hterm]
  exact phi_gram_nonneg φ (fun i => a i * e) b

theorem pTheta_mono (v : 𝒜 ⊗[ℂ] ℬ) {d d' : 𝒜} (h : d ≤ d') :
    pTheta φ v d ≤ pTheta φ v d' := by
  rw [← sub_nonneg]
  have h0 : pTheta φ v (d' - d) + pTheta φ v d = pTheta φ v d' := by
    rw [← pTheta_add, sub_add_cancel]
  have hsub : pTheta φ v d' - pTheta φ v d = pTheta φ v (d' - d) := by
    rw [← h0]; abel
  rw [hsub]
  exact pTheta_nonneg φ _ (sub_nonneg.mpr h)

end Theta

section ThetaNormal

variable [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ)

/-- The index set `(i, j, k, l)` of the double polarisation. -/
def pIdx (n : ℕ) : Finset (Fin n × Fin n × ℕ × ℕ) :=
  (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))
    ×ˢ Finset.range 4 ×ˢ Finset.range 4

/-- Its coefficients. -/
noncomputable def pCoef {n : ℕ} (p : Fin n × Fin n × ℕ × ℕ) : ℂ :=
  (16 : ℂ)⁻¹ * (Complex.I ^ p.2.2.1 * Complex.I ^ p.2.2.2)

/-- The np-functionals of the double polarisation:
`d ↦ ω(w* φ(v* d v) w)`. -/
noncomputable def pNP (ω : NPFunctional ℬ) {n : ℕ} (a : Fin n → 𝒜) (b : Fin n → ℬ)
    (p : Fin n × Fin n × ℕ × ℕ) : NPFunctional 𝒜 :=
  conjNP (Complex.I ^ p.2.2.2 • star (a p.1) + star (a p.2.1))
    (compNP (ncpPositive φ) φ.preservesDirSups'
      (conjNP (Complex.I ^ p.2.2.1 • star (b p.1) + star (b p.2.1)) ω))

theorem pTheta_combination (ω : NPFunctional ℬ) {n : ℕ} (a : Fin n → 𝒜)
    (b : Fin n → ℬ) (d : 𝒜) :
    (ω (pTheta φ (∑ i, a i ⊗ₜ[ℂ] b i) d) : ℂ)
      = ∑ p ∈ pIdx n, pCoef p * pNP φ ω a b p d := by
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → ℬ),
      (ω (∑ i ∈ s, f i) : ℂ) = ∑ i ∈ s, ω (f i) :=
    fun s f => map_sum ω.toPositiveLinearMap f s
  have hsmul : ∀ (c : ℂ) (x : ℬ), (ω (c • x) : ℂ) = c * ω x := fun c x =>
    (map_smul ω.toPositiveLinearMap c x).trans (smul_eq_mul _ _)
  rw [pTheta_sum, hsum, pIdx, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsum, Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gram_polarization φ (a i) (a j) (b i) (b j) d, hsum, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hsum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hsmul]
  rfl

theorem pTheta_normal (ω : NPFunctional ℬ) (v : 𝒜 ⊗[ℂ] ℬ) :
    PreservesDirSups (fun d : 𝒜 => (ω (pTheta φ v d) : ℂ)) := by
  obtain ⟨n, a, b, rfl⟩ := exists_fin_tmul v
  exact preservesDirSups_of_np_combination (pIdx n) _
    (fun h => npFunctional_mono ω (pTheta_mono φ _ h)) pCoef (pNP φ ω a b)
    (pTheta_combination φ ω a b)

end ThetaNormal

section RhoHom

variable [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
  (φ : NCPMap 𝒜 ℬ) (E : SelfDualCompletion.{u, u, u} (ptensBInner φ))

/-- `ϱ` as a ring homomorphism into `𝒷ᵃ(𝒜 ⊗_φ ℬ)ᵐᵒᵖ` (the `ᵐᵒᵖ` turns the
anti-multiplicativity of `a₀ ↦ (a ⊗ b ↦ (a a₀) ⊗ b)` into
multiplicativity). -/
noncomputable def prhoRing : 𝒜 →+* (Ba ℬ E.X)ᵐᵒᵖ where
  toFun a₀ := MulOpposite.op (prho φ E a₀)
  map_one' := by rw [prho_one]; rfl
  map_mul' a₀ a₁ := by
    show MulOpposite.op (prho φ E (a₀ * a₁)) = _
    rw [prho_mul, ← MulOpposite.op_mul]
  map_zero' := by rw [prho_zero]; rfl
  map_add' a₀ a₁ := by
    show MulOpposite.op (prho φ E (a₀ + a₁)) = _
    rw [prho_add, MulOpposite.op_add]

/-- **154III**.2: `ϱ : 𝒜 → 𝒷ᵃ(𝒜 ⊗_φ ℬ)ᵐᵒᵖ` is a ∗-homomorphism. -/
noncomputable def prhoHom : 𝒜 →⋆ₐ[ℂ] (Ba ℬ E.X)ᵐᵒᵖ where
  toAlgHom := AlgHom.mk' (prhoRing φ E) fun c x => by
    show MulOpposite.op (prho φ E (c • x)) = _
    rw [prho_smul, MulOpposite.op_smul]
    rfl
  map_star' a₀ := by
    show MulOpposite.op (prho φ E (star a₀)) = _
    rw [prho_star, MulOpposite.op_star]
    rfl

@[simp] theorem prhoHom_apply (a₀ : 𝒜) :
    prhoHom φ E a₀ = MulOpposite.op (prho φ E a₀) := rfl

/-- **154III**.2: `ϱ` is normal.  The thesis's route (`normal-faithful` +
`hilmod-fixed-on-V`), with the vector forms `d ↦ ⟨η v, ϱ(d) η v⟩` shown
normal by the double polarisation above rather than by `mn-vna` (which is
still open in `A/VN`). -/
theorem prhoHom_normal : PreservesDirSups ⇑(prhoHom φ E) := by
  haveI : VonNeumannAlgebra (Ba ℬ E.X) := ba_vonNeumannAlgebra E.selfDual
  set Ω : Set (NPFunctional (Ba ℬ E.X)ᵐᵒᵖ) :=
    {ν | ∃ (v : 𝒜 ⊗[ℂ] ℬ) (ω : NPFunctional ℬ),
      ν = npFunctionalOp (baVecNP E.selfDual (E.η v) ω)} with hΩ
  have hfaith : FaithfulCollection Ω := by
    intro Z hZ hzero
    have hZu : (0 : Ba ℬ E.X) ≤ Z.unop := hZ
    have hvec : ∀ v : 𝒜 ⊗[ℂ] ℬ, (inner ℬ (E.η v) (Z.unop.1 (E.η v)) : ℬ) = 0 := fun v =>
      VonNeumannAlgebra.np_faithful _ ((ba_nonneg_iff Z.unop).mp hZu (E.η v))
        fun ω => hzero _ ⟨v, ω, rfl⟩
    refine MulOpposite.unop_injective (Subtype.ext ?_)
    refine hilmod_fixed_on_V_eq (ptensBInner φ) E _ (0 : Ba ℬ E.X).1
      Z.unop.2 (0 : Ba ℬ E.X).2 fun v => ?_
    rw [hvec v]
    show (0 : ℬ) = inner ℬ (E.η v) (0 : E.X)
    rw [CStarModule.inner_zero_right]
  refine (normal_faithful Ω hfaith (starAlgHomP (prhoHom φ E))).mpr ?_
  rintro ν ⟨v, ω, rfl⟩
  have heq : (fun a : 𝒜 =>
      (npFunctionalOp (baVecNP E.selfDual (E.η v) ω) (starAlgHomP (prhoHom φ E) a) : ℂ))
      = fun a : 𝒜 => (ω (pTheta φ v a) : ℂ) := by
    funext a
    show (ω (inner ℬ (E.η v) ((prho φ E a).1 (E.η v))) : ℂ) = _
    rw [prho_eta, E.η_inner]
    rfl
  rw [heq]
  exact pTheta_normal φ ω v

end RhoHom

section VectorState

variable [VonNeumannAlgebra ℬ] {X : Type u} [NormedAddCommGroup X]
  [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X] [CompleteSpace X]

/-- The vector state `T ↦ ⟨e, T e⟩` on `𝒷ᵃ(X)ᵐᵒᵖ`, as a linear map. -/
noncomputable def pVecLin (e : X) : (Ba ℬ X)ᵐᵒᵖ →ₗ[ℂ] ℬ where
  toFun T := inner ℬ e (T.unop.1 e)
  map_add' T S := by
    show (inner ℬ e (T.unop.1 e + S.unop.1 e) : ℬ) = _
    rw [CStarModule.inner_add_right]
  map_smul' c T := by
    show (inner ℬ e (c • T.unop.1 e) : ℬ) = _
    rw [CStarModule.inner_smul_right_complex]
    rfl

@[simp] theorem pVecLin_apply (e : X) (T : (Ba ℬ X)ᵐᵒᵖ) :
    pVecLin (ℬ := ℬ) e T = inner ℬ e (T.unop.1 e) := rfl

/-- **145I** `hilbmod_vectstates_cp`: the vector state is completely
positive on `𝒷ᵃ(X)ᵐᵒᵖ` (and, as the file header explains, *not* on
`𝒷ᵃ(X)`). -/
theorem pVecLin_cp (e : X) : IsCompletelyPositiveMap (pVecLin (ℬ := ℬ) e) := by
  intro n A b
  set T : Fin n → Ba ℬ X := fun i => star ((A i).unop) with hT
  have hAi : ∀ i, (A i).unop = star (T i) := fun i => by rw [hT]; simp
  have hadj : ∀ i, ModuleAdjointTo ℬ ⇑(T i).1 ⇑((star (T i) : Ba ℬ X)).1 :=
    fun i => baSubalgebra_star_spec (T i)
  have h := hilbmod_vectstates_cp (𝒷 := ℬ) e n (fun i => (T i).1)
    (fun i => ((star (T i) : Ba ℬ X)).1) hadj b
  refine le_of_le_of_eq h (Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_)
  have hterm : (inner ℬ (((star (T i) : Ba ℬ X)).1 ((T j).1 e)) e : ℬ)
      = pVecLin (ℬ := ℬ) e (star (A i) * A j) := by
    have h1 : (inner ℬ (((star (T i) : Ba ℬ X)).1 ((T j).1 e)) e : ℬ)
        = inner ℬ ((T j).1 e) ((T i).1 e) :=
      moduleAdjointTo_symm (𝒜 := ℬ) _ _ (hadj i) ((T j).1 e) e
    have h2 : (inner ℬ ((T j).1 e) ((T i).1 e) : ℬ)
        = inner ℬ e (((star (T j) : Ba ℬ X)).1 ((T i).1 e)) := hadj j e ((T i).1 e)
    have h3 : pVecLin (ℬ := ℬ) e (star (A i) * A j)
        = inner ℬ e (((star (T j) : Ba ℬ X)).1 ((T i).1 e)) := by
      show (inner ℬ e ((star (A i) * A j).unop.1 e) : ℬ) = _
      have hstj : (star (T j) : Ba ℬ X) = (A j).unop := by rw [hT]; simp
      have h4 : (star (A i) * A j).unop = (star (T j) : Ba ℬ X) * T i := by
        rw [MulOpposite.unop_mul, MulOpposite.unop_star, hstj]
      rw [h4]
      rfl
    rw [h3, ← h2, ← h1]
  exact congrArg (fun z => star (b i) * z * b j) hterm

theorem pVecLin_nonneg (e : X) {T : (Ba ℬ X)ᵐᵒᵖ} (hT : 0 ≤ T) :
    (0 : ℬ) ≤ pVecLin (ℬ := ℬ) e T :=
  (ba_nonneg_iff T.unop).mp hT e

/-- **152XIII** `baVecNP`: the vector state is normal. -/
theorem pVecLin_normal (hX : SelfDual ℬ X) (e : X) :
    PreservesDirSups ⇑(pVecLin (ℬ := ℬ) e) := by
  haveI : VonNeumannAlgebra (Ba ℬ X) := ba_vonNeumannAlgebra hX
  have hfaith : FaithfulCollection (Set.univ : Set (NPFunctional ℬ)) := fun c hc h =>
    VonNeumannAlgebra.np_faithful c hc fun ω => h ω (Set.mem_univ ω)
  refine (normal_faithful _ hfaith
    (PositiveLinearMap.mk₀ (pVecLin (ℬ := ℬ) e) fun x hx => pVecLin_nonneg e hx)).mpr ?_
  intro ω _
  exact (npFunctionalOp (baVecNP hX e ω)).preservesDirSups'

/-- **154III**.3: `h(T) = ⟨e, T e⟩` is an ncp-map `𝒷ᵃ(X)ᵐᵒᵖ → ℬ`. -/
noncomputable def pVecNCP (hX : SelfDual ℬ X) (e : X) : NCPMap (Ba ℬ X)ᵐᵒᵖ ℬ where
  toCompletelyPositiveMap :=
    { toLinearMap := pVecLin (ℬ := ℬ) e
      map_cstarMatrix_nonneg' := by
        have h : ∀ (N : ℕ) (M : CStarMatrix (Fin N) (Fin N) ((Ba ℬ X)ᵐᵒᵖ)),
            0 ≤ M → 0 ≤ M.map ⇑(pVecLin (ℬ := ℬ) e) :=
          ((cp_iff (pVecLin (ℬ := ℬ) e)).out 0 1).mp (pVecLin_cp e)
        exact fun k M hM => h k M hM }
  preservesDirSups' := pVecLin_normal hX e

@[simp] theorem pVecNCP_apply (hX : SelfDual ℬ X) (e : X) (T : (Ba ℬ X)ᵐᵒᵖ) :
    pVecNCP hX e T = inner ℬ e (T.unop.1 e) := rfl

end VectorState


/-- **154III** (`existence-paschke`, dils.tex:3558, Theorem), parts 1–3:
the module `𝒜 ⊗_φ ℬ`, the representation `ϱ` and the vector state `h`
exist.

The bundle is not vacuous: `paschkeModuleId` exhibits `ℬ` itself as
`ℬ ⊗_id ℬ`, so every field below is jointly satisfiable for a non-zero
`φ`. -/
theorem existence_paschke [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) : Nonempty (PaschkeModule φ) := by
  obtain ⟨E⟩ := dils_completion (𝒷 := ℬ) (V := 𝒜 ⊗[ℂ] ℬ) (ptensBInner φ)
  exact ⟨{ X := E.X
           selfDual := E.selfDual
           tprod := ptprod φ E
           compat := phiCompatible_ptprod φ E
           inner_tprod := inner_ptprod φ E
           univ := fun Y i1 i2 i3 i4 i5 hY T hT => by
             letI := i1; letI := i2; letI := i3; letI := i4; letI := i5
             exact ptprod_univ φ E hY T hT
           ρ := { toStarAlgHom := prhoHom φ E
                  preservesDirSups' := prhoHom_normal φ E }
           ρ_tprod := fun a₀ a b => prho_ptprod φ E a₀ a b
           h := pVecNCP E.selfDual (ptprod φ E 1 1)
           h_def := fun T => rfl }⟩

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

/-! ### Toward part 5: separation and extensionality on the elementary tensors

The thesis's proof of **154VIII** `paschke-uniqueness` compares the vector
forms `⟨x̂, σₖ(c) x̂⟩` for `x ∈ 𝒜 ⊙ ℬ` and then appeals to
**152IX** `hilmod-fixed-on-V`, i.e. to ultranorm density of the image of
`η`.  A `PaschkeModule` is *abstract* — it carries no `η` — so that route
is unavailable here.  It is not needed either: the two lemmas below extract
from the **uniqueness** half of the universal property of part 1 exactly
what the density argument was for.

* `paschkeModule_inner_tprod_separating`: `⟨a ⊗ b, w⟩ = 0` for all `a, b`
  forces `w = 0`, because `x ↦ ⟨w, x⟩` and `0` are then two bounded module
  maps `𝒜 ⊗_φ ℬ → ℬ` lifting the *zero* bilinear map (`ℬ` is self dual
  over itself, `selfDual_self`).
* `paschkeModule_ba_ext`: adjointable operators agreeing on the elementary
  tensors are equal, by the same uniqueness at `Y = 𝒜 ⊗_φ ℬ`.

Moreover the sesquilinear form — not merely its diagonal — is determined
(`paschke_sigma_matrix`), so no polarization step is needed either. -/

/-- The zero bilinear map is φ-compatible. -/
theorem phiCompatible_zero (φ : NCPMap 𝒜 ℬ) {Y : Type u} [NormedAddCommGroup Y]
    [Module ℂ Y] [SMul ℬ Y] [CStarModule ℬ Y] :
    PhiCompatible ⇑φ (fun (_ : 𝒜) (_ : ℬ) => (0 : Y)) where
  add_left _ _ _ := (add_zero _).symm
  add_right _ _ _ := (add_zero _).symm
  smul_complex _ _ _ := (smul_zero _).symm
  smul_action _ _ c := op_smul_zero (X := Y) c
  bound := ⟨1, one_pos, fun n a b => by
    have h0 : ‖∑ _i : Fin n, (0 : Y)‖ ^ 2 = 0 := by simp
    rw [h0]
    positivity⟩

/-- Composing the elementary tensors with a bounded module map again gives a
φ-compatible bilinear map. -/
theorem phiCompatible_comp (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ) {Y : Type u}
    [NormedAddCommGroup Y] [Module ℂ Y] [SMul ℬ Y] [CStarModule ℬ Y]
    (T : M.X → Y) (C : ℝ)
    (hT : IsBoundedModuleMap (cstarBInner ℬ M.X) (cstarBInner ℬ Y) C T) :
    PhiCompatible ⇑φ (fun a b => T (M.tprod a b)) := by
  obtain ⟨r, hr0, hr⟩ := M.compat.bound
  refine { add_left := fun a a' b => by rw [M.compat.add_left, hT.add]
           add_right := fun a b b' => by rw [M.compat.add_right, hT.add]
           smul_complex := fun c a b => by
             rw [M.compat.smul_complex, hT.smul_complex]
           smul_action := fun a b c => by
             rw [← M.compat.smul_action, hT.smul]
           bound := ⟨r * (C ^ 2 + 1), by positivity, fun n a b => ?_⟩ }
  have hsum : (∑ i, T (M.tprod (a i) (b i))) = T (∑ i, M.tprod (a i) (b i)) := by
    classical
    induction (Finset.univ : Finset (Fin n)) using Finset.induction with
    | empty =>
        simp only [Finset.sum_empty]
        have h0 : T 0 = 0 := by
          have := hT.smul_complex 0 0
          simpa using this
        exact h0.symm
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, hT.add]
  rw [hsum]
  have hb := hT.bound (∑ i, M.tprod (a i) (b i))
  rw [cstarBInner_norm, cstarBInner_norm] at hb
  have h3 := hr n a b
  have h4 : (0 : ℝ) ≤ ‖∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j)‖ :=
    norm_nonneg _
  have h5 : (0 : ℝ) ≤ ‖∑ i, M.tprod (a i) (b i)‖ := norm_nonneg _
  have h6 : ‖T (∑ i, M.tprod (a i) (b i))‖ ≤ |C| * ‖∑ i, M.tprod (a i) (b i)‖ := by
    nlinarith [le_abs_self C]
  have h7 : (0 : ℝ) ≤ ‖T (∑ i, M.tprod (a i) (b i))‖ := norm_nonneg _
  calc ‖T (∑ i, M.tprod (a i) (b i))‖ ^ 2
      ≤ (|C| * ‖∑ i, M.tprod (a i) (b i)‖) ^ 2 := by nlinarith
    _ = C ^ 2 * ‖∑ i, M.tprod (a i) (b i)‖ ^ 2 := by rw [mul_pow, sq_abs]
    _ ≤ C ^ 2 * (r * ‖∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j)‖) := by
        nlinarith [sq_nonneg C]
    _ ≤ r * (C ^ 2 + 1)
          * ‖∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j)‖ := by
        nlinarith [sq_nonneg C, mul_nonneg hr0.le h4]

/-- The elementary tensors are *separating*: an element of `𝒜 ⊗_φ ℬ`
orthogonal to every `a ⊗ b` is zero.  This is the universal property of
part 1 applied to the zero bilinear map and to `ℬ` itself: `x ↦ ⟨w, x⟩` and
`0` are two bounded module maps `𝒜 ⊗_φ ℬ → ℬ` lifting it. -/
theorem paschkeModule_inner_tprod_separating [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ) {w : M.X}
    (hw : ∀ (a : 𝒜) (b : ℬ), (inner ℬ (M.tprod a b) w : ℬ) = 0) : w = 0 := by
  obtain ⟨F, -, hFuniq⟩ :=
    M.univ ℬ inferInstance inferInstance inferInstance inferInstance
      inferInstance (selfDual_self ℬ) _ (phiCompatible_zero (Y := ℬ) φ)
  have h1 : (fun x => (inner ℬ w x : ℬ)) = F := by
    refine hFuniq _ ⟨⟨‖w‖, { add := fun x x' => CStarModule.inner_add_right
                             smul_complex := fun c x =>
                               CStarModule.inner_smul_right_complex
                             smul := fun b x => by
                               rw [CStarModule.inner_op_smul_right, smul_eq_mul]
                             bound := fun x => by
                               rw [cstarBInner_norm, cstarBInner_norm]
                               exact CStarModule.norm_inner_le (A := ℬ) M.X }⟩,
      fun a b => ?_⟩
    show (inner ℬ w (M.tprod a b) : ℬ) = 0
    rw [← CStarModule.star_inner (A := ℬ) (M.tprod a b) w, hw a b, star_zero]
  have h2 : (fun _ : M.X => (0 : ℬ)) = F := by
    refine hFuniq _ ⟨⟨0, { add := fun x x' => (add_zero _).symm
                           smul_complex := fun c x => (smul_zero c).symm
                           smul := fun b x => (op_smul_zero (X := ℬ) b).symm
                           bound := fun x => by
                             rw [cstarBInner_norm, cstarBInner_norm, norm_zero,
                               zero_mul] }⟩, fun a b => rfl⟩
  have h3 : (inner ℬ w w : ℬ) = 0 := by
    have := h1.trans h2.symm
    exact congrFun this w
  exact CStarModule.inner_self.mp h3

/-- Adjointable operators on `𝒜 ⊗_φ ℬ` agreeing on all elementary tensors
are equal (the uniqueness half of part 1, at `Y = 𝒜 ⊗_φ ℬ`). -/
theorem paschkeModule_ba_ext [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ) {S R : Ba ℬ M.X}
    (h : ∀ (a : 𝒜) (b : ℬ), S.1 (M.tprod a b) = R.1 (M.tprod a b)) : S = R := by
  have hbdd : ∀ T : Ba ℬ M.X, ∃ C : ℝ,
      IsBoundedModuleMap (cstarBInner ℬ M.X) (cstarBInner ℬ M.X) C ⇑T.1 := by
    intro T
    obtain ⟨-, -, hmod⟩ := moduleAdjointable_linear (𝒜 := ℬ) ⇑T.1 T.2
    refine ⟨‖T.1‖ + 1, { add := fun x y => map_add T.1 x y
                         smul_complex := fun c x => map_smul T.1 c x
                         smul := hmod
                         bound := fun x => ?_ }⟩
    rw [cstarBInner_norm, cstarBInner_norm]
    have h1 := T.1.le_opNorm x
    have h0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    nlinarith
  obtain ⟨CS, hCS⟩ := hbdd S
  obtain ⟨CR, hCR⟩ := hbdd R
  obtain ⟨F, -, hFuniq⟩ :=
    M.univ M.X inferInstance inferInstance inferInstance inferInstance
      inferInstance M.selfDual _ (phiCompatible_comp φ M ⇑S.1 CS hCS)
  have h1 : ⇑S.1 = F := hFuniq _ ⟨⟨CS, hCS⟩, fun a b => rfl⟩
  have h2 : ⇑R.1 = F := hFuniq _ ⟨⟨CR, hCR⟩, fun a b => (h a b).symm⟩
  exact Subtype.ext (DFunLike.coe_injective (h1.trans h2.symm))

/-- **154VIII** (`paschke-uniqueness`, dils.tex:3719): a mediating ncp-map
`σ` has determined matrix elements on the elementary tensors. -/
theorem paschke_sigma_matrix [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (D' : PaschkeTriple 𝒜 ℬ) (σ : NCPMap D'.P (Ba ℬ M.X)ᵐᵒᵖ)
    (hσ1 : ∀ a, σ (D'.ρ a) = M.ρ a) (hσ2 : ∀ c, M.h (σ c) = D'.h c)
    (c : D'.P) (a a' : 𝒜) (b b' : ℬ) :
    (inner ℬ (M.tprod a b) ((σ c).unop.1 (M.tprod a' b')) : ℬ)
      = b' * D'.h (D'.ρ a' * c * D'.ρ (star a)) * star b := by
  have htp : ∀ (x : 𝒜) (y : ℬ),
      M.tprod x y = y • (M.ρ x).unop.1 (M.tprod 1 1) := by
    intro x y
    rw [M.ρ_tprod, one_mul, M.compat.smul_action, mul_one]
  have hmod : ∀ (bb : ℬ) (x : M.X), (σ c).unop.1 (bb • x) = bb • (σ c).unop.1 x :=
    (moduleAdjointable_linear (𝒜 := ℬ) ⇑(σ c).unop.1 (σ c).unop.2).2.2
  have hRadj : ∀ x y : M.X,
      (inner ℬ ((M.ρ a).unop.1 x) y : ℬ)
        = inner ℬ x ((M.ρ (star a)).unop.1 y) := by
    intro x y
    have h : ModuleAdjointTo ℬ ⇑(M.ρ a).unop.1
        ⇑((star (M.ρ a).unop : Ba ℬ M.X)).1 := baSubalgebra_star_spec _
    have h2 : (star (M.ρ a).unop : Ba ℬ M.X) = (M.ρ (star a)).unop := by
      rw [show M.ρ (star a) = star (M.ρ a) from map_star M.ρ.toStarAlgHom a]
      rfl
    rw [← h2]
    exact h x y
  have hkey : (inner ℬ ((M.ρ a).unop.1 (M.tprod 1 1))
        ((σ c).unop.1 ((M.ρ a').unop.1 (M.tprod 1 1))) : ℬ)
      = D'.h (D'.ρ a' * c * D'.ρ (star a)) := by
    rw [hRadj]
    rw [show ((M.ρ (star a)).unop : Ba ℬ M.X).1
          ((σ c).unop.1 ((M.ρ a').unop.1 (M.tprod 1 1)))
        = ((M.ρ a' * σ c * M.ρ (star a)).unop : Ba ℬ M.X).1 (M.tprod 1 1)
        from rfl, ← M.h_def,
      ← dils_univlemma M.ρ D'.ρ σ hσ1 a' (star a) c, hσ2]
  rw [htp a b, htp a' b', hmod, CStarModule.inner_op_smul_right,
    CStarModule.inner_op_smul_left, hkey]
  exact (mul_assoc _ _ _).symm

/-- **154III** (`existence-paschke`, dils.tex:3558, Theorem), part 5:
`(ℬᵃ(𝒜 ⊗_φ ℬ), ϱ, h)` is a Paschke dilation of `φ`.  (In particular every
ncp-map between von Neumann algebras has a Paschke dilation.)

**154IV**–**154X** are the proof (including **154VIII**
`paschke-uniqueness` and **154IX** `paschke-spatial` as proof steps) — not
converted separately; **154IX** *is* `existence_paschke_4` above, and the
matrix-element computation of **154VIII** is `paschke_sigma_matrix`.

The existence half is **154X** verbatim: run the construction again on the
ncp-map `h' : 𝒫' → ℬ` — legitimate because `𝒫'` is a von Neumann algebra
by `PaschkeTriple.vn`, so `existence_paschke h'` applies — take
`ϱ'' = ϱ_{h'} ∘ ϱ'`, feed `(𝒫' ⊗_{h'} ℬ, ϱ'', 1 ⊗ 1)` to part 4 to get the
inner-product-preserving intertwiner `S`, and put `σ = ad_S ∘ ϱ_{h'}`.
`ad_S` is an ncp-map by **153I** `hilbmod_ad_ncp` and survives the passage
to the opposite algebras by `ncpMop`.

Divergence from the thesis: uniqueness does **not** go through
`hilmod-fixed-on-V` (which needs the concrete `η`, absent from an abstract
`PaschkeModule`) but through `paschkeModule_inner_tprod_separating` and
`paschkeModule_ba_ext` — see the section header above. -/
theorem existence_paschke_5 [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ) :
    IsPaschkeDilationOf
      ⟨(Ba ℬ M.X)ᵐᵒᵖ,
        @vonNeumannAlgebra_mulOpposite (Ba ℬ M.X) _ _ _
          (ba_vonNeumannAlgebra M.selfDual),
        M.ρ, M.h⟩ ⇑φ := by
  -- `h ∘ ϱ = φ` is `paschkeModule_h_ρ`; it is the half that was *false*
  -- before the `ᵐᵒᵖ` repair.  The universal property is **154IV**–**154X**.
  refine ⟨paschkeModule_h_ρ φ M, fun D' hD' => ?_⟩
  let _ := D'.vn
  -- **154VIII**: uniqueness of the mediating map
  have huniq : ∀ σ₁ σ₂ : NCPMap D'.P (Ba ℬ M.X)ᵐᵒᵖ,
      ((∀ a, σ₁ (D'.ρ a) = M.ρ a) ∧ ∀ c, M.h (σ₁ c) = D'.h c) →
      ((∀ a, σ₂ (D'.ρ a) = M.ρ a) ∧ ∀ c, M.h (σ₂ c) = D'.h c) →
      σ₁ = σ₂ := by
    intro σ₁ σ₂ h₁ h₂
    refine DFunLike.ext _ _ fun c => ?_
    refine MulOpposite.unop_injective (paschkeModule_ba_ext φ M fun a' b' => ?_)
    have hd : ∀ (a : 𝒜) (b : ℬ),
        (inner ℬ (M.tprod a b)
          ((σ₁ c).unop.1 (M.tprod a' b')
            - (σ₂ c).unop.1 (M.tprod a' b')) : ℬ) = 0 := by
      intro a b
      rw [CStarModule.inner_sub_right,
        paschke_sigma_matrix φ M D' σ₁ h₁.1 h₁.2 c a a' b b',
        paschke_sigma_matrix φ M D' σ₂ h₂.1 h₂.2 c a a' b b', sub_self]
    exact sub_eq_zero.mp (paschkeModule_inner_tprod_separating φ M hd)
  -- **154X**: the construction re-run on `h' : 𝒫' → ℬ`
  obtain ⟨M'⟩ := existence_paschke (𝒜 := D'.P) (ℬ := ℬ) D'.h
  set ϱ'' : NMIUMap 𝒜 (Ba ℬ M'.X)ᵐᵒᵖ :=
    { toStarAlgHom := M'.ρ.toStarAlgHom.comp D'.ρ.toStarAlgHom
      preservesDirSups' :=
        preservesDirSups_pmap_comp (starAlgHomP D'.ρ.toStarAlgHom)
          D'.ρ.preservesDirSups' (starAlgHomP M'.ρ.toStarAlgHom)
          M'.ρ.preservesDirSups' } with hϱ''
  have hϱ''app : ∀ a : 𝒜, ϱ'' a = M'.ρ (D'.ρ a) := fun _ => rfl
  have hφe : ∀ a : 𝒜,
      φ a = inner ℬ (M'.tprod 1 1) ((ϱ'' a).unop.1 (M'.tprod 1 1)) := by
    intro a
    rw [hϱ''app, ← M'.h_def, paschkeModule_h_ρ D'.h M' (D'.ρ a), hD' a]
  -- **154IX** (spatial case) = part 4
  obtain ⟨S, ⟨hSbdd, hSinner, hSone, hSint⟩, -⟩ :=
    existence_paschke_4 φ M M'.selfDual (M'.tprod 1 1) ϱ'' hφe
  obtain ⟨C, hC⟩ := hSbdd
  set Sl : M.X →ₗ[ℂ] M'.X :=
    { toFun := S, map_add' := hC.add, map_smul' := hC.smul_complex } with hSl
  have hbd : ∀ x, ‖Sl x‖ ≤ max C 0 * ‖x‖ := by
    intro x
    have h := hC.bound x
    rw [cstarBInner_norm, cstarBInner_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  set Sc : M.X →L[ℂ] M'.X := Sl.mkContinuous (max C 0) hbd with hSc
  have hScapp : ∀ x, Sc x = S x := fun _ => rfl
  obtain ⟨S', hS'⟩ := hilbmod_adjoint_exists M.selfDual Sc hC.smul
  have hSS : ∀ y : M.X, S' (Sc y) = y := by
    intro y
    refine eq_of_inner_right_eq (𝒜 := ℬ) fun x => ?_
    rw [← hS' x (Sc y), hScapp, hScapp, hSinner]
  obtain ⟨ad, hadeq⟩ := hilbmod_ad_ncp M.selfDual M'.selfDual Sc S' hS'
  -- `σ = ad_S^ᵐᵒᵖ ∘ ϱ_{h'}`
  set Lρ : D'.P →ₗ[ℂ] (Ba ℬ M'.X)ᵐᵒᵖ :=
    { toFun := fun c => M'.ρ c
      map_add' := fun x y => map_add M'.ρ.toStarAlgHom x y
      map_smul' := fun r x => map_smul M'.ρ.toStarAlgHom r x } with hLρ
  have hLρcp : IsCompletelyPositiveMap Lρ :=
    cp_of_mi Lρ (fun x y => map_mul M'.ρ.toStarAlgHom x y)
      (fun x => map_star M'.ρ.toStarAlgHom x)
  have hLadcp : IsCompletelyPositiveMap
      (ncpMop ad).toCompletelyPositiveMap.toLinearMap :=
    (cp_iff _).out 1 0 |>.mp fun N Mm hM =>
      (ncpMop ad).toCompletelyPositiveMap.map_cstarMatrix_nonneg' N Mm hM
  set σ : NCPMap D'.P (Ba ℬ M.X)ᵐᵒᵖ :=
    { toCompletelyPositiveMap :=
        { toLinearMap :=
            (ncpMop ad).toCompletelyPositiveMap.toLinearMap.comp Lρ
          map_cstarMatrix_nonneg' :=
            (cp_iff _).out 0 1 |>.mp (cp_comp Lρ _ hLρcp hLadcp) }
      preservesDirSups' :=
        preservesDirSups_pmap_comp (starAlgHomP M'.ρ.toStarAlgHom)
          M'.ρ.preservesDirSups' (ncpPositive (ncpMop ad))
          (ncpMop ad).preservesDirSups' } with hσdef
  have hσapp : ∀ (c : D'.P) (x : M.X),
      (σ c).unop.1 x = S' ((M'.ρ c).unop.1 (Sc x)) := by
    intro c x
    show ((ad ((M'.ρ c).unop) : Ba ℬ M.X)).1 x = _
    rw [hadeq]
    rfl
  have hσ1 : ∀ a : 𝒜, σ (D'.ρ a) = M.ρ a := by
    intro a
    refine MulOpposite.unop_injective (Subtype.ext (ContinuousLinearMap.ext fun x => ?_))
    rw [hσapp]
    have h1 : (M'.ρ (D'.ρ a)).unop.1 (Sc x) = Sc ((M.ρ a).unop.1 x) := by
      rw [hScapp, hScapp]
      exact (hSint a x).symm
    rw [h1, hSS]
  have hσ2 : ∀ c : D'.P, M.h (σ c) = D'.h c := by
    intro c
    rw [M.h_def, hσapp, ← hS' (M.tprod 1 1) ((M'.ρ c).unop.1 (Sc (M.tprod 1 1))),
      hScapp, hSone, ← M'.h_def, paschkeModule_h_ρ D'.h M' c]
  exact ⟨σ, ⟨hσ1, hσ2⟩, fun τ hτ => huniq τ σ hτ ⟨hσ1, hσ2⟩⟩

/-- **154III**.5 together with **140VIII** `paschke_unique_up_to_iso`:
*every* Paschke dilation of `φ` is nmiu-isomorphic to the constructed one
`(𝒷ᵃ(𝒜 ⊗_φ ℬ)ᵐᵒᵖ, ϱ, h)`, compatibly with `ϱ` and `h`.

This is the "by `paschke-unique-up-to-iso` it suffices to prove it for the
dilation constructed in `existence-paschke`" step with which the thesis
opens its proofs of **156II** `paschke-injective` (dils.tex:3886) and of
**157IV**.2/.3 `paschke-correspondence` (dils.tex:4042) — the two places
where a computation inside `𝒜 ⊗_φ ℬ` has to be exported to an abstract
`PaschkeTriple`.  It is exactly what those items were waiting for, and it
is available only now: it consumes `existence_paschke_5`. -/
theorem exists_paschke_iso_paschkeModule [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (D : PaschkeTriple 𝒜 ℬ) (hD : IsPaschkeDilationOf D ⇑φ) :
    ∃! ϑ : NMIUMap D.P (Ba ℬ M.X)ᵐᵒᵖ,
      Function.Bijective ⇑ϑ ∧ (∀ a, ϑ (D.ρ a) = M.ρ a) ∧
        ∀ c, M.h (ϑ c) = D.h c :=
  paschke_unique_up_to_iso ⇑φ D
    ⟨(Ba ℬ M.X)ᵐᵒᵖ,
      @vonNeumannAlgebra_mulOpposite (Ba ℬ M.X) _ _ _
        (ba_vonNeumannAlgebra M.selfDual),
      M.ρ, M.h⟩
    hD (existence_paschke_5 φ M)

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

/-! ### Auxiliary: the commutant of `ϱ(𝒜)` on the constructed module

The thesis proves parts 2 and 3 of **157IV** for the dilation constructed in
`existence_paschke` and transfers them to an arbitrary one at **157IX**
through `paschke-unique-up-to-iso` (`exists_paschke_iso_paschkeModule`).
The four lemmas below are that computation, on an arbitrary
`M : PaschkeModule φ`.

**Divergence from the thesis (157VII/157VIII), logged in `PROVING-LOG.md`.**
The thesis reads both parts off the *vector states of the dense image of
`η`* (`hilmod-fixed-on-V`): for the order embedding it shows
`⟨x̂, T x̂⟩ = ∑ᵢⱼ bᵢ* φ_T(aᵢ*aⱼ) bⱼ ≥ 0` for `x ∈ 𝒜 ⊙ ℬ` and concludes
`T ≥ 0` by ultranorm density, and for `T ≤ 1` in the surjectivity half it
compares `⟨x, Tx⟩_φ` with `⟨x,x⟩_φ` the same way.  An abstract
`PaschkeModule` carries no `η`, so neither is available here (this is the
same obstruction that `existence_paschke_5` met in **154VIII**).  What
replaces them is the *matrix* identity
`⟨a ⊗ b, T(a' ⊗ b')⟩ = b' φ_T(a' a*) b*` for `T` in the commutant
(`paschkeModule_inner_tprod_commutant`), which together with
`paschkeModule_inner_tprod_separating` and `paschkeModule_ba_ext` gives
**injectivity** of `t ↦ φ_t` outright; positivity of `T` is then not proved
by hand at all but obtained from the construction of part 3
(`T = W*W ≥ 0`), and `T ≤ 1` from `φ_{T + T'} = φ = φ_1` for the two
complementary maps `ψ` and `φ − ψ`, again by injectivity.  So **no density
argument and no `hilmod_fixed_on_V` is used anywhere in 157IV**. -/

/-- The adjoint of `ϱ(d)` is `ϱ(d*)`. -/
theorem paschkeModule_rho_adjoint (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (d : 𝒜) (x y : M.X) :
    (inner ℬ x ((M.ρ d).unop.1 y) : ℬ)
      = inner ℬ ((M.ρ (star d)).unop.1 x) y := by
  have h : ModuleAdjointTo ℬ ⇑(M.ρ (star d)).unop.1
      ⇑((star (M.ρ (star d)).unop : Ba ℬ M.X)).1 := baSubalgebra_star_spec _
  have h2 : (star (M.ρ (star d)).unop : Ba ℬ M.X) = (M.ρ d).unop := by
    rw [show M.ρ (star d) = star (M.ρ d) from map_star M.ρ.toStarAlgHom d,
      MulOpposite.unop_star, star_star]
  rw [← h2]
  exact (h x y).symm

/-- The Gram identity on an abstract Paschke module: the φ-compatibility
bound of **154II** holds with equality and `r = 1` for `⊗` itself
(`norm_sq_sum_ptprod` is the same statement for the concrete module). -/
theorem paschkeModule_norm_sq_sum_tprod (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    {n : ℕ} (a : Fin n → 𝒜) (b : Fin n → ℬ) :
    ‖∑ i, M.tprod (a i) (b i)‖ ^ 2
      = ‖∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j)‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ),
    Real.sq_sqrt (norm_nonneg _)]
  congr 1
  rw [CStarModule.inner_sum_left, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [CStarModule.inner_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact M.inner_tprod (a i) (a j) (b i) (b j)

/-- **157VII**, the matrix elements of an element of the commutant: for `t`
commuting with `ϱ(𝒜)`, the whole sesquilinear form of `t` on the elementary
tensors is `φ_t`, `⟨a ⊗ b, t(a' ⊗ b')⟩ = b' φ_t(a' a*) b*` (mirrored).
The thesis states only the diagonal `⟨x̂, T x̂⟩ = ∑ᵢⱼ bᵢ* φ_T(aᵢ*aⱼ) bⱼ`. -/
theorem paschkeModule_inner_tprod_commutant [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (t : (Ba ℬ M.X)ᵐᵒᵖ) (ht : ∀ a : 𝒜, t * M.ρ a = M.ρ a * t)
    (a a' : 𝒜) (b b' : ℬ) :
    (inner ℬ (M.tprod a b) (t.unop.1 (M.tprod a' b')) : ℬ)
      = b' * M.h (t * M.ρ (a' * star a)) * star b := by
  have htp : ∀ (x : 𝒜) (y : ℬ),
      M.tprod x y = y • (M.ρ x).unop.1 (M.tprod 1 1) := by
    intro x y
    rw [M.ρ_tprod, one_mul, M.compat.smul_action, mul_one]
  have hmod : ∀ (bb : ℬ) (x : M.X), t.unop.1 (bb • x) = bb • t.unop.1 x :=
    (moduleAdjointable_linear (𝒜 := ℬ) ⇑t.unop.1 t.unop.2).2.2
  have hRadj : ∀ (d : 𝒜) (x y : M.X),
      (inner ℬ ((M.ρ d).unop.1 x) y : ℬ)
        = inner ℬ x ((M.ρ (star d)).unop.1 y) := by
    intro d x y
    have h : ModuleAdjointTo ℬ ⇑(M.ρ d).unop.1
        ⇑((star (M.ρ d).unop : Ba ℬ M.X)).1 := baSubalgebra_star_spec _
    have h2 : (star (M.ρ d).unop : Ba ℬ M.X) = (M.ρ (star d)).unop := by
      rw [show M.ρ (star d) = star (M.ρ d) from map_star M.ρ.toStarAlgHom d]
      rfl
    rw [← h2]
    exact h x y
  have hRcomp : ∀ (d d' : 𝒜) (y : M.X),
      (M.ρ d').unop.1 ((M.ρ d).unop.1 y) = (M.ρ (d * d')).unop.1 y := by
    intro d d' y
    have h : ((M.ρ (d * d')).unop : Ba ℬ M.X)
        = ((M.ρ d').unop : Ba ℬ M.X) * ((M.ρ d).unop : Ba ℬ M.X) := by
      rw [show M.ρ (d * d') = M.ρ d * M.ρ d' from map_mul M.ρ.toStarAlgHom d d']
      rfl
    rw [h]
    rfl
  have hcomm : ∀ (d : 𝒜) (x : M.X),
      (M.ρ d).unop.1 (t.unop.1 x) = t.unop.1 ((M.ρ d).unop.1 x) := by
    intro d x
    exact congrArg (fun z : (Ba ℬ M.X)ᵐᵒᵖ => (MulOpposite.unop z).1 x) (ht d)
  have hh : ∀ d : 𝒜, (M.h (t * M.ρ d) : ℬ)
      = inner ℬ (M.tprod 1 1) (t.unop.1 ((M.ρ d).unop.1 (M.tprod 1 1))) := by
    intro d
    rw [M.h_def]
    exact congrArg _ (hcomm d _)
  rw [htp a b, htp a' b', hmod, CStarModule.inner_op_smul_right,
    CStarModule.inner_op_smul_left, hRadj, ← hcomm, hRcomp, hh,
    ← mul_assoc, hcomm]

/-- **157VII**, injectivity of `t ↦ φ_t`: an element of the commutant of
`ϱ(𝒜)` with `φ_t = 0` is zero.  This is the previous lemma together with
`paschkeModule_inner_tprod_separating` and `paschkeModule_ba_ext`, and it
replaces the thesis's density argument. -/
theorem paschkeModule_phiT_injective [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (t : (Ba ℬ M.X)ᵐᵒᵖ) (ht : ∀ a : 𝒜, t * M.ρ a = M.ρ a * t)
    (h0 : ∀ d : 𝒜, (M.h (t * M.ρ d) : ℬ) = 0) : t = 0 := by
  refine MulOpposite.unop_injective (paschkeModule_ba_ext φ M (S := t.unop)
    (R := 0) fun a' b' => ?_)
  refine paschkeModule_inner_tprod_separating φ M fun a b => ?_
  rw [paschkeModule_inner_tprod_commutant φ M t ht a a' b b', h0, mul_zero,
    zero_mul]

/-- Bounded module maps compose. -/
private theorem bmm_comp_aux {X Y Z : Type u} [NormedAddCommGroup X]
    [Module ℂ X] [SMul ℬ X] [CStarModule ℬ X] [NormedAddCommGroup Y]
    [Module ℂ Y] [SMul ℬ Y] [CStarModule ℬ Y] [NormedAddCommGroup Z]
    [Module ℂ Z] [SMul ℬ Z] [CStarModule ℬ Z] {F : X → Y} {G : Y → Z}
    {C D : ℝ}
    (hF : IsBoundedModuleMap (cstarBInner ℬ X) (cstarBInner ℬ Y) C F)
    (hG : IsBoundedModuleMap (cstarBInner ℬ Y) (cstarBInner ℬ Z) D G) :
    IsBoundedModuleMap (cstarBInner ℬ X) (cstarBInner ℬ Z) (|D| * |C|)
      (fun x => G (F x)) where
  add x y := by rw [hF.add, hG.add]
  smul_complex c x := by rw [hF.smul_complex, hG.smul_complex]
  smul b x := by rw [hF.smul, hG.smul]
  bound x := by
    have h1 := hG.bound (F x)
    have h2 := hF.bound x
    rw [cstarBInner_norm, cstarBInner_norm] at h1
    rw [cstarBInner_norm, cstarBInner_norm] at h2 ⊢
    have h3 : ‖F x‖ ≤ |C| * ‖x‖ := h2.trans (mul_le_mul_of_nonneg_right
      (le_abs_self C) (norm_nonneg x))
    have h4 : ‖G (F x)‖ ≤ |D| * ‖F x‖ := h1.trans (mul_le_mul_of_nonneg_right
      (le_abs_self D) (norm_nonneg (F x)))
    calc ‖G (F x)‖ ≤ |D| * ‖F x‖ := h4
      _ ≤ |D| * (|C| * ‖x‖) := mul_le_mul_of_nonneg_left h3 (abs_nonneg D)
      _ = |D| * |C| * ‖x‖ := by ring

/-- **157VIII**, surjectivity of `t ↦ φ_t` on the constructed module, in the
form the proof produces it: if `φ = ψ + δ` with `ψ`, `δ` ncp, then there is a
positive `T` in the commutant of `ϱ(𝒜)` with `φ_T = ψ`.

This is the thesis's argument verbatim, minus the bound `T ≤ 1` (which the
thesis gets from `hilmod-fixed-on-V` and which is instead obtained at the use
site by applying this lemma to `δ` as well and comparing with `φ_1`): the
identity `a ⊗ b ↦ a ⊗ b` is φ-compatible into `𝒜 ⊗_ψ ℬ` because
`⟨x,x⟩_ψ ≤ ⟨x,x⟩_φ`, the universal property of part 1 turns it into a bounded
module map `W`, self-duality of `𝒜 ⊗_ψ ℬ` gives `W*`
(**152VIII** `hilbmod_adjoint_exists`), and `T = W*W`. -/
theorem paschkeModule_phiT_surjective [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ ψ δ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (hsum : ∀ a, φ a = ψ a + δ a) :
    ∃ t : (Ba ℬ M.X)ᵐᵒᵖ, (∀ a : 𝒜, t * M.ρ a = M.ρ a * t) ∧ 0 ≤ t ∧
      ∀ d : 𝒜, (M.h (t * M.ρ d) : ℬ) = ψ d := by
  obtain ⟨N⟩ := existence_paschke ψ
  -- (1) `(a,b) ↦ a ⊗_ψ b` is φ-compatible, because `ψ ≤_ncp φ`
  have hcompat : PhiCompatible ⇑φ (fun a b => N.tprod a b) := by
    refine { add_left := N.compat.add_left, add_right := N.compat.add_right,
             smul_complex := N.compat.smul_complex,
             smul_action := N.compat.smul_action,
             bound := ⟨1, one_pos, fun n a b => ?_⟩ }
    rw [one_mul, paschkeModule_norm_sq_sum_tprod ψ N a b]
    refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (phi_gram_nonneg ψ a b) ?_
    have hd := phi_gram_nonneg δ a b
    have hsub : (∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j))
        - (∑ i, ∑ j, b i * ψ (a i * star (a j)) * star (b j))
        = ∑ i, ∑ j, b i * δ (a i * star (a j)) * star (b j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hsum, mul_add, add_mul]
      abel
    refine sub_nonneg.mp ?_
    rw [hsub]
    exact hd
  -- (2) the induced bounded module map `W : 𝒜 ⊗_φ ℬ → 𝒜 ⊗_ψ ℬ`
  obtain ⟨W, ⟨⟨C, hC⟩, hWt⟩, -⟩ :=
    M.univ N.X inferInstance inferInstance inferInstance inferInstance
      inferInstance N.selfDual _ hcompat
  set Wl : M.X →ₗ[ℂ] N.X :=
    { toFun := W, map_add' := hC.add, map_smul' := hC.smul_complex } with hWl
  have hbd : ∀ x, ‖Wl x‖ ≤ max C 0 * ‖x‖ := by
    intro x
    have h := hC.bound x
    rw [cstarBInner_norm, cstarBInner_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  set Wc : M.X →L[ℂ] N.X := Wl.mkContinuous (max C 0) hbd with hWc
  have hWcapp : ∀ x, Wc x = W x := fun _ => rfl
  obtain ⟨W', hW'⟩ := hilbmod_adjoint_exists M.selfDual Wc hC.smul
  -- (3) `T = W*W`
  have hZadj : ModuleAdjointTo ℬ (⇑(W'.comp Wc)) (⇑(W'.comp Wc)) := by
    intro x y
    show (inner ℬ (W' (Wc x)) y : ℬ) = inner ℬ x (W' (Wc y))
    rw [← CStarModule.star_inner (A := ℬ) y (W' (Wc x)), ← hW' y (Wc x),
      CStarModule.star_inner, hW' x (Wc y)]
  set Z : Ba ℬ M.X := ⟨W'.comp Wc, ⟨_, hZadj⟩⟩ with hZ
  have hZapp : ∀ x, Z.1 x = W' (Wc x) := fun _ => rfl
  -- (4) `W ϱ(a) = ϱ_ψ(a) W`, by uniqueness in the universal property
  have hWρ : ∀ (a₀ : 𝒜) (x : M.X),
      W ((M.ρ a₀).unop.1 x) = (N.ρ a₀).unop.1 (W x) := by
    intro a₀
    obtain ⟨F, -, hFuniq⟩ := M.univ N.X inferInstance inferInstance inferInstance
      inferInstance inferInstance N.selfDual _ (hcompat.mul_right φ a₀)
    obtain ⟨C₁, hC₁⟩ := ba_isBoundedModuleMap ((M.ρ a₀).unop)
    obtain ⟨C₂, hC₂⟩ := ba_isBoundedModuleMap ((N.ρ a₀).unop)
    have h1 : (fun x => W ((M.ρ a₀).unop.1 x)) = F := by
      refine hFuniq _ ⟨⟨_, bmm_comp_aux hC₁ hC⟩, fun a b => ?_⟩
      show W ((M.ρ a₀).unop.1 (M.tprod a b)) = N.tprod (a * a₀) b
      rw [M.ρ_tprod, hWt]
    have h2 : (fun x => (N.ρ a₀).unop.1 (W x)) = F := by
      refine hFuniq _ ⟨⟨_, bmm_comp_aux hC hC₂⟩, fun a b => ?_⟩
      show (N.ρ a₀).unop.1 (W (M.tprod a b)) = N.tprod (a * a₀) b
      rw [hWt, N.ρ_tprod]
    exact fun x => congrFun (h1.trans h2.symm) x
  -- (5) `T` commutes with `ϱ(𝒜)`
  have hZcomm : ∀ (a₀ : 𝒜) (x : M.X),
      (M.ρ a₀).unop.1 (Z.1 x) = Z.1 ((M.ρ a₀).unop.1 x) := by
    intro a₀ x
    refine eq_of_inner_right_eq (𝒜 := ℬ) fun y => ?_
    calc (inner ℬ y ((M.ρ a₀).unop.1 (Z.1 x)) : ℬ)
        = inner ℬ ((M.ρ (star a₀)).unop.1 y) (Z.1 x) :=
          paschkeModule_rho_adjoint φ M a₀ y _
      _ = inner ℬ (Wc ((M.ρ (star a₀)).unop.1 y)) (Wc x) := (hW' _ (Wc x)).symm
      _ = inner ℬ ((N.ρ (star a₀)).unop.1 (Wc y)) (Wc x) := by
            congr 1
            exact hWρ (star a₀) y
      _ = inner ℬ (Wc y) ((N.ρ a₀).unop.1 (Wc x)) :=
            (paschkeModule_rho_adjoint ψ N a₀ (Wc y) (Wc x)).symm
      _ = inner ℬ (Wc y) (Wc ((M.ρ a₀).unop.1 x)) := by
            congr 1
            exact (hWρ a₀ x).symm
      _ = inner ℬ y (Z.1 ((M.ρ a₀).unop.1 x)) := hW' y _
  refine ⟨MulOpposite.op Z, ?_, ?_, ?_⟩
  · intro a
    refine MulOpposite.unop_injective (Subtype.ext
      (ContinuousLinearMap.ext fun x => ?_))
    exact hZcomm a x
  · rw [mop_nonneg_iff]
    refine (ba_nonneg_iff Z).mpr fun x => ?_
    rw [hZapp, ← hW' x (Wc x)]
    exact CStarModule.inner_self_nonneg
  · intro d
    rw [M.h_def]
    show (inner ℬ (M.tprod 1 1) ((M.ρ d).unop.1 (Z.1 (M.tprod 1 1))) : ℬ) = ψ d
    rw [hZcomm, hZapp, ← hW' (M.tprod 1 1) (Wc _), hWcapp, hWcapp, M.ρ_tprod,
      hWt, hWt, one_mul, N.inner_tprod]
    simp

/-- A bijective ∗-homomorphism *reflects* positivity: `0 ≤ f x` forces
`0 ≤ x`.  (`starAlgHom_nonneg` of `A/VN/Basic.lean` is the forward half.)
Used to transport `[0,1]_{ϱ(𝒜)^□}` back along the nmiu-isomorphism of
**140VIII**, where the thesis says only "it is easy to see `ϑ` restricts to a
linear order isomorphism". -/
theorem starAlgHom_nonneg_reflect {P Q : Type u} [CStarAlgebra P]
    [PartialOrder P] [StarOrderedRing P] [CStarAlgebra Q] [PartialOrder Q]
    [StarOrderedRing Q] (f : P →⋆ₐ[ℂ] Q) (hinj : Function.Injective ⇑f)
    (hsurj : Function.Surjective ⇑f) {x : P} (h : 0 ≤ f x) : 0 ≤ x := by
  have hy : star (CFC.sqrt (f x)) * CFC.sqrt (f x) = f x := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (f x))).star_eq,
      CFC.sqrt_mul_sqrt_self _ h]
  obtain ⟨z, hz⟩ := hsurj (CFC.sqrt (f x))
  have hfz : f (star z * z) = f x := by rw [map_mul, map_star, hz]; exact hy
  rw [← hinj hfz]
  exact star_mul_self_nonneg z

/-- **140VIII** `paschke_unique_up_to_iso` in the shape parts 2 and 3 use it:
a bijective ∗-homomorphism `𝒫 → 𝒷ᵃ(𝒜 ⊗_φ ℬ)ᵐᵒᵖ` compatible with `ϱ` and
`h`.  This is `exists_paschke_iso_paschkeModule` with the normality clause
forgotten. -/
private theorem exists_paschke_starAlgHom [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (D : PaschkeTriple 𝒜 ℬ) (hD : IsPaschkeDilationOf D ⇑φ) :
    ∃ f : D.P →⋆ₐ[ℂ] (Ba ℬ M.X)ᵐᵒᵖ,
      Function.Bijective ⇑f ∧ (∀ a, f (D.ρ a) = M.ρ a) ∧
      (∀ c, M.h (f c) = D.h c) := by
  letI := D.vn
  obtain ⟨ϑ, ⟨hbij, hρ, hh⟩, -⟩ := exists_paschke_iso_paschkeModule φ M D hD
  exact ⟨ϑ.toStarAlgHom, hbij, hρ, hh⟩

/-- **157VI** (dils.tex:3966, the Set-up of the proof of **157IV**): for
`0 ≤ s` in the commutant of `ϱ(𝒜)` the map `φ_s = h(s ϱ(·))` is ncp,
because `√s` again commutes with `ϱ(𝒜)`, so `φ_s(a) = h(√s ϱ(a) √s)` is the
composite of the three ncp-maps `ϱ`, `ad_{√s}` and `h`.

Extracted from the proof of `paschke_correspondence_mem` (part 1), which is
now one line of it, and used by parts 2 and 3.  It is model-independent:
only `D` is needed, no `PaschkeModule`. -/
theorem exists_phiT_ncp [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (D : PaschkeTriple 𝒜 ℬ) (s : D.P) (hs0 : 0 ≤ s)
    (hsc : ∀ a : 𝒜, s * D.ρ a = D.ρ a * s) :
    ∃ δ : NCPMap 𝒜 ℬ, ∀ a : 𝒜, δ a = D.h (s * D.ρ a) := by
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
  have htc : ∀ a : 𝒜, t * D.ρ a = D.ρ a * t := fun a => (ht _ ⟨a, rfl⟩).symm
  obtain ⟨δ₁, hδ₁⟩ := exists_phiT_ncp D t h0 htc
  obtain ⟨δ₂, hδ₂⟩ := exists_phiT_ncp D (1 - t) (sub_nonneg.mpr h1)
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
linear).

**Not** the thesis's 157VII (see the section header above): from
`φ_t ≤_ncp φ_s` one reads off that `δ = φ_{s−t}` is ncp and that
`φ = δ + φ_{1−s+t}`, where the second summand is ncp by `exists_phiT_ncp`
because `0 ≤ 1−s+t`; part **3** then supplies a *positive* `u` in the
commutant with `φ_u = δ`, and `paschkeModule_phiT_injective` identifies `u`
with `s − t`.  So no positivity is proved by hand and no density argument is
needed.  Of the four order hypotheses only `s ≤ 1` and `0 ≤ t` are used. -/
theorem paschke_correspondence_embedding [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ) (D : PaschkeTriple 𝒜 ℬ)
    (hD : IsPaschkeDilationOf D ⇑φ) (s t : D.P)
    (hs : s ∈ commutant D.P (Set.range ⇑D.ρ)) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht : t ∈ commutant D.P (Set.range ⇑D.ρ)) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    NCPLe (phiT D t) (phiT D s) ↔ t ≤ s := by
  letI := D.vn
  have hsc : ∀ a : 𝒜, s * D.ρ a = D.ρ a * s := fun a => (hs _ ⟨a, rfl⟩).symm
  have htc : ∀ a : 𝒜, t * D.ρ a = D.ρ a * t := fun a => (ht _ ⟨a, rfl⟩).symm
  have hhsub : ∀ x y : D.P, (D.h (x - y) : ℬ) = D.h x - D.h y := fun x y =>
    map_sub D.h.toCompletelyPositiveMap.toLinearMap x y
  have hhadd : ∀ x y : D.P, (D.h (x + y) : ℬ) = D.h x + D.h y := fun x y =>
    map_add D.h.toCompletelyPositiveMap.toLinearMap x y
  constructor
  · rintro ⟨δ, hδ⟩
    -- `δ = φ_{s-t}`
    have h1 : ∀ a : 𝒜, (D.h ((s - t) * D.ρ a) : ℬ) = δ a := by
      intro a
      rw [sub_mul, hhsub]
      have h2 := hδ a
      show (D.h (s * D.ρ a) : ℬ) - D.h (t * D.ρ a) = δ a
      rw [show (D.h (s * D.ρ a) : ℬ) = D.h (t * D.ρ a) + δ a from h2]
      abel
    -- `ε = φ_{1-s+t}` is ncp, and `φ = δ + ε`
    obtain ⟨ε, hε⟩ := exists_phiT_ncp D (1 - s + t)
      (add_nonneg (sub_nonneg.mpr hs1) ht0)
      (fun a => by
        simp only [sub_mul, add_mul, mul_sub, mul_add, one_mul, mul_one, hsc a,
          htc a])
    have hsum : ∀ a : 𝒜, φ a = δ a + ε a := by
      intro a
      rw [hε a, ← h1 a, ← hhadd,
        show (s - t) * D.ρ a + (1 - s + t) * D.ρ a = 1 * D.ρ a from by
          noncomm_ring, one_mul]
      exact (hD.1 a).symm
    -- the constructed module, and the transport
    obtain ⟨M⟩ := existence_paschke φ
    obtain ⟨f, hbij, hfρ, hfh⟩ := exists_paschke_starAlgHom φ M D hD
    have hphi : ∀ (u : D.P) (a : 𝒜),
        (D.h (u * D.ρ a) : ℬ) = M.h (f u * M.ρ a) := by
      intro u a
      rw [← hfρ, ← map_mul, hfh]
    have hfcomm : ∀ u : D.P, (∀ a : 𝒜, u * D.ρ a = D.ρ a * u) →
        ∀ a : 𝒜, f u * M.ρ a = M.ρ a * f u := by
      intro u hu a
      rw [← hfρ, ← map_mul, ← map_mul, hu]
    -- surjectivity on the constructed module
    obtain ⟨u, hucomm, hu0, huφ⟩ := paschkeModule_phiT_surjective φ δ ε M hsum
    have hstc : ∀ a : 𝒜, (s - t) * D.ρ a = D.ρ a * (s - t) := fun a => by
      simp only [sub_mul, mul_sub, hsc a, htc a]
    have hMhsub : ∀ x y : (Ba ℬ M.X)ᵐᵒᵖ, (M.h (x - y) : ℬ) = M.h x - M.h y :=
      fun x y => map_sub M.h.toCompletelyPositiveMap.toLinearMap x y
    -- `u = f (s - t)` by injectivity
    have hzero : u - f (s - t) = 0 := by
      refine paschkeModule_phiT_injective φ M _ ?_ ?_
      · intro a
        rw [sub_mul, mul_sub, hucomm a, hfcomm (s - t) hstc a]
      · intro d
        rw [sub_mul, hMhsub, huφ d, ← hphi, h1 d, sub_self]
    have hu : u = f (s - t) := sub_eq_zero.mp hzero
    have h0 : (0 : (Ba ℬ M.X)ᵐᵒᵖ) ≤ f (s - t) := hu ▸ hu0
    exact sub_nonneg.mp (starAlgHom_nonneg_reflect f hbij.1 hbij.2 h0)
  · intro hts
    obtain ⟨δ, hδ⟩ := exists_phiT_ncp D (s - t) (sub_nonneg.mpr hts)
      (fun a => by simp only [sub_mul, mul_sub, hsc a, htc a])
    refine ⟨δ, fun a => ?_⟩
    show (D.h (s * D.ρ a) : ℬ) = D.h (t * D.ρ a) + δ a
    rw [hδ a, ← hhadd,
      show t * D.ρ a + (s - t) * D.ρ a = s * D.ρ a from by noncomm_ring]

/-- **157IV** (`paschke-correspondence`, dils.tex:3950, Theorem), part 3:
`t ↦ φ_t` maps `[0,1]_{ϱ(𝒜)'}` *onto* `[0,φ]_ncp`.

**157VIII** transcribed on the constructed module
(`paschkeModule_phiT_surjective`: `T = W*W` for the map `W` induced by
`a ⊗_φ b ↦ a ⊗_ψ b`) and transported to `D` by **157IX**, i.e. by
`exists_paschke_iso_paschkeModule`.  The one step that is not the thesis's is
`T ≤ 1`: instead of `hilmod-fixed-on-V` we run the construction on `φ − ψ` as
well, obtaining `T'` with `φ_{T+T'} = φ = φ_1`, so `T + T' = 1` by
`paschkeModule_phiT_injective`. -/
theorem paschke_correspondence_surjective [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ) (D : PaschkeTriple 𝒜 ℬ)
    (hD : IsPaschkeDilationOf D ⇑φ) (ψ : 𝒜 → ℬ)
    (hψ : ψ ∈ ncpInterval ⇑φ) :
    ∃ t : D.P, t ∈ commutant D.P (Set.range ⇑D.ρ) ∧ 0 ≤ t ∧ t ≤ 1 ∧
      phiT D t = ψ := by
  letI := D.vn
  obtain ⟨⟨δ, hδ⟩, ⟨ε, hε⟩⟩ := hψ
  have hψδ : ∀ a, ψ a = δ a := fun a => by rw [hδ a, zero_add]
  have hsum : ∀ a, φ a = δ a + ε a := fun a => by rw [hε a, hψδ a]
  obtain ⟨M⟩ := existence_paschke φ
  obtain ⟨f, hbij, hfρ, hfh⟩ := exists_paschke_starAlgHom φ M D hD
  obtain ⟨u, hucomm, hu0, huφ⟩ := paschkeModule_phiT_surjective φ δ ε M hsum
  obtain ⟨v, hvcomm, hv0, hvφ⟩ := paschkeModule_phiT_surjective φ ε δ M (fun a => by
    rw [hsum a, add_comm])
  have hMhadd : ∀ x y : (Ba ℬ M.X)ᵐᵒᵖ, (M.h (x + y) : ℬ) = M.h x + M.h y :=
    fun x y => map_add M.h.toCompletelyPositiveMap.toLinearMap x y
  have hMhsub : ∀ x y : (Ba ℬ M.X)ᵐᵒᵖ, (M.h (x - y) : ℬ) = M.h x - M.h y :=
    fun x y => map_sub M.h.toCompletelyPositiveMap.toLinearMap x y
  -- `u + v = 1`, by injectivity
  have huv : u + v = 1 := by
    have hz : u + v - 1 = 0 := by
      refine paschkeModule_phiT_injective φ M _ ?_ ?_
      · intro a
        rw [sub_mul, mul_sub, add_mul, mul_add, hucomm a, hvcomm a, one_mul,
          mul_one]
      · intro d
        rw [sub_mul, hMhsub, add_mul, hMhadd, huφ d, hvφ d, one_mul,
          paschkeModule_h_ρ, hsum d, sub_self]
    exact sub_eq_zero.mp hz
  -- transport back
  obtain ⟨w, hw⟩ := hbij.2 u
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    refine hbij.1 ?_
    rw [map_mul, map_mul, hw, hfρ, hucomm a]
  · exact starAlgHom_nonneg_reflect f hbij.1 hbij.2 (by rw [hw]; exact hu0)
  · refine sub_nonneg.mp (starAlgHom_nonneg_reflect f hbij.1 hbij.2 ?_)
    rw [map_sub, map_one, hw, show (1 : (Ba ℬ M.X)ᵐᵒᵖ) - u = v from by
      rw [← huv]; abel]
    exact hv0
  · funext a
    show (D.h (w * D.ρ a) : ℬ) = ψ a
    rw [← hfh (w * D.ρ a), map_mul, hw, hfρ, huφ a, hψδ a]

end Correspondence

end Theses.B.Dils
