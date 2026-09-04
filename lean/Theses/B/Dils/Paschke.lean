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

— the ℂ-action is *conjugated* too.  (It has to be: `[·,·]` is
conjugate-linear in its first argument and so is Mathlib's `⟨·,·⟩`, so
`⟨x,y⟩ = [y,x]` can only be ℂ-sesquilinear for the conjugated action.)

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
(`paschkeModule_h_ρ`), so `IsPaschkeDilationOf` (`Stinespring.lean:3367`),
which asks for `h (ρ a) = φ a` with no `star`, is correct as it stands
(ruling of the author, Bas, 2026-08-15: "the definition of Paschke dilation
should not include the star").

Two earlier renderings are recorded as machine-checked negative results:
`paschke_inner_conj_forces_zero` (the inner product `b' φ(a'* a) b*`,
i.e. no `star` on the `𝒜`-argument of `tprod`, forces `φ = 0`) and
`paschke_rho_forces_cyclic` (the inner product below together with a `ρ`
into `𝒷ᵃ(X)` rather than `𝒷ᵃ(X)ᵐᵒᵖ` forces `φ` to be cyclic, which fails
for `φ = id` on `M₂`).  Both leave `PaschkeModule` uninhabited.
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

**154I** (dils.tex:3537): introduction — nothing to formalize. -/

section Existence

variable {𝒜 ℬ : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **154II** (`phi-compatible-paschke`, dils.tex:3549, Definition): for an
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
`a = e₀₀`, `b = e₁₀` (left side `‖e₁₁‖ = 1`, right side `0`). -/
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
`(a,b) ↦ T (a₀a) b`).  Only the bound needs an argument, and it is the
thesis's own display at dils.tex:3689–3696 (**154VI**, `2: ϱ`, dils.tex:3670):
with the row vector `a = (a₁ ⋯ aₙ)` and the column vector `b`,

  `‖∑ᵢ B(aᵢ,bᵢ)‖² = ‖b* (Mₙφ)(a*a₀*a₀a) b‖ ≤ ‖a₀*a₀‖ ‖b* (Mₙφ)(a*a) b‖`.

Mirrored, the two matrices are `A₁ = (aᵢa₀(aⱼa₀)*)ᵢⱼ` and `A₀ = (aᵢaⱼ*)ᵢⱼ`
in `M_n(𝒜) = CStarMatrix (Fin n) (Fin n) 𝒜`, and the three steps are:
`A₁ ≤ ‖a₀‖²·A₀` — because `(‖a₀‖²·A₀ − A₁)ᵢⱼ = aᵢ(‖a₀‖²1 − a₀a₀*)aⱼ*`, whose
conjugate by a vector `c` is `u(‖a₀‖²1 − a₀a₀*)u*` for `u = ∑ᵢ cᵢ*aᵢ`, so
**33II** (`cstar_matrix_positive_iff`, the row-vector form of positivity)
applies; then `Mₙφ` is positive by complete positivity of `φ` (**34IV**,
`cp_iff`); then **33II** again, conjugating by the column vector `b`, gives
`S₁ ≤ ‖a₀‖²·S₀` in ℬ, and the norms follow since `0 ≤ S₁`.

Only the *witness* differs from the thesis: **154II** asks for an `r > 0`,
and the display gives `r‖a₀‖²`, which is `0` when `a₀ = 0`; the witness taken
here is the (larger) `r(‖a₀‖² + 1)`, the thesis's inequality being used
unchanged.

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
  -- **34IV**: `M_N φ` is a positive map for every `N`
  have hcpmat : ∀ (N : ℕ) (A : CStarMatrix (Fin N) (Fin N) 𝒜), 0 ≤ A → 0 ≤ A.map ⇑ψ :=
    (cp_iff ψ).out 0 1 |>.mp hcp
  obtain ⟨r, hr0, hr⟩ := hT.bound
  refine { add_left := fun a a' b => by
             rw [add_mul]; exact hT.add_left _ _ _
           add_right := fun a b b' => hT.add_right _ _ _
           smul_complex := fun c a b => by
             rw [smul_mul_assoc]; exact hT.smul_complex _ _ _
           smul_action := fun a b c => hT.smul_action _ _ _
           bound := ⟨r * (‖a₀‖ ^ 2 + 1), by positivity, fun n a b => ?_⟩ }
  -- `a₀a₀* ≤ ‖a₀a₀*‖·1 = ‖a₀‖²·1`, the thesis's `‖a₀*a₀‖` step
  have hcast : ∀ t : ℝ, algebraMap ℝ 𝒜 t = ((t : ℂ)) • (1 : 𝒜) := by
    intro t
    rw [IsScalarTower.algebraMap_apply ℝ ℂ 𝒜, Algebra.algebraMap_eq_smul_one]
    norm_num
  have hnorm2 : ‖a₀ * star a₀‖ = ‖a₀‖ ^ 2 := by
    rw [CStarRing.norm_self_mul_star]; ring
  have hle : a₀ * star a₀ ≤ ((‖a₀‖ ^ 2 : ℝ) : ℂ) • (1 : 𝒜) := by
    have h1 := (IsSelfAdjoint.mul_star_self a₀).le_algebraMap_norm_self
    rw [hcast, hnorm2] at h1
    exact h1
  set t : 𝒜 := ((‖a₀‖ ^ 2 : ℝ) : ℂ) • (1 : 𝒜) - a₀ * star a₀ with htdef
  have htnn : (0 : 𝒜) ≤ t := sub_nonneg.mpr hle
  set S0 : ℬ := ∑ i, ∑ j, b i * ψ (a i * star (a j)) * star (b j) with hS0def
  set S1 : ℬ := ∑ i, ∑ j, b i * ψ (a i * a₀ * star (a j * a₀)) * star (b j) with hS1def
  -- the thesis's two matrices `a*a₀*a₀a` and `a*a` over 𝒜 (mirrored)
  set A1 : CStarMatrix (Fin n) (Fin n) 𝒜 :=
    CStarMatrix.ofMatrix (Matrix.of fun i j => a i * a₀ * star (a j * a₀)) with hA1def
  set A0 : CStarMatrix (Fin n) (Fin n) 𝒜 :=
    CStarMatrix.ofMatrix (Matrix.of fun i j => a i * star (a j)) with hA0def
  have hA1app : ∀ i j, A1 i j = a i * a₀ * star (a j * a₀) := by
    intro i j; rw [hA1def]; simp [CStarMatrix.ofMatrix_apply]
  have hA0app : ∀ i j, A0 i j = a i * star (a j) := by
    intro i j; rw [hA0def]; simp [CStarMatrix.ofMatrix_apply]
  have hentry : ∀ i j, (((‖a₀‖ ^ 2 : ℝ) : ℂ) • A0 - A1) i j = a i * t * star (a j) := by
    intro i j
    rw [CStarMatrix.sub_apply, CStarMatrix.smul_apply, hA1app, hA0app, htdef]
    rw [mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, star_mul]
    noncomm_ring
  -- `a*a₀*a₀a ≤ ‖a₀‖²·a*a` in `M_n(𝒜)`, by **33II** at the vector `c`
  have hmatle : A1 ≤ ((‖a₀‖ ^ 2 : ℝ) : ℂ) • A0 := by
    rw [← sub_nonneg, cstar_matrix_positive_iff]
    intro c
    have hstar : star (∑ i, star (c i) * a i) = ∑ j, star (a j) * c j := by
      simp [star_sum, star_mul]
    have hkey : ∑ i, ∑ j, star (c i) * ((((‖a₀‖ ^ 2 : ℝ) : ℂ) • A0 - A1) i j) * c j
        = (∑ i, star (c i) * a i) * t * star (∑ i, star (c i) * a i) := by
      simp only [hentry]
      calc ∑ i, ∑ j, star (c i) * (a i * t * star (a j)) * c j
          = (∑ i, star (c i) * a i * t) * (∑ j, star (a j) * c j) := by
            rw [Finset.sum_mul_sum]
            exact Finset.sum_congr rfl fun i _ =>
              Finset.sum_congr rfl fun j _ => by noncomm_ring
        _ = (∑ i, star (c i) * a i) * t * star (∑ i, star (c i) * a i) := by
            simp only [hstar, Finset.sum_mul]
    rw [hkey]
    exact star_right_conjugate_nonneg htnn _
  -- apply `M_n φ` and conjugate by the column vector `b`, again by **33II**
  have hentry2 : ∀ i j, ((((‖a₀‖ ^ 2 : ℝ) : ℂ) • A0 - A1).map ⇑ψ) i j
      = ((‖a₀‖ ^ 2 : ℝ) : ℂ) • ψ (a i * star (a j)) - ψ (a i * a₀ * star (a j * a₀)) := by
    intro i j
    rw [CStarMatrix.map_apply, CStarMatrix.sub_apply, CStarMatrix.smul_apply, hA0app, hA1app,
      map_sub, map_smul]
  have hS1le : S1 ≤ ((‖a₀‖ ^ 2 : ℝ) : ℂ) • S0 := by
    have h := (cstar_matrix_positive_iff _).mp (hcpmat n _ (sub_nonneg.mpr hmatle))
      (fun i => star (b i))
    simp only [star_star, hentry2] at h
    have hsum2 : ∑ i, ∑ j, b i * (((‖a₀‖ ^ 2 : ℝ) : ℂ) • ψ (a i * star (a j))
          - ψ (a i * a₀ * star (a j * a₀))) * star (b j)
        = ((‖a₀‖ ^ 2 : ℝ) : ℂ) • S0 - S1 := by
      rw [hS0def, hS1def, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
    rw [hsum2] at h
    exact sub_nonneg.mp h
  have hS1nn : (0 : ℬ) ≤ S1 := by
    have h := hcp n (fun i => star (a i * a₀)) (fun i => star (b i))
    simp only [star_star] at h
    exact h
  have hnormS1 : ‖S1‖ ≤ ‖a₀‖ ^ 2 * ‖S0‖ := by
    have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le hS1nn hS1le
    rwa [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖a₀‖ ^ 2)] at h
  have hkey := hr n (fun i => a i * a₀) b
  simp only [← hψ] at hS0def hS1def
  calc ‖∑ i, T (a i * a₀) (b i)‖ ^ 2
      ≤ r * ‖S1‖ := by rw [hS1def]; simpa [hψ] using hkey
    _ ≤ r * (‖a₀‖ ^ 2 * ‖S0‖) := mul_le_mul_of_nonneg_left hnormS1 hr0.le
    _ ≤ r * ((‖a₀‖ ^ 2 + 1) * ‖S0‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hr0.le
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ = r * (‖a₀‖ ^ 2 + 1)
          * ‖∑ i, ∑ j, b i * φ (a i * star (a j)) * star (b j)‖ := by
        rw [hS0def]; ring

/-- **154III** (`existence-paschke`, dils.tex:3566, Theorem), the data: the
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
`star` anywhere — see the head of the file for the author's ruling. -/
theorem paschkeModule_h_ρ (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ) (a : 𝒜) :
    M.h (M.ρ a) = φ a := by
  rw [M.h_def, M.ρ_tprod, M.inner_tprod]
  simp

/-- **Negative result** (kept in the tree).
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

/-- **Negative result** (kept in the tree).
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

The one step the thesis compresses into two lines is normality of `ϱ`:
dils.tex gets it from **153IV** `hilbmod-adj-vector-ncp` and **49IV**
`mn-vna`, by factoring the vector form `d ↦ ∑ᵢⱼ bᵢ φ(aᵢ d aⱼ*) bⱼ*` of `ϱ`
as

  `𝒜 → Mₙ𝒜 → Mₙℬ → ℬ`,

and that is the route taken here (`pTheta_normal`): all three factors are in
the tree — `hilbmod_adj_vector_ncp` in `SelfDualCompletion.lean`, `mn_vna_3`
and the third clause of `mn_vna_2` in `A/VN/Basic.lean` — and `compNP`
composes them with an np-functional of `ℬ` into one np-functional of `𝒜`. -/

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

/-- The φ-inner product on `𝒜 ⊙ ℬ` (**154V**, mirrored):
`⟨a ⊗ b, a' ⊗ b'⟩ = b' φ(a' a*) b*`.  (The formula is displayed in 154V,
the first point of the *proof* of **154III**; 154IV is only that proof's
header point.) -/
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
bound of **154II** holds with equality.  The identity itself is the display
of **154V**; 154II is the definition whose bound it saturates. -/
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

/-- **154III**.2, the analytic core: the vector form `d ↦ ⟨v, ϱ(d) v⟩` of
`ϱ`, paired with an np-functional `ω` of `ℬ`, is normal.

The thesis's own argument (dils.tex, parsec 1540, point 60).  Writing
`v = ∑ᵢ aᵢ ⊗ bᵢ`, the vector form factors as a composite of three normal
positive maps

  `𝒜  →  Mₙ𝒜  →  Mₙℬ  →  ℬ`,
  `d  ↦  (aᵢ d aⱼ*)ᵢⱼ  ↦  (φ(aᵢ d aⱼ*))ᵢⱼ  ↦  ∑ᵢⱼ bᵢ φ(aᵢ d aⱼ*) bⱼ*`,

which are **153IV** `hilbmod_adj_vector_ncp`, **49IV**.3 `mn_vna_3` (the
entrywise `Mₙφ` is normal) and the third clause of **49IV**.2 `mn_vna_2`
(`M ↦ ∑ᵢⱼ cᵢ* Mᵢⱼ cⱼ` preserves suprema).  `compNP` composes the three with
`ω` into a single np-functional of `𝒜`, whose normality is the claim. -/
theorem pTheta_normal (ω : NPFunctional ℬ) (v : 𝒜 ⊗[ℂ] ℬ) :
    PreservesDirSups (fun d : 𝒜 => (ω (pTheta φ v d) : ℂ)) := by
  obtain ⟨n, a, b, rfl⟩ := exists_fin_tmul v
  -- **153IV**: `d ↦ (aᵢ d aⱼ*)ᵢⱼ : 𝒜 → Mₙ𝒜` is ncp.
  obtain ⟨L, hentry, hcp, hLn⟩ :=
    hilbmod_adj_vector_ncp (𝒜 := 𝒜) (n := n) (fun i => star (a i))
  have hentry' : ∀ (d : 𝒜) (i j : Fin n), L d i j = a i * d * star (a j) := by
    intro d i j; rw [hentry, star_star]
  have hLpos : ∀ d : 𝒜, 0 ≤ d → 0 ≤ L d := by
    intro d hd
    have hsa : star (CFC.sqrt d) = CFC.sqrt d :=
      IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg d)
    have hd' : star (CFC.sqrt d) * CFC.sqrt d = d := by
      rw [hsa]; exact CFC.sqrt_mul_sqrt_self d hd
    simpa [hd'] using hcp 1 (fun _ => CFC.sqrt d) (fun _ => 1)
  set F₁ : 𝒜 →ₚ[ℂ] CStarMatrix (Fin n) (Fin n) 𝒜 :=
    { toFun := ⇑L
      map_add' := map_add L
      map_smul' := map_smul L
      monotone' := fun x y h => by
        have h0 := hLpos (y - x) (sub_nonneg.mpr h)
        rwa [map_sub, sub_nonneg] at h0 }
  -- **49IV**.3 `mn_vna_3`: the entrywise `Mₙφ : Mₙ𝒜 → Mₙℬ` is normal.
  set F₂ : CStarMatrix (Fin n) (Fin n) 𝒜 →ₚ[ℂ] CStarMatrix (Fin n) (Fin n) ℬ :=
    { toFun := fun M => CStarMatrix.mapₗ φ.toCompletelyPositiveMap.toLinearMap M
      map_add' := map_add _
      map_smul' := map_smul _
      monotone' := fun X Y h => by
        have h0 := φ.toCompletelyPositiveMap.map_cstarMatrix_nonneg' n (Y - X)
          (sub_nonneg.mpr h)
        rw [← sub_nonneg]
        refine le_of_le_of_eq h0 ?_
        ext i j
        show (φ.toCompletelyPositiveMap ((Y - X) i j) : ℬ)
            = φ.toCompletelyPositiveMap (Y i j) - φ.toCompletelyPositiveMap (X i j)
        rw [show ((Y - X) i j : 𝒜) = Y i j - X i j from rfl]
        exact map_sub φ.toCompletelyPositiveMap _ _ }
  -- **49IV**.2 `mn_vna_2`, third clause: `M ↦ ∑ᵢⱼ bᵢ Mᵢⱼ bⱼ* : Mₙℬ → ℬ` is normal.
  set c : Fin n → ℬ := fun i => star (b i) with hc
  set F₃ : CStarMatrix (Fin n) (Fin n) ℬ →ₚ[ℂ] ℬ :=
    { toFun := fun M => matForm c c M
      map_add' := matForm_add_matrix c c
      map_smul' := fun r M => matForm_smul_matrix r c c M
      monotone' := fun _ _ h => matForm_mono h c }
  set ν : NPFunctional 𝒜 :=
    compNP F₁ hLn (compNP F₂ (mn_vna_3 n φ) (compNP F₃ (mn_vna_2 n c c).2.2 ω))
  have heq : (fun d : 𝒜 => (ω (pTheta φ (∑ i, a i ⊗ₜ[ℂ] b i) d) : ℂ))
      = fun d : 𝒜 => (ν d : ℂ) := by
    funext d
    have hcomp : (ν d : ℂ) = ω (∑ i, ∑ j, star (c i) * φ (L d i j) * c j) := rfl
    rw [hcomp, pTheta_sum]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    rw [hentry', hc, star_star]
  rw [heq]
  exact ν.preservesDirSups'

end Theta

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

/-- **154III**.2: `ϱ` is normal.  The thesis's route throughout
(`normal-faithful` + `hilmod-fixed-on-V`): the vector forms
`d ↦ ⟨η v, ϱ(d) η v⟩` are normal by `pTheta_normal` above, i.e. by the
thesis's factorisation of them through `Mₙ𝒜 → Mₙℬ` (**153IV** and **49IV**
`mn-vna`). -/
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


/-- **154III** (`existence-paschke`, dils.tex:3566, Theorem), parts 1–3,
as a *term*: the module `𝒜 ⊗_φ ℬ` built on a self-dual completion `E` of
`(𝒜 ⊙ ℬ, ⟨·,·⟩_φ)`, with `⊗ = η(· ⊗ ·)`, `ϱ` and `h(T) = ⟨η(1⊗1), T η(1⊗1)⟩`.

`existence_paschke` below is this term, with `E` discharged by **150II**
`dils_completion`.  The term is kept accessible because the *concrete* `η`
is what **157VII** needs (`hilmod-fixed-on-V` is a statement about `η`, and
an abstract `PaschkeModule` carries none). -/

noncomputable def paschkeModuleOf [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (E : SelfDualCompletion.{u, u, u} (ptensBInner φ)) :
    PaschkeModule φ where
  X := E.X
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
  h_def := fun T => rfl

@[simp] theorem paschkeModuleOf_tprod [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ)
    (E : SelfDualCompletion.{u, u, u} (ptensBInner φ)) (a : 𝒜) (b : ℬ) :
    (paschkeModuleOf φ E).tprod a b = E.η (a ⊗ₜ[ℂ] b) := rfl

/-- **154III** (`existence-paschke`, dils.tex:3566, Theorem), parts 1–3:
the module `𝒜 ⊗_φ ℬ`, the representation `ϱ` and the vector state `h`
exist.

The bundle is not vacuous: `paschkeModuleId` exhibits `ℬ` itself as
`ℬ ⊗_id ℬ`, so every field below is jointly satisfiable for a non-zero
`φ`. -/
theorem existence_paschke [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) : Nonempty (PaschkeModule φ) := by
  obtain ⟨E⟩ := dils_completion (𝒷 := ℬ) (V := 𝒜 ⊗[ℂ] ℬ) (ptensBInner φ)
  exact ⟨paschkeModuleOf φ E⟩

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

/-- **154III** (`existence-paschke`, dils.tex:3566, Theorem), part 2,
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

/-- **154III** (`existence-paschke`, dils.tex:3566, Theorem), part 4
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

/-- **154VIII** (`paschke-uniqueness`, dils.tex:3727): a mediating ncp-map
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

/-- **154III** (`existence-paschke`, dils.tex:3566, Theorem), part 5:
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
  -- `h ∘ ϱ = φ` is `paschkeModule_h_ρ`; the universal property is
  -- **154IV**–**154X**.
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
`PaschkeTriple`.  It is stated here because it consumes
`existence_paschke_5`. -/
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

`ℬ` itself is `ℬ ⊗_id ℬ`.  This is the check that catches a mirroring
defect in `PhiCompatible.bound`, `inner_tprod` or `ρ` — any of which leaves
the bundle uninhabited; `vnTensor_mul_complex` in `SelfDual.lean` is the
model.  It also exhibits the `ᵐᵒᵖ` concretely: the
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

theorem rightMul_star (t : ℬ) : star (rightMul t) = rightMul (star t) := by
  refine Subtype.ext (ContinuousLinearMap.ext fun x => ?_)
  have h1 : ModuleAdjointTo ℬ ⇑(rightMul t).1 ⇑((star (rightMul t) : Ba ℬ ℬ)).1 :=
    baSubalgebra_star_spec _
  have h2 : ModuleAdjointTo ℬ ⇑(rightMul t).1 ⇑(rightMul (star t)).1 := by
    intro x y
    show (y * star (x * t) : ℬ) = (y * star t) * star x
    rw [star_mul, mul_assoc]
  exact congrFun (moduleAdjointTo_unique (𝒜 := ℬ) _ _ _ h1 h2) x

/-- `t ↦ R_t` is a ∗-isomorphism `ℬ ≅ 𝒷ᵃ(ℬ)ᵐᵒᵖ`.  Surjectivity is the
ℬ-linearity of adjointable operators (`moduleAdjointable_linear`):
`T x = T (x • 1) = x · T 1`.

**Not a statement of the thesis.**  **141III** gives only the example "a
C*-algebra `ℬ` is a self-dual Hilbert `ℬ`-module over itself, with
`⟨a,b⟩ = a*b`" and **143I** only the definition of `𝒷ᵃ(X)`; the
∗-isomorphism `ℬ ≅ 𝒷ᵃ(ℬ)ᵐᵒᵖ` is a Lean-side addition — true, and needed to
inhabit `PaschkeModule` (see `paschkeModuleId` below).  The two points are
cited here as *provenance* for the objects it relates, not as its source. -/
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

Kept in the tree deliberately: a mirroring defect leaves `PaschkeModule`
*uninhabited* and the theorems of this file vacuous, and only a concrete
example catches that. -/
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

**155I**, **155III** (dils.tex:3849, 3867): discussion — nothing to
formalize. -/

/-! ### The KSGNS construction

The thesis states **155II** as Kasparov's theorem and cites it (155III leaves
even its universal property open), so there is no printed proof to transcribe:
what follows is the standard KSGNS construction, written from scratch.  It has
three parts.

1. `ksgns_gram_nonneg`: complete positivity of `φ : 𝒜 → 𝒷ᵃ(X)` makes the form
   `⟨x ⊗ a, x' ⊗ a'⟩ = ⟪x, φ(a* a') x'⟫` on `X ⊙ 𝒜` positive.  The tree's
   `IsCompletelyPositiveMap` is the *sesquilinear* form of complete positivity
   (**10II**), and **34IV** `cp_iff` turns it into positivity of the matrix
   `[φ(aᵢ* aⱼ)]` over the C*-algebra `𝒷ᵃ(X)` (**143IV**); writing that matrix
   as `star Y * Y` turns the Gram sum into `∑ₖ ⟪yₖ, yₖ⟫`.  **No isomorphism
   `Mₙ(𝒷ᵃ(X)) ≅ 𝒷ᵃ(Xⁿ)` is needed.**

2. The **norm** completion of a module with a (possibly indefinite) `BInner`,
   `NC B` → `UniformSpace.Completion (NC B)`: the seminorm is **142V**
   (`module_seminorm_1`, `module_seminorm_2`), the completion is Mathlib's
   Hausdorff completion of the seminormed group (so the null vectors are
   quotiented out automatically), and the inner product is extended one slot
   at a time by `clmExtend`.  This is *not* `dils_completion` (**150II**),
   which is the ultranorm/self-dual completion and needs a von Neumann `𝒷`;
   here `ℬ` is only a C*-algebra.  `IsLinearAction` records the one thing a
   semidefinite form does not give for free: that the `ℬ`-action is ℂ-linear.

3. `ϱ(a₀)(x ⊗ a) = x ⊗ (a₀a)`, bounded by `‖a₀‖` because
   `‖a₀‖² - a₀*a₀ = c*c` makes the defect another Gram form, and
   `T(x) = x ⊗ 1` with adjoint `T*(x ⊗ a) = φ(a)x`; then
   `T* ϱ(a) T = φ(a)` on the nose.
-/

section KSGNSGram

variable {𝒜 ℬ : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  {X : Type u} [NormedAddCommGroup X] [Module ℂ X] [SMul ℬ X]
  [CStarModule ℬ X] [CompleteSpace X]

private theorem ks_sum_comm₃ {N : ℕ} {M : Type*} [AddCommMonoid M]
    (h : Fin N → Fin N → Fin N → M) :
    ∑ i, ∑ j, ∑ k, h i j k = ∑ k, ∑ i, ∑ j, h i j k := by
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]

private theorem ks_exists_star_mul_self {M : Type*} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] {a : M} (ha : 0 ≤ a) : ∃ b, a = star b * b :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha

/-- The Gram form `∑ᵢⱼ ⟪xᵢ, φ(aᵢ* aⱼ) xⱼ⟫` of a cp-map `φ : 𝒜 → 𝒷ᵃ(X)` is
positive: `[φ(aᵢ* aⱼ)]ᵢⱼ ≥ 0` in `Mₙ(𝒷ᵃ(X))` by **34IV** `cp_iff`, so it is
`star Y * Y`, and the sum becomes `∑ₖ ⟪∑ᵢ Yₖᵢxᵢ, ∑ⱼ Yₖⱼxⱼ⟫`. -/
private theorem ksgns_gram_nonneg (φ : 𝒜 →ₗ[ℂ] Ba ℬ X) (hφ : IsCompletelyPositiveMap φ)
    {n : ℕ} (a : Fin n → 𝒜) (x : Fin n → X) :
    0 ≤ ∑ i, ∑ j, (inner ℬ (x i) ((φ (star (a i) * a j)).1 (x j)) : ℬ) := by
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore ℬ)
  have h3 : ∀ (N : ℕ) (a : Fin N → 𝒜),
      0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => φ (star (a i) * a j)) :=
    (cp_iff φ).out 0 2 |>.mp hφ
  set M : CStarMatrix (Fin n) (Fin n) (Ba ℬ X) :=
    CStarMatrix.ofMatrix (Matrix.of fun i j => φ (star (a i) * a j)) with hM
  have hM0 : 0 ≤ M := h3 n a
  obtain ⟨Y, hMY⟩ := ks_exists_star_mul_self hM0
  have hentry : ∀ i j, (φ (star (a i) * a j) : Ba ℬ X)
      = ∑ k, star (Y k i) * Y k j := by
    intro i j
    have : M i j = (star Y * Y) i j := by rw [← hMY]
    rw [CStarMatrix.mul_apply] at this
    simp only [CStarMatrix.star_apply] at this
    exact this
  have hsum_val : ∀ (s : Finset (Fin n)) (T : Fin n → Ba ℬ X) (y : X),
      ((∑ k ∈ s, T k : Ba ℬ X)).1 y = ∑ k ∈ s, (T k).1 y := by
    intro s T y
    classical
    induction s using Finset.induction_on with
    | empty => simp; rfl
    | insert b s hb ih =>
        rw [Finset.sum_insert hb, Finset.sum_insert hb, ← ih]; rfl
  set z : Fin n → Fin n → X := fun k i => (Y k i).1 (x i) with hz
  have key : ∀ i j, (inner ℬ (x i) ((φ (star (a i) * a j)).1 (x j)) : ℬ)
      = ∑ k, (inner ℬ (z k i) (z k j) : ℬ) := by
    intro i j
    rw [hentry i j, hsum_val, CStarModule.inner_sum_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    show (inner ℬ (x i) ((star (Y k i) * Y k j).1 (x j)) : ℬ) = _
    have hmul : ((star (Y k i) * Y k j : Ba ℬ X)).1 (x j)
        = (star (Y k i) : Ba ℬ X).1 ((Y k j).1 (x j)) := rfl
    rw [hmul]
    exact (baSubalgebra_star_spec (𝒷 := ℬ) (X := X) (Y k i) (x i) ((Y k j).1 (x j))).symm
  have hcol : ∀ k : Fin n, ∑ i, ∑ j, (inner ℬ (z k i) (z k j) : ℬ)
      = inner ℬ (∑ i, z k i) (∑ j, z k j) := by
    intro k
    rw [CStarModule.inner_sum_left]
    exact Finset.sum_congr rfl fun i _ => (CStarModule.inner_sum_right).symm
  calc (0 : ℬ) ≤ ∑ k, (inner ℬ (∑ i, z k i) (∑ j, z k j) : ℬ) :=
        Finset.sum_nonneg fun k _ => CStarModule.inner_self_nonneg
    _ = ∑ k, ∑ i, ∑ j, (inner ℬ (z k i) (z k j) : ℬ) :=
        Finset.sum_congr rfl fun k _ => (hcol k).symm
    _ = ∑ i, ∑ j, ∑ k, (inner ℬ (z k i) (z k j) : ℬ) :=
        (ks_sum_comm₃ fun i j k => (inner ℬ (z k i) (z k j) : ℬ)).symm
    _ = ∑ i, ∑ j, (inner ℬ (x i) ((φ (star (a i) * a j)).1 (x j)) : ℬ) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (key i j).symm

end KSGNSGram

/-! ## The norm completion of a semi-inner-product module -/

section ClmExtend

open UniformSpace

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A bounded linear map into a Banach space extends to the completion. -/
private noncomputable def clmExtend (f : E →L[ℂ] F) : Completion E →L[ℂ] F where
  toFun := Completion.extension f
  map_add' x y := by
    refine Completion.induction_on₂ (p := fun x y =>
      Completion.extension f (x + y) = Completion.extension f x + Completion.extension f y)
      x y (isClosed_eq (Completion.continuous_extension.comp continuous_add)
        ((Completion.continuous_extension.comp continuous_fst).add
          (Completion.continuous_extension.comp continuous_snd))) ?_
    intro a b
    rw [← Completion.coe_add, Completion.extension_coe f.uniformContinuous,
      Completion.extension_coe f.uniformContinuous,
      Completion.extension_coe f.uniformContinuous, map_add]
  map_smul' c x := by
    refine Completion.induction_on (p := fun x =>
      Completion.extension f (c • x) = c • Completion.extension f x)
      x (isClosed_eq (Completion.continuous_extension.comp (continuous_const_smul c))
        ((continuous_const_smul c).comp Completion.continuous_extension)) ?_
    intro a
    rw [← Completion.coe_smul, Completion.extension_coe f.uniformContinuous,
      Completion.extension_coe f.uniformContinuous, map_smul]
  cont := Completion.continuous_extension

@[simp] private theorem clmExtend_coe (f : E →L[ℂ] F) (x : E) :
    clmExtend f (x : Completion E) = f x :=
  Completion.extension_coe f.uniformContinuous x

private theorem clmExtend_norm_le (f : E →L[ℂ] F) {C : ℝ}
    (h : ∀ x : E, ‖f x‖ ≤ C * ‖x‖) (ξ : Completion E) : ‖clmExtend f ξ‖ ≤ C * ‖ξ‖ := by
  refine Completion.induction_on (p := fun ξ => ‖clmExtend f ξ‖ ≤ C * ‖ξ‖) ξ
    (isClosed_le ((clmExtend f).continuous.norm) (continuous_const.mul continuous_norm)) ?_
  intro a
  rw [clmExtend_coe, Completion.norm_coe]
  exact h a

end ClmExtend

section NormCompletion

open UniformSpace

universe v

variable {ℬ : Type u} {V : Type v}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [AddCommGroup V] [Module ℂ V] [SMul ℬ V]

/-- `V` carrying the seminorm `‖x‖ = ‖[x,x]‖^½` of a ℬ-valued inner product
`B` (**142V**). -/
private def NC (B : BInner ℬ V) : Type v := V

private instance (B : BInner ℬ V) : AddCommGroup (NC B) := inferInstanceAs (AddCommGroup V)
private instance (B : BInner ℬ V) : Module ℂ (NC B) := inferInstanceAs (Module ℂ V)
private instance (B : BInner ℬ V) : SMul ℬ (NC B) := inferInstanceAs (SMul ℬ V)

/-- The ℬ-action of a `BInner`-module is ℂ-linear.  For a *definite* inner
product this follows from the axioms; for a semidefinite one it does not, and
the norm completion needs it. -/
private class IsLinearAction (B : BInner ℬ V) : Prop where
  op_smul_add : ∀ (b : ℬ) (x y : V), b • (x + y) = b • x + b • y
  op_smul_comm : ∀ (b : ℬ) (c : ℂ) (x : V), b • (c • x) = c • (b • x)

private noncomputable instance (B : BInner ℬ V) : SeminormedAddCommGroup (NC B) :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := fun x => B.norm x
      map_zero' := by
        show Real.sqrt ‖B.inner 0 0‖ = 0
        rw [B.inner_zero_right, norm_zero, Real.sqrt_zero]
      add_le' := fun x y => (module_seminorm_2 B x y 0 0).1
      neg' := fun x => by
        show B.norm (-x) = B.norm x
        have h : B.norm ((-1 : ℂ) • (x : V)) = ‖(-1 : ℂ)‖ * B.norm (x : V) :=
          (module_seminorm_2 B x x (-1) 0).2.1
        rw [show (-(x : V)) = (-1 : ℂ) • (x : V) from (neg_one_smul ℂ (x : V)).symm, h]
        simp }

private instance ncUniformSMul (B : BInner ℬ V) : UniformContinuousConstSMul ℂ (NC B) where
  uniformContinuous_const_smul c := by
    have hl : LipschitzWith ‖c‖₊ (fun x : NC B => c • x) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      have hx : ‖c • (x - y)‖ = ‖c‖ * ‖x - y‖ :=
        (module_seminorm_2 B ((x : V) - y) ((x : V) - y) c 0).2.1
      rw [dist_eq_norm, dist_eq_norm, ← smul_sub, hx]
      simp
    exact hl.uniformContinuous

private noncomputable instance (B : BInner ℬ V) : NormedSpace ℂ (NC B) where
  norm_smul_le c x := le_of_eq (module_seminorm_2 B x x c 0).2.1

/-- `[v, ·]` as a bounded linear map on `NC B`. -/
private noncomputable def ncIpL (B : BInner ℬ V) (v : NC B) : NC B →L[ℂ] ℬ :=
  LinearMap.mkContinuous
    ({ toFun := fun y => B.inner v y
       map_add' := fun y z => B.inner_add_right v y z
       map_smul' := fun c y => B.inner_smul_right_complex c v y } : NC B →ₗ[ℂ] ℬ)
    (B.norm v) (fun y => module_seminorm_1 B v y)

private theorem ncIpL_apply (B : BInner ℬ V) (v w : NC B) : ncIpL B v w = B.inner v w := rfl

/-- `[w, ·]` extended to the completion. -/
private noncomputable def ncIpP (B : BInner ℬ V) (w : NC B) : Completion (NC B) →L[ℂ] ℬ :=
  clmExtend (ncIpL B w)

private theorem ncIpP_coe (B : BInner ℬ V) (w v : NC B) :
    ncIpP B w (v : Completion (NC B)) = B.inner w v := by
  rw [ncIpP, clmExtend_coe, ncIpL_apply]

private theorem ncIpP_norm_le (B : BInner ℬ V) (w : NC B) (ξ : Completion (NC B)) :
    ‖ncIpP B w ξ‖ ≤ B.norm w * ‖ξ‖ :=
  clmExtend_norm_le (ncIpL B w) (fun y : NC B => module_seminorm_1 B w y) ξ

private theorem ncIpP_add (B : BInner ℬ V) (w w' : NC B) (ξ : Completion (NC B)) :
    ncIpP B (w + w') ξ = ncIpP B w ξ + ncIpP B w' ξ := by
  refine Completion.induction_on (p := fun ξ =>
    ncIpP B (w + w') ξ = ncIpP B w ξ + ncIpP B w' ξ) ξ
    (isClosed_eq (ncIpP B (w + w')).continuous ((ncIpP B w).continuous.add
      (ncIpP B w').continuous)) ?_
  intro v
  rw [ncIpP_coe, ncIpP_coe, ncIpP_coe]
  exact B.inner_add_left w w' v

private theorem ncIpP_smul (B : BInner ℬ V) (c : ℂ) (w : NC B) (ξ : Completion (NC B)) :
    ncIpP B (c • w) ξ = (starRingEnd ℂ) c • ncIpP B w ξ := by
  refine Completion.induction_on (p := fun ξ =>
    ncIpP B (c • w) ξ = (starRingEnd ℂ) c • ncIpP B w ξ) ξ
    (isClosed_eq (ncIpP B (c • w)).continuous
      ((continuous_const_smul _).comp (ncIpP B w).continuous)) ?_
  intro v
  rw [ncIpP_coe, ncIpP_coe]
  exact B.inner_smul_left_complex c w v


/-- `⟨ξ, ·⟩` for `ξ` in the completion, as a bounded linear map on `NC B`. -/
private noncomputable def ncIpQ (B : BInner ℬ V) (ξ : Completion (NC B)) : NC B →L[ℂ] ℬ :=
  LinearMap.mkContinuous
    ({ toFun := fun w => star (ncIpP B w ξ)
       map_add' := fun w w' => by rw [ncIpP_add, star_add]
       map_smul' := fun c w => by
         rw [ncIpP_smul, star_smul]
         simp } : NC B →ₗ[ℂ] ℬ)
    ‖ξ‖ (fun w => by
      show ‖star (ncIpP B w ξ)‖ ≤ ‖ξ‖ * ‖w‖
      rw [norm_star]
      exact (ncIpP_norm_le B w ξ).trans (le_of_eq (mul_comm _ _)))

private theorem ncIpQ_apply (B : BInner ℬ V) (ξ : Completion (NC B)) (w : NC B) :
    ncIpQ B ξ w = star (ncIpP B w ξ) := rfl

/-- The ℬ-valued inner product of the norm completion. -/
private noncomputable def ncInner (B : BInner ℬ V) (ξ η : Completion (NC B)) : ℬ :=
  clmExtend (ncIpQ B ξ) η

private theorem continuous_ncInner_right (B : BInner ℬ V) (ξ : Completion (NC B)) :
    Continuous (ncInner B ξ) := (clmExtend (ncIpQ B ξ)).continuous

private theorem ncInner_coe_right (B : BInner ℬ V) (ξ : Completion (NC B)) (w : NC B) :
    ncInner B ξ (w : Completion (NC B)) = star (ncIpP B w ξ) := by
  rw [ncInner, clmExtend_coe, ncIpQ_apply]

private theorem ncInner_coe_coe (B : BInner ℬ V) (v w : NC B) :
    ncInner B (v : Completion (NC B)) (w : Completion (NC B)) = B.inner v w := by
  rw [ncInner_coe_right, ncIpP_coe]
  exact B.star_inner (w : V) (v : V)

private theorem ncInner_add_right (B : BInner ℬ V) (ξ η η' : Completion (NC B)) :
    ncInner B ξ (η + η') = ncInner B ξ η + ncInner B ξ η' :=
  map_add (clmExtend (ncIpQ B ξ)) η η'

private theorem ncInner_smul_right (B : BInner ℬ V) (c : ℂ) (ξ η : Completion (NC B)) :
    ncInner B ξ (c • η) = c • ncInner B ξ η :=
  map_smul (clmExtend (ncIpQ B ξ)) c η

private theorem ncInner_norm_le (B : BInner ℬ V) (ξ η : Completion (NC B)) :
    ‖ncInner B ξ η‖ ≤ ‖ξ‖ * ‖η‖ :=
  clmExtend_norm_le (ncIpQ B ξ) (fun w => (ncIpQ B ξ).le_opNorm w |>.trans
    (mul_le_mul_of_nonneg_right ((ncIpQ B ξ).opNorm_le_bound (norm_nonneg _)
      (fun w => by
        rw [ncIpQ_apply, norm_star]
        exact (ncIpP_norm_le B w ξ).trans (le_of_eq (mul_comm _ _)))) (norm_nonneg w))) η

private theorem ncInner_add_left (B : BInner ℬ V) (ξ ξ' η : Completion (NC B)) :
    ncInner B (ξ + ξ') η = ncInner B ξ η + ncInner B ξ' η := by
  refine Completion.induction_on (p := fun η =>
    ncInner B (ξ + ξ') η = ncInner B ξ η + ncInner B ξ' η) η
    (isClosed_eq (continuous_ncInner_right B (ξ + ξ'))
      ((continuous_ncInner_right B ξ).add (continuous_ncInner_right B ξ'))) ?_
  intro w
  rw [ncInner_coe_right, ncInner_coe_right, ncInner_coe_right, map_add, star_add]

private theorem ncInner_sub_left (B : BInner ℬ V) (ξ ξ' η : Completion (NC B)) :
    ncInner B (ξ - ξ') η = ncInner B ξ η - ncInner B ξ' η := by
  have h := ncInner_add_left B (ξ - ξ') ξ' η
  rw [sub_add_cancel] at h
  rw [h]
  abel

private theorem ncInner_sub_right (B : BInner ℬ V) (ξ η η' : Completion (NC B)) :
    ncInner B ξ (η - η') = ncInner B ξ η - ncInner B ξ η' :=
  map_sub (clmExtend (ncIpQ B ξ)) η η'

private theorem continuous_ncInner_left (B : BInner ℬ V) (η : Completion (NC B)) :
    Continuous (fun ξ => ncInner B ξ η) := by
  have hlip : LipschitzWith ‖η‖₊ (fun ξ : Completion (NC B) => ncInner B ξ η) := by
    refine LipschitzWith.of_dist_le_mul fun ξ ξ' => ?_
    rw [dist_eq_norm, dist_eq_norm, ← ncInner_sub_left]
    exact (ncInner_norm_le B (ξ - ξ') η).trans (le_of_eq (mul_comm _ _))
  exact hlip.continuous

private theorem ncInner_star (B : BInner ℬ V) (ξ η : Completion (NC B)) :
    star (ncInner B ξ η) = ncInner B η ξ := by
  refine Completion.induction_on (p := fun η => star (ncInner B ξ η) = ncInner B η ξ) η
    (isClosed_eq ((continuous_ncInner_right B ξ).star) (continuous_ncInner_left B ξ)) ?_
  intro w
  rw [ncInner_coe_right, star_star]
  refine Completion.induction_on (p := fun ξ => ncIpP B w ξ = ncInner B (w : Completion (NC B)) ξ) ξ
    (isClosed_eq (ncIpP B w).continuous (continuous_ncInner_right B _)) ?_
  intro v
  rw [ncIpP_coe, ncInner_coe_coe]

private theorem continuous_ncInner_self (B : BInner ℬ V) :
    Continuous (fun ξ : Completion (NC B) => ncInner B ξ ξ) := by
  refine Metric.continuous_iff.mpr fun ξ₀ ε hε => ?_
  refine ⟨min 1 (ε / (2 * ‖ξ₀‖ + 2)), lt_min one_pos (by positivity), fun ξ hξ => ?_⟩
  rw [dist_eq_norm] at hξ
  have hle1 : ‖ξ - ξ₀‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hξ (min_le_left _ _))
  have h2 : ‖ξ - ξ₀‖ < ε / (2 * ‖ξ₀‖ + 2) := lt_of_lt_of_le hξ (min_le_right _ _)
  have hdec : ncInner B ξ ξ - ncInner B ξ₀ ξ₀
      = ncInner B (ξ - ξ₀) ξ + ncInner B ξ₀ (ξ - ξ₀) := by
    rw [ncInner_sub_left, ncInner_sub_right]
    abel
  have hb1 : ‖ncInner B (ξ - ξ₀) ξ‖ ≤ ‖ξ - ξ₀‖ * ‖ξ‖ := ncInner_norm_le B _ _
  have hb2 : ‖ncInner B ξ₀ (ξ - ξ₀)‖ ≤ ‖ξ₀‖ * ‖ξ - ξ₀‖ := ncInner_norm_le B _ _
  have hxi : ‖ξ‖ ≤ ‖ξ₀‖ + ‖ξ - ξ₀‖ := by
    have h := norm_add_le (ξ - ξ₀) ξ₀
    rw [sub_add_cancel] at h
    linarith [h]
  have hkey : ‖ncInner B ξ ξ - ncInner B ξ₀ ξ₀‖ ≤ ‖ξ - ξ₀‖ * (2 * ‖ξ₀‖ + 1) := by
    rw [hdec]
    have h := norm_add_le (ncInner B (ξ - ξ₀) ξ) (ncInner B ξ₀ (ξ - ξ₀))
    nlinarith [norm_nonneg (ξ - ξ₀), norm_nonneg ξ₀, norm_nonneg ξ]
  have hdenom : (0 : ℝ) < 2 * ‖ξ₀‖ + 2 := by positivity
  have hlt : ‖ξ - ξ₀‖ * (2 * ‖ξ₀‖ + 1) < ε := by
    have h3 : ‖ξ - ξ₀‖ * (2 * ‖ξ₀‖ + 2) < ε := by
      rw [← lt_div_iff₀ hdenom]
      exact h2
    nlinarith [norm_nonneg (ξ - ξ₀)]
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hkey hlt

private theorem ncInner_self_nonneg (B : BInner ℬ V) (ξ : Completion (NC B)) :
    0 ≤ ncInner B ξ ξ := by
  refine Completion.induction_on (p := fun ξ => 0 ≤ ncInner B ξ ξ) ξ
    (isClosed_le continuous_const (continuous_ncInner_self B)) ?_
  intro v
  rw [ncInner_coe_coe]
  exact B.inner_self_nonneg v

private theorem ncInner_norm_self (B : BInner ℬ V) (ξ : Completion (NC B)) :
    ‖ξ‖ = Real.sqrt ‖ncInner B ξ ξ‖ := by
  refine Completion.induction_on (p := fun ξ => ‖ξ‖ = Real.sqrt ‖ncInner B ξ ξ‖) ξ
    (isClosed_eq continuous_norm
      (Real.continuous_sqrt.comp (continuous_ncInner_self B).norm)) ?_
  intro v
  rw [Completion.norm_coe, ncInner_coe_coe]
  rfl


/-! ### The ℬ-action and the `CStarModule` structure on the completion -/

section Action

/-- `b • ·` as a bounded linear map on `NC B`. -/
private noncomputable def ncSmulCLM (B : BInner ℬ V) [IsLinearAction B] (b : ℬ) :
    NC B →L[ℂ] NC B :=
  LinearMap.mkContinuous
    ({ toFun := fun x => b • x
       map_add' := fun x y => IsLinearAction.op_smul_add (B := B) b x y
       map_smul' := fun c x => IsLinearAction.op_smul_comm (B := B) b c x } : NC B →ₗ[ℂ] NC B)
    ‖b‖ (fun x => by
      show B.norm (b • (x : V)) ≤ ‖b‖ * B.norm (x : V)
      exact (module_seminorm_2 B x x 0 b).2.2.trans (le_of_eq (mul_comm _ _)))

private theorem ncSmulCLM_apply (B : BInner ℬ V) [IsLinearAction B] (b : ℬ) (x : NC B) :
    ncSmulCLM B b x = b • x := rfl

private noncomputable instance ncSMul (B : BInner ℬ V) [IsLinearAction B] :
    SMul ℬ (Completion (NC B)) where
  smul b ξ := clmExtend
    ((Completion.toComplL : NC B →L[ℂ] Completion (NC B)).comp (ncSmulCLM B b)) ξ

private theorem ncSMul_def (B : BInner ℬ V) [IsLinearAction B] (b : ℬ) (ξ : Completion (NC B)) :
    b • ξ = clmExtend
      ((Completion.toComplL : NC B →L[ℂ] Completion (NC B)).comp (ncSmulCLM B b)) ξ := rfl

private theorem continuous_ncSMul (B : BInner ℬ V) [IsLinearAction B] (b : ℬ) :
    Continuous (fun ξ : Completion (NC B) => b • ξ) :=
  (clmExtend ((Completion.toComplL : NC B →L[ℂ] Completion (NC B)).comp (ncSmulCLM B b))).continuous

private theorem ncSMul_coe (B : BInner ℬ V) [IsLinearAction B] (b : ℬ) (x : NC B) :
    b • (x : Completion (NC B)) = ((b • x : NC B) : Completion (NC B)) := by
  rw [ncSMul_def, clmExtend_coe]
  rfl

private theorem ncIpP_op_smul (B : BInner ℬ V) (b : ℬ) (w : NC B) (ξ : Completion (NC B)) :
    ncIpP B (b • w) ξ = ncIpP B w ξ * star b := by
  refine Completion.induction_on (p := fun ξ => ncIpP B (b • w) ξ = ncIpP B w ξ * star b) ξ
    (isClosed_eq (ncIpP B (b • w)).continuous
      ((ncIpP B w).continuous.mul continuous_const)) ?_
  intro v
  rw [ncIpP_coe, ncIpP_coe]
  exact B.inner_op_smul_left b w v

private theorem ncInner_op_smul_right (B : BInner ℬ V) [IsLinearAction B] (b : ℬ)
    (ξ η : Completion (NC B)) :
    ncInner B ξ (b • η) = b * ncInner B ξ η := by
  refine Completion.induction_on (p := fun η => ncInner B ξ (b • η) = b * ncInner B ξ η) η
    (isClosed_eq ((continuous_ncInner_right B ξ).comp (continuous_ncSMul B b))
      (continuous_const.mul (continuous_ncInner_right B ξ))) ?_
  intro w
  rw [ncSMul_coe, ncInner_coe_right, ncInner_coe_right, ncIpP_op_smul, star_mul, star_star]

/-- The norm completion of a semi-inner-product ℬ-module is a Hilbert
ℬ-module. -/
private noncomputable instance ncCStarModule (B : BInner ℬ V) [IsLinearAction B] :
    CStarModule ℬ (Completion (NC B)) where
  inner := ncInner B
  inner_add_right := ncInner_add_right B _ _ _
  inner_self_nonneg := ncInner_self_nonneg B _
  inner_self := by
    intro ξ
    refine ⟨fun h => ?_, fun h => by rw [h]; simpa using ncInner_add_right B 0 0 0⟩
    have : ‖ξ‖ = 0 := by rw [ncInner_norm_self B ξ, h, norm_zero, Real.sqrt_zero]
    exact norm_eq_zero.mp this
  inner_op_smul_right := ncInner_op_smul_right B _ _ _
  inner_smul_right_complex := ncInner_smul_right B _ _ _
  star_inner ξ η := ncInner_star B ξ η
  norm_eq_sqrt_norm_inner_self := ncInner_norm_self B

private theorem nc_inner_apply (B : BInner ℬ V) [IsLinearAction B] (ξ η : Completion (NC B)) :
    (inner ℬ ξ η : ℬ) = ncInner B ξ η := rfl

private theorem nc_inner_coe_coe (B : BInner ℬ V) [IsLinearAction B] (v w : NC B) :
    (inner ℬ (v : Completion (NC B)) (w : Completion (NC B)) : ℬ) = B.inner v w :=
  ncInner_coe_coe B v w

end Action

end NormCompletion

/-! ## 155II: the KSGNS construction -/

section KSGNS

open UniformSpace

variable {𝒜 ℬ : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  {X : Type u} [NormedAddCommGroup X] [Module ℂ X] [SMul ℬ X]
  [CStarModule ℬ X] [CompleteSpace X]

/-- The ℬ-action on a Hilbert ℬ-module is additive (by definiteness). -/
private theorem cstar_smul_add (b : ℬ) (x y : X) : b • (x + y) = b • x + b • y := by
  refine eq_of_inner_right_eq (𝒜 := ℬ) fun z => ?_
  simp [mul_add]

/-- The ℬ-action on a Hilbert ℬ-module commutes with the ℂ-action. -/
private theorem cstar_smul_comm (b : ℬ) (c : ℂ) (x : X) : b • (c • x) = c • (b • x) := by
  refine eq_of_inner_right_eq (𝒜 := ℬ) fun z => ?_
  simp [mul_smul_comm]

/-- `b • ·` on `X` as a ℂ-linear map. -/
private noncomputable def ksSmulLM (b : ℬ) : X →ₗ[ℂ] X where
  toFun x := b • x
  map_add' := cstar_smul_add b
  map_smul' c x := cstar_smul_comm b c x

/-- Application of a sum and of a scalar multiple in `𝒷ᵃ(X)`. -/
private theorem ba_add_apply (S T : Ba ℬ X) (x : X) : (S + T).1 x = S.1 x + T.1 x := rfl

private theorem ba_smul_apply (c : ℂ) (T : Ba ℬ X) (x : X) : (c • T).1 x = c • T.1 x := rfl

private theorem ba_sub_apply (S T : Ba ℬ X) (x : X) : (S - T).1 x = S.1 x - T.1 x := rfl

private theorem ba_smul_apply' (c : ℂ) (T : Ba ℬ X) (x : X) : (c • T).1 x = c • T.1 x := rfl

/-- The ℬ-action on `X ⊙ 𝒜`: `b • (x ⊗ a) = (b • x) ⊗ a`. -/
private noncomputable local instance ksSMul : SMul ℬ (X ⊗[ℂ] 𝒜) where
  smul b := LinearMap.rTensor 𝒜 (ksSmulLM (X := X) b)

private theorem ksSMul_tmul (b : ℬ) (x : X) (a : 𝒜) :
    b • (x ⊗ₜ[ℂ] a) = (b • x) ⊗ₜ[ℂ] a := rfl

private theorem ksSMul_zero (b : ℬ) : b • (0 : X ⊗[ℂ] 𝒜) = 0 :=
  map_zero (LinearMap.rTensor 𝒜 (ksSmulLM (X := X) b))

private theorem ksSMul_add (b : ℬ) (u v : X ⊗[ℂ] 𝒜) : b • (u + v) = b • u + b • v :=
  map_add (LinearMap.rTensor 𝒜 (ksSmulLM (X := X) b)) u v

private theorem ksSMul_smul (b : ℬ) (c : ℂ) (u : X ⊗[ℂ] 𝒜) : b • (c • u) = c • (b • u) :=
  map_smul (LinearMap.rTensor 𝒜 (ksSmulLM (X := X) b)) c u

/-- Every element of `X ⊗[ℂ] 𝒜` is a finite sum of elementary tensors. -/
private theorem exists_fin_tmul' (u : X ⊗[ℂ] 𝒜) :
    ∃ (n : ℕ) (x : Fin n → X) (a : Fin n → 𝒜), u = ∑ i, x i ⊗ₜ[ℂ] a i := by
  classical
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset u
  refine ⟨S.card, fun i => ((S.equivFin.symm i : X × 𝒜)).1,
    fun i => ((S.equivFin.symm i : X × 𝒜)).2, ?_⟩
  rw [← Finset.sum_coe_sort S (fun p : X × 𝒜 => p.1 ⊗ₜ[ℂ] p.2)]
  exact (Fintype.sum_equiv S.equivFin.symm _ _ (fun i => rfl)).symm

/-- The right slot of the φ-pairing: `⟨x ⊗ a, ·⟩`. -/
private noncomputable def ksR (φ : 𝒜 →ₗ[ℂ] Ba ℬ X) (x : X) (a : 𝒜) :
    (X ⊗[ℂ] 𝒜) →ₗ[ℂ] ℬ :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ
    (fun (x' : X) (a' : 𝒜) => (inner ℬ x ((φ (star a * a')).1 x') : ℬ))
    (fun x₁ x₂ a' => by rw [map_add, CStarModule.inner_add_right])
    (fun c x' a' => by rw [map_smul, CStarModule.inner_smul_right_complex])
    (fun x' a₁ a₂ => by rw [mul_add, map_add, ba_add_apply, CStarModule.inner_add_right])
    (fun c x' a' => by
      rw [mul_smul_comm, map_smul, ba_smul_apply, CStarModule.inner_smul_right_complex])

@[simp] private theorem ksR_tmul (φ : 𝒜 →ₗ[ℂ] Ba ℬ X) (x x' : X) (a a' : 𝒜) :
    ksR φ x a (x' ⊗ₜ[ℂ] a') = (inner ℬ x ((φ (star a * a')).1 x') : ℬ) := rfl

/-- The φ-pairing on `X ⊙ 𝒜`, additive in the first slot (it is
conjugate-linear, so it is not a `TensorProduct.lift`; the two slots are
conjugated together, so the pairing is ℂ-*balanced* and
`TensorProduct.liftAddHom` applies). -/
private noncomputable def ksPair (φ : 𝒜 →ₗ[ℂ] Ba ℬ X) :
    (X ⊗[ℂ] 𝒜) →+ ((X ⊗[ℂ] 𝒜) →ₗ[ℂ] ℬ) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun x : X => AddMonoidHom.mk' (fun a : 𝒜 => ksR φ x a) (fun a₁ a₂ => by
        refine TensorProduct.ext' fun x' a' => ?_
        rw [ksR_tmul, LinearMap.add_apply, ksR_tmul, ksR_tmul, star_add, add_mul, map_add,
          ba_add_apply, CStarModule.inner_add_right]))
      (fun x₁ x₂ => by
        refine AddMonoidHom.ext fun a => ?_
        refine TensorProduct.ext' fun x' a' => ?_
        rw [AddMonoidHom.add_apply]
        show ksR φ (x₁ + x₂) a (x' ⊗ₜ[ℂ] a') = ksR φ x₁ a (x' ⊗ₜ[ℂ] a') + ksR φ x₂ a _
        rw [ksR_tmul, ksR_tmul, ksR_tmul, CStarModule.inner_add_left]))
    (fun c x a => by
      refine TensorProduct.ext' fun x' a' => ?_
      show ksR φ (c • x) a (x' ⊗ₜ[ℂ] a') = ksR φ x (c • a) (x' ⊗ₜ[ℂ] a')
      rw [ksR_tmul, ksR_tmul, CStarModule.inner_smul_left_complex, star_smul,
        Complex.star_def, smul_mul_assoc, map_smul, ba_smul_apply,
        CStarModule.inner_smul_right_complex])

/-- `star` in `𝒷ᵃ(X)` is the module adjoint. -/
private theorem ba_star_inner (T : Ba ℬ X) (x y : X) :
    (inner ℬ (T.1 x) y : ℬ) = inner ℬ x ((star T : Ba ℬ X).1 y) := by
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore ℬ)
  exact baSubalgebra_star_spec (𝒷 := ℬ) (X := X) T x y

@[simp] private theorem ksPair_tmul (φ : 𝒜 →ₗ[ℂ] Ba ℬ X) (x x' : X) (a a' : 𝒜) :
    ksPair φ (x ⊗ₜ[ℂ] a) (x' ⊗ₜ[ℂ] a') = (inner ℬ x ((φ (star a * a')).1 x') : ℬ) := rfl

/-- The φ-inner product on `X ⊙ 𝒜` (**155II**, the KSGNS form):
`⟨x ⊗ a, x' ⊗ a'⟩ = ⟪x, φ(a* a') x'⟫`. -/
private noncomputable def ksBInner (φ : 𝒜 →ₗ[ℂ] Ba ℬ X) (hφ : IsCompletelyPositiveMap φ) :
    BInner ℬ (X ⊗[ℂ] 𝒜) where
  inner u v := ksPair φ u v
  inner_add_right u v w := map_add (ksPair φ u) v w
  inner_smul_right_complex c u v := map_smul (ksPair φ u) c v
  inner_op_smul_right b u v := by
    induction v using TensorProduct.induction_on with
    | zero => rw [ksSMul_zero, map_zero, mul_zero]
    | tmul x' a' =>
        induction u using TensorProduct.induction_on with
        | zero => simp
        | tmul x a =>
            rw [ksSMul_tmul, ksPair_tmul, ksPair_tmul,
              ((moduleAdjointable_linear (𝒜 := ℬ) _ (φ (star a * a')).2).2.2 b x'),
              CStarModule.inner_op_smul_right]
        | add u₁ u₂ h₁ h₂ =>
            rw [map_add, LinearMap.add_apply, LinearMap.add_apply, h₁, h₂, mul_add]
    | add v₁ v₂ h₁ h₂ => rw [ksSMul_add, map_add, map_add, h₁, h₂, mul_add]
  star_inner u v := by
    have hi : IsInvolutionPreserving φ :=
      cstar_p_implies_i φ (astara_pos_basic_2_cp φ hφ)
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul x a =>
        induction v using TensorProduct.induction_on with
        | zero => simp
        | tmul x' a' =>
            have hst : (star (φ (star a * a')) : Ba ℬ X) = φ (star a' * a) := by
              rw [← hi, star_mul, star_star]
            rw [ksPair_tmul, ksPair_tmul, CStarModule.star_inner, ba_star_inner, hst]
        | add v₁ v₂ h₁ h₂ =>
            rw [map_add, map_add, LinearMap.add_apply, star_add, h₁, h₂]
    | add u₁ u₂ h₁ h₂ =>
        rw [map_add, LinearMap.add_apply, star_add, h₁, h₂, map_add]
  inner_self_nonneg u := by
    obtain ⟨n, x, a, rfl⟩ := exists_fin_tmul' u
    have hexp : ksPair φ (∑ i, x i ⊗ₜ[ℂ] a i) (∑ i, x i ⊗ₜ[ℂ] a i)
        = ∑ i, ∑ j, (inner ℬ (x i) ((φ (star (a i) * a j)).1 (x j)) : ℬ) := by
      have h1 : ksPair φ (∑ i, x i ⊗ₜ[ℂ] a i) = ∑ i, ksPair φ (x i ⊗ₜ[ℂ] a i) :=
        map_sum (ksPair φ) _ _
      rw [h1, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum]
      rfl
    show (0 : ℬ) ≤ ksPair φ _ _
    rw [hexp]
    exact ksgns_gram_nonneg φ hφ a x

private instance ksIsLinearAction (φ : 𝒜 →ₗ[ℂ] Ba ℬ X) (hφ : IsCompletelyPositiveMap φ) :
    IsLinearAction (ksBInner φ hφ) where
  op_smul_add := ksSMul_add
  op_smul_comm := ksSMul_smul

/-- The Gram sum of a finite family, for the φ-inner product. -/
private theorem ksBInner_gram (φ : 𝒜 →ₗ[ℂ] Ba ℬ X) (hφ : IsCompletelyPositiveMap φ)
    {n : ℕ} (x : Fin n → X) (a : Fin n → 𝒜) :
    (ksBInner φ hφ).inner (∑ i, x i ⊗ₜ[ℂ] a i) (∑ i, x i ⊗ₜ[ℂ] a i)
      = ∑ i, ∑ j, (inner ℬ (x i) ((φ (star (a i) * a j)).1 (x j)) : ℬ) := by
  show ksPair φ (∑ i, x i ⊗ₜ[ℂ] a i) (∑ i, x i ⊗ₜ[ℂ] a i) = _
  have h1 : ksPair φ (∑ i, x i ⊗ₜ[ℂ] a i) = ∑ i, ksPair φ (x i ⊗ₜ[ℂ] a i) :=
    map_sum (ksPair φ) _ _
  rw [h1, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  rfl

/-- The norm of an element of `𝒷ᵃ(X)` dominates its action. -/
private theorem ba_apply_norm_le (T : Ba ℬ X) (x : X) : ‖T.1 x‖ ≤ ‖T‖ * ‖x‖ := by
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore ℬ)
  have h : ‖T‖ = ‖T.1‖ := rfl
  rw [h]
  exact T.1.le_opNorm x

/-- `a₀ ⬝` on `X ⊙ 𝒜`. -/
private noncomputable def ksRhoLM (a₀ : 𝒜) : (X ⊗[ℂ] 𝒜) →ₗ[ℂ] (X ⊗[ℂ] 𝒜) :=
  LinearMap.lTensor X (LinearMap.mulLeft ℂ a₀)

private theorem ksRhoLM_tmul (a₀ : 𝒜) (x : X) (a : 𝒜) :
    ksRhoLM (X := X) a₀ (x ⊗ₜ[ℂ] a) = x ⊗ₜ[ℂ] (a₀ * a) := rfl

/-- `⟨a₀ u, v⟩ = ⟨u, a₀* v⟩` for the φ-inner product. -/
private theorem ksBInner_rho_adj (φ : 𝒜 →ₗ[ℂ] Ba ℬ X) (hφ : IsCompletelyPositiveMap φ)
    (a₀ : 𝒜) (u v : X ⊗[ℂ] 𝒜) :
    (ksBInner φ hφ).inner (ksRhoLM a₀ u) v
      = (ksBInner φ hφ).inner u (ksRhoLM (star a₀) v) := by
  induction u using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, (ksBInner φ hφ).inner_zero_left, (ksBInner φ hφ).inner_zero_left]
  | tmul x a =>
      induction v using TensorProduct.induction_on with
      | zero =>
          rw [map_zero, (ksBInner φ hφ).inner_zero_right, (ksBInner φ hφ).inner_zero_right]
      | tmul x' a' =>
          show ksPair φ (x ⊗ₜ[ℂ] (a₀ * a)) (x' ⊗ₜ[ℂ] a')
            = ksPair φ (x ⊗ₜ[ℂ] a) (x' ⊗ₜ[ℂ] (star a₀ * a'))
          rw [ksPair_tmul, ksPair_tmul, star_mul, mul_assoc]
      | add v₁ v₂ h₁ h₂ =>
          rw [map_add, (ksBInner φ hφ).inner_add_right, (ksBInner φ hφ).inner_add_right,
            h₁, h₂]
  | add u₁ u₂ h₁ h₂ =>
      rw [map_add, (ksBInner φ hφ).inner_add_left, (ksBInner φ hφ).inner_add_left, h₁, h₂]

/-- `‖a₀ u‖ ≤ ‖a₀‖ ‖u‖` for the φ-seminorm: the key estimate behind `ϱ`. -/
private theorem ksRho_bound (φ : 𝒜 →ₗ[ℂ] Ba ℬ X) (hφ : IsCompletelyPositiveMap φ)
    (a₀ : 𝒜) (u : X ⊗[ℂ] 𝒜) :
    (ksBInner φ hφ).norm (ksRhoLM a₀ u) ≤ ‖a₀‖ * (ksBInner φ hφ).norm u := by
  obtain ⟨n, x, a, rfl⟩ := exists_fin_tmul' u
  -- `‖a₀‖² - a₀* a₀ = c* c`
  have hsa : IsSelfAdjoint (star a₀ * a₀) := IsSelfAdjoint.star_mul_self a₀
  have hle : star a₀ * a₀ ≤ ‖star a₀ * a₀‖ • (1 : 𝒜) := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self (a := star a₀ * a₀) hsa
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hnorm2 : ‖star a₀ * a₀‖ = ‖a₀‖ ^ 2 := by
    rw [CStarRing.norm_star_mul_self]; ring
  obtain ⟨c, hc⟩ : ∃ c : 𝒜, (‖a₀‖ ^ 2 : ℝ) • (1 : 𝒜) - star a₀ * a₀ = star c * c :=
    ks_exists_star_mul_self (by rw [← hnorm2]; exact sub_nonneg.mpr hle)
  -- the termwise identity
  have hterm : ∀ i j, ((‖a₀‖ ^ 2 : ℝ) : ℂ) • (inner ℬ (x i) ((φ (star (a i) * a j)).1 (x j)) : ℬ)
      - (inner ℬ (x i) ((φ (star (a₀ * a i) * (a₀ * a j))).1 (x j)) : ℬ)
      = (inner ℬ (x i) ((φ (star (c * a i) * (c * a j))).1 (x j)) : ℬ) := by
    intro i j
    have harg : star (c * a i) * (c * a j)
        = ((‖a₀‖ ^ 2 : ℝ) : ℂ) • (star (a i) * a j) - star (a₀ * a i) * (a₀ * a j) := by
      rw [star_mul, star_mul]
      have : star (a i) * (star c * c) * a j
          = ((‖a₀‖ ^ 2 : ℝ) : ℂ) • (star (a i) * a j) - star (a i) * (star a₀ * a₀) * a j := by
        rw [← hc, RCLike.real_smul_eq_coe_smul (K := ℂ)]
        simp [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm]
      calc star (a i) * star c * (c * a j) = star (a i) * (star c * c) * a j := by
            noncomm_ring
        _ = _ := by rw [this]; noncomm_ring
    rw [harg, map_sub, map_smul, ba_sub_apply, CStarModule.inner_sub_right,
      ba_smul_apply, CStarModule.inner_smul_right_complex]
  -- sum up
  have hsum : ((‖a₀‖ ^ 2 : ℝ) : ℂ) • (∑ i, ∑ j, (inner ℬ (x i) ((φ (star (a i) * a j)).1 (x j)) : ℬ))
      - (∑ i, ∑ j, (inner ℬ (x i) ((φ (star (a₀ * a i) * (a₀ * a j))).1 (x j)) : ℬ))
      = ∑ i, ∑ j, (inner ℬ (x i) ((φ (star (c * a i) * (c * a j))).1 (x j)) : ℬ) := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => hterm i j
  have hgram_le : (ksBInner φ hφ).inner (ksRhoLM a₀ (∑ i, x i ⊗ₜ[ℂ] a i))
      (ksRhoLM a₀ (∑ i, x i ⊗ₜ[ℂ] a i))
      ≤ ((‖a₀‖ ^ 2 : ℝ) : ℂ) • (ksBInner φ hφ).inner (∑ i, x i ⊗ₜ[ℂ] a i)
          (∑ i, x i ⊗ₜ[ℂ] a i) := by
    have hrho : ksRhoLM a₀ (∑ i, x i ⊗ₜ[ℂ] a i) = ∑ i, x i ⊗ₜ[ℂ] (a₀ * a i) := by
      rw [map_sum]
      rfl
    rw [hrho, ksBInner_gram, ksBInner_gram]
    have h0 := ksgns_gram_nonneg φ hφ (fun i => c * a i) x
    rw [← hsum] at h0
    exact sub_nonneg.mp h0
  -- pass to norms
  have hnn : (0 : ℬ) ≤ (ksBInner φ hφ).inner (ksRhoLM a₀ (∑ i, x i ⊗ₜ[ℂ] a i))
      (ksRhoLM a₀ (∑ i, x i ⊗ₜ[ℂ] a i)) := (ksBInner φ hφ).inner_self_nonneg _
  have hn := CStarAlgebra.norm_le_norm_of_nonneg_of_le hnn hgram_le
  rw [norm_smul] at hn
  have hcnorm : ‖((‖a₀‖ ^ 2 : ℝ) : ℂ)‖ = ‖a₀‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hcnorm] at hn
  have h2 := Real.sqrt_le_sqrt hn
  calc (ksBInner φ hφ).norm (ksRhoLM a₀ (∑ i, x i ⊗ₜ[ℂ] a i))
      = Real.sqrt ‖(ksBInner φ hφ).inner (ksRhoLM a₀ (∑ i, x i ⊗ₜ[ℂ] a i))
          (ksRhoLM a₀ (∑ i, x i ⊗ₜ[ℂ] a i))‖ := rfl
    _ ≤ Real.sqrt (‖a₀‖ ^ 2 * ‖(ksBInner φ hφ).inner (∑ i, x i ⊗ₜ[ℂ] a i)
          (∑ i, x i ⊗ₜ[ℂ] a i)‖) := h2
    _ = ‖a₀‖ * (ksBInner φ hφ).norm (∑ i, x i ⊗ₜ[ℂ] a i) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
        rfl

private theorem ksRhoLM_one (u : X ⊗[ℂ] 𝒜) : ksRhoLM (1 : 𝒜) u = u := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | tmul x a => rw [ksRhoLM_tmul, one_mul]
  | add u₁ u₂ h₁ h₂ => rw [map_add, h₁, h₂]

private theorem ksRhoLM_mul (a a' : 𝒜) (u : X ⊗[ℂ] 𝒜) :
    ksRhoLM (a * a') u = ksRhoLM a (ksRhoLM a' u) := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul x a₁ => rw [ksRhoLM_tmul, ksRhoLM_tmul, ksRhoLM_tmul, mul_assoc]
  | add u₁ u₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]

private theorem ksRhoLM_add (a a' : 𝒜) (u : X ⊗[ℂ] 𝒜) :
    ksRhoLM (a + a') u = ksRhoLM a u + ksRhoLM a' u := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | tmul x a₁ => rw [ksRhoLM_tmul, ksRhoLM_tmul, ksRhoLM_tmul, add_mul, TensorProduct.tmul_add]
  | add u₁ u₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, h₁, h₂]
      abel

private theorem ksRhoLM_smul (c : ℂ) (a : 𝒜) (u : X ⊗[ℂ] 𝒜) :
    ksRhoLM (c • a) u = c • ksRhoLM a u := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul x a₁ =>
      rw [ksRhoLM_tmul, ksRhoLM_tmul, smul_mul_assoc, TensorProduct.tmul_smul]
  | add u₁ u₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, smul_add]

private theorem ksRhoLM_zero (u : X ⊗[ℂ] 𝒜) : ksRhoLM (0 : 𝒜) u = 0 := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | tmul x a => rw [ksRhoLM_tmul, zero_mul, TensorProduct.tmul_zero]
  | add u₁ u₂ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]

/-- Two bounded maps out of a completion agreeing on the image agree. -/
private theorem clm_ext_of_coe {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f g : Completion E →L[ℂ] F} (h : ∀ v : E, f (v : Completion E) = g v) : f = g := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  exact Completion.induction_on (p := fun ξ => f ξ = g ξ) ξ
    (isClosed_eq f.continuous g.continuous) h

section Assembly

variable (φ : 𝒜 →ₗ[ℂ] Ba ℬ X) (hφ : IsCompletelyPositiveMap φ)

/-- The carrier of the KSGNS dilation: the norm completion of `X ⊙ 𝒜`. -/
private noncomputable abbrev ksY : Type u := Completion (NC (ksBInner φ hφ))

private noncomputable def ksRhoCLM (a₀ : 𝒜) :
    NC (ksBInner φ hφ) →L[ℂ] NC (ksBInner φ hφ) :=
  LinearMap.mkContinuous
    (ksRhoLM a₀ : NC (ksBInner φ hφ) →ₗ[ℂ] NC (ksBInner φ hφ)) ‖a₀‖
    (fun u => ksRho_bound φ hφ a₀ u)

private noncomputable def ksRhoY (a₀ : 𝒜) : ksY φ hφ →L[ℂ] ksY φ hφ :=
  clmExtend ((Completion.toComplL : NC (ksBInner φ hφ) →L[ℂ] ksY φ hφ).comp
    (ksRhoCLM φ hφ a₀))

/-- The canonical map `X ⊙ 𝒜 → Y`. -/
private noncomputable def ksEta (u : NC (ksBInner φ hφ)) : ksY φ hφ :=
  (u : Completion (NC (ksBInner φ hφ)))

private theorem ksEta_inner (u v : NC (ksBInner φ hφ)) :
    (inner ℬ (ksEta φ hφ u) (ksEta φ hφ v) : ℬ) = (ksBInner φ hφ).inner u v :=
  nc_inner_coe_coe (ksBInner φ hφ) u v

private theorem ksEta_add (u v : NC (ksBInner φ hφ)) :
    ksEta φ hφ (u + v) = ksEta φ hφ u + ksEta φ hφ v :=
  Completion.coe_add _ _

private theorem ksEta_smul (c : ℂ) (u : NC (ksBInner φ hφ)) :
    ksEta φ hφ (c • u) = c • ksEta φ hφ u :=
  Completion.coe_smul c _

private theorem ksRhoCLM_one (u : NC (ksBInner φ hφ)) : ksRhoCLM φ hφ 1 u = u :=
  ksRhoLM_one u

private theorem ksRhoCLM_zero (u : NC (ksBInner φ hφ)) : ksRhoCLM φ hφ 0 u = 0 :=
  ksRhoLM_zero u

private theorem ksRhoCLM_mul (a a' : 𝒜) (u : NC (ksBInner φ hφ)) :
    ksRhoCLM φ hφ (a * a') u = ksRhoCLM φ hφ a (ksRhoCLM φ hφ a' u) :=
  ksRhoLM_mul a a' u

private theorem ksRhoCLM_add (a a' : 𝒜) (u : NC (ksBInner φ hφ)) :
    ksRhoCLM φ hφ (a + a') u = ksRhoCLM φ hφ a u + ksRhoCLM φ hφ a' u :=
  ksRhoLM_add a a' u

private theorem ksRhoCLM_smul (c : ℂ) (a : 𝒜) (u : NC (ksBInner φ hφ)) :
    ksRhoCLM φ hφ (c • a) u = c • ksRhoCLM φ hφ a u :=
  ksRhoLM_smul c a u

private theorem ksRhoCLM_adj (a₀ : 𝒜) (u v : NC (ksBInner φ hφ)) :
    (ksBInner φ hφ).inner (ksRhoCLM φ hφ a₀ u) v
      = (ksBInner φ hφ).inner u (ksRhoCLM φ hφ (star a₀) v) :=
  ksBInner_rho_adj φ hφ a₀ u v

private theorem ksRhoY_coe (a₀ : 𝒜) (u : NC (ksBInner φ hφ)) :
    ksRhoY φ hφ a₀ (ksEta φ hφ u) = ksEta φ hφ (ksRhoCLM φ hφ a₀ u) := by
  show clmExtend ((Completion.toComplL : NC (ksBInner φ hφ) →L[ℂ] ksY φ hφ).comp
      (ksRhoCLM φ hφ a₀)) (u : Completion (NC (ksBInner φ hφ))) = _
  rw [clmExtend_coe]
  rfl

private theorem ksRhoY_adj (a₀ : 𝒜) (ξ η : ksY φ hφ) :
    (inner ℬ (ksRhoY φ hφ a₀ ξ) η : ℬ) = inner ℬ ξ (ksRhoY φ hφ (star a₀) η) := by
  refine Completion.induction_on (p := fun η =>
    (inner ℬ (ksRhoY φ hφ a₀ ξ) η : ℬ) = inner ℬ ξ (ksRhoY φ hφ (star a₀) η)) η
    (isClosed_eq (continuous_ncInner_right _ _)
      ((continuous_ncInner_right _ _).comp (ksRhoY φ hφ (star a₀)).continuous)) ?_
  intro w
  refine Completion.induction_on (p := fun ξ =>
    (inner ℬ (ksRhoY φ hφ a₀ ξ) (ksEta φ hφ w) : ℬ)
      = inner ℬ ξ (ksRhoY φ hφ (star a₀) (ksEta φ hφ w))) ξ
    (isClosed_eq ((continuous_ncInner_left _ _).comp (ksRhoY φ hφ a₀).continuous)
      (continuous_ncInner_left _ _)) ?_
  intro u
  rw [show ((u : Completion (NC (ksBInner φ hφ))) : ksY φ hφ) = ksEta φ hφ u from rfl,
    ksRhoY_coe, ksRhoY_coe, ksEta_inner, ksEta_inner]
  exact ksRhoCLM_adj φ hφ a₀ u w

/-- `ϱ(a₀)` as an adjointable operator on the completion. -/
private noncomputable def ksRhoBa (a₀ : 𝒜) : Ba ℬ (ksY φ hφ) :=
  ⟨ksRhoY φ hφ a₀, ⟨ksRhoY φ hφ (star a₀), fun ξ η => ksRhoY_adj φ hφ a₀ ξ η⟩⟩

/-- **155II**, the representation `ϱ : 𝒜 → 𝒷ᵃ(Y)`. -/
private noncomputable def ksRho : MIUMap 𝒜 (Ba ℬ (ksY φ hφ)) where
  toFun := ksRhoBa φ hφ
  map_one' := by
    refine Subtype.ext (clm_ext_of_coe fun u => ?_)
    show ksRhoY φ hφ 1 (ksEta φ hφ u) = ksEta φ hφ u
    rw [ksRhoY_coe, ksRhoCLM_one]
  map_mul' a a' := by
    refine Subtype.ext (clm_ext_of_coe fun u => ?_)
    show ksRhoY φ hφ (a * a') (ksEta φ hφ u)
      = ksRhoY φ hφ a (ksRhoY φ hφ a' (ksEta φ hφ u))
    rw [ksRhoY_coe, ksRhoY_coe, ksRhoY_coe, ksRhoCLM_mul]
  map_zero' := by
    refine Subtype.ext (clm_ext_of_coe fun u => ?_)
    show ksRhoY φ hφ 0 (ksEta φ hφ u) = 0
    rw [ksRhoY_coe, ksRhoCLM_zero]
    show ((0 : NC (ksBInner φ hφ)) : Completion (NC (ksBInner φ hφ))) = 0
    exact Completion.coe_zero
  map_add' a a' := by
    refine Subtype.ext (clm_ext_of_coe fun u => ?_)
    show ksRhoY φ hφ (a + a') (ksEta φ hφ u)
      = ksRhoY φ hφ a (ksEta φ hφ u) + ksRhoY φ hφ a' (ksEta φ hφ u)
    rw [ksRhoY_coe, ksRhoY_coe, ksRhoY_coe, ksRhoCLM_add, ksEta_add]
  commutes' r := by
    refine Subtype.ext (clm_ext_of_coe fun u => ?_)
    show ksRhoY φ hφ (algebraMap ℂ 𝒜 r) (ksEta φ hφ u)
      = ((algebraMap ℂ (Ba ℬ (ksY φ hφ)) r).1 : ksY φ hφ →L[ℂ] ksY φ hφ) (ksEta φ hφ u)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ksRhoY_coe,
      ksRhoCLM_smul, ksRhoCLM_one, ksEta_smul, ba_smul_apply']
    rfl
  map_star' a := by
    refine Subtype.ext ?_
    have h1 : ModuleAdjointTo ℬ ⇑(ksRhoY φ hφ a) ⇑(ksRhoY φ hφ (star a)) :=
      fun ξ η => ksRhoY_adj φ hφ a ξ η
    have h2 : ModuleAdjointTo ℬ ⇑(ksRhoY φ hφ a)
        ⇑((star (ksRhoBa φ hφ a) : Ba ℬ (ksY φ hφ)).1) := by
      let _ : NormedSpace ℂ (ksY φ hφ) := NormedSpace.ofCore (CStarModule.normedSpaceCore ℬ)
      exact baSubalgebra_star_spec (𝒷 := ℬ) (X := ksY φ hφ) (ksRhoBa φ hφ a)
    have h4 : ((ksRhoBa φ hφ (star a) : Ba ℬ (ksY φ hφ)).1) = ksRhoY φ hφ (star a) := rfl
    rw [h4]
    exact DFunLike.coe_injective (moduleAdjointTo_unique (𝒜 := ℬ) _ _ _ h1 h2)


private theorem continuous_inner_right' (x : X) :
    Continuous (fun y : X => (inner ℬ x y : ℬ)) := by
  have hl : LipschitzWith ‖x‖₊ (fun y : X => (inner ℬ x y : ℬ)) := by
    refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    rw [dist_eq_norm, dist_eq_norm, ← CStarModule.inner_sub_right]
    have hb : ‖(inner ℬ x (y - y') : ℬ)‖ ≤ ‖x‖ * ‖y - y'‖ := CStarModule.norm_inner_le X
    simpa using hb
  exact hl.continuous

/-- `T : X → Y`, `x ↦ x ⊗ 1`, as a linear map into `X ⊙ 𝒜`. -/
private noncomputable def ksTLM : X →ₗ[ℂ] NC (ksBInner φ hφ) where
  toFun x := (x ⊗ₜ[ℂ] (1 : 𝒜) : X ⊗[ℂ] 𝒜)
  map_add' x y := by
    show ((x + y) ⊗ₜ[ℂ] (1 : 𝒜) : X ⊗[ℂ] 𝒜)
      = (x ⊗ₜ[ℂ] (1 : 𝒜) : X ⊗[ℂ] 𝒜) + (y ⊗ₜ[ℂ] (1 : 𝒜) : X ⊗[ℂ] 𝒜)
    rw [TensorProduct.add_tmul]
  map_smul' c x := by
    show ((c • x) ⊗ₜ[ℂ] (1 : 𝒜) : X ⊗[ℂ] 𝒜) = c • (x ⊗ₜ[ℂ] (1 : 𝒜) : X ⊗[ℂ] 𝒜)
    rw [TensorProduct.smul_tmul']

private theorem ksT_bound (x : X) :
    (ksBInner φ hφ).norm (x ⊗ₜ[ℂ] (1 : 𝒜)) ≤ Real.sqrt ‖φ (1 : 𝒜)‖ * ‖x‖ := by
  have hin : (ksBInner φ hφ).inner (x ⊗ₜ[ℂ] (1 : 𝒜)) (x ⊗ₜ[ℂ] (1 : 𝒜))
      = (inner ℬ x ((φ (1 : 𝒜)).1 x) : ℬ) := by
    show ksPair φ _ _ = _
    rw [ksPair_tmul, star_one, one_mul]
  have h1 : ‖(inner ℬ x ((φ (1 : 𝒜)).1 x) : ℬ)‖ ≤ ‖φ (1 : 𝒜)‖ * ‖x‖ ^ 2 := by
    calc ‖(inner ℬ x ((φ (1 : 𝒜)).1 x) : ℬ)‖ ≤ ‖x‖ * ‖(φ (1 : 𝒜)).1 x‖ :=
          CStarModule.norm_inner_le X
      _ ≤ ‖x‖ * (‖φ (1 : 𝒜)‖ * ‖x‖) := by
          gcongr
          exact ba_apply_norm_le (φ (1 : 𝒜)) x
      _ = ‖φ (1 : 𝒜)‖ * ‖x‖ ^ 2 := by ring
  show Real.sqrt ‖(ksBInner φ hφ).inner (x ⊗ₜ[ℂ] (1 : 𝒜)) (x ⊗ₜ[ℂ] (1 : 𝒜))‖ ≤ _
  rw [hin]
  calc Real.sqrt ‖(inner ℬ x ((φ (1 : 𝒜)).1 x) : ℬ)‖
      ≤ Real.sqrt (‖φ (1 : 𝒜)‖ * ‖x‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt ‖φ (1 : 𝒜)‖ * ‖x‖ := by
        rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- **155II**, the map `T : X → Y`. -/
private noncomputable def ksT : X →L[ℂ] ksY φ hφ :=
  (Completion.toComplL : NC (ksBInner φ hφ) →L[ℂ] ksY φ hφ).comp
    (LinearMap.mkContinuous (ksTLM φ hφ) (Real.sqrt ‖φ (1 : 𝒜)‖) (fun x => ksT_bound φ hφ x))

private theorem ksT_apply (x : X) :
    ksT φ hφ x = ksEta φ hφ (x ⊗ₜ[ℂ] (1 : 𝒜)) := rfl

/-- `T* : Y → X`, `x ⊗ a ↦ φ(a) x`, on `X ⊙ 𝒜`. -/
private noncomputable def ksTadjLM : (X ⊗[ℂ] 𝒜) →ₗ[ℂ] X :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ (fun (x : X) (a : 𝒜) => ((φ a).1 x : X))
    (fun x y a => by rw [map_add])
    (fun c x a => by rw [map_smul])
    (fun x a a' => by rw [map_add, ba_add_apply])
    (fun c x a => by rw [map_smul, ba_smul_apply])

private theorem ksTadjLM_tmul (x : X) (a : 𝒜) :
    ksTadjLM φ (x ⊗ₜ[ℂ] a) = (φ a).1 x := rfl

private theorem ksTadj_pair (y : X) (u : X ⊗[ℂ] 𝒜) :
    (inner ℬ y (ksTadjLM φ u) : ℬ) = (ksBInner φ hφ).inner (y ⊗ₜ[ℂ] (1 : 𝒜)) u := by
  induction u using TensorProduct.induction_on with
  | zero =>
      rw [map_zero (ksTadjLM φ), CStarModule.inner_zero_right,
        (ksBInner φ hφ).inner_zero_right]
  | tmul x a =>
      rw [ksTadjLM_tmul]
      show _ = ksPair φ _ _
      rw [ksPair_tmul, star_one, one_mul]
  | add u v h1 h2 =>
      rw [map_add (ksTadjLM φ) u v, CStarModule.inner_add_right, h1, h2,
        (ksBInner φ hφ).inner_add_right]

private theorem ksTadj_bound (u : X ⊗[ℂ] 𝒜) :
    ‖ksTadjLM φ u‖ ≤ Real.sqrt ‖φ (1 : 𝒜)‖ * (ksBInner φ hφ).norm u := by
  have h1 : ‖ksTadjLM φ u‖ ^ 2 = ‖(inner ℬ (ksTadjLM φ u) (ksTadjLM φ u) : ℬ)‖ :=
    CStarModule.norm_sq_eq (A := ℬ)
  rw [ksTadj_pair φ hφ (ksTadjLM φ u) u] at h1
  have h3 : ‖(ksBInner φ hφ).inner (ksTadjLM φ u ⊗ₜ[ℂ] (1 : 𝒜)) u‖
      ≤ (ksBInner φ hφ).norm (ksTadjLM φ u ⊗ₜ[ℂ] (1 : 𝒜)) * (ksBInner φ hφ).norm u :=
    module_seminorm_1 _ _ _
  have h4 := ksT_bound φ hφ (ksTadjLM φ u)
  have hnn : (0 : ℝ) ≤ (ksBInner φ hφ).norm u := Real.sqrt_nonneg _
  have hsq : (0 : ℝ) ≤ Real.sqrt ‖φ (1 : 𝒜)‖ := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le (norm_nonneg (ksTadjLM φ u)) with h | h
  · rw [← h]
    positivity
  · nlinarith [h1, h3, h4]

/-- **155II**, the adjoint `T* : Y → X`. -/
private noncomputable def ksTadjCLM : NC (ksBInner φ hφ) →L[ℂ] X :=
  LinearMap.mkContinuous (ksTadjLM φ : NC (ksBInner φ hφ) →ₗ[ℂ] X)
    (Real.sqrt ‖φ (1 : 𝒜)‖) (fun u => ksTadj_bound φ hφ u)

private noncomputable def ksTadj : ksY φ hφ →L[ℂ] X := by
  letI : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore ℬ)
  exact clmExtend (ksTadjCLM φ hφ)

private theorem ksTadj_coe (u : NC (ksBInner φ hφ)) :
    ksTadj φ hφ (ksEta φ hφ u) = ksTadjCLM φ hφ u := by
  letI : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore ℬ)
  show clmExtend (ksTadjCLM φ hφ) (u : Completion (NC (ksBInner φ hφ))) = _
  rw [clmExtend_coe]

private theorem ksT_adjointTo : ModuleAdjointTo ℬ ⇑(ksT φ hφ) ⇑(ksTadj φ hφ) := by
  intro x ξ
  refine Completion.induction_on (p := fun ξ =>
    (inner ℬ (ksT φ hφ x) ξ : ℬ) = inner ℬ x (ksTadj φ hφ ξ)) ξ
    (isClosed_eq (continuous_ncInner_right _ _)
      ((continuous_inner_right' x).comp (ksTadj φ hφ).continuous)) ?_
  intro u
  show (inner ℬ (ksT φ hφ x) (ksEta φ hφ u) : ℬ) = inner ℬ x (ksTadj φ hφ (ksEta φ hφ u))
  have h1 : (inner ℬ (ksT φ hφ x) (ksEta φ hφ u) : ℬ)
      = (ksBInner φ hφ).inner (x ⊗ₜ[ℂ] (1 : 𝒜)) u := ksEta_inner φ hφ _ u
  have h2 : (inner ℬ x (ksTadj φ hφ (ksEta φ hφ u)) : ℬ)
      = (ksBInner φ hφ).inner (x ⊗ₜ[ℂ] (1 : 𝒜)) u := by
    rw [ksTadj_coe]
    exact ksTadj_pair φ hφ x u
  rw [h1, h2]


include hφ in
/-- **155II**: the KSGNS dilation built above. -/
private theorem ksgns_aux :
    ∃ (Y : Type u) (_ : NormedAddCommGroup Y) (_ : Module ℂ Y)
      (_ : SMul ℬ Y) (_ : CStarModule ℬ Y) (_ : CompleteSpace Y)
      (ϱ : MIUMap 𝒜 (Ba ℬ Y)) (T : X →L[ℂ] Y) (T' : Y →L[ℂ] X),
      ModuleAdjointTo ℬ ⇑T ⇑T' ∧
      ∀ a : 𝒜, (φ a).1 = T'.comp (((ϱ a).1).comp T) := by
  refine ⟨ksY φ hφ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ksRho φ hφ, ksT φ hφ, ksTadj φ hφ, ksT_adjointTo φ hφ, fun a => ?_⟩
  refine ContinuousLinearMap.ext fun x => ?_
  show (φ a).1 x = ksTadj φ hφ ((ksRho φ hφ a).1 (ksT φ hφ x))
  have h1 : (ksRho φ hφ a).1 (ksT φ hφ x) = ksEta φ hφ (x ⊗ₜ[ℂ] (a * 1)) :=
    ksRhoY_coe φ hφ a (x ⊗ₜ[ℂ] (1 : 𝒜))
  have h2 : ksTadj φ hφ (ksEta φ hφ (x ⊗ₜ[ℂ] (a * 1))) = (φ (a * 1)).1 x :=
    ksTadj_coe φ hφ (x ⊗ₜ[ℂ] (a * 1))
  rw [h1, h2, mul_one]

end Assembly

end KSGNS


/-- **155II** (dils.tex:3857, Theorem (KSGNS)): for a cp-map
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
  ksgns_aux φ hφ

/-! ## Parsec 1560: injectivity of the Paschke representation

**156I** (dils.tex:3876): introduction; **156III** is the proof — not
converted. -/

section Injective

variable {𝒜 ℬ : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

-- The right ℬ-action on `𝒜 ⊙ ℬ` (`ptensSMul`, parsec 1540 above) is declared
-- `local`; the proof below descends to the *concrete* module `𝒜 ⊗_φ ℬ`, where
-- `hilmod-fixed-on-V` lives, so it has to be switched on again here.
attribute [local instance] ptensSMul

/-- **156II** (`paschke-injective`, dils.tex:3883, Theorem), carrier form:
for an ncp-map `φ : 𝒜 → ℬ` with Paschke dilation `(𝒫, ϱ, h)` we have
`⌈ϱ⌉ = ⌈⌈φ⌉⌉` (the carrier of `ϱ` is the central carrier of `φ`); stated
via the characterization used in the proof: for every projection
`p ∈ 𝒜`, `ϱ(p) = 0` iff `φ(a* p a) = 0` for all `a ∈ 𝒜`.

The proof is the thesis's (dils.tex:3893–3919).  By `paschke-unique-up-to-iso`
(here `exists_paschke_iso_paschkeModule`) it is enough to prove the
equivalence for the dilation constructed in **154III** — so the transport is
done first, onto the *concrete* `paschkeModuleOf φ E`, where
`ϱ(p)(a ⊗ b) = (ap) ⊗ b` and `⟨(ap) ⊗ b, (ap) ⊗ b⟩ = b φ(a p a*) b*`.  Read
at `b = 1` and `a := a*` that gives `⇒`; conversely the hypothesis kills
every elementary tensor, hence (by `exists_fin_tmul` and linearity of `η`)
every `η v`, and **152IX** `hilmod_fixed_on_V_eq` — the thesis's own last
step — concludes `ϱ(p) = 0`.

The `[VonNeumannAlgebra ℬ]` binder here and on `paschke_injective` below is
the source's own, not a strengthening: dils.tex 156II is stated for an
ncp-map, and ncp-maps go between von Neumann algebras (every sibling in this
file — `existence_paschke`, **157IV** — carries both binders).  Without it
there is no `PaschkeModule φ` to transport to. -/
theorem paschke_injective_carrier [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (D : PaschkeTriple 𝒜 ℬ)
    (hD : IsPaschkeDilationOf D ⇑φ) (p : 𝒜) (hp : IsStarProjection p) :
    D.ρ p = 0 ↔ ∀ a : 𝒜, φ (star a * p * a) = 0 := by
  letI := D.vn
  -- dils.tex:3893: by `paschke-unique-up-to-iso` it suffices to prove the
  -- equivalence for the dilation constructed in **154III**
  obtain ⟨E⟩ := dils_completion (𝒷 := ℬ) (V := 𝒜 ⊗[ℂ] ℬ) (ptensBInner φ)
  obtain ⟨ϑ, ⟨hbij, hϑρ, -⟩, -⟩ :=
    exists_paschke_iso_paschkeModule φ (paschkeModuleOf φ E) D hD
  have hϑ0 : (ϑ (0 : D.P) : (Ba ℬ (paschkeModuleOf φ E).X)ᵐᵒᵖ) = 0 :=
    map_zero ϑ.toStarAlgHom
  -- `(a p)(a p)* = a p a*`, since `p` is a projection
  have hpp : ∀ a : 𝒜, (a * p) * star (a * p) = a * p * star a := fun a => by
    rw [star_mul, hp.isSelfAdjoint.star_eq, ← mul_assoc, mul_assoc a p p,
      hp.isIdempotentElem.eq]
  constructor
  · -- `ϱ(p) = 0`, so `ϱ(p) a ⊗ b = (ap) ⊗ b = 0`, so `b φ(a p a*) b* = 0`
    intro h
    have hM : ((paschkeModuleOf φ E).ρ p :
        (Ba ℬ (paschkeModuleOf φ E).X)ᵐᵒᵖ) = 0 := by
      rw [← hϑρ p, h, hϑ0]
    intro a
    have hz : (paschkeModuleOf φ E).tprod (star a * p) 1 = 0 :=
      ((paschkeModuleOf φ E).ρ_tprod p (star a) 1).symm.trans
        (congrArg (fun T : (Ba ℬ (paschkeModuleOf φ E).X)ᵐᵒᵖ =>
          (T.unop).1 ((paschkeModuleOf φ E).tprod (star a) 1)) hM)
    have h2 : (inner ℬ ((paschkeModuleOf φ E).tprod (star a * p) 1)
        ((paschkeModuleOf φ E).tprod (star a * p) 1) : ℬ) = 0 := by
      rw [hz, CStarModule.inner_zero_left]
    rw [(paschkeModuleOf φ E).inner_tprod, hpp (star a), star_star, one_mul,
      star_one, mul_one] at h2
    exact h2
  · intro h
    have hφa : ∀ a : 𝒜, φ (a * p * star a) = 0 := fun a => by
      have := h (star a)
      rwa [star_star] at this
    have hM : ((paschkeModuleOf φ E).ρ p :
        (Ba ℬ (paschkeModuleOf φ E).X)ᵐᵒᵖ) = 0 := by
      -- `T` is `ϱ(p)` read on `E.X` itself, which is what `hilmod-fixed-on-V`
      -- speaks about (`(paschkeModuleOf φ E).X` is `E.X`, but only by unfolding)
      obtain ⟨T, hTadj, hTt⟩ : ∃ (T : E.X →L[ℂ] E.X) (_ : ModuleAdjointable ℬ ⇑T),
          ∀ x, T x = (((paschkeModuleOf φ E).ρ p).unop).1 x :=
        ⟨(((paschkeModuleOf φ E).ρ p).unop).1,
          (((paschkeModuleOf φ E).ρ p).unop).2, fun _ => rfl⟩
      -- `ϱ(p) a ⊗ b = (ap) ⊗ b` has `⟨(ap) ⊗ b, (ap) ⊗ b⟩ = b φ(a p a*) b* = 0`
      have htp : ∀ (a : 𝒜) (b : ℬ), T (ptprod φ E a b) = 0 := by
        intro a b
        rw [hTt]
        show (((paschkeModuleOf φ E).ρ p).unop).1
          ((paschkeModuleOf φ E).tprod a b) = 0
        rw [(paschkeModuleOf φ E).ρ_tprod]
        have hzero : (inner ℬ ((paschkeModuleOf φ E).tprod (a * p) b)
            ((paschkeModuleOf φ E).tprod (a * p) b) : ℬ) = 0 := by
          rw [(paschkeModuleOf φ E).inner_tprod, hpp a, hφa a, mul_zero, zero_mul]
        exact CStarModule.inner_self.mp hzero
      have hTη : ∀ v : 𝒜 ⊗[ℂ] ℬ, T (E.η v) = 0 := by
        intro v
        obtain ⟨n, a, b, rfl⟩ := exists_fin_tmul v
        rw [eta_sum φ E a b, map_sum]
        exact Finset.sum_eq_zero fun i _ => htp (a i) (b i)
      -- **152IX** `hilmod-fixed-on-V`: the vector states of the ultranorm
      -- dense image of `η` already decide equality, so `ϱ(p) = 0`
      have hT0 : T = (0 : Ba ℬ E.X).1 :=
        hilmod_fixed_on_V_eq (ptensBInner φ) E T (0 : Ba ℬ E.X).1 hTadj
          (0 : Ba ℬ E.X).2 fun v => by
            rw [show T (E.η v) = ((0 : Ba ℬ E.X).1) (E.η v) from hTη v]
      refine MulOpposite.unop_injective
        (Subtype.ext (ContinuousLinearMap.ext fun x => ?_))
      exact (hTt x).symm.trans (congrArg (fun f : E.X →L[ℂ] E.X => f x) hT0)
    exact hbij.1 ((hϑρ p).trans (hM.trans hϑ0.symm))

/-- Auxiliary for **156II**: for `‖a‖ ≤ 1` and a projection `r`, the
conjugate `a*ra` is an effect — `a*ra ≤ a*a ≤ ‖a*a‖·1 ≤ 1`.  (The same
estimate that **55V** `ad_contraposed` runs, and the reason it is stated for
`‖a‖ ≤ 1`.) -/
private theorem conj_proj_effect {a r : 𝒜} (ha : ‖a‖ ≤ 1)
    (hr : IsStarProjection r) : star a * r * a ∈ effects 𝒜 := by
  refine ⟨star_left_conjugate_nonneg hr.nonneg a, ?_⟩
  have h1 : star a * r * a ≤ star a * 1 * a :=
    star_left_conjugate_le_conjugate hr.le_one a
  rw [mul_one] at h1
  refine h1.trans ?_
  have hnn : (0 : 𝒜) ≤ star a * a := star_mul_self_nonneg a
  have hn : ‖star a * a‖ ≤ 1 := by
    calc ‖star a * a‖ ≤ ‖star a‖ * ‖a‖ := norm_mul_le _ _
      _ ≤ 1 := by rw [norm_star]; nlinarith [norm_nonneg a]
  refine (le_norm_smul_one hnn).trans ?_
  have h2 := smul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ‖star a * a‖) (zero_le_one (α := 𝒜))
  rw [sub_smul, one_smul, sub_nonneg] at h2
  exact h2

/-- Auxiliary for **156II**, the first link of the thesis's chain
(dils.tex:3904, "in other words `a*pa ≤ ⌈φ⌉^⊥`"): for an *effect* `c`,
`f(c) = 0` iff `c ≤ ⌈f⌉^⊥`.

Forwards: `⌈f(⌈c⌉)⌉ = ⌈f(c)⌉ = 0` by **60V** `ncp_ceil`, so `f(⌈c⌉) = 0` by
**59III**.3 `ceil_basic_3`, so `⌈f⌉ ≤ ⌈c⌉^⊥` by the leastness of the carrier
(**63I** `carrier_spec`), and `c ≤ ⌈c⌉`.  Backwards: `0 ≤ f(c) ≤ f(⌈f⌉^⊥) = 0`
by monotonicity. -/
private theorem pmap_eq_zero_iff_le_carrier_ortho [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (f : 𝒜 →ₚ[ℂ] ℬ) (hf : PreservesDirSups ⇑f) {c : 𝒜}
    (hc : c ∈ effects 𝒜) : (f c : ℬ) = 0 ↔ c ≤ 1 - carrier f hf := by
  have hnn : ∀ x : 𝒜, 0 ≤ x → (0 : ℬ) ≤ f x := fun x hx => by
    have h : (f (0 : 𝒜) : ℬ) ≤ f x := f.monotone hx
    rwa [map_zero f] at h
  constructor
  · intro h
    have h1 : ceil (f (ceil c)) = 0 := by
      rw [← ncp_ceil f hf c hc.1, h, ceil_zero]
    have h2 : (f (ceil c) : ℬ) = 0 :=
      (ceil_basic_3 _ (hnn _ (ceil_spec hc.1).1.nonneg)).mpr h1
    have hle : carrier f hf ≤ 1 - ceil c :=
      (carrier_spec f hf).2.2 _ (ceil_spec hc.1).1.one_sub (by rwa [sub_sub_cancel])
    have hcc : c ≤ ceil c :=
      (le_proj_iff hc (ceil_spec hc.1).1).mpr (by
        rw [mul_sub, mul_one, (ceil_spec hc.1).2.1, sub_self])
    exact hcc.trans (le_sub_comm.mp hle)
  · intro h
    refine le_antisymm ?_ (hnn _ hc.1)
    have h2 : (f c : ℬ) ≤ f (1 - carrier f hf) := f.monotone h
    rwa [(carrier_spec f hf).2.1] at h2

/-- Auxiliary for **156II**: the thesis's chain at dils.tex:3904–3912.  For a
projection `p`: `f(a*pa) = 0` for every `a` iff `⌈⌈f⌉⌉ ≤ p^⊥`.

Link by link, as printed: `f(a*pa) = 0` iff `a*pa ≤ ⌈f⌉^⊥`
(`pmap_eq_zero_iff_le_carrier_ortho`), iff `a⌈f⌉a* ≤ p^⊥` by **55V**
`ad_contraposed`, iff `⌈a⌈f⌉a*⌉ ≤ p^⊥` (both sides are effects, and `⌈·⌉` is
the least projection absorbing them, **59I** `ceil_spec` with **Key lemma 1**
`le_proj_iff`); and since `⌈⌈f⌉⌉ = ⋃_a ⌈a*⌈f⌉a⌉` (**68I** `cceil_fundamental`)
the family of bounds is equivalent to the single bound `⌈⌈f⌉⌉ ≤ p^⊥` by the
leastness of `⋃` (**56XVI** `projSup_spec`).

`ad_contraposed` is stated for `‖a‖ ≤ 1`, which costs nothing here: replacing
`a` by `‖a‖⁻¹a` multiplies `f(a*pa)` by a non-zero scalar and leaves
`⌈a⌈f⌉a*⌉` alone (`⌈λa⌉ = ⌈a⌉` for `λ > 0`, **59III**.4 `ceil_smul`). -/
private theorem pmap_conj_eq_zero_iff_cceilMap_le [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (f : 𝒜 →ₚ[ℂ] ℬ) (hf : PreservesDirSups ⇑f) {p : 𝒜}
    (hp : IsStarProjection p) :
    (∀ a : 𝒜, (f (star a * p * a) : ℬ) = 0) ↔ cceilMap f hf ≤ 1 - p := by
  have hq : IsStarProjection (carrier f hf) := (carrier_spec f hf).1
  have hnn0 : ∀ a : 𝒜, (0 : 𝒜) ≤ a * carrier f hf * star a := fun a => by
    have h := star_left_conjugate_nonneg hq.nonneg (star a)
    rwa [star_star] at h
  -- the printed chain, for `‖a‖ ≤ 1`
  have core : ∀ a : 𝒜, ‖a‖ ≤ 1 →
      ((f (star a * p * a) : ℬ) = 0 ↔ ceil (a * carrier f hf * star a) ≤ 1 - p) := by
    intro a ha
    have h1 : (f (star a * p * a) : ℬ) = 0 ↔ star a * p * a ≤ 1 - carrier f hf :=
      pmap_eq_zero_iff_le_carrier_ortho f hf (conj_proj_effect ha hp)
    have h2 : star a * p * a ≤ 1 - carrier f hf ↔ a * carrier f hf * star a ≤ 1 - p :=
      (ad_contraposed a p (carrier f hf) ha hp hq).out 0 2
    have hsa : ‖star a‖ ≤ 1 := by rwa [norm_star]
    have heff : a * carrier f hf * star a ∈ effects 𝒜 := by
      have h := conj_proj_effect hsa hq
      rwa [star_star] at h
    have h3 : a * carrier f hf * star a ≤ 1 - p ↔
        ceil (a * carrier f hf * star a) ≤ 1 - p := by
      constructor
      · intro h
        refine (ceil_spec heff.1).2.2 _ hp.one_sub ?_
        have h0 : a * carrier f hf * star a * (1 - (1 - p)) = 0 :=
          (le_proj_iff heff hp.one_sub).mp h
        rw [sub_sub_cancel] at h0
        rw [mul_sub, mul_one, h0, sub_zero]
      · intro h
        refine le_trans ?_ h
        refine (le_proj_iff heff (ceil_spec heff.1).1).mpr ?_
        rw [mul_sub, mul_one, (ceil_spec heff.1).2.1, sub_self]
    exact h1.trans (h2.trans h3)
  -- both sides of `core` are invariant under rescaling `a`, so `‖a‖ ≤ 1` is no loss
  have hnormalize : ∀ a : 𝒜, ∃ b : 𝒜, ‖b‖ ≤ 1 ∧
      ((f (star b * p * b) : ℬ) = 0 ↔ (f (star a * p * a) : ℬ) = 0) ∧
      ceil (b * carrier f hf * star b) = ceil (a * carrier f hf * star a) := by
    intro a
    rcases eq_or_ne a 0 with rfl | hane
    · exact ⟨0, by simp, Iff.rfl, rfl⟩
    have hpos : 0 < ‖a‖ := norm_pos_iff.mpr hane
    have htpos : 0 < ‖a‖⁻¹ := inv_pos.mpr hpos
    set t : ℝ := ‖a‖⁻¹ with htdef
    have hst : star ((t : ℂ) • a) = (t : ℂ) • star a := by
      simp [star_smul]
    refine ⟨(t : ℂ) • a, ?_, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, htdef,
        inv_mul_cancel₀ (ne_of_gt hpos)]
    · have hexp : star ((t : ℂ) • a) * p * ((t : ℂ) • a)
          = ((t * t : ℝ) : ℂ) • (star a * p * a) := by
        rw [hst]
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
        norm_cast
      rw [hexp, map_smul f]
      have hne : (((t * t : ℝ) : ℂ)) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        positivity
      refine ⟨fun h => ?_, fun h => by rw [h, smul_zero]⟩
      have h2 := congrArg (fun z : ℬ => (((t * t : ℝ) : ℂ))⁻¹ • z) h
      simp only [smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] at h2
      exact h2
    · have hexp : ((t : ℂ) • a) * carrier f hf * star ((t : ℂ) • a)
          = ((t * t : ℝ) : ℂ) • (a * carrier f hf * star a) := by
        rw [hst]
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
        norm_cast
      rw [hexp, Complex.coe_smul, ceil_smul (hnn0 a) (by positivity)]
  -- `⌈⌈f⌉⌉ = ⋃_a ⌈a*⌈f⌉a⌉` (**68I** `cceil_fundamental`), and `⋃` is least
  have hS : ∀ x ∈ {x : 𝒜 | ∃ a : 𝒜, x = ceil (star a * carrier f hf * a)},
      IsStarProjection x := by
    rintro _ ⟨a, rfl⟩
    exact (ceil_spec (star_left_conjugate_nonneg hq.nonneg a)).1
  obtain ⟨hsproj, hsub, hsleast⟩ := projSup_spec hS
  have hcm : cceilMap f hf
      = projSup {x : 𝒜 | ∃ a : 𝒜, x = ceil (star a * carrier f hf * a)} :=
    (cceil_fundamental (carrier f hf) hq).2
  rw [hcm]
  constructor
  · intro h
    refine hsleast _ hp.one_sub ?_
    rintro _ ⟨a, rfl⟩
    have h4 := hnormalize (star a)
    obtain ⟨b, hb1, hb2, hb3⟩ := h4
    have h5 := (core b hb1).mp (hb2.mpr (h (star a)))
    rw [hb3, star_star] at h5
    exact h5
  · intro h a
    obtain ⟨b, hb1, hb2, hb3⟩ := hnormalize a
    refine hb2.mp ((core b hb1).mpr ?_)
    rw [hb3]
    refine le_trans ?_ h
    have h5 := hsub _ ⟨star a, rfl⟩
    rwa [star_star] at h5

/-- **156II** (`paschke-injective`, dils.tex:3883, Theorem), the equation
itself: `⌈ϱ⌉ = ⌈⌈φ⌉⌉` (dils.tex:3886), the carrier of the Paschke
representation is the central carrier of `φ` (**69I** `cceilMap`, the
`cceil` of the carrier).

The proof is the thesis's (dils.tex:3897–3919): for *every* projection `p`,
`p ≤ ⌈ϱ⌉^⊥` iff `p ≤ ⌈⌈φ⌉⌉^⊥`.  That is `key` below — the thesis's first
chain `ϱ(p) = 0 iff φ(a*pa) = 0 for all a` (`paschke_injective_carrier`)
followed by its second, `φ(a*pa) = 0 for all a iff ⌈⌈φ⌉⌉ ≤ p^⊥`
(`pmap_conj_eq_zero_iff_cceilMap_le`, which runs `ad-contraposed` and
`cceil-fundamental` as printed).  Reading it at `p = ⌈ϱ⌉^⊥` gives
`⌈⌈φ⌉⌉ ≤ ⌈ϱ⌉` and at `p = ⌈⌈φ⌉⌉^⊥` gives `⌈ϱ⌉ ≤ ⌈⌈φ⌉⌉`, by the leastness of
the carrier. -/
theorem paschke_carrier_eq_cceil [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (D : PaschkeTriple 𝒜 ℬ) (hD : IsPaschkeDilationOf D ⇑φ) :
    letI := D.vn
    carrier (nmiuP D.ρ) D.ρ.preservesDirSups'
      = cceilMap (ncpPositive φ) φ.preservesDirSups' := by
  letI := D.vn
  have hcarr := carrier_spec (nmiuP D.ρ) D.ρ.preservesDirSups'
  have hccp : IsStarProjection (cceilMap (ncpPositive φ) φ.preservesDirSups') :=
    (cceil_isLeast (carrier (ncpPositive φ) φ.preservesDirSups')).1.1
  -- dils.tex:3897–3919: `p ≤ ⌈ϱ⌉^⊥` iff `p ≤ ⌈⌈φ⌉⌉^⊥`, for every projection `p`
  have key : ∀ p : 𝒜, IsStarProjection p →
      ((nmiuP D.ρ p : D.P) = 0 ↔
        cceilMap (ncpPositive φ) φ.preservesDirSups' ≤ 1 - p) := by
    intro p hp
    rw [nmiuP_apply]
    refine (paschke_injective_carrier φ D hD p hp).trans ?_
    have hb : (∀ a : 𝒜, φ (star a * p * a) = 0) ↔
        ∀ a : 𝒜, (ncpPositive φ (star a * p * a) : ℬ) = 0 := by
      simp only [ncpPositive_apply]
    exact hb.trans (pmap_conj_eq_zero_iff_cceilMap_le (ncpPositive φ)
      φ.preservesDirSups' hp)
  -- at `p = ⌈ϱ⌉^⊥`: `⌈⌈φ⌉⌉ ≤ ⌈ϱ⌉`
  have hle1 : cceilMap (ncpPositive φ) φ.preservesDirSups'
      ≤ carrier (nmiuP D.ρ) D.ρ.preservesDirSups' := by
    have h := (key _ hcarr.1.one_sub).mp hcarr.2.1
    rwa [sub_sub_cancel] at h
  -- at `p = ⌈⌈φ⌉⌉^⊥`: `⌈ϱ⌉ ≤ ⌈⌈φ⌉⌉`, by the leastness of the carrier
  have hle2 : carrier (nmiuP D.ρ) D.ρ.preservesDirSups'
      ≤ cceilMap (ncpPositive φ) φ.preservesDirSups' :=
    hcarr.2.2 _ hccp ((key _ hccp.one_sub).mpr (le_of_eq (sub_sub_cancel _ _).symm))
  exact le_antisymm hle2 hle1

/-- **156II** (`paschke-injective`, dils.tex:3883, Theorem), the "thus"
(dils.tex:3888): the Paschke representation `ϱ` is injective if and only if
`φ` maps no non-zero central projection to zero (`⌈⌈φ⌉⌉ = 1`).

Both halves are read off the thesis's identity `⌈ϱ⌉ = ⌈⌈φ⌉⌉`
(`paschke_carrier_eq_cceil`), exactly as the thesis does: injectivity of `ϱ`
is `⌈ϱ⌉ = 1` by **63II**.4 `carrier_basic_4`, and `⌈⌈φ⌉⌉ = 1` is the
kill-no-central-projection condition by the leastness of `⌈⌈φ⌉⌉` among
central effects annihilating `φ` (**69I** `cceilMap_least`): if `φ(z) = 0`
for a central projection `z` then `⌈⌈φ⌉⌉ ≤ z^⊥`, and conversely `z = ⌈⌈φ⌉⌉^⊥`
is itself a central projection with `φ(z) = 0`.

See the note on `paschke_injective_carrier` about `[VonNeumannAlgebra ℬ]`. -/
theorem paschke_injective [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (D : PaschkeTriple 𝒜 ℬ) (hD : IsPaschkeDilationOf D ⇑φ) :
    Function.Injective ⇑D.ρ ↔
      ∀ z : 𝒜, IsStarProjection z → IsCentral 𝒜 z → φ z = 0 → z = 0 := by
  letI := D.vn
  set g : 𝒜 →ₚ[ℂ] D.P := nmiuP D.ρ with hgdef
  have hgnorm : PreservesDirSups ⇑g := D.ρ.preservesDirSups'
  set f : 𝒜 →ₚ[ℂ] ℬ := ncpPositive φ with hfdef
  have hfnorm : PreservesDirSups ⇑f := φ.preservesDirSups'
  -- the identity of **156II**
  have hkey : carrier g hgnorm = cceilMap f hfnorm := paschke_carrier_eq_cceil φ D hD
  -- `ϱ` injective iff `⌈ϱ⌉ = 1`, **63II**.4
  have hinj : carrier g hgnorm = 1 ↔ Function.Injective ⇑D.ρ :=
    carrier_basic_4 g hgnorm (fun a b => map_mul D.ρ.toStarAlgHom a b)
  have hcc : IsStarProjection (cceilMap f hfnorm) ∧ IsCentral 𝒜 (cceilMap f hfnorm) := by
    have := (cceil_isLeast (carrier f hfnorm)).1
    exact ⟨this.1, this.2.1⟩
  rw [← hinj, hkey]
  constructor
  · intro h1 z hz hzc hφz
    have hcl := cceilMap_least f hfnorm (1 - z) (effect_orthosupplement z ⟨hz.nonneg, hz.le_one⟩)
      (fun b => by rw [sub_mul, mul_sub, one_mul, mul_one, hzc b])
    have hfz : (f ((1 : 𝒜) - (1 - z)) : ℬ) = 0 := by rw [sub_sub_cancel]; exact hφz
    have hle : cceilMap f hfnorm ≤ 1 - z := hcl.2.mp (hcl.1.mp hfz)
    rw [h1] at hle
    exact le_antisymm (by simpa using le_sub_iff_add_le.mp hle) hz.nonneg
  · intro H
    have hccle : carrier f hfnorm ≤ cceilMap f hfnorm := by
      have hcl := cceilMap_least f hfnorm (cceilMap f hfnorm)
        ⟨hcc.1.nonneg, hcc.1.le_one⟩ hcc.2
      exact hcl.2.mpr le_rfl
    have hfz : (φ ((1 : 𝒜) - cceilMap f hfnorm) : ℬ) = 0 := by
      have hcl := cceilMap_least f hfnorm (cceilMap f hfnorm)
        ⟨hcc.1.nonneg, hcc.1.le_one⟩ hcc.2
      exact hcl.1.mpr hccle
    have hzero : (1 : 𝒜) - cceilMap f hfnorm = 0 :=
      H _ hcc.1.one_sub (fun b => by rw [sub_mul, mul_sub, one_mul, mul_one, hcc.2 b]) hfz
    exact (sub_eq_zero.mp hzero).symm

end Injective

/-! ## Parsec 1570: the order correspondence

**157I** (dils.tex:3926): introduction; **157IIIa**, **157V**–**157X** are
discussion and the proof of **157IV** — not converted. -/

section Correspondence

variable {𝒜 ℬ : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **157II** (dils.tex:3935, Definition): for maps `ψ, χ : 𝒜 → ℬ`, `ψ` is
**ncp-below** `χ` (`ψ ≤_ncp χ`) when `χ - ψ` is an ncp-map. -/
def NCPLe (ψ χ : 𝒜 → ℬ) : Prop :=
  ∃ δ : NCPMap 𝒜 ℬ, ∀ a, χ a = ψ a + δ a

/-- **157II** (dils.tex:3935, Definition), continued: the interval
`[0, φ]_ncp` of maps `ψ` with `0 ≤_ncp ψ ≤_ncp φ`. -/
def ncpInterval (φ : 𝒜 → ℬ) : Set (𝒜 → ℬ) :=
  {ψ | NCPLe (fun _ => 0) ψ ∧ NCPLe ψ φ}

/-- **157III** (dils.tex:3948, Definition): for an ncp-map `φ` with Paschke
dilation `(𝒫, ϱ, h)` and `t` in the commutant of `ϱ(𝒜)`, the map
`φ_t = h(t ϱ(·)) : 𝒜 → ℬ`. -/
noncomputable def phiT (D : PaschkeTriple 𝒜 ℬ) (t : D.P) : 𝒜 → ℬ :=
  fun a => D.h (t * D.ρ a)

/-! ### Auxiliary: ncp-maps compose

`Theses/B/Dils/Stinespring.lean` and `Theses/B/Dils/Pure.lean` carry the same
two constructions, both as `private` declarations, so they are repeated here
rather than exported (a merge is noted in `Pure.lean`'s header). -/

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

**How the thesis's density argument is used here.**  157VII and the `T ≤ 1`
half of 157VIII both read off the *vector states of the dense image of `η`*
(**152IX** `hilmod-fixed-on-V`): the order embedding shows
`⟨x̂, T x̂⟩ = ∑ᵢⱼ bᵢ* φ_T(aᵢ*aⱼ) bⱼ ≥ 0` for `x ∈ 𝒜 ⊙ ℬ` and concludes
`T ≥ 0` by ultranorm density.  An abstract `PaschkeModule` carries no `η`
(the same obstruction that `existence_paschke_5` met in **154VIII**), so
157VII is proved on the *constructed* module — `paschkeModuleOf φ E`, where
`E` is a self-dual completion and `η` is at hand — and carried to an
arbitrary dilation by **157IX**, exactly as the thesis carries the whole of
157IV.  That is `paschkeModuleOf_phiT_reflects_nonneg` and
`phiT_reflects_nonneg` below, and it is what parts 2 and 3 of **157IV**
use.

Two things do *not* need the density argument and are proved without it:
the **injectivity** of `t ↦ φ_t` (the point's "and in particular an
injection"), which follows from the matrix identity
`⟨a ⊗ b, T(a' ⊗ b')⟩ = b' φ_T(a' a*) b*`
(`paschkeModule_inner_tprod_commutant`) together with
`paschkeModule_inner_tprod_separating` and `paschkeModule_ba_ext`; and the
positivity of the `T` produced by 157VIII, which is `T = W*W`. -/

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
(`norm_sq_sum_ptprod` is the same statement for the concrete module).  The
identity is displayed in **154V**; 154II is the definition it saturates. -/
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

/-- **157VII**, injectivity of `t ↦ φ_t` (the point's "and in particular an
injection"): an element of the commutant of `ϱ(𝒜)` with `φ_t = 0` is zero.

The thesis gets this as a corollary of the order embedding, which it proves
by the density argument; here it is the previous lemma together with
`paschkeModule_inner_tprod_separating` and `paschkeModule_ba_ext`, so it is
available for an *abstract* `PaschkeModule` and without any density.  The
positivity-reflection half of 157VII is
`paschkeModuleOf_phiT_reflects_nonneg`/`phiT_reflects_nonneg` below. -/
theorem paschkeModule_phiT_injective [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (t : (Ba ℬ M.X)ᵐᵒᵖ) (ht : ∀ a : 𝒜, t * M.ρ a = M.ρ a * t)
    (h0 : ∀ d : 𝒜, (M.h (t * M.ρ d) : ℬ) = 0) : t = 0 := by
  refine MulOpposite.unop_injective (paschkeModule_ba_ext φ M (S := t.unop)
    (R := 0) fun a' b' => ?_)
  refine paschkeModule_inner_tprod_separating φ M fun a b => ?_
  rw [paschkeModule_inner_tprod_commutant φ M t ht a a' b b', h0, mul_zero,
    zero_mul]

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

/-- `exists_paschke_iso_paschkeModule` (**154III**.5 + **140VIII**) with the
*normality* of the isomorphism and its *uniqueness* forgotten: a bijective
∗-homomorphism `𝒫 → 𝒷ᵃ(𝒜 ⊗_φ ℬ)ᵐᵒᵖ` compatible with `ϱ` and `h`, which is
all parts 2 and 3 of **157IV** consume.

**Not a rendering of 140VIII.**
140VIII in full (the nmiu-isomorphism, and its uniqueness) is
`B/Dils/Stinespring.paschke_unique_up_to_iso`, which this is a corollary
of, via `exists_paschke_iso_paschkeModule`. -/
private theorem exists_paschke_starAlgHom [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (D : PaschkeTriple 𝒜 ℬ) (hD : IsPaschkeDilationOf D ⇑φ) :
    ∃ f : D.P →⋆ₐ[ℂ] (Ba ℬ M.X)ᵐᵒᵖ,
      Function.Bijective ⇑f ∧ (∀ a, f (D.ρ a) = M.ρ a) ∧
      (∀ c, M.h (f c) = D.h c) := by
  letI := D.vn
  obtain ⟨ϑ, ⟨hbij, hρ, hh⟩, -⟩ := exists_paschke_iso_paschkeModule φ M D hD
  exact ⟨ϑ.toStarAlgHom, hbij, hρ, hh⟩

-- The right ℬ-action on `𝒜 ⊙ ℬ` (`ptensSMul`, parsec 1540 above) is
-- declared `local`, and the two lemmas below speak about the *concrete*
-- module `𝒜 ⊗_φ ℬ`, so it has to be switched on again here.
attribute [local instance] ptensSMul

/-- **157VII** (dils.tex:3988, the *Order embedding* step of the proof of
**157IV**) for the module *constructed* in `existence_paschke`: `t ↦ φ_t`
**reflects positivity** — if `t` commutes with `ϱ(𝒜)` and `φ_t` is ncp,
then `0 ≤ t`.  (Injectivity, the point's "and in particular an injection",
is `paschkeModule_phiT_injective` above.)

This is 157VII transcribed.  The point picks `x ∈ 𝒜 ⊙ ℬ`, says that by
**152IX** `hilmod-fixed-on-V` it is enough to show `⟨x̂, T x̂⟩ ≥ 0`, and
computes, for `x̂ = ∑ᵢ aᵢ ⊗ bᵢ`,
`⟨x̂, T x̂⟩ = ∑ᵢⱼ bᵢ* ⟨1⊗1, T ϱ(aᵢ*aⱼ) 1⊗1⟩ bⱼ = ∑ᵢⱼ bᵢ* φ_T(aᵢ*aⱼ) bⱼ ≥ 0`,
the last step by complete positivity of `φ_T`.  Here: `hilmod_fixed_on_V`
for `E`, `exists_fin_tmul` for `x̂ = ∑ᵢ aᵢ ⊗ bᵢ`, the matrix element
`paschkeModule_inner_tprod_commutant` (which is the same computation, done
once for a general pair of elementary tensors rather than summed), and
`phi_gram_nonneg` at `φ_T` for the final inequality.

It is stated for `paschkeModuleOf φ E` and not for an abstract
`PaschkeModule` because `hilmod-fixed-on-V` is a statement about the
*concrete* `η`; `phiT_reflects_nonneg` below carries it to an arbitrary
Paschke dilation by **157IX**, exactly as the thesis does. -/
theorem paschkeModuleOf_phiT_reflects_nonneg [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ : NCPMap 𝒜 ℬ)
    (E : SelfDualCompletion.{u, u, u} (ptensBInner φ))
    (t : (Ba ℬ (paschkeModuleOf φ E).X)ᵐᵒᵖ)
    (ht : ∀ a : 𝒜,
      t * (paschkeModuleOf φ E).ρ a = (paschkeModuleOf φ E).ρ a * t)
    (δ : NCPMap 𝒜 ℬ)
    (hδ : ∀ a : 𝒜,
      (δ a : ℬ) = (paschkeModuleOf φ E).h (t * (paschkeModuleOf φ E).ρ a)) :
    0 ≤ t := by
  rw [mop_nonneg_iff]
  -- `T` is `t` read on `E.X` itself, which is what `hilmod-fixed-on-V` speaks
  -- about (`(paschkeModuleOf φ E).X` is `E.X`, but only by unfolding)
  obtain ⟨T, hTadj, hTt⟩ : ∃ (T : E.X →L[ℂ] E.X) (_ : ModuleAdjointable ℬ ⇑T),
      ∀ x, T x = t.unop.1 x := ⟨t.unop.1, t.unop.2, fun _ => rfl⟩
  -- the matrix element of 157VII, `⟨a ⊗ b, T(a' ⊗ b')⟩ = b' φ_T(a' a*) b*`
  have hmat : ∀ (a a' : 𝒜) (b b' : ℬ),
      (inner ℬ (ptprod φ E a b) (T (ptprod φ E a' b')) : ℬ)
        = b' * δ (a' * star a) * star b := by
    intro a a' b b'
    have h := paschkeModule_inner_tprod_commutant φ (paschkeModuleOf φ E) t ht
      a a' b b'
    rw [← hδ (a' * star a)] at h
    rw [hTt]
    exact h
  -- `⟨x̂, T x̂⟩ = ∑ᵢⱼ bᵢ* φ_T(aᵢ*aⱼ) bⱼ ≥ 0` for `x̂ = ∑ᵢ aᵢ ⊗ bᵢ`
  have hpos : IsPositiveOp ℬ T := by
    refine (hilmod_fixed_on_V (ptensBInner φ) E T hTadj).mpr ?_
    intro v
    obtain ⟨n, a, b, rfl⟩ := exists_fin_tmul v
    rw [eta_sum φ E a b, map_sum, CStarModule.inner_sum_left]
    have hrow : ∀ i : Fin n,
        (inner ℬ (ptprod φ E (a i) (b i))
          (∑ j, T (ptprod φ E (a j) (b j))) : ℬ)
          = ∑ j, b j * δ (a j * star (a i)) * star (b i) := by
      intro i
      rw [CStarModule.inner_sum_right]
      exact Finset.sum_congr rfl fun j _ => hmat (a i) (a j) (b i) (b j)
    rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_comm]
    exact phi_gram_nonneg δ a b
  -- **152IX**/**144I**: the vector forms of the dense image decide positivity
  refine (ba_nonneg_iff t.unop).mpr fun x => ?_
  have h := (hilbmod_ordersep T hTadj).mp hpos x
  exact le_of_le_of_eq h (congrArg (fun y : E.X => (inner ℬ x y : ℬ)) (hTt x))

/-- **157VII** for an arbitrary Paschke dilation `(𝒫, ϱ, h)` of `φ`: if `t`
lies in the commutant of `ϱ(𝒜)` and `φ_t` is ncp, then `0 ≤ t`.  Together
with `phiT_ncpLe` (**157VI**) this is the *order embedding* half of
**157IV**.

The passage from the constructed module to an arbitrary dilation is
**157IX**'s: `paschke-unique-up-to-iso` (here
`exists_paschke_starAlgHom`) gives a ∗-isomorphism `ϑ` with `ϑ ∘ ϱ' = ϱ`
and `h ∘ ϑ = h'`, so `φ_t^{𝒫'} = φ_{ϑ(t)}^{𝒫}`; `ϑ` and its inverse are
positive, so `0 ≤ ϑ(t)` gives `0 ≤ t` (`starAlgHom_nonneg_reflect`, which
is the thesis's "it is easy to see `ϑ` restricts to a linear order
isomorphism `[0,1]_{ϱ'(𝒜)^□} → [0,1]_{ϱ(𝒜)^□}`"). -/
theorem phiT_reflects_nonneg [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (D : PaschkeTriple 𝒜 ℬ) (hD : IsPaschkeDilationOf D ⇑φ)
    (t : D.P) (ht : ∀ a : 𝒜, t * D.ρ a = D.ρ a * t) (δ : NCPMap 𝒜 ℬ)
    (hδ : ∀ a : 𝒜, (δ a : ℬ) = D.h (t * D.ρ a)) :
    0 ≤ t := by
  letI := D.vn
  obtain ⟨E⟩ := dils_completion (𝒷 := ℬ) (V := 𝒜 ⊗[ℂ] ℬ) (ptensBInner φ)
  obtain ⟨f, hbij, hfρ, hfh⟩ :=
    exists_paschke_starAlgHom φ (paschkeModuleOf φ E) D hD
  have hcomm : ∀ a : 𝒜,
      f t * (paschkeModuleOf φ E).ρ a = (paschkeModuleOf φ E).ρ a * f t := by
    intro a
    rw [← hfρ, ← map_mul, ← map_mul, ht a]
  have hδ' : ∀ a : 𝒜,
      (δ a : ℬ) = (paschkeModuleOf φ E).h (f t * (paschkeModuleOf φ E).ρ a) := by
    intro a
    rw [hδ a, ← hfρ, ← map_mul, hfh]
  exact starAlgHom_nonneg_reflect f hbij.1 hbij.2
    (paschkeModuleOf_phiT_reflects_nonneg φ E (f t) hcomm δ hδ')

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

This is the thesis's argument: the identity `a ⊗ b ↦ a ⊗ b` is φ-compatible
into `𝒜 ⊗_ψ ℬ` because `⟨x,x⟩_ψ ≤ ⟨x,x⟩_φ`, the universal property of part 1
turns it into a bounded module map `W`, self-duality of `𝒜 ⊗_ψ ℬ` gives `W*`
(**152VIII** `hilbmod_adjoint_exists`), and `T = W*W`, whence `0 ≤ T`.

The bound `T ≤ 1` is 157VIII's too.  Local deviation in its proof: the
thesis reads
`⟨x, Tx⟩_φ = ⟨x,x⟩_ψ ≤ ⟨x,x⟩_φ` off the elementary tensors and concludes by
`hilmod-fixed-on-V`; here `φ_{1−T} = φ − ψ = δ` is ncp by hypothesis, so
`0 ≤ 1 − T` by **157VII** `phiT_reflects_nonneg` — which is itself proved by
`hilmod-fixed-on-V`, so the density argument is used, once, in the place the
thesis first uses it.

⚠️ **The appeal is to the *transported* form of 157VII**, and that inverts
the thesis's order locally: `phiT_reflects_nonneg` is stated for an arbitrary
Paschke dilation, so it re-runs `dils_completion` + `paschkeModuleOf` and
transports along `exists_paschke_starAlgHom` — which is **154III**.5 +
**140VIII**, i.e. exactly the **157IX** step the thesis performs *after*
157VIII in order to carry it to an arbitrary dilation.  Nothing is circular
(154III and 140VIII both precede parsec 1570), but this rendering of 157VIII
rests on them.  It is forced by the shape of the statement: `M` is an
abstract `PaschkeModule`, which carries no `η` and hence no density
statement, and positivity — unlike the *equalities* that
`paschkeModule_ba_ext` and `paschkeModule_inner_tprod_separating` settle — is
not determined by matrix elements on a non-dense separating set.  A
concrete-module `paschkeModuleOf_phiT_surjective` proved by the thesis's own
`⟨x, Tx⟩_φ = ⟨x,x⟩_ψ ≤ ⟨x,x⟩_φ` and then transported would remove the
detour; that is a new statement, so it is flagged here rather than made. -/
theorem paschkeModule_phiT_surjective [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] (φ ψ δ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (hsum : ∀ a, φ a = ψ a + δ a) :
    ∃ t : (Ba ℬ M.X)ᵐᵒᵖ, (∀ a : 𝒜, t * M.ρ a = M.ρ a * t) ∧ 0 ≤ t ∧ t ≤ 1 ∧
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
  have hcomm : ∀ a : 𝒜,
      MulOpposite.op Z * M.ρ a = M.ρ a * MulOpposite.op Z := by
    intro a
    refine MulOpposite.unop_injective (Subtype.ext
      (ContinuousLinearMap.ext fun x => ?_))
    exact hZcomm a x
  have hval : ∀ d : 𝒜, (M.h (MulOpposite.op Z * M.ρ d) : ℬ) = ψ d := by
    intro d
    rw [M.h_def]
    show (inner ℬ (M.tprod 1 1) ((M.ρ d).unop.1 (Z.1 (M.tprod 1 1))) : ℬ) = ψ d
    rw [hZcomm, hZapp, ← hW' (M.tprod 1 1) (Wc _), hWcapp, hWcapp, M.ρ_tprod,
      hWt, hWt, one_mul, N.inner_tprod]
    simp
  refine ⟨MulOpposite.op Z, hcomm, ?_, ?_, hval⟩
  · rw [mop_nonneg_iff]
    refine (ba_nonneg_iff Z).mpr fun x => ?_
    rw [hZapp, ← hW' x (Wc x)]
    exact CStarModule.inner_self_nonneg
  · -- `T ≤ 1`: `φ_{1−T} = φ − ψ = δ` is ncp, so **157VII** applies
    refine sub_nonneg.mp (phiT_reflects_nonneg φ
      ⟨(Ba ℬ M.X)ᵐᵒᵖ,
        @vonNeumannAlgebra_mulOpposite (Ba ℬ M.X) _ _ _
          (ba_vonNeumannAlgebra M.selfDual),
        M.ρ, M.h⟩ (existence_paschke_5 φ M) (1 - MulOpposite.op Z)
      (fun a => by rw [sub_mul, mul_sub, one_mul, mul_one, hcomm a]) δ
      fun a => ?_)
    have hMhsub : ∀ x y : (Ba ℬ M.X)ᵐᵒᵖ, (M.h (x - y) : ℬ) = M.h x - M.h y :=
      fun x y => map_sub M.h.toCompletelyPositiveMap.toLinearMap x y
    show (δ a : ℬ) = M.h ((1 - MulOpposite.op Z) * M.ρ a)
    rw [sub_mul, hMhsub, one_mul, paschkeModule_h_ρ, hval a, hsum a]
    abel

/-- **157VI** (dils.tex:3974, the Set-up of the proof of **157IV**): for
`0 ≤ s` in the commutant of `ϱ(𝒜)` the map `φ_s = h(s ϱ(·))` is ncp,
because `√s` again commutes with `ϱ(𝒜)`, so `φ_s(a) = h(√s ϱ(a) √s)` is the
composite of the three ncp-maps `ϱ`, `ad_{√s}` and `h`.

Extracted from the proof of `paschke_correspondence_mem` (part 1), which is
now one line of it, and used by parts 2 and 3.  It is model-independent:
only `D` is needed, no `PaschkeModule`.  157VI's two further clauses are
`phiT_ncpLe` and `phiT_one` below.

**Thesis slip**, filed as the **157VI** row of `ERRATA.md`.  157VI says
"Pick `T ∈ ϱ(𝒜)^□`" and then forms `√T`; as printed its conclusion "`φ_T` is
ncp" is false for a general self-adjoint `T` of the commutant (take
`T = −1`, `φ ≠ 0`).  What the argument needs, and what is absorbed here as
the hypothesis `0 ≤ s`, is `0 ≤ T`. -/
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

/-- **157IV** (`paschke-correspondence`, dils.tex:3958, Theorem), the
*linear* clause: `t ↦ φ_t` is additive.  Immediate from the definition —
`h` is linear and `(s + t)ϱ(a) = sϱ(a) + tϱ(a)` — but the point does assert
it, and it was stated in none of the three parts. -/
theorem phiT_add (D : PaschkeTriple 𝒜 ℬ) (s t : D.P) (a : 𝒜) :
    phiT D (s + t) a = phiT D s a + phiT D t a := by
  show (D.h ((s + t) * D.ρ a) : ℬ) = D.h (s * D.ρ a) + D.h (t * D.ρ a)
  rw [add_mul]
  exact map_add D.h.toCompletelyPositiveMap.toLinearMap _ _

/-- **157IV**, the *linear* clause, ℂ-homogeneity. -/
theorem phiT_smul (D : PaschkeTriple 𝒜 ℬ) (c : ℂ) (t : D.P) (a : 𝒜) :
    phiT D (c • t) a = c • phiT D t a := by
  show (D.h ((c • t) * D.ρ a) : ℬ) = c • D.h (t * D.ρ a)
  rw [smul_mul_assoc]
  exact map_smul D.h.toCompletelyPositiveMap.toLinearMap _ _

/-- **157VI** (dils.tex:3974, the Set-up of the proof of **157IV**), second
clause: `t ↦ φ_t` is *monotone* — if `t ≤ s` for `s, t` in the commutant of
`ϱ(𝒜)` then `φ_t ≤_ncp φ_s`.

The thesis's one-liner: `φ_{s−t} = φ_s − φ_t` is ncp by the first clause
(`exists_phiT_ncp`, applicable because `0 ≤ s − t`), which is what
`φ_t ≤_ncp φ_s` says.  No positivity of `t` or `s` separately is needed. -/
theorem phiT_ncpLe [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (D : PaschkeTriple 𝒜 ℬ) (s t : D.P)
    (hsc : ∀ a : 𝒜, s * D.ρ a = D.ρ a * s)
    (htc : ∀ a : 𝒜, t * D.ρ a = D.ρ a * t) (hts : t ≤ s) :
    NCPLe (phiT D t) (phiT D s) := by
  obtain ⟨δ, hδ⟩ := exists_phiT_ncp D (s - t) (sub_nonneg.mpr hts)
    (fun a => by simp only [sub_mul, mul_sub, hsc a, htc a])
  have hhadd : ∀ x y : D.P, (D.h (x + y) : ℬ) = D.h x + D.h y := fun x y =>
    map_add D.h.toCompletelyPositiveMap.toLinearMap x y
  refine ⟨δ, fun a => ?_⟩
  show (D.h (s * D.ρ a) : ℬ) = D.h (t * D.ρ a) + δ a
  rw [hδ a, ← hhadd,
    show t * D.ρ a + (s - t) * D.ρ a = s * D.ρ a from by noncomm_ring]

/-- **157VI** (dils.tex:3974, the Set-up of the proof of **157IV**), third
clause: `φ_1 = φ`.  (Together with the second clause: `T ≤ 1` gives
`φ_T ≤_ncp φ`, which is how 157VI closes.)  This is `h ∘ ϱ = φ`, the first
half of `IsPaschkeDilationOf`. -/
theorem phiT_one [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (D : PaschkeTriple 𝒜 ℬ) (hD : IsPaschkeDilationOf D ⇑φ) :
    phiT D 1 = ⇑φ := by
  funext a
  show (D.h (1 * D.ρ a) : ℬ) = φ a
  rw [one_mul]
  exact hD.1 a

/-- **157VI**, the two clauses together, in the form the point states them:
for `t ≤ 1` in the commutant, `φ_t ≤_ncp φ_1 = φ`. -/
theorem phiT_ncpLe_self [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (D : PaschkeTriple 𝒜 ℬ) (hD : IsPaschkeDilationOf D ⇑φ)
    (t : D.P) (htc : ∀ a : 𝒜, t * D.ρ a = D.ρ a * t) (ht1 : t ≤ 1) :
    NCPLe (phiT D t) ⇑φ := by
  rw [← phiT_one φ D hD]
  exact phiT_ncpLe D 1 t (fun a => by rw [one_mul, mul_one]) htc ht1

/-- **157IV** (`paschke-correspondence`, dils.tex:3958, Theorem), part 1:
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

/-- **157IV** (`paschke-correspondence`, dils.tex:3958, Theorem), part 2:
`t ↦ φ_t` is an order embedding of `[0,1]_{ϱ(𝒜)'}` into `[0,φ]_ncp`: for
`s, t` in the positive unit interval of the commutant,
`φ_t ≤_ncp φ_s` iff `t ≤ s` (in particular `t ↦ φ_t` is injective and
linear).

Both directions are the thesis's, now that **157VI** and **157VII** are
stated in their own right: `←` is `phiT_ncpLe` (157VI's second clause), and
`→` is `phiT_reflects_nonneg` (157VII) applied to `s − t`, whose `φ_{s−t}`
is the ncp-map `δ` witnessing `φ_t ≤_ncp φ_s`.  Of the four order
hypotheses none is needed for either direction; they are kept because the
point quantifies over `[0,1]_{ϱ(𝒜)^□}`. -/
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
  have hstc : ∀ a : 𝒜, (s - t) * D.ρ a = D.ρ a * (s - t) := fun a => by
    simp only [sub_mul, mul_sub, hsc a, htc a]
  constructor
  · rintro ⟨δ, hδ⟩
    -- `δ = φ_{s−t}`, so `φ_{s−t}` is ncp; **157VII** gives `0 ≤ s − t`
    refine sub_nonneg.mp (phiT_reflects_nonneg φ D hD (s - t) hstc δ fun a => ?_)
    rw [sub_mul, hhsub]
    show (δ a : ℬ) = D.h (s * D.ρ a) - D.h (t * D.ρ a)
    rw [show (D.h (s * D.ρ a) : ℬ) = D.h (t * D.ρ a) + δ a from hδ a]
    abel
  · exact fun hts => phiT_ncpLe D s t hsc htc hts

/-- **157IV** (`paschke-correspondence`, dils.tex:3958, Theorem), part 3:
`t ↦ φ_t` maps `[0,1]_{ϱ(𝒜)'}` *onto* `[0,φ]_ncp`.

**157VIII** transcribed on the constructed module
(`paschkeModule_phiT_surjective`: `T = W*W` for the map `W` induced by
`a ⊗_φ b ↦ a ⊗_ψ b`, with `0 ≤ T ≤ 1`) and transported to `D` by **157IX**,
i.e. by `exists_paschke_iso_paschkeModule`. -/
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
  obtain ⟨u, hucomm, hu0, hu1, huφ⟩ := paschkeModule_phiT_surjective φ δ ε M hsum
  -- transport back
  obtain ⟨w, hw⟩ := hbij.2 u
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    refine hbij.1 ?_
    rw [map_mul, map_mul, hw, hfρ, hucomm a]
  · exact starAlgHom_nonneg_reflect f hbij.1 hbij.2 (by rw [hw]; exact hu0)
  · refine sub_nonneg.mp (starAlgHom_nonneg_reflect f hbij.1 hbij.2 ?_)
    rw [map_sub, map_one, hw]
    exact sub_nonneg.mpr hu1
  · funext a
    show (D.h (w * D.ρ a) : ℬ) = ψ a
    rw [← hfh (w * D.ρ a), map_mul, hw, hfρ, huφ a, hψδ a]

end Correspondence

end Theses.B.Dils
