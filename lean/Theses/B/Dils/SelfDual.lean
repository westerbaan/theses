/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 4280–5965.

  parsec 1590:  |x⟩⟨y| operators, ultraweak density of their span
  parsec 1600:  orthocomplements and the projection theorem
  parsec 1610:  ℓ²((pᵢ)ᵢ) and orthonormal bases
  parsec 1620:  comparison of projections; the normal form of self-dual
                modules over factors
  parsec 1630:  the completion is determined by its universal property
  parsec 1640:  the self-dual exterior tensor product
  parsec 1650:  𝒷ᵃ(X) ⊗ 𝒷ᵃ(Y) ≅ 𝒷ᵃ(X ⊗ Y)
  parsec 1660:  ultranorm continuity of the exterior tensor product
  parsec 1670:  the tensor product of Paschke dilations

Statements only; every proof is `sorry`.  Conventions as in
`HilbertModules.lean` (mirrored left-action convention).

NOTE(proc-dep): the tensor product of von Neumann algebras is developed in
thesis A (proc.tex, parsec 1080, label `tensor`), which is not yet
formalized; the interface needed here (an miu-bilinear map whose image
generates, whose product functionals of np-functionals all exist, and whose
product np-functionals are separating — the three clauses `tensor-1`,
`tensor-2`, `tensor-3` of 108II) is axiomatized below as `IsVNTensor`.
-/
import Theses.B.Dils.Paschke
import Theses.B.Dils.Kaplansky

open scoped ComplexOrder CStarAlgebra WithCStarModule Uniformity TensorProduct
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u v

namespace Theses.B.Dils

/-! ## Parsec 1590: the operators |x⟩⟨y|

**159I** (dils.tex:4282): introduction — nothing to formalize. -/

section Ketbra

variable {ℬ : Type u} {X : Type v}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X]

/-! The module laws for the action of `ℬ` on a `CStarModule` (`op_add_smul`,
`op_mul_smul`, `norm_op_smul_le`, …) are in `HilbertModules.lean`; together
they are what is needed to *define* the operator `|x⟩⟨y| : z ↦ ⟨y,z⟩ • x` of
**159II** as a `LinearMap.mkContinuous`. -/

variable (ℬ) in
/-- **159II** (dils.tex:4292, Definition): for `x, y` in a Hilbert
ℬ-module `X`, the bounded operator `|x⟩⟨y| : z ↦ x⟨y,z⟩` (mirrored:
`⟨y,z⟩ • x`; in the literature `θ_{x,y}`, **159IIa**).

The algebra `ℬ` is an explicit argument: `CStarModule ℬ X` is what supplies
the ℬ-valued inner product `⟨y,z⟩`, and it cannot be inferred from `x, y :
X` alone. -/
noncomputable def mketbra (x y : X) : X →L[ℂ] X :=
  LinearMap.mkContinuous
    { toFun := fun z => inner ℬ y z • x
      map_add' := fun z z' => by
        rw [CStarModule.inner_add_right, op_add_smul]
      map_smul' := fun c z => by
        rw [CStarModule.inner_smul_right_complex, op_smul_complex_smul,
          RingHom.id_apply] }
    (‖y‖ * ‖x‖) fun z => by
      calc ‖(inner ℬ y z : ℬ) • x‖ ≤ ‖(inner ℬ y z : ℬ)‖ * ‖x‖ :=
            norm_op_smul_le _ _
        _ ≤ ‖y‖ * ‖z‖ * ‖x‖ :=
            mul_le_mul_of_nonneg_right (CStarModule.norm_inner_le X)
              (norm_nonneg _)
        _ = ‖y‖ * ‖x‖ * ‖z‖ := by ring

variable (ℬ) in
/-- **159II** (dils.tex:4292, Definition), characterizing property:
`|x⟩⟨y| z = ⟨y,z⟩ • x`. -/
theorem mketbra_apply (x y z : X) :
    mketbra ℬ x y z = inner ℬ y z • x :=
  rfl

variable (ℬ) in
/-- **159III** (`hilbmodketbrarules`, dils.tex:4302): `|x⟩⟨y|` is
adjointable, with adjoint `|y⟩⟨x|`. -/
theorem mketbra_adjointable (x y : X) :
    ModuleAdjointTo ℬ (⇑(mketbra ℬ x y) : X → X) ⇑(mketbra ℬ y x) := by
  intro z w
  rw [mketbra_apply, mketbra_apply, CStarModule.inner_op_smul_left,
    CStarModule.inner_op_smul_right, CStarModule.star_inner]

variable (ℬ) in
/-- **159III** (`hilbmodketbrarules`, dils.tex:4302): the calculus of the
`|x⟩⟨y|`: `|xb⟩⟨y| = |x⟩⟨yb*|` (mirrored) and
`|x⟩⟨y| |v⟩⟨w| = |x⟨y,v⟩⟩⟨w|`; if `⟨e,e⟩` is a projection then `|e⟩⟨e|`
is a projection; and `T|x⟩⟨y| = |Tx⟩⟨y|`, `|x⟩⟨y| T* = |x⟩⟨Ty|` for
adjointable `T`. -/
theorem mketbra_rules (x y v w e : X) (b : ℬ)
    (T T' : X →L[ℂ] X) (hT : ModuleAdjointTo ℬ ⇑T ⇑T')
    (he : IsStarProjection (inner ℬ e e)) :
    mketbra ℬ (b • x) y = mketbra ℬ x (star b • y) ∧
    (mketbra ℬ x y).comp (mketbra ℬ v w) = mketbra ℬ (inner ℬ y v • x) w ∧
    ((mketbra ℬ e e).comp (mketbra ℬ e e) = mketbra ℬ e e ∧
      ModuleAdjointTo ℬ (⇑(mketbra ℬ e e) : X → X) ⇑(mketbra ℬ e e)) ∧
    T.comp (mketbra ℬ x y) = mketbra ℬ (T x) y ∧
    (mketbra ℬ x y).comp T' = mketbra ℬ x (T y) := by
  obtain ⟨-, hTc, hTm⟩ := moduleAdjointable_linear (𝒜 := ℬ) ⇑T ⟨_, hT⟩
  refine ⟨?_, ?_, ⟨?_, mketbra_adjointable ℬ e e⟩, ?_, ?_⟩
  · ext z
    change (inner ℬ y z : ℬ) • (b • x) = (inner ℬ (star b • y) z : ℬ) • x
    rw [CStarModule.inner_op_smul_left, star_star, op_mul_smul]
  · ext z
    change (inner ℬ y ((inner ℬ w z : ℬ) • v) : ℬ) • x
      = (inner ℬ w z : ℬ) • ((inner ℬ y v : ℬ) • x)
    rw [CStarModule.inner_op_smul_right, op_mul_smul]
  · ext z
    change (inner ℬ e ((inner ℬ e z : ℬ) • e) : ℬ) • e = (inner ℬ e z : ℬ) • e
    rw [CStarModule.inner_op_smul_right, op_mul_smul, mod_projelabs e he]
  · ext z
    change T ((inner ℬ y z : ℬ) • x) = (inner ℬ y z : ℬ) • T x
    rw [hTm]
  · ext z
    change (inner ℬ y (T' z) : ℬ) • x = (inner ℬ (T y) z : ℬ) • x
    rw [hT y z]

variable [CompleteSpace X]

/-! ### Infrastructure for **159IV**: the projections `p_S = ∑_{i∈S} |eᵢ⟩⟨eᵢ|`

**159VI** (`ketbra-dense-pt1`, dils.tex:4330) — the heart of **159IV**.  The
`p_S`, indexed by the finite subsets of the basis, form an increasing net of
effects of `𝒷ᵃ(X)` with supremum `1`: their vector forms are the partial
Parseval sums (**149IV**), which are bounded by `⟨x,x⟩` (Bessel, `mod_bessel`)
and converge ultraweakly to it, and the vector states of `𝒷ᵃ(X)` are order
separating (**144I**, here through `ba_nonneg_iff`).

The self-duality hypothesis of the thesis is not used below: by **149XI**
`selfDual_of_isONBasis` it already follows from the existence of the basis.
See ERRATA.md. -/

section KetbraProj

variable {ι : Type v}

/-- `|x⟩⟨y|` as an element of `𝒷ᵃ(X)`. -/
noncomputable def mketbraBa (x y : X) : Ba ℬ X :=
  ⟨mketbra ℬ x y, ⟨_, mketbra_adjointable ℬ x y⟩⟩

omit [CompleteSpace X] in
@[simp] theorem mketbraBa_coe (x y : X) :
    (mketbraBa (ℬ := ℬ) x y).1 = mketbra ℬ x y := rfl

/-- The coercion `𝒷ᵃ(X) → B(X)` as an additive map, so that it commutes
with finite sums. -/
private def baVal : Ba ℬ X →+ (X →L[ℂ] X) where
  toFun S := S.1
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem baVal_sum {ι : Type*} (s : Finset ι) (f : ι → Ba ℬ X) (z : X) :
    ((∑ i ∈ s, f i : Ba ℬ X)).1 z = ∑ i ∈ s, ((f i).1 z) := by
  have h : ((∑ i ∈ s, f i : Ba ℬ X)).1 = ∑ i ∈ s, (f i).1 := by
    change baVal _ = _
    exact map_sum baVal _ _
  rw [h]
  simp


variable [VonNeumannAlgebra ℬ]

/-- The finite-rank projection `p_S = ∑_{i∈S} |eᵢ⟩⟨eᵢ|` of **159VI**
(`ketbra-dense-pt1`). -/
noncomputable def onbProj (e : ι → X) (S : Finset ι) : Ba ℬ X :=
  ∑ i ∈ S, mketbraBa (ℬ := ℬ) (e i) (e i)

omit [VonNeumannAlgebra ℬ] in
theorem onbProj_apply (e : ι → X) (S : Finset ι) (z : X) :
    (onbProj (ℬ := ℬ) e S).1 z = ∑ i ∈ S, (inner ℬ (e i) z : ℬ) • e i := by
  rw [onbProj, baVal_sum]
  rfl

omit [VonNeumannAlgebra ℬ] in
/-- `⟨x, p_S x⟩ = ∑_{i∈S} ⟨eᵢ,x⟩⟨x,eᵢ⟩` (mirrored). -/
theorem onbProj_vec (e : ι → X) (S : Finset ι) (x : X) :
    (inner ℬ x ((onbProj (ℬ := ℬ) e S).1 x) : ℬ)
      = ∑ i ∈ S, (inner ℬ (e i) x : ℬ) * inner ℬ x (e i) := by
  rw [onbProj_apply, CStarModule.inner_sum_right]
  exact Finset.sum_congr rfl fun i _ => by rw [CStarModule.inner_op_smul_right]

omit [VonNeumannAlgebra ℬ] in
theorem onbProj_nonneg (e : ι → X) (S : Finset ι) :
    0 ≤ onbProj (ℬ := ℬ) e S := by
  refine (ba_nonneg_iff _).mpr fun x => ?_
  rw [onbProj_vec]
  refine Finset.sum_nonneg fun i _ => ?_
  have h : (inner ℬ x (e i) : ℬ) = star (inner ℬ (e i) x) :=
    (CStarModule.star_inner _ _).symm
  rw [h]
  exact mul_star_self_nonneg (inner ℬ (e i) x)

omit [VonNeumannAlgebra ℬ] in
theorem onbProj_le_one {e : ι → X} (he : OrthonormalFam ℬ e) (S : Finset ι) :
    onbProj (ℬ := ℬ) e S ≤ 1 := by
  rw [← sub_nonneg]
  refine (ba_nonneg_iff _).mpr fun x => ?_
  have h1 : ((1 : Ba ℬ X) - onbProj (ℬ := ℬ) e S).1 x
      = x - (onbProj (ℬ := ℬ) e S).1 x := rfl
  rw [h1, CStarModule.inner_sub_right, onbProj_vec, sub_nonneg]
  exact mod_bessel he x S

omit [VonNeumannAlgebra ℬ] in
theorem onbProj_mono (e : ι → X) {S S' : Finset ι}
    (hS : S ⊆ S') : onbProj (ℬ := ℬ) e S ≤ onbProj (ℬ := ℬ) e S' := by
  classical
  rw [← sub_nonneg]
  refine (ba_nonneg_iff _).mpr fun x => ?_
  have h1 : ((onbProj (ℬ := ℬ) e S' - onbProj (ℬ := ℬ) e S)).1 x
      = (onbProj (ℬ := ℬ) e S').1 x - (onbProj (ℬ := ℬ) e S).1 x := rfl
  rw [h1, CStarModule.inner_sub_right, onbProj_vec, onbProj_vec,
    ← Finset.sum_sdiff hS, add_sub_cancel_right]
  refine Finset.sum_nonneg fun i _ => ?_
  have h : (inner ℬ x (e i) : ℬ) = star (inner ℬ (e i) x) :=
    (CStarModule.star_inner _ _).symm
  rw [h]
  exact mul_star_self_nonneg (inner ℬ (e i) x)


/-- `p_S` as a self-adjoint element of `𝒷ᵃ(X)`. -/
noncomputable def onbProjSA (e : ι → X) (S : Finset ι) :
    selfAdjoint (Ba ℬ X) :=
  ⟨onbProj (ℬ := ℬ) e S, IsSelfAdjoint.of_nonneg (onbProj_nonneg e S)⟩

omit [VonNeumannAlgebra ℬ] in
@[simp] theorem onbProjSA_coe (e : ι → X) (S : Finset ι) :
    ((onbProjSA (ℬ := ℬ) e S : selfAdjoint (Ba ℬ X)) : Ba ℬ X)
      = onbProj (ℬ := ℬ) e S := rfl

/-- **159VI** (`ketbra-dense-pt1`, dils.tex:4330): `⋁_S p_S = 1`.
Parseval (**149IV**) makes `⟨x, p_S x⟩` converge ultraweakly to `⟨x,x⟩`,
and the vector states of `𝒷ᵃ(X)` are order separating (**144I**). -/
theorem onbProj_isLUB {e : ι → X} (he : IsONBasis ℬ e) :
    IsLUB (Set.range fun S : Finset ι => onbProjSA (ℬ := ℬ) e S)
      (1 : selfAdjoint (Ba ℬ X)) := by
  classical
  constructor
  · rintro _ ⟨S, rfl⟩
    exact Subtype.coe_le_coe.mp (onbProj_le_one he.1 S)
  · intro u hu
    refine Subtype.coe_le_coe.mp ?_
    change (1 : Ba ℬ X) ≤ (u : Ba ℬ X)
    rw [← sub_nonneg]
    refine (ba_nonneg_iff _).mpr fun x => ?_
    have hstep : ((u : Ba ℬ X) - 1).1 x = (u : Ba ℬ X).1 x - x := rfl
    rw [hstep, CStarModule.inner_sub_right, sub_nonneg]
    -- `⟨x,x⟩ ≤ ⟨x, u x⟩` by order separation of the np-functionals of `ℬ`
    refine np_orderSeparating _ _ ?_ ?_ fun ω => ?_
    · exact CStarModule.isSelfAdjoint_inner_self (E := X)
    · exact ba_inner_isSelfAdjoint x _ u.2
    -- `ω⟨x, p_S x⟩ ≤ ω⟨x, u x⟩` for every `S`, and the left side tends to
    -- `ω⟨x,x⟩` by Parseval
    have hle : ∀ S : Finset ι,
        (ω (∑ i ∈ S, (inner ℬ (e i) x : ℬ) * inner ℬ x (e i))) ≤ ω (inner ℬ x (u.1.1 x)) := by
      intro S
      have h1 : onbProj (ℬ := ℬ) e S ≤ (u : Ba ℬ X) :=
        Subtype.coe_le_coe.mpr (hu ⟨S, rfl⟩)
      have h2 := ba_inner_mono x h1
      rw [onbProj_vec] at h2
      exact ω.toPositiveLinearMap.monotone' h2
    have hpar := mod_parseval e he x
    rw [uwTendsto_iff] at hpar
    have hlim := hpar ω
    refine le_of_tendsto_of_tendsto' hlim tendsto_const_nhds ?_
    exact hle
  
/-- For an effect `E` of a C*-algebra, `E² ≤ E`. -/
private theorem sq_le_self_of_effect {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {E : A} (h0 : 0 ≤ E) (h1 : E ≤ 1) : E * E ≤ E := by
  obtain ⟨r, hrsa, hr⟩ : ∃ r : A, star r = r ∧ r * r = E :=
    ⟨CFC.sqrt E, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg E)).star_eq,
      CFC.sqrt_mul_sqrt_self E h0⟩
  have h := star_left_conjugate_le_conjugate h1 r
  rw [hrsa, mul_one, hr] at h
  calc E * E = r * E * r := by rw [← hr]; noncomm_ring
    _ ≤ E := h

/-- **159VIII** (dils.tex:4390), the half that is used: `‖1 − p_S‖_ω → 0`
for every np-functional `ω` of `𝒷ᵃ(X)`. -/
theorem onbProj_omegaNorm_tendsto {e : ι → X}
    (he : IsONBasis ℬ e) (ω : NPFunctional (Ba ℬ X)) :
    Tendsto (fun S : Finset ι => omegaNorm (Ba ℬ X) ω (1 - onbProj (ℬ := ℬ) e S))
      atTop (𝓝 0) := by
  classical
  set D : Set (selfAdjoint (Ba ℬ X)) :=
    Set.range fun S : Finset ι => onbProjSA (ℬ := ℬ) e S with hD
  have hne : D.Nonempty := ⟨_, ⟨∅, rfl⟩⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨S, rfl⟩ _ ⟨S', rfl⟩
    refine ⟨onbProjSA (ℬ := ℬ) e (S ∪ S'), ⟨S ∪ S', rfl⟩, ?_, ?_⟩
    · exact Subtype.coe_le_coe.mp (onbProj_mono e Finset.subset_union_left)
    · exact Subtype.coe_le_coe.mp (onbProj_mono e Finset.subset_union_right)
  have hlub := onbProj_isLUB he
  have hnorm := ω.preservesDirSups' D 1 hne hdir hlub
  have hreal : ∀ w ∈ (fun d : selfAdjoint (Ba ℬ X) => (ω (d : Ba ℬ X) : ℂ)) '' D,
      w.im = 0 := by
    rintro _ ⟨d, -, rfl⟩
    exact npFunctional_im_eq_zero ω d.2
  have hre : IsLUB (Complex.re '' ((fun d : selfAdjoint (Ba ℬ X) => (ω (d : Ba ℬ X) : ℂ)) '' D))
      ((ω (1 : Ba ℬ X) : ℂ)).re := isLUB_re_of_isLUB hreal hnorm
  have hset : Complex.re '' ((fun d : selfAdjoint (Ba ℬ X) => (ω (d : Ba ℬ X) : ℂ)) '' D)
      = Set.range fun S : Finset ι => ((ω (onbProj (ℬ := ℬ) e S) : ℂ)).re := by
    ext r
    constructor
    · rintro ⟨w, ⟨d, ⟨S, rfl⟩, rfl⟩, rfl⟩
      exact ⟨S, rfl⟩
    · rintro ⟨S, rfl⟩
      exact ⟨ω (onbProj (ℬ := ℬ) e S), ⟨onbProjSA (ℬ := ℬ) e S, ⟨S, rfl⟩, rfl⟩, rfl⟩
  rw [hset] at hre
  have hmono : Monotone fun S : Finset ι => ((ω (onbProj (ℬ := ℬ) e S) : ℂ)).re := by
    intro S S' hSS'
    exact (Complex.le_def.mp
      (ω.toPositiveLinearMap.monotone' (onbProj_mono e hSS'))).1
  have htend := tendsto_atTop_isLUB hmono hre
  have hsub : Tendsto
      (fun S : Finset ι => ((ω (1 - onbProj (ℬ := ℬ) e S) : ℂ)).re) atTop (𝓝 0) := by
    have h : (fun S : Finset ι => ((ω (1 - onbProj (ℬ := ℬ) e S) : ℂ)).re)
        = fun S : Finset ι =>
          ((ω (1 : Ba ℬ X) : ℂ)).re - ((ω (onbProj (ℬ := ℬ) e S) : ℂ)).re := by
      funext S
      rw [npFunctional_sub]
      simp
    rw [h]
    simpa using htend.const_sub ((ω (1 : Ba ℬ X) : ℂ)).re
  have hsqrt : Tendsto
      (fun S : Finset ι => Real.sqrt ((ω (1 - onbProj (ℬ := ℬ) e S) : ℂ)).re)
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hsub
  refine squeeze_zero (fun S => omegaNorm_nonneg _ _) (fun S => ?_) hsqrt
  set E : Ba ℬ X := 1 - onbProj (ℬ := ℬ) e S with hEdef
  have h0 : (0 : Ba ℬ X) ≤ E := sub_nonneg.mpr (onbProj_le_one he.1 S)
  have h1 : E ≤ 1 := by
    rw [hEdef, sub_le_self_iff]
    exact onbProj_nonneg e S
  have hsa : star E = E := (IsSelfAdjoint.of_nonneg h0).star_eq
  have hmul : star E * E = E * E := by rw [hsa]
  have hle : ((ω (star E * E) : ℂ)).re ≤ ((ω E : ℂ)).re := by
    rw [hmul]
    exact (Complex.le_def.mp
      (ω.toPositiveLinearMap.monotone' (sq_le_self_of_effect h0 h1))).1
  rw [omegaNorm]
  exact Real.sqrt_le_sqrt hle

omit [VonNeumannAlgebra ℬ] in
/-- The compression `p_S T p_S` is a finite linear combination of the
`|eᵢb⟩⟨eⱼ|` (**159VII**, dils.tex:4368). -/
theorem onbProj_compress {e : ι → X} (he : IsONBasis ℬ e) (T : Ba ℬ X)
    (S : Finset ι) :
    onbProj (ℬ := ℬ) e S * T * onbProj (ℬ := ℬ) e S
      = ∑ i ∈ S, ∑ j ∈ S,
          mketbraBa (ℬ := ℬ) ((inner ℬ (e i) (T.1 (e j)) : ℬ) • e i) (e j) := by
  have hT : ModuleAdjointTo ℬ (⇑(T.1) : X → X) ⇑((star T : Ba ℬ X)).1 :=
    baSubalgebra_star_spec T
  simp only [onbProj]
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Subtype.ext ?_
  have hstep :
      (mketbraBa (ℬ := ℬ) (e i) (e i) * T * mketbraBa (ℬ := ℬ) (e j) (e j)).1
        = (mketbra ℬ (e i) (e i)).comp (T.1.comp (mketbra ℬ (e j) (e j))) := rfl
  rw [hstep]
  obtain ⟨-, hcomp, -, -, -⟩ :=
    mketbra_rules ℬ (e i) (e i) (T.1 (e j)) (e j) (e i) 1 T.1 (star T : Ba ℬ X).1
      hT (he.1.2 i).1
  obtain ⟨-, -, -, hleft, -⟩ :=
    mketbra_rules ℬ (e j) (e j) (e j) (e j) (e i) 1 T.1 (star T : Ba ℬ X).1
      hT (he.1.2 i).1
  rw [hleft, hcomp]
  rfl

end KetbraProj

-- `hX` is deliberately unused: **159IV** carries the thesis's self-duality
-- hypothesis, which by **149XI** `selfDual_of_isONBasis` already follows from
-- the orthonormal basis (see ERRATA.md).
set_option linter.unusedVariables false in
/-- **159IV** (`ketbra-ultraweakly-dense`, dils.tex:4319, Proposition): for
a self-dual Hilbert ℬ-module `X` with orthonormal basis `(eᵢ)`, the linear
span of the operators `|eᵢb⟩⟨eⱼ|` is ultraweakly dense in `ℬᵃ(X)`: every
`T` is the ultraweak limit of a net (canonically `p_S T p_S`, indexed by
finite subsets of the basis) from the span.

**159V**–**159VIII** are the proof — not converted. -/
theorem ketbra_ultraweakly_dense [VonNeumannAlgebra ℬ]
    (hX : SelfDual ℬ X) {ι : Type v} (e : ι → X) (he : IsONBasis ℬ e)
    (T : Ba ℬ X) :
    ∃ approx : Finset ι → Ba ℬ X,
      (∀ s, approx s ∈ Submodule.span ℂ
        {S : Ba ℬ X | ∃ (i j : ι) (b : ℬ), S.1 = mketbra ℬ (b • e i) (e j)}) ∧
      UWTendsto approx atTop T := by
  classical
  refine ⟨fun S => onbProj (ℬ := ℬ) e S * T * onbProj (ℬ := ℬ) e S, fun S => ?_, ?_⟩
  · change onbProj (ℬ := ℬ) e S * T * onbProj (ℬ := ℬ) e S ∈ _
    rw [onbProj_compress he T S]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.subset_span ⟨i, j, inner ℬ (e i) (T.1 (e j)), rfl⟩
  · rw [uwTendsto_iff]
    intro ω
    set p : Finset ι → Ba ℬ X := fun S => onbProj (ℬ := ℬ) e S with hp
    -- `T − p T p = (1−p)*T + (pT)*(1−p)`, with `1−p` and `p` self-adjoint
    have hsa : ∀ S, star (p S) = p S := fun S =>
      (IsSelfAdjoint.of_nonneg (onbProj_nonneg e S)).star_eq
    have hsplit : ∀ S, T - p S * T * p S
        = star (1 - p S) * T + star (star T * p S) * (1 - p S) := by
      intro S
      rw [star_sub, star_one, hsa, star_mul, star_star, hsa]
      noncomm_ring
    -- the two Cauchy–Schwarz estimates
    set M : ℝ := ‖(1 : Ba ℬ X)‖ with hM
    have hpnorm : ∀ S, ‖p S‖ ≤ M :=
      fun S => CStarAlgebra.norm_le_norm_of_nonneg_of_le
        (onbProj_nonneg e S) (onbProj_le_one he.1 S)
    set C : ℝ := omegaNorm (Ba ℬ X) ω T + ‖T‖ * (M * omegaNorm (Ba ℬ X) ω 1) with hC
    have hbound : ∀ S, ‖ω (T - p S * T * p S)‖
        ≤ C * omegaNorm (Ba ℬ X) ω (1 - p S) := by
      intro S
      have h2 : omegaNorm (Ba ℬ X) ω (star T * p S)
          ≤ ‖T‖ * (M * omegaNorm (Ba ℬ X) ω 1) := by
        refine le_trans (omegaNorm_mul_le ω (star T) (p S)) ?_
        rw [norm_star]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg T)
        have h3 := omegaNorm_mul_le ω (p S) 1
        rw [mul_one] at h3
        refine le_trans h3 ?_
        exact mul_le_mul_of_nonneg_right (hpnorm S) (omegaNorm_nonneg _ _)
      have hA : ‖ω (star (1 - p S) * T)‖
          ≤ omegaNorm (Ba ℬ X) ω (1 - p S) * omegaNorm (Ba ℬ X) ω T :=
        norm_apply_star_mul_le ω _ _
      have hB : ‖ω (star (star T * p S) * (1 - p S))‖
          ≤ omegaNorm (Ba ℬ X) ω (star T * p S)
            * omegaNorm (Ba ℬ X) ω (1 - p S) :=
        norm_apply_star_mul_le ω _ _
      have hB' : ‖ω (star (star T * p S) * (1 - p S))‖
          ≤ (‖T‖ * (M * omegaNorm (Ba ℬ X) ω 1))
            * omegaNorm (Ba ℬ X) ω (1 - p S) :=
        hB.trans (mul_le_mul_of_nonneg_right h2 (omegaNorm_nonneg _ _))
      calc ‖ω (T - p S * T * p S)‖
          = ‖ω (star (1 - p S) * T + star (star T * p S) * (1 - p S))‖ := by
            rw [hsplit S]
        _ ≤ ‖ω (star (1 - p S) * T)‖ + ‖ω (star (star T * p S) * (1 - p S))‖ := by
            rw [npFunctional_add]; exact norm_add_le _ _
        _ ≤ omegaNorm (Ba ℬ X) ω (1 - p S) * omegaNorm (Ba ℬ X) ω T
              + (‖T‖ * (M * omegaNorm (Ba ℬ X) ω 1))
                * omegaNorm (Ba ℬ X) ω (1 - p S) := add_le_add hA hB'
        _ = C * omegaNorm (Ba ℬ X) ω (1 - p S) := by rw [hC]; ring
    have hz : Tendsto
        (fun S : Finset ι => ‖ω (T - p S * T * p S)‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun S => norm_nonneg _) hbound ?_
      simpa using (onbProj_omegaNorm_tendsto he ω).const_mul C
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine hz.congr fun S => ?_
    have hEq : (ω (T - p S * T * p S) : ℂ)
        = -((ω (p S * T * p S) : ℂ) - ω T) := by
      rw [npFunctional_sub]; ring
    rw [hEq, norm_neg]

/-- **159IX** (`ketbra-ultranorm-continuous`, dils.tex:4378, Proposition):
for a self-dual Hilbert ℬ-module `X`: if a norm-bounded net `x_α → x`
ultranorm, then `|x_α⟩⟨y| → |x⟩⟨y|` ultraweakly.

**159X**–**159XI** are the proof, transcribed below.  Two divergences:
the thesis's preparatory estimate `‖|z⟩⟨y|‖ ≤ ‖z‖‖y‖` (159X, proved there
from order separation of the vector states and `order-separating-norm`) is
already the bound with which `mketbra` is defined — Cauchy–Schwarz plus
`‖b·x‖ ≤ ‖b‖‖x‖` give it outright — so that half of 159X is not needed;
and where the thesis says "`ω(T*(·)T) ∈ Ω`, so `span Ω` is operator-norm
dense by **90II**", we feed `Ω` to `vn_center_separating_fundamental_2`
directly with `S = 𝒷ᵃ(X)` and read the resulting `ωₖ(sₖ*(·)sₖ)` back as
the vector functional of `sₖxₖ`. -/
theorem ketbra_ultranorm_continuous [VonNeumannAlgebra ℬ]
    (hX : SelfDual ℬ X) {ι : Type v} {l : Filter ι} (x : ι → X) (x₀ : X)
    (hbdd : ∃ M : ℝ, ∀ i, ‖x i‖ ≤ M)
    (hx : UnTendsto (inner ℬ) x l x₀) (y : X)
    (K : ι → Ba ℬ X) (hK : ∀ i, (K i).1 = mketbra ℬ (x i) y)
    (K₀ : Ba ℬ X) (hK₀ : K₀.1 = mketbra ℬ x₀ y) :
    UWTendsto K l K₀ := by
  classical
  have : VonNeumannAlgebra (Ba ℬ X) := ba_vonNeumannAlgebra hX
  obtain ⟨M, hM⟩ := hbdd
  set z : ι → X := fun i => x i - x₀ with hzdef
  have hzt : UnTendsto (inner ℬ) z l 0 := by
    intro ν
    simpa [hzdef, sub_zero] using hx ν
  have hKz : ∀ i, (K i - K₀).1 = mketbra ℬ (z i) y := by
    intro i
    have h : (K i - K₀).1 = (K i).1 - K₀.1 := rfl
    rw [h, hK i, hK₀]
    refine ContinuousLinearMap.ext fun v => ?_
    show (inner ℬ y v : ℬ) • x i - (inner ℬ y v : ℬ) • x₀
      = (inner ℬ y v : ℬ) • (x i - x₀)
    have hadd : (inner ℬ y v : ℬ) • (x i - x₀) + (inner ℬ y v : ℬ) • x₀
        = (inner ℬ y v : ℬ) • x i := by
      rw [← op_smul_add]; congr 1; abel
    exact (eq_sub_of_add_eq hadd).symm
  have hnb : ∀ i, ‖K i - K₀‖ ≤ ‖y‖ * (M + ‖x₀‖) := by
    intro i
    have h1 : ‖K i - K₀‖ ≤ ‖y‖ * ‖z i‖ := by
      show ‖(K i - K₀).1‖ ≤ _
      rw [hKz i]
      exact LinearMap.mkContinuous_norm_le _ (by positivity) _
    have h2 : ‖z i‖ ≤ M + ‖x₀‖ := by
      show ‖x i - x₀‖ ≤ M + ‖x₀‖
      linarith [norm_sub_le (x i) x₀, hM i]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg y))
  set Ω : Set (NPFunctional (Ba ℬ X)) :=
    {ν | ∃ (v : X) (fν : NPFunctional ℬ), ν = baVecNP hX v fν} with hΩdef
  have hΩ : CentreSeparatingConj (Ba ℬ X) Ω := by
    rw [centreSeparatingConj_iff]
    intro a ha
    refine ⟨fun h ν hν b => by rw [h]; simp, fun h => ?_⟩
    have hvec : ∀ v : X, (inner ℬ v (a.1 v) : ℬ) = 0 := by
      intro v
      refine VonNeumannAlgebra.np_faithful _ ((ba_nonneg_iff a).mp ha v) fun fν => ?_
      have h1 := h (baVecNP hX v fν) ⟨v, fν, rfl⟩ 1
      rw [star_one, one_mul, mul_one, baVecNP_apply] at h1
      exact h1
    have hle : a ≤ 0 := by
      rw [← neg_nonneg]
      refine (ba_nonneg_iff _).mpr fun v => ?_
      have he : (-a).1 v = -(a.1 v) := rfl
      rw [he, CStarModule.inner_neg_right, hvec v, neg_zero]
    exact le_antisymm hle ha
  rw [uwTendsto_iff]
  intro g
  rw [← tendsto_sub_nhds_zero_iff, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  set C : ℝ := max (‖y‖ * (M + ‖x₀‖)) 0 + 1 with hCdef
  have hC0 : 0 < C := by
    have : (0:ℝ) ≤ max (‖y‖ * (M + ‖x₀‖)) 0 := le_max_right _ _
    linarith
  obtain ⟨n, ω, s, hωs, hgs⟩ :=
    vn_center_separating_fundamental_2 Ω hΩ Set.univ
      (@dense_univ _ (ultrastrong (Ba ℬ X))) g (ε / (2 * C))
      (by positivity)
  have hmem : ∀ k : Fin n, ∃ (v : X) (fν : NPFunctional ℬ), ω k = baVecNP hX v fν :=
    fun k => (hωs k).1
  choose u f hu using hmem
  have hkey : ∀ (k : Fin n) (T : Ba ℬ X),
      ((ω k) (star (s k) * T * s k) : ℂ)
        = f k (inner ℬ ((s k).1 (u k)) (T.1 ((s k).1 (u k)))) := by
    intro k T
    have hadj : ModuleAdjointTo ℬ (⇑((s k).1) : X → X) ⇑((star (s k) : Ba ℬ X)).1 :=
      baSubalgebra_star_spec (s k)
    have hinner : (inner ℬ (u k) ((star (s k) * T * s k).1 (u k)) : ℬ)
        = inner ℬ ((s k).1 (u k)) (T.1 ((s k).1 (u k))) := by
      have h1 : (star (s k) * T * s k).1 (u k)
          = (star (s k) : Ba ℬ X).1 (T.1 ((s k).1 (u k))) := rfl
      rw [h1]
      exact (hadj (u k) (T.1 ((s k).1 (u k)))).symm
    rw [hu k, baVecNP_apply, hinner]
  have hlim : ∀ k : Fin n,
      Tendsto (fun i => ((ω k) (star (s k) * (K i - K₀) * s k) : ℂ)) l (𝓝 0) := by
    intro k
    have hsm : UnTendsto (inner ℬ)
        (fun i => (inner ℬ y ((s k).1 (u k)) : ℬ) • z i) l 0 := by
      have h := ultranormscalar (cstarBInner ℬ X)
        (inner ℬ y ((s k).1 (u k)) : ℬ) z 0 hzt
      rw [op_smul_zero] at h
      exact h
    have hconst : UnTendsto (inner ℬ : X → X → ℬ)
        (fun _ : ι => (s k).1 (u k)) l ((s k).1 (u k)) := by
      intro ν
      simp only [sub_self]
      have h0 : (inner ℬ (0 : X) (0 : X) : ℬ) = 0 :=
        (cstarBInner ℬ X).inner_zero_left 0
      simp [unSeminorm, h0]
      exact tendsto_const_nhds
    have huw := innerprod_ultraweak (cstarBInner ℬ X)
      (fun _ : ι => (s k).1 (u k))
      (fun i => (inner ℬ y ((s k).1 (u k)) : ℬ) • z i)
      ((s k).1 (u k)) 0 hconst hsm
    rw [uwTendsto_iff] at huw
    have h2 := huw (f k)
    have heq : ∀ i, ((ω k) (star (s k) * (K i - K₀) * s k) : ℂ)
        = f k (inner ℬ ((s k).1 (u k))
            ((inner ℬ y ((s k).1 (u k)) : ℬ) • z i)) := by
      intro i
      rw [hkey k (K i - K₀), hKz i, mketbra_apply]
    simp only [heq]
    have hz0 : (inner ℬ ((s k).1 (u k)) (0 : X) : ℬ) = 0 :=
      CStarModule.inner_zero_right
    rw [show ((cstarBInner ℬ X).inner : X → X → ℬ) = inner ℬ from rfl] at h2
    rw [hz0, npFunctional_zero] at h2
    exact h2
  have hsum : Tendsto
      (fun i => ∑ k : Fin n, ((ω k) (star (s k) * (K i - K₀) * s k) : ℂ)) l (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun k _ => hlim k)
    simpa using h
  filter_upwards [NormedAddGroup.tendsto_nhds_zero.mp hsum (ε/2) (half_pos hε)]
    with i hi
  set Sm : ℂ := ∑ k : Fin n, ((ω k) (star (s k) * (K i - K₀) * s k) : ℂ) with hSm
  have hgi : ((g (K i) : ℂ) - g K₀) = g (K i - K₀) := (npFunctional_sub g _ _).symm
  have hb1 : ‖(g (K i - K₀) : ℂ) - Sm‖ ≤ (ε / (2 * C)) * ‖K i - K₀‖ := hgs (K i - K₀)
  have hb2 : ‖K i - K₀‖ ≤ C := by
    have := hnb i
    have h3 : ‖y‖ * (M + ‖x₀‖) ≤ max (‖y‖ * (M + ‖x₀‖)) 0 := le_max_left _ _
    simp only [hCdef]
    linarith
  have hb3 : (ε / (2 * C)) * ‖K i - K₀‖ ≤ ε / 2 := by
    have h4 : (0:ℝ) ≤ ε / (2 * C) := by positivity
    have h5 : (ε / (2 * C)) * ‖K i - K₀‖ ≤ (ε / (2 * C)) * C :=
      mul_le_mul_of_nonneg_left hb2 h4
    have h6 : (ε / (2 * C)) * C = ε / 2 := by field_simp
    linarith
  calc ‖(g (K i) : ℂ) - g K₀‖ = ‖(g (K i - K₀) : ℂ)‖ := by rw [hgi]
    _ = ‖((g (K i - K₀) : ℂ) - Sm) + Sm‖ := by rw [sub_add_cancel]
    _ ≤ ‖(g (K i - K₀) : ℂ) - Sm‖ + ‖Sm‖ := norm_add_le _ _
    _ < ε := by linarith

end Ketbra

/-! ## Parsec 1600: orthocomplements

**160I** (dils.tex:4456): introduction — nothing to formalize. -/

section Ortho

variable {ℬ : Type u} {X Y Z : Type v}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul ℬ Y] [CStarModule ℬ Y]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z] [SMul ℬ Z] [CStarModule ℬ Z]

omit [StarOrderedRing ℬ] in
/-- An inner-product-preserving map between pre-Hilbert ℬ-modules is
automatically additive: `⟨κ(x+x') − κx − κx', κ(x+x') − κx − κx'⟩` expands to
`⟨(x+x') − x − x', (x+x') − x − x'⟩ = 0`. -/
theorem innerPreserving_add (κ : X → Z)
    (h : ∀ x x' : X, inner ℬ (κ x) (κ x') = inner ℬ x x') (x x' : X) :
    κ (x + x') = κ x + κ x' := by
  have hz : (inner ℬ (κ (x + x') - (κ x + κ x')) (κ (x + x') - (κ x + κ x')) : ℬ)
      = 0 := by
    simp only [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
      CStarModule.inner_add_left, CStarModule.inner_add_right, h]
    abel
  have h0 := CStarModule.inner_self (A := ℬ) (x := κ (x + x') - (κ x + κ x')) |>.mp hz
  rwa [sub_eq_zero] at h0

omit [StarOrderedRing ℬ] in
/-- The additive-monoid-hom packaging of an inner-product-preserving map
(`innerPreserving_add`). -/
noncomputable def innerPreservingHom (κ : X → Z)
    (h : ∀ x x' : X, inner ℬ (κ x) (κ x') = inner ℬ x x') : X →+ Z :=
  AddMonoidHom.mk' κ (innerPreserving_add κ h)

/-- Taking the left part of a finite subset of `ι ⊕ κ` is cofinal: the net
indexed by `Finset (ι ⊕ κ)` refines the one indexed by `Finset ι`. -/
private theorem tendsto_finset_toLeft_atTop {ι κ : Type v} :
    Tendsto (Finset.toLeft : Finset (ι ⊕ κ) → Finset ι) atTop atTop :=
  Filter.tendsto_atTop_atTop.mpr fun t =>
    ⟨t.map Function.Embedding.inl, fun _ hs _ hi =>
      Finset.mem_toLeft.mpr (hs (Finset.mem_map_of_mem _ hi))⟩

private theorem tendsto_finset_toRight_atTop {ι κ : Type v} :
    Tendsto (Finset.toRight : Finset (ι ⊕ κ) → Finset κ) atTop atTop :=
  Filter.tendsto_atTop_atTop.mpr fun t =>
    ⟨t.map Function.Embedding.inr, fun _ hs _ hi =>
      Finset.mem_toRight.mpr (hs (Finset.mem_map_of_mem _ hi))⟩

/-- **160II** (`direct-prod-self-dual-basis`, dils.tex:4465, Exercise): the
direct sum of self-dual Hilbert ℬ-modules `X ⊕ Y` (represented abstractly:
a Hilbert ℬ-module `Z` with module embeddings `κ₁, κ₂` which are mutually
orthogonal, inner-product-preserving and jointly surjective) has
`κ₁(E) ∪ κ₂(F)` as an orthonormal basis for bases `E` of `X`, `F` of `Y`;
in particular it is self dual. -/
theorem direct_prod_self_dual_basis [VonNeumannAlgebra ℬ]
    [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z]
    (κ₁ : X → Z) (κ₂ : Y → Z)
    (h₁ : ∀ x x' : X, inner ℬ (κ₁ x) (κ₁ x') = inner ℬ x x')
    (h₂ : ∀ y y' : Y, inner ℬ (κ₂ y) (κ₂ y') = inner ℬ y y')
    (h₁₂ : ∀ (x : X) (y : Y), inner ℬ (κ₁ x) (κ₂ y) = 0)
    (hadd : ∀ z : Z, ∃ (x : X) (y : Y), z = κ₁ x + κ₂ y)
    (hκ₁ : ∀ (b : ℬ) (x : X), κ₁ (b • x) = b • κ₁ x)
    (hκ₂ : ∀ (b : ℬ) (y : Y), κ₂ (b • y) = b • κ₂ y)
    {ι κ : Type v} (e : ι → X) (d : κ → Y)
    (he : IsONBasis ℬ e) (hd : IsONBasis ℬ d) :
    IsONBasis ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d)) ∧ SelfDual ℬ Z := by
  set K₁ : X →+ Z := innerPreservingHom κ₁ h₁ with hK₁def
  set K₂ : Y →+ Z := innerPreservingHom κ₂ h₂ with hK₂def
  have h₂₁ : ∀ (y : Y) (x : X), (inner ℬ (κ₂ y) (κ₁ x) : ℬ) = 0 := by
    intro y x
    have h := congrArg star (h₁₂ x y)
    rwa [CStarModule.star_inner, star_zero] at h
  -- splitting a finite sum over `ι ⊕ κ`
  have hsplit : ∀ (c : ι ⊕ κ → ℬ) (s : Finset (ι ⊕ κ)),
      ∑ g ∈ s, c g • Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) g
        = κ₁ (∑ i ∈ s.toLeft, c (Sum.inl i) • e i)
          + κ₂ (∑ j ∈ s.toRight, c (Sum.inr j) • d j) := by
    intro c s
    rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
    congr 1
    · rw [show κ₁ (∑ i ∈ s.toLeft, c (Sum.inl i) • e i)
        = K₁ (∑ i ∈ s.toLeft, c (Sum.inl i) • e i) from rfl, map_sum]
      exact Finset.sum_congr rfl fun i _ => (hκ₁ _ _).symm
    · rw [show κ₂ (∑ j ∈ s.toRight, c (Sum.inr j) • d j)
        = K₂ (∑ j ∈ s.toRight, c (Sum.inr j) • d j) from rfl, map_sum]
      exact Finset.sum_congr rfl fun j _ => (hκ₂ _ _).symm
  -- the embeddings are ultranorm isometries
  have htr₁ : ∀ (ω : NPFunctional ℬ) (u u' : X),
      unSeminorm ω (inner ℬ : Z → Z → ℬ) (κ₁ u - κ₁ u')
        = unSeminorm ω (inner ℬ : X → X → ℬ) (u - u') := by
    intro ω u u'
    rw [show κ₁ u - κ₁ u' = κ₁ (u - u') from (map_sub K₁ u u').symm,
      unSeminorm, unSeminorm, h₁]
  have htr₂ : ∀ (ω : NPFunctional ℬ) (u u' : Y),
      unSeminorm ω (inner ℬ : Z → Z → ℬ) (κ₂ u - κ₂ u')
        = unSeminorm ω (inner ℬ : Y → Y → ℬ) (u - u') := by
    intro ω u u'
    rw [show κ₂ u - κ₂ u' = κ₂ (u - u') from (map_sub K₂ u u').symm,
      unSeminorm, unSeminorm, h₂]
  -- the joint convergence statement used for both clauses of `IsONBasis`
  have hconv : ∀ (c : ι ⊕ κ → ℬ) (x : X) (y : Y),
      UnTendsto (inner ℬ) (fun t : Finset ι => ∑ i ∈ t, c (Sum.inl i) • e i) atTop x →
      UnTendsto (inner ℬ) (fun u : Finset κ => ∑ j ∈ u, c (Sum.inr j) • d j) atTop y →
      UnTendsto (inner ℬ)
        (fun s : Finset (ι ⊕ κ) => ∑ g ∈ s, c g • Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) g)
        atTop (κ₁ x + κ₂ y) := by
    intro c x y hx hy ω
    simp only [hsplit c]
    refine squeeze_zero (fun s => unSeminorm_nonneg _ _ _)
      (g := fun s : Finset (ι ⊕ κ) =>
        unSeminorm ω (inner ℬ : X → X → ℬ)
            ((∑ i ∈ s.toLeft, c (Sum.inl i) • e i) - x)
          + unSeminorm ω (inner ℬ : Y → Y → ℬ)
            ((∑ j ∈ s.toRight, c (Sum.inr j) • d j) - y)) (fun s => ?_) ?_
    · have hrw : κ₁ (∑ i ∈ s.toLeft, c (Sum.inl i) • e i)
            + κ₂ (∑ j ∈ s.toRight, c (Sum.inr j) • d j) - (κ₁ x + κ₂ y)
          = (κ₁ (∑ i ∈ s.toLeft, c (Sum.inl i) • e i) - κ₁ x)
            + (κ₂ (∑ j ∈ s.toRight, c (Sum.inr j) • d j) - κ₂ y) := by abel
      rw [hrw, ← htr₁ ω _ x, ← htr₂ ω _ y]
      exact unSeminorm_add_le ω (cstarBInner ℬ Z) _ _
    · have hL := (hx ω).comp (tendsto_finset_toLeft_atTop (ι := ι) (κ := κ))
      have hR := (hy ω).comp (tendsto_finset_toRight_atTop (ι := ι) (κ := κ))
      simpa using hL.add hR
  -- orthonormality
  have hbasis : IsONBasis ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d)) := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rintro (i | j) (i' | j') hne
      · exact (h₁ _ _).trans (he.1.1 i i' (fun h => hne (by rw [h])))
      · exact h₁₂ _ _
      · exact h₂₁ _ _
      · exact (h₂ _ _).trans (hd.1.1 j j' (fun h => hne (by rw [h])))
    · rintro (i | j)
      · rw [show (inner ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) (Sum.inl i))
          (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) (Sum.inl i)) : ℬ) = inner ℬ (e i) (e i) from h₁ _ _]
        exact he.1.2 i
      · rw [show (inner ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) (Sum.inr j))
          (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) (Sum.inr j)) : ℬ) = inner ℬ (d j) (d j) from h₂ _ _]
        exact hd.1.2 j
    · intro z
      obtain ⟨x, y, rfl⟩ := hadd z
      have hcoefL : ∀ i : ι,
          (inner ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) (Sum.inl i)) (κ₁ x + κ₂ y) : ℬ)
            = inner ℬ (e i) x := by
        intro i
        change (inner ℬ (κ₁ (e i)) (κ₁ x + κ₂ y) : ℬ) = _
        rw [CStarModule.inner_add_right, h₁, h₁₂, add_zero]
      have hcoefR : ∀ j : κ,
          (inner ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) (Sum.inr j)) (κ₁ x + κ₂ y) : ℬ)
            = inner ℬ (d j) y := by
        intro j
        change (inner ℬ (κ₂ (d j)) (κ₁ x + κ₂ y) : ℬ) = _
        rw [CStarModule.inner_add_right, h₂, h₂₁, zero_add]
      refine hconv (fun g => inner ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) g) (κ₁ x + κ₂ y)) x y
        ?_ ?_
      · simpa only [hcoefL] using he.2.1 x
      · simpa only [hcoefR] using hd.2.1 y
    · rintro c ⟨M, hM⟩
      have hL : L2Summable ℬ (fun i => c (Sum.inl i)) := by
        refine ⟨M, fun t => ?_⟩
        have h := hM (t.map Function.Embedding.inl)
        rwa [Finset.sum_map] at h
      have hR : L2Summable ℬ (fun j => c (Sum.inr j)) := by
        refine ⟨M, fun t => ?_⟩
        have h := hM (t.map Function.Embedding.inr)
        rwa [Finset.sum_map] at h
      obtain ⟨x₀, hx₀⟩ := he.2.2 _ hL
      obtain ⟨y₀, hy₀⟩ := hd.2.2 _ hR
      exact ⟨κ₁ x₀ + κ₂ y₀, hconv c x₀ y₀ hx₀ hy₀⟩
  exact ⟨hbasis, selfDual_of_isONBasis hbasis⟩

variable (ℬ) in
/-- **160III** (dils.tex:4476, Definition): the **orthocomplement**
`V^⊥ = {x : ⟨x,v⟩ = 0 for all v ∈ V}` of a subset `V` of a Hilbert
C*-module. -/
def orthoCompl (V : Set X) : Set X :=
  {x : X | ∀ v ∈ V, inner ℬ x v = 0}

variable (ℬ) in
/-- The set of points ultranorm-approximable from `S` (the ultranorm
closure; auxiliary for **160IV**). -/
def unClosure (B : X → X → ℬ) (S : Set X) : Set X :=
  {x : X | ∀ (n : ℕ) (ωs : Fin n → NPFunctional ℬ) (ε : ℝ), 0 < ε →
    ∃ d ∈ S, ∀ i, unSeminorm (ωs i) B (x - d) ≤ ε}

variable (ℬ) in
/-- The ℬ-linear span of a subset of a Hilbert ℬ-module (auxiliary for
**160IV**). -/
def bSpan (V : Set X) : Set X :=
  {x : X | ∃ (n : ℕ) (c : Fin n → ℂ) (b : Fin n → ℬ) (v : Fin n → X),
    (∀ i, v i ∈ V) ∧ x = ∑ i, c i • b i • v i}

/-- **160IV** (`hilbmod-projthm`, dils.tex:4488, Proposition), part 1: for
a subset `V` of a self-dual Hilbert ℬ-module `X`, the orthocomplement
`V^⊥` is an ultranorm-closed ℬ-submodule of `X` (and hence so is
`V^⊥⊥`). -/
theorem hilbmod_projthm_1 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) (V : Set X) :
    (0 : X) ∈ orthoCompl ℬ V ∧
    (∀ x ∈ orthoCompl ℬ V, ∀ y ∈ orthoCompl ℬ V, x + y ∈ orthoCompl ℬ V) ∧
    (∀ (b : ℬ), ∀ x ∈ orthoCompl ℬ V, b • x ∈ orthoCompl ℬ V) ∧
    (∀ (c : ℂ), ∀ x ∈ orthoCompl ℬ V, c • x ∈ orthoCompl ℬ V) ∧
    unClosure ℬ (inner ℬ) (orthoCompl ℬ V) = orthoCompl ℬ V := by
  -- "It is easy to see `V^⊥` is a submodule of `X`" (dils.tex:4506)
  refine ⟨fun v _ => CStarModule.inner_zero_left, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy v hv
    rw [CStarModule.inner_add_left, hx v hv, hy v hv, add_zero]
  · intro b x hx v hv
    rw [CStarModule.inner_op_smul_left, hx v hv, zero_mul]
  · intro c x hx v hv
    rw [CStarModule.inner_smul_left_complex, hx v hv, smul_zero]
  -- "To show `V^⊥` is ultranorm closed … `⟨v, unlim xα⟩ = uslim ⟨v, xα⟩ = 0`"
  refine Set.eq_of_subset_of_subset (fun x hx v hv => ?_) (fun x hx n ωs ε hε => ?_)
  · -- every np-functional kills `⟨x,v⟩`, so it is `0` (**44XI**)
    refine np_separating _ fun ω => ?_
    set C : ℝ := unSeminorm ω (cstarBInner ℬ X).inner v with hCdef
    have hC : 0 ≤ C := unSeminorm_nonneg ω _ v
    -- `|ω⟨x,v⟩| = |ω⟨x−d,v⟩| ≤ ‖x−d‖_ω ‖v‖_ω ≤ ε C` for every `ε > 0`
    have key : ∀ ε : ℝ, 0 < ε → ‖ω (inner ℬ x v : ℬ)‖ ≤ ε * C := by
      intro ε hε
      obtain ⟨d, hd, hdist⟩ := hx 1 (fun _ => ω) ε hε
      have hsplit : (inner ℬ x v : ℬ) = inner ℬ (x - d) v := by
        rw [CStarModule.inner_sub_left, hd v hv, sub_zero]
      calc ‖ω (inner ℬ x v : ℬ)‖
          = ‖ω ((cstarBInner ℬ X).inner (x - d) v)‖ := by rw [hsplit]; rfl
        _ ≤ unSeminorm ω (cstarBInner ℬ X).inner (x - d) * C :=
            unSeminorm_inner_le ω (cstarBInner ℬ X) _ _
        _ ≤ ε * C := mul_le_mul_of_nonneg_right (hdist 0) hC
    have hzero : ‖ω (inner ℬ x v : ℬ)‖ ≤ 0 := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have h1 : δ / (C + 1) * C ≤ δ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith [key (δ / (C + 1)) (by positivity)]
    simpa using le_antisymm hzero (norm_nonneg _)
  · exact ⟨x, hx, fun i => by simpa [unSeminorm] using hε.le⟩

/-! ### Auxiliary for **160IV**.3: the orthonormalization, relativized

The thesis (160VI–160VIII) proves the decomposition by extending an
orthonormal basis of `W = V^⊥⊥` to a *maximal orthonormal subset of the
whole of `X`*, appealing to the construction inside **149VIII**
(`selfdual-bcompl-then-basis`) for the fact that this extension is possible.

**Divergence, class 2** (same argument, run one level down).  Rather than
extend a basis of `W` to a basis of `X`, we run **149VIII**'s Zorn argument
*inside* `W` directly: a maximal orthonormal `E ⊆ W` expands every `y ∈ X`
as `p = ∑ᵢ ⟨eᵢ,y⟩ • eᵢ` (which converges by
`exists_unTendsto_of_l2Summable`, i.e. Bessel plus norm-bounded ultranorm
completeness of `X`, and lies in `W` because `W` is an ultranorm-closed
submodule), leaving a remainder orthogonal to `E`; for `y ∈ W` maximality
forces that remainder to be `0`, because the polar decomposition of a
non-zero remainder would extend `E` inside `W`.  So every `w ∈ W` *is* its
own expansion, and `x − p ⊥ E` gives `x − p ⊥ W`.  This needs no basis of
`X` at all, and hence neither 160IV.2 nor the "we can extend it to a
maximal orthonormal subset of `X`" step, which the thesis asserts by
pointing back into the proof of 149VIII.

The one thing 149VIII's proof does not hand over as stated is that the
isometric part of the polar decomposition of `y` stays inside a closed
submodule containing `y`; `polar_decomposition` (`HilbertModules.lean`) now
records it, as the third conjunct of its conclusion. -/

omit [StarOrderedRing ℬ] in
private theorem unSeminorm_neg_inner (ω : NPFunctional ℬ) (u : X) :
    unSeminorm ω (inner ℬ : X → X → ℬ) (-u)
      = unSeminorm ω (inner ℬ : X → X → ℬ) u := by
  have h : (inner ℬ (-u) (-u) : ℬ) = inner ℬ u u := by
    rw [show (-u) = ((-1 : ℂ)) • u by simp,
      CStarModule.inner_smul_right_complex, CStarModule.inner_smul_left_complex]
    simp
  rw [unSeminorm, unSeminorm, h]

/-- An ultranorm limit of a net (over a directed index) of points of `S`
lies in the ultranorm closure of `S`. -/
private theorem mem_unClosure_of_unTendsto {κ : Type*} [Nonempty κ]
    [SemilatticeSup κ] (S : Set X) (v : κ → X) (hv : ∀ k, v k ∈ S) (y : X)
    (h : UnTendsto (inner ℬ : X → X → ℬ) v atTop y) :
    y ∈ unClosure ℬ (inner ℬ) S := by
  intro n ωs ε hε
  have hall : ∀ᶠ k in atTop, ∀ i : Fin n,
      unSeminorm (ωs i) (inner ℬ : X → X → ℬ) (v k - y) ≤ ε := by
    rw [Filter.eventually_all]
    exact fun i => ((h (ωs i)).eventually_lt_const hε).mono fun k hk => hk.le
  obtain ⟨k, hk⟩ := hall.exists
  refine ⟨v k, hv k, fun i => ?_⟩
  have hneg := unSeminorm_neg_inner (X := X) (ωs i) (v k - y)
  rw [neg_sub] at hneg
  exact hneg ▸ hk i

/-! ### Auxiliary for **160IV**.2: the ultranorm closure of a submodule -/

private theorem subset_unClosure (S : Set X) : S ⊆ unClosure ℬ (inner ℬ) S :=
  fun x hx _ _ ε hε => ⟨x, hx, fun i => by simpa [unSeminorm] using hε.le⟩

private theorem unClosure_mono {S T : Set X} (h : S ⊆ T) :
    unClosure ℬ (inner ℬ) S ⊆ unClosure ℬ (inner ℬ) T := by
  intro x hx n ωs ε hε
  obtain ⟨d, hd, hdist⟩ := hx n ωs ε hε
  exact ⟨d, h hd, hdist⟩

private theorem unClosure_unClosure (S : Set X) :
    unClosure ℬ (inner ℬ) (unClosure ℬ (inner ℬ) S) = unClosure ℬ (inner ℬ) S := by
  refine Set.eq_of_subset_of_subset (fun x hx n ωs ε hε => ?_)
    (subset_unClosure _)
  obtain ⟨d, hd, h1⟩ := hx n ωs (ε / 2) (by linarith)
  obtain ⟨d', hd', h2⟩ := hd n ωs (ε / 2) (by linarith)
  refine ⟨d', hd', fun i => ?_⟩
  have hsplit : x - d' = (x - d) + (d - d') := by abel
  calc unSeminorm (ωs i) (inner ℬ : X → X → ℬ) (x - d')
      = unSeminorm (ωs i) (inner ℬ : X → X → ℬ) ((x - d) + (d - d')) := by
        rw [hsplit]
    _ ≤ unSeminorm (ωs i) (inner ℬ : X → X → ℬ) (x - d)
        + unSeminorm (ωs i) (inner ℬ : X → X → ℬ) (d - d') :=
        unSeminorm_add_le _ (cstarBInner ℬ X) _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (h1 i) (h2 i)
    _ = ε := by ring

private theorem unClosure_add {S : Set X}
    (hS : ∀ y ∈ S, ∀ z ∈ S, y + z ∈ S) {y z : X}
    (hy : y ∈ unClosure ℬ (inner ℬ) S) (hz : z ∈ unClosure ℬ (inner ℬ) S) :
    y + z ∈ unClosure ℬ (inner ℬ) S := by
  intro n ωs ε hε
  obtain ⟨d, hd, h1⟩ := hy n ωs (ε / 2) (by linarith)
  obtain ⟨d', hd', h2⟩ := hz n ωs (ε / 2) (by linarith)
  refine ⟨d + d', hS d hd d' hd', fun i => ?_⟩
  have hsplit : y + z - (d + d') = (y - d) + (z - d') := by abel
  calc unSeminorm (ωs i) (inner ℬ : X → X → ℬ) (y + z - (d + d'))
      = unSeminorm (ωs i) (inner ℬ : X → X → ℬ) ((y - d) + (z - d')) := by
        rw [hsplit]
    _ ≤ unSeminorm (ωs i) (inner ℬ : X → X → ℬ) (y - d)
        + unSeminorm (ωs i) (inner ℬ : X → X → ℬ) (z - d') :=
        unSeminorm_add_le _ (cstarBInner ℬ X) _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (h1 i) (h2 i)
    _ = ε := by ring

private theorem unClosure_neg {S : Set X} (hS : ∀ y ∈ S, -y ∈ S) {y : X}
    (hy : y ∈ unClosure ℬ (inner ℬ) S) : -y ∈ unClosure ℬ (inner ℬ) S := by
  intro n ωs ε hε
  obtain ⟨d, hd, h1⟩ := hy n ωs ε hε
  refine ⟨-d, hS d hd, fun i => ?_⟩
  have h : -y - -d = -(y - d) := by abel
  rw [h, unSeminorm_neg_inner]
  exact h1 i

/-- `‖b·z‖_ω = ‖z‖_{ω(b*·b)}`: the ultranorm seminorms are permuted by the
ℬ-action, which is why the ultranorm closure of a submodule is one. -/
private theorem unSeminorm_op_smul_inner [VonNeumannAlgebra ℬ] (ω : NPFunctional ℬ)
    (b : ℬ) (z : X) :
    unSeminorm ω (inner ℬ : X → X → ℬ) (b • z)
      = unSeminorm (conjNP (star b) ω) (inner ℬ : X → X → ℬ) z := by
  have h : (inner ℬ (b • z) (b • z) : ℬ) = star (star b) * (inner ℬ z z : ℬ) * star b := by
    rw [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
      star_star, mul_assoc]
  rw [unSeminorm, unSeminorm, h, conjNP_apply]

private theorem unClosure_op_smul [VonNeumannAlgebra ℬ] {S : Set X}
    (hS : ∀ b : ℬ, ∀ y ∈ S, b • y ∈ S) (b : ℬ) {y : X}
    (hy : y ∈ unClosure ℬ (inner ℬ) S) : b • y ∈ unClosure ℬ (inner ℬ) S := by
  intro n ωs ε hε
  obtain ⟨d, hd, h1⟩ := hy n (fun i => conjNP (star b) (ωs i)) ε hε
  refine ⟨b • d, hS b d hd, fun i => ?_⟩
  have hsub : b • y - b • d = b • (y - d) := by
    have h : b • (y - d) + b • d = b • y := by
      rw [← op_smul_add]
      congr 1
      abel
    rw [← h]
    abel
  rw [hsub, unSeminorm_op_smul_inner]
  exact h1 i

/-! ### Auxiliary for **160IV**.2: the ℬ-linear span -/

private theorem op_smul_sum {κ : Type*} (a : ℬ) (s : Finset κ) (f : κ → X) :
    a • (∑ i ∈ s, f i) = ∑ i ∈ s, a • f i := by
  classical
  refine Finset.induction_on s (by simp [op_smul_zero]) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, op_smul_add, ih, Finset.sum_insert hi]

private theorem subset_bSpan (V : Set X) : V ⊆ bSpan ℬ V := by
  intro v hv
  exact ⟨1, fun _ => 1, fun _ => 1, fun _ => v, fun _ => hv, by
    simp [op_one_smul]⟩

private theorem zero_mem_bSpan (V : Set X) : (0 : X) ∈ bSpan ℬ V :=
  ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
    by simp⟩

private theorem bSpan_add (V : Set X) : ∀ y ∈ bSpan ℬ V, ∀ z ∈ bSpan ℬ V,
    y + z ∈ bSpan ℬ V := by
  rintro y ⟨n, c, b, v, hv, rfl⟩ z ⟨m, c', b', v', hv', rfl⟩
  refine ⟨n + m, Fin.append c c', Fin.append b b', Fin.append v v', ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact hv j
    · rw [Fin.append_right]; exact hv' j
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

private theorem bSpan_neg (V : Set X) : ∀ y ∈ bSpan ℬ V, -y ∈ bSpan ℬ V := by
  rintro y ⟨n, c, b, v, hv, rfl⟩
  exact ⟨n, fun i => -c i, b, v, hv, by simp [neg_smul]⟩

private theorem bSpan_op_smul (V : Set X) : ∀ a : ℬ, ∀ y ∈ bSpan ℬ V,
    a • y ∈ bSpan ℬ V := by
  rintro a y ⟨n, c, b, v, hv, rfl⟩
  refine ⟨n, c, fun i => a * b i, v, hv, ?_⟩
  rw [op_smul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [op_smul_comm_complex, op_mul_smul]


/-- The **projection theorem** for an ultranorm-closed submodule of the form
`U^⊥`: every `x ∈ X` splits as `p + (x − p)` with `p ∈ U^⊥` and `x − p`
orthogonal to all of `U^⊥`.  This is the substance of **160IV**.3. -/
private theorem exists_orthogonal_decomp [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) (W : Set X) (hW0 : (0 : X) ∈ W)
    (hWadd : ∀ y ∈ W, ∀ z ∈ W, y + z ∈ W)
    (hWb : ∀ b : ℬ, ∀ y ∈ W, b • y ∈ W) (hWneg : ∀ y ∈ W, -y ∈ W)
    (hWcl : unClosure ℬ (inner ℬ) W = W) (x : X) :
    ∃ p ∈ W, ∀ w ∈ W, (inner ℬ (x - p) w : ℬ) = 0 := by
  classical
  have hWsub : ∀ y ∈ W, ∀ z ∈ W, y - z ∈ W := fun y hy z hz => by
    rw [sub_eq_add_neg]; exact hWadd y hy (-z) (hWneg z hz)
  have hbdd : BddUnComplete ℬ X := bddUnComplete_of_selfDual hX
  -- a maximal orthonormal subset **of `W`**
  obtain ⟨E, hEmax⟩ := zorn_subset
    {E : Set X | E ⊆ W ∧ (∀ y ∈ E, ∀ z ∈ E, y ≠ z → (inner ℬ y z : ℬ) = 0)
      ∧ ∀ y ∈ E, IsStarProjection (inner ℬ y y : ℬ) ∧ (inner ℬ y y : ℬ) ≠ 0}
    (fun c hc hchain => by
      refine ⟨⋃₀ c, ⟨?_, ?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
      · rintro y ⟨s, hs, hys⟩
        exact (hc hs).1 hys
      · rintro y ⟨s₁, hs₁, hys₁⟩ z ⟨s₂, hs₂, hzs₂⟩ hyz
        rcases hchain.total hs₁ hs₂ with h12 | h21
        · exact (hc hs₂).2.1 y (h12 hys₁) z hzs₂ hyz
        · exact (hc hs₁).2.1 y hys₁ z (h21 hzs₂) hyz
      · rintro y ⟨s₁, hs₁, hys₁⟩
        exact (hc hs₁).2.2 y hys₁)
  have hE := hEmax.1
  have hEW : E ⊆ W := hE.1
  have horth : OrthonormalFam ℬ (fun i : E => (i : X)) :=
    ⟨fun i j hij => hE.2.1 (i : X) i.2 (j : X) j.2 fun hh => hij (Subtype.ext hh),
      fun i => hE.2.2 (i : X) i.2⟩
  -- finite ℬ-combinations of members of `E` lie in `W`
  have hWsum : ∀ (b : ↥E → ℬ) (s : Finset ↥E),
      (∑ i ∈ s, b i • (i : X)) ∈ W := by
    intro b s
    refine Finset.induction_on s (by simpa using hW0) ?_
    intro i s hi ih
    rw [Finset.sum_insert hi]
    exact hWadd _ (hWb (b i) (i : X) (hEW i.2)) _ ih
  -- every `y ∈ X` has an expansion along `E` inside `W`
  have hexp : ∀ y : X, ∃ p : X, p ∈ W ∧
      UnTendsto (inner ℬ : X → X → ℬ)
        (fun s : Finset ↥E => ∑ i ∈ s, (inner ℬ ((i : X)) y : ℬ) • (i : X))
        atTop p ∧
      ∀ j : ↥E, (inner ℬ ((j : X)) (y - p) : ℬ) = 0 := by
    intro y
    have hL2 : L2Summable ℬ (fun i : ↥E => (inner ℬ ((i : X)) y : ℬ)) := by
      refine ⟨‖(inner ℬ y y : ℬ)‖, fun s => ?_⟩
      have h1 : ∑ i ∈ s,
            (inner ℬ ((i : X)) y : ℬ) * star (inner ℬ ((i : X)) y : ℬ)
          = ∑ i ∈ s, (inner ℬ ((i : X)) y : ℬ) * (inner ℬ y ((i : X)) : ℬ) :=
        Finset.sum_congr rfl fun i _ => by rw [CStarModule.star_inner]
      rw [h1]
      have h3 : (0 : ℬ) ≤ ∑ i ∈ s,
          (inner ℬ ((i : X)) y : ℬ) * (inner ℬ y ((i : X)) : ℬ) := by
        rw [← h1]
        exact Finset.sum_nonneg fun i _ => mul_star_self_nonneg _
      exact CStarAlgebra.norm_le_norm_of_nonneg_of_le h3 (mod_bessel horth y s)
    obtain ⟨p, hp⟩ := exists_unTendsto_of_l2Summable hbdd horth _ hL2
    refine ⟨p, hWcl ▸ mem_unClosure_of_unTendsto W _ (fun s => hWsum _ s) p hp,
      hp, fun j => ?_⟩
    rw [CStarModule.inner_sub_right, inner_of_unTendsto_sum_smul horth _
      (fun i => onbasis_coef_absorb horth y i) hp j, sub_self]
  -- maximality: an element of `W` orthogonal to `E` is `0`
  have hmax0 : ∀ z ∈ W, (∀ j : ↥E, (inner ℬ ((j : X)) z : ℬ) = 0) → z = 0 := by
    intro z hzW hzo
    by_contra hne
    obtain ⟨u, huu, hbu, cc, hcc⟩ := polar_decomposition hbdd z
    have huW : u ∈ W := hWcl ▸ mem_unClosure_of_unTendsto W (fun N => cc N • z)
      (fun N => hWb (cc N) z hzW) u hcc
    have hzz : (inner ℬ z z : ℬ) ≠ 0 := fun h0 =>
      hne ((CStarModule.inner_self (A := ℬ)).mp h0)
    have hbne : CFC.sqrt (inner ℬ z z : ℬ) ≠ 0 := by
      intro h0
      refine hzz ?_
      rw [← CFC.sqrt_mul_sqrt_self (inner ℬ z z : ℬ)
        CStarModule.inner_self_nonneg, h0, mul_zero]
    have hqproj : IsStarProjection (inner ℬ u u : ℬ) := by
      rw [huu]; exact (ceill_basic_1 _).1.1
    have hqne : (inner ℬ u u : ℬ) ≠ 0 := by
      rw [huu]
      intro h0
      have h1 := (ceill_basic_1 (CFC.sqrt (inner ℬ z z : ℬ))).1.2
      rw [h0, mul_zero] at h1
      exact hbne h1.symm
    have horthu : ∀ j : ↥E, (inner ℬ ((j : X)) u : ℬ) = 0 := fun j =>
      inner_eq_zero_of_polar huu hbu (hzo j)
    have huE : u ∉ E := fun h => hqne (horthu ⟨u, h⟩)
    have hEu : (insert u E) ∈ {E' : Set X | E' ⊆ W ∧
        (∀ y ∈ E', ∀ z ∈ E', y ≠ z → (inner ℬ y z : ℬ) = 0)
        ∧ ∀ y ∈ E', IsStarProjection (inner ℬ y y : ℬ)
          ∧ (inner ℬ y y : ℬ) ≠ 0} := by
      refine ⟨?_, ?_, ?_⟩
      · rintro y (rfl | hy)
        · exact huW
        · exact hEW hy
      · rintro y (rfl | hy) z (rfl | hz) hne'
        · exact absurd rfl hne'
        · have h5 := congrArg star (horthu ⟨z, hz⟩)
          rwa [CStarModule.star_inner, star_zero] at h5
        · exact horthu ⟨y, hy⟩
        · exact hE.2.1 y hy z hz hne'
      · rintro y (rfl | hy)
        · exact ⟨hqproj, hqne⟩
        · exact hE.2.2 y hy
    exact huE (hEmax.2 hEu (Set.subset_insert u E) (Set.mem_insert u E))
  -- the decomposition
  obtain ⟨p, hpW, -, hpo⟩ := hexp x
  refine ⟨p, hpW, fun w hw => ?_⟩
  obtain ⟨q, hqW, hq, hqo⟩ := hexp w
  have hwq : q = w := by
    have h0 := hmax0 (w - q) (hWsub w hw q hqW) hqo
    rw [sub_eq_zero] at h0
    exact h0.symm
  rw [hwq] at hq
  -- `x − p` kills every partial sum of `w`'s expansion …
  have hzero : ∀ s : Finset ↥E,
      (inner ℬ (x - p)
        (∑ i ∈ s, (inner ℬ ((i : X)) w : ℬ) • (i : X)) : ℬ) = 0 := by
    intro s
    rw [CStarModule.inner_sum_right]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [CStarModule.inner_op_smul_right]
    have h1 : (inner ℬ (x - p) ((i : X)) : ℬ) = 0 := by
      have h2 := congrArg star (hpo i)
      rwa [CStarModule.star_inner, star_zero] at h2
    rw [h1, mul_zero]
  -- … so `ω⟨x−p,w⟩ = ω⟨x−p, w − ∑…⟩ → 0` for every np-functional `ω`
  refine np_separating _ fun ω => ?_
  set C : ℝ := unSeminorm ω (cstarBInner ℬ X).inner (x - p) with hCdef
  have hbound : ∀ s : Finset ↥E, ‖ω (inner ℬ (x - p) w : ℬ)‖
      ≤ C * unSeminorm ω (cstarBInner ℬ X).inner
          ((∑ i ∈ s, (inner ℬ ((i : X)) w : ℬ) • (i : X)) - w) := by
    intro s
    have hsplit : (inner ℬ (x - p) w : ℬ)
        = inner ℬ (x - p) (w - ∑ i ∈ s, (inner ℬ ((i : X)) w : ℬ) • (i : X)) := by
      rw [CStarModule.inner_sub_right, hzero s, sub_zero]
    have hneg := unSeminorm_neg_inner (X := X) ω
      ((∑ i ∈ s, (inner ℬ ((i : X)) w : ℬ) • (i : X)) - w)
    rw [neg_sub] at hneg
    calc ‖ω (inner ℬ (x - p) w : ℬ)‖
        = ‖ω ((cstarBInner ℬ X).inner (x - p)
            (w - ∑ i ∈ s, (inner ℬ ((i : X)) w : ℬ) • (i : X)))‖ := by
          rw [hsplit]; rfl
      _ ≤ C * unSeminorm ω (cstarBInner ℬ X).inner
            (w - ∑ i ∈ s, (inner ℬ ((i : X)) w : ℬ) • (i : X)) :=
          unSeminorm_inner_le ω (cstarBInner ℬ X) _ _
      _ = C * unSeminorm ω (cstarBInner ℬ X).inner
            ((∑ i ∈ s, (inner ℬ ((i : X)) w : ℬ) • (i : X)) - w) :=
          congrArg (fun t => C * t) hneg
  have hlim : Tendsto (fun s : Finset ↥E => C * unSeminorm ω
      (cstarBInner ℬ X).inner
        ((∑ i ∈ s, (inner ℬ ((i : X)) w : ℬ) • (i : X)) - w)) atTop (𝓝 0) := by
    have h := (hq ω).const_mul C
    rw [mul_zero] at h
    exact h
  have hle : ‖ω (inner ℬ (x - p) w : ℬ)‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  simpa using le_antisymm hle (norm_nonneg _)

/-- **160IV** (`hilbmod-projthm`, dils.tex:4488, Proposition), part 2:
`V^⊥⊥` is the ultranorm closure of the ℬ-linear span of `V`.

**Divergence, class 2.**  The thesis proves 2 and 3 together, in the order
3-then-2: it takes an orthonormal basis `(eᵢ)` of `W` (the ultranorm closure
of the span), *extends it to a basis of `X`*, and reads off
`V^⊥⊥ ⊆ W` from the expansion of an `x ∈ V^⊥⊥` along that extended basis.
Here the inclusion comes from the same relativized decomposition that
proves part 3: `x = p + (x−p)` with `p ∈ W` and `x − p ⊥ W`, so
`x − p ∈ V^⊥` (as `V ⊆ W`) and `x − p ∈ V^⊥⊥` (as `x, p ∈ V^⊥⊥`), whence
`x − p = 0`.  The other inclusion is the thesis's own "`W ⊆ V^⊥⊥`":
`V^⊥⊥` is an ultranorm-closed submodule containing `V` (part 1). -/
theorem hilbmod_projthm_2 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) (V : Set X) :
    orthoCompl ℬ (orthoCompl ℬ V) = unClosure ℬ (inner ℬ) (bSpan ℬ V) := by
  classical
  obtain ⟨hW0, hWadd, hWb, hWc, hWcl⟩ := hilbmod_projthm_1 hX (orthoCompl ℬ V)
  have hVV : V ⊆ orthoCompl ℬ (orthoCompl ℬ V) := by
    intro v hv y hy
    have h := congrArg star (hy v hv)
    rwa [CStarModule.star_inner, star_zero] at h
  have hspan : bSpan ℬ V ⊆ orthoCompl ℬ (orthoCompl ℬ V) := by
    rintro y ⟨n, c, b, v, hv, rfl⟩
    refine Finset.sum_induction _ (fun z => z ∈ orthoCompl ℬ (orthoCompl ℬ V))
      (fun z z' hz hz' => hWadd z hz z' hz') hW0 (fun i _ => ?_)
    exact hWc (c i) _ (hWb (b i) _ (hVV (hv i)))
  refine Set.eq_of_subset_of_subset (fun x hx => ?_) ?_
  · obtain ⟨p, hpW, horth⟩ := exists_orthogonal_decomp hX
      (unClosure ℬ (inner ℬ) (bSpan ℬ V))
      (subset_unClosure _ (zero_mem_bSpan V))
      (fun y hy z hz => unClosure_add (bSpan_add V) hy hz)
      (fun a y hy => unClosure_op_smul (bSpan_op_smul V) a hy)
      (fun y hy => unClosure_neg (bSpan_neg V) hy)
      (unClosure_unClosure _) x
    have hpV : p ∈ orthoCompl ℬ (orthoCompl ℬ V) :=
      hWcl ▸ unClosure_mono hspan hpW
    have h1 : x - p ∈ orthoCompl ℬ V := fun v hv =>
      horth v (subset_unClosure _ (subset_bSpan V hv))
    have h2 : x - p ∈ orthoCompl ℬ (orthoCompl ℬ V) := by
      intro w hw
      rw [CStarModule.inner_sub_left, hx w hw, hpV w hw, sub_zero]
    have h0 : x - p = 0 := (CStarModule.inner_self (A := ℬ)).mp (h2 (x - p) h1)
    rw [sub_eq_zero] at h0
    rw [h0]
    exact hpW
  · calc unClosure ℬ (inner ℬ) (bSpan ℬ V)
        ⊆ unClosure ℬ (inner ℬ) (orthoCompl ℬ (orthoCompl ℬ V)) :=
        unClosure_mono hspan
      _ = orthoCompl ℬ (orthoCompl ℬ V) := hWcl

/-- **160IV** (`hilbmod-projthm`, dils.tex:4488, Proposition), part 3:
`V^⊥⊥ ⊕ V^⊥ ≅ X` via `(x,y) ↦ x + y`: every element of `X` decomposes
uniquely as a sum of an element of `V^⊥⊥` and one of `V^⊥`.

**160V**–**160VIII** are the proof.  Existence is
`exists_orthogonal_decomp` above (see its doc comment for the divergence:
the orthonormalization is run inside `V^⊥⊥` rather than extended to a basis
of `X`, which needs neither 160IV.2 nor a basis of `X`).  Uniqueness is the
thesis's "`ϑ` is inner product preserving and thus injective", in the
sharper form `V^⊥⊥ ∩ V^⊥ = {0}`: a `z` in both has `⟨z,z⟩ = 0`. -/
theorem hilbmod_projthm_3 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) (V : Set X) (x : X) :
    ∃! p : X × X, p.1 ∈ orthoCompl ℬ (orthoCompl ℬ V) ∧
      p.2 ∈ orthoCompl ℬ V ∧ x = p.1 + p.2 := by
  -- `V ⊆ V^⊥⊥`, so `(V^⊥)^⊥ ⊆ V^⊥`
  have hVV : V ⊆ orthoCompl ℬ (orthoCompl ℬ V) := by
    intro v hv y hy
    have h := congrArg star (hy v hv)
    rwa [CStarModule.star_inner, star_zero] at h
  -- an element of both `V^⊥⊥` and `V^⊥` is zero
  have hinter : ∀ z : X, z ∈ orthoCompl ℬ (orthoCompl ℬ V) →
      z ∈ orthoCompl ℬ V → z = 0 := fun z hz₁ hz₂ =>
    (CStarModule.inner_self (A := ℬ)).mp (hz₁ z hz₂)
  obtain ⟨hW0, hWadd, hWb, hWc, hWcl⟩ := hilbmod_projthm_1 hX (orthoCompl ℬ V)
  obtain ⟨p, hp, horth⟩ := exists_orthogonal_decomp hX _ hW0 hWadd hWb
    (fun y hy => by
      have h := hWc (-1 : ℂ) y hy
      rwa [neg_one_smul] at h) hWcl x
  refine ⟨(p, x - p), ⟨hp, fun v hv => horth v (hVV hv), by simp⟩, ?_⟩
  rintro ⟨y, z⟩ ⟨hy, hz, hyz⟩
  have hsum : y + z = p + (x - p) := by rw [← hyz]; abel
  have hd : p - y = z - (x - p) := by
    calc p - y = (p + (x - p)) - (x - p) - y := by abel
      _ = (y + z) - (x - p) - y := by rw [hsum]
      _ = z - (x - p) := by abel
  have h1 : p - y ∈ orthoCompl ℬ (orthoCompl ℬ V) := by
    intro v hv
    rw [CStarModule.inner_sub_left, hp v hv, hy v hv, sub_zero]
  have h2 : p - y ∈ orthoCompl ℬ V := by
    rw [hd]
    intro v hv
    rw [CStarModule.inner_sub_left, hz v hv, horth v (hVV hv), sub_zero]
  have h0 : p - y = 0 := hinter _ h1 h2
  have hyp : y = p := (sub_eq_zero.mp h0).symm
  have hzp : z = x - p := by
    have h3 : z - (x - p) = 0 := by rw [← hd, h0]
    exact sub_eq_zero.mp h3
  rw [hyp, hzp]

/-- Uniqueness of ultraweak limits (**44XI**.1, `vn_positive_basic_1`); the
same three-line helper as in `HilbertModules.lean`, which keeps it
`private`. -/
private theorem uwTendsto_unique₂ [VonNeumannAlgebra ℬ] {κ : Type*}
    {l : Filter κ} [l.NeBot] {f : κ → ℬ} {a c : ℬ} (ha : UWTendsto f l a)
    (hc : UWTendsto f l c) : a = c :=
  @tendsto_nhds_unique ℬ κ (ultraweak ℬ) (vn_positive_basic_1 (A := ℬ)).1
    f l a c _ ha hc

/-- **160IX** (`selfdual-orthn-basis`, dils.tex:4565, Exercise): for an
orthonormal family `(eᵢ)` in a self-dual Hilbert ℬ-module: (1) `(eᵢ)` is a
basis of `E^⊥⊥` (every `x ∈ E^⊥⊥` is the ultranorm limit of its basis
expansion); (2) `x ∈ E^⊥⊥` iff `⟨x,x⟩ = ∑ᵢ ⟨x,eᵢ⟩⟨eᵢ,x⟩` (mirrored).

Both parts run off the same three facts, and neither needs a basis of `X`:
the expansion `p = ∑ᵢ ⟨eᵢ,x⟩ • eᵢ` converges by Bessel plus
`exists_unTendsto_of_l2Summable`, it lies in the ultranorm-closed submodule
`E^⊥⊥` (**160IV**.1), and `x − p ⊥ eᵢ` for every `i`
(`inner_of_unTendsto_sum_smul`), so `x − p ∈ E^⊥`.  For (1) and for the `⇐`
of (2) one then intersects: `E^⊥⊥ ∩ E^⊥ = {0}` because `z` in both has
`⟨z,z⟩ = 0`.  The `⇒` of (2) is Parseval for the partial sums, read off
ultraweakly through `innerprod_ultraweak`; the `⇐` computes
`⟨x−p,x−p⟩ = ⟨x,x⟩ − ⟨x,p⟩ − ⟨p,x⟩ + ⟨p,p⟩ = 0`, all four terms being the
same ultraweak limit. -/
theorem selfdual_orthn_basis [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) {ι : Type v} (e : ι → X)
    (he : OrthonormalFam ℬ e) (x : X) :
    (x ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) →
      UnTendsto (inner ℬ)
        (fun s : Finset ι => ∑ i ∈ s, inner ℬ (e i) x • e i) atTop x) ∧
    (x ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) ↔
      UWTendsto
        (fun s : Finset ι => ∑ i ∈ s, inner ℬ (e i) x * inner ℬ x (e i))
        atTop (inner ℬ x x)) := by
  classical
  obtain ⟨hW0, hWadd, hWb, hWc, hWcl⟩ :=
    hilbmod_projthm_1 hX (orthoCompl ℬ (Set.range e))
  have hbdd : BddUnComplete ℬ X := bddUnComplete_of_selfDual hX
  have hWsub : ∀ y ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)),
      ∀ z ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)),
      y - z ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) := by
    intro y hy z hz
    have hneg : -z ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) := by
      have h := hWc (-1 : ℂ) z hz
      rwa [neg_one_smul] at h
    rw [sub_eq_add_neg]
    exact hWadd y hy (-z) hneg
  -- `E^⊥⊥ ∩ E^⊥ = {0}`
  have hinter : ∀ z : X, z ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) →
      z ∈ orthoCompl ℬ (Set.range e) → z = 0 :=
    fun z hz₁ hz₂ => (CStarModule.inner_self (A := ℬ)).mp (hz₁ z hz₂)
  -- each `eᵢ` lies in `E^⊥⊥`
  have heW : ∀ i, e i ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) := by
    intro i v hv
    have h := congrArg star (hv (e i) ⟨i, rfl⟩)
    rwa [CStarModule.star_inner, star_zero] at h
  -- Bessel: the coefficients are ℓ²-summable, so the expansion converges
  have hL2 : L2Summable ℬ (fun i => (inner ℬ (e i) x : ℬ)) := by
    refine ⟨‖(inner ℬ x x : ℬ)‖, fun s => ?_⟩
    have h1 : ∑ i ∈ s, (inner ℬ (e i) x : ℬ) * star (inner ℬ (e i) x : ℬ)
        = ∑ i ∈ s, (inner ℬ (e i) x : ℬ) * (inner ℬ x (e i) : ℬ) :=
      Finset.sum_congr rfl fun i _ => by rw [CStarModule.star_inner]
    rw [h1]
    have h3 : (0 : ℬ) ≤ ∑ i ∈ s,
        (inner ℬ (e i) x : ℬ) * (inner ℬ x (e i) : ℬ) := by
      rw [← h1]
      exact Finset.sum_nonneg fun i _ => mul_star_self_nonneg _
    exact CStarAlgebra.norm_le_norm_of_nonneg_of_le h3 (mod_bessel he x s)
  obtain ⟨p, hp⟩ := exists_unTendsto_of_l2Summable hbdd he _ hL2
  -- the limit lies in `E^⊥⊥` …
  have hWsum : ∀ s : Finset ι,
      (∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i)
        ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) := by
    intro s
    refine Finset.induction_on s (by simpa using hW0) ?_
    intro i s hi ih
    rw [Finset.sum_insert hi]
    exact hWadd _ (hWb _ (e i) (heW i)) _ ih
  have hpW : p ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) :=
    hWcl ▸ mem_unClosure_of_unTendsto _ _ hWsum p hp
  -- … and `x − p` is orthogonal to every `eᵢ`
  have hpo : ∀ j : ι, (inner ℬ (e j) (x - p) : ℬ) = 0 := by
    intro j
    rw [CStarModule.inner_sub_right, inner_of_unTendsto_sum_smul he _
      (fun i => onbasis_coef_absorb he x i) hp j, sub_self]
  have hpE : x - p ∈ orthoCompl ℬ (Set.range e) := by
    rintro w ⟨j, rfl⟩
    have h := congrArg star (hpo j)
    rwa [CStarModule.star_inner, star_zero] at h
  -- the Gram sums of the partial sums are the Parseval sums
  have hgram : ∀ s : Finset ι,
      (inner ℬ (∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i)
        (∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i) : ℬ)
      = ∑ i ∈ s, (inner ℬ (e i) x : ℬ) * inner ℬ x (e i) := by
    intro s
    rw [inner_sum_smul_self he.1 _ (fun i => onbasis_coef_absorb he x i) s]
    exact Finset.sum_congr rfl fun i _ => by rw [CStarModule.star_inner]
  have hconst : UnTendsto (inner ℬ : X → X → ℬ)
      (fun _ : Finset ι => x) atTop x := by
    intro ω
    simp only [sub_self]
    have h0 : (inner ℬ (0 : X) (0 : X) : ℬ) = 0 :=
      (cstarBInner ℬ X).inner_zero_left 0
    simp [unSeminorm, h0]
  have hpart1 : x ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) → x = p := by
    intro hxW
    have h0 : x - p = 0 := hinter _ (hWsub x hxW p hpW) hpE
    rwa [sub_eq_zero] at h0
  refine ⟨fun hxW => ?_, fun hxW => ?_, fun hpars => ?_⟩
  · have hxp := hpart1 hxW
    subst hxp
    exact hp
  · have h := innerprod_ultraweak (cstarBInner ℬ X)
      (fun s : Finset ι => ∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i)
      (fun s : Finset ι => ∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i) p p hp hp
    rw [← hpart1 hxW] at h
    simpa only [show (cstarBInner ℬ X).inner = (inner ℬ : X → X → ℬ) from rfl,
      hgram] using h
  · -- `⇐`: Parseval forces `⟨x−p,x−p⟩ = 0`
    have hxp : (inner ℬ x p : ℬ) = inner ℬ x x := by
      have h1 : UWTendsto (fun s : Finset ι =>
          (inner ℬ x (∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i) : ℬ)) atTop
          (inner ℬ x p) :=
        innerprod_ultraweak (cstarBInner ℬ X) (fun _ => x)
          (fun s : Finset ι => ∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i) x p hconst hp
      have h2 : ∀ s : Finset ι,
          (inner ℬ x (∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i) : ℬ)
            = ∑ i ∈ s, (inner ℬ (e i) x : ℬ) * inner ℬ x (e i) := by
        intro s
        rw [CStarModule.inner_sum_right]
        exact Finset.sum_congr rfl fun i _ => CStarModule.inner_op_smul_right
      simp only [h2] at h1
      exact uwTendsto_unique₂ h1 hpars
    have hpx : (inner ℬ p x : ℬ) = inner ℬ x x := by
      have h := congrArg star hxp
      rwa [CStarModule.star_inner, CStarModule.star_inner] at h
    have hpp : (inner ℬ p p : ℬ) = inner ℬ x x := by
      have h1 := innerprod_ultraweak (cstarBInner ℬ X)
        (fun s : Finset ι => ∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i)
        (fun s : Finset ι => ∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i) p p hp hp
      simp only [show (cstarBInner ℬ X).inner = (inner ℬ : X → X → ℬ) from rfl,
        hgram] at h1
      exact uwTendsto_unique₂ h1 hpars
    have hz : (inner ℬ (x - p) (x - p) : ℬ) = 0 := by
      rw [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
        CStarModule.inner_sub_right, hxp, hpx, hpp]
      abel
    have hxp0 : x = p := by
      have h := (CStarModule.inner_self (A := ℬ)).mp hz
      rwa [sub_eq_zero] at h
    rw [hxp0]
    exact hpW

private theorem subset_biorthoCompl (V : Set X) :
    V ⊆ orthoCompl ℬ (orthoCompl ℬ V) := by
  intro v hv y hy
  have h := congrArg star (hy v hv)
  rwa [CStarModule.star_inner, star_zero] at h

private theorem biorthoCompl_mono {S T : Set X} (h : S ⊆ T) :
    orthoCompl ℬ (orthoCompl ℬ S) ⊆ orthoCompl ℬ (orthoCompl ℬ T) :=
  fun _ hz v hv => hz v fun w hw => hv w (h hw)

/-- The **orthogonal projection** onto an ultranorm-closed submodule `W` of
a self-dual Hilbert ℬ-module: the first component of the decomposition of
`exists_orthogonal_decomp` is a bounded module map fixing `W`.  (Everything
here is uniqueness of that decomposition, which holds because
`W ∩ W^⊥ = {0}`.)  This is the thesis's `ϑ` of 160VIII read as an
idempotent on `X`; it is what turns a universal property into density —
see `selfdual_compl_defining_dense`. -/
private theorem exists_orthoProj [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) (W : Set X) (hW0 : (0 : X) ∈ W)
    (hWadd : ∀ y ∈ W, ∀ z ∈ W, y + z ∈ W)
    (hWb : ∀ b : ℬ, ∀ y ∈ W, b • y ∈ W)
    (hWc : ∀ c : ℂ, ∀ y ∈ W, c • y ∈ W)
    (hWcl : unClosure ℬ (inner ℬ) W = W) :
    ∃ P : X → X,
      IsBoundedModuleMap (cstarBInner ℬ X) (cstarBInner ℬ X) 1 P ∧
      (∀ x, P x ∈ W) ∧ ∀ w ∈ W, P w = w := by
  classical
  have hWneg : ∀ y ∈ W, -y ∈ W := fun y hy => by
    have h := hWc (-1 : ℂ) y hy
    rwa [neg_one_smul] at h
  have hWsub : ∀ y ∈ W, ∀ z ∈ W, y - z ∈ W := fun y hy z hz => by
    rw [sub_eq_add_neg]; exact hWadd y hy (-z) (hWneg z hz)
  choose p hp horth using
    fun x => exists_orthogonal_decomp hX W hW0 hWadd hWb hWneg hWcl x
  -- uniqueness of the decomposition
  have huniq : ∀ (x q : X), q ∈ W → (∀ w ∈ W, (inner ℬ (x - q) w : ℬ) = 0) →
      p x = q := by
    intro x q hq hqo
    have hd : p x - q ∈ W := hWsub _ (hp x) _ hq
    have harg : p x - q = (x - q) - (x - p x) := by abel
    have h0 : (inner ℬ (p x - q) (p x - q) : ℬ) = 0 :=
      calc (inner ℬ (p x - q) (p x - q) : ℬ)
          = inner ℬ ((x - q) - (x - p x)) (p x - q) := by rw [← harg]
        _ = inner ℬ (x - q) (p x - q) - inner ℬ (x - p x) (p x - q) :=
            CStarModule.inner_sub_left
        _ = 0 := by rw [hqo _ hd, horth x _ hd, sub_zero]
    have := (CStarModule.inner_self (A := ℬ)).mp h0
    rwa [sub_eq_zero] at this
  refine ⟨p, ⟨fun x y => ?_, fun c x => ?_, fun b x => ?_, fun x => ?_⟩,
    hp, fun w hw => ?_⟩
  · refine huniq _ _ (hWadd _ (hp x) _ (hp y)) fun w hw => ?_
    have hrw : x + y - (p x + p y) = (x - p x) + (y - p y) := by abel
    rw [hrw, CStarModule.inner_add_left, horth x w hw, horth y w hw, add_zero]
  · refine huniq _ _ (hWc c _ (hp x)) fun w hw => ?_
    rw [← smul_sub, CStarModule.inner_smul_left_complex, horth x w hw, smul_zero]
  · refine huniq _ _ (hWb b _ (hp x)) fun w hw => ?_
    have hrw : b • x - b • p x = b • (x - p x) := by
      have h : b • (x - p x) + b • p x = b • x := by
        rw [← op_smul_add]
        congr 1
        abel
      rw [← h]
      abel
    rw [hrw, CStarModule.inner_op_smul_left, horth x w hw, zero_mul]
  · -- `⟨x,x⟩ = ⟨Px,Px⟩ + ⟨x−Px,x−Px⟩ ≥ ⟨Px,Px⟩`
    have h1 : (inner ℬ (p x) (x - p x) : ℬ) = 0 := by
      have h := congrArg star (horth x _ (hp x))
      rwa [CStarModule.star_inner, star_zero] at h
    have h2 : (inner ℬ x x : ℬ)
        = inner ℬ (p x) (p x) + inner ℬ (x - p x) (x - p x) := by
      have hx : x = p x + (x - p x) := by abel
      calc (inner ℬ x x : ℬ)
          = inner ℬ (p x + (x - p x)) (p x + (x - p x)) := by rw [← hx]
        _ = inner ℬ (p x) (p x) + inner ℬ (x - p x) (x - p x) := by
            rw [CStarModule.inner_add_left, CStarModule.inner_add_right,
              CStarModule.inner_add_right, h1, horth x _ (hp x)]
            abel
    have h3 : (inner ℬ (p x) (p x) : ℬ) ≤ inner ℬ x x := by
      rw [h2]
      exact le_add_of_nonneg_right CStarModule.inner_self_nonneg
    have h4 : ‖(inner ℬ (p x) (p x) : ℬ)‖ ≤ ‖(inner ℬ x x : ℬ)‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le CStarModule.inner_self_nonneg h3
    rw [cstarBInner_norm, cstarBInner_norm, one_mul,
      CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ) (E := X) (p x),
      CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ) (E := X) x]
    exact Real.sqrt_le_sqrt h4
  · refine huniq w w hw fun w' _ => ?_
    rw [sub_self, CStarModule.inner_zero_left]

/-- **160X** (`selfdual-gramschmidt`, dils.tex:4581, Exercise): for
`x₁, …, xₙ` in a self-dual Hilbert ℬ-module there is a finite orthonormal
basis of `{x₁,…,xₙ}^⊥⊥` of at most `n` elements (each `xᵢ` is its finite
basis expansion).

Divergence class 1 (faithful): this *is* the thesis's hint, "use the
orthonormalization in the last part of `selfdual-bcompl-then-basis`", made
into an induction on `n`.  The new element is the isometric part `u` of the
polar decomposition of the remainder `z = xₙ − ∑ₖ ⟨fₖ,xₙ⟩ • fₖ`; it lies in
`{x₁,…,xₙ}^⊥⊥` because that is an ultranorm-closed submodule and `u` is an
ultranorm limit of ℬ-multiples of `z` (the third conjunct of
`polar_decomposition`), and `⟨u,xₙ⟩ = √⟨z,z⟩` makes `z = ⟨u,xₙ⟩ • u`. -/
theorem selfdual_gramschmidt [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) {n : ℕ} (x : Fin n → X) :
    ∃ (m : ℕ), m ≤ n ∧ ∃ f : Fin m → X,
      OrthonormalFam ℬ f ∧
      (∀ k, f k ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range x))) ∧
      ∀ i, x i = ∑ k, inner ℬ (f k) (x i) • f k := by
  classical
  induction n with
  | zero =>
      exact ⟨0, le_refl 0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩,
        fun k => k.elim0, fun i => i.elim0⟩
  | succ n ih =>
      obtain ⟨m, hm, f, hf, hfW, hexp⟩ := ih (fun i : Fin n => x i.castSucc)
      obtain ⟨hW0, hWadd, hWb, hWc, hWcl⟩ :=
        hilbmod_projthm_1 hX (orthoCompl ℬ (Set.range x))
      set W : Set X := orthoCompl ℬ (orthoCompl ℬ (Set.range x)) with hWdef
      have hWneg : ∀ y ∈ W, -y ∈ W := fun y hy => by
        have h := hWc (-1 : ℂ) y hy
        rwa [neg_one_smul] at h
      have hWsub : ∀ y ∈ W, ∀ z ∈ W, y - z ∈ W := fun y hy z hz => by
        rw [sub_eq_add_neg]; exact hWadd y hy (-z) (hWneg z hz)
      -- the old orthonormal family already lies in the bigger `W`
      have hsub : Set.range (fun i : Fin n => x i.castSucc) ⊆ Set.range x := by
        rintro y ⟨i, rfl⟩
        exact ⟨i.castSucc, rfl⟩
      have hfW' : ∀ k, f k ∈ W := fun k => biorthoCompl_mono hsub (hfW k)
      have hxW : ∀ i, x i ∈ W := fun i => subset_biorthoCompl _ ⟨i, rfl⟩
      set xl : X := x (Fin.last n) with hxldef
      set P : X := ∑ k, (inner ℬ (f k) xl : ℬ) • f k with hPdef
      have hPW : P ∈ W := by
        rw [hPdef]
        refine Finset.sum_induction _ (fun z => z ∈ W)
          (fun z z' hz hz' => hWadd z hz z' hz') hW0 (fun k _ => ?_)
        exact hWb _ _ (hfW' k)
      set z : X := xl - P with hzdef
      have hzW : z ∈ W := hWsub xl (hxW _) P hPW
      have hzo : ∀ j : Fin m, (inner ℬ (f j) z : ℬ) = 0 := by
        intro j
        rw [hzdef, CStarModule.inner_sub_right, hPdef, CStarModule.inner_sum_right,
          Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
        · rw [CStarModule.inner_op_smul_right, onbasis_coef_absorb hf xl j,
            sub_self]
        · intro k _ hkj
          rw [CStarModule.inner_op_smul_right, hf.1 j k (Ne.symm hkj), mul_zero]
      by_cases hz0 : z = 0
      · refine ⟨m, hm.trans (Nat.le_succ n), f, hf, hfW', fun i => ?_⟩
        refine Fin.lastCases ?_ (fun j => ?_) i
        · have h : xl = P := by
            have h0 := hz0
            rw [hzdef, sub_eq_zero] at h0
            exact h0
          rw [← hxldef, ← hPdef]
          exact h
        · exact hexp j
      · obtain ⟨u, huu, hbu, cc, hcc⟩ := polar_decomposition
          (bddUnComplete_of_selfDual hX) z
        have huW : u ∈ W :=
          hWcl ▸ mem_unClosure_of_unTendsto W (fun N => cc N • z)
            (fun N => hWb (cc N) z hzW) u hcc
        have hzz : (inner ℬ z z : ℬ) ≠ 0 := fun h0 =>
          hz0 ((CStarModule.inner_self (A := ℬ)).mp h0)
        have hbne : CFC.sqrt (inner ℬ z z : ℬ) ≠ 0 := by
          intro h0
          refine hzz ?_
          rw [← CFC.sqrt_mul_sqrt_self (inner ℬ z z : ℬ)
            CStarModule.inner_self_nonneg, h0, mul_zero]
        have hqproj : IsStarProjection (inner ℬ u u : ℬ) := by
          rw [huu]; exact (ceill_basic_1 _).1.1
        have hqne : (inner ℬ u u : ℬ) ≠ 0 := by
          rw [huu]
          intro h0
          have h1 := (ceill_basic_1 (CFC.sqrt (inner ℬ z z : ℬ))).1.2
          rw [h0, mul_zero] at h1
          exact hbne h1.symm
        have hfu : ∀ j : Fin m, (inner ℬ (f j) u : ℬ) = 0 := fun j =>
          inner_eq_zero_of_polar huu hbu (hzo j)
        have huf : ∀ j : Fin m, (inner ℬ u (f j) : ℬ) = 0 := by
          intro j
          have h := congrArg star (hfu j)
          rwa [CStarModule.star_inner, star_zero] at h
        -- `u` is orthogonal to each `xᵢ` with `i < n`, by their expansions
        have hux : ∀ j : Fin n, (inner ℬ u (x j.castSucc) : ℬ) = 0 := by
          intro j
          rw [hexp j, CStarModule.inner_sum_right]
          exact Finset.sum_eq_zero fun k _ => by
            rw [CStarModule.inner_op_smul_right, huf k, mul_zero]
        -- and `⟨u, xₙ⟩ = √⟨z,z⟩`, so `z = ⟨u,xₙ⟩ • u`
        have huz : (inner ℬ u z : ℬ) = CFC.sqrt (inner ℬ z z : ℬ) :=
          calc (inner ℬ u z : ℬ)
              = inner ℬ u (CFC.sqrt (inner ℬ z z : ℬ) • u) := by rw [hbu]
            _ = CFC.sqrt (inner ℬ z z : ℬ) := by
                rw [CStarModule.inner_op_smul_right, huu]
                exact (ceill_basic_1 (CFC.sqrt (inner ℬ z z : ℬ))).1.2
        have huP : (inner ℬ u P : ℬ) = 0 := by
          rw [hPdef, CStarModule.inner_sum_right]
          exact Finset.sum_eq_zero fun k _ => by
            rw [CStarModule.inner_op_smul_right, huf k, mul_zero]
        have huxl : (inner ℬ u xl : ℬ) = CFC.sqrt (inner ℬ z z : ℬ) := by
          have h : xl = z + P := by rw [hzdef]; abel
          rw [h, CStarModule.inner_add_right, huz, huP, add_zero]
        refine ⟨m + 1, Nat.succ_le_succ hm, Fin.snoc f u, ⟨?_, ?_⟩, ?_, ?_⟩
        · intro a
          refine Fin.lastCases ?_ (fun a' => ?_) a
          · intro b
            refine Fin.lastCases ?_ (fun b' => ?_) b
            · intro hab
              exact absurd rfl hab
            · intro _
              rw [Fin.snoc_last, Fin.snoc_castSucc]
              exact huf b'
          · intro b
            refine Fin.lastCases ?_ (fun b' => ?_) b
            · intro _
              rw [Fin.snoc_castSucc, Fin.snoc_last]
              exact hfu a'
            · intro hab
              rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
              exact hf.1 a' b' fun h => hab (by rw [h])
        · intro a
          refine Fin.lastCases ?_ (fun a' => ?_) a
          · rw [Fin.snoc_last]
            exact ⟨hqproj, hqne⟩
          · rw [Fin.snoc_castSucc]
            exact hf.2 a'
        · intro k
          refine Fin.lastCases ?_ (fun k' => ?_) k
          · rw [Fin.snoc_last]; exact huW
          · rw [Fin.snoc_castSucc]; exact hfW' k'
        · intro i
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          refine Fin.lastCases ?_ (fun j => ?_) i
          · rw [← hxldef, ← hPdef, huxl, hbu, hzdef]
            abel
          · rw [hux j, op_zero_smul, add_zero]
            exact hexp j

end Ortho

/-! ## Parsec 1610: ℓ²((pᵢ)) and orthonormal bases

**161I** (`thel2matter`, dils.tex:4594) and **161III** (`hilbel-matter`,
dils.tex:4625, counterexamples): discussion — nothing to formalize. -/

section L2

variable {ℬ : Type u}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

variable (ℬ) in
/-- The set `ℓ²((pᵢ)ᵢ)` of ℓ²-summable tuples `(bᵢ)` with `⌈bᵢbᵢ*⌉ ≤ pᵢ`
(**161II**), as a subset of `ι → ℬ`.

**Mirroring.**  The thesis's tuples are the coordinates `⟨eᵢ,x⟩` of the
*right* module, this file's are the coordinates `⟪eᵢ,x⟫ = ⟨x,eᵢ⟩` of its
mirror, so the entries are starred relative to the thesis — which is why
`L2Summable` (`HilbertModules.lean`) renders `∑ᵢ bᵢ*bᵢ` as `∑ᵢ bᵢbᵢ*` and
the inner product `∑ᵢ bᵢ*cᵢ` as `∑ᵢ cᵢbᵢ*`.  The support condition has to
be starred with them: `⌈bᵢbᵢ*⌉ ≤ pᵢ` becomes `⌈bᵢ*bᵢ⌉ ≤ pᵢ`.  (It read
`⌈bᵢbᵢ*⌉ ≤ pᵢ` until 2026-08-16, which made **161II**.2 false: for
`ℬ = X = M₂` with orthonormal basis `(e₀₀, e₁₁)` the coordinates of
`x = e₁₀` are `bᵢ = x eᵢᵢ`, and `⌈b₀b₀*⌉ = e₁₁ ≰ e₀₀`.) -/
def L2Set [VonNeumannAlgebra ℬ] {ι : Type v} (p : ι → ℬ) : Set (ι → ℬ) :=
  {b | L2Summable ℬ b ∧ ∀ i, ceil (star (b i) * b i) ≤ p i}

/-- Membership of `L2Set` is an absorption condition: `⌈bᵢ*bᵢ⌉ ≤ pᵢ` iff
`bᵢpᵢ = bᵢ` (**59VI**.1 `ceill_basic_1`, the "recall from `ceill-basic`" of
the author's solution to **161II**). -/
private theorem ceil_star_mul_self_le_iff [VonNeumannAlgebra ℬ] (x : ℬ)
    {r : ℬ} (hr : IsStarProjection r) :
    ceil (star x * x) ≤ r ↔ x * r = x := by
  obtain ⟨⟨hproj, habs⟩, hleast⟩ := ceill_basic_1 x
  have hsupp : suppProj x = ceil (star x * x) := rfl
  rw [hsupp] at hproj habs hleast
  refine ⟨fun h => ?_, fun h => hleast ⟨hr, h⟩⟩
  have h1 : ceil (ceil (star x * x)) ≤ r := by
    rwa [ceil_of_isStarProjection hproj]
  have h2 : ceil (star x * x) * r = ceil (star x * x) :=
    (ceil_le_iff hproj.nonneg hr).mp h1
  calc x * r = x * ceil (star x * x) * r := by rw [habs]
    _ = x * (ceil (star x * x) * r) := by noncomm_ring
    _ = x * ceil (star x * x) := by rw [h2]
    _ = x := habs

private theorem mem_l2Set_iff [VonNeumannAlgebra ℬ] {ι : Type v} {p : ι → ℬ}
    (hp : ∀ i, IsStarProjection (p i)) (b : ι → ℬ) :
    b ∈ L2Set ℬ p ↔ L2Summable ℬ b ∧ ∀ i, b i * p i = b i :=
  and_congr_right fun _ =>
    forall_congr' fun i => ceil_star_mul_self_le_iff (b i) (hp i)

/-! ### Auxiliary for **161II**.1: ℓ²-summability and ultraweak convergence -/

/-- `(x+y)(x+y)* ≤ 2xx* + 2yy*`, because `(x−y)(x−y)* ≥ 0`. -/
private theorem mul_star_add_le (x y : ℬ) :
    (x + y) * star (x + y)
      ≤ (x * star x + x * star x) + (y * star y + y * star y) := by
  have h : (0 : ℬ) ≤ (x - y) * star (x - y) := mul_star_self_nonneg _
  have hid : (x * star x + x * star x) + (y * star y + y * star y)
      - (x + y) * star (x + y) = (x - y) * star (x - y) := by
    rw [star_add, star_sub]; noncomm_ring
  rw [← sub_nonneg, hid]
  exact h

/-- ℓ²-summable families are closed under addition (**161II**, first part of
the author's solution) — here without the Cauchy–Schwarz estimate the
solution uses, since `(x+y)(x+y)* ≤ 2xx* + 2yy*` already bounds the partial
sums. -/
private theorem l2Summable_add {ι : Type v} {b c : ι → ℬ}
    (hb : L2Summable ℬ b) (hc : L2Summable ℬ c) :
    L2Summable ℬ fun i => b i + c i := by
  obtain ⟨Mb, hMb⟩ := hb
  obtain ⟨Mc, hMc⟩ := hc
  refine ⟨(Mb + Mb) + (Mc + Mc), fun t => ?_⟩
  have hnn : (0 : ℬ) ≤ ∑ i ∈ t, (b i + c i) * star (b i + c i) :=
    Finset.sum_nonneg fun i _ => mul_star_self_nonneg _
  have hle : (∑ i ∈ t, (b i + c i) * star (b i + c i))
      ≤ ((∑ i ∈ t, b i * star (b i)) + ∑ i ∈ t, b i * star (b i))
        + ((∑ i ∈ t, c i * star (c i)) + ∑ i ∈ t, c i * star (c i)) := by
    have h1 : (∑ i ∈ t, (b i + c i) * star (b i + c i))
        ≤ ∑ i ∈ t, ((b i * star (b i) + b i * star (b i))
          + (c i * star (c i) + c i * star (c i))) :=
      Finset.sum_le_sum fun i _ => mul_star_add_le (b i) (c i)
    refine h1.trans_eq ?_
    simp [Finset.sum_add_distrib]
  refine (CStarAlgebra.norm_le_norm_of_nonneg_of_le hnn hle).trans ?_
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (norm_add_le _ _).trans (add_le_add (hMb t) (hMb t))
  · exact (norm_add_le _ _).trans (add_le_add (hMc t) (hMc t))

/-- ℓ²-summable families are closed under scalar multiplication. -/
private theorem l2Summable_smul {ι : Type v} (z : ℂ) {c : ι → ℬ}
    (hc : L2Summable ℬ c) : L2Summable ℬ fun i => z • c i := by
  obtain ⟨M, hM⟩ := hc
  have hM0 : (0 : ℝ) ≤ M := by simpa using hM ∅
  refine ⟨‖z‖ * ‖z‖ * M, fun t => ?_⟩
  have hEq : (∑ i ∈ t, (z • c i) * star (z • c i))
      = (z * star z) • ∑ i ∈ t, c i * star (c i) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hEq, norm_smul, norm_mul, norm_star]
  exact mul_le_mul_of_nonneg_left (hM t) (by positivity)

/-- The partial sums `∑ᵢ dᵢdᵢ*` of an ℓ²-summable family are a monotone,
norm-bounded net of positive elements, so they converge ultraweakly to their
supremum by **44VI**. -/
private theorem exists_uwTendsto_l2_diag [VonNeumannAlgebra ℬ] {ι : Type v}
    (d : ι → ℬ) (hd : L2Summable ℬ d) :
    ∃ s : ℬ, UWTendsto (fun t : Finset ι => ∑ i ∈ t, d i * star (d i))
      atTop s := by
  classical
  obtain ⟨M, hM⟩ := hd
  have hnn : ∀ t : Finset ι, (0 : ℬ) ≤ ∑ i ∈ t, d i * star (d i) :=
    fun t => Finset.sum_nonneg fun i _ => mul_star_self_nonneg _
  set f : Finset ι → selfAdjoint ℬ := fun t =>
    ⟨∑ i ∈ t, d i * star (d i), IsSelfAdjoint.of_nonneg (hnn t)⟩ with hfdef
  have hmono : Monotone f := by
    intro s t hst
    refine Subtype.coe_le_coe.mp ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hst
      fun i _ _ => mul_star_self_nonneg _
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨⟨algebraMap ℂ ℬ ((M : ℝ) : ℂ), isSelfAdjoint_algebraMap_ofReal M⟩,
      ?_⟩
    rintro _ ⟨t, rfl⟩
    refine Subtype.coe_le_coe.mp ?_
    have h1 : (∑ i ∈ t, d i * star (d i))
        ≤ algebraMap ℂ ℬ ((‖∑ i ∈ t, d i * star (d i)‖ : ℝ) : ℂ) := by
      have h := IsSelfAdjoint.le_algebraMap_norm_self
        (IsSelfAdjoint.of_nonneg (hnn t))
      rwa [algebraMap_real_eq] at h
    exact h1.trans (algebraMap_ofReal_mono (hM t))
  have hne : (Set.range f).Nonempty := Set.range_nonempty f
  have hdir : DirectedOn (· ≤ ·) (Set.range f) := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    exact ⟨f (s ⊔ t), ⟨s ⊔ t, rfl⟩, hmono le_sup_left, hmono le_sup_right⟩
  have h3 : (Set.range f).Nonempty ∧ DirectedOn (· ≤ ·) (Set.range f)
      ∧ BddAbove (Set.range f) := ⟨hne, hdir, hbdd⟩
  exact ⟨((dirSup (Set.range f) h3 : selfAdjoint ℬ) : ℬ),
    uwTendsto_of_monotone_isLUB f hmono _ (isLUB_dirSup (Set.range f) h3)⟩

/-- The polarization identity for the ℬ-valued form `(x,y) ↦ y x*`:
`4 y x* = (x+y)(x+y)* − (x−y)(x−y)* − i(x+iy)(x+iy)* + i(x−iy)(x−iy)*`. -/
private theorem polarization_mul_star (x y : ℬ) :
    (4 : ℂ) • (y * star x)
      = ((x + y) * star (x + y) - (x + (-1 : ℂ) • y) * star (x + (-1 : ℂ) • y)
          - Complex.I • ((x + Complex.I • y) * star (x + Complex.I • y)))
        + Complex.I • ((x + (-Complex.I) • y) * star (x + (-Complex.I) • y)) := by
  have hexp : ∀ z : ℂ, (x + z • y) * star (x + z • y)
      = x * star x + (star z) • (x * star y) + z • (y * star x)
        + (z * star z) • (y * star y) := by
    intro z
    rw [star_add, star_smul]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    match_scalars <;> ring
  have hone : star (1 : ℂ) = 1 := star_one ℂ
  have hnone : star (-1 : ℂ) = -1 := by rw [star_neg, star_one]
  have hI : star (Complex.I) = -Complex.I := Complex.conj_I
  have hnI : star (-Complex.I) = Complex.I := by rw [star_neg, hI, neg_neg]
  have h0 : (x + y) * star (x + y) = (x + (1 : ℂ) • y) * star (x + (1 : ℂ) • y) := by
    rw [one_smul]
  rw [h0, hexp, hexp, hexp, hexp, hone, hnone, hI, hnI]
  match_scalars <;> simp [Complex.ext_iff] <;> ring

/-- **161II** (`hilbmod-el2`, dils.tex:4602, Exercise), part 1: for
ℓ²-summable tuples `(bᵢ)`, `(cᵢ)` over a von Neumann algebra the inner
product `∑ᵢ bᵢ* cᵢ` (mirrored: `∑ᵢ cᵢ bᵢ*`) converges ultraweakly; with
the coordinatewise operations this turns `ℓ²((pᵢ)ᵢ)` into a (pre-)Hilbert
ℬ-module.

**Divergence (class 2).**  The author's solution shows the net of partial
sums is norm-bounded and ultraweakly Cauchy (two Cauchy–Schwarz estimates
and an ε-argument) and appeals to bounded ultraweak completeness
(**77I**.2).  The proof below instead *polarizes*: `4 cᵢbᵢ*` is a fixed
ℂ-combination of four diagonal terms `dᵢdᵢ*`, each of whose partial sums is
a monotone bounded net of positives, hence ultraweakly convergent by
**44VI** alone.  No completeness and no Cauchy–Schwarz is used. -/
theorem hilbmod_el2_inner [VonNeumannAlgebra ℬ] {ι : Type v} (b c : ι → ℬ)
    (hb : L2Summable ℬ b) (hc : L2Summable ℬ c) :
    ∃ s : ℬ, UWTendsto (fun t : Finset ι => ∑ i ∈ t, c i * star (b i))
      atTop s := by
  classical
  obtain ⟨s0, hs0⟩ := exists_uwTendsto_l2_diag (fun i => b i + c i)
    (l2Summable_add hb hc)
  obtain ⟨s1, hs1⟩ := exists_uwTendsto_l2_diag
    (fun i => b i + (-1 : ℂ) • c i) (l2Summable_add hb (l2Summable_smul _ hc))
  obtain ⟨s2, hs2⟩ := exists_uwTendsto_l2_diag
    (fun i => b i + Complex.I • c i)
    (l2Summable_add hb (l2Summable_smul _ hc))
  obtain ⟨s3, hs3⟩ := exists_uwTendsto_l2_diag
    (fun i => b i + (-Complex.I) • c i)
    (l2Summable_add hb (l2Summable_smul _ hc))
  refine ⟨(4⁻¹ : ℂ) • (s0 - s1 - Complex.I • s2 + Complex.I • s3), ?_⟩
  have hcomb : UWTendsto
      (fun t : Finset ι => (4⁻¹ : ℂ) •
        (((∑ i ∈ t, (b i + c i) * star (b i + c i))
            - ∑ i ∈ t, (b i + (-1 : ℂ) • c i) * star (b i + (-1 : ℂ) • c i)
            - Complex.I • ∑ i ∈ t,
              (b i + Complex.I • c i) * star (b i + Complex.I • c i))
          + Complex.I • ∑ i ∈ t,
            (b i + (-Complex.I) • c i) * star (b i + (-Complex.I) • c i)))
      atTop ((4⁻¹ : ℂ) • (s0 - s1 - Complex.I • s2 + Complex.I • s3)) := by
    have hsub : ∀ {f g : Finset ι → ℬ} {u v : ℬ}, UWTendsto f atTop u →
        UWTendsto g atTop v → UWTendsto (fun t => f t - g t) atTop (u - v) := by
      intro f g u v hf hg
      have h := uwTendsto_add' hf (uwTendsto_smul' (-1 : ℂ) hg)
      simpa only [neg_smul, one_smul, ← sub_eq_add_neg] using h
    exact uwTendsto_smul' _
      (uwTendsto_add' (hsub (hsub hs0 hs1) (uwTendsto_smul' Complex.I hs2))
        (uwTendsto_smul' Complex.I hs3))
  have hEq : (fun t : Finset ι => ∑ i ∈ t, c i * star (b i))
      = fun t : Finset ι => (4⁻¹ : ℂ) •
        (((∑ i ∈ t, (b i + c i) * star (b i + c i))
            - ∑ i ∈ t, (b i + (-1 : ℂ) • c i) * star (b i + (-1 : ℂ) • c i)
            - Complex.I • ∑ i ∈ t,
              (b i + Complex.I • c i) * star (b i + Complex.I • c i))
          + Complex.I • ∑ i ∈ t,
            (b i + (-Complex.I) • c i) * star (b i + (-Complex.I) • c i)) := by
    funext t
    have hsum : (((∑ i ∈ t, (b i + c i) * star (b i + c i))
            - ∑ i ∈ t, (b i + (-1 : ℂ) • c i) * star (b i + (-1 : ℂ) • c i)
            - Complex.I • ∑ i ∈ t,
              (b i + Complex.I • c i) * star (b i + Complex.I • c i))
          + Complex.I • ∑ i ∈ t,
            (b i + (-Complex.I) • c i) * star (b i + (-Complex.I) • c i))
        = ∑ i ∈ t, ((4 : ℂ) • (c i * star (b i))) := by
      simp only [Finset.smul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ =>
        (polarization_mul_star (b i) (c i)).symm
    rw [hsum, ← Finset.smul_sum, smul_smul]
    norm_num
  rw [hEq]
  exact hcomb


variable {X : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X]

set_option linter.unusedVariables false in
/-- **161II** (`hilbmod-el2`, dils.tex:4602, Exercise), part 2:
`ℓ²((pᵢ)ᵢ)` is self dual, and every self-dual Hilbert ℬ-module `X` with
orthonormal basis `(eᵢ)ᵢ` is isomorphic to `ℓ²((⟨eᵢ,eᵢ⟩)ᵢ)` via the
coordinate map `x ↦ (⟨eᵢ,x⟩)ᵢ`: the coordinate map is injective, additive,
lands bijectively on `ℓ²((⟨eᵢ,eᵢ⟩)ᵢ)` and identifies the inner
products.

**Divergence (class 2/3).**  The author's solution builds `ℓ²((pᵢ))` as a
module, proves it self-dual, and only then transports the structure along
the coordinate map.  Nothing of that is needed for the statement above: all
three clauses come straight out of the two convergence clauses of
`IsONBasis`.

* the coordinates are ℓ²-summable by Bessel (`mod_bessel`) and absorbed by
  the projections `⟨eᵢ,eᵢ⟩` (`onbasis_coef_absorb`), which by
  `ceil_star_mul_self_le_iff` *is* the support condition `⌈bᵢ*bᵢ⌉ ≤ pᵢ`;
* surjectivity is clause (b) of `IsONBasis` followed by
  `inner_of_unTendsto_sum_smul` (the coefficients of a convergent
  `∑ᵢ bᵢ • eᵢ` are the `bᵢ`), for which the absorption is again exactly the
  support condition;
* injectivity and the inner-product clause are both **148V**
  `innerprod_ultraweak` applied to the basis expansions of clause (a): for
  injectivity the two expansions are the *same* net, so all four of
  `⟨x,x⟩, ⟨x,y⟩, ⟨y,x⟩, ⟨y,y⟩` are its Gram limit and `⟨x−y,x−y⟩ = 0`; for
  the inner product the cross Gram sum collapses to the Parseval sum by
  `inner_sum_smul_orthogonal` plus absorption.

Consequently the hypothesis `hX : SelfDual ℬ X` is **not used** — an
orthonormal *basis* already carries everything.  (Note also that our
statement is weaker than the exercise, which additionally asks for the
right-module structure on `ℓ²((pᵢ))` and its self-duality; those are not
formalized anywhere in this file.) -/
theorem hilbmod_el2 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) {ι : Type v} (e : ι → X) (he : IsONBasis ℬ e) :
    Set.BijOn (fun (x : X) (i : ι) => inner ℬ (e i) x) Set.univ
        (L2Set ℬ fun i => inner ℬ (e i) (e i)) ∧
      ∀ x y : X,
        UWTendsto
          (fun t : Finset ι =>
            ∑ i ∈ t, inner ℬ (e i) y * star (inner ℬ (e i) x))
          atTop (inner ℬ x y) := by
  classical
  obtain ⟨horth, hexp, hbl2⟩ := he
  have hB : (cstarBInner ℬ X).inner = (inner ℬ : X → X → ℬ) := rfl
  have hproj : ∀ i : ι, IsStarProjection (inner ℬ (e i) (e i) : ℬ) :=
    fun i => (horth.2 i).1
  -- **149IV**: the coordinates are absorbed by the projections `⟨eᵢ,eᵢ⟩`
  have habs : ∀ (x : X) (i : ι),
      (inner ℬ (e i) x : ℬ) * inner ℬ (e i) (e i) = inner ℬ (e i) x :=
    fun x i => onbasis_coef_absorb horth x i
  -- Bessel: the coordinates are ℓ²-summable
  have hL2 : ∀ x : X, L2Summable ℬ fun i => (inner ℬ (e i) x : ℬ) := by
    intro x
    refine ⟨‖(inner ℬ x x : ℬ)‖, fun s => ?_⟩
    have h1 : ∑ i ∈ s, (inner ℬ (e i) x : ℬ) * star (inner ℬ (e i) x : ℬ)
        = ∑ i ∈ s, (inner ℬ (e i) x : ℬ) * (inner ℬ x (e i) : ℬ) :=
      Finset.sum_congr rfl fun i _ => by rw [CStarModule.star_inner]
    rw [h1]
    have h3 : (0 : ℬ) ≤ ∑ i ∈ s,
        (inner ℬ (e i) x : ℬ) * (inner ℬ x (e i) : ℬ) := by
      rw [← h1]
      exact Finset.sum_nonneg fun i _ => mul_star_self_nonneg _
    exact CStarAlgebra.norm_le_norm_of_nonneg_of_le h3 (mod_bessel horth x s)
  -- the cross Gram sums of two basis expansions are the Parseval cross sums
  have hgram : ∀ (x y : X) (s : Finset ι),
      (inner ℬ (∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i)
        (∑ i ∈ s, (inner ℬ (e i) y : ℬ) • e i) : ℬ)
        = ∑ i ∈ s, (inner ℬ (e i) y : ℬ) * star (inner ℬ (e i) x : ℬ) := by
    intro x y s
    rw [inner_sum_smul_orthogonal horth.1 _ _ s]
    exact Finset.sum_congr rfl fun i _ => by rw [habs y i]
  -- the inner-product clause, by **148V**
  have hpart2 : ∀ x y : X, UWTendsto
      (fun t : Finset ι =>
        ∑ i ∈ t, (inner ℬ (e i) y : ℬ) * star (inner ℬ (e i) x : ℬ))
      atTop (inner ℬ x y) := by
    intro x y
    have h := innerprod_ultraweak (cstarBInner ℬ X)
      (fun s : Finset ι => ∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i)
      (fun s : Finset ι => ∑ i ∈ s, (inner ℬ (e i) y : ℬ) • e i)
      x y (hexp x) (hexp y)
    simpa only [hB, hgram] using h
  refine ⟨⟨fun x _ => (mem_l2Set_iff hproj _).mpr ⟨hL2 x, fun i => habs x i⟩,
    fun x _ y _ hxy => ?_, fun b hb => ?_⟩, hpart2⟩
  · -- injectivity: the two expansions are the same net
    have hxy' : ∀ i : ι, (inner ℬ (e i) x : ℬ) = inner ℬ (e i) y :=
      fun i => congrFun hxy i
    have hx : UnTendsto (inner ℬ : X → X → ℬ)
        (fun s : Finset ι => ∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i) atTop x :=
      hexp x
    have hy : UnTendsto (inner ℬ : X → X → ℬ)
        (fun s : Finset ι => ∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i) atTop y := by
      have hnet : (fun s : Finset ι => ∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i)
          = fun s : Finset ι => ∑ i ∈ s, (inner ℬ (e i) y : ℬ) • e i := by
        funext s
        exact Finset.sum_congr rfl fun i _ => by rw [hxy' i]
      rw [hnet]
      exact hexp y
    have hxx := innerprod_ultraweak (cstarBInner ℬ X) _ _ x x hx hx
    have hxy₂ := innerprod_ultraweak (cstarBInner ℬ X) _ _ x y hx hy
    have hyx := innerprod_ultraweak (cstarBInner ℬ X) _ _ y x hy hx
    have hyy := innerprod_ultraweak (cstarBInner ℬ X) _ _ y y hy hy
    have e1 : (inner ℬ x x : ℬ) = inner ℬ x y := uwTendsto_unique₂ hxx hxy₂
    have e2 : (inner ℬ x x : ℬ) = inner ℬ y x := uwTendsto_unique₂ hxx hyx
    have e3 : (inner ℬ x x : ℬ) = inner ℬ y y := uwTendsto_unique₂ hxx hyy
    have hz : (inner ℬ (x - y) (x - y) : ℬ) = 0 := by
      rw [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
        CStarModule.inner_sub_right, ← e1, ← e2, ← e3]
      abel
    exact sub_eq_zero.mp ((CStarModule.inner_self (A := ℬ)).mp hz)
  · -- surjectivity: clause (b) of `IsONBasis`, then the coefficient lemma
    obtain ⟨hbsum, hbabs⟩ := (mem_l2Set_iff hproj b).mp hb
    obtain ⟨x, hx⟩ := hbl2 b hbsum
    exact ⟨x, Set.mem_univ x,
      funext fun i => inner_of_unTendsto_sum_smul horth b hbabs hx i⟩

/-- **161IV** (`onb1`, dils.tex:4673, Exercise), part 1: if `(eᵢ)` is an
orthonormal basis of a Hilbert ℬ-module `X` and `(uᵢ)` are partial
isometries with `uᵢuᵢ* = ⟨eᵢ,eᵢ⟩`, then `(eᵢuᵢ)ᵢ` (mirrored:
`star uᵢ • eᵢ`) is an orthonormal basis of `X`. -/
theorem onb1 [VonNeumannAlgebra ℬ] [CompleteSpace X] {ι : Type v}
    (e : ι → X) (he : IsONBasis ℬ e) (u : ι → ℬ)
    (hpi : ∀ i, IsStarProjection (star (u i) * u i))
    (hu : ∀ i, u i * star (u i) = inner ℬ (e i) (e i)) :
    IsONBasis ℬ fun i => star (u i) • e i := by
  -- `bsols.tex`, solution `onb1`, first part, transcribed.
  obtain ⟨⟨heorth, heproj⟩, hebasis, hel2⟩ := he
  -- `⟨eᵢuᵢ, eⱼuⱼ⟩ = uⱼ* ⟨eᵢ,eⱼ⟩ uᵢ` (mirrored)
  have hinner : ∀ i j : ι, (inner ℬ (star (u i) • e i) (star (u j) • e j) : ℬ)
      = star (u j) * inner ℬ (e i) (e j) * u i := by
    intro i j
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_left,
      star_star, mul_assoc]
  -- `⟨eᵢuᵢ, eᵢuᵢ⟩ = uᵢ*uᵢ`, a projection
  have hdiag : ∀ i : ι, (inner ℬ (star (u i) • e i) (star (u i) • e i) : ℬ)
      = star (u i) * u i := by
    intro i
    rw [hinner i i, ← hu i]
    have h := (hpi i).isIdempotentElem
    calc star (u i) * (u i * star (u i)) * u i
        = (star (u i) * u i) * (star (u i) * u i) := by noncomm_ring
      _ = star (u i) * u i := h
  -- `⟨eᵢ,x⟩⟨eᵢ,eᵢ⟩ = ⟨eᵢ,x⟩` (mirrored), from **149III**
  have hself : ∀ (i : ι) (x : X), (inner ℬ (e i) x : ℬ) * inner ℬ (e i) (e i)
      = inner ℬ (e i) x := by
    intro i x
    have hps : star (inner ℬ (e i) (e i) : ℬ) = inner ℬ (e i) (e i) :=
      (heproj i).1.isSelfAdjoint
    have h2 : (inner ℬ ((inner ℬ (e i) (e i) : ℬ) • e i) x : ℬ)
        = inner ℬ (e i) x := by rw [mod_projelabs (e i) (heproj i).1]
    rwa [CStarModule.inner_op_smul_left, hps] at h2
  -- the two families have the same partial sums
  have hterm : ∀ (x : X) (i : ι),
      (inner ℬ (star (u i) • e i) x : ℬ) • (star (u i) • e i)
        = (inner ℬ (e i) x : ℬ) • e i := by
    intro x i
    rw [CStarModule.inner_op_smul_left, star_star, ← op_mul_smul, mul_assoc,
      hu i, hself i x]
  refine ⟨⟨fun i j hij => by rw [hinner i j, heorth i j hij, mul_zero, zero_mul],
    fun i => ⟨?_, ?_⟩⟩, fun x => ?_, fun b hb => ?_⟩
  · rw [hdiag i]; exact hpi i
  · -- `uᵢ*uᵢ ≠ 0`, for otherwise `uᵢ = 0` and `⟨eᵢ,eᵢ⟩ = uᵢuᵢ* = 0`
    rw [hdiag i]
    intro h0
    have hun : ‖u i‖ * ‖u i‖ = 0 := by
      rw [← CStarRing.norm_star_mul_self, h0, norm_zero]
    have hu0 : u i = 0 := norm_eq_zero.mp (mul_self_eq_zero.mp hun)
    exact (heproj i).2 (by rw [← hu i, hu0]; simp)
  · -- basis expansion: term by term the same as for `(eᵢ)`
    have hfun : (fun s : Finset ι =>
        ∑ i ∈ s, (inner ℬ (star (u i) • e i) x : ℬ) • (star (u i) • e i))
        = fun s : Finset ι => ∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i := by
      funext s
      exact Finset.sum_congr rfl fun i _ => hterm x i
    rw [hfun]
    exact hebasis x
  · -- `∑ᵢ bᵢ(eᵢuᵢ) = ∑ᵢ (bᵢuᵢ*)eᵢ`, and `(bᵢuᵢ*)` is again ℓ²-summable
    obtain ⟨M, hM⟩ := hb
    have hple : ∀ i : ι, star (u i) * u i ≤ 1 := by
      intro i
      refine sub_nonneg.mp ?_
      have hidem : (star (u i) * u i) * (star (u i) * u i) = star (u i) * u i :=
        (hpi i).isIdempotentElem
      have hsa : star (star (u i) * u i) = star (u i) * u i :=
        (hpi i).isSelfAdjoint
      have hsq : (1 - star (u i) * u i) * (1 - star (u i) * u i)
          = 1 - star (u i) * u i := by
        simp only [sub_mul, mul_sub, one_mul, mul_one, hidem]
        abel
      have : (1 : ℬ) - star (u i) * u i
          = star ((1 : ℬ) - star (u i) * u i) * (1 - star (u i) * u i) := by
        rw [star_sub, star_one, hsa, hsq]
      rw [this]
      exact star_mul_self_nonneg _
    have hl2 : L2Summable ℬ fun i => b i * star (u i) := by
      refine ⟨M, fun s => ?_⟩
      have hcalc : ∀ i : ι, (b i * star (u i)) * star (b i * star (u i))
          = b i * (star (u i) * u i) * star (b i) := by
        intro i; rw [star_mul, star_star]; noncomm_ring
      have hle : ∑ i ∈ s, (b i * star (u i)) * star (b i * star (u i))
          ≤ ∑ i ∈ s, b i * star (b i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hcalc i]
        have := star_right_conjugate_le_conjugate (hple i) (b i)
        rwa [mul_one] at this
      have hnn : (0 : ℬ) ≤ ∑ i ∈ s, (b i * star (u i)) * star (b i * star (u i)) :=
        Finset.sum_nonneg fun i _ => mul_star_self_nonneg _
      exact le_trans (CStarAlgebra.norm_le_norm_of_nonneg_of_le hnn hle) (hM s)
    obtain ⟨x, hx⟩ := hel2 _ hl2
    refine ⟨x, ?_⟩
    have hfun : (fun s : Finset ι => ∑ i ∈ s, b i • (star (u i) • e i))
        = fun s : Finset ι => ∑ i ∈ s, (b i * star (u i)) • e i := by
      funext s
      exact Finset.sum_congr rfl fun i _ => (op_mul_smul _ _ _).symm
    rw [hfun]
    exact hx

/-- Murray–von Neumann equivalence `p ∼ q` of projections: `u* u = p` and
`u u* = q` for some partial isometry `u` (**161IV**; cf. vn.tex 83II
`vmleq`). -/
def MvNEquiv (p q : ℬ) : Prop :=
  ∃ u : ℬ, star u * u = p ∧ u * star u = q

/-- **161IV** (`onb1`, dils.tex:4673, Exercise), part 2:
`ℓ²((pᵢ)ᵢ) ≅ ℓ²((qᵢ)ᵢ)` for pointwise Murray–von Neumann equivalent
families of projections: there is a bijection between the tuple sets that
identifies the (ultraweakly converging) inner products.

**Divergence (class 2).**  The author's solution routes this through the
*module* `ℓ²((pᵢ))`: the `δᵢ` are an orthonormal basis (**161II**), so
`(δᵢuᵢ)ᵢ` is another one by part 1 of this exercise, and the second half of
**161II** then produces the isomorphism with `ℓ²((⟨δᵢuᵢ, δᵢuᵢ⟩)ᵢ) =
ℓ²((qᵢ))`.  Both halves of 161II are still `sorry` here, so the bijection is
written down directly instead: `Φ(b)ᵢ = bᵢuᵢ*` (mirrored from the thesis's
`bᵢ ↦ uᵢ*bᵢ`), with inverse `bᵢ ↦ bᵢuᵢ`.  Absorption `bᵢpᵢ = bᵢ` makes
`Φ(c)ᵢ Φ(b)ᵢ* = cᵢ pᵢ bᵢ* = cᵢbᵢ*` termwise, so the two nets of partial sums
are *equal*, which is why the inner-product clause is an equality of
functions rather than a limit argument. -/
theorem onb1_el2 [VonNeumannAlgebra ℬ] {ι : Type v} (p q : ι → ℬ)
    (hp : ∀ i, IsStarProjection (p i)) (hq : ∀ i, IsStarProjection (q i))
    (hpq : ∀ i, MvNEquiv (p i) (q i)) :
    ∃ Φ : (ι → ℬ) → (ι → ℬ),
      Set.BijOn Φ (L2Set ℬ p) (L2Set ℬ q) ∧
      ∀ b ∈ L2Set ℬ p, ∀ c ∈ L2Set ℬ p, ∀ s : ℬ,
        UWTendsto (fun t : Finset ι => ∑ i ∈ t, c i * star (b i)) atTop s ↔
        UWTendsto (fun t : Finset ι => ∑ i ∈ t, Φ c i * star (Φ b i))
          atTop s := by
  classical
  choose u hu1 hu2 using hpq
  -- `Φ b = (bᵢuᵢ*)ᵢ` with inverse `Ψ b = (bᵢuᵢ)ᵢ` (mirrored from the
  -- author's `δᵢ ↦ δᵢuᵢ`)
  have hΦinner : ∀ (b c : ι → ℬ), (∀ i, c i * p i = c i) → ∀ i,
      (c i * star (u i)) * star (b i * star (u i)) = c i * star (b i) := by
    intro b c hc i
    rw [star_mul, star_star]
    calc c i * star (u i) * (u i * star (b i))
        = c i * (star (u i) * u i) * star (b i) := by noncomm_ring
      _ = c i * p i * star (b i) := by rw [hu1 i]
      _ = c i * star (b i) := by rw [hc i]
  have hΨinner : ∀ (b c : ι → ℬ), (∀ i, c i * q i = c i) → ∀ i,
      (c i * u i) * star (b i * u i) = c i * star (b i) := by
    intro b c hc i
    rw [star_mul]
    calc c i * u i * (star (u i) * star (b i))
        = c i * (u i * star (u i)) * star (b i) := by noncomm_ring
      _ = c i * q i * star (b i) := by rw [hu2 i]
      _ = c i * star (b i) := by rw [hc i]
  have hΦabs : ∀ b : ι → ℬ, (∀ i, b i * p i = b i) → ∀ i,
      (b i * star (u i)) * q i = b i * star (u i) := by
    intro b hb i
    calc b i * star (u i) * q i
        = b i * star (u i) * (u i * star (u i)) := by rw [hu2 i]
      _ = b i * (star (u i) * u i) * star (u i) := by noncomm_ring
      _ = b i * p i * star (u i) := by rw [hu1 i]
      _ = b i * star (u i) := by rw [hb i]
  have hΨabs : ∀ b : ι → ℬ, (∀ i, b i * q i = b i) → ∀ i,
      (b i * u i) * p i = b i * u i := by
    intro b hb i
    calc b i * u i * p i
        = b i * u i * (star (u i) * u i) := by rw [hu1 i]
      _ = b i * (u i * star (u i)) * u i := by noncomm_ring
      _ = b i * q i * u i := by rw [hu2 i]
      _ = b i * u i := by rw [hb i]
  have hΦsum : ∀ b : ι → ℬ, (∀ i, b i * p i = b i) → L2Summable ℬ b →
      L2Summable ℬ fun i => b i * star (u i) := by
    intro b hb hL
    obtain ⟨M, hM⟩ := hL
    refine ⟨M, fun t => ?_⟩
    have hter := hΦinner b b hb
    simp only [hter]
    exact hM t
  have hΨsum : ∀ b : ι → ℬ, (∀ i, b i * q i = b i) → L2Summable ℬ b →
      L2Summable ℬ fun i => b i * u i := by
    intro b hb hL
    obtain ⟨M, hM⟩ := hL
    refine ⟨M, fun t => ?_⟩
    have hter := hΨinner b b hb
    simp only [hter]
    exact hM t
  refine ⟨fun b i => b i * star (u i), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro b hb
    rw [mem_l2Set_iff hp] at hb
    rw [mem_l2Set_iff hq]
    exact ⟨hΦsum b hb.2 hb.1, hΦabs b hb.2⟩
  · intro b hb c hc hbc
    rw [mem_l2Set_iff hp] at hb hc
    have hround : ∀ d : ι → ℬ, (∀ i, d i * p i = d i) →
        (fun i => (d i * star (u i)) * u i) = d := by
      intro d hd
      funext i
      rw [mul_assoc, hu1 i, hd i]
    have h := congrArg (fun (f : ι → ℬ) i => f i * u i) hbc
    rw [← hround b hb.2, ← hround c hc.2]
    exact h
  · intro b hb
    rw [mem_l2Set_iff hq] at hb
    refine ⟨fun i => b i * u i, ?_, ?_⟩
    · rw [mem_l2Set_iff hp]
      exact ⟨hΨsum b hb.2 hb.1, hΨabs b hb.2⟩
    · funext i
      show (b i * u i) * star (u i) = b i
      rw [mul_assoc, hu2 i, hb.2 i]
  · intro b hb c hc s
    have hc' := ((mem_l2Set_iff hp c).mp hc).2
    have hEq : (fun t : Finset ι => ∑ i ∈ t, c i * star (b i))
        = fun t : Finset ι =>
          ∑ i ∈ t, (c i * star (u i)) * star (b i * star (u i)) := by
      funext t
      exact Finset.sum_congr rfl fun i _ => (hΦinner b c hc' i).symm
    rw [hEq]

/-- **161V** (`onb2`, dils.tex:4696, Exercise): if `(eᵢ)` is an orthonormal
basis of `X` with distinguished indices `i₁ ≠ i₂` and
`⟨e_{i₁},e_{i₁}⟩ + ⟨e_{i₂},e_{i₂}⟩ ≤ 1`, then removing `e_{i₁}, e_{i₂}`
and inserting `e_{i₁} + e_{i₂}` again yields an orthonormal basis.  (The
consequence `pℬ ⊕ qℬ ≅ (p+q)ℬ` for `p + q ≤ 1` is not converted
separately.) -/
theorem onb2 [VonNeumannAlgebra ℬ] [CompleteSpace X] {ι : Type v}
    [DecidableEq ι]
    (e : ι → X) (he : IsONBasis ℬ e) (i₁ i₂ : ι) (hne : i₁ ≠ i₂)
    (hle : inner ℬ (e i₁) (e i₁) + inner ℬ (e i₂) (e i₂) ≤ 1) :
    IsONBasis ℬ fun i : {i : ι // i ≠ i₂} =>
      if (i : ι) = i₁ then e i₁ + e i₂ else e i := by
  -- `bsols.tex`, solution `onb2`, transcribed.
  classical
  obtain ⟨⟨horth, hproj⟩, hexp, hl2⟩ := he
  set f : {i : ι // i ≠ i₂} → X :=
    fun i => if (i : ι) = i₁ then e i₁ + e i₂ else e i with hfdef
  set i₁' : {i : ι // i ≠ i₂} := ⟨i₁, hne⟩ with hi₁'
  have hpr : ∀ i, IsStarProjection (inner ℬ (e i) (e i) : ℬ) := fun i => (hproj i).1
  have hfpair : f i₁' = e i₁ + e i₂ := by simp [hfdef, hi₁']
  have hfelse : ∀ i : {i : ι // i ≠ i₂}, (i : ι) ≠ i₁ → f i = e (i : ι) := by
    intro i hi; simp [hfdef, hi]
  -- "$p_1$ and $p_2$ are projections with $p_1 + p_2 \leq 1$ and so by
  -- `orthogonal-tuple-of-projections` they are orthogonal" (**55XIII**)
  have htfae := orthogonal_tuple_of_projections_1
    (inner ℬ (e i₁) (e i₁) : ℬ) (inner ℬ (e i₂) (e i₂) : ℬ) (hpr i₁) (hpr i₂)
  have h12 : (inner ℬ (e i₁) (e i₁) : ℬ) * inner ℬ (e i₂) (e i₂) = 0 :=
    (htfae.out 3 0).mp hle
  have h21 : (inner ℬ (e i₂) (e i₂) : ℬ) * inner ℬ (e i₁) (e i₁) = 0 :=
    (htfae.out 3 1).mp hle
  have hsumproj :
      IsStarProjection ((inner ℬ (e i₁) (e i₁) : ℬ) + inner ℬ (e i₂) (e i₂)) :=
    (htfae.out 3 5).mp hle
  -- **149III** `mod-projelabs` in coefficient form: `⟨eᵢ,x⟩⟨eᵢ,eᵢ⟩ = ⟨eᵢ,x⟩`
  have hcoef : ∀ (i : ι) (x : X),
      (inner ℬ (e i) x : ℬ) * inner ℬ (e i) (e i) = inner ℬ (e i) x := by
    intro i x
    calc (inner ℬ (e i) x : ℬ) * inner ℬ (e i) (e i)
        = inner ℬ ((inner ℬ (e i) (e i) : ℬ) • e i) x := by
          rw [CStarModule.inner_op_smul_left, (hpr i).isSelfAdjoint.star_eq]
      _ = inner ℬ (e i) x := by rw [mod_projelabs (e i) (hpr i)]
  -- "$e_2 \langle e_1, x\rangle = e_2 p_2 \langle e_1, x\rangle = 0$"
  have hkill : ∀ i j : ι, (inner ℬ (e i) (e i) : ℬ) * inner ℬ (e j) (e j) = 0 →
      ∀ x : X, (inner ℬ (e i) x : ℬ) • e j = 0 := by
    intro i j hij x
    have h1 : (inner ℬ (e i) x : ℬ) * inner ℬ (e j) (e j) = 0 := by
      conv_lhs => rw [← hcoef i x]
      rw [mul_assoc, hij, mul_zero]
    calc (inner ℬ (e i) x : ℬ) • e j
        = (inner ℬ (e i) x : ℬ) • ((inner ℬ (e j) (e j) : ℬ) • e j) := by
          rw [mod_projelabs (e j) (hpr j)]
      _ = ((inner ℬ (e i) x : ℬ) * inner ℬ (e j) (e j)) • e j :=
          (op_mul_smul _ _ _).symm
      _ = 0 := by rw [h1, op_zero_smul]
  -- "$(e_1+e_2)\langle e_1+e_2,x\rangle = e_1\langle e_1,x\rangle
  --    + e_2 \langle e_2,x\rangle$"
  have hpairsum : ∀ x : X, (inner ℬ (e i₁ + e i₂) x : ℬ) • (e i₁ + e i₂)
      = (inner ℬ (e i₁) x : ℬ) • e i₁ + (inner ℬ (e i₂) x : ℬ) • e i₂ := by
    intro x
    rw [CStarModule.inner_add_left, op_add_smul, op_smul_add, op_smul_add,
      hkill i₁ i₂ h12 x, hkill i₂ i₁ h21 x, add_zero, zero_add]
  have hdiag : (inner ℬ (e i₁ + e i₂) (e i₁ + e i₂) : ℬ)
      = inner ℬ (e i₁) (e i₁) + inner ℬ (e i₂) (e i₂) := by
    rw [CStarModule.inner_add_left, CStarModule.inner_add_right,
      CStarModule.inner_add_right, horth i₁ i₂ hne, horth i₂ i₁ hne.symm]
    abel
  have hoff : ∀ j : ι, j ≠ i₁ → j ≠ i₂ →
      (inner ℬ (e i₁ + e i₂) (e j) : ℬ) = 0 ∧
      (inner ℬ (e j) (e i₁ + e i₂) : ℬ) = 0 := by
    intro j hj1 hj2
    refine ⟨?_, ?_⟩
    · rw [CStarModule.inner_add_left, horth i₁ j (Ne.symm hj1),
        horth i₂ j (Ne.symm hj2), add_zero]
    · rw [CStarModule.inner_add_right, horth j i₁ hj1, horth j i₂ hj2, add_zero]
  -- the reindexing `Finset {i // i ≠ i₂} → Finset ι`
  set g : Finset {i : ι // i ≠ i₂} → Finset ι :=
    fun s => if i₁' ∈ s then insert i₂ (s.image Subtype.val) else s.image Subtype.val
    with hgdef
  have hvalinj : Function.Injective (Subtype.val : {i : ι // i ≠ i₂} → ι) :=
    Subtype.val_injective
  have hi₂notmem : ∀ s : Finset {i : ι // i ≠ i₂}, i₂ ∉ s.image Subtype.val := by
    intro s hmem
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hmem
    exact a.2 ha
  have hsplit : ∀ (v : {i : ι // i ≠ i₂} → X) (v' : ι → X),
      (∀ i : {i : ι // i ≠ i₂}, (i : ι) ≠ i₁ → v i = v' (i : ι)) →
      v i₁' = v' i₁ + v' i₂ →
      ∀ s : Finset {i : ι // i ≠ i₂}, ∑ i ∈ s, v i = ∑ j ∈ g s, v' j := by
    intro v v' hveq hvpair s
    by_cases hs : i₁' ∈ s
    · have hcong : ∀ i ∈ s.erase i₁', v i = v' (i : ι) := fun i hi =>
        hveq i fun hc => Finset.ne_of_mem_erase hi (Subtype.ext hc)
      rw [hgdef]
      simp only [if_pos hs]
      rw [Finset.sum_insert (hi₂notmem s),
        Finset.sum_image (fun a _ c _ h => hvalinj h),
        ← Finset.add_sum_erase s v hs,
        ← Finset.add_sum_erase s (fun i => v' (i : ι)) hs, hvpair,
        Finset.sum_congr rfl hcong]
      abel
    · have hcong : ∀ i ∈ s, v i = v' (i : ι) := by
        intro i hi
        refine hveq i fun hc => hs ?_
        have : i = i₁' := Subtype.ext hc
        rwa [← this]
      rw [hgdef]
      simp only [if_neg hs]
      rw [Finset.sum_image (fun a _ c _ h => hvalinj h)]
      exact Finset.sum_congr rfl hcong
  have hgtop : Tendsto g atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro t
    refine ⟨insert i₁' (t.subtype (fun j => j ≠ i₂)), fun s hs => ?_⟩
    have hmem : i₁' ∈ s := hs (Finset.mem_insert_self _ _)
    intro j hj
    rw [hgdef]
    simp only [if_pos hmem]
    by_cases hj2 : j = i₂
    · subst hj2; exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨j, hj2⟩, ?_, rfl⟩)
      exact hs (Finset.mem_insert_of_mem (Finset.mem_subtype.mpr hj))
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  -- "$E'$ is an orthogonal set"
  · intro i j hij
    by_cases hi : (i : ι) = i₁ <;> by_cases hj : (j : ι) = i₁
    · exact absurd (Subtype.ext (hi.trans hj.symm)) hij
    · rw [show f i = e i₁ + e i₂ by rw [hfdef]; simp [hi], hfelse j hj]
      exact (hoff (j : ι) hj j.2).1
    · rw [hfelse i hi, show f j = e i₁ + e i₂ by rw [hfdef]; simp [hj]]
      exact (hoff (i : ι) hi i.2).2
    · rw [hfelse i hi, hfelse j hj]
      exact horth _ _ fun hc => hij (Subtype.ext hc)
  -- "$\langle e_1+e_2, e_1+e_2\rangle = p_1 + p_2$ is a (non-zero) projection"
  · intro i
    by_cases hi : (i : ι) = i₁
    · rw [show f i = e i₁ + e i₂ by rw [hfdef]; simp [hi], hdiag]
      refine ⟨hsumproj, fun hzero => (hproj i₁).2 ?_⟩
      calc (inner ℬ (e i₁) (e i₁) : ℬ)
          = inner ℬ (e i₁) (e i₁) *
              (inner ℬ (e i₁) (e i₁) + inner ℬ (e i₂) (e i₂)) := by
            rw [mul_add, h12, add_zero, (hpr i₁).isIdempotentElem.eq]
        _ = 0 := by rw [hzero, mul_zero]
    · rw [hfelse i hi]; exact hproj _
  -- "$x = (e_1+e_2)\langle e_1+e_2,x\rangle + \sum_{e\in E} e\langle e,x\rangle$"
  · intro x ω
    have hkey : ∀ s : Finset {i : ι // i ≠ i₂},
        ∑ i ∈ s, (inner ℬ (f i) x : ℬ) • f i
          = ∑ j ∈ g s, (inner ℬ (e j) x : ℬ) • e j := by
      refine hsplit _ _ (fun i hi => by rw [hfelse i hi]) ?_
      rw [hfpair]; exact hpairsum x
    refine ((hexp x ω).comp hgtop).congr fun s => ?_
    simp only [Function.comp_apply, hkey s]
  -- "the second condition holds automatically as $E'$ is an orthonormal set"
  · intro b hb
    obtain ⟨M, hM⟩ := hb
    set b' : ι → ℬ := fun j => if h : j = i₂ then b i₁' else b ⟨j, h⟩ with hb'def
    have hb'val : ∀ i : {i : ι // i ≠ i₂}, b' (i : ι) = b i := by
      intro i; simp [hb'def, i.2]
    have hb'one : b' i₁ = b i₁' := by simp [hb'def, hne, hi₁']
    have hb'two : b' i₂ = b i₁' := by simp [hb'def]
    have himg : (t : Finset ι) → (t.subtype (fun j => j ≠ i₂)).image Subtype.val
        = t.erase i₂ := by
      intro t; ext j; simp [Finset.mem_erase, and_comm]
    have hsub : ∀ t : Finset ι, ∑ j ∈ t.erase i₂, b' j * star (b' j)
        = ∑ i ∈ t.subtype (fun j => j ≠ i₂), b i * star (b i) := by
      intro t
      rw [← himg t, Finset.sum_image (fun a _ c _ h => hvalinj h)]
      exact Finset.sum_congr rfl fun i _ => by rw [hb'val i]
    have hb'l2 : L2Summable ℬ b' := by
      refine ⟨M + ‖b i₁' * star (b i₁')‖, fun t => ?_⟩
      by_cases hi₂ : i₂ ∈ t
      · rw [← Finset.add_sum_erase t (fun j => b' j * star (b' j)) hi₂, hsub t,
          hb'two]
        calc ‖b i₁' * star (b i₁')
              + ∑ i ∈ t.subtype (fun j => j ≠ i₂), b i * star (b i)‖
            ≤ ‖b i₁' * star (b i₁')‖
              + ‖∑ i ∈ t.subtype (fun j => j ≠ i₂), b i * star (b i)‖ :=
              norm_add_le _ _
          _ ≤ ‖b i₁' * star (b i₁')‖ + M := by gcongr; exact hM _
          _ = M + ‖b i₁' * star (b i₁')‖ := add_comm _ _
      · rw [← Finset.erase_eq_of_notMem hi₂, hsub t]
        exact le_trans (hM _) (le_add_of_nonneg_right (norm_nonneg _))
    obtain ⟨x, hx⟩ := hl2 b' hb'l2
    refine ⟨x, fun ω => ?_⟩
    have hkey : ∀ s : Finset {i : ι // i ≠ i₂},
        ∑ i ∈ s, b i • f i = ∑ j ∈ g s, b' j • e j := by
      refine hsplit _ _ (fun i hi => by rw [hfelse i hi, hb'val i]) ?_
      rw [hfpair, hb'one, hb'two]
      exact op_smul_add _ _ _
    refine ((hx ω).comp hgtop).congr fun s => ?_
    simp only [Function.comp_apply, hkey s]

end L2

/-! ## Parsec 1620: comparison of projections and the normal form

**162I** (dils.tex:4708): introduction — nothing to formalize. -/

section NormalForm

variable {ℬ : Type u}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

variable (ℬ) in
/-- A von Neumann algebra is a **factor** when its centre is `ℂ1`
(**162II**). -/
def IsFactor : Prop :=
  ∀ z : ℬ, IsCentral ℬ z → ∃ c : ℂ, z = algebraMap ℂ ℬ c

/-- The Murray–von Neumann preorder `p ≲ q` on projections: `u* u = p` and
`u u* ≤ q` for some `u` (dils.tex:4708, recalled from vn.tex 83II). -/
def MvNLe (p q : ℬ) : Prop :=
  ∃ u : ℬ, star u * u = p ∧ u * star u ≤ q

section MvnLinking

variable [VonNeumannAlgebra ℬ]
variable (p q : ℬ)

/-! ### The Zorn argument of **162III**

The proof of 162II needs a fact the thesis states without proof (**89III**
`summing-partial-isometries`, vn.tex:6928, asks only for the *Hilbert space*
version — which is `summing_partial_isometries` in `A/VN` — and merely
asserts the von Neumann algebra case): the ultraweak
sum of a family of partial isometries with pairwise orthogonal initial and
pairwise orthogonal final projections is again a partial isometry.  We do
not build that sum.  Instead a partial isometry `u` with `u*u ≤ p` and
`uu* ≤ q` is encoded as the *linking projection*

  `½ [[u*u, u*], [u, uu*]] = ½ w* w`,   `w = [u, uu*] ∈ M₂(ℬ)`,

which is a projection of `M₂(ℬ)` (**49IV**.1) precisely because `u` is a
partial isometry, and which is monotone in `u` (extending `u` adds an
orthogonal linking projection).  Suprema of *directed sets of projections*
are supplied by the von Neumann axiom (**56XIV**), the corners of the
supremum are read off by normality of `M ↦ ∑ᵢⱼ aᵢ* Mᵢⱼ aⱼ` (**49IV**.2),
and the identity `R² = R` for the supremum gives back `v*v` and `vv*`.  So
Zorn's lemma can be applied to the *order* of `M₂(ℬ)` directly, and the
thesis's "maximal set `U` of partial isometries" becomes a maximal linking
projection. -/

/-- `matEmb i j x * matEmb k l y = 0` when `j ≠ k`. -/
private theorem matEmb_mul_zero {N : ℕ} (i j k l : Fin N) (h : j ≠ k) (x y : ℬ) :
    matEmb i j x * matEmb k l y = (0 : CStarMatrix (Fin N) (Fin N) ℬ) := by
  ext p q
  rw [CStarMatrix.mul_apply]
  simp only [matEmb_apply, ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [CStarMatrix.zero_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hp : p = i <;> by_cases hr : r = j <;> by_cases hr' : r = k <;>
    simp_all

/-- The row `w_u = [u, uu*]` in `M₂(ℬ)`. -/
private noncomputable def mvW (u : ℬ) : CStarMatrix (Fin 2) (Fin 2) ℬ :=
  matEmb 0 0 u + matEmb 0 1 (u * star u)

/-- The linking matrix `S_u = [[u*u, u*], [u, uu*]] = w_u* w_u`. -/
private noncomputable def mvMat (u : ℬ) : CStarMatrix (Fin 2) (Fin 2) ℬ :=
  star (mvW u) * mvW u

private theorem mvMat_expand {u : ℬ} (hu : IsPartialIsometry ℬ u) :
    mvMat u = matEmb 0 0 (star u * u) + matEmb 0 1 (star u) + matEmb 1 0 u
      + matEmb 1 1 (u * star u) := by
  have huu : u * star u * u = u := ((partial_isometry_equivalents u).out 0 2).mp hu
  have huu' : star u * u * star u = star u := ((partial_isometry_equivalents u).out 0 4).mp hu
  have h1 : star u * (u * star u) = star u := by rw [← mul_assoc]; exact huu'
  have h3 : u * star u * (u * star u) = u * star u := by
    rw [mul_assoc, ← mul_assoc (star u), huu']
  rw [mvMat, mvW, star_add, matEmb_star, matEmb_star, star_mul, star_star]
  rw [add_mul, mul_add, mul_add]
  simp only [matEmb_mul]
  rw [h1, huu, h3]
  abel

/-- Transfer of a normal map's `PreservesDirSups` to plain sets. -/
private theorem isLUB_image_of_preservesDirSups
    {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {f : A → B} (hf : PreservesDirSups f) {D : Set A} {R : A}
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (hsa : ∀ x ∈ D, IsSelfAdjoint x) (hR : IsLUB D R) :
    IsLUB (f '' D) (f R) := by
  obtain ⟨d₀, hd₀⟩ := hne
  have hRsa : IsSelfAdjoint R := by
    have h := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr (hR.1 hd₀))
    simpa using h.add (hsa d₀ hd₀)
  set D' : Set (selfAdjoint A) := {d : selfAdjoint A | (d : A) ∈ D} with hD'def
  have hval : Subtype.val '' D' = D := by
    ext x
    exact ⟨by rintro ⟨d, hd, rfl⟩; exact hd,
      fun hx => ⟨⟨x, hsa x hx⟩, hx, rfl⟩⟩
  have hne' : D'.Nonempty := ⟨⟨d₀, hsa d₀ hd₀⟩, hd₀⟩
  have hdir' : DirectedOn (· ≤ ·) D' := by
    intro x hx y hy
    obtain ⟨z, hz, hxz, hyz⟩ := hdir _ hx _ hy
    exact ⟨⟨z, hsa z hz⟩, hz, hxz, hyz⟩
  have hR' : IsLUB D' (⟨R, hRsa⟩ : selfAdjoint A) :=
    isLUB_sa_of_isLUB (by rw [hval]; exact hR)
  have h := hf D' ⟨R, hRsa⟩ hne' hdir' hR'
  have himg : (fun d : selfAdjoint A => f (d : A)) '' D' = f '' D := by
    rw [← hval, Set.image_image]
  rwa [himg] at h

private theorem preservesDirSups_matForm (a : Fin 2 → ℬ) :
    PreservesDirSups (fun M : CStarMatrix (Fin 2) (Fin 2) ℬ => matForm a a M) :=
  (mn_vna_2 (A := ℬ) 2 a a).2.2

/-- The vector `√2 e_i ∈ ℬ²`. -/
private noncomputable def dblVec (i : Fin 2) : Fin 2 → ℬ :=
  fun k => if k = i then ((Real.sqrt 2 : ℝ) : ℂ) • (1 : ℬ) else 0

private theorem matForm_dblVec (i : Fin 2) (M : CStarMatrix (Fin 2) (Fin 2) ℬ) :
    matForm (dblVec i) (dblVec i) M = (2 : ℂ) • M i i := by
  have hc : (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)) = (2 : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  simp only [matForm, dblVec, apply_ite star, star_zero, star_smul, star_one,
    Complex.star_def, Complex.conj_ofReal, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul, hc]


/-- The linking projection `½[[u*u, u*],[u, uu*]]`. -/
private noncomputable def mvP (u : ℬ) : CStarMatrix (Fin 2) (Fin 2) ℬ := (2 : ℂ)⁻¹ • mvMat u

private theorem mvMat_mul_self (u : ℬ) (hu : IsPartialIsometry ℬ u) :
    mvMat u * mvMat u = mvMat u + mvMat u := by
  have huu : u * star u * u = u := ((partial_isometry_equivalents u).out 0 2).mp hu
  have hff : u * star u * (u * star u) = u * star u := by
    have huu' : star u * u * star u = star u :=
      ((partial_isometry_equivalents u).out 0 4).mp hu
    rw [mul_assoc, ← mul_assoc (star u), huu']
  have hstarW : star (mvW u) = matEmb 0 0 (star u) + matEmb 1 0 (u * star u) := by
    rw [mvW, star_add, matEmb_star, matEmb_star, star_mul, star_star]
  have h1 : mvW u * star (mvW u)
      = matEmb 0 0 (u * star u) + matEmb 0 0 (u * star u) := by
    rw [hstarW, mvW, add_mul, mul_add, mul_add]
    simp only [matEmb_mul, matEmb_mul_zero _ _ _ _ (by decide : (0 : Fin 2) ≠ 1),
      matEmb_mul_zero _ _ _ _ (by decide : (1 : Fin 2) ≠ 0)]
    rw [hff, add_zero, zero_add]
  have hww : mvW u * star (mvW u) * mvW u = mvW u + mvW u := by
    rw [h1, mvW]
    simp only [add_mul, mul_add, matEmb_mul]
    rw [huu, hff]
    abel
  calc mvMat u * mvMat u
      = star (mvW u) * (mvW u * star (mvW u) * mvW u) := by
        rw [mvMat]; noncomm_ring
    _ = star (mvW u) * (mvW u + mvW u) := by rw [hww]
    _ = mvMat u + mvMat u := by rw [mul_add]; rfl

private theorem mvMat_star (u : ℬ) : star (mvMat u) = mvMat u := by
  rw [mvMat, star_mul, star_star]

private theorem mvP_isStarProjection {u : ℬ} (hu : IsPartialIsometry ℬ u) :
    IsStarProjection (mvP u) := by
  constructor
  · show mvP u * mvP u = mvP u
    rw [mvP, smul_mul_smul_comm, mvMat_mul_self u hu, ← two_smul ℂ (mvMat u),
      smul_smul]
    norm_num
  · show star (mvP u) = mvP u
    rw [mvP, star_smul, mvMat_star]
    norm_num [Complex.star_def]

private theorem mvP_apply {u : ℬ} (hu : IsPartialIsometry ℬ u) :
    mvP u 0 0 = (2 : ℂ)⁻¹ • (star u * u) ∧ mvP u 0 1 = (2 : ℂ)⁻¹ • star u ∧
      mvP u 1 0 = (2 : ℂ)⁻¹ • u ∧ mvP u 1 1 = (2 : ℂ)⁻¹ • (u * star u) := by
  rw [mvP, mvMat_expand hu]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [CStarMatrix.smul_apply, CStarMatrix.add_apply, matEmb_apply]


variable (p q : ℬ)

/-- Partial isometries from a subprojection of `p` onto one of `q`, encoded
as linking projections in `M₂(ℬ)`. -/
private def mvSet : Set (CStarMatrix (Fin 2) (Fin 2) ℬ) :=
  {R | ∃ u : ℬ, IsPartialIsometry ℬ u ∧ star u * u ≤ p ∧ u * star u ≤ q ∧ R = mvP u}

variable {p q}

set_option maxHeartbeats 1000000 in
private theorem isLUB_entry2 (i : Fin 2) {D : Set (CStarMatrix (Fin 2) (Fin 2) ℬ)}
    {R : CStarMatrix (Fin 2) (Fin 2) ℬ} (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hsa : ∀ x ∈ D, IsSelfAdjoint x) (hR : IsLUB D R) :
    IsLUB ((fun M : CStarMatrix (Fin 2) (Fin 2) ℬ => (2 : ℂ) • M i i) '' D)
      ((2 : ℂ) • R i i) := by
  have h := isLUB_image_of_preservesDirSups
    (A := CStarMatrix (Fin 2) (Fin 2) ℬ) (B := ℬ)
    (f := fun M : CStarMatrix (Fin 2) (Fin 2) ℬ => matForm (dblVec i) (dblVec i) M)
    (preservesDirSups_matForm (dblVec i)) hne hdir hsa hR
  simpa only [matForm_dblVec] using h

private theorem entry2_mono {M N : CStarMatrix (Fin 2) (Fin 2) ℬ} (h : M ≤ N) (i : Fin 2) :
    (2 : ℂ) • M i i ≤ (2 : ℂ) • N i i := by
  have h2 := matForm_mono h (dblVec i)
  rwa [matForm_dblVec, matForm_dblVec] at h2

private theorem mvSet_chain_bound (hp : IsStarProjection p) (hq : IsStarProjection q)
    (c : Set (CStarMatrix (Fin 2) (Fin 2) ℬ)) (hc : c ⊆ mvSet p q)
    (hchain : IsChain (· ≤ ·) c) :
    ∃ R ∈ mvSet p q, ∀ z ∈ c, z ≤ R := by
  have hzeropi : IsPartialIsometry ℬ (0 : ℬ) :=
    ((partial_isometry_equivalents (0 : ℬ)).out 1 0).mp
      (by simpa using (⟨by simp, by simp⟩ : IsStarProjection (0 : ℬ)))
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨mvP 0, ⟨0, hzeropi, by simpa using hp.nonneg, by simpa using hq.nonneg, rfl⟩,
      by simp⟩
  have hproj : ∀ M ∈ c, IsStarProjection M := by
    rintro M hM
    obtain ⟨u, hu, -, -, rfl⟩ := hc hM
    exact mvP_isStarProjection hu
  have hdir : DirectedOn (· ≤ ·) c := by
    intro x hx y hy
    rcases eq_or_ne x y with rfl | hxy
    · exact ⟨x, hx, le_refl x, le_refl x⟩
    rcases hchain hx hy hxy with h | h
    · exact ⟨y, hy, h, le_refl y⟩
    · exact ⟨x, hx, le_refl x, h⟩
  have hRlub : IsLUB c (projSup c) := isLUB_projSup_of_directed c hproj hne hdir
  have hRproj : IsStarProjection (projSup c) := (projSup_spec hproj).1
  set R : CStarMatrix (Fin 2) (Fin 2) ℬ := projSup c with hRdef
  -- the two diagonal entries, doubled
  have hlub : ∀ i : Fin 2,
      IsLUB ((fun M : CStarMatrix (Fin 2) (Fin 2) ℬ => (2 : ℂ) • M i i) '' c)
        ((2 : ℂ) • R i i) := by
    intro i
    exact isLUB_entry2 i hne hdir (fun x hx => (hproj x hx).isSelfAdjoint) hRlub
  have himgne : ∀ i : Fin 2,
      ((fun M : CStarMatrix (Fin 2) (Fin 2) ℬ => (2 : ℂ) • M i i) '' c).Nonempty := by
    intro i; exact hne.image _
  have himgdir : ∀ i : Fin 2,
      DirectedOn (· ≤ ·) ((fun M : CStarMatrix (Fin 2) (Fin 2) ℬ => (2 : ℂ) • M i i) '' c) := by
    rintro i _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
    obtain ⟨K, hK, hMK, hNK⟩ := hdir M hM N hN
    exact ⟨_, ⟨K, hK, rfl⟩, entry2_mono hMK i, entry2_mono hNK i⟩
  have himg0 : ∀ x ∈ (fun M : CStarMatrix (Fin 2) (Fin 2) ℬ => (2 : ℂ) • M 0 0) '' c,
      IsStarProjection x ∧ x ≤ p := by
    rintro _ ⟨M, hM, rfl⟩
    obtain ⟨u, hu, hup, huq, rfl⟩ := hc hM
    have hval : (2 : ℂ) • mvP u 0 0 = star u * u := by
      rw [(mvP_apply hu).1, smul_smul]; norm_num
    show IsStarProjection ((2 : ℂ) • mvP u 0 0) ∧ (2 : ℂ) • mvP u 0 0 ≤ p
    rw [hval]
    exact ⟨((partial_isometry_equivalents u).out 0 1).mp hu, hup⟩
  have himg1 : ∀ x ∈ (fun M : CStarMatrix (Fin 2) (Fin 2) ℬ => (2 : ℂ) • M 1 1) '' c,
      IsStarProjection x ∧ x ≤ q := by
    rintro _ ⟨M, hM, rfl⟩
    obtain ⟨u, hu, hup, huq, rfl⟩ := hc hM
    have hval : (2 : ℂ) • mvP u 1 1 = u * star u := by
      rw [(mvP_apply hu).2.2.2, smul_smul]; norm_num
    show IsStarProjection ((2 : ℂ) • mvP u 1 1) ∧ (2 : ℂ) • mvP u 1 1 ≤ q
    rw [hval]
    exact ⟨((partial_isometry_equivalents u).out 0 3).mp hu, huq⟩
  have heproj : IsStarProjection ((2 : ℂ) • R 0 0) :=
    vna_directed_supremum_projections _ _ (fun x hx => (himg0 x hx).1) (himgne 0)
      (himgdir 0) (hlub 0)
  have hfproj : IsStarProjection ((2 : ℂ) • R 1 1) :=
    vna_directed_supremum_projections _ _ (fun x hx => (himg1 x hx).1) (himgne 1)
      (himgdir 1) (hlub 1)
  have hep : (2 : ℂ) • R 0 0 ≤ p := (hlub 0).2 fun x hx => (himg0 x hx).2
  have hfq : (2 : ℂ) • R 1 1 ≤ q := (hlub 1).2 fun x hx => (himg1 x hx).2
  -- the matrix identities
  have hmul : ∀ i j : Fin 2, R i 0 * R 0 j + R i 1 * R 1 j = R i j := by
    intro i j
    have h := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) ℬ => M i j)
      hRproj.isIdempotentElem.eq
    simpa [CStarMatrix.mul_apply, Fin.sum_univ_two] using h
  have hR01 : R 0 1 = star (R 1 0) := by
    conv_lhs => rw [← hRproj.isSelfAdjoint.star_eq]
    rw [CStarMatrix.star_apply]
  have hstar2 : ∀ x : ℬ, star ((2 : ℂ) • x) = (2 : ℂ) • star x := by
    intro x; rw [star_smul]; norm_num [Complex.star_def]
  have hvv : star ((2 : ℂ) • R 1 0) * ((2 : ℂ) • R 1 0) = (2 : ℂ) • R 0 0 := by
    have h00 : R 0 1 * R 1 0 = R 0 0 - R 0 0 * R 0 0 := eq_sub_of_add_eq' (hmul 0 0)
    have hee : ((2 : ℂ) • R 0 0) * ((2 : ℂ) • R 0 0) = (2 : ℂ) • R 0 0 :=
      heproj.isIdempotentElem.eq
    calc star ((2 : ℂ) • R 1 0) * ((2 : ℂ) • R 1 0)
        = ((2 : ℂ) * (2 : ℂ)) • (R 0 1 * R 1 0) := by
          rw [hstar2, smul_mul_smul_comm, hR01]
      _ = ((2 : ℂ) * 2) • R 0 0 - ((2 : ℂ) * 2) • (R 0 0 * R 0 0) := by
          rw [h00, smul_sub]
      _ = ((2 : ℂ) * 2) • R 0 0 - ((2 : ℂ) • R 0 0) * ((2 : ℂ) • R 0 0) := by
          rw [smul_mul_smul_comm]
      _ = (2 : ℂ) • R 0 0 := by
          rw [hee, ← sub_smul]; norm_num
  have hff : ((2 : ℂ) • R 1 0) * star ((2 : ℂ) • R 1 0) = (2 : ℂ) • R 1 1 := by
    have h11 : R 1 0 * R 0 1 = R 1 1 - R 1 1 * R 1 1 := eq_sub_of_add_eq (hmul 1 1)
    have hee : ((2 : ℂ) • R 1 1) * ((2 : ℂ) • R 1 1) = (2 : ℂ) • R 1 1 :=
      hfproj.isIdempotentElem.eq
    calc ((2 : ℂ) • R 1 0) * star ((2 : ℂ) • R 1 0)
        = ((2 : ℂ) * (2 : ℂ)) • (R 1 0 * R 0 1) := by
          rw [hstar2, smul_mul_smul_comm, hR01]
      _ = ((2 : ℂ) * 2) • R 1 1 - ((2 : ℂ) * 2) • (R 1 1 * R 1 1) := by
          rw [h11, smul_sub]
      _ = ((2 : ℂ) * 2) • R 1 1 - ((2 : ℂ) • R 1 1) * ((2 : ℂ) • R 1 1) := by
          rw [smul_mul_smul_comm]
      _ = (2 : ℂ) • R 1 1 := by
          rw [hee, ← sub_smul]; norm_num
  have hvpi : IsPartialIsometry ℬ ((2 : ℂ) • R 1 0) :=
    ((partial_isometry_equivalents _).out 1 0).mp (by rw [hvv]; exact heproj)
  refine ⟨R, ⟨(2 : ℂ) • R 1 0, hvpi, by rw [hvv]; exact hep, by rw [hff]; exact hfq, ?_⟩,
    fun z hz => hRlub.1 hz⟩
  obtain ⟨h1, h2, h3, h4⟩ := mvP_apply hvpi
  rw [hvv] at h1
  rw [hff] at h4
  ext i j
  fin_cases i <;> fin_cases j
  · show R 0 0 = mvP ((2 : ℂ) • R 1 0) 0 0
    rw [h1, smul_smul]; norm_num
  · show R 0 1 = mvP ((2 : ℂ) • R 1 0) 0 1
    rw [h2, hstar2, smul_smul]; norm_num [hR01]
  · show R 1 0 = mvP ((2 : ℂ) • R 1 0) 1 0
    rw [h3, smul_smul]; norm_num
  · show R 1 1 = mvP ((2 : ℂ) • R 1 0) 1 1
    rw [h4, smul_smul]; norm_num


private theorem mvn_proj_mul_eq {e r : ℬ} (hr : IsStarProjection r) (he : IsStarProjection e)
    (h : e ≤ r) : r * e = e ∧ e * r = e :=
  ⟨((projection_below_effect r e ⟨hr.nonneg, hr.le_one⟩ he).out 0 6).mp h,
    ((projection_below_effect r e ⟨hr.nonneg, hr.le_one⟩ he).out 0 7).mp h⟩

private theorem mvn_proj_sub {r e : ℬ} (hr : IsStarProjection r) (he : IsStarProjection e)
    (h : e ≤ r) : IsStarProjection (r - e) := by
  obtain ⟨h1, h2⟩ := mvn_proj_mul_eq hr he h
  constructor
  · show (r - e) * (r - e) = r - e
    rw [sub_mul, mul_sub, mul_sub, h1, h2, hr.isIdempotentElem.eq, he.isIdempotentElem.eq]
    abel
  · show star (r - e) = r - e
    rw [star_sub, hr.isSelfAdjoint.star_eq, he.isSelfAdjoint.star_eq]

private theorem mvn_proj_orth {r g k : ℬ} (hr : IsStarProjection r)
    (hg : IsStarProjection g) (hk : IsStarProjection k) (hgr : g ≤ r)
    (hkr : k ≤ r - g) : g * k = 0 := by
  have hsub : (0 : ℬ) ≤ r - g := sub_nonneg.mpr hgr
  have hsub1 : r - g ≤ 1 := le_trans (sub_le_self _ hg.nonneg) hr.le_one
  have h1 : (r - g) * k = k :=
    ((projection_below_effect (r - g) k ⟨hsub, hsub1⟩ hk).out 0 6).mp hkr
  have hgr' : g * r = g := (mvn_proj_mul_eq hr hg hgr).2
  calc g * k = g * ((r - g) * k) := by rw [h1]
    _ = (g * r - g * g) * k := by noncomm_ring
    _ = 0 := by rw [hgr', hg.isIdempotentElem.eq, sub_self, zero_mul]

private theorem mvn_proj_add {e g : ℬ} (he : IsStarProjection e) (hg : IsStarProjection g)
    (h1 : e * g = 0) (h2 : g * e = 0) : IsStarProjection (e + g) := by
  constructor
  · show (e + g) * (e + g) = e + g
    rw [add_mul, mul_add, mul_add, h1, h2, he.isIdempotentElem.eq, hg.isIdempotentElem.eq]
    abel
  · show star (e + g) = e + g
    rw [star_add, he.isSelfAdjoint.star_eq, hg.isSelfAdjoint.star_eq]

end MvnLinking

/-- **162II** (`total-mv-order`, dils.tex:4717, Proposition): in a factor,
any two projections are comparable: `p ≲ q` or `q ≲ p`.

**162III** is the proof; see the section note above for the one divergence
(the thesis's `∑_{u ∈ U} u` is replaced by a maximal linking projection in
`M₂(ℬ)`, which avoids `summing-partial-isometries`). -/
theorem total_mv_order [VonNeumannAlgebra ℬ] (hF : IsFactor ℬ) (p q : ℬ)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    MvNLe p q ∨ MvNLe q p := by
  obtain ⟨R, hmax⟩ := zorn_le₀ (mvSet p q)
    fun c hc hchain => mvSet_chain_bound hp hq c hc hchain
  obtain ⟨u, hu, hup, huq, hRu⟩ := hmax.1
  have heproj : IsStarProjection (star u * u) :=
    ((partial_isometry_equivalents u).out 0 1).mp hu
  have hfproj : IsStarProjection (u * star u) :=
    ((partial_isometry_equivalents u).out 0 3).mp hu
  by_cases hpe : star u * u = p
  · exact Or.inl ⟨u, hpe, huq⟩
  by_cases hqf : u * star u = q
  · exact Or.inr ⟨star u, by rw [star_star]; exact hqf, by rw [star_star]; exact hup⟩
  exfalso
  have hp₀proj : IsStarProjection (p - star u * u) := mvn_proj_sub hp heproj hup
  have hq₀proj : IsStarProjection (q - u * star u) := mvn_proj_sub hq hfproj huq
  have hp₀ne : p - star u * u ≠ 0 := sub_ne_zero.mpr (Ne.symm hpe)
  have hq₀ne : q - u * star u ≠ 0 := sub_ne_zero.mpr (Ne.symm hqf)
  -- **162III**: in a factor the central carrier of `q₀` is `1`
  obtain ⟨a, ha⟩ : ∃ a : ℬ, (q - u * star u) * a * (p - star u * u) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hzproj : IsStarProjection (cceil (q - u * star u)) := (cceil_isLeast _).1.1
    have hzone : cceil (q - u * star u) = 1 := by
      obtain ⟨c, hc⟩ := hF _ (cceil_isLeast _).1.2.1
      haveI : Nontrivial ℬ := nontrivial_of_ne _ _ hq₀ne
      have hcc : c * c = c := by
        have hid := hzproj.isIdempotentElem.eq
        rw [hc, ← map_mul] at hid
        exact (algebraMap ℂ ℬ).injective hid
      have hc01 : c = 0 ∨ c = 1 := by
        have h0 : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hcc, sub_self]
        rcases mul_eq_zero.mp h0 with h | h
        · exact Or.inl h
        · exact Or.inr (sub_eq_zero.mp h)
      rcases hc01 with rfl | rfl
      · exfalso
        refine hq₀ne (le_antisymm ?_ hq₀proj.nonneg)
        have hle : q - u * star u ≤ cceil (q - u * star u) :=
          ((cceil_fundamental _ hq₀proj).1.1).2.2
        rwa [hc, map_zero] at hle
      · rw [hc, map_one]
    have hub : cceil (q - u * star u) ≤ 1 - (p - star u * u) := by
      have hPproj : ∀ x ∈ {x : ℬ | ∃ a : ℬ, x = ceil (star a * (q - u * star u) * a)},
          IsStarProjection x := by
        rintro _ ⟨b, rfl⟩
        exact (ceil_spec (star_left_conjugate_nonneg hq₀proj.nonneg b)).1
      rw [(cceil_fundamental _ hq₀proj).2]
      refine (projSup_spec hPproj).2.2 _ hp₀proj.one_sub ?_
      rintro _ ⟨b, rfl⟩
      refine (ceil_le_iff (star_left_conjugate_nonneg hq₀proj.nonneg b)
        hp₀proj.one_sub).mpr ?_
      have hz : star b * (q - u * star u) * b * (p - star u * u) = 0 := by
        calc star b * (q - u * star u) * b * (p - star u * u)
            = star b * ((q - u * star u) * b * (p - star u * u)) := by noncomm_ring
          _ = 0 := by rw [hcon b, mul_zero]
      rw [mul_sub, mul_one, hz, sub_zero]
    rw [hzone] at hub
    refine hp₀ne (le_antisymm ?_ hp₀proj.nonneg)
    have h := sub_nonneg.mpr hub
    simpa using h
  -- the new partial isometry u0 = [q0 a p0] (82I, polar decomposition)
  obtain ⟨b, hbdef⟩ : ∃ b : ℬ, b = (q - u * star u) * a * (p - star u * u) := ⟨_, rfl⟩
  rw [← hbdef] at ha
  obtain ⟨v, hvdef⟩ : ∃ v : ℬ, v = polar b := ⟨_, rfl⟩
  have hvpi : IsPartialIsometry ℬ v := by rw [hvdef]; exact (polar_decomposition_1 b).1
  have he₀proj : IsStarProjection (star v * v) :=
    ((partial_isometry_equivalents v).out 0 1).mp hvpi
  have hf₀proj : IsStarProjection (v * star v) :=
    ((partial_isometry_equivalents v).out 0 3).mp hvpi
  have he₀le : star v * v ≤ p - star u * u := by
    rw [hvdef, (polar_decomposition_1 b).2.1]
    calc suppProj b ≤ suppProj (p - star u * u) := by
          rw [hbdef]; exact suppProj_mul_le _ _
      _ = p - star u * u := suppProj_of_isStarProjection hp₀proj
  have hf₀le : v * star v ≤ q - u * star u := by
    rw [hvdef, (polar_decomposition_1 b).2.2]
    calc rangeProj b = rangeProj ((q - u * star u) * (a * (p - star u * u))) := by
          rw [hbdef, mul_assoc]
      _ ≤ rangeProj (q - u * star u) := rangeProj_mul_le _ _
      _ = q - u * star u := rangeProj_of_isStarProjection hq₀proj
  have hvne : v ≠ 0 := by
    intro h0
    refine ha ?_
    -- `Theses.A.VN.polar_decomposition`; `polar_decomposition` alone resolves to
    -- the Hilbert-module version of `HilbertModules.lean` inside this namespace
    have hb := (Theses.A.VN.polar_decomposition b).2.1
    rw [← hvdef, h0, zero_mul] at hb
    exact hb
  -- u and v have orthogonal initial and final projections
  have hee₀ : star u * u * (star v * v) = 0 :=
    mvn_proj_orth hp heproj he₀proj hup he₀le
  have hff₀ : u * star u * (v * star v) = 0 :=
    mvn_proj_orth hq hfproj hf₀proj huq hf₀le
  have hee₀' : star v * v * (star u * u) = 0 := by
    have h := congrArg star hee₀
    rwa [star_mul, he₀proj.isSelfAdjoint.star_eq, heproj.isSelfAdjoint.star_eq,
      star_zero] at h
  have huf : star u * (u * star u) = star u := by
    rw [← mul_assoc]; exact ((partial_isometry_equivalents u).out 0 4).mp hu
  have hue : u * (star u * u) = u := by
    rw [← mul_assoc]; exact ((partial_isometry_equivalents u).out 0 2).mp hu
  have hvf : v * star v * v = v := ((partial_isometry_equivalents v).out 0 2).mp hvpi
  have hve : star v * v * star v = star v := ((partial_isometry_equivalents v).out 0 4).mp hvpi
  have hc1 : star u * v = 0 := by
    calc star u * v = star u * (u * star u) * (v * star v * v) := by rw [huf, hvf]
      _ = star u * (u * star u * (v * star v)) * v := by noncomm_ring
      _ = 0 := by rw [hff₀, mul_zero, zero_mul]
  have hc2 : star v * u = 0 := by
    have h := congrArg star hc1
    rwa [star_mul, star_star, star_zero] at h
  have hc3 : u * star v = 0 := by
    calc u * star v = u * (star u * u) * (star v * v * star v) := by rw [hue, hve]
      _ = u * (star u * u * (star v * v)) * star v := by noncomm_ring
      _ = 0 := by rw [hee₀, mul_zero, zero_mul]
  have hc4 : v * star u = 0 := by
    have h := congrArg star hc3
    rwa [star_mul, star_star, star_zero] at h
  have hsum1 : star (u + v) * (u + v) = star u * u + star v * v := by
    rw [star_add, add_mul, mul_add, mul_add, hc1, hc2]; abel
  have hsum2 : (u + v) * star (u + v) = u * star u + v * star v := by
    rw [star_add, add_mul, mul_add, mul_add, hc3, hc4]; abel
  have hupi' : IsPartialIsometry ℬ (u + v) := by
    refine ((partial_isometry_equivalents (u + v)).out 1 0).mp ?_
    rw [hsum1]
    exact mvn_proj_add heproj he₀proj hee₀ hee₀'
  have hupp : star (u + v) * (u + v) ≤ p := by
    rw [hsum1]
    calc star u * u + star v * v ≤ star u * u + (p - star u * u) :=
          add_le_add le_rfl he₀le
      _ = p := by abel
  have hupq : (u + v) * star (u + v) ≤ q := by
    rw [hsum2]
    calc u * star u + v * star v ≤ u * star u + (q - u * star u) :=
          add_le_add le_rfl hf₀le
      _ = q := by abel
  have hmvsum : mvP (u + v) = mvP u + mvP v := by
    rw [mvP, mvP, mvP, ← smul_add, mvMat_expand hupi', mvMat_expand hu, mvMat_expand hvpi,
      hsum1, hsum2, star_add]
    simp only [matEmb_add]
    abel
  have hle : R ≤ mvP (u + v) := by
    rw [hRu, hmvsum]
    exact le_add_of_nonneg_right (mvP_isStarProjection hvpi).nonneg
  have hge : mvP (u + v) ≤ R := hmax.2 ⟨u + v, hupi', hupp, hupq, rfl⟩ hle
  have heq : mvP u + mvP v = mvP u := by
    rw [← hmvsum, ← hRu]
    exact le_antisymm hge hle
  have hzero : mvP v = 0 := by
    have h : mvP v = mvP u + mvP v - mvP u := by abel
    rw [heq, sub_self] at h
    exact h
  refine hvne ?_
  have h10 := (mvP_apply hvpi).2.2.1
  rw [hzero] at h10
  have hhalf : (2 : ℂ)⁻¹ • v = 0 := by
    rw [← h10]; rfl
  have h2 := congrArg (fun x : ℬ => (2 : ℂ) • x) hhalf
  simpa [smul_smul] using h2

variable {X : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X]

/-- **162IV** (`selfdual-normalish-form`, dils.tex:4747, Theorem): every
self-dual Hilbert ℬ-module over a factor `ℬ` is isomorphic to
`ℓ²((1)_{α∈κ})` for an infinite cardinal `κ`, or to `ℓ²((1,…,1,p))` for
some `n ∈ ℕ` and projection `p`.  Stated through bases (cf. **161II**):
`X` has an orthonormal basis `(eᵢ)` such that either `⟨eᵢ,eᵢ⟩ = 1` for all
`i`, or the basis is finite and `⟨eᵢ,eᵢ⟩ = 1` for all but (at most) one
index.

**162V**–**162VII** are the proof; **162VIII** (dils.tex:4908, discussion
of non-uniqueness of κ) — not converted. -/
theorem selfdual_normalish_form [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hF : IsFactor ℬ) (hX : SelfDual ℬ X) :
    ∃ (ι : Type v) (e : ι → X), IsONBasis ℬ e ∧
      ((∀ i, inner ℬ (e i) (e i) = 1) ∨
        (Finite ι ∧ ∃ i₀ : ι, ∀ i, i ≠ i₀ → inner ℬ (e i) (e i) = 1)) :=
  sorry

end NormalForm

/-! ## Parsec 1630: the completion is determined by its universal property

**163I** (dils.tex:4927): introduction; **163III** is the proof — not
converted. -/

section CompletionDefining

variable {ℬ : Type u} {V : Type v}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [AddCommGroup V] [Module ℂ V] [SMul ℬ V]

/-- **163II** (`selfdual-compl-defining`, dils.tex:4935, Proposition),
uniqueness half: two self-dual completions of the same 𝒷-module with
𝒷-valued inner product (each has the universal property by **151Ia**) are
isomorphic by a unique inner-product-preserving module isomorphism
commuting with the embeddings. -/
theorem selfdual_compl_defining_unique [VonNeumannAlgebra ℬ]
    (B : BInner ℬ V) (E₁ E₂ : SelfDualCompletion.{u, v, v} B) :
    ∃! U : E₁.X → E₂.X,
      (∃ C : ℝ, IsBoundedModuleMap (cstarBInner ℬ E₁.X)
        (cstarBInner ℬ E₂.X) C U) ∧
      Function.Bijective U ∧
      (∀ x y : E₁.X, inner ℬ (U x) (U y) = inner ℬ x y) ∧
      ∀ v : V, U (E₁.η v) = E₂.η v := by
  classical
  -- both embeddings are bounded module maps, with constant `1`
  have hb₁ : IsBoundedModuleMap B (cstarBInner ℬ E₁.X) 1 E₁.η :=
    ⟨E₁.η_add, E₁.η_smul_complex, E₁.η_smul, fun v => by
      have h : (cstarBInner ℬ E₁.X).norm (E₁.η v) = B.norm v := by
        show Real.sqrt ‖(inner ℬ (E₁.η v) (E₁.η v) : ℬ)‖ = Real.sqrt ‖B.inner v v‖
        rw [E₁.η_inner]
      rw [h, one_mul]⟩
  have hb₂ : IsBoundedModuleMap B (cstarBInner ℬ E₂.X) 1 E₂.η :=
    ⟨E₂.η_add, E₂.η_smul_complex, E₂.η_smul, fun v => by
      have h : (cstarBInner ℬ E₂.X).norm (E₂.η v) = B.norm v := by
        show Real.sqrt ‖(inner ℬ (E₂.η v) (E₂.η v) : ℬ)‖ = Real.sqrt ‖B.inner v v‖
        rw [E₂.η_inner]
      rw [h, one_mul]⟩
  -- **151Ia** in both directions, and for the identity
  obtain ⟨U, ⟨⟨CU, hU⟩, hUη⟩, hUuniq⟩ :=
    selfdual_completion_univ B E₁ E₂.selfDual 1 E₂.η hb₂
  obtain ⟨W, ⟨⟨CW, hW⟩, hWη⟩, -⟩ :=
    selfdual_completion_univ B E₂ E₁.selfDual 1 E₁.η hb₁
  obtain ⟨Z₁, -, hId₁⟩ := selfdual_completion_univ B E₁ E₁.selfDual 1 E₁.η hb₁
  obtain ⟨Z₂, -, hId₂⟩ := selfdual_completion_univ B E₂ E₂.selfDual 1 E₂.η hb₂
  set CU' : ℝ := max CU 0 with hCU'def
  set CW' : ℝ := max CW 0 with hCW'def
  have hCU'0 : (0 : ℝ) ≤ CU' := le_max_right _ _
  have hCW'0 : (0 : ℝ) ≤ CW' := le_max_right _ _
  have hU' : IsBoundedModuleMap (cstarBInner ℬ E₁.X) (cstarBInner ℬ E₂.X) CU' U :=
    { hU with
      bound := fun x => (hU.bound x).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) }
  have hW' : IsBoundedModuleMap (cstarBInner ℬ E₂.X) (cstarBInner ℬ E₁.X) CW' W :=
    { hW with
      bound := fun x => (hW.bound x).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) }
  -- `W ∘ U` and `U ∘ W` both factor the embeddings, hence are the identity
  have hWUb : IsBoundedModuleMap (cstarBInner ℬ E₁.X) (cstarBInner ℬ E₁.X)
      (CW' * CU') (fun x => W (U x)) :=
    { add := fun x y => by rw [hU.add, hW.add]
      smul_complex := fun c x => by rw [hU.smul_complex, hW.smul_complex]
      smul := fun b x => by rw [hU.smul, hW.smul]
      bound := fun x => (hW'.bound (U x)).trans (by
        calc CW' * (cstarBInner ℬ E₂.X).norm (U x)
            ≤ CW' * (CU' * (cstarBInner ℬ E₁.X).norm x) :=
              mul_le_mul_of_nonneg_left (hU'.bound x) hCW'0
          _ = CW' * CU' * (cstarBInner ℬ E₁.X).norm x := by ring) }
  have hUWb : IsBoundedModuleMap (cstarBInner ℬ E₂.X) (cstarBInner ℬ E₂.X)
      (CU' * CW') (fun y => U (W y)) :=
    { add := fun x y => by rw [hW.add, hU.add]
      smul_complex := fun c x => by rw [hW.smul_complex, hU.smul_complex]
      smul := fun b x => by rw [hW.smul, hU.smul]
      bound := fun x => (hU'.bound (W x)).trans (by
        calc CU' * (cstarBInner ℬ E₁.X).norm (W x)
            ≤ CU' * (CW' * (cstarBInner ℬ E₂.X).norm x) :=
              mul_le_mul_of_nonneg_left (hW'.bound x) hCU'0
          _ = CU' * CW' * (cstarBInner ℬ E₂.X).norm x := by ring) }
  have hIdb₁ : IsBoundedModuleMap (cstarBInner ℬ E₁.X) (cstarBInner ℬ E₁.X) 1
      (fun x : E₁.X => x) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun x => by rw [one_mul]⟩
  have hIdb₂ : IsBoundedModuleMap (cstarBInner ℬ E₂.X) (cstarBInner ℬ E₂.X) 1
      (fun x : E₂.X => x) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun x => by rw [one_mul]⟩
  have hWUid : ∀ x : E₁.X, W (U x) = x := by
    have h1 := hId₁ (fun x => W (U x))
      ⟨⟨CW' * CU', hWUb⟩, fun v => by
        show W (U (E₁.η v)) = E₁.η v
        rw [hUη, hWη]⟩
    have h2 := hId₁ (fun x : E₁.X => x) ⟨⟨1, hIdb₁⟩, fun _ => rfl⟩
    exact fun x => congrFun (h1.trans h2.symm) x
  have hUWid : ∀ y : E₂.X, U (W y) = y := by
    have h1 := hId₂ (fun y => U (W y))
      ⟨⟨CU' * CW', hUWb⟩, fun v => by
        show U (W (E₂.η v)) = E₂.η v
        rw [hWη, hUη]⟩
    have h2 := hId₂ (fun y : E₂.X => y) ⟨⟨1, hIdb₂⟩, fun _ => rfl⟩
    exact fun y => congrFun (h1.trans h2.symm) y
  have hbij : Function.Bijective U :=
    ⟨fun a b h => by rw [← hWUid a, ← hWUid b, h], fun y => ⟨W y, hUWid y⟩⟩
  -- `U` preserves the inner product: `U* U` and `id` have the same vector
  -- states on `η₁ V`, so **152IX**.2 identifies them
  have hUnorm : ∀ x : E₁.X, ‖U x‖ ≤ CU' * ‖x‖ := fun x => by
    have h := hU'.bound x
    rwa [cstarBInner_norm, cstarBInner_norm] at h
  let Ul : E₁.X →ₗ[ℂ] E₂.X :=
    { toFun := U, map_add' := hU.add, map_smul' := fun c x => hU.smul_complex c x }
  let Ucl : E₁.X →L[ℂ] E₂.X := Ul.mkContinuous CU' hUnorm
  obtain ⟨S, hS⟩ :=
    hilbmod_adjoint_exists E₁.selfDual Ucl (fun b x => hU.smul b x)
  have hSU : ∀ (x : E₁.X) (y : E₂.X), (inner ℬ (U x) y : ℬ) = inner ℬ x (S y) := hS
  have hadj : ModuleAdjointable ℬ (⇑(S.comp Ucl) : E₁.X → E₁.X) := by
    refine ⟨⇑(S.comp Ucl), fun x y => ?_⟩
    show (inner ℬ (S (U x)) y : ℬ) = inner ℬ x (S (U y))
    rw [← hSU x (U y), ← CStarModule.star_inner (A := ℬ) y (S (U x)),
      ← hSU y (U x), CStarModule.star_inner]
  have hadjId : ModuleAdjointable ℬ
      (⇑(ContinuousLinearMap.id ℂ E₁.X) : E₁.X → E₁.X) := ⟨id, fun _ _ => rfl⟩
  have hfix : S.comp Ucl = ContinuousLinearMap.id ℂ E₁.X := by
    refine hilmod_fixed_on_V_eq B E₁ _ _ hadj hadjId fun v => ?_
    show (inner ℬ (E₁.η v) (S (U (E₁.η v))) : ℬ) = inner ℬ (E₁.η v) (E₁.η v)
    rw [← hSU (E₁.η v) (U (E₁.η v)), hUη, E₂.η_inner, E₁.η_inner]
  have hip : ∀ x y : E₁.X, (inner ℬ (U x) (U y) : ℬ) = inner ℬ x y := by
    intro x y
    have hy : S (U y) = y := congrArg (fun F : E₁.X →L[ℂ] E₁.X => F y) hfix
    rw [hSU x (U y), hy]
  refine ⟨U, ⟨⟨CU, hU⟩, hbij, hip, hUη⟩, ?_⟩
  rintro U' ⟨hU'b, -, -, hU'η⟩
  exact hUuniq U' ⟨hU'b, hU'η⟩

/-- **163II** (`selfdual-compl-defining`, dils.tex:4935, Proposition),
moreover-clause: if an inner-product-preserving module map `η : V → X`
into a self-dual Hilbert ℬ-module has the universal property (every
bounded module map `V → Y` into a self-dual `Y` factors uniquely through
`η`), then the image of `η` is ultranorm dense.

Divergence class 1 (faithful).  The thesis's argument is exactly this one:
`W = ηV^{⊥⊥}` is a self-dual (ultranorm-closed) submodule, so `X` splits as
`W ⊕ W^⊥` (**160IV**.3) and the projection `P` onto `W` is a bounded module
map fixing `ηV`; both `P` and `id` factor `η` through itself, so the
uniqueness clause of the universal property gives `P = id` and hence
`X = W`.  The identification of `W` with the ultranorm closure of `ηV` is
**160IV**.2, using that `ηV` is already a ℬ-submodule, so
`bSpan(ηV) = ηV`. -/
theorem selfdual_compl_defining_dense [VonNeumannAlgebra ℬ]
    (B : BInner ℬ V) {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [SMul ℬ X] [CStarModule ℬ X] [CompleteSpace X] (hX : SelfDual ℬ X)
    (η : V → X) (hadd : ∀ v w, η (v + w) = η v + η w)
    (hsmulc : ∀ (c : ℂ) v, η (c • v) = c • η v)
    (hsmul : ∀ (b : ℬ) v, η (b • v) = b • η v)
    (hinner : ∀ v w, inner ℬ (η v) (η w) = B.inner v w)
    (huniv : ∀ (Y : Type v) (_ : NormedAddCommGroup Y) (_ : NormedSpace ℂ Y)
      (_ : SMul ℬ Y) (_ : CStarModule ℬ Y) (_ : CompleteSpace Y),
      SelfDual ℬ Y → ∀ (C : ℝ) (T : V → Y),
        IsBoundedModuleMap B (cstarBInner ℬ Y) C T →
        ∃! T' : X → Y,
          (∃ C' : ℝ, IsBoundedModuleMap (cstarBInner ℬ X)
            (cstarBInner ℬ Y) C' T') ∧ ∀ v, T' (η v) = T v) :
    UnDense (inner ℬ) (Set.range η) := by
  classical
  -- `η` is bounded, with constant `1`
  have hηbdd : IsBoundedModuleMap B (cstarBInner ℬ X) 1 η := by
    refine ⟨hadd, hsmulc, hsmul, fun v => ?_⟩
    have h : (cstarBInner ℬ X).norm (η v) = B.norm v := by
      rw [cstarBInner_norm,
        CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ) (E := X) (η v), hinner]
      rfl
    rw [h, one_mul]
  -- `ηV` is a ℬ-submodule, so its ℬ-linear span is itself
  have hη0 : η 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have h2 : η 0 + η 0 = η 0 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  have hηsum : ∀ (n : ℕ) (g : Fin n → V) (s : Finset (Fin n)),
      η (∑ i ∈ s, g i) = ∑ i ∈ s, η (g i) := by
    intro n g s
    refine Finset.induction_on s (by simpa using hη0) ?_
    intro i s hi ih
    rw [Finset.sum_insert hi, hadd, ih, Finset.sum_insert hi]
  have hspan : bSpan ℬ (Set.range η) ⊆ Set.range η := by
    rintro y ⟨n, c, b, v, hv, rfl⟩
    choose w hw using hv
    refine ⟨∑ i, c i • b i • w i, ?_⟩
    rw [hηsum]
    exact Finset.sum_congr rfl fun i _ => by rw [hsmulc, hsmul, hw i]
  have hspan' : bSpan ℬ (Set.range η) = Set.range η :=
    Set.eq_of_subset_of_subset hspan (subset_bSpan _)
  -- the projection onto `ηV^{⊥⊥}` fixes `ηV`
  obtain ⟨hW0, hWadd, hWb, hWc, hWcl⟩ :=
    hilbmod_projthm_1 hX (orthoCompl ℬ (Set.range η))
  obtain ⟨P, hPbdd, hPW, hPfix⟩ :=
    exists_orthoProj hX (orthoCompl ℬ (orthoCompl ℬ (Set.range η)))
      hW0 hWadd hWb hWc hWcl
  obtain ⟨T', -, hT'uniq⟩ := huniv X inferInstance inferInstance inferInstance
    inferInstance inferInstance hX 1 η hηbdd
  have hPid : P = id := by
    have h1 : P = T' := hT'uniq P ⟨⟨1, hPbdd⟩, fun v =>
      hPfix (η v) (subset_biorthoCompl _ ⟨v, rfl⟩)⟩
    have h2 : id = T' := hT'uniq id
      ⟨⟨1, ⟨fun x y => rfl, fun c x => rfl, fun b x => rfl,
        fun x => le_of_eq (one_mul _).symm⟩⟩, fun v => rfl⟩
    exact h1.trans h2.symm
  -- hence `X = ηV^{⊥⊥}`, which by **160IV**.2 is the ultranorm closure of `ηV`
  intro x n ωs ε hε
  have hxW : x ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range η)) := by
    have h := hPW x
    rwa [hPid] at h
  rw [hilbmod_projthm_2 hX (Set.range η), hspan'] at hxW
  exact hxW n ωs ε hε

end CompletionDefining

/-! ## The von Neumann algebra tensor product interface

NOTE(proc-dep): axiomatization of thesis A's tensor product of von Neumann
algebras (proc.tex 108II, label `tensor`), used by parsecs 1640–1670. -/

section VNTensor

variable {𝒜 ℬ 𝒞 : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]

variable (𝒜 ℬ) in
/-- An np-functional on `𝒞` is a *product functional* for a bilinear map
`t : 𝒜 × ℬ → 𝒞` when it is of the form `ω ⊗ ξ` on the image of `t`. -/
def IsProductFunctional (t : 𝒜 → ℬ → 𝒞) (Ω : NPFunctional 𝒞) : Prop :=
  ∃ (ω : NPFunctional 𝒜) (ξ : NPFunctional ℬ),
    ∀ (a : 𝒜) (b : ℬ), Ω (t a b) = ω a * ξ b

/-- The interface of the tensor product `𝒞 = 𝒜 ⊗ ℬ` of von Neumann
algebras (proc.tex 108II, `tensor`): an miu-bilinear map
`t : 𝒜 × ℬ → 𝒞` whose image generates `𝒞` as a von Neumann algebra
(`tensor-1`), for which every product functional of np-functionals exists and
is positive (`tensor-2`), and whose product np-functionals are separating
(`tensor-3`). -/
structure IsVNTensor (t : 𝒜 → ℬ → 𝒞) : Prop where
  add_left : ∀ (a a' : 𝒜) (b : ℬ), t (a + a') b = t a b + t a' b
  add_right : ∀ (a : 𝒜) (b b' : ℬ), t a (b + b') = t a b + t a b'
  smul_complex : ∀ (c : ℂ) (a : 𝒜) (b : ℬ), t (c • a) b = c • t a b
  mul : ∀ (a a' : 𝒜) (b b' : ℬ), t a b * t a' b' = t (a * a') (b * b')
  one : t 1 1 = 1
  star : ∀ (a : 𝒜) (b : ℬ), star (t a b) = t (star a) (star b)
  generates : wstar 𝒞 (Set.range fun p : 𝒜 × ℬ => t p.1 p.2) = ⊤
  /-- `tensor-2` (proc.tex:2063): for all np-functionals `σ : 𝒜 → ℂ` and
  `τ : ℬ → ℂ` the product functional `γ(σ,τ) : 𝒞 → ℂ` **exists** and is
  positive — positivity and normality being carried by the type
  `NPFunctional 𝒞`.  `generates` gives uniqueness, never existence, so this
  clause is not redundant, and `separating` (`tensor-3`) says nothing about
  which product functionals exist. -/
  exists_productFunctional : ∀ (ω : NPFunctional 𝒜) (ξ : NPFunctional ℬ),
    ∃ Ω : NPFunctional 𝒞, ∀ (a : 𝒜) (b : ℬ), Ω (t a b) = ω a * ξ b
  separating : ∀ z : 𝒞, 0 ≤ z →
    (∀ Ω : NPFunctional 𝒞, IsProductFunctional 𝒜 ℬ t Ω → Ω z = 0) → z = 0

omit [StarOrderedRing 𝒜] in
private theorem npf_csmul (ω : NPFunctional 𝒜) (c : ℂ) (a : 𝒜) :
    ω (c • a) = c * ω a :=
  (map_smul ω.toPositiveLinearMap c a).trans (smul_eq_mul _ _)

private theorem npf_apply_complex (ω : NPFunctional ℂ) (a : ℂ) :
    ω a = a * ω 1 := by simpa using npf_csmul (𝒜 := ℂ) ω a 1

private theorem npf_one_ofReal (ω : NPFunctional ℂ) :
    (0 : ℝ) ≤ (ω 1).re ∧ (((ω 1).re : ℝ) : ℂ) = ω 1 := by
  have h : (0 : ℂ) ≤ ω 1 := npFunctional_nonneg ω zero_le_one
  rw [Complex.le_def] at h
  exact ⟨by simpa using h.1, Complex.ext (by simp) (by simpa using h.2)⟩

/-- **Non-vacuity check** for `IsVNTensor`: multiplication exhibits `ℂ` as
`ℂ ⊗ ℂ`, so the structure is inhabited and everything derived from it below
(ℂ-homogeneity in the second slot, normality of the legs, **165III**,
**166II**) says something.  Kept in the tree deliberately: a mirroring defect
that left `PaschkeModule` *uninhabited* once made nine theorems of
`Paschke.lean` vacuous (PROVING-LOG session 14), and only a concrete example
caught it. -/
theorem vnTensor_mul_complex : IsVNTensor (fun a b : ℂ => a * b) where
  add_left a a' b := add_mul a a' b
  add_right a b b' := mul_add a b b'
  smul_complex c a b := smul_mul_assoc c a b
  mul a a' b b' := by ring
  one := one_mul 1
  star a b := by rw [star_mul, mul_comm]
  generates := by
    refine eq_top_iff.mpr (le_sInf ?_)
    rintro T ⟨-, hST⟩ z -
    exact hST ⟨(z, 1), by simp⟩
  exists_productFunctional ω ξ := by
    obtain ⟨hω0, hω1⟩ := npf_one_ofReal ω
    obtain ⟨hξ0, hξ1⟩ := npf_one_ofReal ξ
    refine ⟨smulNP (mul_nonneg hω0 hξ0) complexIdNP, fun a b => ?_⟩
    rw [smulNP_apply, npf_apply_complex ω a, npf_apply_complex ξ b, ← hω1, ← hξ1]
    show ((((ω 1).re * (ξ 1).re : ℝ)) : ℂ) * (a * b) = _
    push_cast
    ring
  separating z _ h :=
    h complexIdNP ⟨complexIdNP, complexIdNP, fun _ _ => rfl⟩

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- proc.tex **108I** (`bilinear-basic`) asks a tensor product to be a
*bilinear* — hence ℂ-bilinear — miu-map; `IsVNTensor` records ℂ-homogeneity
only in the **first** argument, because homogeneity in the second is a
consequence of the remaining clauses: `t 1 (c·1)` and `c·1` have the same
value under every product np-functional, hence `d = t 1 (c·1) − c·1` has
`Ω(d*d) = 0` for all of them, so `d*d = 0` by `separating`, so `d = 0`; and
then `t a (c·b) = t 1 (c·1) · t a b = c · t a b` by multiplicativity. -/
theorem vnTensor_smul_complex_right {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t)
    (c : ℂ) (a : 𝒜) (b : ℬ) : t a (c • b) = c • t a b := by
  have hone : t 1 (c • (1 : ℬ)) = c • (1 : 𝒞) := by
    set u : 𝒞 := t 1 (c • (1 : ℬ)) with hu
    set v : 𝒞 := c • (1 : 𝒞) with hv
    have hus : star u = t 1 (star c • (1 : ℬ)) := by
      rw [hu, ht.star, star_one, star_smul, star_one]
    have hvs : star v = star c • (1 : 𝒞) := by rw [hv, star_smul, star_one]
    have e1 : star u * u = t 1 ((star c * c) • (1 : ℬ)) := by
      rw [hus, hu, ht.mul, one_mul, smul_mul_smul_comm, one_mul]
    have e2 : star u * v = c • t 1 (star c • (1 : ℬ)) := by
      rw [hus, hv, mul_smul_comm, mul_one]
    have e3 : star v * u = star c • t 1 (c • (1 : ℬ)) := by
      rw [hvs, hu, smul_mul_assoc, one_mul]
    have e4 : star v * v = (star c * c) • (1 : 𝒞) := by
      rw [hvs, hv, smul_mul_smul_comm, one_mul]
    have hexp : star (u - v) * (u - v)
        = star u * u - star u * v - star v * u + star v * v := by
      rw [star_sub]; noncomm_ring
    have key : star (u - v) * (u - v) = 0 := by
      refine ht.separating _ (star_mul_self_nonneg _) ?_
      rintro Ω ⟨ω, ξ, hΩ⟩
      have hΩ1 : Ω (1 : 𝒞) = ω 1 * ξ 1 := by rw [← ht.one]; exact hΩ 1 1
      rw [hexp, e1, e2, e3, e4, npFunctional_add, npFunctional_sub,
        npFunctional_sub, npf_csmul, npf_csmul, npf_csmul, hΩ, hΩ, hΩ, hΩ1,
        npf_csmul, npf_csmul, npf_csmul]
      ring
    rw [← sub_eq_zero]
    exact (CStarRing.star_mul_self_eq_zero_iff _).mp key
  have h := ht.mul 1 a (c • (1 : ℬ)) b
  rw [hone, one_mul, smul_mul_assoc, one_mul, smul_mul_assoc, one_mul] at h
  exact h.symm

/-! ### The legs of a von Neumann tensor product

`QUESTIONS.md` B5 asks whether `IsVNTensor` should carry a *normality*
clause for its legs `a ↦ a ⊗ 1`, `b ↦ 1 ⊗ b` (dils.tex 166III leaves the
justification as a commented-out `\TODO`).  It should not: normality is a
consequence of the faithfulness of the product functionals, as follows. -/

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- The flip `(b,a) ↦ a ⊗ b` of a von Neumann tensor product is again one
(with the roles of the two factors exchanged).  ℂ-homogeneity in the new
first slot is `vnTensor_smul_complex_right`. -/
theorem vnTensor_flip {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) :
    IsVNTensor (fun (b : ℬ) (a : 𝒜) => t a b) where
  add_left b b' a := ht.add_right a b b'
  add_right b a a' := ht.add_left a a' b
  smul_complex c b a := vnTensor_smul_complex_right ht c a b
  mul b b' a a' := ht.mul a a' b b'
  one := ht.one
  star b a := ht.star a b
  generates := by
    rw [show (Set.range fun p : ℬ × 𝒜 => t p.2 p.1)
        = Set.range fun p : 𝒜 × ℬ => t p.1 p.2 by
      ext z
      exact ⟨fun ⟨p, hp⟩ => ⟨(p.2, p.1), hp⟩, fun ⟨p, hp⟩ => ⟨(p.2, p.1), hp⟩⟩]
    exact ht.generates
  exists_productFunctional ξ ω := by
    obtain ⟨Ω, hΩ⟩ := ht.exists_productFunctional ω ξ
    exact ⟨Ω, fun b a => (hΩ a b).trans (mul_comm _ _)⟩
  separating z hz h := by
    refine ht.separating z hz fun Ω hΩ => ?_
    obtain ⟨ω, ξ, hΩval⟩ := hΩ
    exact h Ω ⟨ξ, ω, fun b a => by rw [hΩval a b, mul_comm]⟩

omit [StarOrderedRing ℬ] in
/-- The left leg `a ↦ a ⊗ 1` is positive. -/
theorem vnTensor_legLeft_nonneg {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) {a : 𝒜}
    (ha : 0 ≤ a) : 0 ≤ t a 1 := by
  obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  have hs : t (star c) 1 = star (t c 1) := by rw [ht.star c 1, star_one]
  have h := ht.mul (star c) c (star (1 : ℬ)) 1
  rw [star_one, one_mul, hs] at h
  rw [← h]
  exact star_mul_self_nonneg _

omit [StarOrderedRing ℬ] in
/-- The left leg is monotone. -/
theorem vnTensor_legLeft_mono {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) {a a' : 𝒜}
    (h : a ≤ a') : t a 1 ≤ t a' 1 := by
  have hd : t a' 1 - t a 1 = t (a' - a) 1 := by
    have h2 := ht.add_left (a' - a) a 1
    rw [sub_add_cancel] at h2
    rw [h2]; abel
  rw [← sub_nonneg, hd]
  exact vnTensor_legLeft_nonneg ht (sub_nonneg.mpr h)

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] [StarOrderedRing 𝒞] in
/-- The left leg preserves self-adjointness. -/
theorem vnTensor_legLeft_isSelfAdjoint {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t)
    {a : 𝒜} (ha : IsSelfAdjoint a) : IsSelfAdjoint (t a 1) := by
  change star (t a 1) = t a 1
  rw [ht.star, star_one, ha.star_eq]

/-- `IsLUB` is preserved by multiplication with a nonnegative real. -/
private theorem isLUB_mul_const {S : Set ℝ} {a k : ℝ} (hS : S.Nonempty)
    (h : IsLUB S a) (hk : 0 ≤ k) : IsLUB ((fun x => x * k) '' S) (a * k) := by
  rcases eq_or_lt_of_le hk with hk0 | hk0
  · subst_vars
    obtain ⟨x, hx⟩ := hS
    have himg : (fun x : ℝ => x * 0) '' S = {0} := by
      ext r; constructor
      · rintro ⟨w, -, rfl⟩; simp
      · rintro rfl; exact ⟨x, hx, by simp⟩
    rw [himg, mul_zero]
    exact isLUB_singleton
  · refine ⟨?_, ?_⟩
    · rintro r ⟨w, hw, rfl⟩
      exact mul_le_mul_of_nonneg_right (h.1 hw) hk
    · intro c hc
      have hle : ∀ w ∈ S, w ≤ c / k := fun w hw =>
        (le_div_iff₀ hk0).mpr (hc ⟨w, hw, rfl⟩)
      exact (le_div_iff₀ hk0).mp (h.2 hle)

/-- **Normality of the legs** of a von Neumann tensor product: `a ↦ a ⊗ 1`
preserves suprema of bounded directed sets of self-adjoint elements.  This
is *not* an extra clause of `IsVNTensor`: it follows from the faithfulness
of the product functionals (`separating`), because the supremum `s'` of the
image in `𝒞` and `s ⊗ 1` are separated by no product functional. -/
theorem vnTensor_legLeft_normal [VonNeumannAlgebra 𝒞] {t : 𝒜 → ℬ → 𝒞}
    (ht : IsVNTensor t) : PreservesDirSups (fun a : 𝒜 => t a 1) := by
  intro D s hne hdir hlub
  set g : selfAdjoint 𝒜 → selfAdjoint 𝒞 := fun d =>
    ⟨t (d : 𝒜) 1, vnTensor_legLeft_isSelfAdjoint ht d.2⟩ with hg
  have hgmono : ∀ d d' : selfAdjoint 𝒜, d ≤ d' → g d ≤ g d' := fun d d' h =>
    Subtype.coe_le_coe.mp (vnTensor_legLeft_mono ht (Subtype.coe_le_coe.mpr h))
  obtain ⟨d₀, hd₀⟩ := id hne
  have hEne : (g '' D).Nonempty := ⟨g d₀, d₀, hd₀, rfl⟩
  have hEdir : DirectedOn (· ≤ ·) (g '' D) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hxw, hzw⟩ := hdir x hx z hz
    exact ⟨g w, ⟨w, hw, rfl⟩, hgmono _ _ hxw, hgmono _ _ hzw⟩
  have hEub : g s ∈ upperBounds (g '' D) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hgmono _ _ (hlub.1 hd)
  have hEbdd : BddAbove (g '' D) := ⟨_, hEub⟩
  set s' : selfAdjoint 𝒞 := dirSup (g '' D) ⟨hEne, hEdir, hEbdd⟩ with hs'
  have hlubE : IsLUB (g '' D) s' := isLUB_dirSup _ _
  have hs'le : s' ≤ g s := hlubE.2 hEub
  -- `g s = s'`, because their difference is positive and killed by every
  -- product np-functional
  have hkey : g s = s' := by
    refine Subtype.ext (sub_eq_zero.mp ?_)
    refine ht.separating _ (sub_nonneg.mpr (Subtype.coe_le_coe.mpr hs'le))
      fun Ω hΩp => ?_
    obtain ⟨ω, ξ, hΩ⟩ := hΩp
    have hval : ∀ d : selfAdjoint 𝒜, ((Ω (g d : 𝒞) : ℂ)).re
        = ((ω (d : 𝒜) : ℂ)).re * ((ξ (1 : ℬ) : ℂ)).re := by
      intro d
      rw [show (Ω (g d : 𝒞) : ℂ) = ω (d : 𝒜) * ξ 1 from hΩ _ _, Complex.mul_re,
        npFunctional_im_eq_zero ω d.2, zero_mul, sub_zero]
    have hωre : IsLUB (Complex.re ''
        ((fun d : selfAdjoint 𝒜 => (ω (d : 𝒜) : ℂ)) '' D)) ((ω (s : 𝒜) : ℂ)).re :=
      isLUB_re_of_isLUB (by
        rintro _ ⟨d, -, rfl⟩
        exact npFunctional_im_eq_zero ω d.2) (ω.preservesDirSups' D s hne hdir hlub)
    have hΩre : IsLUB (Complex.re ''
        ((fun d : selfAdjoint 𝒞 => (Ω (d : 𝒞) : ℂ)) '' (g '' D)))
        ((Ω (s' : 𝒞) : ℂ)).re :=
      isLUB_re_of_isLUB (by
        rintro _ ⟨d, -, rfl⟩
        exact npFunctional_im_eq_zero Ω d.2)
        (Ω.preservesDirSups' (g '' D) s' hEne hEdir hlubE)
    have hk : (0 : ℝ) ≤ ((ξ (1 : ℬ) : ℂ)).re :=
      (Complex.le_def.mp (npFunctional_nonneg ξ zero_le_one)).1
    have hsets : Complex.re ''
        ((fun d : selfAdjoint 𝒞 => (Ω (d : 𝒞) : ℂ)) '' (g '' D))
        = (fun x : ℝ => x * ((ξ (1 : ℬ) : ℂ)).re) ''
          (Complex.re '' ((fun d : selfAdjoint 𝒜 => (ω (d : 𝒜) : ℂ)) '' D)) := by
      ext r
      constructor
      · rintro ⟨-, ⟨-, ⟨d, hd, rfl⟩, rfl⟩, rfl⟩
        exact ⟨((ω (d : 𝒜) : ℂ)).re, ⟨_, ⟨d, hd, rfl⟩, rfl⟩, (hval d).symm⟩
      · rintro ⟨-, ⟨-, ⟨d, hd, rfl⟩, rfl⟩, rfl⟩
        exact ⟨Ω (g d : 𝒞), ⟨g d, ⟨d, hd, rfl⟩, rfl⟩, hval d⟩
    rw [hsets] at hΩre
    have hSne : (Complex.re ''
        ((fun d : selfAdjoint 𝒜 => (ω (d : 𝒜) : ℂ)) '' D)).Nonempty :=
      ⟨((ω (d₀ : 𝒜) : ℂ)).re, ⟨_, ⟨d₀, hd₀, rfl⟩, rfl⟩⟩
    have hre : ((Ω (s' : 𝒞) : ℂ)).re
        = ((ω (s : 𝒜) : ℂ)).re * ((ξ (1 : ℬ) : ℂ)).re :=
      hΩre.unique (isLUB_mul_const hSne hωre hk)
    have him1 : ((Ω (g s : 𝒞) : ℂ)).im = 0 :=
      npFunctional_im_eq_zero Ω (g s).2
    have him2 : ((Ω (s' : 𝒞) : ℂ)).im = 0 := npFunctional_im_eq_zero Ω s'.2
    rw [npFunctional_sub]
    refine Complex.ext ?_ ?_
    · simp only [Complex.sub_re, Complex.zero_re, hval s, hre, sub_self]
    · simp only [Complex.sub_im, Complex.zero_im, him1, him2, sub_self]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact vnTensor_legLeft_mono ht (Subtype.coe_le_coe.mpr (hlub.1 hd))
  · intro c hc
    have hcsa : IsSelfAdjoint c := by
      have h0 : (0 : 𝒞) ≤ c - t (d₀ : 𝒜) 1 := sub_nonneg.mpr (hc ⟨d₀, hd₀, rfl⟩)
      have h1 : c = (c - t (d₀ : 𝒜) 1) + t (d₀ : 𝒜) 1 := by abel
      rw [h1]
      exact (IsSelfAdjoint.of_nonneg h0).add
        (vnTensor_legLeft_isSelfAdjoint ht d₀.2)
    have hub : (⟨c, hcsa⟩ : selfAdjoint 𝒞) ∈ upperBounds (g '' D) := by
      rintro _ ⟨d, hd, rfl⟩
      exact Subtype.coe_le_coe.mp (hc ⟨d, hd, rfl⟩)
    have hfin := hlubE.2 hub
    rw [← hkey] at hfin
    exact Subtype.coe_le_coe.mpr hfin

omit [StarOrderedRing 𝒜] in
/-- The right leg `b ↦ 1 ⊗ b` is positive. -/
theorem vnTensor_legRight_nonneg {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) {b : ℬ}
    (hb : 0 ≤ b) : 0 ≤ t 1 b :=
  vnTensor_legLeft_nonneg (vnTensor_flip ht) hb

omit [StarOrderedRing 𝒜] in
/-- The right leg is monotone. -/
theorem vnTensor_legRight_mono {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) {b b' : ℬ}
    (h : b ≤ b') : t 1 b ≤ t 1 b' :=
  vnTensor_legLeft_mono (vnTensor_flip ht) h

/-- **Normality of the right leg** `b ↦ 1 ⊗ b`. -/
theorem vnTensor_legRight_normal [VonNeumannAlgebra 𝒞] {t : 𝒜 → ℬ → 𝒞}
    (ht : IsVNTensor t) : PreservesDirSups (fun b : ℬ => t 1 b) :=
  vnTensor_legLeft_normal (vnTensor_flip ht)

/-- A positive element is dominated by any real bound on its norm:
`0 ≤ u`, `‖u‖ ≤ r` give `u ≤ r·1`.  (**9X**.2 plus monotonicity of
`r ↦ r·1`.) -/
private theorem le_ofReal_smul_one {𝒟 : Type*} [CStarAlgebra 𝒟]
    [PartialOrder 𝒟] [StarOrderedRing 𝒟] {u : 𝒟} {r : ℝ} (hu : 0 ≤ u)
    (h : ‖u‖ ≤ r) : u ≤ ((r : ℝ) : ℂ) • (1 : 𝒟) := by
  refine (cstar_positive_2 u (IsSelfAdjoint.of_nonneg hu)).2.2.trans ?_
  rw [← Algebra.algebraMap_eq_smul_one]
  exact algebraMap_ofReal_mono h

/-- `⊗` of two positive elements is positive: `a = c*c`, `b = d*d` give
`a ⊗ b = (c ⊗ d)* (c ⊗ d)`. -/
theorem vnTensor_nonneg {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) {a : 𝒜} {b : ℬ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ t a b := by
  obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  obtain ⟨d, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
  rw [← ht.mul, ← ht.star]
  exact star_mul_self_nonneg _

/-- `⊗` is monotone in its second argument, over a positive first one. -/
theorem vnTensor_mono_right {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) {a : 𝒜}
    (ha : 0 ≤ a) {b b' : ℬ} (h : b ≤ b') : t a b ≤ t a b' := by
  have hd : t a b' - t a b = t a (b' - b) := by
    have h2 := ht.add_right a (b' - b) b
    rw [sub_add_cancel] at h2
    rw [h2]; abel
  rw [← sub_nonneg, hd]
  exact vnTensor_nonneg ht ha (sub_nonneg.mpr h)

/-- `⊗` is monotone in its first argument, over a positive second one. -/
theorem vnTensor_mono_left {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) {b : ℬ}
    (hb : 0 ≤ b) {a a' : 𝒜} (h : a ≤ a') : t a b ≤ t a' b :=
  vnTensor_mono_right (vnTensor_flip ht) hb h

/-- The left leg `a ↦ a ⊗ 1` as a positive linear map. -/
noncomputable def vnTensorLegLeft {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) :
    𝒜 →ₚ[ℂ] 𝒞 where
  toFun a := t a 1
  map_add' a a' := ht.add_left a a' 1
  map_smul' c a := ht.smul_complex c a 1
  monotone' _ _ h := vnTensor_legLeft_mono ht h

/-- The right leg `b ↦ 1 ⊗ b` as a positive linear map. -/
noncomputable def vnTensorLegRight {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) :
    ℬ →ₚ[ℂ] 𝒞 where
  toFun b := t 1 b
  map_add' b b' := ht.add_right 1 b b'
  map_smul' c b := vnTensor_smul_complex_right ht c 1 b
  monotone' _ _ h := vnTensor_legRight_mono ht h

/-- `Ω ↦ Ω(· ⊗ 1)`: an np-functional on `𝒞 = 𝒜 ⊗ ℬ` restricts along the
left leg to an np-functional on `𝒜`.  Normality is
`vnTensor_legLeft_normal`, i.e. it needs no clause beyond `IsVNTensor`. -/
noncomputable def vnTensorLegLeftNP [VonNeumannAlgebra 𝒞] {t : 𝒜 → ℬ → 𝒞}
    (ht : IsVNTensor t) (Ω : NPFunctional 𝒞) : NPFunctional 𝒜 :=
  compNP (vnTensorLegLeft ht) (vnTensor_legLeft_normal ht) Ω

@[simp] theorem vnTensorLegLeftNP_apply [VonNeumannAlgebra 𝒞]
    {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) (Ω : NPFunctional 𝒞) (a : 𝒜) :
    vnTensorLegLeftNP ht Ω a = Ω (t a 1) := rfl

/-- `Ω ↦ Ω(1 ⊗ ·)`; see `vnTensorLegLeftNP`. -/
noncomputable def vnTensorLegRightNP [VonNeumannAlgebra 𝒞] {t : 𝒜 → ℬ → 𝒞}
    (ht : IsVNTensor t) (Ω : NPFunctional 𝒞) : NPFunctional ℬ :=
  compNP (vnTensorLegRight ht) (vnTensor_legRight_normal ht) Ω

@[simp] theorem vnTensorLegRightNP_apply [VonNeumannAlgebra 𝒞]
    {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) (Ω : NPFunctional 𝒞) (b : ℬ) :
    vnTensorLegRightNP ht Ω b = Ω (t 1 b) := rfl

/-! ### Auxiliary material for **165IV**

The estimate of **165IV** (dils.tex:5433) needs: positivity of
`Mₙ(⊗)` — thesis A's **113II**/**113IV**, available here as
`Theses.A.CStar.matBilin_nonneg_of_mi` — together with its two-sided
monotonicity, which follows from positivity and additivity; and positivity
of the Gram matrices `(⟨xᵢ,xⱼ⟩)ᵢⱼ`, which is **33II**.1
(`cstar_matrix_positive_iff`). -/

/-- **113II**/**113IV** in the form used by **165IV**:
`∑ᵢⱼ t Mᵢⱼ M'ᵢⱼ ≥ 0` for positive matrices `M`, `M'`. -/
private theorem sum_t_nonneg {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) {n : ℕ}
    (f : Fin n → Fin n → 𝒜) (g : Fin n → Fin n → ℬ)
    (hf : (0 : CStarMatrix (Fin n) (Fin n) 𝒜)
      ≤ CStarMatrix.ofMatrix (Matrix.of f))
    (hg : (0 : CStarMatrix (Fin n) (Fin n) ℬ)
      ≤ CStarMatrix.ofMatrix (Matrix.of g)) :
    0 ≤ ∑ i, ∑ j, t (f i j) (g i j) := by
  have h := matBilin_nonneg_of_mi t ht.add_left ht.add_right ht.mul ht.star
    (CStarMatrix.ofMatrix (Matrix.of f)) (CStarMatrix.ofMatrix (Matrix.of g))
    hf hg (fun _ => 1)
  simpa using h

/-- Monotonicity of `∑ᵢⱼ t · ·` in the first slot. -/
private theorem sum_t_mono_left {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) {n : ℕ}
    (f f' d : Fin n → Fin n → 𝒜) (g : Fin n → Fin n → ℬ)
    (hd : ∀ i j, f' i j = d i j + f i j)
    (hdpos : (0 : CStarMatrix (Fin n) (Fin n) 𝒜)
      ≤ CStarMatrix.ofMatrix (Matrix.of d))
    (hg : (0 : CStarMatrix (Fin n) (Fin n) ℬ)
      ≤ CStarMatrix.ofMatrix (Matrix.of g)) :
    ∑ i, ∑ j, t (f i j) (g i j) ≤ ∑ i, ∑ j, t (f' i j) (g i j) := by
  have hsplit : ∑ i, ∑ j, t (f' i j) (g i j)
      = (∑ i, ∑ j, t (d i j) (g i j)) + ∑ i, ∑ j, t (f i j) (g i j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hd i j, ht.add_left]
  rw [hsplit, le_add_iff_nonneg_left]
  exact sum_t_nonneg ht d g hdpos hg

/-- Monotonicity of `∑ᵢⱼ t · ·` in the second slot. -/
private theorem sum_t_mono_right {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) {n : ℕ}
    (f : Fin n → Fin n → 𝒜) (g g' e : Fin n → Fin n → ℬ)
    (he : ∀ i j, g' i j = e i j + g i j)
    (hepos : (0 : CStarMatrix (Fin n) (Fin n) ℬ)
      ≤ CStarMatrix.ofMatrix (Matrix.of e))
    (hf : (0 : CStarMatrix (Fin n) (Fin n) 𝒜)
      ≤ CStarMatrix.ofMatrix (Matrix.of f)) :
    ∑ i, ∑ j, t (f i j) (g i j) ≤ ∑ i, ∑ j, t (f i j) (g' i j) := by
  have hsplit : ∑ i, ∑ j, t (f i j) (g' i j)
      = (∑ i, ∑ j, t (f i j) (e i j)) + ∑ i, ∑ j, t (f i j) (g i j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [he i j, ht.add_right]
  rw [hsplit, le_add_iff_nonneg_left]
  exact sum_t_nonneg ht f e hf hepos

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] [StarOrderedRing 𝒞] in
/-- Pulling a scalar out of the first slot. -/
private theorem sum_t_smul_left {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) {n : ℕ}
    (c : ℂ) (f : Fin n → Fin n → 𝒜) (g : Fin n → Fin n → ℬ) :
    ∑ i, ∑ j, t (c • f i j) (g i j) = c • ∑ i, ∑ j, t (f i j) (g i j) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => ht.smul_complex _ _ _

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- Pulling a scalar out of the second slot (`vnTensor_smul_complex_right`). -/
private theorem sum_t_smul_right {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t) {n : ℕ}
    (c : ℂ) (f : Fin n → Fin n → 𝒜) (g : Fin n → Fin n → ℬ) :
    ∑ i, ∑ j, t (f i j) (c • g i j) = c • ∑ i, ∑ j, t (f i j) (g i j) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => vnTensor_smul_complex_right ht _ _ _

/-! ### Gram matrices -/

section Gram

variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒜 X]
  [CStarModule 𝒜 X]

omit [StarOrderedRing 𝒜] in
/-- `∑ᵢⱼ cᵢ* ⟨xⱼ,xᵢ⟩ cⱼ = ⟨v,v⟩` for `v = ∑ᵢ cᵢ* xᵢ` (mirrored
convention). -/
private theorem gram_conj {n : ℕ} (x : Fin n → X) (c : Fin n → 𝒜) :
    ∑ i, ∑ j, star (c i) * (inner 𝒜 (x j) (x i) : 𝒜) * c j
      = inner 𝒜 (∑ i, star (c i) • x i) (∑ i, star (c i) • x i) := by
  rw [CStarModule.inner_sum_left, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [CStarModule.inner_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
    star_star, mul_assoc]

/-- The Gram matrix `(⟨xⱼ,xᵢ⟩)ᵢⱼ` of a finite family is positive
(**33II**.1 `cstar_matrix_positive_iff`). -/
private theorem gram_nonneg {n : ℕ} (x : Fin n → X) :
    (0 : CStarMatrix (Fin n) (Fin n) 𝒜)
      ≤ CStarMatrix.ofMatrix
          (Matrix.of fun i j => (inner 𝒜 (x j) (x i) : 𝒜)) := by
  refine (cstar_matrix_positive_iff _).mpr fun c => ?_
  rw [show (∑ i, ∑ j, star (c i)
        * (CStarMatrix.ofMatrix
            (Matrix.of fun i j => (inner 𝒜 (x j) (x i) : 𝒜))) i j * c j)
      = ∑ i, ∑ j, star (c i) * (inner 𝒜 (x j) (x i) : 𝒜) * c j from rfl,
    gram_conj]
  exact CStarModule.inner_self_nonneg

variable [CompleteSpace X]

/-- `⟨Sv, Sv⟩ ≤ ‖S‖² ⟨v,v⟩` for an adjointable bounded operator `S`. -/
private theorem ba_inner_le_norm_sq (S : Ba 𝒜 X) (v : X) :
    (inner 𝒜 (S.1 v) (S.1 v) : 𝒜) ≤ ((‖S‖ ^ 2 : ℝ) : ℂ) • inner 𝒜 v v := by
  have h1 : (inner 𝒜 (S.1 v) (S.1 v) : 𝒜)
      = inner 𝒜 v ((star S * S : Ba 𝒜 X).1 v) := by
    have h := baSubalgebra_star_spec (𝒷 := 𝒜) (X := X) S
    change (inner 𝒜 (S.1 v) (S.1 v) : 𝒜)
      = inner 𝒜 v ((star S : Ba 𝒜 X).1 (S.1 v))
    exact h v (S.1 v)
  have h2 := ba_inner_mono (𝒷 := 𝒜) v
    (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := S))
  rw [h1]
  refine h2.trans (le_of_eq ?_)
  have h3 : ((algebraMap ℝ (Ba 𝒜 X) (‖S‖ ^ 2)).1 : X →L[ℂ] X) v
      = ((‖S‖ ^ 2 : ℝ) : ℂ) • v := by
    rw [Algebra.algebraMap_eq_smul_one]; rfl
  rw [h3, CStarModule.inner_smul_right_complex]

/-- `‖S‖²·Gram(x) − Gram(Sx) ≥ 0` — the thesis's "reasoning in the same way
for `√(‖S‖² − S*S)`" (**165IV**), here by way of `ba_inner_le_norm_sq`. -/
private theorem gram_sub_nonneg {n : ℕ} (S : Ba 𝒜 X) (x : Fin n → X) :
    (0 : CStarMatrix (Fin n) (Fin n) 𝒜)
      ≤ CStarMatrix.ofMatrix (Matrix.of fun i j =>
          ((‖S‖ ^ 2 : ℝ) : ℂ) • (inner 𝒜 (x j) (x i) : 𝒜)
            - inner 𝒜 (S.1 (x j)) (S.1 (x i))) := by
  obtain ⟨-, -, hSm⟩ := moduleAdjointable_linear (𝒜 := 𝒜) ⇑S.1 S.2
  refine (cstar_matrix_positive_iff _).mpr fun c => ?_
  have hsplit : (∑ i, ∑ j, star (c i)
        * (CStarMatrix.ofMatrix (Matrix.of fun i j =>
            ((‖S‖ ^ 2 : ℝ) : ℂ) • (inner 𝒜 (x j) (x i) : 𝒜)
              - inner 𝒜 (S.1 (x j)) (S.1 (x i)))) i j * c j)
      = ((‖S‖ ^ 2 : ℝ) : ℂ)
          • (∑ i, ∑ j, star (c i) * (inner 𝒜 (x j) (x i) : 𝒜) * c j)
        - ∑ i, ∑ j, star (c i)
            * (inner 𝒜 (S.1 (x j)) (S.1 (x i)) : 𝒜) * c j := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    change star (c i) * (((‖S‖ ^ 2 : ℝ) : ℂ) • (inner 𝒜 (x j) (x i) : 𝒜)
        - inner 𝒜 (S.1 (x j)) (S.1 (x i))) * c j = _
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  rw [hsplit, gram_conj, gram_conj, sub_nonneg]
  have hsum : ∑ i, star (c i) • S.1 (x i) = S.1 (∑ i, star (c i) • x i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (hSm _ _).symm
  rw [hsum]
  exact ba_inner_le_norm_sq S _

end Gram

/-- The estimate of **165IV** (dils.tex:5433): `Θ(x,y) = (Sx) ⊗ (Ty)` is
bounded by `‖S‖‖T‖`, in the Gram form in which `ExtTensor.univ` asks for
it.  This is the displayed computation of **165IV**, with the row vector
`s` of `1`s replaced by the equivalent `c = (1,…,1)` in `Mₙ(⊗)`'s
positivity. -/
private theorem tensor_gram_bound {t : 𝒜 → ℬ → 𝒞} (ht : IsVNTensor t)
    {X Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒜 X] [CStarModule 𝒜 X]
    [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul ℬ Y] [CStarModule ℬ Y]
    [CompleteSpace Y]
    (S : Ba 𝒜 X) (T : Ba ℬ Y) {n : ℕ} (x : Fin n → X) (y : Fin n → Y) :
    ‖∑ i, ∑ j, t (inner 𝒜 (S.1 (x i)) (S.1 (x j)))
        (inner ℬ (T.1 (y i)) (T.1 (y j)))‖
      ≤ ‖S‖ ^ 2 * ‖T‖ ^ 2
        * ‖∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))‖ := by
  have hGpos := gram_nonneg (𝒜 := 𝒜) x
  have hApos := gram_nonneg (𝒜 := 𝒜) fun i => S.1 (x i)
  have hBpos := gram_nonneg (𝒜 := ℬ) fun i => T.1 (y i)
  have hDS := gram_sub_nonneg S x
  have hDT := gram_sub_nonneg T y
  have step1 : ∑ i, ∑ j, t (inner 𝒜 (S.1 (x j)) (S.1 (x i)))
        (inner ℬ (T.1 (y j)) (T.1 (y i)))
      ≤ ∑ i, ∑ j, t (((‖S‖ ^ 2 : ℝ) : ℂ) • (inner 𝒜 (x j) (x i) : 𝒜))
        (inner ℬ (T.1 (y j)) (T.1 (y i))) :=
    sum_t_mono_left ht _ _ _ _ (fun _ _ => (sub_add_cancel _ _).symm) hDS hBpos
  have step2 := sum_t_smul_left ht ((‖S‖ ^ 2 : ℝ) : ℂ)
    (fun i j => (inner 𝒜 (x j) (x i) : 𝒜))
    (fun i j => (inner ℬ (T.1 (y j)) (T.1 (y i)) : ℬ))
  have step3 : ∑ i, ∑ j, t (inner 𝒜 (x j) (x i))
        (inner ℬ (T.1 (y j)) (T.1 (y i)))
      ≤ ∑ i, ∑ j, t (inner 𝒜 (x j) (x i))
        (((‖T‖ ^ 2 : ℝ) : ℂ) • (inner ℬ (y j) (y i) : ℬ)) :=
    sum_t_mono_right ht _ _ _ _ (fun _ _ => (sub_add_cancel _ _).symm) hDT hGpos
  have step4 := sum_t_smul_right ht ((‖T‖ ^ 2 : ℝ) : ℂ)
    (fun i j => (inner 𝒜 (x j) (x i) : 𝒜))
    (fun i j => (inner ℬ (y j) (y i) : ℬ))
  have pos1 : (0 : 𝒞) ≤ ∑ i, ∑ j, t (inner 𝒜 (S.1 (x j)) (S.1 (x i)))
      (inner ℬ (T.1 (y j)) (T.1 (y i))) := sum_t_nonneg ht _ _ hApos hBpos
  have pos2 : (0 : 𝒞) ≤ ∑ i, ∑ j, t (inner 𝒜 (x j) (x i))
      (inner ℬ (T.1 (y j)) (T.1 (y i))) := sum_t_nonneg ht _ _ hGpos hBpos
  have hnormsmul : ∀ (r : ℝ) (z : 𝒞), 0 ≤ r → ‖(r : ℂ) • z‖ = r * ‖z‖ := by
    intro r z hr
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have n1 := CStarAlgebra.norm_le_norm_of_nonneg_of_le pos1
    (step1.trans (le_of_eq step2))
  have n2 := CStarAlgebra.norm_le_norm_of_nonneg_of_le pos2
    (step3.trans (le_of_eq step4))
  rw [hnormsmul _ _ (by positivity)] at n1
  rw [hnormsmul _ _ (by positivity)] at n2
  have hswapST : ∑ i, ∑ j, t (inner 𝒜 (S.1 (x i)) (S.1 (x j)))
        (inner ℬ (T.1 (y i)) (T.1 (y j)))
      = ∑ i, ∑ j, t (inner 𝒜 (S.1 (x j)) (S.1 (x i)))
        (inner ℬ (T.1 (y j)) (T.1 (y i))) := Finset.sum_comm
  have hswap : ∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))
      = ∑ i, ∑ j, t (inner 𝒜 (x j) (x i)) (inner ℬ (y j) (y i)) :=
    Finset.sum_comm
  rw [hswapST, hswap]
  calc ‖∑ i, ∑ j, t (inner 𝒜 (S.1 (x j)) (S.1 (x i)))
        (inner ℬ (T.1 (y j)) (T.1 (y i)))‖
      ≤ ‖S‖ ^ 2 * ‖∑ i, ∑ j, t (inner 𝒜 (x j) (x i))
          (inner ℬ (T.1 (y j)) (T.1 (y i)))‖ := n1
    _ ≤ ‖S‖ ^ 2 * (‖T‖ ^ 2 * ‖∑ i, ∑ j, t (inner 𝒜 (x j) (x i))
          (inner ℬ (y j) (y i))‖) := mul_le_mul_of_nonneg_left n2 (by positivity)
    _ = ‖S‖ ^ 2 * ‖T‖ ^ 2 * ‖∑ i, ∑ j, t (inner 𝒜 (x j) (x i))
          (inner ℬ (y j) (y i))‖ := by ring

end VNTensor

/-! ## Parsec 1640: the self-dual exterior tensor product

**164I** (dils.tex:4987): introduction — nothing to formalize. -/

section ExtTensor

variable {𝒜 ℬ 𝒞 : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]
  {X Y : Type u}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒜 X] [CStarModule 𝒜 X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul ℬ Y] [CStarModule ℬ Y]

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), the data:
a **self-dual exterior tensor product** of a self-dual Hilbert 𝒜-module
`X` and a self-dual Hilbert ℬ-module `Y` over the von Neumann tensor
product `𝒞 = 𝒜 ⊗ ℬ` (given by `t`): a self-dual Hilbert 𝒞-module `Z`
with a bilinear `η : X × Y → Z` satisfying
`η(xa, yb) = (a ⊗ b)·η(x,y)` and
`⟨η(x,y), η(x',y')⟩ = ⟨x,x'⟩ ⊗ ⟨y,y'⟩`, whose image spans an
ultranorm-dense submodule, and which is universal among bounded
`𝒜 ⊙ ℬ`-bilinear maps into self-dual Hilbert 𝒞-modules. -/
structure ExtTensor (t : 𝒜 → ℬ → 𝒞) (ht : IsVNTensor t)
    (X Y : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒜 X]
    [CStarModule 𝒜 X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul ℬ Y]
    [CStarModule ℬ Y] : Type (u + 1) where
  /-- The carrier `X ⊗ Y`. -/
  Z : Type u
  [nacg : NormedAddCommGroup Z]
  [nsp : NormedSpace ℂ Z]
  [smul : SMul 𝒞 Z]
  [cstarMod : CStarModule 𝒞 Z]
  [complete : CompleteSpace Z]
  /-- `X ⊗ Y` is self dual. -/
  selfDual : SelfDual 𝒞 Z
  /-- The bilinear map `η(x, y) = x ⊗ y`. -/
  η : X → Y → Z
  η_add_left : ∀ (x x' : X) (y : Y), η (x + x') y = η x y + η x' y
  η_add_right : ∀ (x : X) (y y' : Y), η x (y + y') = η x y + η x y'
  η_smul_complex : ∀ (c : ℂ) (x : X) (y : Y), η (c • x) y = c • η x y
  /-- `η(xa, yb) = (a ⊗ b) η(x,y)` (mirrored). -/
  η_smul : ∀ (a : 𝒜) (b : ℬ) (x : X) (y : Y),
    η (a • x) (b • y) = t a b • η x y
  /-- `⟨x ⊗ y, x' ⊗ y'⟩ = ⟨x,x'⟩ ⊗ ⟨y,y'⟩`. -/
  η_inner : ∀ (x x' : X) (y y' : Y),
    inner 𝒞 (η x y) (η x' y') = t (inner 𝒜 x x') (inner ℬ y y')
  /-- Universal property: bounded `𝒜 ⊙ ℬ`-bilinear maps into self-dual
  Hilbert 𝒞-modules factor uniquely through `η`. -/
  univ : ∀ (W : Type u) (_ : NormedAddCommGroup W) (_ : NormedSpace ℂ W)
    (_ : SMul 𝒞 W) (_ : CStarModule 𝒞 W) (_ : CompleteSpace W),
    SelfDual 𝒞 W →
    ∀ T : X → Y → W,
      (∀ (x x' : X) (y : Y), T (x + x') y = T x y + T x' y) →
      (∀ (x : X) (y y' : Y), T x (y + y') = T x y + T x y') →
      (∀ (a : 𝒜) (b : ℬ) (x : X) (y : Y),
        T (a • x) (b • y) = t a b • T x y) →
      (∃ C : ℝ, ∀ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
        ‖∑ i, T (x i) (y i)‖ ^ 2 ≤
          C * ‖∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))‖) →
      ∃! T' : Z → W,
        (∃ C' : ℝ, IsBoundedModuleMap (cstarBInner 𝒞 Z) (cstarBInner 𝒞 W)
          C' T') ∧ ∀ (x : X) (y : Y), T' (η x y) = T x y

attribute [instance] ExtTensor.nacg ExtTensor.nsp ExtTensor.smul
  ExtTensor.cstarMod ExtTensor.complete

variable {t : 𝒜 → ℬ → 𝒞} {ht : IsVNTensor t}

/-! ### Auxiliary for **164II** and **164II**.1: ultranorm density of `𝒜 ⊙ ℬ`

This block sat below `ext_tensor_uniqueness` until session 79, when the
*existence* proof of **164II** turned out to need it too (`unDense_tSpan` is
the input to the `𝒜 ⊙ ℬ → 𝒜 ⊗ ℬ` coefficient upgrade there); it was moved up
unchanged, so that `univprop_ext_tensor` could stay where it is.

The thesis's **164VII** (`ultranorm-dense-tensor-base`) reads the density off
its own construction of `X ⊗ Y` as `ℓ²((pᵢⱼ))`.  Our statement quantifies
over an *arbitrary* `E : ExtTensor`, so the density has to come from the
universal property instead — exactly as in `selfdual_compl_defining_dense`
(**163II**), through the orthogonal projection onto `D^⊥⊥` (`exists_orthoProj`)
and **160IV**.2.  The one step that does not transfer verbatim is that
**160IV**.2 identifies `D^⊥⊥` with the ultranorm closure of the `𝒞`-**span**
of `D = {∑ᵢ xᵢ ⊗ yᵢ}`, which is strictly bigger than `D`: the latter absorbs
elementary tensors `t a b` only.  Bridging that gap *is* the thesis's own
argument for 164VII — `𝒜 ⊙ ℬ` is ultrastrongly dense in `𝒜 ⊗ ℬ` (by `tensor`
and `ultraclosed`), so `D·(𝒜 ⊙ ℬ)` is ultranorm dense in `D·(𝒜 ⊗ ℬ)` — and
it is developed here.  Note that no *bounded* net is needed for it, so
Kaplansky density (**158Ia**, `kaplansky_bounded_approx`) does not enter. -/

section TensorDense

variable (t) in
/-- The algebraic tensor product `𝒜 ⊙ ℬ` seen inside `𝒞 = 𝒜 ⊗ ℬ`: the finite
sums of elementary tensors.  (Auxiliary for **164II**.1.) -/
private def tSpan : Set 𝒞 :=
  {c : 𝒞 | ∃ (n : ℕ) (a : Fin n → 𝒜) (b : Fin n → ℬ), c = ∑ i, t (a i) (b i)}

private theorem t_mem_tSpan (a : 𝒜) (b : ℬ) : t a b ∈ tSpan t :=
  ⟨1, fun _ => a, fun _ => b, by simp⟩

private theorem tSpan_add {c d : 𝒞} (hc : c ∈ tSpan t) (hd : d ∈ tSpan t) :
    c + d ∈ tSpan t := by
  obtain ⟨n, a, b, rfl⟩ := hc
  obtain ⟨m, a', b', rfl⟩ := hd
  refine ⟨n + m, Fin.append a a', Fin.append b b', ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

private theorem tSpan_star (ht : IsVNTensor t) {c : 𝒞} (hc : c ∈ tSpan t) :
    star c ∈ tSpan t := by
  obtain ⟨n, a, b, rfl⟩ := hc
  refine ⟨n, fun i => star (a i), fun i => star (b i), ?_⟩
  rw [star_sum]
  exact Finset.sum_congr rfl fun i _ => ht.star (a i) (b i)

private theorem tSpan_mul (ht : IsVNTensor t) {c d : 𝒞} (hc : c ∈ tSpan t)
    (hd : d ∈ tSpan t) : c * d ∈ tSpan t := by
  obtain ⟨n, a, b, rfl⟩ := hc
  obtain ⟨m, a', b', rfl⟩ := hd
  have h1 : (∑ i, t (a i) (b i)) * ∑ j, t (a' j) (b' j)
      = ∑ p : Fin n × Fin m, t (a p.1 * a' p.2) (b p.1 * b' p.2) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ht.mul _ _ _ _
  refine ⟨n * m,
    fun k => a (finProdFinEquiv.symm k).1 * a' (finProdFinEquiv.symm k).2,
    fun k => b (finProdFinEquiv.symm k).1 * b' (finProdFinEquiv.symm k).2, ?_⟩
  rw [h1]
  exact Fintype.sum_equiv finProdFinEquiv _ _ fun p => by simp

variable (ht) in
/-- `𝒜 ⊙ ℬ` as a unital `*`-subalgebra of `𝒞 = 𝒜 ⊗ ℬ`. -/
private def tSpanSubalg : StarSubalgebra ℂ 𝒞 where
  carrier := tSpan t
  mul_mem' := tSpan_mul ht
  add_mem' := tSpan_add
  one_mem' := ⟨1, fun _ => 1, fun _ => 1, by simp [ht.one]⟩
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  algebraMap_mem' := fun r => ⟨1, fun _ => r • (1 : 𝒜), fun _ => 1, by
    simp [ht.smul_complex, ht.one, Algebra.algebraMap_eq_smul_one]⟩
  star_mem' := tSpan_star ht

/-- **The algebraic tensor product is ultrastrongly dense**: this is the
thesis's "by `tensor` (and `ultraclosed`) `𝒜 ⊙ ℬ` is ultrastrongly dense in
`𝒜 ⊗ ℬ`" (dils.tex:5153), in the mirrored (`mulInner`) ultranorm form used
throughout this file.  It needs only the *generation* clause of `IsVNTensor`,
plus thesis A's `isVNSubalgebra_usClosureSubalgebra` (the ultrastrong closure
of a `*`-subalgebra is a von Neumann subalgebra), which makes `W*(𝒜 ⊙ ℬ)`
land inside that closure. -/
private theorem unDense_tSpan [VonNeumannAlgebra 𝒞] (ht : IsVNTensor t) :
    UnDense (mulInner 𝒞) (tSpan t) := by
  have hclosed : ∀ c : 𝒞, c ∈ @closure 𝒞 (ultrastrong 𝒞) (tSpan t) := by
    have hmem : usClosureSubalgebra (tSpanSubalg ht) ∈
        {T : StarSubalgebra ℂ 𝒞 | IsVNSubalgebra 𝒞 T ∧
          (Set.range fun p : 𝒜 × ℬ => t p.1 p.2) ⊆ T} := by
      refine ⟨isVNSubalgebra_usClosureSubalgebra _, ?_⟩
      rintro _ ⟨p, rfl⟩
      exact @subset_closure 𝒞 (ultrastrong 𝒞) (tSpan t) _ (t_mem_tSpan p.1 p.2)
    have hle : wstar 𝒞 (Set.range fun p : 𝒜 × ℬ => t p.1 p.2)
        ≤ usClosureSubalgebra (tSpanSubalg ht) := sInf_le hmem
    rw [ht.generates] at hle
    intro c
    exact hle (by simp : c ∈ (⊤ : StarSubalgebra ℂ 𝒞))
  intro c n ωs ε hε
  obtain ⟨z, hz, hlt⟩ := (mem_usClosure_iff (tSpan t) (star c)).mp
    (hclosed (star c)) (npSum n ωs) ε hε
  refine ⟨star z, tSpan_star ht hz, fun i => ?_⟩
  rw [unSeminorm_mulInner_eq, star_sub, star_star]
  calc omegaNorm 𝒞 (ωs i) (star c - z)
      = omegaNorm 𝒞 (ωs i) (z - star c) := by rw [← omegaNorm_neg, neg_sub]
    _ ≤ omegaNorm 𝒞 (npSum n ωs) (z - star c) := omegaNorm_le_npSum n ωs i _
    _ ≤ ε := hlt.le

variable {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [SMul 𝒞 Z]
  [CStarModule 𝒞 Z]

/-- `(∑ᵢ cᵢ)·z = ∑ᵢ (cᵢ·z)`; the companion of `op_smul_sum`. -/
private theorem add_smul_sum {κ : Type*} (s : Finset κ) (f : κ → 𝒞) (z : Z) :
    (∑ i ∈ s, f i) • z = ∑ i ∈ s, f i • z := by
  classical
  refine Finset.induction_on s (by simp [op_zero_smul]) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, op_add_smul, ih, Finset.sum_insert hi]

/-- `‖c·z‖_ω ≤ ‖z‖·‖c‖_ω`: the module action is ultranorm continuous in the
*algebra* variable, uniformly on norm-bounded sets — where `‖c‖_ω` is the
mirrored ultrastrong seminorm `ω(cc*)^½` (`mulInner`).  This is the estimate
behind the thesis's "so `E(𝒜 ⊙ ℬ)` is ultranorm dense in `E(𝒜 ⊗ ℬ)`, see
`ultranormcontstruct`" (dils.tex:5155); it is `c⟨z,z⟩c* ≤ ‖⟨z,z⟩‖ cc*`. -/
private theorem unSeminorm_op_smul_le [VonNeumannAlgebra 𝒞]
    (ω : NPFunctional 𝒞) (c : 𝒞) (z : Z) :
    unSeminorm ω (inner 𝒞 : Z → Z → 𝒞) (c • z)
      ≤ ‖z‖ * unSeminorm ω (mulInner 𝒞) c := by
  have hinner : (inner 𝒞 (c • z) (c • z) : 𝒞) = c * (inner 𝒞 z z : 𝒞) * star c := by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_left, mul_assoc]
  have hsa : IsSelfAdjoint (inner 𝒞 z z : 𝒞) :=
    IsSelfAdjoint.of_nonneg (CStarModule.inner_self_nonneg (A := 𝒞))
  have hle : c * (inner 𝒞 z z : 𝒞) * star c
      ≤ ‖(inner 𝒞 z z : 𝒞)‖ • (c * star c) :=
    CStarAlgebra.star_right_conjugate_le_norm_smul hsa
  have hnorm : ‖(inner 𝒞 z z : 𝒞)‖ = ‖z‖ ^ 2 := (CStarModule.norm_sq_eq (A := 𝒞) (x := z)).symm
  have hsmul : ((‖z‖ ^ 2 : ℝ) • (c * star c) : 𝒞)
      = ((‖z‖ ^ 2 : ℝ) : ℂ) • (c * star c) := by
    rw [← Complex.coe_algebraMap, algebraMap_smul]
  have hre : (ω (c * (inner 𝒞 z z : 𝒞) * star c)).re
      ≤ ‖z‖ ^ 2 * (ω (c * star c)).re := by
    have h1 := np_re_mono' ω hle
    rwa [hnorm, hsmul, npf_csmul, Complex.re_ofReal_mul] at h1
  have hm : mulInner 𝒞 c c = c * star c := rfl
  rw [unSeminorm, unSeminorm, hinner, hm]
  calc Real.sqrt (ω (c * (inner 𝒞 z z : 𝒞) * star c)).re
      ≤ Real.sqrt (‖z‖ ^ 2 * (ω (c * star c)).re) := Real.sqrt_le_sqrt hre
    _ = ‖z‖ * Real.sqrt ((ω (c * star c)).re) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg z)]

end TensorDense

/-! ### The construction behind **164II** (existence)

The thesis builds `X ⊗ Y` as `ℓ²((pᵢⱼ))` for orthonormal bases of `X` and
`Y` (164III–164VIII).  The route here is the one the survey names as the
shortcut, now that **150II** `dils_completion` and **151Ia**
`selfdual_completion_univ` are both proved: `X ⊗ Y` is the *self-dual
completion* of `V = (X ⊙ Y) ⊙ 𝒞` — an honest `𝒞`-module, which `X ⊙ Y`
alone is not — with the `𝒞`-valued inner product
`[(x ⊗ y) ⊗ c, (x' ⊗ y') ⊗ c'] = c' (⟨x,x'⟩ ⊗ ⟨y,y'⟩) c*`.

⚠️ **This is not the same three-step shape as `existence_paschke`.**  The
thesis itself flags the difference (dils.tex:5166, **164VIII**): "If `X ⊙ Y`
were an `𝒜 ⊗ ℬ`-module *and* both `η` and `T` were `𝒜 ⊗ ℬ`-linear, we could
simply apply `selfdual-completion-univ`… Instead, we will retrace the steps
of its proof."  The `univ` field of `ExtTensor` bounds `T` over families of
*elementary* tensors only, i.e. with coefficients in `𝒜 ⊙ ℬ`, whereas the
lift to `V` has coefficients in all of `𝒜 ⊗ ℬ`.  Bridging that gap — instead
of retracing the ~360 lines of 151Ia — is `tensor_gram_le` below, and it
takes the three steps documented at `tensor_bound_tSpan`,
`le_smul_of_conj_norm_le` and `nonneg_of_unDense`.

Positivity of the inner product on `V` is **113II**/**113IV**
(`matBilin_nonneg_of_mi`) applied to the two Gram matrices, with the
`𝒞`-coefficients that lemma already allows.

Two hypotheses of the theorem are **not used**: self-duality (and
completeness) of `X` and of `Y`.  The thesis needs them for its orthonormal
bases; the completion route does not. -/

section UnivPropExistence

/-- **The order form of a norm bound, over a dense subalgebra.**  This is the
device that replaces the thesis's passage to the norm completions
(dils.tex:5190): `T` is bounded only over `𝒜 ⊙ ℬ`-coefficients, and the
resolvent `(B + ε)^{-½}` that the proof of **144V**
`blinear_inprod_inequality` needs does *not* lie in `𝒜 ⊙ ℬ` — but it does lie
in its norm closure (the spatial tensor product, which is exactly what
dils.tex passes to), and `cfc_mem` puts it there.  Everything else is the
proof of 144V, verbatim. -/
private theorem le_smul_of_conj_norm_le (S : StarSubalgebra ℂ 𝒞)
    {C : ℝ} (hC : 0 ≤ C) {P B : 𝒞} (hP : 0 ≤ P) (hB : 0 ≤ B) (hBS : B ∈ S)
    (h : ∀ d ∈ S, ‖d * P * star d‖ ≤ C * ‖d * B * star d‖) :
    P ≤ C • B := by
  have key : ∀ ε : ℝ, 0 < ε → P ≤ C • B + (C * ε) • (1 : 𝒞) := by
    intro ε hε
    set s : 𝒞 := B + ε • (1 : 𝒞) with hs
    have hsp : IsStrictlyPositive s :=
      IsStrictlyPositive.nonneg_add hB (IsStrictlyPositive.smul hε isStrictlyPositive_one)
    have hsnn : (0 : 𝒞) ≤ s := by
      rw [hs]; exact add_nonneg hB (smul_nonneg hε.le zero_le_one)
    set g : 𝒞 := s ^ (-(1 / 2) : ℝ) with hg
    set k : 𝒞 := s ^ ((1 / 2) : ℝ) with hk
    have hgnn : (0 : 𝒞) ≤ g := CFC.rpow_nonneg
    have hknn : (0 : 𝒞) ≤ k := CFC.rpow_nonneg
    have hgsa : IsSelfAdjoint g := IsSelfAdjoint.of_nonneg hgnn
    have hksa : IsSelfAdjoint k := IsSelfAdjoint.of_nonneg hknn
    have hgstar : star g = g := hgsa
    have hconj : g * s * g = 1 := CFC.conjugate_rpow_neg_one_half s hsp
    have hkg : k * g = 1 := by
      rw [hk, hg, ← CFC.rpow_add hsp.isUnit]
      norm_num
      exact CFC.rpow_zero s
    have hgk : g * k = 1 := by
      rw [hk, hg, ← CFC.rpow_add hsp.isUnit]
      norm_num
      exact CFC.rpow_zero s
    have hkk : k * k = s := by
      rw [hk, ← CFC.rpow_add hsp.isUnit]
      norm_num
      exact CFC.rpow_one s
    -- `g` lies in the norm closure of `S`
    have hsS : s ∈ S.topologicalClosure := by
      refine add_mem (S.le_topologicalClosure hBS) ?_
      have hsm : (ε : ℝ) • (1 : 𝒞) = ((ε : ℂ)) • (1 : 𝒞) := by
        rw [← IsScalarTower.algebraMap_smul ℂ ε (1 : 𝒞), Complex.coe_algebraMap]
      rw [hsm]
      exact SMulMemClass.smul_mem _ (one_mem _)
    have hgS : g ∈ S.topologicalClosure := by
      have : IsClosed ((S.topologicalClosure : StarSubalgebra ℂ 𝒞) : Set 𝒞) :=
        S.isClosed_topologicalClosure
      rw [hg, CFC.rpow_eq_cfc_real hsnn]
      exact cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) _ hsS
    have hgcl : g ∈ closure (S : Set 𝒞) := hgS
    obtain ⟨d, hdS, hdlim⟩ := mem_closure_iff_seq_limit.mp hgcl
    -- pass the hypothesis to the limit
    have hcont1 : Tendsto (fun n => ‖d n * P * star (d n)‖) atTop (𝓝 ‖g * P * star g‖) := by
      have : Tendsto (fun n => d n * P * star (d n)) atTop (𝓝 (g * P * star g)) := by
        exact ((hdlim.mul tendsto_const_nhds).mul (hdlim.star))
      exact this.norm
    have hcont2 : Tendsto (fun n => C * ‖d n * B * star (d n)‖) atTop
        (𝓝 (C * ‖g * B * star g‖)) := by
      have : Tendsto (fun n => d n * B * star (d n)) atTop (𝓝 (g * B * star g)) := by
        exact ((hdlim.mul tendsto_const_nhds).mul (hdlim.star))
      exact (this.norm).const_mul C
    have hlim : ‖g * P * star g‖ ≤ C * ‖g * B * star g‖ :=
      le_of_tendsto_of_tendsto' hcont1 hcont2 fun n => h (d n) (hdS n)
    -- `g B g ≤ 1`
    have hgBg : g * B * star g ≤ 1 := by
      rw [hgstar]
      calc g * B * g ≤ g * s * g :=
            hgsa.conjugate_le_conjugate
              (by rw [hs]; exact le_add_of_nonneg_right (smul_nonneg hε.le zero_le_one))
        _ = 1 := hconj
    have hgBgnn : (0 : 𝒞) ≤ g * B * star g := by
      rw [hgstar]
      exact conjugate_nonneg_of_nonneg hB hgnn
    have hnB : ‖g * B * star g‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ hgBgnn).mpr hgBg
    have hnP : ‖g * P * star g‖ ≤ C := by
      calc ‖g * P * star g‖ ≤ C * ‖g * B * star g‖ := hlim
        _ ≤ C * 1 := by gcongr
        _ = C := mul_one C
    have hPnn : (0 : 𝒞) ≤ g * P * star g := by
      rw [hgstar]; exact conjugate_nonneg_of_nonneg hP hgnn
    have h4 : g * P * star g ≤ C • (1 : 𝒞) := by
      refine le_trans (hPnn.isSelfAdjoint.le_algebraMap_norm_self) ?_
      rw [Algebra.algebraMap_eq_smul_one]
      have hh : (0 : 𝒞) ≤ (C - ‖g * P * star g‖) • (1 : 𝒞) :=
        smul_nonneg (by linarith) zero_le_one
      rw [sub_smul] at hh
      exact sub_nonneg.mp hh
    have h5 := hksa.conjugate_le_conjugate h4
    have hlhs : k * (g * P * star g) * k = P := by
      rw [hgstar]
      calc k * (g * P * g) * k = (k * g) * P * (g * k) := by simp only [mul_assoc]
        _ = P := by rw [hkg, hgk, one_mul, mul_one]
    have hrhs : k * (C • (1 : 𝒞)) * k = C • B + (C * ε) • (1 : 𝒞) := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, hkk, hs, smul_add, smul_smul]
    rw [hlhs, hrhs] at h5
    exact h5
  have hlim : Tendsto (fun ε : ℝ => C • B + (C * ε) • (1 : 𝒞))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (C • B)) := by
    have hcont : Continuous (fun ε : ℝ => C • B + (C * ε) • (1 : 𝒞)) := by fun_prop
    have h0 := hcont.tendsto 0
    simp only [mul_zero, zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε using key ε hε


/-- **From `𝒜 ⊙ ℬ`- to `𝒜 ⊗ ℬ`-coefficients.**  A self-adjoint matrix `Q`
over `𝒞` whose quadratic form is positive on an ultranorm dense set `D` has
positive quadratic form everywhere.  Kaplansky density is *not* needed: the
form is continuous for the GNS seminorms `‖·‖_ω` of the np-functionals
(Cauchy–Schwarz `norm_apply_star_mul_le` and `omegaNorm_mul_le`), in which
`D` is dense by hypothesis, and `nonneg_of_conjNP` (**44XI**) turns
`ω(z) ≥ 0` for every np `ω` into `z ≥ 0`. -/
private theorem nonneg_of_unDense [VonNeumannAlgebra 𝒞] (D : Set 𝒞)
    (hD : UnDense (mulInner 𝒞) D) {n : ℕ} (Q : Fin n → Fin n → 𝒞)
    (hQ : ∀ i j, star (Q i j) = Q j i)
    (h : ∀ d : Fin n → 𝒞, (∀ k, d k ∈ D) →
      0 ≤ ∑ i, ∑ j, d j * Q i j * star (d i))
    (c : Fin n → 𝒞) : 0 ≤ ∑ i, ∑ j, c j * Q i j * star (c i) := by
  classical
  set z : 𝒞 := ∑ i, ∑ j, c j * Q i j * star (c i) with hz
  -- `z` is self-adjoint
  have hzsa : star z = z := by
    rw [hz, star_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul, star_mul, star_star, hQ, mul_assoc]
  -- the main estimate, for one np-functional
  have main : ∀ ω : NPFunctional 𝒞, (0 : ℂ) ≤ ω z := by
    intro ω
    have him : (ω z).im = 0 := by
      have h1 : ω (star z) = star (ω z) := npFunctional_star ω z
      rw [hzsa] at h1
      have := congrArg Complex.im h1
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    set N : Fin n → ℝ := fun i => omegaNorm 𝒞 ω (star (c i)) with hN
    set K : ℝ := ∑ i, ∑ j, ‖Q i j‖ * (N i + N j + 1) with hK
    have hNnn : ∀ i, 0 ≤ N i := fun i => omegaNorm_nonneg _ _
    have hKnn : (0 : ℝ) ≤ K := by
      rw [hK]
      refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
      have := hNnn i; have := hNnn j
      positivity
    have hre : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → -(ε * K) ≤ (ω z).re := by
      intro ε hε hε1
      choose d hdD hd using fun k => hD (c k) 1 (fun _ => ω) ε hε
      have hd' : ∀ k, omegaNorm 𝒞 ω (star (c k - d k)) ≤ ε := by
        intro k
        have := hd k 0
        rwa [unSeminorm_mulInner_eq] at this
      set zd : 𝒞 := ∑ i, ∑ j, d j * Q i j * star (d i) with hzd
      have hzdnn : (0 : 𝒞) ≤ zd := h d hdD
      have hzdre : 0 ≤ (ω zd).re :=
        (Complex.le_def.mp (npFunctional_nonneg ω hzdnn)).1
      -- the difference
      have hdiff : z - zd = ∑ i, ∑ j,
          ((c j - d j) * Q i j * star (c i) + d j * Q i j * star (c i - d i)) := by
        rw [hz, hzd, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [star_sub]
        noncomm_ring
      have hbound : ‖ω (z - zd)‖ ≤ ε * K := by
        rw [hdiff]
        have hmapsum : ∀ (f : Fin n → 𝒞), ω (∑ i, f i) = ∑ i, ω (f i) :=
          fun f => map_sum ω.toPositiveLinearMap f Finset.univ
        have hsum : ω (∑ i, ∑ j,
            ((c j - d j) * Q i j * star (c i) + d j * Q i j * star (c i - d i)))
            = ∑ i, ∑ j, (ω ((c j - d j) * Q i j * star (c i))
              + ω (d j * Q i j * star (c i - d i))) := by
          rw [hmapsum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hmapsum]
          refine Finset.sum_congr rfl fun j _ => ?_
          exact map_add ω.toPositiveLinearMap _ _
        rw [hsum]
        calc ‖∑ i, ∑ j, (ω ((c j - d j) * Q i j * star (c i))
                + ω (d j * Q i j * star (c i - d i)))‖
            ≤ ∑ i, ∑ j, ‖ω ((c j - d j) * Q i j * star (c i))
                + ω (d j * Q i j * star (c i - d i))‖ :=
              (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
          _ ≤ ∑ i, ∑ j, (ε * (‖Q i j‖ * N i) + (N j + ε) * (‖Q i j‖ * ε)) := by
              refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
              refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
              · have h1 : ‖ω ((c j - d j) * Q i j * star (c i))‖
                    ≤ omegaNorm 𝒞 ω (star (c j - d j))
                      * omegaNorm 𝒞 ω (Q i j * star (c i)) := by
                  have := norm_apply_star_mul_le ω (star (c j - d j)) (Q i j * star (c i))
                  rwa [star_star, ← mul_assoc] at this
                refine h1.trans (mul_le_mul (hd' j) ?_ (omegaNorm_nonneg _ _) hε.le)
                exact omegaNorm_mul_le ω _ _
              · have h1 : ‖ω (d j * Q i j * star (c i - d i))‖
                    ≤ omegaNorm 𝒞 ω (star (d j))
                      * omegaNorm 𝒞 ω (Q i j * star (c i - d i)) := by
                  have := norm_apply_star_mul_le ω (star (d j)) (Q i j * star (c i - d i))
                  rwa [star_star, ← mul_assoc] at this
                have h2 : omegaNorm 𝒞 ω (star (d j)) ≤ N j + ε := by
                  have hsplit : star (d j) = star (c j) - star (c j - d j) := by
                    rw [star_sub]; abel
                  have h4 : omegaNorm 𝒞 ω (star (d j))
                      ≤ omegaNorm 𝒞 ω (star (c j)) + omegaNorm 𝒞 ω (star (c j - d j)) := by
                    rw [hsplit]
                    have := omegaNorm_add_le ω (star (c j)) (-star (c j - d j))
                    rwa [omegaNorm_neg, ← sub_eq_add_neg] at this
                  have h5 := hd' j
                  simp only [hN]
                  linarith
                have h3 : omegaNorm 𝒞 ω (Q i j * star (c i - d i)) ≤ ‖Q i j‖ * ε :=
                  (omegaNorm_mul_le ω _ _).trans
                    (mul_le_mul_of_nonneg_left (hd' i) (norm_nonneg _))
                exact h1.trans (mul_le_mul h2 h3 (omegaNorm_nonneg _ _)
                  (by have := hNnn j; linarith))
          _ ≤ ε * K := by
              rw [hK, Finset.mul_sum]
              refine Finset.sum_le_sum fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_le_sum fun j _ => ?_
              have h1 := hNnn i
              have h2 := hNnn j
              have h3 : (0 : ℝ) ≤ ‖Q i j‖ := norm_nonneg _
              nlinarith [mul_nonneg h3 h2, mul_nonneg h3 h1,
                mul_nonneg (mul_nonneg hε.le h3) (sub_nonneg.mpr hε1)]
      have hre1 : (ω zd).re - (ω z).re ≤ ε * K := by
        have habs : |(ω (z - zd)).re| ≤ ‖ω (z - zd)‖ := Complex.abs_re_le_norm _
        have h2 : ω (z - zd) = ω z - ω zd := npFunctional_sub ω z zd
        have h3 : |(ω z - ω zd).re| ≤ ε * K := by rw [← h2]; exact habs.trans hbound
        have h4 := abs_le.mp h3
        simp only [Complex.sub_re] at h4
        linarith [h4.1]
      linarith
    have hre0 : 0 ≤ (ω z).re := by
      by_contra hcon
      push_neg at hcon
      set ε : ℝ := min 1 (-(ω z).re / (2 * (K + 1))) with hεdef
      have hKpos : (0 : ℝ) < K + 1 := by linarith
      have hnum : (0 : ℝ) < -(ω z).re := by linarith
      have hden : (0 : ℝ) < 2 * (K + 1) := by linarith
      have hε2 : 0 < -(ω z).re / (2 * (K + 1)) := div_pos hnum hden
      have hεpos : 0 < ε := lt_min one_pos hε2
      have hεle1 : ε ≤ 1 := min_le_left _ _
      have hεle2 : ε ≤ -(ω z).re / (2 * (K + 1)) := min_le_right _ _
      have := hre ε hεpos hεle1
      have hKε : ε * K ≤ -(ω z).re / 2 := by
        have h1 : ε * K ≤ (-(ω z).re / (2 * (K + 1))) * K :=
          mul_le_mul_of_nonneg_right hεle2 hKnn
        have h2 : (-(ω z).re / (2 * (K + 1))) * K ≤ -(ω z).re / 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hden]
          nlinarith
        linarith
      linarith
    exact Complex.le_def.mpr ⟨by simpa using hre0, by simp [him]⟩
  refine nonneg_of_conjNP fun ω c₀ => ?_
  have := main (conjNP c₀ ω)
  rwa [conjNP_apply] at this


section TensorGram

variable {W : Type u} [NormedAddCommGroup W] [NormedSpace ℂ W] [SMul 𝒞 W]
  [CStarModule 𝒞 W]

variable {C : ℝ} {T : X → Y → W}

private theorem bound_fintype
    (hbound : ∀ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
      ‖∑ i, T (x i) (y i)‖ ^ 2 ≤
        C * ‖∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))‖)
    {ι : Type} [Fintype ι] (x : ι → X) (y : ι → Y) :
    ‖∑ i, T (x i) (y i)‖ ^ 2 ≤
      C * ‖∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))‖ := by
  classical
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he
  have h := hbound (Fintype.card ι) (fun i => x (e i)) (fun i => y (e i))
  have h1 : ∑ i, T (x (e i)) (y (e i)) = ∑ i, T (x i) (y i) :=
    Fintype.sum_equiv e _ _ fun i => rfl
  have h2 : ∑ i, ∑ j, t (inner 𝒜 (x (e i)) (x (e j))) (inner ℬ (y (e i)) (y (e j)))
      = ∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j)) :=
    Fintype.sum_equiv e _ _ fun i => Fintype.sum_equiv e _ _ fun j => rfl
  rw [h1, h2] at h
  exact h

private theorem tensor_bound_tSpan (ht : IsVNTensor t)
    (hTs : ∀ (a : 𝒜) (b : ℬ) (x : X) (y : Y), T (a • x) (b • y) = t a b • T x y)
    (hbound : ∀ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
      ‖∑ i, T (x i) (y i)‖ ^ 2 ≤
        C * ‖∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))‖)
    {n : ℕ} (x : Fin n → X) (y : Fin n → Y) (c : Fin n → 𝒞)
    (hc : ∀ k, ∃ (m : ℕ) (a : Fin m → 𝒜) (b : Fin m → ℬ),
      c k = ∑ l, t (a l) (b l)) :
    ‖∑ k, c k • T (x k) (y k)‖ ^ 2 ≤
      C * ‖∑ i, ∑ j, c j * t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))
        * star (c i)‖ := by
  classical
  choose m a b hab using hc
  have h := bound_fintype (t := t) (T := T) hbound
    (ι := Σ k : Fin n, Fin (m k))
    (fun p => a p.1 p.2 • x p.1) (fun p => b p.1 p.2 • y p.1)
  have hLHS : ∑ p : Σ k : Fin n, Fin (m k),
      T (a p.1 p.2 • x p.1) (b p.1 p.2 • y p.1) = ∑ k, c k • T (x k) (y k) := by
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hstep : ∀ l ∈ Finset.univ, T (a k l • x k) (b k l • y k)
        = t (a k l) (b k l) • T (x k) (y k) := fun l _ => hTs _ _ _ _
    rw [Finset.sum_congr rfl hstep, ← add_smul_sum, ← hab k]
  have hinner : ∀ (p q : Σ k : Fin n, Fin (m k)),
      t (inner 𝒜 (a p.1 p.2 • x p.1) (a q.1 q.2 • x q.1))
        (inner ℬ (b p.1 p.2 • y p.1) (b q.1 q.2 • y q.1))
      = t (a q.1 q.2) (b q.1 q.2)
          * t (inner 𝒜 (x p.1) (x q.1)) (inner ℬ (y p.1) (y q.1))
          * star (t (a p.1 p.2) (b p.1 p.2)) := by
    intro p q
    rw [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
      CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
      ht.star, ← ht.mul, ← ht.mul]
  have hRHS : ∑ p : Σ k : Fin n, Fin (m k), ∑ q : Σ k : Fin n, Fin (m k),
      t (inner 𝒜 (a p.1 p.2 • x p.1) (a q.1 q.2 • x q.1))
        (inner ℬ (b p.1 p.2 • y p.1) (b q.1 q.2 • y q.1))
      = ∑ i, ∑ j, c j * t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))
          * star (c i) := by
    have hq : ∀ (p : Σ k : Fin n, Fin (m k)),
        ∑ q : Σ k : Fin n, Fin (m k),
          t (a q.1 q.2) (b q.1 q.2)
            * t (inner 𝒜 (x p.1) (x q.1)) (inner ℬ (y p.1) (y q.1))
        = ∑ j, c j * t (inner 𝒜 (x p.1) (x j)) (inner ℬ (y p.1) (y j)) := by
      intro p
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only
      rw [← Finset.sum_mul, ← hab j]
    calc ∑ p : Σ k : Fin n, Fin (m k), ∑ q : Σ k : Fin n, Fin (m k),
          t (inner 𝒜 (a p.1 p.2 • x p.1) (a q.1 q.2 • x q.1))
            (inner ℬ (b p.1 p.2 • y p.1) (b q.1 q.2 • y q.1))
        = ∑ p : Σ k : Fin n, Fin (m k),
            (∑ j, c j * t (inner 𝒜 (x p.1) (x j)) (inner ℬ (y p.1) (y j)))
              * star (t (a p.1 p.2) (b p.1 p.2)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← hq p, Finset.sum_mul]
          exact Finset.sum_congr rfl fun q _ => hinner p q
      _ = ∑ i, ∑ j, c j * t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))
            * star (c i) := by
          rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
          refine Finset.sum_congr rfl fun i _ => ?_
          dsimp only
          rw [← Finset.mul_sum, ← star_sum, ← hab i, Finset.sum_mul]
  rw [hLHS, hRHS] at h
  exact h


private theorem gram_t_nonneg (ht : IsVNTensor t) {n : ℕ} (x : Fin n → X) (y : Fin n → Y)
    (d : Fin n → 𝒞) :
    0 ≤ ∑ i, ∑ j, d j * t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))
      * star (d i) := by
  have h := matBilin_nonneg_of_mi t ht.add_left ht.add_right ht.mul ht.star
    (CStarMatrix.ofMatrix (Matrix.of fun i j => (inner 𝒜 (x j) (x i) : 𝒜)))
    (CStarMatrix.ofMatrix (Matrix.of fun i j => (inner ℬ (y j) (y i) : ℬ)))
    (gram_nonneg x) (gram_nonneg y) (fun i => star (d i))
  have heq : (∑ i, ∑ j, star (star (d i))
        * t ((CStarMatrix.ofMatrix (Matrix.of fun i j => (inner 𝒜 (x j) (x i) : 𝒜))) i j)
            ((CStarMatrix.ofMatrix (Matrix.of fun i j => (inner ℬ (y j) (y i) : ℬ))) i j)
        * star (d j))
      = ∑ i, ∑ j, d j * t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j)) * star (d i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_star]
    rfl
  rwa [heq] at h

/-- The estimate that the universal property of **164II** needs: the Gram
bound over families of *elementary* tensors implies the Gram bound with
arbitrary `𝒞`-coefficients, in its order form. -/
private theorem tensor_gram_le [VonNeumannAlgebra 𝒞] (ht : IsVNTensor t) (hC : 0 ≤ C)
    (hTs : ∀ (a : 𝒜) (b : ℬ) (x : X) (y : Y), T (a • x) (b • y) = t a b • T x y)
    (hbound : ∀ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
      ‖∑ i, T (x i) (y i)‖ ^ 2 ≤
        C * ‖∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))‖)
    (S : StarSubalgebra ℂ 𝒞) (hSt : ∀ (a : 𝒜) (b : ℬ), t a b ∈ S)
    (hSrep : ∀ z ∈ S, ∃ (m : ℕ) (a : Fin m → 𝒜) (b : Fin m → ℬ),
      z = ∑ l, t (a l) (b l))
    (hSdense : UnDense (mulInner 𝒞) (S : Set 𝒞))
    {n : ℕ} (x : Fin n → X) (y : Fin n → Y) (c : Fin n → 𝒞) :
    inner 𝒞 (∑ k, c k • T (x k) (y k)) (∑ k, c k • T (x k) (y k))
      ≤ C • ∑ i, ∑ j, c j * t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))
          * star (c i) := by
  classical
  set M : Fin n → Fin n → 𝒞 :=
    fun i j => t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j)) with hM
  set P : Fin n → Fin n → 𝒞 :=
    fun i j => inner 𝒞 (T (x i) (y i)) (T (x j) (y j)) with hP
  have hexp : ∀ d : Fin n → 𝒞,
      inner 𝒞 (∑ k, d k • T (x k) (y k)) (∑ k, d k • T (x k) (y k))
        = ∑ i, ∑ j, d j * P i j * star (d i) := by
    intro d
    rw [CStarModule.inner_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [CStarModule.inner_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right]
  have hscale : ∀ (e : 𝒞) (d : Fin n → 𝒞) (F : Fin n → Fin n → 𝒞),
      ∑ i, ∑ j, (e * d j) * F i j * star (e * d i)
        = e * (∑ i, ∑ j, d j * F i j * star (d i)) * star e := by
    intro e d F
    simp only [Finset.mul_sum, Finset.sum_mul, star_mul]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by noncomm_ring
  have hMpos : ∀ d : Fin n → 𝒞, 0 ≤ ∑ i, ∑ j, d j * M i j * star (d i) :=
    fun d => gram_t_nonneg ht x y d
  have hMval : ∀ i j, M i j = t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j)) :=
    fun _ _ => rfl
  have hPval : ∀ i j, P i j = inner 𝒞 (T (x i) (y i)) (T (x j) (y j)) :=
    fun _ _ => rfl
  have hMs : ∀ i j, star (M i j) = M j i := by
    intro i j
    rw [hMval, hMval, ht.star, CStarModule.star_inner, CStarModule.star_inner]
  have hPs : ∀ i j, star (P i j) = P j i := by
    intro i j
    rw [hPval, hPval, CStarModule.star_inner]
  have hQstar : ∀ i j, star (C • M i j - P i j) = C • M j i - P j i := by
    intro i j
    rw [star_sub, star_smul, star_trivial, hMs, hPs]
  have hkey : ∀ d : Fin n → 𝒞, (∀ k, d k ∈ S) →
      ∑ i, ∑ j, d j * P i j * star (d i)
        ≤ C • ∑ i, ∑ j, d j * M i j * star (d i) := by
    intro d hd
    have hPnn : (0 : 𝒞) ≤ ∑ i, ∑ j, d j * P i j * star (d i) := by
      rw [← hexp d]; exact CStarModule.inner_self_nonneg
    have hmem : (∑ i, ∑ j, d j * M i j * star (d i)) ∈ S :=
      sum_mem fun i _ => sum_mem fun j _ =>
        mul_mem (mul_mem (hd j) (hSt _ _)) (star_mem (hd i))
    refine le_smul_of_conj_norm_le S hC hPnn (hMpos d) hmem ?_
    intro e heS
    have h1 := tensor_bound_tSpan ht hTs hbound x y (fun k => e * d k)
      (fun k => hSrep _ (mul_mem heS (hd k)))
    rw [CStarModule.norm_sq_eq (A := 𝒞), hexp (fun k => e * d k),
      hscale e d P, hscale e d M] at h1
    exact h1
  have hfinal := nonneg_of_unDense (S : Set 𝒞) hSdense (fun i j => C • M i j - P i j)
    hQstar (fun d hd => by
      have h := hkey d hd
      rw [← sub_nonneg] at h
      have heq : ∑ i, ∑ j, d j * (C • M i j - P i j) * star (d i)
          = (C • ∑ i, ∑ j, d j * M i j * star (d i))
            - ∑ i, ∑ j, d j * P i j * star (d i) := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
      rw [heq]
      exact h) c
  have heq : ∑ i, ∑ j, c j * (C • M i j - P i j) * star (c i)
      = (C • ∑ i, ∑ j, c j * M i j * star (c i))
        - ∑ i, ∑ j, c j * P i j * star (c i) := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  rw [heq, sub_nonneg] at hfinal
  rw [hexp c]
  exact hfinal

end TensorGram

/-- The `𝒞`-action on `(X ⊙ Y) ⊙ 𝒞`, mirrored: `c · (z ⊗ c') = z ⊗ (c c')`. -/
noncomputable local instance extSMul : SMul 𝒞 ((X ⊗[ℂ] Y) ⊗[ℂ] 𝒞) where
  smul c := LinearMap.lTensor (X ⊗[ℂ] Y) (LinearMap.mulLeft ℂ c)

private theorem ext_smul_tmul (c : 𝒞) (z : X ⊗[ℂ] Y) (c' : 𝒞) :
    c • (z ⊗ₜ[ℂ] c') = z ⊗ₜ[ℂ] (c * c') := rfl

private theorem ext_smul_add (c : 𝒞) (v w : (X ⊗[ℂ] Y) ⊗[ℂ] 𝒞) :
    c • (v + w) = c • v + c • w :=
  map_add (LinearMap.lTensor (X ⊗[ℂ] Y) (LinearMap.mulLeft ℂ c)) v w

private theorem ext_smul_zero (c : 𝒞) : c • (0 : (X ⊗[ℂ] Y) ⊗[ℂ] 𝒞) = 0 :=
  map_zero (LinearMap.lTensor (X ⊗[ℂ] Y) (LinearMap.mulLeft ℂ c))

private theorem ext_smul_sum {κ : Type*} (c : 𝒞) (s : Finset κ)
    (f : κ → (X ⊗[ℂ] Y) ⊗[ℂ] 𝒞) : c • (∑ i ∈ s, f i) = ∑ i ∈ s, c • f i :=
  map_sum (LinearMap.lTensor (X ⊗[ℂ] Y) (LinearMap.mulLeft ℂ c)) f s

variable (t) in
/-- The `𝒞`-valued pairing of `X ⊙ Y` in the second slot, for a fixed
elementary vector `x ⊗ y` in the first. -/
private noncomputable def extB1 (ht : IsVNTensor t) (x : X) (y : Y) :
    (X ⊗[ℂ] Y) →ₗ[ℂ] 𝒞 :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun (x' : X) (y' : Y) => t (inner 𝒜 x x') (inner ℬ y y'))
    (fun x₁ x₂ y' => by rw [CStarModule.inner_add_right, ht.add_left])
    (fun c x' y' => by
      rw [CStarModule.inner_smul_right_complex, ht.smul_complex])
    (fun x' y₁ y₂ => by rw [CStarModule.inner_add_right, ht.add_right])
    (fun c x' y' => by
      rw [CStarModule.inner_smul_right_complex,
        vnTensor_smul_complex_right ht]))

@[simp] private theorem extB1_tmul (ht : IsVNTensor t) (x x' : X) (y y' : Y) :
    extB1 t ht x y (x' ⊗ₜ[ℂ] y') = t (inner 𝒜 x x') (inner ℬ y y') := rfl

variable (t) in
/-- `extB1`, conjugate-linear in the first slot. -/
private noncomputable def extB2 (ht : IsVNTensor t) :
    X →ₛₗ[starRingEnd ℂ] (Y →ₛₗ[starRingEnd ℂ] ((X ⊗[ℂ] Y) →ₗ[ℂ] 𝒞)) where
  toFun x :=
    { toFun := fun y => extB1 t ht x y
      map_add' := fun y₁ y₂ => by
        refine TensorProduct.ext' fun x' y' => ?_
        change t (inner 𝒜 x x') (inner ℬ (y₁ + y₂) y') = _
        rw [CStarModule.inner_add_left, ht.add_right]
        rfl
      map_smul' := fun c y => by
        refine TensorProduct.ext' fun x' y' => ?_
        change t (inner 𝒜 x x') (inner ℬ (c • y) y') = _
        rw [CStarModule.inner_smul_left_complex,
          vnTensor_smul_complex_right ht]
        rfl }
  map_add' x₁ x₂ := by
    ext y x' y'
    change t (inner 𝒜 (x₁ + x₂) x') (inner ℬ y y') = _
    rw [CStarModule.inner_add_left, ht.add_left]
    rfl
  map_smul' c x := by
    ext y x' y'
    change t (inner 𝒜 (c • x) x') (inner ℬ y y') = _
    rw [CStarModule.inner_smul_left_complex, ht.smul_complex]
    rfl

variable (t) in
/-- The pairing of `X ⊙ Y`, conjugate-linear in the first slot. -/
private noncomputable def extPairAux (ht : IsVNTensor t) :
    (X ⊗[ℂ] Y) →ₛₗ[starRingEnd ℂ] ((X ⊗[ℂ] Y) →ₗ[ℂ] 𝒞) :=
  TensorProduct.lift (extB2 t ht)

@[simp] private theorem extPairAux_tmul (ht : IsVNTensor t) (x x' : X) (y y' : Y) :
    extPairAux t ht (x ⊗ₜ[ℂ] y) (x' ⊗ₜ[ℂ] y')
      = t (inner 𝒜 x x') (inner ℬ y y') := rfl


variable (t) in
/-- The pairing of `(X ⊙ Y) ⊙ 𝒞` in the second slot, for a fixed elementary
vector `z ⊗ c` in the first. -/
private noncomputable def extC1 (ht : IsVNTensor t) (z : X ⊗[ℂ] Y) (c : 𝒞) :
    ((X ⊗[ℂ] Y) ⊗[ℂ] 𝒞) →ₗ[ℂ] 𝒞 :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun (z' : X ⊗[ℂ] Y) (c' : 𝒞) => c' * extPairAux t ht z z' * star c)
    (fun z₁ z₂ c' => by rw [map_add, mul_add, add_mul])
    (fun a z' c' => by rw [map_smul, mul_smul_comm, smul_mul_assoc])
    (fun z' c₁ c₂ => by rw [add_mul, add_mul])
    (fun a z' c' => by rw [smul_mul_assoc, smul_mul_assoc]))

@[simp] private theorem extC1_tmul (ht : IsVNTensor t) (z z' : X ⊗[ℂ] Y) (c c' : 𝒞) :
    extC1 t ht z c (z' ⊗ₜ[ℂ] c') = c' * extPairAux t ht z z' * star c := rfl

variable (t) in
/-- `extC1`, conjugate-linear in the first slot. -/
private noncomputable def extC2 (ht : IsVNTensor t) :
    (X ⊗[ℂ] Y) →ₛₗ[starRingEnd ℂ]
      (𝒞 →ₛₗ[starRingEnd ℂ] (((X ⊗[ℂ] Y) ⊗[ℂ] 𝒞) →ₗ[ℂ] 𝒞)) where
  toFun z :=
    { toFun := fun c => extC1 t ht z c
      map_add' := fun c₁ c₂ => by
        refine TensorProduct.ext' fun z' c' => ?_
        rw [extC1_tmul, star_add, mul_add]
        rfl
      map_smul' := fun a c => by
        refine TensorProduct.ext' fun z' c' => ?_
        rw [extC1_tmul, star_smul, mul_smul_comm]
        rfl }
  map_add' z₁ z₂ := by
    refine LinearMap.ext fun c => ?_
    refine TensorProduct.ext' fun z' c' => ?_
    change extC1 t ht (z₁ + z₂) c (z' ⊗ₜ[ℂ] c') = _
    rw [extC1_tmul, map_add, LinearMap.add_apply, mul_add, add_mul]
    rfl
  map_smul' a z := by
    refine LinearMap.ext fun c => ?_
    refine TensorProduct.ext' fun z' c' => ?_
    change extC1 t ht (a • z) c (z' ⊗ₜ[ℂ] c') = _
    rw [extC1_tmul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, mul_smul_comm,
      smul_mul_assoc]
    simp only [LinearMap.smul_apply]
    rfl

variable (t) in
/-- The `𝒞`-valued pairing of `(X ⊙ Y) ⊙ 𝒞`, conjugate-linear in the first
slot. -/
private noncomputable def extPair (ht : IsVNTensor t) :
    ((X ⊗[ℂ] Y) ⊗[ℂ] 𝒞) →ₛₗ[starRingEnd ℂ]
      (((X ⊗[ℂ] Y) ⊗[ℂ] 𝒞) →ₗ[ℂ] 𝒞) :=
  TensorProduct.lift (extC2 t ht)

@[simp] private theorem extPair_tmul (ht : IsVNTensor t) (z z' : X ⊗[ℂ] Y) (c c' : 𝒞) :
    extPair t ht (z ⊗ₜ[ℂ] c) (z' ⊗ₜ[ℂ] c')
      = c' * extPairAux t ht z z' * star c := rfl

private theorem extPairAux_star (ht : IsVNTensor t) (z z' : X ⊗[ℂ] Y) :
    star (extPairAux t ht z z') = extPairAux t ht z' z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      induction z' using TensorProduct.induction_on with
      | zero => simp
      | tmul x' y' =>
          rw [extPairAux_tmul, extPairAux_tmul, ht.star,
            CStarModule.star_inner, CStarModule.star_inner]
      | add z₁ z₂ h₁ h₂ => rw [map_add, star_add, h₁, h₂, map_add,
          LinearMap.add_apply]
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, LinearMap.add_apply, star_add, h₁, h₂, map_add]

/-- Every element of `(X ⊙ Y) ⊙ 𝒞` is a finite sum of elementary tensors. -/
private theorem exists_fin_rep (v : (X ⊗[ℂ] Y) ⊗[ℂ] 𝒞) :
    ∃ (n : ℕ) (x : Fin n → X) (y : Fin n → Y) (c : Fin n → 𝒞),
      v = ∑ k, (x k ⊗ₜ[ℂ] y k) ⊗ₜ[ℂ] c k := by
  classical
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul z c =>
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, by simp⟩
      | tmul x y => exact ⟨1, fun _ => x, fun _ => y, fun _ => c, by simp⟩
      | add z₁ z₂ h₁ h₂ =>
          obtain ⟨n₁, x₁, y₁, c₁, hv₁⟩ := h₁
          obtain ⟨n₂, x₂, y₂, c₂, hv₂⟩ := h₂
          refine ⟨n₁ + n₂, Fin.append x₁ x₂, Fin.append y₁ y₂,
            Fin.append c₁ c₂, ?_⟩
          rw [TensorProduct.add_tmul, hv₁, hv₂, Fin.sum_univ_add]
          simp only [Fin.append_left, Fin.append_right]
  | add v₁ v₂ h₁ h₂ =>
      obtain ⟨n₁, x₁, y₁, c₁, hv₁⟩ := h₁
      obtain ⟨n₂, x₂, y₂, c₂, hv₂⟩ := h₂
      refine ⟨n₁ + n₂, Fin.append x₁ x₂, Fin.append y₁ y₂,
        Fin.append c₁ c₂, ?_⟩
      rw [hv₁, hv₂, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]

/-- The expansion of the pairing on a finite sum of elementary tensors. -/
private theorem extPair_sum (ht : IsVNTensor t) {n : ℕ} (x : Fin n → X) (y : Fin n → Y)
    (c : Fin n → 𝒞) :
    extPair t ht (∑ k, (x k ⊗ₜ[ℂ] y k) ⊗ₜ[ℂ] c k)
        (∑ k, (x k ⊗ₜ[ℂ] y k) ⊗ₜ[ℂ] c k)
      = ∑ i, ∑ j, c j * t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))
          * star (c i) := by
  have h1 : extPair t ht (∑ k, (x k ⊗ₜ[ℂ] y k) ⊗ₜ[ℂ] c k)
      = ∑ k, extPair t ht ((x k ⊗ₜ[ℂ] y k) ⊗ₜ[ℂ] c k) :=
    map_sum (extPair t ht) _ _
  rw [h1, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => rfl

variable (t) in
/-- The `𝒞`-valued inner product on `(X ⊙ Y) ⊙ 𝒞` (**164II**, existence). -/
private noncomputable def extBInner (ht : IsVNTensor t) :
    BInner 𝒞 ((X ⊗[ℂ] Y) ⊗[ℂ] 𝒞) where
  inner v w := extPair t ht v w
  inner_add_right v w w' := map_add (extPair t ht v) w w'
  inner_smul_right_complex a v w := map_smul (extPair t ht v) a w
  inner_op_smul_right c v w := by
    induction w using TensorProduct.induction_on with
    | zero => simp only [ext_smul_zero, map_zero, mul_zero]
    | tmul z' c' =>
        induction v using TensorProduct.induction_on with
        | zero => simp only [map_zero, LinearMap.zero_apply, mul_zero]
        | tmul z c₀ =>
            rw [ext_smul_tmul, extPair_tmul, extPair_tmul]
            noncomm_ring
        | add v₁ v₂ h₁ h₂ =>
            rw [map_add, LinearMap.add_apply, LinearMap.add_apply, h₁, h₂,
              mul_add]
    | add w₁ w₂ h₁ h₂ =>
        rw [ext_smul_add, map_add, map_add, h₁, h₂, mul_add]
  star_inner v w := by
    induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply, star_zero]
    | tmul z c =>
        induction w using TensorProduct.induction_on with
        | zero => simp only [map_zero, LinearMap.zero_apply, star_zero]
        | tmul z' c' =>
            rw [extPair_tmul, extPair_tmul, star_mul, star_mul, star_star,
              extPairAux_star, mul_assoc]
        | add w₁ w₂ h₁ h₂ =>
            rw [map_add, star_add, h₁, h₂, map_add, LinearMap.add_apply]
    | add v₁ v₂ h₁ h₂ =>
        rw [map_add, LinearMap.add_apply, star_add, h₁, h₂, map_add]
  inner_self_nonneg v := by
    obtain ⟨n, x, y, c, rfl⟩ := exists_fin_rep v
    rw [extPair_sum]
    exact gram_t_nonneg ht x y c

@[simp] private theorem extBInner_tmul (ht : IsVNTensor t) (z z' : X ⊗[ℂ] Y) (c c' : 𝒞) :
    (extBInner t ht).inner (z ⊗ₜ[ℂ] c) (z' ⊗ₜ[ℂ] c')
      = c' * extPairAux t ht z z' * star c :=
  extPair_tmul ht z z' c c'



variable (t) in
/-- `η(x, y) = (x ⊗ y) ⊗ 1`, pushed into the self-dual completion. -/
private noncomputable def extEta (ht : IsVNTensor t)
    (E : SelfDualCompletion.{u, u, u} (extBInner (X := X) (Y := Y) t ht))
    (x : X) (y : Y) : E.X :=
  E.η ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] 1)

section EtaFields

variable (ht : IsVNTensor t)
  (E : SelfDualCompletion.{u, u, u} (extBInner (X := X) (Y := Y) t ht))

/-- `η` as an additive map, so that it commutes with finite sums. -/
private noncomputable def extEtaHom : ((X ⊗[ℂ] Y) ⊗[ℂ] 𝒞) →+ E.X where
  toFun := E.η
  map_zero' := by simpa using E.η_smul_complex 0 0
  map_add' := E.η_add

private theorem extEta_sub (v w : (X ⊗[ℂ] Y) ⊗[ℂ] 𝒞) :
    E.η (v - w) = E.η v - E.η w := map_sub (extEtaHom ht E) v w

/-- Two vectors of `(X ⊙ Y) ⊙ 𝒞` with the same image under `η` are
identified by the completion. -/
private theorem extEta_eq_of_inner_zero {v w : (X ⊗[ℂ] Y) ⊗[ℂ] 𝒞}
    (h : (extBInner t ht).inner (v - w) (v - w) = 0) : E.η v = E.η w := by
  have h1 : (inner 𝒞 (E.η (v - w)) (E.η (v - w)) : 𝒞) = 0 := by
    rw [E.η_inner]; exact h
  have h2 : ‖E.η (v - w)‖ = 0 := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞), h1]
    simp
  have h3 : E.η (v - w) = 0 := norm_eq_zero.mp h2
  rw [extEta_sub ht E] at h3
  exact sub_eq_zero.mp h3

private theorem extEta_inner (x x' : X) (y y' : Y) :
    (inner 𝒞 (extEta t ht E x y) (extEta t ht E x' y') : 𝒞)
      = t (inner 𝒜 x x') (inner ℬ y y') := by
  rw [extEta, extEta, E.η_inner, extBInner_tmul, extPairAux_tmul]
  rw [star_one, mul_one, one_mul]

private theorem extEta_add_left (x x' : X) (y : Y) :
    extEta t ht E (x + x') y = extEta t ht E x y + extEta t ht E x' y := by
  rw [extEta, extEta, extEta, ← E.η_add, TensorProduct.add_tmul,
    TensorProduct.add_tmul]

private theorem extEta_add_right (x : X) (y y' : Y) :
    extEta t ht E x (y + y') = extEta t ht E x y + extEta t ht E x y' := by
  rw [extEta, extEta, extEta, ← E.η_add, TensorProduct.tmul_add,
    TensorProduct.add_tmul]

private theorem extEta_smul_complex (a : ℂ) (x : X) (y : Y) :
    extEta t ht E (a • x) y = a • extEta t ht E x y := by
  rw [extEta, extEta, ← E.η_smul_complex, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul']

private theorem extEta_smul (a : 𝒜) (b : ℬ) (x : X) (y : Y) :
    extEta t ht E (a • x) (b • y) = t a b • extEta t ht E x y := by
  have hrhs : t a b • extEta t ht E x y
      = E.η ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (t a b)) := by
    rw [extEta, ← E.η_smul, ext_smul_tmul, mul_one]
  rw [hrhs, extEta]
  refine extEta_eq_of_inner_zero ht E ?_
  set M : 𝒞 := t (inner 𝒜 x x) (inner ℬ y y) with hM
  have hAA : (extBInner t ht).inner
      (((a • x) ⊗ₜ[ℂ] (b • y)) ⊗ₜ[ℂ] (1 : 𝒞))
      (((a • x) ⊗ₜ[ℂ] (b • y)) ⊗ₜ[ℂ] (1 : 𝒞))
      = t a b * M * star (t a b) := by
    rw [extBInner_tmul, extPairAux_tmul, star_one, mul_one, one_mul,
      CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
      CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
      ht.star, ← ht.mul, ← ht.mul, hM]
  have hAB : (extBInner t ht).inner
      (((a • x) ⊗ₜ[ℂ] (b • y)) ⊗ₜ[ℂ] (1 : 𝒞))
      ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (t a b))
      = t a b * M * star (t a b) := by
    rw [extBInner_tmul, extPairAux_tmul, star_one, mul_one,
      CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_left,
      ht.star, ← ht.mul, hM, ← mul_assoc]
  have hBA : (extBInner t ht).inner
      ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (t a b))
      (((a • x) ⊗ₜ[ℂ] (b • y)) ⊗ₜ[ℂ] (1 : 𝒞))
      = t a b * M * star (t a b) := by
    rw [extBInner_tmul, extPairAux_tmul, one_mul,
      CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_right,
      ← ht.mul, hM]
  have hBB : (extBInner t ht).inner
      ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (t a b))
      ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (t a b))
      = t a b * M * star (t a b) := by
    rw [extBInner_tmul, extPairAux_tmul, hM]
  have hexp : (extBInner t ht).inner
      ((((a • x) ⊗ₜ[ℂ] (b • y)) ⊗ₜ[ℂ] (1 : 𝒞)) - ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (t a b)))
      ((((a • x) ⊗ₜ[ℂ] (b • y)) ⊗ₜ[ℂ] (1 : 𝒞)) - ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (t a b)))
      = ((extBInner t ht).inner (((a • x) ⊗ₜ[ℂ] (b • y)) ⊗ₜ[ℂ] (1 : 𝒞))
            (((a • x) ⊗ₜ[ℂ] (b • y)) ⊗ₜ[ℂ] (1 : 𝒞))
          - (extBInner t ht).inner (((a • x) ⊗ₜ[ℂ] (b • y)) ⊗ₜ[ℂ] (1 : 𝒞))
            ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (t a b)))
        - ((extBInner t ht).inner ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (t a b))
              (((a • x) ⊗ₜ[ℂ] (b • y)) ⊗ₜ[ℂ] (1 : 𝒞))
            - (extBInner t ht).inner ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (t a b))
              ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (t a b))) := by
    change extPair t ht _ _ = _
    have h1 : extPair t ht ((((a • x) ⊗ₜ[ℂ] (b • y)) ⊗ₜ[ℂ] (1 : 𝒞))
          - ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (t a b)))
        = extPair t ht (((a • x) ⊗ₜ[ℂ] (b • y)) ⊗ₜ[ℂ] (1 : 𝒞))
          - extPair t ht ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (t a b)) := map_sub _ _ _
    rw [h1, LinearMap.sub_apply, map_sub, map_sub]
    rfl
  rw [hexp, hAA, hAB, hBA, hBB]
  abel

end EtaFields

section UnivField

variable {W : Type u} [NormedAddCommGroup W] [NormedSpace ℂ W] [SMul 𝒞 W]
  [CStarModule 𝒞 W]

variable {T : X → Y → W}

/-- The data of a bounded `𝒜 ⊙ ℬ`-bilinear map, as in `ExtTensor.univ`. -/
private structure IsExtBilin (t : 𝒜 → ℬ → 𝒞) (T : X → Y → W) : Prop where
  add_left : ∀ (x x' : X) (y : Y), T (x + x') y = T x y + T x' y
  add_right : ∀ (x : X) (y y' : Y), T x (y + y') = T x y + T x y'
  smul : ∀ (a : 𝒜) (b : ℬ) (x : X) (y : Y), T (a • x) (b • y) = t a b • T x y


private theorem extBilin_smul_left (ht : IsVNTensor t) (hT : IsExtBilin t T) (a : ℂ)
    (x : X) (y : Y) : T (a • x) y = a • T x y := by
  have h3 := hT.smul (a • (1 : 𝒜)) 1 x y
  rw [op_smul_complex_smul, op_one_smul, op_one_smul, ht.smul_complex, ht.one,
    op_smul_complex_smul, op_one_smul] at h3
  exact h3

private theorem extBilin_smul_right (ht : IsVNTensor t) (hT : IsExtBilin t T) (a : ℂ)
    (x : X) (y : Y) : T x (a • y) = a • T x y := by
  have h3 := hT.smul 1 (a • (1 : ℬ)) x y
  rw [op_smul_complex_smul, op_one_smul, op_one_smul,
    vnTensor_smul_complex_right ht, ht.one,
    op_smul_complex_smul, op_one_smul] at h3
  exact h3

variable (t) in
/-- `T` lifted to `X ⊙ Y`. -/
private noncomputable def extLift0 (ht : IsVNTensor t) (hT : IsExtBilin t T) :
    (X ⊗[ℂ] Y) →ₗ[ℂ] W :=
  TensorProduct.lift (LinearMap.mk₂ ℂ T hT.add_left
    (fun a x y => extBilin_smul_left ht hT a x y) hT.add_right
    (fun a x y => extBilin_smul_right ht hT a x y))

@[simp] private theorem extLift0_tmul (ht : IsVNTensor t) (hT : IsExtBilin t T)
    (x : X) (y : Y) : extLift0 t ht hT (x ⊗ₜ[ℂ] y) = T x y := rfl

variable (t) in
/-- `T` lifted to `(X ⊙ Y) ⊙ 𝒞`. -/
private noncomputable def extLift (ht : IsVNTensor t) (hT : IsExtBilin t T) :
    ((X ⊗[ℂ] Y) ⊗[ℂ] 𝒞) →ₗ[ℂ] W :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun (z : X ⊗[ℂ] Y) (c : 𝒞) => c • extLift0 t ht hT z)
    (fun z₁ z₂ c => by rw [map_add, op_smul_add])
    (fun a z c => by rw [map_smul, op_smul_comm_complex])
    (fun z c₁ c₂ => by rw [op_add_smul])
    (fun a z c => by rw [op_smul_complex_smul]))

@[simp] private theorem extLift_tmul (ht : IsVNTensor t) (hT : IsExtBilin t T)
    (z : X ⊗[ℂ] Y) (c : 𝒞) :
    extLift t ht hT (z ⊗ₜ[ℂ] c) = c • extLift0 t ht hT z := rfl

private theorem extLift_op_smul (ht : IsVNTensor t) (hT : IsExtBilin t T) (c : 𝒞)
    (v : (X ⊗[ℂ] Y) ⊗[ℂ] 𝒞) :
    extLift t ht hT (c • v) = c • extLift t ht hT v := by
  induction v using TensorProduct.induction_on with
  | zero => rw [ext_smul_zero, map_zero, op_smul_zero]
  | tmul z c' => rw [ext_smul_tmul, extLift_tmul, extLift_tmul, op_mul_smul]
  | add v₁ v₂ h₁ h₂ => rw [ext_smul_add, map_add, map_add, h₁, h₂, op_smul_add]

private theorem extLift_rep (ht : IsVNTensor t) (hT : IsExtBilin t T) {n : ℕ}
    (x : Fin n → X) (y : Fin n → Y) (c : Fin n → 𝒞) :
    extLift t ht hT (∑ k, (x k ⊗ₜ[ℂ] y k) ⊗ₜ[ℂ] c k)
      = ∑ k, c k • T (x k) (y k) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => rfl

private theorem bmm_sum {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [SMul 𝒞 V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [SMul 𝒞 V₂] {B₁ : BInner 𝒞 V₁}
    {B₂ : BInner 𝒞 V₂} {C : ℝ} {S : V₁ → V₂} (hS : IsBoundedModuleMap B₁ B₂ C S)
    {κ : Type*} (s : Finset κ) (f : κ → V₁) :
    S (∑ i ∈ s, f i) = ∑ i ∈ s, S (f i) := by
  classical
  have hS0 : S 0 = 0 := by simpa using hS.smul_complex 0 0
  refine Finset.induction_on s (by simpa using hS0) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, hS.add, ih, Finset.sum_insert hi]


variable [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ] [VonNeumannAlgebra 𝒞]

private theorem extLift_bounded (ht : IsVNTensor t) (hT : IsExtBilin t T) {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
      ‖∑ i, T (x i) (y i)‖ ^ 2 ≤
        C * ‖∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))‖)
    (S : StarSubalgebra ℂ 𝒞) (hSt : ∀ (a : 𝒜) (b : ℬ), t a b ∈ S)
    (hSrep : ∀ z ∈ S, ∃ (m : ℕ) (a : Fin m → 𝒜) (b : Fin m → ℬ),
      z = ∑ l, t (a l) (b l))
    (hSdense : UnDense (mulInner 𝒞) (S : Set 𝒞)) :
    IsBoundedModuleMap (extBInner t ht) (cstarBInner 𝒞 W) (Real.sqrt C)
      (extLift t ht hT) where
  add := map_add _
  smul_complex := map_smul _
  smul := extLift_op_smul ht hT
  bound := by
    intro v
    obtain ⟨n, x, y, c, rfl⟩ := exists_fin_rep v
    have hle := tensor_gram_le ht hC (fun a b x y => hT.smul a b x y) hbound
      S hSt hSrep hSdense x y c
    have hGnn : (0 : 𝒞) ≤ ∑ i, ∑ j, c j
        * t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j)) * star (c i) :=
      gram_t_nonneg ht x y c
    have hInn : (0 : 𝒞) ≤ inner 𝒞 (∑ k, c k • T (x k) (y k))
        (∑ k, c k • T (x k) (y k)) := CStarModule.inner_self_nonneg
    have hnorm : ‖(inner 𝒞 (∑ k, c k • T (x k) (y k))
          (∑ k, c k • T (x k) (y k)) : 𝒞)‖
        ≤ C * ‖∑ i, ∑ j, c j
            * t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j)) * star (c i)‖ := by
      have h1 := CStarAlgebra.norm_le_norm_of_nonneg_of_le hInn hle
      rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] at h1
    have hBv : (extBInner t ht).inner (∑ k, (x k ⊗ₜ[ℂ] y k) ⊗ₜ[ℂ] c k)
          (∑ k, (x k ⊗ₜ[ℂ] y k) ⊗ₜ[ℂ] c k)
        = ∑ i, ∑ j, c j * t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))
            * star (c i) := extPair_sum ht x y c
    change (cstarBInner 𝒞 W).norm _ ≤ Real.sqrt C * (extBInner t ht).norm _
    rw [BInner.norm, BInner.norm, extLift_rep, hBv, ← Real.sqrt_mul hC]
    change Real.sqrt ‖(inner 𝒞 (∑ k, c k • T (x k) (y k))
      (∑ k, c k • T (x k) (y k)) : 𝒞)‖ ≤ _
    exact Real.sqrt_le_sqrt hnorm

end UnivField

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), existence:
for self-dual `X`, `Y` over von Neumann algebras the self-dual exterior
tensor product exists.

**164III**–**164VIII** (construction via `ℓ²((pᵢⱼ))` and its proof,
including `ext-tensor-dfn-eta`, `ext-tensor-preserves-inner-prod`,
injectivity of `η`, `ultranorm-dense-tensor-base`) are proof steps — not
converted separately. -/
theorem univprop_ext_tensor [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) :
    Nonempty (ExtTensor t ht X Y) := by
  have hSt : ∀ (a : 𝒜) (b : ℬ), t a b ∈ tSpanSubalg ht := fun a b => t_mem_tSpan a b
  have hSrep : ∀ z ∈ tSpanSubalg ht, ∃ (m : ℕ) (a : Fin m → 𝒜) (b : Fin m → ℬ),
      z = ∑ l, t (a l) (b l) := fun z hz => hz
  have hSdense : UnDense (mulInner 𝒞) ((tSpanSubalg ht : StarSubalgebra ℂ 𝒞) : Set 𝒞) :=
    unDense_tSpan ht
  obtain ⟨E⟩ := dils_completion (𝒷 := 𝒞) (extBInner (X := X) (Y := Y) t ht)
  refine ⟨{ Z := E.X
            selfDual := E.selfDual
            η := extEta t ht E
            η_add_left := extEta_add_left ht E
            η_add_right := extEta_add_right ht E
            η_smul_complex := extEta_smul_complex ht E
            η_smul := extEta_smul ht E
            η_inner := extEta_inner ht E
            univ := ?_ }⟩
  intro W inacg innsp insmul incstar incompl hW T hTl hTr hTsm hbd
  letI := inacg
  letI := innsp
  letI := insmul
  letI := incstar
  letI := incompl
  obtain ⟨C₀, hbound₀⟩ := hbd
  have hC : (0 : ℝ) ≤ max C₀ 0 := le_max_right _ _
  have hbound : ∀ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
      ‖∑ i, T (x i) (y i)‖ ^ 2 ≤
        max C₀ 0 * ‖∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))‖ :=
    fun n x y => (hbound₀ n x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hT : IsExtBilin t T := ⟨hTl, hTr, hTsm⟩
  obtain ⟨T', ⟨hT'b, hT'v⟩, hT'u⟩ := selfdual_completion_univ
    (extBInner (X := X) (Y := Y) t ht) E hW (Real.sqrt (max C₀ 0))
    (extLift t ht hT) (extLift_bounded ht hT hC hbound (tSpanSubalg ht) hSt hSrep hSdense)
  refine ⟨T', ⟨hT'b, fun x y => ?_⟩, fun S' hS' => ?_⟩
  · have h := hT'v ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (1 : 𝒞))
    rw [extLift_tmul, extLift0_tmul, op_one_smul] at h
    exact h
  · refine hT'u S' ⟨hS'.1, fun v => ?_⟩
    obtain ⟨C', hSb⟩ := hS'.1
    obtain ⟨n, x, y, c, rfl⟩ := exists_fin_rep v
    have hη : E.η (∑ k, (x k ⊗ₜ[ℂ] y k) ⊗ₜ[ℂ] c k)
        = ∑ k, c k • extEta t ht E (x k) (y k) := by
      rw [show E.η (∑ k, (x k ⊗ₜ[ℂ] y k) ⊗ₜ[ℂ] c k)
          = ∑ k, E.η ((x k ⊗ₜ[ℂ] y k) ⊗ₜ[ℂ] c k) from
        map_sum (extEtaHom ht E) _ _]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [extEta, ← E.η_smul, ext_smul_tmul, mul_one]
    rw [hη, bmm_sum hSb, extLift_rep]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hSb.smul, hS'.2]

end UnivPropExistence

/-- **Non-vacuity check** for `ExtTensor` — the analogue of
`vnTensor_mul_complex` for `IsVNTensor` and of `paschkeModuleId` for
`PaschkeModule`.  `𝒞 = 𝒜 ⊗ ℬ` itself, as a Hilbert `𝒞`-module over itself
with `η = t`, **is** a self-dual exterior tensor product of `X = 𝒜` and
`Y = ℬ`: it is the case `X = 𝒜`, `Y = ℬ` of `univprop_ext_tensor`, and it
needs no von Neumann hypotheses at all.

Every field is checked against the mirrored convention: `inner 𝒜 x x'`
is `x' * star x`, so `η_inner` reads
`t x' y' * star (t x y) = t (x' * star x) (y' * star y)`, which is exactly
`IsVNTensor.star` followed by `IsVNTensor.mul` — a star in the wrong slot
would not typecheck.  The universal property is *not* proved by density:
`T' z := z · T(1,1)` is forced, because `z = z · 1 = z · t(1,1)` and a
module map commutes with the action.

Kept in the tree deliberately: without it every theorem hypothesising
`E : ExtTensor t ht X Y` (**164II**.1/.2a/.2b, **165III**, **165VI**,
**166IV**, **166VI**, **167I**) would be conditional on a structure not
known to be inhabited; PROVING-LOG session 14 records a mirroring defect
that left `PaschkeModule` uninhabited and nine theorems vacuous. -/
noncomputable def extTensorSelf (t : 𝒜 → ℬ → 𝒞) (ht : IsVNTensor t) :
    ExtTensor t ht 𝒜 ℬ where
  Z := 𝒞
  selfDual := selfDual_self 𝒞
  η := t
  η_add_left x x' y := ht.add_left x x' y
  η_add_right x y y' := ht.add_right x y y'
  η_smul_complex c x y := ht.smul_complex c x y
  η_smul a b x y := by
    show t (a * x) (b * y) = t a b * t x y
    rw [ht.mul]
  η_inner x x' y y' := by
    show t x' y' * star (t x y) = t (x' * star x) (y' * star y)
    rw [ht.star, ht.mul]
  univ := by
    intro W iW₁ iW₂ iW₃ iW₄ iW₅ _ T _ _ hsmul _
    letI := iW₁; letI := iW₂; letI := iW₃; letI := iW₄; letI := iW₅
    -- `T` is determined by `w₀ := T 1 1`, since `T x y = T (x·1) (y·1)`.
    set w₀ : W := T 1 1 with hw₀
    have hTxy : ∀ (x : 𝒜) (y : ℬ), T x y = t x y • w₀ := by
      intro x y
      have h := hsmul x y 1 1
      rwa [smul_eq_mul, mul_one, smul_eq_mul, mul_one] at h
    have hone : ∀ z : 𝒞, z • (1 : 𝒞) = z := fun z => by
      rw [smul_eq_mul, mul_one]
    refine ⟨fun z => z • w₀, ⟨⟨‖w₀‖, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · exact fun z z' => op_add_smul z z' w₀
    · exact fun c z => op_smul_complex_smul c z w₀
    · exact fun b z => op_mul_smul b z w₀
    · intro z
      rw [cstarBInner_norm, cstarBInner_norm, mul_comm]
      exact norm_op_smul_le z w₀
    · exact fun x y => (hTxy x y).symm
    · rintro T'' ⟨⟨C, -, -, hmod, -⟩, hT''⟩
      funext z
      have h1 : T'' (1 : 𝒞) = w₀ := by
        have := hT'' 1 1
        rwa [ht.one] at this
      have := hmod z 1
      rw [hone z, h1] at this
      exact this

section ExtTensorAux

variable [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ] [VonNeumannAlgebra 𝒞]
  [CompleteSpace X] [CompleteSpace Y]

/-- The Gram identity `‖∑ᵢ xᵢ ⊗ yᵢ‖² = ‖∑ᵢⱼ ⟨xᵢ,xⱼ⟩ ⊗ ⟨yᵢ,yⱼ⟩‖`, from
`ExtTensor.η_inner`.  (Auxiliary for parsecs 1640–1670.) -/
private theorem extTensor_gram (E : ExtTensor t ht X Y) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) :
    ‖∑ i, E.η (x i) (y i)‖ ^ 2
      = ‖∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))‖ := by
  have hg : (inner 𝒞 (∑ i, E.η (x i) (y i)) (∑ i, E.η (x i) (y i)) : 𝒞)
      = ∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j)) := by
    rw [CStarModule.inner_sum_left]
    exact Finset.sum_congr rfl fun i _ => by
      rw [CStarModule.inner_sum_right]
      exact Finset.sum_congr rfl fun j _ => E.η_inner _ _ _ _
  rw [← hg, CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞),
    Real.sq_sqrt (norm_nonneg _)]

/-- Auxiliary for parsecs 1640–1670: two bounded module maps out of a
self-dual exterior tensor product which agree on the elementary tensors
are equal.  This is the uniqueness half of the universal property
**164II**, and is the substitute — offered by the author himself in
`bsols.tex`, solution `hilbmod-tensor-ketbra` — for the ultranorm density
of the elementary tensors. -/
private theorem extTensor_map_ext (E : ExtTensor t ht X Y) {W : Type u}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [SMul 𝒞 W] [CStarModule 𝒞 W]
    [CompleteSpace W] (hW : SelfDual 𝒞 W) (C₁ C₂ : ℝ) (F G : E.Z → W)
    (hF : IsBoundedModuleMap (cstarBInner 𝒞 E.Z) (cstarBInner 𝒞 W) C₁ F)
    (hG : IsBoundedModuleMap (cstarBInner 𝒞 E.Z) (cstarBInner 𝒞 W) C₂ G)
    (hFG : ∀ (x : X) (y : Y), F (E.η x y) = G (E.η x y)) :
    F = G := by
  have hnormF : ∀ z : E.Z, ‖F z‖ ≤ C₁ * ‖z‖ := fun z => by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) (F z),
      CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) z]
    exact hF.bound z
  have huniv := E.univ W inferInstance inferInstance inferInstance
    inferInstance inferInstance hW (fun x y => F (E.η x y))
    (fun x x' y => by rw [E.η_add_left, hF.add])
    (fun x y y' => by rw [E.η_add_right, hF.add])
    (fun a b x y => by rw [E.η_smul, hF.smul])
    ⟨C₁ ^ 2, fun n x y => ?_⟩
  · exact huniv.unique ⟨⟨C₁, hF⟩, fun _ _ => rfl⟩
      ⟨⟨C₂, hG⟩, fun x y => (hFG x y).symm⟩
  · have hsum : ∑ i, F (E.η (x i) (y i)) = F (∑ i, E.η (x i) (y i)) :=
      (map_sum (AddMonoidHom.mk' F hF.add) _ _).symm
    rw [hsum, ← extTensor_gram E n x y]
    nlinarith [hnormF (∑ i, E.η (x i) (y i)),
      norm_nonneg (∑ i, E.η (x i) (y i)),
      norm_nonneg (F (∑ i, E.η (x i) (y i)))]

/-- Auxiliary for parsecs 1640–1670: a vector of `X ⊗ Y` orthogonal to
every elementary tensor is `0`.  (Via `extTensor_map_ext` applied to
`|w⟩⟨w|`.) -/
private theorem extTensor_sep (E : ExtTensor t ht X Y) (w : E.Z)
    (hw : ∀ (x : X) (y : Y), (inner 𝒞 (E.η x y) w : 𝒞) = 0) : w = 0 := by
  have hK : IsBoundedModuleMap (cstarBInner 𝒞 E.Z) (cstarBInner 𝒞 E.Z)
      ‖mketbra 𝒞 w w‖ ⇑(mketbra 𝒞 w w) :=
    ⟨fun z z' => map_add _ z z', fun c z => map_smul _ c z,
      fun b z => by
        show (inner 𝒞 w (b • z) : 𝒞) • w = b • ((inner 𝒞 w z : 𝒞) • w)
        rw [CStarModule.inner_op_smul_right, op_mul_smul],
      fun z => by
        have h : ‖(mketbra 𝒞 w w) z‖ ≤ ‖mketbra 𝒞 w w‖ * ‖z‖ :=
          (mketbra 𝒞 w w).le_opNorm z
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞)
            ((mketbra 𝒞 w w) z),
          CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) z] at h
        exact h⟩
  have hZ : IsBoundedModuleMap (cstarBInner 𝒞 E.Z) (cstarBInner 𝒞 E.Z) 0
      (fun _ : E.Z => (0 : E.Z)) :=
    ⟨fun _ _ => (add_zero _).symm, fun c _ => (smul_zero c).symm,
      fun b _ => (op_smul_zero b).symm,
      fun z => by
        show Real.sqrt ‖(inner 𝒞 (0 : E.Z) (0 : E.Z) : 𝒞)‖
          ≤ 0 * Real.sqrt ‖(inner 𝒞 z z : 𝒞)‖
        simp [CStarModule.inner_zero_left]⟩
  have hmap := extTensor_map_ext E E.selfDual _ _ _ _ hK hZ fun x y => by
    show (inner 𝒞 w (E.η x y) : 𝒞) • w = 0
    rw [← CStarModule.star_inner (E.η x y) w, hw x y, star_zero, op_zero_smul]
  have happ : (inner 𝒞 w w : 𝒞) • w = 0 := congrFun hmap w
  have hsa : star (inner 𝒞 w w : 𝒞) = inner 𝒞 w w := CStarModule.star_inner w w
  have h3 : (inner 𝒞 w w : 𝒞) * inner 𝒞 w w * inner 𝒞 w w = 0 := by
    have := congrArg (fun z : E.Z => (inner 𝒞 z z : 𝒞)) happ
    simpa [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
      hsa, mul_assoc] using this
  have h4 : (inner 𝒞 w w : 𝒞) * inner 𝒞 w w = 0 := by
    refine (CStarRing.star_mul_self_eq_zero_iff _).mp ?_
    calc star ((inner 𝒞 w w : 𝒞) * inner 𝒞 w w) * ((inner 𝒞 w w : 𝒞) * inner 𝒞 w w)
        = (inner 𝒞 w w : 𝒞) * (inner 𝒞 w w * inner 𝒞 w w * inner 𝒞 w w) := by
          rw [star_mul, hsa]; noncomm_ring
      _ = 0 := by rw [h3, mul_zero]
  refine (CStarModule.inner_self (A := 𝒞) (x := w)).mp ?_
  refine (CStarRing.star_mul_self_eq_zero_iff _).mp ?_
  rw [hsa]; exact h4

/-- The identity is a bounded module map (auxiliary). -/
private theorem isBoundedModuleMap_id {V : Type u} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [SMul 𝒞 V] [CStarModule 𝒞 V] :
    IsBoundedModuleMap (cstarBInner 𝒞 V) (cstarBInner 𝒞 V) 1
      (id : V → V) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun z => by
    show (cstarBInner 𝒞 V).norm z ≤ 1 * (cstarBInner 𝒞 V).norm z
    rw [one_mul]⟩

/-- Bounded module maps compose (auxiliary). -/
private theorem isBoundedModuleMap_comp {V₁ V₂ V₃ : Type u}
    [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [SMul 𝒞 V₁] [CStarModule 𝒞 V₁]
    [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [SMul 𝒞 V₂] [CStarModule 𝒞 V₂]
    [NormedAddCommGroup V₃] [NormedSpace ℂ V₃] [SMul 𝒞 V₃] [CStarModule 𝒞 V₃]
    {C₁ C₂ : ℝ} {F : V₁ → V₂} {G : V₂ → V₃}
    (hF : IsBoundedModuleMap (cstarBInner 𝒞 V₁) (cstarBInner 𝒞 V₂) C₁ F)
    (hG : IsBoundedModuleMap (cstarBInner 𝒞 V₂) (cstarBInner 𝒞 V₃) C₂ G) :
    IsBoundedModuleMap (cstarBInner 𝒞 V₁) (cstarBInner 𝒞 V₃) (|C₂| * |C₁|)
      (fun z => G (F z)) := by
  refine ⟨fun z z' => by rw [hF.add, hG.add],
    fun c z => by rw [hF.smul_complex, hG.smul_complex],
    fun b z => by rw [hF.smul, hG.smul], fun z => ?_⟩
  have h1 : ‖F z‖ ≤ C₁ * ‖z‖ := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) (F z),
      CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) z]
    exact hF.bound z
  have h2 : ‖G (F z)‖ ≤ C₂ * ‖F z‖ := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) (G (F z)),
      CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) (F z)]
    exact hG.bound (F z)
  have hgoal : ‖G (F z)‖ ≤ |C₂| * |C₁| * ‖z‖ := by
    have hA : ‖F z‖ ≤ |C₁| * ‖z‖ :=
      h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    have hB : ‖G (F z)‖ ≤ |C₂| * ‖F z‖ :=
      h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    calc ‖G (F z)‖ ≤ |C₂| * ‖F z‖ := hB
      _ ≤ |C₂| * (|C₁| * ‖z‖) := mul_le_mul_of_nonneg_left hA (abs_nonneg _)
      _ = |C₂| * |C₁| * ‖z‖ := by ring
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) (G (F z)),
    CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) z] at hgoal
  exact hgoal

/-- Auxiliary for parsecs 1640–1670: a bounded 𝒞-linear functional on
`X ⊗ Y` vanishing on the elementary tensors is `0` (self-duality of
`X ⊗ Y` plus `extTensor_sep`). -/
private theorem extTensor_functional_ext (E : ExtTensor t ht X Y)
    (ψ : E.Z →ₗ[ℂ] 𝒞) (hmod : ∀ (b : 𝒞) (z : E.Z), ψ (b • z) = b * ψ z)
    (hbdd : ∃ C : ℝ, ∀ z : E.Z, ‖ψ z‖ ≤ C * ‖z‖)
    (hzero : ∀ (x : X) (y : Y), ψ (E.η x y) = 0) : ∀ z : E.Z, ψ z = 0 := by
  obtain ⟨p, hp⟩ := E.selfDual ψ hmod hbdd
  have hp0 : p = 0 := by
    refine extTensor_sep E p fun x y => ?_
    rw [← CStarModule.star_inner p (E.η x y), ← hp (E.η x y), hzero x y,
      star_zero]
  intro z
  rw [hp z, hp0, CStarModule.inner_zero_left]

/-- Auxiliary for **164IX**: two vector functionals `⟨a, U ·⟩` and `⟨b, ·⟩`
on `X ⊗ Y` (with `U` a bounded module map) which agree on the elementary
tensors agree everywhere. -/
private theorem extTensor_inner_diff_ext (E : ExtTensor t ht X Y)
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℂ W] [SMul 𝒞 W]
    [CStarModule 𝒞 W] (U : E.Z → W) (C : ℝ)
    (hU : IsBoundedModuleMap (cstarBInner 𝒞 E.Z) (cstarBInner 𝒞 W) C U)
    (a : W) (b : E.Z)
    (hzero : ∀ (x : X) (y : Y),
      (inner 𝒞 a (U (E.η x y)) : 𝒞) = inner 𝒞 b (E.η x y)) :
    ∀ z : E.Z, (inner 𝒞 a (U z) : 𝒞) = inner 𝒞 b z := by
  have hUnorm : ∀ z : E.Z, ‖U z‖ ≤ |C| * ‖z‖ := fun z => by
    have h : ‖U z‖ ≤ C * ‖z‖ := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) (U z),
        CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) z]
      exact hU.bound z
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have hψ := extTensor_functional_ext E
    { toFun := fun z => (inner 𝒞 a (U z) : 𝒞) - inner 𝒞 b z
      map_add' := fun z z' => by
        simp only [hU.add, CStarModule.inner_add_right]; abel
      map_smul' := fun c z => by
        simp only [hU.smul_complex, CStarModule.inner_smul_right_complex,
          RingHom.id_apply, smul_sub] }
    (fun b₀ z => by
      show (inner 𝒞 a (U (b₀ • z)) : 𝒞) - inner 𝒞 b (b₀ • z)
        = b₀ * ((inner 𝒞 a (U z) : 𝒞) - inner 𝒞 b z)
      rw [hU.smul, CStarModule.inner_op_smul_right,
        CStarModule.inner_op_smul_right, mul_sub])
    ⟨‖a‖ * |C| + ‖b‖, fun z => ?_⟩
    (fun x y => by
      show (inner 𝒞 a (U (E.η x y)) : 𝒞) - inner 𝒞 b (E.η x y) = 0
      rw [hzero x y, sub_self])
  · intro z
    have h : (inner 𝒞 a (U z) : 𝒞) - inner 𝒞 b z = 0 := hψ z
    exact sub_eq_zero.mp h
  · show ‖(inner 𝒞 a (U z) : 𝒞) - inner 𝒞 b z‖ ≤ (‖a‖ * |C| + ‖b‖) * ‖z‖
    calc ‖(inner 𝒞 a (U z) : 𝒞) - inner 𝒞 b z‖
        ≤ ‖(inner 𝒞 a (U z) : 𝒞)‖ + ‖(inner 𝒞 b z : 𝒞)‖ := norm_sub_le _ _
      _ ≤ ‖a‖ * ‖U z‖ + ‖b‖ * ‖z‖ := by
          gcongr <;> exact CStarModule.norm_inner_le _
      _ ≤ ‖a‖ * (|C| * ‖z‖) + ‖b‖ * ‖z‖ := by
          gcongr
          exact hUnorm z
      _ = (‖a‖ * |C| + ‖b‖) * ‖z‖ := by ring

end ExtTensorAux


/-- **164IX** (`ext-tensor-uniqueness`, dils.tex:5286, Uniqueness — stated
in **164II** as "up-to-isomorphism unique"): two self-dual exterior tensor
products are isomorphic by a unique inner-product-preserving module
isomorphism commuting with the embeddings. -/
theorem ext_tensor_uniqueness [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y)
    (E₁ E₂ : ExtTensor t ht X Y) :
    ∃! U : E₁.Z → E₂.Z,
      (∃ C : ℝ, IsBoundedModuleMap (cstarBInner 𝒞 E₁.Z)
        (cstarBInner 𝒞 E₂.Z) C U) ∧
      Function.Bijective U ∧
      (∀ z z' : E₁.Z, inner 𝒞 (U z) (U z') = inner 𝒞 z z') ∧
      ∀ (x : X) (y : Y), U (E₁.η x y) = E₂.η x y := by
  -- `η₂ : X × Y → E₂.Z` is itself an admissible datum for `E₁`'s universal
  -- property (the required bound is the Gram identity with `C = 1`), and
  -- symmetrically; the two induced maps are mutually inverse.
  obtain ⟨U, ⟨hUb, hUη⟩, -⟩ := E₁.univ E₂.Z inferInstance inferInstance
    inferInstance inferInstance inferInstance E₂.selfDual E₂.η
    E₂.η_add_left E₂.η_add_right E₂.η_smul
    ⟨1, fun n x y => by rw [extTensor_gram E₂ n x y, one_mul]⟩
  obtain ⟨V, ⟨hVb, hVη⟩, -⟩ := E₂.univ E₁.Z inferInstance inferInstance
    inferInstance inferInstance inferInstance E₁.selfDual E₁.η
    E₁.η_add_left E₁.η_add_right E₁.η_smul
    ⟨1, fun n x y => by rw [extTensor_gram E₁ n x y, one_mul]⟩
  obtain ⟨CU, hCU⟩ := hUb
  obtain ⟨CV, hCV⟩ := hVb
  have hVU : (fun z => V (U z)) = (id : E₁.Z → E₁.Z) :=
    extTensor_map_ext E₁ E₁.selfDual _ 1 _ _
      (isBoundedModuleMap_comp hCU hCV) isBoundedModuleMap_id
      fun x y => by rw [hUη, hVη]; rfl
  have hUV : (fun z => U (V z)) = (id : E₂.Z → E₂.Z) :=
    extTensor_map_ext E₂ E₂.selfDual _ 1 _ _
      (isBoundedModuleMap_comp hCV hCU) isBoundedModuleMap_id
      fun x y => by rw [hVη, hUη]; rfl
  -- inner products: first against elementary tensors, then in general
  have hstep1 : ∀ (x₀ : X) (y₀ : Y) (z : E₁.Z),
      (inner 𝒞 (E₂.η x₀ y₀) (U z) : 𝒞) = inner 𝒞 (E₁.η x₀ y₀) z := by
    intro x₀ y₀
    refine extTensor_inner_diff_ext E₁ U CU hCU _ _ fun x y => ?_
    rw [hUη, E₂.η_inner, E₁.η_inner]
  have hstep2 : ∀ z' z : E₁.Z,
      (inner 𝒞 (U z') (U z) : 𝒞) = inner 𝒞 z' z := by
    intro z'
    refine extTensor_inner_diff_ext E₁ U CU hCU _ _ fun x y => ?_
    rw [hUη, ← CStarModule.star_inner (E₂.η x y) (U z'), hstep1 x y z',
      CStarModule.star_inner]
  refine ⟨U, ⟨⟨CU, hCU⟩, ?_, fun z z' => hstep2 z z', hUη⟩, ?_⟩
  · exact Function.bijective_iff_has_inverse.mpr
      ⟨V, fun z => congrFun hVU z, fun z => congrFun hUV z⟩
  · rintro U' ⟨⟨CU', hCU'⟩, -, -, hU'η⟩
    exact extTensor_map_ext E₁ E₂.selfDual _ _ _ _ hCU' hCU
      fun x y => by rw [hU'η, hUη]

-- `hX`, `hY` are not used: the universal property is a *field* of
-- `ExtTensor`, and the self-duality that the argument needs is `E.selfDual`.
set_option linter.unusedVariables false in
/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), property 1:
the (span of the) image of `η` is ultranorm dense in `X ⊗ Y`.

**Divergence, class 2 (and forced).**  The thesis proves this at **164VII**
(`ultranorm-dense-tensor-base`) *for its own construction* of `X ⊗ Y` as
`ℓ²((pᵢⱼ))`, where "the linear span of `E(𝒜 ⊗ ℬ)` is by construction
ultranorm dense" is read off the definition.  Our statement is about an
arbitrary `E : ExtTensor`, so that last step is unavailable and its place is
taken by the projection argument of **163II**
(`selfdual_compl_defining_dense`): the orthogonal projection `P` onto
`D^⊥⊥` (`exists_orthoProj`, from **160IV**.3) fixes every elementary
tensor, so `P` and `id` both factor `η` through itself and the uniqueness
half of the universal property gives `P = id`, i.e. `D^⊥⊥ = X ⊗ Y`.
**160IV**.2 then identifies `D^⊥⊥` with the ultranorm closure of the
`𝒞`-span of `D`, and it is exactly here that the thesis's own argument is
still needed: `D` absorbs elementary tensors only, so its `𝒞`-span is
strictly bigger, and `bSpan D ⊆ unClosure D` is the thesis's
"`𝒜 ⊙ ℬ` ultrastrongly dense in `𝒜 ⊗ ℬ`, hence `E(𝒜 ⊙ ℬ)` ultranorm dense
in `E(𝒜 ⊗ ℬ)`" (`unDense_tSpan` and `unSeminorm_op_smul_le` above). -/
theorem ext_tensor_dense [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y) :
    UnDense (inner 𝒞)
      {z : E.Z | ∃ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
        z = ∑ i, E.η (x i) (y i)} := by
  classical
  set D : Set E.Z := {z : E.Z | ∃ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
    z = ∑ i, E.η (x i) (y i)} with hDdef
  -- `D` is closed under sums, complex scalars and *elementary* tensors
  have hD0 : (0 : E.Z) ∈ D := ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  have hDadd : ∀ z ∈ D, ∀ z' ∈ D, z + z' ∈ D := by
    rintro _ ⟨n, x, y, rfl⟩ _ ⟨m, x', y', rfl⟩
    refine ⟨n + m, Fin.append x x', Fin.append y y', ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  have hDc : ∀ (c : ℂ), ∀ z ∈ D, c • z ∈ D := by
    rintro c _ ⟨n, x, y, rfl⟩
    refine ⟨n, fun i => c • x i, y, ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => (E.η_smul_complex c (x i) (y i)).symm
  have hDt : ∀ (a : 𝒜) (b : ℬ), ∀ z ∈ D, t a b • z ∈ D := by
    rintro a b _ ⟨n, x, y, rfl⟩
    refine ⟨n, fun i => a • x i, fun i => b • y i, ?_⟩
    rw [op_smul_sum]
    exact Finset.sum_congr rfl fun i _ => (E.η_smul a b (x i) (y i)).symm
  have hDspan : ∀ c ∈ tSpan t, ∀ z ∈ D, c • z ∈ D := by
    rintro _ ⟨n, a, b, rfl⟩ z hz
    rw [add_smul_sum]
    exact Finset.sum_induction _ (fun w => w ∈ D) (fun w w' hw hw' => hDadd w hw w' hw')
      hD0 fun i _ => hDt (a i) (b i) z hz
  -- the `𝒞`-span of `D` lies in its ultranorm closure: this is **164VII**
  have hsmul : ∀ (c : 𝒞), ∀ v ∈ D, c • v ∈ unClosure 𝒞 (inner 𝒞) D := by
    intro c v hv n ωs ε hε
    obtain ⟨d, hd, hdist⟩ := unDense_tSpan ht c n ωs (ε / (‖v‖ + 1)) (by positivity)
    refine ⟨d • v, hDspan d hd v hv, fun i => ?_⟩
    have hsub : c • v - d • v = (c - d) • v := by
      have h : (c - d) • v + d • v = c • v := by
        rw [← op_add_smul]; congr 1; abel
      rw [← h]; abel
    calc unSeminorm (ωs i) (inner 𝒞 : E.Z → E.Z → 𝒞) (c • v - d • v)
        = unSeminorm (ωs i) (inner 𝒞 : E.Z → E.Z → 𝒞) ((c - d) • v) := by rw [hsub]
      _ ≤ ‖v‖ * unSeminorm (ωs i) (mulInner 𝒞) (c - d) :=
          unSeminorm_op_smul_le _ _ _
      _ ≤ ‖v‖ * (ε / (‖v‖ + 1)) :=
          mul_le_mul_of_nonneg_left (hdist i) (norm_nonneg v)
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg v, hε.le]
  have hbSpan : bSpan 𝒞 D ⊆ unClosure 𝒞 (inner 𝒞) D := by
    rintro _ ⟨n, c, b, v, hv, rfl⟩
    refine Finset.sum_induction _ (fun w => w ∈ unClosure 𝒞 (inner 𝒞) D)
      (fun w w' hw hw' => unClosure_add hDadd hw hw') (subset_unClosure _ hD0)
      fun i _ => ?_
    rw [← op_smul_complex_smul]
    exact hsmul _ _ (hv i)
  -- the projection onto `D^⊥⊥` fixes `D`, so the universal property makes it `id`
  obtain ⟨hW0, hWadd, hWb, hWc, hWcl⟩ := hilbmod_projthm_1 E.selfDual (orthoCompl 𝒞 D)
  obtain ⟨P, hPbdd, hPW, hPfix⟩ :=
    exists_orthoProj E.selfDual (orthoCompl 𝒞 (orthoCompl 𝒞 D)) hW0 hWadd hWb hWc hWcl
  have hbound : ∃ C : ℝ, ∀ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
      ‖∑ i, E.η (x i) (y i)‖ ^ 2 ≤
        C * ‖∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))‖ :=
    ⟨1, fun n x y => by rw [extTensor_gram E n x y, one_mul]⟩
  obtain ⟨T', -, hT'uniq⟩ := E.univ E.Z inferInstance inferInstance inferInstance
    inferInstance inferInstance E.selfDual E.η E.η_add_left E.η_add_right
    E.η_smul hbound
  have hPid : P = id := by
    have h1 : P = T' := hT'uniq P ⟨⟨1, hPbdd⟩, fun x y =>
      hPfix (E.η x y) (subset_biorthoCompl _
        ⟨1, fun _ => x, fun _ => y, by simp⟩)⟩
    have h2 : id = T' := hT'uniq id
      ⟨⟨1, ⟨fun x y => rfl, fun c x => rfl, fun b x => rfl,
        fun x => le_of_eq (one_mul _).symm⟩⟩, fun x y => rfl⟩
    exact h1.trans h2.symm
  intro z n ωs ε hε
  have hzW : z ∈ orthoCompl 𝒞 (orthoCompl 𝒞 D) := by
    have h := hPW z
    rwa [hPid] at h
  rw [hilbmod_projthm_2 E.selfDual D] at hzW
  have hz : z ∈ unClosure 𝒞 (inner 𝒞) D := by
    rw [← unClosure_unClosure D]
    exact unClosure_mono hbSpan hzW
  exact hz n ωs ε hε

section EtaEstimates

variable [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ] [VonNeumannAlgebra 𝒞]
  [CompleteSpace X] [CompleteSpace Y]

/-- `‖u ⊗ w‖_Ω ≤ ‖w‖ · ‖u‖_{Ω(·⊗1)}`: the one estimate behind **166II** and
**166IV**, from `⟨u,u⟩ ⊗ ⟨w,w⟩ ≤ ‖⟨w,w⟩‖ · (⟨u,u⟩ ⊗ 1)` and the normality of
the left leg (`vnTensorLegLeftNP`). -/
private theorem unSeminorm_eta_le_left (E : ExtTensor t ht X Y)
    (Ω : NPFunctional 𝒞) (u : X) (w : Y) :
    unSeminorm Ω (inner 𝒞) (E.η u w)
      ≤ ‖w‖ * unSeminorm (vnTensorLegLeftNP ht Ω) (inner 𝒜) u := by
  have hw2 : ‖(inner ℬ w w : ℬ)‖ ≤ ‖w‖ ^ 2 := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ) w,
      Real.sq_sqrt (norm_nonneg _)]
  have hmono : t (inner 𝒜 u u) (inner ℬ w w)
      ≤ t (inner 𝒜 u u) (((‖w‖ ^ 2 : ℝ) : ℂ) • (1 : ℬ)) :=
    vnTensor_mono_right ht CStarModule.inner_self_nonneg
      (le_ofReal_smul_one CStarModule.inner_self_nonneg hw2)
  have hre : (Ω (inner 𝒞 (E.η u w) (E.η u w))).re
      ≤ ‖w‖ ^ 2 * (vnTensorLegLeftNP ht Ω (inner 𝒜 u u)).re := by
    rw [E.η_inner, vnTensorLegLeftNP_apply]
    have h2 := npFunctional_mono Ω hmono
    rw [vnTensor_smul_complex_right ht, npf_csmul] at h2
    simpa [Complex.mul_re, ← Complex.ofReal_pow] using (Complex.le_def.mp h2).1
  calc unSeminorm Ω (inner 𝒞) (E.η u w)
      ≤ Real.sqrt (‖w‖ ^ 2 * (vnTensorLegLeftNP ht Ω (inner 𝒜 u u)).re) :=
        Real.sqrt_le_sqrt hre
    _ = ‖w‖ * unSeminorm (vnTensorLegLeftNP ht Ω) (inner 𝒜) u := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]; rfl

/-- `‖u ⊗ w‖_Ω ≤ ‖u‖ · ‖w‖_{Ω(1⊗·)}`: the mirror of
`unSeminorm_eta_le_left`. -/
private theorem unSeminorm_eta_le_right (E : ExtTensor t ht X Y)
    (Ω : NPFunctional 𝒞) (u : X) (w : Y) :
    unSeminorm Ω (inner 𝒞) (E.η u w)
      ≤ ‖u‖ * unSeminorm (vnTensorLegRightNP ht Ω) (inner ℬ) w := by
  have hu2 : ‖(inner 𝒜 u u : 𝒜)‖ ≤ ‖u‖ ^ 2 := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒜) u,
      Real.sq_sqrt (norm_nonneg _)]
  have hmono : t (inner 𝒜 u u) (inner ℬ w w)
      ≤ t (((‖u‖ ^ 2 : ℝ) : ℂ) • (1 : 𝒜)) (inner ℬ w w) :=
    vnTensor_mono_left ht CStarModule.inner_self_nonneg
      (le_ofReal_smul_one CStarModule.inner_self_nonneg hu2)
  have hre : (Ω (inner 𝒞 (E.η u w) (E.η u w))).re
      ≤ ‖u‖ ^ 2 * (vnTensorLegRightNP ht Ω (inner ℬ w w)).re := by
    rw [E.η_inner, vnTensorLegRightNP_apply]
    have h2 := npFunctional_mono Ω hmono
    rw [ht.smul_complex, npf_csmul] at h2
    simpa [Complex.mul_re, ← Complex.ofReal_pow] using (Complex.le_def.mp h2).1
  calc unSeminorm Ω (inner 𝒞) (E.η u w)
      ≤ Real.sqrt (‖u‖ ^ 2 * (vnTensorLegRightNP ht Ω (inner ℬ w w)).re) :=
        Real.sqrt_le_sqrt hre
    _ = ‖u‖ * unSeminorm (vnTensorLegRightNP ht Ω) (inner ℬ) w := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]; rfl

end EtaEstimates

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), property 2a:
for orthonormal bases `(eᵢ)` of `X` and `(dⱼ)` of `Y`, the family
`(eᵢ ⊗ dⱼ)` is an orthonormal basis of `X ⊗ Y`.

The thesis's proof is **164X**, and the skeleton is transcribed: `E₂` is
clearly orthonormal, and by **160IX** + **160IV** it is enough that every
point of `X ⊗ Y` lies in `E₂^⊥⊥`, which by **160IV**.2 is the ultranorm
closure of the `𝒞`-span of `E₂`.

**Divergence (class 2) in the last step.**  Because the thesis has `X ⊗ Y`
*defined* as `ℓ²((pᵢⱼ))` for one distinguished pair of bases, it can reduce
to `eᵢ₀ ⊗ dⱼ₀ ∈ E₂^⊥⊥` for the distinguished basis and then verify the
Parseval identity of **160IX**.2 by testing against product np-functionals.
Our `E` is an arbitrary `ExtTensor`, so there is no distinguished basis to
reduce to; instead **164II**.1 `ext_tensor_dense` (now proved) reduces the
claim to the elementary tensors, and `η v w` is approximated directly by
`η vₛ wᵤ = ∑_{i∈s} ∑_{j∈u} (⟨eᵢ,v⟩ ⊗ ⟨dⱼ,w⟩)·(eᵢ ⊗ dⱼ)`, with `s` chosen
first and `u` afterwards — the same order-of-choice device that removed
**158II** from **166IV** — so that only the **166III** estimates
`unSeminorm_eta_le_left/_right` are needed and the product-functional
computation is avoided altogether.  (Testing against product functionals
would still be needed for the thesis's route: it needs to know that
`∑ᵢⱼ aᵢ*aᵢ ⊗ bⱼ*bⱼ` converges ultraweakly to `⟨v,v⟩ ⊗ ⟨w,w⟩`, which is
`tensor-3`.  Here the only use of `IsVNTensor` beyond bilinearity is the
non-degeneracy `⟨eᵢ,eᵢ⟩ ⊗ ⟨dⱼ,dⱼ⟩ ≠ 0`, for which the product functionals
*are* used.) -/
theorem ext_tensor_basis [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    {ι κ : Type u} (e : ι → X) (d : κ → Y)
    (he : IsONBasis 𝒜 e) (hd : IsONBasis ℬ d) :
    IsONBasis 𝒞 fun p : ι × κ => E.η (e p.1) (d p.2) := by
  classical
  obtain ⟨heo, heexp, -⟩ := he
  obtain ⟨hdo, hdexp, -⟩ := hd
  set f : ι × κ → E.Z := fun p => E.η (e p.1) (d p.2) with hfdef
  -- `t` and `η` kill zeros
  have ht0l : ∀ b : ℬ, t (0 : 𝒜) b = 0 := fun b => by
    have h := ht.add_left 0 0 b
    rw [add_zero] at h
    exact (add_left_cancel (a := t 0 b) (by rw [add_zero]; exact h)).symm
  have ht0r : ∀ a : 𝒜, t a (0 : ℬ) = 0 := fun a => by
    have h := ht.add_right a 0 0
    rw [add_zero] at h
    exact (add_left_cancel (a := t a 0) (by rw [add_zero]; exact h)).symm
  have hη0l : ∀ w : Y, E.η (0 : X) w = 0 := fun w => by
    have h := E.η_add_left 0 0 w
    rw [add_zero] at h
    exact (add_left_cancel (a := E.η 0 w) (by rw [add_zero]; exact h)).symm
  have hη0r : ∀ v : X, E.η v (0 : Y) = 0 := fun v => by
    have h := E.η_add_right v 0 0
    rw [add_zero] at h
    exact (add_left_cancel (a := E.η v 0) (by rw [add_zero]; exact h)).symm
  have hηsuml : ∀ (s : Finset ι) (g : ι → X) (w : Y),
      E.η (∑ i ∈ s, g i) w = ∑ i ∈ s, E.η (g i) w := by
    intro s g w
    refine Finset.induction_on s (by rw [Finset.sum_empty, Finset.sum_empty,
      hη0l]) fun i s hi ih => ?_
    rw [Finset.sum_insert hi, E.η_add_left, ih, Finset.sum_insert hi]
  have hηsumr : ∀ (v : X) (s : Finset κ) (g : κ → Y),
      E.η v (∑ j ∈ s, g j) = ∑ j ∈ s, E.η v (g j) := by
    intro v s g
    refine Finset.induction_on s (by rw [Finset.sum_empty, Finset.sum_empty,
      hη0r]) fun j s hj ih => ?_
    rw [Finset.sum_insert hj, E.η_add_right, ih, Finset.sum_insert hj]
  have hfinner : ∀ p q : ι × κ, (inner 𝒞 (f p) (f q) : 𝒞)
      = t (inner 𝒜 (e p.1) (e q.1)) (inner ℬ (d p.2) (d q.2)) :=
    fun p q => E.η_inner _ _ _ _
  -- (1) `E₂` is orthonormal
  have horth : OrthonormalFam 𝒞 f := by
    refine ⟨fun p q hpq => ?_, fun p => ⟨?_, ?_⟩⟩
    · rw [hfinner]
      by_cases h1 : p.1 = q.1
      · have h2 : p.2 ≠ q.2 := fun h => hpq (Prod.ext h1 h)
        rw [hdo.1 p.2 q.2 h2, ht0r]
      · rw [heo.1 p.1 q.1 h1, ht0l]
    · rw [hfinner, isStarProjection_iff']
      refine ⟨?_, ?_⟩
      · rw [ht.mul, (heo.2 p.1).1.isIdempotentElem, (hdo.2 p.2).1.isIdempotentElem]
      · rw [ht.star, (heo.2 p.1).1.isSelfAdjoint, (hdo.2 p.2).1.isSelfAdjoint]
    · -- non-degeneracy, via product np-functionals (`tensor-2`)
      rw [hfinner]
      intro h0
      obtain ⟨ω, hω⟩ : ∃ ω : NPFunctional 𝒜, ω (inner 𝒜 (e p.1) (e p.1)) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact (heo.2 p.1).2 (np_separating _ hcon)
      obtain ⟨ξ, hξ⟩ : ∃ ξ : NPFunctional ℬ, ξ (inner ℬ (d p.2) (d p.2)) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact (hdo.2 p.2).2 (np_separating _ hcon)
      obtain ⟨Ω, hΩ⟩ := ht.exists_productFunctional ω ξ
      have hz := hΩ (inner 𝒜 (e p.1) (e p.1)) (inner ℬ (d p.2) (d p.2))
      rw [h0, npFunctional_zero] at hz
      exact mul_ne_zero hω hξ hz.symm
  -- (3) clause (b) of `IsONBasis` holds for every orthonormal family
  refine ⟨horth, fun z => ?_, fun b hb => exists_unTendsto_of_l2Summable
    (bddUnComplete_of_selfDual E.selfDual) horth b hb⟩
  -- (2) clause (a): by **160IX**.1 it suffices that `z ∈ E₂^⊥⊥`
  refine (selfdual_orthn_basis E.selfDual f horth z).1 ?_
  rw [hilbmod_projthm_2 E.selfDual (Set.range f)]
  -- every *elementary* tensor lies in the ultranorm closure of the span
  have helem : ∀ (v : X) (w : Y),
      E.η v w ∈ unClosure 𝒞 (inner 𝒞) (bSpan 𝒞 (Set.range f)) := by
    intro v w n Ωs ε hε
    have hw1 : (0 : ℝ) < ‖w‖ + 1 := by positivity
    have hδ₁ : 0 < ε / (2 * (‖w‖ + 1)) := by positivity
    obtain ⟨s, hs⟩ : ∃ s : Finset ι, ∀ k : Fin n,
        unSeminorm (vnTensorLegLeftNP ht (Ωs k)) (inner 𝒜)
            ((∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i) - v)
          ≤ ε / (2 * (‖w‖ + 1)) := by
      have hall : ∀ᶠ s in (atTop : Filter (Finset ι)), ∀ k : Fin n,
          unSeminorm (vnTensorLegLeftNP ht (Ωs k)) (inner 𝒜)
              ((∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i) - v)
            ≤ ε / (2 * (‖w‖ + 1)) := by
        rw [Filter.eventually_all]
        exact fun k => ((heexp v (vnTensorLegLeftNP ht (Ωs k))).eventually_lt_const
          hδ₁).mono fun _ h => h.le
      exact hall.exists
    have hv1 : (0 : ℝ) < ‖∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i‖ + 1 := by positivity
    have hδ₂ : 0 < ε / (2 * (‖∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i‖ + 1)) := by
      positivity
    obtain ⟨u, hu⟩ : ∃ u : Finset κ, ∀ k : Fin n,
        unSeminorm (vnTensorLegRightNP ht (Ωs k)) (inner ℬ)
            ((∑ j ∈ u, (inner ℬ (d j) w : ℬ) • d j) - w)
          ≤ ε / (2 * (‖∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i‖ + 1)) := by
      have hall : ∀ᶠ u in (atTop : Filter (Finset κ)), ∀ k : Fin n,
          unSeminorm (vnTensorLegRightNP ht (Ωs k)) (inner ℬ)
              ((∑ j ∈ u, (inner ℬ (d j) w : ℬ) • d j) - w)
            ≤ ε / (2 * (‖∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i‖ + 1)) := by
        rw [Filter.eventually_all]
        exact fun k => ((hdexp w (vnTensorLegRightNP ht (Ωs k))).eventually_lt_const
          hδ₂).mono fun _ h => h.le
      exact hall.exists
    refine ⟨E.η (∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i)
      (∑ j ∈ u, (inner ℬ (d j) w : ℬ) • d j), ?_, fun k => ?_⟩
    · -- the approximant is a `𝒞`-combination of the `eᵢ ⊗ dⱼ`
      have hexpand : E.η (∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i)
            (∑ j ∈ u, (inner ℬ (d j) w : ℬ) • d j)
          = ∑ i ∈ s, ∑ j ∈ u,
              t (inner 𝒜 (e i) v) (inner ℬ (d j) w) • f (i, j) := by
        rw [hηsuml s (fun i => (inner 𝒜 (e i) v : 𝒜) • e i)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hηsumr _ u (fun j => (inner ℬ (d j) w : ℬ) • d j)]
        exact Finset.sum_congr rfl fun j _ => E.η_smul _ _ _ _
      rw [hexpand]
      refine Finset.sum_induction _ _ (fun a b ha hb => bSpan_add _ a ha b hb)
        (zero_mem_bSpan _) fun i _ => ?_
      refine Finset.sum_induction _ _ (fun a b ha hb => bSpan_add _ a ha b hb)
        (zero_mem_bSpan _) fun j _ => ?_
      exact bSpan_op_smul _ _ _ (subset_bSpan _ (Set.mem_range_self (i, j)))
    · -- the estimate: split, then **166III** twice
      have hsplit : E.η v w - E.η (∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i)
            (∑ j ∈ u, (inner ℬ (d j) w : ℬ) • d j)
          = E.η (v - ∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i) w
            + E.η (∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i)
                (w - ∑ j ∈ u, (inner ℬ (d j) w : ℬ) • d j) := by
        have h1 : E.η (v - ∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i) w
            + E.η (∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i) w = E.η v w := by
          rw [← E.η_add_left]; congr 1; abel
        have h2 : E.η (∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i)
              (w - ∑ j ∈ u, (inner ℬ (d j) w : ℬ) • d j)
            + E.η (∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i)
                (∑ j ∈ u, (inner ℬ (d j) w : ℬ) • d j)
            = E.η (∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i) w := by
          rw [← E.η_add_right]; congr 1; abel
        rw [← h1, ← h2]; abel
      have hneg1 : unSeminorm (vnTensorLegLeftNP ht (Ωs k)) (inner 𝒜)
            (v - ∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i)
          = unSeminorm (vnTensorLegLeftNP ht (Ωs k)) (inner 𝒜)
            ((∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i) - v) := by
        rw [← unSeminorm_neg_inner (X := X), neg_sub]
      have hneg2 : unSeminorm (vnTensorLegRightNP ht (Ωs k)) (inner ℬ)
            (w - ∑ j ∈ u, (inner ℬ (d j) w : ℬ) • d j)
          = unSeminorm (vnTensorLegRightNP ht (Ωs k)) (inner ℬ)
            ((∑ j ∈ u, (inner ℬ (d j) w : ℬ) • d j) - w) := by
        rw [← unSeminorm_neg_inner (X := Y), neg_sub]
      rw [hsplit]
      refine le_trans (unSeminorm_add_le _ (cstarBInner 𝒞 E.Z) _ _) ?_
      refine le_trans (add_le_add (unSeminorm_eta_le_left E _ _ _)
        (unSeminorm_eta_le_right E _ _ _)) ?_
      rw [hneg1, hneg2]
      have hq1 : ε / (2 * (‖w‖ + 1)) * (2 * (‖w‖ + 1)) = ε :=
        div_mul_cancel₀ _ (by positivity)
      have hq2 : ε / (2 * (‖∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i‖ + 1))
          * (2 * (‖∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i‖ + 1)) = ε :=
        div_mul_cancel₀ _ (by positivity)
      have hb1 : ‖w‖ * unSeminorm (vnTensorLegLeftNP ht (Ωs k)) (inner 𝒜)
          ((∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i) - v) ≤ ε / 2 := by
        refine le_trans (mul_le_mul_of_nonneg_left (hs k) (norm_nonneg w)) ?_
        have hD0 : (0 : ℝ) ≤ ε / (2 * (‖w‖ + 1)) := le_of_lt hδ₁
        nlinarith [hD0, norm_nonneg w, hq1]
      have hb2 : ‖∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i‖
          * unSeminorm (vnTensorLegRightNP ht (Ωs k)) (inner ℬ)
            ((∑ j ∈ u, (inner ℬ (d j) w : ℬ) • d j) - w) ≤ ε / 2 := by
        refine le_trans (mul_le_mul_of_nonneg_left (hu k) (norm_nonneg _)) ?_
        have hD0 : (0 : ℝ) ≤ ε
            / (2 * (‖∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i‖ + 1)) := le_of_lt hδ₂
        nlinarith [hD0, norm_nonneg (∑ i ∈ s, (inner 𝒜 (e i) v : 𝒜) • e i), hq2]
      linarith
  -- **164II**.1: the elementary tensors span an ultranorm-dense set
  have hD : {w : E.Z | ∃ (m : ℕ) (x : Fin m → X) (y : Fin m → Y),
        w = ∑ i, E.η (x i) (y i)}
      ⊆ unClosure 𝒞 (inner 𝒞) (bSpan 𝒞 (Set.range f)) := by
    rintro _ ⟨m, x, y, rfl⟩
    exact Finset.sum_induction _ _
      (fun a b ha hb => unClosure_add (bSpan_add _) ha hb)
      (subset_unClosure _ (zero_mem_bSpan _)) fun i _ => helem (x i) (y i)
  rw [← unClosure_unClosure (bSpan 𝒞 (Set.range f))]
  exact unClosure_mono hD (ext_tensor_dense hX hY E z)

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), property 2b:
the linear span of the `|(eᵢa) ⊗ (dⱼb)⟩⟨e_k ⊗ d_l|` is ultraweakly dense
in `𝒞ᵃ(X ⊗ Y)`.

**164X**–**164XI** are the proof; **164XII** (Examples) — not
converted. -/
theorem ext_tensor_ketbra_dense [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    {ι κ : Type u} (e : ι → X) (d : κ → Y)
    (he : IsONBasis 𝒜 e) (hd : IsONBasis ℬ d) (T : Ba 𝒞 E.Z) :
    ∃ approx : Finset (ι × κ) → Ba 𝒞 E.Z,
      (∀ s, approx s ∈ Submodule.span ℂ
        {S : Ba 𝒞 E.Z | ∃ (i k : ι) (j l : κ) (a : 𝒜) (b : ℬ),
          S.1 = mketbra 𝒞 (E.η (a • e i) (b • d j)) (E.η (e k) (d l))}) ∧
      UWTendsto approx atTop T :=
  sorry

/-- **164XI** (dils.tex:5327), the thesis's own claim: the linear span of
`D = {|(e'ᵢa) ⊗ (d'ⱼb)⟩⟨e_k ⊗ d_l|}` is **ultraweakly dense** in
`𝒞ᵃ(X ⊗ Y)` — here in the entourage form (given finitely many
np-functionals and an `ε > 0`, some element of the span is within `ε` of
`T` on all of them).

⚠️ This is *weaker* than `ext_tensor_ketbra_dense` above, which forces the
approximating net to be indexed by `Finset (ι × κ)` along `atTop`; that
form is **false** (QUESTIONS **D6**): take `ι = κ = PUnit`, `X = 𝒜`,
`Y = ℬ`, `E = extTensorSelf` — then `Finset (ι × κ)` has a greatest
element, `atTop` is the principal filter there, and the net's value at that
element would have to *equal* `T`, forcing `𝒜 ⊗ ℬ = 𝒜 ⊙ ℬ`.

The proof is the thesis's **164XI**: **159IV** `ketbra_ultraweakly_dense`,
applied to the basis `E₂` supplied by **164II**.2a, gives the operators
`|b·(e'ᵢ ⊗ d'ⱼ)⟩⟨e'_k ⊗ d'_l|` with `b ∈ 𝒜 ⊗ ℬ` arbitrary, and Kaplansky
(**74IV**, through `unDense_tSpan`) together with **159IX**
`ketbra_ultranorm_continuous` replaces `b` by an element of `𝒜 ⊙ ℬ` — the
extra step being that Kaplansky's net lies in the *norm* closure of
`𝒜 ⊙ ℬ`, from which the norm-continuity of `b ↦ |b·v⟩⟨w|` and of the
np-functionals brings it back into `𝒜 ⊙ ℬ` itself. -/
theorem ext_tensor_ketbra_uwDense [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    {ι κ : Type u} (e : ι → X) (d : κ → Y)
    (he : IsONBasis 𝒜 e) (hd : IsONBasis ℬ d) (T : Ba 𝒞 E.Z)
    {m : ℕ} (gs : Fin m → NPFunctional (Ba 𝒞 E.Z)) (ε : ℝ) (hε : 0 < ε) :
    ∃ S ∈ Submodule.span ℂ
        {S : Ba 𝒞 E.Z | ∃ (i k : ι) (j l : κ) (a : 𝒜) (b : ℬ),
          S.1 = mketbra 𝒞 (E.η (a • e i) (b • d j)) (E.η (e k) (d l))},
      ∀ k, ‖(gs k) T - (gs k) S‖ ≤ ε := by
  classical
  set f : ι × κ → E.Z := fun p => E.η (e p.1) (d p.2) with hfdef
  have hf : IsONBasis 𝒞 f := ext_tensor_basis hX hY E e d he hd
  set Dset : Set (Ba 𝒞 E.Z) :=
    {S : Ba 𝒞 E.Z | ∃ (i k : ι) (j l : κ) (a : 𝒜) (b : ℬ),
      S.1 = mketbra 𝒞 (E.η (a • e i) (b • d j)) (E.η (e k) (d l))} with hDdef
  -- the `gs` are norm-bounded (positive linear maps are)
  choose Cs hCs using fun k : Fin m =>
    PositiveLinearMap.exists_norm_apply_le (gs k).toPositiveLinearMap
  set Cmax : ℝ := ∑ k : Fin m, (Cs k : ℝ) with hCmaxdef
  have hCmax0 : (0 : ℝ) ≤ Cmax :=
    Finset.sum_nonneg fun k _ => (Cs k).coe_nonneg
  have hgsb : ∀ (k : Fin m) (z : Ba 𝒞 E.Z), ‖(gs k) z‖ ≤ Cmax * ‖z‖ := by
    intro k z
    refine (hCs k z).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg z))
    exact Finset.single_le_sum (f := fun k : Fin m => (Cs k : ℝ))
      (fun k _ => (Cs k).coe_nonneg) (Finset.mem_univ k)
  -- **Kaplansky**: every `c ∈ 𝒜 ⊗ ℬ` is the limit of a norm-bounded net
  -- from the norm closure of `𝒜 ⊙ ℬ`
  have hkap : ∀ c : 𝒞, ∃ (J : Type u) (l : Filter J), l.NeBot ∧ ∃ a : J → 𝒞,
      (∀ j, a j ∈ (tSpanSubalg ht).topologicalClosure ∧ ‖a j‖ ≤ ‖c‖) ∧
      UnTendsto (mulInner 𝒞) a l c := by
    intro c
    have hsub : tSpan t ⊆ (((tSpanSubalg ht).topologicalClosure : StarSubalgebra ℂ 𝒞) : Set 𝒞) :=
      fun x hx => subset_closure (show x ∈ (tSpanSubalg ht : Set 𝒞) from hx)
    have hmem : star c ∈ @closure 𝒞 (ultrastrong 𝒞)
        ((((tSpanSubalg ht).topologicalClosure : StarSubalgebra ℂ 𝒞) : Set 𝒞)) := by
      rw [mem_usClosure_iff]
      intro ω δ hδ
      obtain ⟨z, hz, hzε⟩ := unDense_tSpan ht c 1 (fun _ => ω) (δ / 2) (by positivity)
      have h0 := hzε 0
      rw [unSeminorm_mulInner_eq, star_sub] at h0
      refine ⟨star z, star_mem (hsub hz), ?_⟩
      have h1 : omegaNorm 𝒞 ω (star z - star c) = omegaNorm 𝒞 ω (star c - star z) := by
        rw [← omegaNorm_neg, neg_sub]
      rw [h1]
      linarith
    obtain ⟨J, l, hl, b, hb, hlim⟩ := Theses.A.VN.kaplansky
      ((tSpanSubalg ht).topologicalClosure)
      (StarSubalgebra.isClosed_topologicalClosure _) (star c) hmem
    refine ⟨J, l, hl, fun j => star (b j),
      fun j => ⟨star_mem (hb j).1, by simpa using (hb j).2⟩, fun ω => ?_⟩
    refine ((usTendsto_iff b l (star c)).mp hlim ω).congr fun j => ?_
    rw [unSeminorm_mulInner_eq, star_sub, star_star]
  -- the generators of **159IV** are approximable from `span D`
  have hgen : ∀ (c : 𝒞) (p q : ι × κ) (δ : ℝ), 0 < δ →
      ∃ S ∈ Submodule.span ℂ Dset,
        ∀ k, ‖(gs k) (mketbraBa (ℬ := 𝒞) (c • f p) (f q)) - (gs k) S‖ ≤ δ := by
    intro c p q δ hδ
    obtain ⟨J, l, hl, a, ha, halim⟩ := hkap c
    haveI := hl
    have hsmul_sub : ∀ (u v : 𝒞) (z : E.Z), (u - v) • z = u • z - v • z := by
      intro u v z
      have h := op_add_smul (u - v) v z
      rw [sub_add_cancel] at h
      rw [h]; abel
    have hsmul_sub' : ∀ (b : 𝒞) (u v : E.Z), b • (u - v) = b • u - b • v := by
      intro b u v
      have h := op_smul_add b (u - v) v
      rw [sub_add_cancel] at h
      rw [h]; abel
    have hun : UnTendsto (inner 𝒞) (fun j => a j • f p) l (c • f p) := by
      intro ω
      have hb : ∀ j, unSeminorm ω (inner 𝒞 : E.Z → E.Z → 𝒞) (a j • f p - c • f p)
          ≤ ‖f p‖ * unSeminorm ω (mulInner 𝒞) (a j - c) := by
        intro j
        rw [← hsmul_sub]
        exact unSeminorm_op_smul_le ω (a j - c) (f p)
      refine squeeze_zero (fun j => Real.sqrt_nonneg _) hb ?_
      simpa using (halim ω).const_mul ‖f p‖
    have hbdd : ∃ M : ℝ, ∀ j, ‖a j • f p‖ ≤ M :=
      ⟨‖c‖ * ‖f p‖, fun j => (norm_op_smul_le _ _).trans
        (mul_le_mul_of_nonneg_right (ha j).2 (norm_nonneg _))⟩
    have huw : UWTendsto (fun j => mketbraBa (ℬ := 𝒞) (a j • f p) (f q)) l
        (mketbraBa (ℬ := 𝒞) (c • f p) (f q)) :=
      ketbra_ultranorm_continuous E.selfDual _ _ hbdd hun (f q) _ (fun j => rfl) _ rfl
    rw [uwTendsto_iff] at huw
    have hev : ∀ᶠ j in l, ∀ k,
        ‖(gs k) (mketbraBa (ℬ := 𝒞) (c • f p) (f q))
          - (gs k) (mketbraBa (ℬ := 𝒞) (a j • f p) (f q))‖ ≤ δ / 2 := by
      refine Filter.eventually_all.mpr fun k => ?_
      filter_upwards [Metric.tendsto_nhds.mp (huw (gs k)) (δ / 2) (by positivity)] with j hj
      rw [dist_eq_norm] at hj
      rw [norm_sub_rev]
      exact hj.le
    obtain ⟨j₀, hj₀⟩ := hev.exists
    -- back from the norm closure into `𝒜 ⊙ ℬ`
    set η₀ : ℝ := δ / (2 * (Cmax + 1) * (‖f p‖ * ‖f q‖ + 1)) with hηdef
    have hη0 : 0 < η₀ := by
      rw [hηdef]; positivity
    obtain ⟨s, hs, hsd⟩ : ∃ s ∈ tSpan t, ‖a j₀ - s‖ < η₀ := by
      have hmem : a j₀ ∈ closure (tSpan t) := (ha j₀).1
      rw [Metric.mem_closure_iff] at hmem
      obtain ⟨s, hs, hdist⟩ := hmem η₀ hη0
      exact ⟨s, hs, by rwa [dist_eq_norm] at hdist⟩
    refine ⟨mketbraBa (ℬ := 𝒞) (s • f p) (f q), ?_, fun k => ?_⟩
    · obtain ⟨n, α, β, rfl⟩ := hs
      have hsum : mketbraBa (ℬ := 𝒞) ((∑ i, t (α i) (β i)) • f p) (f q)
          = ∑ i, mketbraBa (ℬ := 𝒞) (t (α i) (β i) • f p) (f q) := by
        refine Subtype.ext (ContinuousLinearMap.ext fun z => ?_)
        rw [baVal_sum]
        show (inner 𝒞 (f q) z : 𝒞) • ((∑ i, t (α i) (β i)) • f p)
          = ∑ i, (inner 𝒞 (f q) z : 𝒞) • (t (α i) (β i) • f p)
        rw [add_smul_sum, op_smul_sum]
      rw [hsum]
      refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_
      refine ⟨p.1, q.1, p.2, q.2, α i, β i, ?_⟩
      show mketbra 𝒞 (t (α i) (β i) • f p) (f q) = _
      rw [hfdef]
      rw [← E.η_smul]
    · have hdiff : mketbraBa (ℬ := 𝒞) (a j₀ • f p) (f q)
          - mketbraBa (ℬ := 𝒞) (s • f p) (f q)
          = mketbraBa (ℬ := 𝒞) ((a j₀ - s) • f p) (f q) := by
        refine Subtype.ext (ContinuousLinearMap.ext fun z => ?_)
        show (inner 𝒞 (f q) z : 𝒞) • (a j₀ • f p) - (inner 𝒞 (f q) z : 𝒞) • (s • f p)
          = (inner 𝒞 (f q) z : 𝒞) • ((a j₀ - s) • f p)
        rw [hsmul_sub, hsmul_sub']
      have hnorm : ‖mketbraBa (ℬ := 𝒞) (a j₀ • f p) (f q)
          - mketbraBa (ℬ := 𝒞) (s • f p) (f q)‖ ≤ ‖f q‖ * (‖a j₀ - s‖ * ‖f p‖) := by
        rw [hdiff]
        show ‖mketbra 𝒞 ((a j₀ - s) • f p) (f q)‖ ≤ _
        refine (LinearMap.mkContinuous_norm_le _ (by positivity) _).trans ?_
        exact mul_le_mul_of_nonneg_left (norm_op_smul_le _ _) (norm_nonneg _)
      have hgsdiff : ‖(gs k) (mketbraBa (ℬ := 𝒞) (a j₀ • f p) (f q))
          - (gs k) (mketbraBa (ℬ := 𝒞) (s • f p) (f q))‖
          ≤ Cmax * (‖f q‖ * (‖a j₀ - s‖ * ‖f p‖)) := by
        rw [← npFunctional_sub]
        exact (hgsb k _).trans (mul_le_mul_of_nonneg_left hnorm hCmax0)
      have hkey : Cmax * (‖f q‖ * (‖a j₀ - s‖ * ‖f p‖)) ≤ δ / 2 := by
        have h1 : ‖a j₀ - s‖ ≤ η₀ := hsd.le
        have hn1 : (0 : ℝ) ≤ ‖f p‖ := norm_nonneg _
        have hn2 : (0 : ℝ) ≤ ‖f q‖ := norm_nonneg _
        have hA : Cmax * (‖f q‖ * (‖a j₀ - s‖ * ‖f p‖))
            ≤ Cmax * (‖f p‖ * ‖f q‖) * η₀ := by
          have hrw : Cmax * (‖f q‖ * (‖a j₀ - s‖ * ‖f p‖))
              = Cmax * (‖f p‖ * ‖f q‖) * ‖a j₀ - s‖ := by ring
          rw [hrw]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
        have hB : Cmax * (‖f p‖ * ‖f q‖) * η₀
            ≤ (Cmax + 1) * (‖f p‖ * ‖f q‖ + 1) * η₀ := by
          refine mul_le_mul_of_nonneg_right ?_ hη0.le
          nlinarith
        have h3 : (Cmax + 1) * (‖f p‖ * ‖f q‖ + 1) * η₀ = δ / 2 := by
          rw [hηdef]
          field_simp
        linarith
      calc ‖(gs k) (mketbraBa (ℬ := 𝒞) (c • f p) (f q))
            - (gs k) (mketbraBa (ℬ := 𝒞) (s • f p) (f q))‖
          ≤ ‖(gs k) (mketbraBa (ℬ := 𝒞) (c • f p) (f q))
              - (gs k) (mketbraBa (ℬ := 𝒞) (a j₀ • f p) (f q))‖
            + ‖(gs k) (mketbraBa (ℬ := 𝒞) (a j₀ • f p) (f q))
              - (gs k) (mketbraBa (ℬ := 𝒞) (s • f p) (f q))‖ := by
            simpa using norm_sub_le_norm_sub_add_norm_sub
              ((gs k) (mketbraBa (ℬ := 𝒞) (c • f p) (f q)))
              ((gs k) (mketbraBa (ℬ := 𝒞) (a j₀ • f p) (f q)))
              ((gs k) (mketbraBa (ℬ := 𝒞) (s • f p) (f q)))
        _ ≤ δ / 2 + δ / 2 := add_le_add (hj₀ k) (hgsdiff.trans hkey)
        _ = δ := by ring
  -- the whole span of the **159IV** generators is approximable
  have hspan : ∀ z ∈ Submodule.span ℂ
      {S : Ba 𝒞 E.Z | ∃ (p q : ι × κ) (b : 𝒞), S.1 = mketbra 𝒞 (b • f p) (f q)},
      ∀ δ : ℝ, 0 < δ → ∃ S ∈ Submodule.span ℂ Dset,
        ∀ k, ‖(gs k) z - (gs k) S‖ ≤ δ := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨p, q, b, hb⟩ := hx
        intro δ hδ
        have hx' : x = mketbraBa (ℬ := 𝒞) (b • f p) (f q) := Subtype.ext hb
        rw [hx']
        exact hgen b p q δ hδ
    | zero =>
        intro δ hδ
        exact ⟨0, Submodule.zero_mem _, fun k => by simp [hδ.le]⟩
    | add x y hx hy ihx ihy =>
        intro δ hδ
        obtain ⟨S₁, hS₁, hS₁e⟩ := ihx (δ / 2) (by positivity)
        obtain ⟨S₂, hS₂, hS₂e⟩ := ihy (δ / 2) (by positivity)
        refine ⟨S₁ + S₂, Submodule.add_mem _ hS₁ hS₂, fun k => ?_⟩
        have hsplit : (gs k) (x + y) - (gs k) (S₁ + S₂)
            = ((gs k) x - (gs k) S₁) + ((gs k) y - (gs k) S₂) := by
          rw [npFunctional_add, npFunctional_add]; ring
        rw [hsplit]
        calc ‖((gs k) x - (gs k) S₁) + ((gs k) y - (gs k) S₂)‖
            ≤ ‖(gs k) x - (gs k) S₁‖ + ‖(gs k) y - (gs k) S₂‖ := norm_add_le _ _
          _ ≤ δ / 2 + δ / 2 := add_le_add (hS₁e k) (hS₂e k)
          _ = δ := by ring
    | smul c x hx ih =>
        intro δ hδ
        obtain ⟨S₁, hS₁, hS₁e⟩ := ih (δ / (‖c‖ + 1)) (by positivity)
        refine ⟨c • S₁, Submodule.smul_mem _ c hS₁, fun k => ?_⟩
        have hsplit : (gs k) (c • x) - (gs k) (c • S₁)
            = c * ((gs k) x - (gs k) S₁) := by
          rw [npf_csmul, npf_csmul]; ring
        rw [hsplit, norm_mul]
        have hc0 : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
        have h1 : ‖(gs k) x - (gs k) S₁‖ ≤ δ / (‖c‖ + 1) := hS₁e k
        have h2 : ‖c‖ * (δ / (‖c‖ + 1)) ≤ δ := by
          rw [mul_div_assoc'] at *
          rw [div_le_iff₀ (by positivity)]
          nlinarith
        calc ‖c‖ * ‖(gs k) x - (gs k) S₁‖ ≤ ‖c‖ * (δ / (‖c‖ + 1)) :=
              mul_le_mul_of_nonneg_left h1 hc0
          _ ≤ δ := h2
  -- **159IV**, then the two approximations
  obtain ⟨approx, happrox, hlim⟩ := ketbra_ultraweakly_dense E.selfDual f hf T
  rw [uwTendsto_iff] at hlim
  have hev : ∀ᶠ s in (atTop : Filter (Finset (ι × κ))), ∀ k,
      ‖(gs k) T - (gs k) (approx s)‖ ≤ ε / 2 := by
    refine Filter.eventually_all.mpr fun k => ?_
    filter_upwards [Metric.tendsto_nhds.mp (hlim (gs k)) (ε / 2) (by positivity)] with s hs
    rw [dist_eq_norm] at hs
    rw [norm_sub_rev]
    exact hs.le
  obtain ⟨s₀, hs₀⟩ := hev.exists
  obtain ⟨S, hS, hSe⟩ := hspan (approx s₀) (happrox s₀) (ε / 2) (by positivity)
  refine ⟨S, hS, fun k => ?_⟩
  calc ‖(gs k) T - (gs k) S‖
      ≤ ‖(gs k) T - (gs k) (approx s₀)‖ + ‖(gs k) (approx s₀) - (gs k) S‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub ((gs k) T)
          ((gs k) (approx s₀)) ((gs k) S)
    _ ≤ ε / 2 + ε / 2 := add_le_add (hs₀ k) (hSe k)
    _ = ε := by ring

/-! ## Parsec 1650: 𝒷ᵃ(X) ⊗ 𝒷ᵃ(Y) ≅ 𝒷ᵃ(X ⊗ Y)

**165I** (dils.tex:5407): introduction; **165II** (Setting) — nothing to
formalize. -/

-- `hX`, `hY` are not used below: the universal property is a *field* of
-- `ExtTensor`, and adjointability of the factorisation is supplied by the
-- factorisation of `(S*, T*)`, so no self-duality of `X`, `Y` beyond what
-- `E` already carries is needed.  They are kept for uniformity with the
-- neighbouring statements of parsecs 1640-1670.
set_option linter.unusedVariables false in
/-- **165III** (`dfn-tensor-of-hilbmod-maps`, dils.tex:5426, Proposition):
for `S ∈ 𝒜ᵃ(X)` and `T ∈ ℬᵃ(Y)` there is a unique operator
`S ⊗ T ∈ 𝒞ᵃ(X ⊗ Y)` with `(S ⊗ T)(x ⊗ y) = (Sx) ⊗ (Ty)`.

**165IV** is the proof, transcribed below. -/
theorem dfn_tensor_of_hilbmod_maps [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] [VonNeumannAlgebra 𝒞] [CompleteSpace X]
    [CompleteSpace Y] (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y)
    (E : ExtTensor t ht X Y) (S : Ba 𝒜 X) (T : Ba ℬ Y) :
    ∃! R : Ba 𝒞 E.Z,
      ∀ (x : X) (y : Y), R.1 (E.η x y) = E.η (S.1 x) (T.1 y) := by
  -- **165IV**: `Θ(x,y) = (Sx) ⊗ (Ty)` is `𝒜 ⊙ ℬ`-bilinear, and bounded by
  -- `‖S‖‖T‖` (`tensor_gram_bound`), so it factors uniquely through `η` by
  -- the universal property **164II**.  The factorisation is *adjointable*
  -- because the same construction applied to `(S*, T*)` produces its
  -- adjoint — this replaces the thesis's tacit "`S ⊗ T ∈ 𝒞ᵃ(X ⊗ Y)`".
  have hmk : ∀ (S₀ : Ba 𝒜 X) (T₀ : Ba ℬ Y), ∃ (C : ℝ) (F : E.Z → E.Z),
      IsBoundedModuleMap (cstarBInner 𝒞 E.Z) (cstarBInner 𝒞 E.Z) C F ∧
        ∀ (x : X) (y : Y), F (E.η x y) = E.η (S₀.1 x) (T₀.1 y) := by
    intro S₀ T₀
    obtain ⟨-, -, hSm⟩ := moduleAdjointable_linear (𝒜 := 𝒜) ⇑S₀.1 S₀.2
    obtain ⟨-, -, hTm⟩ := moduleAdjointable_linear (𝒜 := ℬ) ⇑T₀.1 T₀.2
    have hbound : ∃ C : ℝ, ∀ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
        ‖∑ i, E.η (S₀.1 (x i)) (T₀.1 (y i))‖ ^ 2 ≤
          C * ‖∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))‖ := by
      refine ⟨‖S₀‖ ^ 2 * ‖T₀‖ ^ 2, fun n x y => ?_⟩
      rw [extTensor_gram E n (fun i => S₀.1 (x i)) fun i => T₀.1 (y i)]
      exact tensor_gram_bound ht S₀ T₀ x y
    obtain ⟨F, ⟨⟨C, hC⟩, hFη⟩, -⟩ := E.univ E.Z inferInstance inferInstance
      inferInstance inferInstance inferInstance E.selfDual
      (fun x y => E.η (S₀.1 x) (T₀.1 y))
      (fun x x' y => by rw [map_add, E.η_add_left])
      (fun x y y' => by rw [map_add, E.η_add_right])
      (fun a b x y => by rw [hSm, hTm, E.η_smul]) hbound
    exact ⟨C, F, hC, hFη⟩
  obtain ⟨CF, F, hCF, hFη⟩ := hmk S T
  obtain ⟨CG, G, hCG, hGη⟩ := hmk (star S) (star T)
  have hSadj : ModuleAdjointTo 𝒜 (⇑S.1 : X → X) ⇑((star S : Ba 𝒜 X)).1 :=
    baSubalgebra_star_spec S
  have hTadj : ModuleAdjointTo ℬ (⇑T.1 : Y → Y) ⇑((star T : Ba ℬ Y)).1 :=
    baSubalgebra_star_spec T
  -- `G` is an adjoint of `F`: check it against the elementary tensors in
  -- each argument separately (`extTensor_inner_diff_ext`, twice).
  have hstep1 : ∀ (x : X) (y : Y) (z : E.Z),
      (inner 𝒞 (E.η x y) (G z) : 𝒞) = inner 𝒞 (E.η (S.1 x) (T.1 y)) z := by
    intro x y
    refine extTensor_inner_diff_ext E G CG hCG _ _ fun x' y' => ?_
    rw [hGη, E.η_inner, E.η_inner, hSadj x x', hTadj y y']
  have hadj : ModuleAdjointTo 𝒞 F G := by
    intro z z'
    have h := extTensor_inner_diff_ext E F CF hCF z' (G z')
      (fun x y => by
        rw [hFη, ← CStarModule.star_inner (E.η x y) (G z'), hstep1 x y z',
          CStarModule.star_inner]) z
    rw [← CStarModule.star_inner z' (F z), ← CStarModule.star_inner (G z') z, h]
  have hFnorm : ∀ z : E.Z, ‖F z‖ ≤ CF * ‖z‖ := fun z => by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) (F z),
      CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) z]
    exact hCF.bound z
  refine ⟨⟨LinearMap.mkContinuous
      { toFun := F
        map_add' := hCF.add
        map_smul' := fun c z => hCF.smul_complex c z } CF hFnorm,
    ⟨G, hadj⟩⟩, fun x y => hFη x y, ?_⟩
  -- uniqueness: two elements of `𝒞ᵃ(X ⊗ Y)` agreeing on the elementary
  -- tensors are equal (the uniqueness half of **164II**)
  rintro R' hR'
  obtain ⟨C', hC'⟩ : ∃ C : ℝ, IsBoundedModuleMap (cstarBInner 𝒞 E.Z)
      (cstarBInner 𝒞 E.Z) C ⇑R'.1 := by
    obtain ⟨-, -, hRm⟩ := moduleAdjointable_linear (𝒜 := 𝒞) ⇑R'.1 R'.2
    refine ⟨‖R'.1‖, ⟨fun a b => map_add _ a b, fun c a => map_smul _ c a,
      hRm, fun z => ?_⟩⟩
    change Real.sqrt ‖(inner 𝒞 (R'.1 z) (R'.1 z) : 𝒞)‖
      ≤ ‖R'.1‖ * Real.sqrt ‖(inner 𝒞 z z : 𝒞)‖
    rw [← CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞),
      ← CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞)]
    exact R'.1.le_opNorm z
  exact Subtype.ext (DFunLike.coe_injective
    (extTensor_map_ext E E.selfDual C' CF _ _ hC' hCF fun x y => by
      rw [hR' x y]; exact (hFη x y).symm))

/-- **165V** (`hilbmod-tensor-ketbra`, dils.tex:5506, Exercise): the rules
for `⊗` of module operators: (1) `|x₁⟩⟨x₂| ⊗ |y₁⟩⟨y₂| = |x₁⊗y₁⟩⟨x₂⊗y₂|`;
(2) `1 ⊗ 1 = 1`; (3) `(S ⊗ T)(S' ⊗ T') = SS' ⊗ TT'`;
(4) `(S ⊗ T)* = S* ⊗ T*`.  (Stated for operators characterized by their
values on elementary tensors, as in **165III**.) -/
theorem hilbmod_tensor_ketbra [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    (S S' : Ba 𝒜 X) (T T' : Ba ℬ Y) (R R' R'' : Ba 𝒞 E.Z)
    (hR : ∀ x y, R.1 (E.η x y) = E.η (S.1 x) (T.1 y))
    (hR' : ∀ x y, R'.1 (E.η x y) = E.η (S'.1 x) (T'.1 y))
    (hR'' : ∀ x y, R''.1 (E.η x y) = E.η ((S * S').1 x) ((T * T').1 y)) :
    (∀ (x₁ x₂ : X) (y₁ y₂ : Y),
      (∀ x y, R.1 (E.η x y) =
          E.η ((mketbra 𝒜 x₁ x₂ : X →L[ℂ] X) x) ((mketbra ℬ y₁ y₂) y)) →
        R.1 = mketbra 𝒞 (E.η x₁ y₁) (E.η x₂ y₂)) ∧
    ((∀ x y, R.1 (E.η x y) = E.η x y) → R = 1) ∧
    R * R' = R'' ∧
    (∀ x y, (star R).1 (E.η x y) = E.η ((star S).1 x) ((star T).1 y)) := by
  -- `bsols.tex`, solution `hilbmod-tensor-ketbra`.  Of the two routes the
  -- author offers ("either by appealing to the defining universal property
  -- of `X ⊗ Y` or by … ultranorm density") we take the first, since the
  -- density statement **164II**.1 (`ext_tensor_dense`) is still `sorry`.
  -- Every `R ∈ 𝒞ᵃ(X ⊗ Y)` is a bounded module map.
  have hbdd : ∀ R₀ : Ba 𝒞 E.Z, ∃ C : ℝ,
      IsBoundedModuleMap (cstarBInner 𝒞 E.Z) (cstarBInner 𝒞 E.Z) C ⇑R₀.1 := by
    intro R₀
    obtain ⟨-, -, hRm⟩ := moduleAdjointable_linear (𝒜 := 𝒞) ⇑R₀.1 R₀.2
    refine ⟨‖R₀.1‖, ⟨fun x y => map_add _ x y, fun c x => map_smul _ c x,
      hRm, fun x => ?_⟩⟩
    change Real.sqrt ‖(inner 𝒞 (R₀.1 x) (R₀.1 x) : 𝒞)‖
      ≤ ‖R₀.1‖ * Real.sqrt ‖(inner 𝒞 x x : 𝒞)‖
    rw [← CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞),
      ← CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞)]
    exact R₀.1.le_opNorm x
  -- "This is sufficient to show …": operators agreeing on the elementary
  -- tensors agree, by the uniqueness half of the universal property.
  have hunique : ∀ R₁ R₂ : Ba 𝒞 E.Z,
      (∀ (x : X) (y : Y), R₁.1 (E.η x y) = R₂.1 (E.η x y)) → R₁ = R₂ := by
    intro R₁ R₂ hagree
    obtain ⟨C₁, hC₁⟩ := hbdd R₁
    obtain ⟨C₂, hC₂⟩ := hbdd R₂
    exact Subtype.ext (DFunLike.coe_injective
      (extTensor_map_ext E E.selfDual C₁ C₂ _ _ hC₁ hC₂ hagree))
  -- vector separation: a vector orthogonal to every elementary tensor is `0`
  have hsep : ∀ w : E.Z, (∀ (x : X) (y : Y), (inner 𝒞 (E.η x y) w : 𝒞) = 0) →
      w = 0 := extTensor_sep E
  refine ⟨?_, ?_, ?_, ?_⟩
  -- (1) `|x₁⟩⟨x₂| ⊗ |y₁⟩⟨y₂| = |x₁⊗y₁⟩⟨x₂⊗y₂|`
  · intro x₁ x₂ y₁ y₂ hRk
    have hK : ModuleAdjointable 𝒞 ⇑(mketbra 𝒞 (E.η x₁ y₁) (E.η x₂ y₂)) :=
      ⟨_, mketbra_adjointable 𝒞 _ _⟩
    have := hunique R ⟨mketbra 𝒞 (E.η x₁ y₁) (E.η x₂ y₂), hK⟩ fun x y => by
      rw [hRk x y]
      show E.η ((inner 𝒜 x₂ x : 𝒜) • x₁) ((inner ℬ y₂ y : ℬ) • y₁)
        = (inner 𝒞 (E.η x₂ y₂) (E.η x y) : 𝒞) • E.η x₁ y₁
      rw [E.η_smul, E.η_inner]
    rw [this]
  -- (2) `1 ⊗ 1 = 1`
  · intro h1
    exact hunique R 1 fun x y => h1 x y
  -- (3) `(S ⊗ T)(S' ⊗ T') = SS' ⊗ TT'`
  · refine hunique _ _ fun x y => ?_
    show R.1 (R'.1 (E.η x y)) = _
    rw [hR' x y, hR (S'.1 x) (T'.1 y), hR'' x y]
    rfl
  -- (4) `(S ⊗ T)* = S* ⊗ T*`
  · intro x y
    have hRadj : ModuleAdjointTo 𝒞 (⇑R.1 : E.Z → E.Z)
      ⇑((star R : Ba 𝒞 E.Z)).1 := baSubalgebra_star_spec R
    have hSadj : ModuleAdjointTo 𝒜 (⇑S.1 : X → X)
      ⇑((star S : Ba 𝒜 X)).1 := baSubalgebra_star_spec S
    have hTadj : ModuleAdjointTo ℬ (⇑T.1 : Y → Y)
      ⇑((star T : Ba ℬ Y)).1 := baSubalgebra_star_spec T
    refine sub_eq_zero.mp (hsep _ fun x' y' => ?_)
    rw [CStarModule.inner_sub_right, ← hRadj (E.η x' y') (E.η x y), hR x' y',
      E.η_inner, E.η_inner, hSadj x' x, hTadj y' y, sub_self]

/-- **165VI** (`ba-ext-tensor-pres`, dils.tex:5531, Theorem): there is an
nmiu-isomorphism `𝒜ᵃ(X) ⊗ ℬᵃ(Y) ≅ 𝒞ᵃ(X ⊗ Y)` sending `S ⊗ T` to
`S ⊗ T`; stated as: the bilinear map `Θ(S,T) = S ⊗ T` exhibits
`𝒞ᵃ(X ⊗ Y)` as the von Neumann tensor product of `𝒜ᵃ(X)` and `ℬᵃ(Y)`.

**165VII**–**165X** are the proof — not converted. -/
theorem ba_ext_tensor_pres [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    (Θ : Ba 𝒜 X → Ba ℬ Y → Ba 𝒞 E.Z)
    (hΘ : ∀ (S : Ba 𝒜 X) (T : Ba ℬ Y) (x : X) (y : Y),
      (Θ S T).1 (E.η x y) = E.η (S.1 x) (T.1 y)) :
    IsVNTensor Θ :=
  sorry

/-! ## Parsec 1660: ultranorm continuity of the exterior tensor product

**166I** (dils.tex:5625): introduction; **166III**, **166V**, **166VII**
are proofs — not converted.

The two estimates of **166III** (`unSeminorm_eta_le_left/_right`) live in
`section EtaEstimates` above, since **164II**.2a already needs them. -/

-- `hX`, `hY` are not used: `E : ExtTensor t ht X Y` already carries
-- self-duality of `X ⊗ Y` and `η_inner`, which is all the proof needs; they
-- are kept for uniformity with the neighbouring statements of parsecs
-- 1640-1670.  **`hxb` is not used either**: the splitting
-- `xα ⊗ yα − x ⊗ y = (xα − x) ⊗ yα + x ⊗ (yα − y)` needs a norm bound on
-- the `y`-net only.  (The thesis needs both because it routes the estimate
-- through **44III** `vanishing-effects`, whose vanishing net must consist of
-- *effects*; the estimate below never leaves the order of `𝒞`.  Splitting
-- the other way, `xα ⊗ (yα − y) + (xα − x) ⊗ y`, would use `hxb` and not
-- `hyb`, so the lemma is true with either one of the two bounds.)
set_option linter.unusedVariables false in
/-- **166II** (`ultranorm-continuity-ext-tensor`, dils.tex:5630, Lemma): if
`x_α → x` and `y_α → y` ultranorm for norm-bounded nets, then
`x_α ⊗ y_α → x ⊗ y` ultranorm.

**166III** is the proof; transcribed below, with its appeal to **44III**
`vanishing_effects` replaced by the order estimate
`Ω(⟨d,d⟩ ⊗ ⟨yα,yα⟩) ≤ M² · Ω(⟨d,d⟩ ⊗ 1)` — which is available because the
legs are normal (`vnTensor_legLeft_normal`), so `Ω(· ⊗ 1)` is again an
np-functional. -/
theorem ultranorm_continuity_ext_tensor [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] [VonNeumannAlgebra 𝒞] [CompleteSpace X]
    [CompleteSpace Y] (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y)
    (E : ExtTensor t ht X Y) {ι : Type u} {l : Filter ι}
    (x : ι → X) (x₀ : X) (y : ι → Y) (y₀ : Y)
    (hxb : ∃ M : ℝ, ∀ i, ‖x i‖ ≤ M) (hyb : ∃ M : ℝ, ∀ i, ‖y i‖ ≤ M)
    (hx : UnTendsto (inner 𝒜) x l x₀) (hy : UnTendsto (inner ℬ) y l y₀) :
    UnTendsto (inner 𝒞) (fun i => E.η (x i) (y i)) l (E.η x₀ y₀) := by
  intro Ω
  obtain ⟨ω, hωa⟩ : ∃ ω : NPFunctional 𝒜, ∀ a : 𝒜, ω a = Ω (t a 1) :=
    ⟨vnTensorLegLeftNP ht Ω, fun _ => rfl⟩
  obtain ⟨ξ, hξb⟩ : ∃ ξ : NPFunctional ℬ, ∀ b : ℬ, ξ b = Ω (t 1 b) :=
    ⟨vnTensorLegRightNP ht Ω, fun _ => rfl⟩
  obtain ⟨M₀, hM₀⟩ := hyb
  obtain ⟨M, hM0, hMy⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ‖y i‖ ≤ M :=
    ⟨max M₀ 0, le_max_right _ _, fun i => (hM₀ i).trans (le_max_left _ _)⟩
  -- `xα ⊗ yα − x ⊗ y = (xα − x) ⊗ yα + x ⊗ (yα − y)`
  have hsplit : ∀ i, E.η (x i) (y i) - E.η x₀ y₀
      = E.η (x i - x₀) (y i) + E.η x₀ (y i - y₀) := by
    intro i
    have h1 : E.η (x i - x₀) (y i) + E.η x₀ (y i) = E.η (x i) (y i) := by
      rw [← E.η_add_left]; congr 1; abel
    have h2 : E.η x₀ (y i - y₀) + E.η x₀ y₀ = E.η x₀ (y i) := by
      rw [← E.η_add_right]; congr 1; abel
    rw [← h1, ← h2]; abel
  -- `‖(xα − x) ⊗ yα‖_Ω ≤ M ‖xα − x‖_{Ω(· ⊗ 1)}`
  have hterm1 : ∀ i, unSeminorm Ω (inner 𝒞) (E.η (x i - x₀) (y i))
      ≤ M * unSeminorm ω (inner 𝒜) (x i - x₀) := by
    intro i
    have hy2 : ‖(inner ℬ (y i) (y i) : ℬ)‖ ≤ M ^ 2 := by
      have hn : ‖(inner ℬ (y i) (y i) : ℬ)‖ = ‖y i‖ ^ 2 := by
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ) (y i),
          Real.sq_sqrt (norm_nonneg _)]
      have h1 := hMy i
      have h2 := norm_nonneg (y i)
      rw [hn]; nlinarith
    have hmono : t (inner 𝒜 (x i - x₀) (x i - x₀)) (inner ℬ (y i) (y i))
        ≤ t (inner 𝒜 (x i - x₀) (x i - x₀)) (((M ^ 2 : ℝ) : ℂ) • (1 : ℬ)) :=
      vnTensor_mono_right ht CStarModule.inner_self_nonneg
        (le_ofReal_smul_one CStarModule.inner_self_nonneg hy2)
    have hre : (Ω (inner 𝒞 (E.η (x i - x₀) (y i)) (E.η (x i - x₀) (y i)))).re
        ≤ M ^ 2 * (ω (inner 𝒜 (x i - x₀) (x i - x₀))).re := by
      rw [E.η_inner, hωa]
      have h2 := npFunctional_mono Ω hmono
      rw [vnTensor_smul_complex_right ht, npf_csmul] at h2
      simpa [Complex.mul_re, ← Complex.ofReal_pow] using
        (Complex.le_def.mp h2).1
    calc unSeminorm Ω (inner 𝒞) (E.η (x i - x₀) (y i))
        ≤ Real.sqrt (M ^ 2 * (ω (inner 𝒜 (x i - x₀) (x i - x₀))).re) :=
          Real.sqrt_le_sqrt hre
      _ = M * unSeminorm ω (inner 𝒜) (x i - x₀) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM0]; rfl
  -- `‖x ⊗ (yα − y)‖_Ω ≤ ‖x‖ ‖yα − y‖_{Ω(1 ⊗ ·)}`
  have hterm2 : ∀ i, unSeminorm Ω (inner 𝒞) (E.η x₀ (y i - y₀))
      ≤ ‖x₀‖ * unSeminorm ξ (inner ℬ) (y i - y₀) := by
    intro i
    have hx2 : ‖(inner 𝒜 x₀ x₀ : 𝒜)‖ ≤ ‖x₀‖ ^ 2 := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒜) x₀,
        Real.sq_sqrt (norm_nonneg _)]
    have hmono : t (inner 𝒜 x₀ x₀) (inner ℬ (y i - y₀) (y i - y₀))
        ≤ t (((‖x₀‖ ^ 2 : ℝ) : ℂ) • (1 : 𝒜)) (inner ℬ (y i - y₀) (y i - y₀)) :=
      vnTensor_mono_left ht CStarModule.inner_self_nonneg
        (le_ofReal_smul_one CStarModule.inner_self_nonneg hx2)
    have hre : (Ω (inner 𝒞 (E.η x₀ (y i - y₀)) (E.η x₀ (y i - y₀)))).re
        ≤ ‖x₀‖ ^ 2 * (ξ (inner ℬ (y i - y₀) (y i - y₀))).re := by
      rw [E.η_inner, hξb]
      have h2 := npFunctional_mono Ω hmono
      rw [ht.smul_complex, npf_csmul] at h2
      simpa [Complex.mul_re, ← Complex.ofReal_pow] using
        (Complex.le_def.mp h2).1
    calc unSeminorm Ω (inner 𝒞) (E.η x₀ (y i - y₀))
        ≤ Real.sqrt (‖x₀‖ ^ 2 * (ξ (inner ℬ (y i - y₀) (y i - y₀))).re) :=
          Real.sqrt_le_sqrt hre
      _ = ‖x₀‖ * unSeminorm ξ (inner ℬ) (y i - y₀) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]; rfl
  refine squeeze_zero (fun i => unSeminorm_nonneg _ _ _) (g := fun i =>
      M * unSeminorm ω (inner 𝒜) (x i - x₀)
        + ‖x₀‖ * unSeminorm ξ (inner ℬ) (y i - y₀)) (fun i => ?_) ?_
  · change unSeminorm Ω (inner 𝒞) (E.η (x i) (y i) - E.η x₀ y₀) ≤ _
    rw [hsplit i]
    exact (unSeminorm_add_le Ω (cstarBInner 𝒞 E.Z) _ _).trans
      (add_le_add (hterm1 i) (hterm2 i))
  · simpa using ((hx ω).const_mul M).add ((hy ξ).const_mul ‖x₀‖)

-- `hUsub`, `hUsmul`, `hVsub`, `hVsmul` are not used: the proof below picks
-- `u` and `v` one after the other rather than through a *net*, so it never
-- needs `U`, `V` to be submodules (see the divergence in the doc comment).
set_option linter.unusedVariables false in
/-- **166IV** (`exttensor-dense-subsets`, dils.tex:5669, Lemma): for
ultranorm-dense submodules `U ⊆ X` and `V ⊆ Y`, the linear span of
`U ⊗ V = {u ⊗ v}` is ultranorm dense in `X ⊗ Y`.

**Divergence, class 2, and it removes a dependency on a `sorry`.**  The
thesis's proof (166V) obtains *norm-bounded* nets `u_α → x`, `v_α → y` from
the Kaplansky density theorem for Hilbert C*-modules **158II**
(`kaplansky_hilbmod`) and then applies **166II**.  158II is open — its
printed proof is false, see `Kaplansky.lean` — so that route is unavailable.
It is also unnecessary: the ultranorm uniformity is approximated one
entourage at a time, so `u ∈ U` may be chosen *first* and `v ∈ V` afterwards,
with an accuracy depending on the `‖u‖` already fixed.  No norm bound, and
hence no Kaplansky density, is needed.  The two estimates are those of
**166III** (`unSeminorm_eta_le_left/_right`). -/
theorem exttensor_dense_subsets [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    (U : Set X) (V : Set Y)
    (hU : UnDense (inner 𝒜) U) (hV : UnDense (inner ℬ) V)
    (hUsub : ∀ u ∈ U, ∀ u' ∈ U, u + u' ∈ U)
    (hUsmul : ∀ (a : 𝒜), ∀ u ∈ U, a • u ∈ U)
    (hVsub : ∀ v ∈ V, ∀ v' ∈ V, v + v' ∈ V)
    (hVsmul : ∀ (b : ℬ), ∀ v ∈ V, b • v ∈ V) :
    UnDense (inner 𝒞)
      {z : E.Z | ∃ (n : ℕ) (u : Fin n → X) (v : Fin n → Y),
        (∀ i, u i ∈ U) ∧ (∀ i, v i ∈ V) ∧ z = ∑ i, E.η (u i) (v i)} := by
  classical
  set D' : Set E.Z := {z : E.Z | ∃ (n : ℕ) (u : Fin n → X) (v : Fin n → Y),
    (∀ i, u i ∈ U) ∧ (∀ i, v i ∈ V) ∧ z = ∑ i, E.η (u i) (v i)} with hD'def
  have hD'0 : (0 : E.Z) ∈ D' :=
    ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩
  have hD'add : ∀ z ∈ D', ∀ z' ∈ D', z + z' ∈ D' := by
    rintro _ ⟨n, u, v, hu, hv, rfl⟩ _ ⟨m, u', v', hu', hv', rfl⟩
    refine ⟨n + m, Fin.append u u', Fin.append v v', ?_, ?_, ?_⟩
    · exact fun i => Fin.addCases (fun j => by rw [Fin.append_left]; exact hu j)
        (fun j => by rw [Fin.append_right]; exact hu' j) i
    · exact fun i => Fin.addCases (fun j => by rw [Fin.append_left]; exact hv j)
        (fun j => by rw [Fin.append_right]; exact hv' j) i
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  -- every *elementary* tensor is an ultranorm limit of elements of `U ⊗ V`
  have helem : ∀ (x : X) (y : Y), E.η x y ∈ unClosure 𝒞 (inner 𝒞) D' := by
    intro x y n Ωs ε hε
    obtain ⟨u, huU, hu⟩ := hU x n (fun i => vnTensorLegLeftNP ht (Ωs i))
      (ε / (2 * (‖y‖ + 1))) (by positivity)
    obtain ⟨v, hvV, hv⟩ := hV y n (fun i => vnTensorLegRightNP ht (Ωs i))
      (ε / (2 * (‖u‖ + 1))) (by positivity)
    refine ⟨E.η u v, ⟨1, fun _ => u, fun _ => v, fun _ => huU, fun _ => hvV, by simp⟩,
      fun i => ?_⟩
    have hsplit : E.η x y - E.η u v = E.η (x - u) y + E.η u (y - v) := by
      have h1 : E.η (x - u) y + E.η u y = E.η x y := by
        rw [← E.η_add_left]; congr 1; abel
      have h2 : E.η u (y - v) + E.η u v = E.η u y := by
        rw [← E.η_add_right]; congr 1; abel
      rw [← h1, ← h2]; abel
    have hb1 : ‖y‖ * unSeminorm (vnTensorLegLeftNP ht (Ωs i)) (inner 𝒜) (x - u)
        ≤ ε / 2 := by
      have h := mul_le_mul_of_nonneg_left (hu i) (norm_nonneg y)
      refine h.trans ?_
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [norm_nonneg y, hε.le]
    have hb2 : ‖u‖ * unSeminorm (vnTensorLegRightNP ht (Ωs i)) (inner ℬ) (y - v)
        ≤ ε / 2 := by
      have h := mul_le_mul_of_nonneg_left (hv i) (norm_nonneg u)
      refine h.trans ?_
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [norm_nonneg u, hε.le]
    calc unSeminorm (Ωs i) (inner 𝒞 : E.Z → E.Z → 𝒞) (E.η x y - E.η u v)
        = unSeminorm (Ωs i) (inner 𝒞 : E.Z → E.Z → 𝒞)
            (E.η (x - u) y + E.η u (y - v)) := by rw [hsplit]
      _ ≤ unSeminorm (Ωs i) (inner 𝒞 : E.Z → E.Z → 𝒞) (E.η (x - u) y)
            + unSeminorm (Ωs i) (inner 𝒞 : E.Z → E.Z → 𝒞) (E.η u (y - v)) :=
          unSeminorm_add_le _ (cstarBInner 𝒞 E.Z) _ _
      _ ≤ ‖y‖ * unSeminorm (vnTensorLegLeftNP ht (Ωs i)) (inner 𝒜) (x - u)
            + ‖u‖ * unSeminorm (vnTensorLegRightNP ht (Ωs i)) (inner ℬ) (y - v) :=
          add_le_add (unSeminorm_eta_le_left E _ _ _)
            (unSeminorm_eta_le_right E _ _ _)
      _ ≤ ε / 2 + ε / 2 := add_le_add hb1 hb2
      _ = ε := by ring
  -- hence so is every finite sum of elementary tensors, and those are dense
  have hDsub : {z : E.Z | ∃ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
      z = ∑ i, E.η (x i) (y i)} ⊆ unClosure 𝒞 (inner 𝒞) D' := by
    rintro _ ⟨n, x, y, rfl⟩
    exact Finset.sum_induction _ (fun w => w ∈ unClosure 𝒞 (inner 𝒞) D')
      (fun w w' hw hw' => unClosure_add hD'add hw hw') (subset_unClosure _ hD'0)
      fun i _ => helem (x i) (y i)
  intro z n Ωs ε hε
  have hz : z ∈ unClosure 𝒞 (inner 𝒞) D' := by
    rw [← unClosure_unClosure D']
    exact unClosure_mono hDsub (ext_tensor_dense hX hY E z)
  exact hz n Ωs ε hε

end ExtTensor

section DilationSpaceDense

variable {𝒜 ℬ : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]

/-- `x ↦ ω(b φ(x) b*)` is again an np-functional: this is `conjNP` followed by
`compNP`, and it is normality of `φ` (`NCPMap.preservesDirSups'`) that makes it
one.  (Auxiliary for **166VI**.) -/
private theorem ncpPreservesDirSups (φ : NCPMap 𝒜 ℬ) :
    PreservesDirSups ⇑(ncpPositive φ) := φ.preservesDirSups'

private theorem exists_conj_comp_np (φ : NCPMap 𝒜 ℬ) (ω : NPFunctional ℬ)
    (b : ℬ) : ∃ ν : NPFunctional 𝒜, ∀ x : 𝒜, ν x = ω (b * φ x * star b) :=
  ⟨compNP (ncpPositive φ) (ncpPreservesDirSups φ) (conjNP (star b) ω),
    fun x => by rw [compNP_apply, conjNP_apply, star_star]; rfl⟩

/-- `‖d ⊗ b‖_ω = ‖d‖_{ω(b φ(·) b*)}`: the ultranorm seminorms of the
elementary tensors of `𝒜 ⊗_φ ℬ` are, in the `𝒜`-variable, exactly the
mirrored ultrastrong seminorms of `𝒜`.  (Auxiliary for **166VI**.) -/
private theorem unSeminorm_tprod_left (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (ω : NPFunctional ℬ) (ν : NPFunctional 𝒜) (b : ℬ)
    (hν : ∀ x : 𝒜, ν x = ω (b * φ x * star b)) (d : 𝒜) :
    unSeminorm ω (inner ℬ) (M.tprod d b) = unSeminorm ν (mulInner 𝒜) d := by
  rw [unSeminorm, unSeminorm, M.inner_tprod, hν]
  rfl

/-- `‖a ⊗ e‖_ω ≤ ‖φ(a a*)‖^½ · ‖e‖_ω`: in the `ℬ`-variable the elementary
tensors are dominated by the mirrored ultrastrong seminorms of `ℬ`, with a
constant depending on `a` only.  (Auxiliary for **166VI**.) -/
private theorem unSeminorm_tprod_right (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (ω : NPFunctional ℬ) (a : 𝒜) (e : ℬ) :
    unSeminorm ω (inner ℬ) (M.tprod a e)
      ≤ Real.sqrt ‖φ (a * star a)‖ * unSeminorm ω (mulInner ℬ) e := by
  have hnn : (0 : ℬ) ≤ φ (a * star a) := by
    have hz : (φ 0 : ℬ) = 0 := map_zero φ.toCompletelyPositiveMap
    have h : (φ 0 : ℬ) ≤ φ (a * star a) :=
      (ncpPositive φ).monotone (mul_star_self_nonneg a)
    rwa [hz] at h
  have hle : e * φ (a * star a) * star e ≤ ‖φ (a * star a)‖ • (e * star e) :=
    CStarAlgebra.star_right_conjugate_le_norm_smul (IsSelfAdjoint.of_nonneg hnn)
  have hsmul : ((‖φ (a * star a)‖ : ℝ) • (e * star e) : ℬ)
      = ((‖φ (a * star a)‖ : ℝ) : ℂ) • (e * star e) := by
    rw [← Complex.coe_algebraMap, algebraMap_smul]
  have hre : (ω (e * φ (a * star a) * star e)).re
      ≤ ‖φ (a * star a)‖ * (ω (e * star e)).re := by
    have h1 := np_re_mono' ω hle
    rwa [hsmul, npf_csmul, Complex.re_ofReal_mul] at h1
  rw [unSeminorm, unSeminorm, M.inner_tprod]
  calc Real.sqrt (ω (e * φ (a * star a) * star e)).re
      ≤ Real.sqrt (‖φ (a * star a)‖ * (ω (e * star e)).re) := Real.sqrt_le_sqrt hre
    _ = Real.sqrt ‖φ (a * star a)‖ * Real.sqrt ((ω (e * star e)).re) := by
        rw [Real.sqrt_mul (norm_nonneg _)]
    _ = Real.sqrt ‖φ (a * star a)‖ * unSeminorm ω (mulInner ℬ) e := rfl

/-- **The elementary tensors of `𝒜 ⊗_φ ℬ` are ultranorm dense.**  This is
the Paschke-module analogue of `selfdual_compl_defining_dense` (**163II**)
and of `ext_tensor_dense` (**164II**.1), and it is the easiest of the three:
the set `D` of finite sums `∑ᵢ aᵢ ⊗ bᵢ` is *already* a ℬ-submodule
(`PhiCompatible.smul_action`, `c·(a ⊗ b) = a ⊗ (cb)`), so `bSpan D = D` and
**160IV**.2 identifies `D^⊥⊥` with the ultranorm closure of `D` outright.
The projection onto `D^⊥⊥` fixes every elementary tensor, hence equals `id`
by the uniqueness half of the universal property of `𝒜 ⊗_φ ℬ`
(**154III**.1), so `D^⊥⊥` is everything.  The thesis states this only
implicitly, in the "by construction" of **151V**/**164VII**. -/
theorem paschke_tprod_dense (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ) :
    UnDense (inner ℬ)
      {z : M.X | ∃ (n : ℕ) (a : Fin n → 𝒜) (b : Fin n → ℬ),
        z = ∑ i, M.tprod (a i) (b i)} := by
  classical
  set D : Set M.X := {z : M.X | ∃ (n : ℕ) (a : Fin n → 𝒜) (b : Fin n → ℬ),
    z = ∑ i, M.tprod (a i) (b i)} with hDdef
  have hD0 : (0 : M.X) ∈ D := ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  have hDadd : ∀ z ∈ D, ∀ z' ∈ D, z + z' ∈ D := by
    rintro _ ⟨n, a, b, rfl⟩ _ ⟨m, a', b', rfl⟩
    refine ⟨n + m, Fin.append a a', Fin.append b b', ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  have hDb : ∀ c : ℬ, ∀ z ∈ D, c • z ∈ D := by
    rintro c _ ⟨n, a, b, rfl⟩
    refine ⟨n, a, fun i => c * b i, ?_⟩
    rw [op_smul_sum]
    exact Finset.sum_congr rfl fun i _ => M.compat.smul_action (a i) (b i) c
  have hDc : ∀ c : ℂ, ∀ z ∈ D, c • z ∈ D := by
    rintro c _ ⟨n, a, b, rfl⟩
    refine ⟨n, fun i => c • a i, b, ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => (M.compat.smul_complex c (a i) (b i)).symm
  have hspan : bSpan ℬ D = D := by
    refine Set.eq_of_subset_of_subset ?_ (subset_bSpan _)
    rintro _ ⟨n, c, b, v, hv, rfl⟩
    exact Finset.sum_induction _ (fun w => w ∈ D)
      (fun w w' hw hw' => hDadd w hw w' hw') hD0
      fun i _ => hDc (c i) _ (hDb (b i) _ (hv i))
  obtain ⟨hW0, hWadd, hWb, hWc, hWcl⟩ := hilbmod_projthm_1 M.selfDual (orthoCompl ℬ D)
  obtain ⟨P, hPbdd, hPW, hPfix⟩ :=
    exists_orthoProj M.selfDual (orthoCompl ℬ (orthoCompl ℬ D)) hW0 hWadd hWb hWc hWcl
  obtain ⟨T', -, hT'uniq⟩ := M.univ M.X inferInstance inferInstance inferInstance
    inferInstance inferInstance M.selfDual M.tprod M.compat
  have hPid : P = id := by
    have h1 : P = T' := hT'uniq P ⟨⟨1, hPbdd⟩, fun a b =>
      hPfix (M.tprod a b) (subset_biorthoCompl _
        ⟨1, fun _ => a, fun _ => b, by simp⟩)⟩
    have h2 : id = T' := hT'uniq id
      ⟨⟨1, ⟨fun x y => rfl, fun c x => rfl, fun b x => rfl,
        fun x => le_of_eq (one_mul _).symm⟩⟩, fun a b => rfl⟩
    exact h1.trans h2.symm
  intro z n ωs ε hε
  have hzW : z ∈ orthoCompl ℬ (orthoCompl ℬ D) := by
    have h := hPW z
    rwa [hPid] at h
  rw [hilbmod_projthm_2 M.selfDual D, hspan] at hzW
  exact hzW n ωs ε hε

end DilationSpaceDense

/-- **166VI** (`dilationspace-dense-subset`, dils.tex:5695, Lemma): for an
ncp-map `φ : 𝒜 → ℬ` between von Neumann algebras with ultrastrongly dense
∗-subalgebras `𝒜' ⊆ 𝒜`, `ℬ' ⊆ ℬ`, the linear span of
`{a ⊗ b : a ∈ 𝒜', b ∈ ℬ'}` is ultranorm dense in `𝒜 ⊗_φ ℬ`. -/
theorem dilationspace_dense_subset {𝒜 ℬ : Type u}
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (A' : StarSubalgebra ℂ 𝒜) (B' : StarSubalgebra ℂ ℬ)
    (hA : UnDense (mulInner 𝒜) (A' : Set 𝒜))
    (hB : UnDense (mulInner ℬ) (B' : Set ℬ)) :
    UnDense (inner ℬ)
      {z : M.X | ∃ (n : ℕ) (a : Fin n → 𝒜) (b : Fin n → ℬ),
        (∀ i, a i ∈ A') ∧ (∀ i, b i ∈ B') ∧
        z = ∑ i, M.tprod (a i) (b i)} := by
  classical
  set T : Set M.X := {z : M.X | ∃ (n : ℕ) (a : Fin n → 𝒜) (b : Fin n → ℬ),
    (∀ i, a i ∈ A') ∧ (∀ i, b i ∈ B') ∧ z = ∑ i, M.tprod (a i) (b i)} with hTdef
  have hT0 : (0 : M.X) ∈ T :=
    ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩
  have hTadd : ∀ z ∈ T, ∀ z' ∈ T, z + z' ∈ T := by
    rintro _ ⟨n, a, b, ha, hb, rfl⟩ _ ⟨m, a', b', ha', hb', rfl⟩
    refine ⟨n + m, Fin.append a a', Fin.append b b', ?_, ?_, ?_⟩
    · exact fun i => Fin.addCases (fun j => by rw [Fin.append_left]; exact ha j)
        (fun j => by rw [Fin.append_right]; exact ha' j) i
    · exact fun i => Fin.addCases (fun j => by rw [Fin.append_left]; exact hb j)
        (fun j => by rw [Fin.append_right]; exact hb' j) i
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  -- every elementary tensor is an ultranorm limit of elements of `𝒯`
  have helem : ∀ (a : 𝒜) (b : ℬ), M.tprod a b ∈ unClosure ℬ (inner ℬ) T := by
    intro a b n ωs ε hε
    choose ν hν using fun i : Fin n => exists_conj_comp_np φ (ωs i) b
    obtain ⟨a', ha'A, ha'⟩ := hA a n ν (ε / 2) (by positivity)
    set K : ℝ := Real.sqrt ‖φ (a' * star a')‖ with hKdef
    have hK0 : 0 ≤ K := Real.sqrt_nonneg _
    obtain ⟨b', hb'B, hb'⟩ := hB b n ωs (ε / (2 * (K + 1))) (by positivity)
    refine ⟨M.tprod a' b',
      ⟨1, fun _ => a', fun _ => b', fun _ => ha'A, fun _ => hb'B, by simp⟩,
      fun i => ?_⟩
    have hsplit : M.tprod a b - M.tprod a' b'
        = M.tprod (a - a') b + M.tprod a' (b - b') := by
      have h1 : M.tprod (a - a') b + M.tprod a' b = M.tprod a b := by
        rw [← M.compat.add_left]; congr 1; abel
      have h2 : M.tprod a' (b - b') + M.tprod a' b' = M.tprod a' b := by
        rw [← M.compat.add_right]; congr 1; abel
      rw [← h1, ← h2]; abel
    have hb2 : K * unSeminorm (ωs i) (mulInner ℬ) (b - b') ≤ ε / 2 := by
      have h := mul_le_mul_of_nonneg_left (hb' i) hK0
      refine h.trans ?_
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hε.le]
    calc unSeminorm (ωs i) (inner ℬ : M.X → M.X → ℬ) (M.tprod a b - M.tprod a' b')
        = unSeminorm (ωs i) (inner ℬ : M.X → M.X → ℬ)
            (M.tprod (a - a') b + M.tprod a' (b - b')) := by rw [hsplit]
      _ ≤ unSeminorm (ωs i) (inner ℬ : M.X → M.X → ℬ) (M.tprod (a - a') b)
            + unSeminorm (ωs i) (inner ℬ : M.X → M.X → ℬ) (M.tprod a' (b - b')) :=
          unSeminorm_add_le _ (cstarBInner ℬ M.X) _ _
      _ ≤ unSeminorm (ν i) (mulInner 𝒜) (a - a')
            + K * unSeminorm (ωs i) (mulInner ℬ) (b - b') :=
          add_le_add
            (le_of_eq (unSeminorm_tprod_left φ M (ωs i) (ν i) b (hν i) (a - a')))
            (unSeminorm_tprod_right φ M (ωs i) a' (b - b'))
      _ ≤ ε / 2 + ε / 2 := add_le_add (ha' i) hb2
      _ = ε := by ring
  -- and hence so is every finite sum of elementary tensors, which are dense
  have hDsub : {z : M.X | ∃ (n : ℕ) (a : Fin n → 𝒜) (b : Fin n → ℬ),
      z = ∑ i, M.tprod (a i) (b i)} ⊆ unClosure ℬ (inner ℬ) T := by
    rintro _ ⟨n, a, b, rfl⟩
    exact Finset.sum_induction _ (fun w => w ∈ unClosure ℬ (inner ℬ) T)
      (fun w w' hw hw' => unClosure_add hTadd hw hw') (subset_unClosure _ hT0)
      fun i _ => helem (a i) (b i)
  intro z n ωs ε hε
  have hz : z ∈ unClosure ℬ (inner ℬ) T := by
    rw [← unClosure_unClosure T]
    exact unClosure_mono hDsub (paschke_tprod_dense φ M z)
  exact hz n ωs ε hε

/-! ## Parsec 1670: the tensor product of Paschke dilations -/

section PaschkeTensor

variable {𝒜₁ 𝒜₂ 𝒜₁₂ ℬ₁ ℬ₂ ℬ₁₂ P₁₂ : Type u}
  [CStarAlgebra 𝒜₁] [PartialOrder 𝒜₁] [StarOrderedRing 𝒜₁]
  [CStarAlgebra 𝒜₂] [PartialOrder 𝒜₂] [StarOrderedRing 𝒜₂]
  [CStarAlgebra 𝒜₁₂] [PartialOrder 𝒜₁₂] [StarOrderedRing 𝒜₁₂]
  [CStarAlgebra ℬ₁] [PartialOrder ℬ₁] [StarOrderedRing ℬ₁]
  [CStarAlgebra ℬ₂] [PartialOrder ℬ₂] [StarOrderedRing ℬ₂]
  [CStarAlgebra ℬ₁₂] [PartialOrder ℬ₁₂] [StarOrderedRing ℬ₁₂]
  [CStarAlgebra P₁₂] [PartialOrder P₁₂] [StarOrderedRing P₁₂]

/-- **167I** (`paschke-tensor`, dils.tex:5746, Theorem), main claim: if
`(𝒫ᵢ, ϱᵢ, hᵢ)` is a Paschke dilation of the ncp-map `φᵢ : 𝒜ᵢ → ℬᵢ`
(i = 1,2), then `(𝒫₁ ⊗ 𝒫₂, ϱ₁ ⊗ ϱ₂, h₁ ⊗ h₂)` is a Paschke dilation of
`φ₁ ⊗ φ₂`.  (The tensor products of algebras are given through the
`IsVNTensor` interface, and the tensor products of maps through their
characterizing values on elementary tensors.)

**167II**–**167VI** are the proof — not converted. -/
theorem paschke_tensor
    (tA : 𝒜₁ → 𝒜₂ → 𝒜₁₂) (htA : IsVNTensor tA)
    (tB : ℬ₁ → ℬ₂ → ℬ₁₂) (htB : IsVNTensor tB)
    (φ₁ : NCPMap 𝒜₁ ℬ₁) (φ₂ : NCPMap 𝒜₂ ℬ₂)
    (D₁ : PaschkeTriple 𝒜₁ ℬ₁) (D₂ : PaschkeTriple 𝒜₂ ℬ₂)
    (h₁ : IsPaschkeDilationOf D₁ ⇑φ₁) (h₂ : IsPaschkeDilationOf D₂ ⇑φ₂)
    (tP : D₁.P → D₂.P → P₁₂) (htP : IsVNTensor tP)
    (vnP : VonNeumannAlgebra P₁₂)
    (Φ : NCPMap 𝒜₁₂ ℬ₁₂)
    (hΦ : ∀ (a₁ : 𝒜₁) (a₂ : 𝒜₂), Φ (tA a₁ a₂) = tB (φ₁ a₁) (φ₂ a₂))
    (R : NMIUMap 𝒜₁₂ P₁₂)
    (hR : ∀ (a₁ : 𝒜₁) (a₂ : 𝒜₂), R (tA a₁ a₂) = tP (D₁.ρ a₁) (D₂.ρ a₂))
    (H : NCPMap P₁₂ ℬ₁₂)
    (hH : ∀ (c₁ : D₁.P) (c₂ : D₂.P),
      H (tP c₁ c₂) = tB (D₁.h c₁) (D₂.h c₂)) :
    IsPaschkeDilationOf ⟨P₁₂, vnP, R, H⟩ ⇑Φ :=
  sorry

/-! ### The isomorphism of dilation spaces (**167III**–**167V**)

The "furthermore" half of **167I** is what the thesis proves *first*, and it
needs neither **165VI** nor the main claim: both `X₁ ⊗ X₂` and
`(𝒜₁ ⊗ 𝒜₂) ⊗_Φ (ℬ₁ ⊗ ℬ₂)` are self-dual completions of one and the same
`ℬ₁₂`-module with `ℬ₁₂`-valued inner product, namely
`V = (𝒜₁ ⊙ 𝒜₂) ⊙ ℬ₁₂`, so **163II** `selfdual_compl_defining_unique`
produces the isomorphism outright.

**Divergence, class 2.**  The thesis (167V) extends its `U₀` in two steps —
first along the ultranorm-dense `𝒜ᵢ ⊙ ℬᵢ ⊆ 𝒜ᵢ ⊗_{φᵢ} ℬᵢ`, then by the
universal property of the exterior tensor product — and reads
inner-product preservation off **148V** and surjectivity off the density.
Recognising the two modules as completions of one `V` replaces all of that:
`selfdual_compl_defining_unique` (i.e. **151Ia** run four times) delivers
boundedness, bijectivity, inner-product preservation and the value on
elementary tensors in one go.  The two densities are the thesis's own
**167III**: `η₁`'s from **166VI** `dilationspace_dense_subset` at
`𝒜' = 𝒜₁ ⊙ 𝒜₂` (ultrastrongly dense by `unDense_tSpan`) and `ℬ' = ℬ₁₂`,
`η₂`'s from **166IV** `exttensor_dense_subsets` at the elementary tensors of
the two Paschke modules (`paschke_tprod_dense`).  The inner-product
computation of 167IV is `ptmEtaA_inner`. -/

section PaschkeTensorModuleAux

variable [VonNeumannAlgebra 𝒜₁] [VonNeumannAlgebra 𝒜₂] [VonNeumannAlgebra 𝒜₁₂]
  [VonNeumannAlgebra ℬ₁] [VonNeumannAlgebra ℬ₂] [VonNeumannAlgebra ℬ₁₂]

/-- The right ℬ₁₂-action on `(𝒜₁ ⊙ 𝒜₂) ⊙ ℬ₁₂`. -/
private noncomputable instance ptmSMul :
    SMul ℬ₁₂ ((𝒜₁ ⊗[ℂ] 𝒜₂) ⊗[ℂ] ℬ₁₂) where
  smul b := LinearMap.lTensor (𝒜₁ ⊗[ℂ] 𝒜₂) (LinearMap.mulLeft ℂ b)

private theorem ptm_smul_tmul (b : ℬ₁₂) (x : 𝒜₁ ⊗[ℂ] 𝒜₂) (b' : ℬ₁₂) :
    b • (x ⊗ₜ[ℂ] b') = x ⊗ₜ[ℂ] (b * b') := rfl

private theorem ptm_smul_add (b : ℬ₁₂) (v w : (𝒜₁ ⊗[ℂ] 𝒜₂) ⊗[ℂ] ℬ₁₂) :
    b • (v + w) = b • v + b • w :=
  map_add (LinearMap.lTensor (𝒜₁ ⊗[ℂ] 𝒜₂) (LinearMap.mulLeft ℂ b)) v w

@[simp] private theorem ptm_smul_zero (b : ℬ₁₂) :
    b • (0 : (𝒜₁ ⊗[ℂ] 𝒜₂) ⊗[ℂ] ℬ₁₂) = 0 :=
  map_zero (LinearMap.lTensor (𝒜₁ ⊗[ℂ] 𝒜₂) (LinearMap.mulLeft ℂ b))

/-- `tA` as a linear map on the algebraic tensor product. -/
private noncomputable def tALin {tA : 𝒜₁ → 𝒜₂ → 𝒜₁₂} (htA : IsVNTensor tA) :
    (𝒜₁ ⊗[ℂ] 𝒜₂) →ₗ[ℂ] 𝒜₁₂ :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ tA htA.add_left htA.smul_complex
    htA.add_right (fun c a b => vnTensor_smul_complex_right htA c a b)

@[simp] private theorem tALin_tmul {tA : 𝒜₁ → 𝒜₂ → 𝒜₁₂} (htA : IsVNTensor tA)
    (a₁ : 𝒜₁) (a₂ : 𝒜₂) : tALin htA (a₁ ⊗ₜ[ℂ] a₂) = tA a₁ a₂ := rfl

/-- The elementary tensor of a Paschke module as a ℂ-bilinear map. -/
private noncomputable def tprodBil {Φ : NCPMap 𝒜₁₂ ℬ₁₂} (M : PaschkeModule Φ) :
    𝒜₁₂ →ₗ[ℂ] ℬ₁₂ →ₗ[ℂ] M.X :=
  LinearMap.mk₂ ℂ M.tprod M.compat.add_left M.compat.smul_complex
    M.compat.add_right (fun c a b => M.compat.smul_complex_right Φ c a b)

/-- `η₁ : (𝒜₁ ⊙ 𝒜₂) ⊙ ℬ₁₂ → 𝒜₁₂ ⊗_Φ ℬ₁₂`, `(a₁ ⊗ a₂) ⊗ b ↦ (a₁ ⊗ a₂) ⊗ b`. -/
private noncomputable def ptmEta1 {tA : 𝒜₁ → 𝒜₂ → 𝒜₁₂} (htA : IsVNTensor tA)
    {Φ : NCPMap 𝒜₁₂ ℬ₁₂} (M : PaschkeModule Φ) :
    ((𝒜₁ ⊗[ℂ] 𝒜₂) ⊗[ℂ] ℬ₁₂) →ₗ[ℂ] M.X :=
  TensorProduct.lift ((tprodBil M).comp (tALin htA))

@[simp] private theorem ptmEta1_tmul {tA : 𝒜₁ → 𝒜₂ → 𝒜₁₂} (htA : IsVNTensor tA)
    {Φ : NCPMap 𝒜₁₂ ℬ₁₂} (M : PaschkeModule Φ) (x : 𝒜₁ ⊗[ℂ] 𝒜₂) (b : ℬ₁₂) :
    ptmEta1 htA M (x ⊗ₜ[ℂ] b) = M.tprod (tALin htA x) b := rfl

private theorem ptmEta1_op_smul {tA : 𝒜₁ → 𝒜₂ → 𝒜₁₂} (htA : IsVNTensor tA)
    {Φ : NCPMap 𝒜₁₂ ℬ₁₂} (M : PaschkeModule Φ) (b : ℬ₁₂)
    (v : (𝒜₁ ⊗[ℂ] 𝒜₂) ⊗[ℂ] ℬ₁₂) :
    ptmEta1 htA M (b • v) = b • ptmEta1 htA M v := by
  induction v using TensorProduct.induction_on with
  | zero => rw [ptm_smul_zero, map_zero, op_smul_zero]
  | tmul x b' => rw [ptm_smul_tmul, ptmEta1_tmul, ptmEta1_tmul, M.compat.smul_action]
  | add v₁ v₂ h₁ h₂ => rw [ptm_smul_add, map_add, map_add, h₁, h₂, op_smul_add]

section EtaTwo

variable {X Y : Type u}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ₁ X] [CStarModule ℬ₁ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul ℬ₂ Y] [CStarModule ℬ₂ Y]

/-- The ℬ-action and the ℂ-action on a Hilbert module commute. -/
private theorem op_smul_smul_complex {Z : Type u} [NormedAddCommGroup Z]
    [NormedSpace ℂ Z] [SMul ℬ₁₂ Z] [CStarModule ℬ₁₂ Z] (b : ℬ₁₂) (c : ℂ)
    (z : Z) : b • (c • z) = c • (b • z) := by
  have h1 : c • z = (c • (1 : ℬ₁₂)) • z := by
    rw [op_smul_complex_smul, op_one_smul]
  have h2 : c • (b • z) = (c • b) • z := by rw [op_smul_complex_smul]
  rw [h1, ← op_mul_smul, mul_smul_comm, mul_one, h2]

/-- `η` is ℂ-homogeneous in its second argument too. -/
private theorem extTensor_eta_smul_complex_right {tB : ℬ₁ → ℬ₂ → ℬ₁₂}
    {htB : IsVNTensor tB} (E : ExtTensor tB htB X Y) (c : ℂ) (x : X) (y : Y) :
    E.η x (c • y) = c • E.η x y := by
  have h := E.η_smul 1 (c • (1 : ℬ₂)) x y
  rw [op_one_smul, op_smul_complex_smul, op_one_smul,
    vnTensor_smul_complex_right htB, htB.one, op_smul_complex_smul,
    op_one_smul] at h
  exact h

end EtaTwo

section EtaTwoDef

variable {φ₁ : NCPMap 𝒜₁ ℬ₁} {φ₂ : NCPMap 𝒜₂ ℬ₂} {tB : ℬ₁ → ℬ₂ → ℬ₁₂}
  {htB : IsVNTensor tB}

/-- `a₁ ⊗ a₂ ↦ (a₁ ⊗ 1) ⊗ (a₂ ⊗ 1)`, as a linear map on `𝒜₁ ⊙ 𝒜₂`. -/
private noncomputable def ptmEtaA (M₁ : PaschkeModule φ₁) (M₂ : PaschkeModule φ₂)
    (E : ExtTensor tB htB M₁.X M₂.X) : (𝒜₁ ⊗[ℂ] 𝒜₂) →ₗ[ℂ] E.Z :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ
    (fun a₁ a₂ => E.η (M₁.tprod a₁ 1) (M₂.tprod a₂ 1))
    (fun a a' b => by rw [M₁.compat.add_left, E.η_add_left])
    (fun c a b => by rw [M₁.compat.smul_complex, E.η_smul_complex])
    (fun a b b' => by rw [M₂.compat.add_left, E.η_add_right])
    (fun c a b => by
      rw [M₂.compat.smul_complex, extTensor_eta_smul_complex_right])

@[simp] private theorem ptmEtaA_tmul (M₁ : PaschkeModule φ₁) (M₂ : PaschkeModule φ₂)
    (E : ExtTensor tB htB M₁.X M₂.X) (a₁ : 𝒜₁) (a₂ : 𝒜₂) :
    ptmEtaA M₁ M₂ E (a₁ ⊗ₜ[ℂ] a₂) = E.η (M₁.tprod a₁ 1) (M₂.tprod a₂ 1) := rfl

/-- `η₂ : (𝒜₁ ⊙ 𝒜₂) ⊙ ℬ₁₂ → X₁ ⊗ X₂`,
`(a₁ ⊗ a₂) ⊗ b ↦ b · ((a₁ ⊗ 1) ⊗ (a₂ ⊗ 1))`. -/
private noncomputable def ptmEta2 (M₁ : PaschkeModule φ₁) (M₂ : PaschkeModule φ₂)
    (E : ExtTensor tB htB M₁.X M₂.X) :
    ((𝒜₁ ⊗[ℂ] 𝒜₂) ⊗[ℂ] ℬ₁₂) →ₗ[ℂ] E.Z :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ
    (fun x b => b • ptmEtaA M₁ M₂ E x)
    (fun x x' b => by rw [map_add, op_smul_add])
    (fun c x b => by rw [map_smul, op_smul_smul_complex])
    (fun x b b' => by rw [op_add_smul])
    (fun c x b => by rw [op_smul_complex_smul])

@[simp] private theorem ptmEta2_tmul (M₁ : PaschkeModule φ₁) (M₂ : PaschkeModule φ₂)
    (E : ExtTensor tB htB M₁.X M₂.X) (x : 𝒜₁ ⊗[ℂ] 𝒜₂) (b : ℬ₁₂) :
    ptmEta2 M₁ M₂ E (x ⊗ₜ[ℂ] b) = b • ptmEtaA M₁ M₂ E x := rfl

private theorem ptmEta2_op_smul (M₁ : PaschkeModule φ₁) (M₂ : PaschkeModule φ₂)
    (E : ExtTensor tB htB M₁.X M₂.X) (b : ℬ₁₂)
    (v : (𝒜₁ ⊗[ℂ] 𝒜₂) ⊗[ℂ] ℬ₁₂) :
    ptmEta2 M₁ M₂ E (b • v) = b • ptmEta2 M₁ M₂ E v := by
  induction v using TensorProduct.induction_on with
  | zero => rw [ptm_smul_zero, map_zero, op_smul_zero]
  | tmul x b' => rw [ptm_smul_tmul, ptmEta2_tmul, ptmEta2_tmul, op_mul_smul]
  | add v₁ v₂ h₁ h₂ => rw [ptm_smul_add, map_add, map_add, h₁, h₂, op_smul_add]

end EtaTwoDef

section PTMain

variable {tA : 𝒜₁ → 𝒜₂ → 𝒜₁₂} {htA : IsVNTensor tA}
  {tB : ℬ₁ → ℬ₂ → ℬ₁₂} {htB : IsVNTensor tB}
  {φ₁ : NCPMap 𝒜₁ ℬ₁} {φ₂ : NCPMap 𝒜₂ ℬ₂} {Φ : NCPMap 𝒜₁₂ ℬ₁₂}
  (M₁ : PaschkeModule φ₁) (M₂ : PaschkeModule φ₂) (M₁₂ : PaschkeModule Φ)

/-- The Gram identity on `𝒜₁ ⊙ 𝒜₂`: `⟨eA x, eA y⟩ = Φ(y x*)`. -/
private theorem ptmEtaA_inner (E : ExtTensor tB htB M₁.X M₂.X)
    (hΦ : ∀ (a₁ : 𝒜₁) (a₂ : 𝒜₂), Φ (tA a₁ a₂) = tB (φ₁ a₁) (φ₂ a₂))
    (x y : 𝒜₁ ⊗[ℂ] 𝒜₂) :
    inner ℬ₁₂ (ptmEtaA M₁ M₂ E x) (ptmEtaA M₁ M₂ E y)
      = Φ (tALin htA y * star (tALin htA x)) := by
  have hadd : ∀ p q : 𝒜₁₂, Φ (p + q) = Φ p + Φ q := fun p q =>
    map_add Φ.toCompletelyPositiveMap.toLinearMap p q
  have hzero : Φ (0 : 𝒜₁₂) = 0 :=
    map_zero Φ.toCompletelyPositiveMap.toLinearMap
  induction x using TensorProduct.induction_on with
  | zero => simp [hzero]
  | tmul a₁ a₂ =>
      induction y using TensorProduct.induction_on with
      | zero => simp [hzero]
      | tmul α₁ α₂ =>
          rw [ptmEtaA_tmul, ptmEtaA_tmul, E.η_inner, M₁.inner_tprod,
            M₂.inner_tprod]
          simp only [star_one, one_mul, mul_one]
          rw [tALin_tmul, tALin_tmul, htA.star, htA.mul, ← hΦ]
      | add y₁ y₂ h₁ h₂ =>
          rw [map_add (ptmEtaA M₁ M₂ E) y₁ y₂, CStarModule.inner_add_right,
            h₁, h₂, map_add (tALin htA) y₁ y₂, add_mul, hadd]
  | add x₁ x₂ h₁ h₂ =>
      rw [map_add (ptmEtaA M₁ M₂ E) x₁ x₂, CStarModule.inner_add_left,
        h₁, h₂, map_add (tALin htA) x₁ x₂, star_add, mul_add, hadd]

/-- Both embeddings induce the same 𝒷-valued inner product on
`(𝒜₁ ⊙ 𝒜₂) ⊙ ℬ₁₂`. -/
private theorem ptmEta_inner_eq (E : ExtTensor tB htB M₁.X M₂.X)
    (hΦ : ∀ (a₁ : 𝒜₁) (a₂ : 𝒜₂), Φ (tA a₁ a₂) = tB (φ₁ a₁) (φ₂ a₂))
    (v w : (𝒜₁ ⊗[ℂ] 𝒜₂) ⊗[ℂ] ℬ₁₂) :
    inner ℬ₁₂ (ptmEta2 M₁ M₂ E v) (ptmEta2 M₁ M₂ E w)
      = inner ℬ₁₂ (ptmEta1 htA M₁₂ v) (ptmEta1 htA M₁₂ w) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul y β =>
          rw [ptmEta2_tmul, ptmEta2_tmul, ptmEta1_tmul, ptmEta1_tmul,
            CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_left,
            ptmEtaA_inner M₁ M₂ E hΦ, M₁₂.inner_tprod, mul_assoc]
      | add w₁ w₂ h₁ h₂ =>
          rw [map_add, map_add, CStarModule.inner_add_right,
            CStarModule.inner_add_right, h₁, h₂]
  | add v₁ v₂ h₁ h₂ =>
      rw [map_add, map_add, CStarModule.inner_add_left,
        CStarModule.inner_add_left, h₁, h₂]

/-- The 𝒷-valued inner product on `(𝒜₁ ⊙ 𝒜₂) ⊙ ℬ₁₂` pulled back along
`η₁`. -/
private noncomputable def ptmBInner (htA : IsVNTensor tA) (M₁₂ : PaschkeModule Φ) :
    BInner ℬ₁₂ ((𝒜₁ ⊗[ℂ] 𝒜₂) ⊗[ℂ] ℬ₁₂) where
  inner v w := inner ℬ₁₂ (ptmEta1 htA M₁₂ v) (ptmEta1 htA M₁₂ w)
  inner_add_right v w z := by rw [map_add, CStarModule.inner_add_right]
  inner_op_smul_right b v w := by
    rw [ptmEta1_op_smul, CStarModule.inner_op_smul_right]
  inner_smul_right_complex c v w := by
    rw [map_smul, CStarModule.inner_smul_right_complex]
  star_inner v w := CStarModule.star_inner _ _
  inner_self_nonneg v := CStarModule.inner_self_nonneg

/-- Ultranorm density of the range of `η₁`: **166VI** with `𝒜' = 𝒜₁ ⊙ 𝒜₂`
(ultrastrongly dense by `unDense_tSpan`) and `ℬ' = ℬ₁₂`. -/
private theorem ptmEta1_denseRange (htA : IsVNTensor tA) (M₁₂ : PaschkeModule Φ)
    (A' : StarSubalgebra ℂ 𝒜₁₂)
    (hA'dense : UnDense (mulInner 𝒜₁₂) (A' : Set 𝒜₁₂))
    (hA'mem : ∀ c ∈ A', ∃ (n : ℕ) (α : Fin n → 𝒜₁) (α' : Fin n → 𝒜₂),
      c = ∑ i, tA (α i) (α' i)) :
    UnDense (inner ℬ₁₂) (Set.range (ptmEta1 htA M₁₂)) := by
  classical
  have hBtop : UnDense (mulInner ℬ₁₂) ((⊤ : StarSubalgebra ℂ ℬ₁₂) : Set ℬ₁₂) := by
    intro x n ωs ε hε
    refine ⟨x, by trivial, fun i => ?_⟩
    rw [sub_self]
    have h0 : unSeminorm (ωs i) (mulInner ℬ₁₂) (0 : ℬ₁₂) = 0 :=
      unSeminorm_zero (ωs i) (cstarBInner ℬ₁₂ ℬ₁₂)
    rw [h0]
    exact hε.le
  have hd := dilationspace_dense_subset Φ M₁₂ A'
    (⊤ : StarSubalgebra ℂ ℬ₁₂) hA'dense hBtop
  intro z n ωs ε hε
  obtain ⟨d, ⟨m, a, b, ha, -, rfl⟩, hdist⟩ := hd z n ωs ε hε
  choose k α α' hα using fun i => hA'mem (a i) (ha i)
  refine ⟨_, ⟨∑ i, (∑ j, α i j ⊗ₜ[ℂ] α' i j) ⊗ₜ[ℂ] b i, rfl⟩, ?_⟩
  have hval : ptmEta1 htA M₁₂ (∑ i, (∑ j, α i j ⊗ₜ[ℂ] α' i j) ⊗ₜ[ℂ] b i)
      = ∑ i, M₁₂.tprod (a i) (b i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 : (tALin htA) (∑ j, α i j ⊗ₜ[ℂ] α' i j) = a i := by
      rw [map_sum, hα i]
      exact Finset.sum_congr rfl fun j _ => tALin_tmul htA _ _
    rw [ptmEta1_tmul, h2]
  rw [hval]
  exact hdist

/-- The image of `η₁`, as a `SelfDualCompletion` of `(𝒜₁ ⊙ 𝒜₂) ⊙ ℬ₁₂`. -/
private noncomputable def ptmCompl1 (htA : IsVNTensor tA) (M₁₂ : PaschkeModule Φ)
    (hdense : UnDense (inner ℬ₁₂) (Set.range (ptmEta1 htA M₁₂))) :
    SelfDualCompletion.{u, u, u} (ptmBInner htA M₁₂) where
  X := M₁₂.X
  selfDual := M₁₂.selfDual
  η := ptmEta1 htA M₁₂
  η_add v w := map_add _ v w
  η_smul_complex c v := map_smul _ c v
  η_smul b v := ptmEta1_op_smul htA M₁₂ b v
  η_inner v w := rfl
  dense := hdense

end PTMain

private theorem ptmOpSmulSum {𝒷 W : Type u} [CStarAlgebra 𝒷] [PartialOrder 𝒷]
    [StarOrderedRing 𝒷] [NormedAddCommGroup W] [NormedSpace ℂ W] [SMul 𝒷 W]
    [CStarModule 𝒷 W] {κ : Type*} (a : 𝒷) (s : Finset κ) (f : κ → W) :
    a • (∑ i ∈ s, f i) = ∑ i ∈ s, a • f i := by
  classical
  refine Finset.induction_on s (by simp [op_smul_zero]) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, op_smul_add, ih, Finset.sum_insert hi]

section EtaSums

variable {tB : ℬ₁ → ℬ₂ → ℬ₁₂} {htB : IsVNTensor tB} {X Y : Type u}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ₁ X] [CStarModule ℬ₁ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul ℬ₂ Y] [CStarModule ℬ₂ Y]

/-- `η(·, y)` as an additive map, so that it commutes with finite sums. -/
private noncomputable def etaHomLeft (E : ExtTensor tB htB X Y) (y : Y) : X →+ E.Z where
  toFun x := E.η x y
  map_zero' := by
    have h := E.η_smul_complex 0 0 y
    rwa [zero_smul, zero_smul] at h
  map_add' x x' := E.η_add_left x x' y

/-- `η(x, ·)` as an additive map. -/
private noncomputable def etaHomRight (E : ExtTensor tB htB X Y) (x : X) : Y →+ E.Z where
  toFun y := E.η x y
  map_zero' := by
    have h := extTensor_eta_smul_complex_right E 0 x 0
    rwa [zero_smul, zero_smul] at h
  map_add' y y' := E.η_add_right x y y'

private theorem eta_sum_left (E : ExtTensor tB htB X Y) {n : ℕ} (f : Fin n → X)
    (y : Y) : E.η (∑ i, f i) y = ∑ i, E.η (f i) y :=
  map_sum (etaHomLeft E y) f Finset.univ

private theorem eta_sum_right (E : ExtTensor tB htB X Y) (x : X) {n : ℕ}
    (g : Fin n → Y) : E.η x (∑ i, g i) = ∑ i, E.η x (g i) :=
  map_sum (etaHomRight E x) g Finset.univ

end EtaSums

section PTMain2

variable {tA : 𝒜₁ → 𝒜₂ → 𝒜₁₂} {htA : IsVNTensor tA}
  {tB : ℬ₁ → ℬ₂ → ℬ₁₂} {htB : IsVNTensor tB}
  {φ₁ : NCPMap 𝒜₁ ℬ₁} {φ₂ : NCPMap 𝒜₂ ℬ₂} {Φ : NCPMap 𝒜₁₂ ℬ₁₂}
  (M₁ : PaschkeModule φ₁) (M₂ : PaschkeModule φ₂) (M₁₂ : PaschkeModule Φ)

/-- The elementary tensor `(a₁ ⊗ b₁) ⊗ (a₂ ⊗ b₂)` of `X₁ ⊗ X₂` is in the
image of `η₂`, at `(a₁ ⊗ a₂) ⊗ (b₁ ⊗ b₂)`. -/
private theorem ptmEta2_eta_tprod (E : ExtTensor tB htB M₁.X M₂.X)
    (a₁ : 𝒜₁) (b₁ : ℬ₁) (a₂ : 𝒜₂) (b₂ : ℬ₂) :
    E.η (M₁.tprod a₁ b₁) (M₂.tprod a₂ b₂)
      = ptmEta2 M₁ M₂ E ((a₁ ⊗ₜ[ℂ] a₂) ⊗ₜ[ℂ] tB b₁ b₂) := by
  have h1 : M₁.tprod a₁ b₁ = b₁ • M₁.tprod a₁ 1 := by
    rw [M₁.compat.smul_action, mul_one]
  have h2 : M₂.tprod a₂ b₂ = b₂ • M₂.tprod a₂ 1 := by
    rw [M₂.compat.smul_action, mul_one]
  rw [h1, h2, E.η_smul, ptmEta2_tmul, ptmEtaA_tmul]

/-- Ultranorm density of the range of `η₂`: **166IV** applied to the
elementary tensors of the two Paschke modules (**166VI** at `𝒜' = 𝒜`,
`ℬ' = ℬ`, i.e. `paschke_tprod_dense`). -/
private theorem ptmEta2_denseRange (E : ExtTensor tB htB M₁.X M₂.X) :
    UnDense (inner ℬ₁₂) (Set.range (ptmEta2 M₁ M₂ E)) := by
  classical
  set U : Set M₁.X := {z : M₁.X | ∃ (n : ℕ) (a : Fin n → 𝒜₁) (b : Fin n → ℬ₁),
    z = ∑ i, M₁.tprod (a i) (b i)} with hUdef
  set V : Set M₂.X := {z : M₂.X | ∃ (n : ℕ) (a : Fin n → 𝒜₂) (b : Fin n → ℬ₂),
    z = ∑ i, M₂.tprod (a i) (b i)} with hVdef
  have hUadd : ∀ u ∈ U, ∀ u' ∈ U, u + u' ∈ U := by
    rintro _ ⟨n, a, b, rfl⟩ _ ⟨m, a', b', rfl⟩
    refine ⟨n + m, Fin.append a a', Fin.append b b', ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  have hUsmul : ∀ (c : ℬ₁), ∀ u ∈ U, c • u ∈ U := by
    rintro c _ ⟨n, a, b, rfl⟩
    refine ⟨n, a, fun i => c * b i, ?_⟩
    rw [ptmOpSmulSum]
    exact Finset.sum_congr rfl fun i _ => M₁.compat.smul_action _ _ _
  have hVadd : ∀ v ∈ V, ∀ v' ∈ V, v + v' ∈ V := by
    rintro _ ⟨n, a, b, rfl⟩ _ ⟨m, a', b', rfl⟩
    refine ⟨n + m, Fin.append a a', Fin.append b b', ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  have hVsmul : ∀ (c : ℬ₂), ∀ v ∈ V, c • v ∈ V := by
    rintro c _ ⟨n, a, b, rfl⟩
    refine ⟨n, a, fun i => c * b i, ?_⟩
    rw [ptmOpSmulSum]
    exact Finset.sum_congr rfl fun i _ => M₂.compat.smul_action _ _ _
  have hd := exttensor_dense_subsets M₁.selfDual M₂.selfDual E U V
    (paschke_tprod_dense φ₁ M₁) (paschke_tprod_dense φ₂ M₂)
    hUadd hUsmul hVadd hVsmul
  -- every member of the dense set is in the range of `η₂`
  have hsub : ∀ z : E.Z,
      (∃ (n : ℕ) (u : Fin n → M₁.X) (v : Fin n → M₂.X),
        (∀ i, u i ∈ U) ∧ (∀ i, v i ∈ V) ∧ z = ∑ i, E.η (u i) (v i)) →
      z ∈ Set.range (ptmEta2 M₁ M₂ E) := by
    rintro _ ⟨n, u, v, hu, hv, rfl⟩
    choose p a b hab using fun i => hu i
    choose q α β hαβ using fun i => hv i
    refine ⟨∑ i, ∑ j, ∑ k,
      ((a i j ⊗ₜ[ℂ] α i k) ⊗ₜ[ℂ] tB (b i j) (β i k)), ?_⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, hab i, hαβ i, eta_sum_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum, eta_sum_right]
    exact Finset.sum_congr rfl fun k _ => (ptmEta2_eta_tprod M₁ M₂ E _ _ _ _).symm
  intro z n ωs ε hε
  obtain ⟨d, hd', hdist⟩ := hd z n ωs ε hε
  exact ⟨d, hsub d hd', hdist⟩

/-- The exterior tensor product `X₁ ⊗ X₂`, as a `SelfDualCompletion` of the
same `(𝒜₁ ⊙ 𝒜₂) ⊙ ℬ₁₂`. -/
private noncomputable def ptmCompl2 (E : ExtTensor tB htB M₁.X M₂.X)
    (hΦ : ∀ (a₁ : 𝒜₁) (a₂ : 𝒜₂), Φ (tA a₁ a₂) = tB (φ₁ a₁) (φ₂ a₂)) :
    SelfDualCompletion.{u, u, u} (ptmBInner htA M₁₂) where
  X := E.Z
  selfDual := E.selfDual
  η := ptmEta2 M₁ M₂ E
  η_add v w := map_add _ v w
  η_smul_complex c v := map_smul _ c v
  η_smul b v := ptmEta2_op_smul M₁ M₂ E b v
  η_inner v w := ptmEta_inner_eq M₁ M₂ M₁₂ E hΦ v w
  dense := ptmEta2_denseRange M₁ M₂ E

end PTMain2

end PaschkeTensorModuleAux

/-- **167I** (`paschke-tensor`, dils.tex:5746, Theorem), furthermore-claim
(dils.tex:5754): the dilation spaces satisfy
`(𝒜₁ ⊗_{φ₁} ℬ₁) ⊗ (𝒜₂ ⊗_{φ₂} ℬ₂) ≅ (𝒜₁ ⊗ 𝒜₂) ⊗_{φ₁⊗φ₂} (ℬ₁ ⊗ ℬ₂)`,
via the map determined on elementary tensors. -/
theorem paschke_tensor_module
    [VonNeumannAlgebra 𝒜₁] [VonNeumannAlgebra 𝒜₂] [VonNeumannAlgebra 𝒜₁₂]
    [VonNeumannAlgebra ℬ₁] [VonNeumannAlgebra ℬ₂] [VonNeumannAlgebra ℬ₁₂]
    (tA : 𝒜₁ → 𝒜₂ → 𝒜₁₂) (htA : IsVNTensor tA)
    (tB : ℬ₁ → ℬ₂ → ℬ₁₂) (htB : IsVNTensor tB)
    (φ₁ : NCPMap 𝒜₁ ℬ₁) (φ₂ : NCPMap 𝒜₂ ℬ₂)
    (M₁ : PaschkeModule φ₁) (M₂ : PaschkeModule φ₂)
    (Φ : NCPMap 𝒜₁₂ ℬ₁₂)
    (hΦ : ∀ (a₁ : 𝒜₁) (a₂ : 𝒜₂), Φ (tA a₁ a₂) = tB (φ₁ a₁) (φ₂ a₂))
    (M₁₂ : PaschkeModule Φ)
    (E : ExtTensor tB htB M₁.X M₂.X) :
    ∃ U : E.Z → M₁₂.X,
      (∃ C : ℝ, IsBoundedModuleMap (cstarBInner ℬ₁₂ E.Z)
        (cstarBInner ℬ₁₂ M₁₂.X) C U) ∧
      Function.Bijective U ∧
      (∀ z z' : E.Z, inner ℬ₁₂ (U z) (U z') = inner ℬ₁₂ z z') ∧
      ∀ (a₁ : 𝒜₁) (b₁ : ℬ₁) (a₂ : 𝒜₂) (b₂ : ℬ₂),
        U (E.η (M₁.tprod a₁ b₁) (M₂.tprod a₂ b₂)) =
          M₁₂.tprod (tA a₁ a₂) (tB b₁ b₂) := by
  have hdense : UnDense (inner ℬ₁₂) (Set.range (ptmEta1 htA M₁₂)) :=
    ptmEta1_denseRange htA M₁₂ (tSpanSubalg htA) (unDense_tSpan htA)
      (fun _ hc => hc)
  obtain ⟨U, ⟨hUb, hUbij, hUip, hUη⟩, -⟩ :=
    selfdual_compl_defining_unique (ptmBInner htA M₁₂)
      (ptmCompl2 M₁ M₂ M₁₂ E hΦ) (ptmCompl1 htA M₁₂ hdense)
  refine ⟨U, hUb, hUbij, hUip, fun a₁ b₁ a₂ b₂ => ?_⟩
  rw [ptmEta2_eta_tprod M₁ M₂ E a₁ b₁ a₂ b₂]
  exact hUη ((a₁ ⊗ₜ[ℂ] a₂) ⊗ₜ[ℂ] tB b₁ b₂)

end PaschkeTensor


end Theses.B.Dils
