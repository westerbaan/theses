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

open scoped ComplexOrder CStarAlgebra WithCStarModule Uniformity
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

**159X**–**159XI** are the proof — not converted. -/
theorem ketbra_ultranorm_continuous [VonNeumannAlgebra ℬ]
    (hX : SelfDual ℬ X) {ι : Type v} {l : Filter ι} (x : ι → X) (x₀ : X)
    (hbdd : ∃ M : ℝ, ∀ i, ‖x i‖ ≤ M)
    (hx : UnTendsto (inner ℬ) x l x₀) (y : X)
    (K : ι → Ba ℬ X) (hK : ∀ i, (K i).1 = mketbra ℬ (x i) y)
    (K₀ : Ba ℬ X) (hK₀ : K₀.1 = mketbra ℬ x₀ y) :
    UWTendsto K l K₀ :=
  sorry

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

/-- **160IV** (`hilbmod-projthm`, dils.tex:4488, Proposition), part 2:
`V^⊥⊥` is the ultranorm closure of the ℬ-linear span of `V`. -/
theorem hilbmod_projthm_2 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) (V : Set X) :
    orthoCompl ℬ (orthoCompl ℬ V) = unClosure ℬ (inner ℬ) (bSpan ℬ V) :=
  sorry

/-- **160IV** (`hilbmod-projthm`, dils.tex:4488, Proposition), part 3:
`V^⊥⊥ ⊕ V^⊥ ≅ X` via `(x,y) ↦ x + y`: every element of `X` decomposes
uniquely as a sum of an element of `V^⊥⊥` and one of `V^⊥`.

**160V**–**160VIII** are the proof — not converted. -/
theorem hilbmod_projthm_3 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) (V : Set X) (x : X) :
    ∃! p : X × X, p.1 ∈ orthoCompl ℬ (orthoCompl ℬ V) ∧
      p.2 ∈ orthoCompl ℬ V ∧ x = p.1 + p.2 :=
  sorry

/-- **160IX** (`selfdual-orthn-basis`, dils.tex:4565, Exercise): for an
orthonormal family `(eᵢ)` in a self-dual Hilbert ℬ-module: (1) `(eᵢ)` is a
basis of `E^⊥⊥` (every `x ∈ E^⊥⊥` is the ultranorm limit of its basis
expansion); (2) `x ∈ E^⊥⊥` iff `⟨x,x⟩ = ∑ᵢ ⟨x,eᵢ⟩⟨eᵢ,x⟩` (mirrored). -/
theorem selfdual_orthn_basis [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) {ι : Type v} (e : ι → X)
    (he : OrthonormalFam ℬ e) (x : X) :
    (x ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) →
      UnTendsto (inner ℬ)
        (fun s : Finset ι => ∑ i ∈ s, inner ℬ (e i) x • e i) atTop x) ∧
    (x ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) ↔
      UWTendsto
        (fun s : Finset ι => ∑ i ∈ s, inner ℬ (e i) x * inner ℬ x (e i))
        atTop (inner ℬ x x)) :=
  sorry

/-- **160X** (`selfdual-gramschmidt`, dils.tex:4581, Exercise): for
`x₁, …, xₙ` in a self-dual Hilbert ℬ-module there is a finite orthonormal
basis of `{x₁,…,xₙ}^⊥⊥` of at most `n` elements (each `xᵢ` is its finite
basis expansion). -/
theorem selfdual_gramschmidt [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) {n : ℕ} (x : Fin n → X) :
    ∃ (m : ℕ), m ≤ n ∧ ∃ f : Fin m → X,
      OrthonormalFam ℬ f ∧
      (∀ k, f k ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range x))) ∧
      ∀ i, x i = ∑ k, inner ℬ (f k) (x i) • f k :=
  sorry

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

/-- **161II** (`hilbmod-el2`, dils.tex:4602, Exercise), part 2:
`ℓ²((pᵢ)ᵢ)` is self dual, and every self-dual Hilbert ℬ-module `X` with
orthonormal basis `(eᵢ)ᵢ` is isomorphic to `ℓ²((⟨eᵢ,eᵢ⟩)ᵢ)` via the
coordinate map `x ↦ (⟨eᵢ,x⟩)ᵢ`: the coordinate map is injective, additive,
lands bijectively on `ℓ²((⟨eᵢ,eᵢ⟩)ᵢ)` and identifies the inner
products. -/
theorem hilbmod_el2 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) {ι : Type v} (e : ι → X) (he : IsONBasis ℬ e) :
    Set.BijOn (fun (x : X) (i : ι) => inner ℬ (e i) x) Set.univ
        (L2Set ℬ fun i => inner ℬ (e i) (e i)) ∧
      ∀ x y : X,
        UWTendsto
          (fun t : Finset ι =>
            ∑ i ∈ t, inner ℬ (e i) y * star (inner ℬ (e i) x))
          atTop (inner ℬ x y) :=
  sorry

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

/-- **162II** (`total-mv-order`, dils.tex:4717, Proposition): in a factor,
any two projections are comparable: `p ≲ q` or `q ≲ p`.

**162III** is the proof — not converted. -/
theorem total_mv_order [VonNeumannAlgebra ℬ] (hF : IsFactor ℬ) (p q : ℬ)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    MvNLe p q ∨ MvNLe q p :=
  sorry

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
      ∀ v : V, U (E₁.η v) = E₂.η v :=
  sorry

/-- **163II** (`selfdual-compl-defining`, dils.tex:4935, Proposition),
moreover-clause: if an inner-product-preserving module map `η : V → X`
into a self-dual Hilbert ℬ-module has the universal property (every
bounded module map `V → Y` into a self-dual `Y` factors uniquely through
`η`), then the image of `η` is ultranorm dense. -/
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
    UnDense (inner ℬ) (Set.range η) :=
  sorry

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
    Nonempty (ExtTensor t ht X Y) :=
  sorry

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

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), property 1:
the (span of the) image of `η` is ultranorm dense in `X ⊗ Y`. -/
theorem ext_tensor_dense [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y) :
    UnDense (inner 𝒞)
      {z : E.Z | ∃ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
        z = ∑ i, E.η (x i) (y i)} :=
  sorry

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), property 2a:
for orthonormal bases `(eᵢ)` of `X` and `(dⱼ)` of `Y`, the family
`(eᵢ ⊗ dⱼ)` is an orthonormal basis of `X ⊗ Y`. -/
theorem ext_tensor_basis [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    {ι κ : Type u} (e : ι → X) (d : κ → Y)
    (he : IsONBasis 𝒜 e) (hd : IsONBasis ℬ d) :
    IsONBasis 𝒞 fun p : ι × κ => E.η (e p.1) (d p.2) :=
  sorry

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
are proofs — not converted. -/

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

/-- **166IV** (`exttensor-dense-subsets`, dils.tex:5669, Lemma): for
ultranorm-dense submodules `U ⊆ X` and `V ⊆ Y`, the linear span of
`U ⊗ V = {u ⊗ v}` is ultranorm dense in `X ⊗ Y`. -/
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
        (∀ i, u i ∈ U) ∧ (∀ i, v i ∈ V) ∧ z = ∑ i, E.η (u i) (v i)} :=
  sorry

end ExtTensor

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
        z = ∑ i, M.tprod (a i) (b i)} :=
  sorry

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
          M₁₂.tprod (tA a₁ a₂) (tB b₁ b₂) :=
  sorry

end PaschkeTensor

end Theses.B.Dils
