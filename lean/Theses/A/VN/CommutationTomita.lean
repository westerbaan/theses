/-
# The commutation theorem in the cyclic and separating case

`(M ⊗̄ N)□ = M□ ⊗̄ N□` for von Neumann algebras `M ⊆ B(ℋ)`, `N ⊆ B(𝒦)` with cyclic and
separating vectors `ω`, `ω'`.

The four-line argument, with each line an already-proved unconditional theorem of the tree:

1. `ξ := ω ⊗ ω'` is cyclic and separating for `M ⊗̄ N` — `ModularTensor.lean`'s
   `isCyclicVector_vnTensor`, `isSeparatingVector_vnTensor`.
2. **Tomita**, applied to `M ⊗̄ N` at `ξ`: `J_ξ (M ⊗̄ N) J_ξ = (M ⊗̄ N)□`
   (`TomitaAnalytic.lean`'s `tomita_JMJ_unconditional`).
3. **The factorisation** `J_ξ = J_ω ⊗ J_{ω'}` — `ModularTensor.lean`'s `modularConj_htmul`.
4. Hence `(M ⊗̄ N)□ = (J_ω M J_ω) ⊗̄ (J_{ω'} N J_{ω'}) = M□ ⊗̄ N□`, Tomita again on each
   factor.

Step 4's middle equality is the work here.  `J_ω ⊗ J_{ω'}` is *conjugate*-linear and is
deliberately never built as an operator; what is used instead is that the ℂ-linear
`Φ := adJ_ξ = (x ↦ J_ξ x J_ξ)` is a **conjugate-linear involutive ∗-automorphism** of
`B(ℋ ⊗ 𝒦)` — so, being a multiplicative bijection, it commutes with `(·)□`
(`adJ_image_commutant`) — and that it acts on elementary tensors of operators by
`Φ (a ⊗ b) = (J_ω a J_ω) ⊗ (J_{ω'} b J_{ω'})` (`adJ_opTensor`), which is checked on
elementary tensors of *vectors* using the factorisation of step 3.

Both `vnTensor` (`ModularTensor.lean`) and `concreteTensor` (`QuantumLambda.lean`) are
`W*` of the same generating set, so the result is stated both ways; the `concreteTensor`
form is `CT` of `A/Proc/Commutation.lean`, `CT_of_cyclicSeparating`.
-/
import Theses.A.VN.TomitaAnalytic
import Theses.A.VN.ModularTensor
import Theses.A.Proc.Commutation

set_option linter.unusedSectionVars false

open Complex ClosedSubmodule Theses.A.VN Theses.A.Proc
open scoped ComplexInnerProductSpace ComplexOrder

namespace Theses.RvD

/-! ## Part I: `x ↦ J x J` commutes with the commutant

Purely algebraic: `adJ` is multiplicative and involutive, hence a bijection of `B(ℋ)`
respecting products, and any such map carries `S□` onto `(J S J)□`. -/

section AdJ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (K : ClosedSubmodule ℝ H) (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤)

include hsep hcyc

/-- `J S□ J = (J S J)□`. -/
theorem adJ_image_commutant (S : Set (H →L[ℂ] H)) :
    (fun x => adJ K hsep hcyc x) '' (commutant (H →L[ℂ] H) S)
      = commutant (H →L[ℂ] H) ((fun x => adJ K hsep hcyc x) '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← adJ_mul K hsep hcyc, ← adJ_mul K hsep hcyc, hx s hs]
  · intro hy
    refine ⟨adJ K hsep hcyc y, ?_, adJ_adJ K hsep hcyc y⟩
    intro s hs
    have h := hy _ ⟨s, hs, rfl⟩
    have h2 := congrArg (adJ K hsep hcyc) h
    rwa [adJ_mul K hsep hcyc, adJ_mul K hsep hcyc, adJ_adJ K hsep hcyc s] at h2

end AdJ

/-! ## Part II: `J_ξ (a ⊗ b) J_ξ = (J_ω a J_ω) ⊗ (J_{ω'} b J_{ω'})`

The one place the factorisation `J_ξ = J_ω ⊗ J_{ω'}` is used.  Both sides are bounded
ℂ-linear operators, so it is enough to check them on elementary tensors. -/

section Factor

variable {ℋ 𝒦 : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (N : StarSubalgebra ℂ (𝒦 →L[ℂ] 𝒦))
variable (ω : ℋ) (ω' : 𝒦)
variable (hcycM : IsCyclicVector M ω) (hsepM : IsSeparatingVector M ω)
  (hMbi : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
    = (M : Set (ℋ →L[ℂ] ℋ)))
variable (hcycN : IsCyclicVector N ω') (hsepN : IsSeparatingVector N ω')
  (hNbi : commutant (𝒦 →L[ℂ] 𝒦) (commutant (𝒦 →L[ℂ] 𝒦) (N : Set (𝒦 →L[ℂ] 𝒦)))
    = (N : Set (𝒦 →L[ℂ] 𝒦)))

include hcycM hsepM hMbi hcycN hsepN hNbi

/-- **`J_ξ = J_ω ⊗ J_{ω'}`**, restated for the bare conjugation `J` (which depends only on
the standard subspace, not on the proofs that it is standard). -/
theorem J_htmul (ζ : ℋ) (ζ' : 𝒦) :
    J (Ksub (vnTensor M N) (ω ⊗ₕ ω')) (ζ ⊗ₕ ζ')
      = J (Ksub M ω) ζ ⊗ₕ J (Ksub N ω') ζ' := by
  -- via the `@[simp]` unfolder rather than by definitional unfolding of `modularConj`
  simpa only [modularConj_apply] using
    modularConj_htmul M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi ζ ζ'

variable (hsM : Ksub M ω ⊓ (Ksub M ω).mulI = ⊥) (hcM : Ksub M ω ⊔ (Ksub M ω).mulI = ⊤)
variable (hsN : Ksub N ω' ⊓ (Ksub N ω').mulI = ⊥) (hcN : Ksub N ω' ⊔ (Ksub N ω').mulI = ⊤)
variable (hsT : Ksub (vnTensor M N) (ω ⊗ₕ ω') ⊓ (Ksub (vnTensor M N) (ω ⊗ₕ ω')).mulI = ⊥)
variable (hcT : Ksub (vnTensor M N) (ω ⊗ₕ ω') ⊔ (Ksub (vnTensor M N) (ω ⊗ₕ ω')).mulI = ⊤)

include hsM hcM hsN hcN hsT hcT

/-- **`J_ξ (a ⊗ b) J_ξ = (J_ω a J_ω) ⊗ (J_{ω'} b J_{ω'})`.** -/
theorem adJ_opTensor (a : ℋ →L[ℂ] ℋ) (b : 𝒦 →L[ℂ] 𝒦) :
    adJ (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT (opTensor a b)
      = opTensor (adJ (Ksub M ω) hsM hcM a) (adJ (Ksub N ω') hsN hcN b) := by
  have hz : adJ (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT (opTensor a b)
      - opTensor (adJ (Ksub M ω) hsM hcM a) (adJ (Ksub N ω') hsN hcN b) = 0 := by
    refine clm_eq_zero_of_span_dense (dense_span_elemTensors (ℋ := ℋ) (𝒦 := 𝒦)) ?_
    rintro _ ⟨ζ, ζ', rfl⟩
    have h1 : adJ (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT (opTensor a b) (ζ ⊗ₕ ζ')
        = opTensor (adJ (Ksub M ω) hsM hcM a) (adJ (Ksub N ω') hsN hcN b) (ζ ⊗ₕ ζ') := by
      rw [adJ_apply, J_htmul M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi,
        opTensor_apply, J_htmul M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi,
        opTensor_apply, adJ_apply, adJ_apply]
    rw [sub_apply, h1, sub_self]
  exact sub_eq_zero.1 hz

end Factor

/-! ## Part III: the generating set

`(M ⊗̄ N)□` and `M ⊗̄ N` in terms of the *set* of elementary tensors `{a ⊗ b}`, which is
what `adJ` can be computed on. -/

section Generators

variable {ℋ 𝒦 : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]

variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (N : StarSubalgebra ℂ (𝒦 →L[ℂ] 𝒦)) in
/-- The generating set `{a ⊗ b : a ∈ M, b ∈ N}` of `M ⊗̄ N`. -/
def elemOps : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) :=
  {x : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦 | ∃ a ∈ M, ∃ b ∈ N, x = opTensor a b}

variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (N : StarSubalgebra ℂ (𝒦 →L[ℂ] 𝒦))

/-- `(M ⊗̄ N)□ = {a ⊗ b}□`. -/
theorem commutant_vnTensor_elemOps :
    commutant (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) (vnTensor M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦))
      = commutant (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) (elemOps M N) := by
  rw [commutant_vnTensor, coe_spatialSpan, commutant_span]
  rfl

/-- `M ⊗̄ N = {a ⊗ b}□□`. -/
theorem vnTensor_eq_bicommutant_elemOps :
    (vnTensor M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦))
      = commutant (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)
          (commutant (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) (elemOps M N)) := by
  rw [← commutant_vnTensor_elemOps, bicommutant_vnTensor]

end Generators

/-! ## Part IV: the commutation theorem, cyclic and separating case -/

section Main

variable {ℋ 𝒦 : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (N : StarSubalgebra ℂ (𝒦 →L[ℂ] 𝒦))
variable (ω : ℋ) (ω' : 𝒦)
variable (hcycM : IsCyclicVector M ω) (hsepM : IsSeparatingVector M ω)
  (hMbi : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
    = (M : Set (ℋ →L[ℂ] ℋ)))
variable (hcycN : IsCyclicVector N ω') (hsepN : IsSeparatingVector N ω')
  (hNbi : commutant (𝒦 →L[ℂ] 𝒦) (commutant (𝒦 →L[ℂ] 𝒦) (N : Set (𝒦 →L[ℂ] 𝒦)))
    = (N : Set (𝒦 →L[ℂ] 𝒦)))

include hcycM hsepM hMbi hcycN hsepN hNbi

/-- **`J_ξ` carries the elementary tensors of `M ⊙ N` onto those of `M□ ⊙ N□`.** -/
theorem adJ_image_elemOps
    (hsM : Ksub M ω ⊓ (Ksub M ω).mulI = ⊥) (hcM : Ksub M ω ⊔ (Ksub M ω).mulI = ⊤)
    (hsN : Ksub N ω' ⊓ (Ksub N ω').mulI = ⊥) (hcN : Ksub N ω' ⊔ (Ksub N ω').mulI = ⊤)
    (hsT : Ksub (vnTensor M N) (ω ⊗ₕ ω') ⊓ (Ksub (vnTensor M N) (ω ⊗ₕ ω')).mulI = ⊥)
    (hcT : Ksub (vnTensor M N) (ω ⊗ₕ ω') ⊔ (Ksub (vnTensor M N) (ω ⊗ₕ ω')).mulI = ⊤) :
    (fun x => adJ (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT x) '' elemOps M N
      = elemOps (commutantSA M) (commutantSA N) := by
  have hJM : (fun x => adJ (Ksub M ω) hsM hcM x) '' (M : Set (ℋ →L[ℂ] ℋ))
      = commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)) :=
    tomita_JMJ_unconditional M ω hsM hcM hcycM (dense_commutant_orbit M ω hsepM hMbi) hMbi
  have hJN : (fun x => adJ (Ksub N ω') hsN hcN x) '' (N : Set (𝒦 →L[ℂ] 𝒦))
      = commutant (𝒦 →L[ℂ] 𝒦) (N : Set (𝒦 →L[ℂ] 𝒦)) :=
    tomita_JMJ_unconditional N ω' hsN hcN hcycN (dense_commutant_orbit N ω' hsepN hNbi) hNbi
  ext z
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine ⟨adJ (Ksub M ω) hsM hcM a, ?_, adJ (Ksub N ω') hsN hcN b, ?_, ?_⟩
    · show adJ (Ksub M ω) hsM hcM a ∈ commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ))
      rw [← hJM]; exact ⟨a, ha, rfl⟩
    · show adJ (Ksub N ω') hsN hcN b ∈ commutant (𝒦 →L[ℂ] 𝒦) (N : Set (𝒦 →L[ℂ] 𝒦))
      rw [← hJN]; exact ⟨b, hb, rfl⟩
    · exact adJ_opTensor M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi hsM hcM hsN hcN hsT hcT a b
  · rintro ⟨a', ha', b', hb', rfl⟩
    have ha'' : a' ∈ (fun x => adJ (Ksub M ω) hsM hcM x) '' (M : Set (ℋ →L[ℂ] ℋ)) := by
      rw [hJM]; exact ha'
    have hb'' : b' ∈ (fun x => adJ (Ksub N ω') hsN hcN x) '' (N : Set (𝒦 →L[ℂ] 𝒦)) := by
      rw [hJN]; exact hb'
    obtain ⟨a, ha, rfl⟩ := ha''
    obtain ⟨b, hb, rfl⟩ := hb''
    exact ⟨opTensor a b, ⟨a, ha, b, hb, rfl⟩,
      adJ_opTensor M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi hsM hcM hsN hcN hsT hcT a b⟩

/-- **The commutation theorem, cyclic and separating case**, in `ModularTensor.lean`'s
`vnTensor` vocabulary: `(M ⊗̄ N)□ = M□ ⊗̄ N□`. -/
theorem commutant_vnTensor_eq_vnTensor_commutant :
    commutant (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) (vnTensor M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦))
      = (vnTensor (commutantSA M) (commutantSA N) : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) := by
  obtain ⟨hsM, hcM⟩ := isStandard M ω hcycM hsepM hMbi
  obtain ⟨hsN, hcN⟩ := isStandard N ω' hcycN hsepN hNbi
  obtain ⟨hsT, hcT⟩ := isStandard_vnTensor M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi
  -- Tomita for `M ⊗̄ N` at `ξ = ω ⊗ ω'`
  have hJT : (fun x => adJ (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT x) ''
        (vnTensor M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦))
      = commutant (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) (vnTensor M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) :=
    tomita_JMJ_unconditional (vnTensor M N) (ω ⊗ₕ ω') hsT hcT
      (isCyclicVector_vnTensor M N ω ω' hcycM hcycN)
      (dense_commutant_orbit (vnTensor M N) (ω ⊗ₕ ω')
        (isSeparatingVector_vnTensor M N ω ω' hsepM hMbi hsepN hNbi)
        (bicommutant_vnTensor M N))
      (bicommutant_vnTensor M N)
  rw [← hJT, vnTensor_eq_bicommutant_elemOps M N,
    adJ_image_commutant (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT,
    adJ_image_commutant (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT,
    adJ_image_elemOps M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi hsM hcM hsN hcN hsT hcT,
    ← vnTensor_eq_bicommutant_elemOps]

end Main

/-! ## Part V: the statement in `A/Proc/Commutation.lean`'s vocabulary

`concreteTensor` and `vnTensor` are `W*` of the same generating set, so the theorem of
Part IV *is* `CT M N`. -/

section CTForm

variable {ℋ 𝒦 : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]

/-- `ModularTensor.lean`'s `vnTensor` and `QuantumLambda.lean`'s `concreteTensor` are the
same von Neumann algebra: both are `W*(𝒜 ⊙ ℬ)`. -/
theorem concreteTensor_eq_vnTensor (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ))
    (N : StarSubalgebra ℂ (𝒦 →L[ℂ] 𝒦)) :
    concreteTensor ℋ 𝒦 M N = vnTensor M N :=
  concreteTensor_eq_wstar_spatialSpan M N

/-- `Commutation.lean`'s bundled commutant agrees with `Tomita.lean`'s. -/
theorem vnComm_eq_commutantSA (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) :
    vnComm M = commutantSA M :=
  SetLike.ext' (by rw [coe_vnComm, coe_commutantSA])

variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (N : StarSubalgebra ℂ (𝒦 →L[ℂ] 𝒦))
variable (ω : ℋ) (ω' : 𝒦)

/-- **The commutation theorem for a pair of von Neumann algebras with cyclic and separating
vectors**, in the form `CT` of `A/Proc/Commutation.lean`:
`(𝒜 ⊗̄ ℬ)□ = 𝒜□ ⊗̄ ℬ□` for the concrete tensor product.

The hypotheses are `M□□ = M`, `N□□ = N` and cyclicity and separatingness of `ω`, `ω'`;
`CT_of_cyclicSeparating` below is the same statement with `IsVNSubalgebra` in place of the
two bicommutant equations. -/
theorem CT_of_cyclicSeparating_bicommutant
    (hcycM : IsCyclicVector M ω) (hsepM : IsSeparatingVector M ω)
    (hMbi : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)))
    (hcycN : IsCyclicVector N ω') (hsepN : IsSeparatingVector N ω')
    (hNbi : commutant (𝒦 →L[ℂ] 𝒦) (commutant (𝒦 →L[ℂ] 𝒦) (N : Set (𝒦 →L[ℂ] 𝒦)))
      = (N : Set (𝒦 →L[ℂ] 𝒦))) :
    CT M N := by
  show vnComm (concreteTensor ℋ 𝒦 M N) = concreteTensor ℋ 𝒦 (vnComm M) (vnComm N)
  rw [concreteTensor_eq_vnTensor, concreteTensor_eq_vnTensor, vnComm_eq_commutantSA M,
    vnComm_eq_commutantSA N]
  refine SetLike.ext' ?_
  rw [coe_vnComm]
  exact commutant_vnTensor_eq_vnTensor_commutant M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi

/-- **The commutation theorem for a pair of von Neumann algebras with cyclic and separating
vectors.**  `(𝒜 ⊗̄ ℬ)□ = 𝒜□ ⊗̄ ℬ□`, `⊗̄` the concrete tensor product. -/
theorem CT_of_cyclicSeparating
    (hM : IsVNSubalgebra (ℋ →L[ℂ] ℋ) M) (hN : IsVNSubalgebra (𝒦 →L[ℂ] 𝒦) N)
    (hcycM : IsCyclicVector M ω) (hsepM : IsSeparatingVector M ω)
    (hcycN : IsCyclicVector N ω') (hsepN : IsSeparatingVector N ω') :
    CT M N := by
  have hMbi : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)) := by
    have h := congrArg (fun S : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ) => (S : Set (ℋ →L[ℂ] ℋ)))
      (vnComm_vnComm M hM)
    simpa [coe_vnComm] using h
  have hNbi : commutant (𝒦 →L[ℂ] 𝒦) (commutant (𝒦 →L[ℂ] 𝒦) (N : Set (𝒦 →L[ℂ] 𝒦)))
      = (N : Set (𝒦 →L[ℂ] 𝒦)) := by
    have h := congrArg (fun S : StarSubalgebra ℂ (𝒦 →L[ℂ] 𝒦) => (S : Set (𝒦 →L[ℂ] 𝒦)))
      (vnComm_vnComm N hN)
    simpa [coe_vnComm] using h
  exact CT_of_cyclicSeparating_bicommutant M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi

end CTForm

end Theses.RvD
