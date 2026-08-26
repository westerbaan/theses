/-
Thesis A, chapter "Assorted Structure in W*_cpsu" (proc.tex), parsec 1250:
**125IV** `equaliser-lemma` (proc.tex:4852, Lemma (Kornell)), proved from
**121II** `intersection-tensor` taken as an explicit hypothesis.
-/
import Theses.A.Proc.QuantumLambda

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
  TensorProduct ENNReal Cardinal
open Filter Topology Theses Theses.A.VN Cardinal

noncomputable section

namespace Theses.A.Proc

universe u v w

section Polarisation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The polarisation identity in the form used by proc.tex:4930
(`eq:polarisation-equaliser`): the off-diagonal matrix entry `⟪ξ, T ζ⟫` is
a combination of the four diagonal entries `⟪i^m ξ + ζ, T (i^m ξ + ζ)⟫`. -/
theorem inner_polarisation (T : H →L[ℂ] H) (ξ ζ : H) :
    ⟪ξ + ζ, T (ξ + ζ)⟫
        + Complex.I * ⟪Complex.I • ξ + ζ, T (Complex.I • ξ + ζ)⟫
        - ⟪(-1 : ℂ) • ξ + ζ, T ((-1 : ℂ) • ξ + ζ)⟫
        - Complex.I * ⟪(-Complex.I) • ξ + ζ, T ((-Complex.I) • ξ + ζ)⟫
      = 4 * ⟪ξ, T ζ⟫ := by
  have hexp : ∀ c : ℂ, ⟪c • ξ + ζ, T (c • ξ + ζ)⟫
      = (starRingEnd ℂ) c * c * ⟪ξ, T ξ⟫ + (starRingEnd ℂ) c * ⟪ξ, T ζ⟫
        + c * ⟪ζ, T ξ⟫ + ⟪ζ, T ζ⟫ := by
    intro c
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right]
    ring
  have h1 : ⟪ξ + ζ, T (ξ + ζ)⟫ = ⟪(1 : ℂ) • ξ + ζ, T ((1 : ℂ) • ξ + ζ)⟫ := by
    rw [one_smul]
  rw [h1, hexp, hexp, hexp, hexp]
  simp only [map_one, Complex.conj_I, map_neg, neg_neg]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (2 * ⟪ζ, T ξ⟫ - 2 * ⟪ξ, T ζ⟫) * hI

end Polarisation


/-! ## Copied infrastructure

`QuantumLambda.lean` proves the following auxiliaries but keeps them
`private`, so they are unavailable by name from another module.  They are
reproduced verbatim here inside the namespace `EqL`; nothing in this block
is new mathematics. -/

namespace EqL

variable {A B C D : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- `x ↦ u * x * v` is ultraweakly continuous. -/
theorem continuous_uw_mulmul {X : Type*} [CStarAlgebra X] [PartialOrder X]
    [StarOrderedRing X] [VonNeumannAlgebra X] (u v : X) :
    @Continuous X X (ultraweak X) (ultraweak X) (fun x => u * x * v) :=
  continuous_ultraweak_of_forall _ fun ω => continuous_ultraweak_conj ω u v

/-- `z ↦ z·1` is monotone on the complex order. -/
theorem algebraMap_complex_mono [VonNeumannAlgebra A] {z w : ℂ} (h : z ≤ w) :
    algebraMap ℂ A z ≤ algebraMap ℂ A w := by
  have h0 : (0:ℂ) ≤ w - z := sub_nonneg.mpr h
  obtain ⟨hre, him⟩ := Complex.le_def.mp h0
  have hd : w - z = (((w - z).re : ℝ) : ℂ) := by
    refine Complex.ext (by simp) ?_
    simp only [Complex.ofReal_im]
    simpa using him.symm
  rw [← sub_nonneg, ← map_sub, hd]
  exact Theses.A.CStar.algebraMap_ofReal_nonneg (by simpa using hre)

/-- The scalar map `a ↦ ω(a)·1` as a positive linear map. -/
def npScalarP [VonNeumannAlgebra A] (ω : NPFunctional A) : A →ₚ[ℂ] A where
  toFun a := algebraMap ℂ A (ω a)
  map_add' x y := by
    show algebraMap ℂ A (ω (x + y)) = _
    rw [npFunctional_add, map_add]
  map_smul' r x := by
    show algebraMap ℂ A (ω (r • x)) = _
    rw [show (ω (r • x) : ℂ) = r * ω x from ω.toPositiveLinearMap.map_smul r x,
      map_mul, ← Algebra.smul_def]
    rfl
  monotone' x y h :=
    algebraMap_complex_mono (ω.toPositiveLinearMap.monotone h)

@[simp] theorem npScalarP_apply [VonNeumannAlgebra A] (ω : NPFunctional A) (a : A) :
    npScalarP ω a = algebraMap ℂ A (ω a) := rfl

theorem npScalarP_cp [VonNeumannAlgebra A] (ω : NPFunctional A) :
    Theses.A.CStar.IsCompletelyPositiveMap
      ((npScalarP ω : A →ₚ[ℂ] A) : A →ₗ[ℂ] A) := by
  have h1 : Theses.A.CStar.IsCompletelyPositiveMap (npLin ω) :=
    Theses.A.CStar.cp_commutative_cod (npLin ω)
      (fun a ha => npFunctional_nonneg ω ha)
  have h2 : Theses.A.CStar.IsCompletelyPositiveMap (Algebra.linearMap ℂ A) :=
    Theses.A.CStar.cp_of_mi (Algebra.linearMap ℂ A)
      (fun x y => by
        show algebraMap ℂ A (x * y) = algebraMap ℂ A x * algebraMap ℂ A y
        rw [map_mul])
      (fun x => by
        show algebraMap ℂ A (star x) = star (algebraMap ℂ A x)
        rw [algebraMap_star_comm])
  exact Theses.A.CStar.cp_comp (npLin ω) (Algebra.linearMap ℂ A) h1 h2

theorem npScalarP_normal [VonNeumannAlgebra A] (ω : NPFunctional A) :
    PreservesDirSups ⇑(npScalarP (A := A) ω) := by
  let _ : TopologicalSpace A := ultraweak A
  refine ((p_uwcont (npScalarP ω)).out 0 2).mp ?_
  refine continuous_ultraweak_of_forall _ fun ν => ?_
  have heq : (fun a : A => (ν (npScalarP ω a) : ℂ))
      = fun a : A => (ν 1 : ℂ) * (ω a : ℂ) := by
    funext a
    show (ν (algebraMap ℂ A (ω a)) : ℂ) = _
    rw [Algebra.algebraMap_eq_smul_one,
      show (ν ((ω a : ℂ) • (1:A)) : ℂ) = (ω a : ℂ) * ν 1 from
        ν.toPositiveLinearMap.map_smul _ _]
    ring
  rw [heq]
  exact continuous_const.mul (continuous_ultraweak_npFunctional ω)

/-- The scalar map as an ncp-map. -/
def npScalar [VonNeumannAlgebra A] (ω : NPFunctional A) : NCPMap A A where
  toCompletelyPositiveMap :=
    { toLinearMap := (npScalarP ω : A →ₗ[ℂ] A)
      map_cstarMatrix_nonneg' :=
        (Theses.A.CStar.cp_iff ((npScalarP ω : A →ₚ[ℂ] A) : A →ₗ[ℂ] A)).out 0 1
          |>.mp (npScalarP_cp ω) }
  preservesDirSups' := npScalarP_normal ω

@[simp] theorem npScalar_apply [VonNeumannAlgebra A] (ω : NPFunctional A) (a : A) :
    npScalar ω a = algebraMap ℂ A (ω a) := rfl

theorem vtmulLeft_add [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (a a' : A) : (a + a') ⊗ᵥ (1 : B) = a ⊗ᵥ (1 : B) + a' ⊗ᵥ (1 : B) := by
  show (vnTensor A B).map (a + a') 1 = _
  rw [map_add]
  rfl

theorem vtmulLeft_smul [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (r : ℂ) (a : A) : (r • a) ⊗ᵥ (1 : B) = r • (a ⊗ᵥ (1 : B)) := by
  show (vnTensor A B).map (r • a) 1 = _
  rw [map_smul]
  rfl

theorem vtmulLeft_mono [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {x y : A} (h : x ≤ y) : x ⊗ᵥ (1 : B) ≤ y ⊗ᵥ (1 : B) := by
  have h1 := vtmul_nonneg (y - x) (1 : B) (sub_nonneg.mpr h) zero_le_one
  have h2 : ((y - x) ⊗ᵥ (1 : B)) = y ⊗ᵥ (1 : B) - x ⊗ᵥ (1 : B) := by
    show (vnTensor A B).map (y - x) 1 = _
    rw [map_sub]
    rfl
  rw [h2] at h1
  exact sub_nonneg.mp h1

def pmapTmulLeft (A B : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra A] [VonNeumannAlgebra B] :
    A →ₚ[ℂ] VNT A B where
  toFun a := a ⊗ᵥ (1 : B)
  map_add' := vtmulLeft_add
  map_smul' := vtmulLeft_smul
  monotone' _ _ h := vtmulLeft_mono h

theorem preservesDirSups_vtmulLeft [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] :
    PreservesDirSups (fun a : A => a ⊗ᵥ (1 : B)) :=
  ((p_uwcont (pmapTmulLeft A B)).out 0 2).mp
    (continuous_ultraweak_vtmul_left (1 : B))

/-- The left slice `a ↦ a ⊗ 1` as an nmiu-map. -/
def nmiuTmulLeft (A B : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra A] [VonNeumannAlgebra B] :
    NMIUMap A (VNT A B) where
  toStarAlgHom :=
    { toFun := fun a => a ⊗ᵥ (1 : B)
      map_one' := (vnTensor A B).isTensorProduct.miu.1
      map_mul' := fun x y => by
        have h := (vnTensor A B).isTensorProduct.miu.2.1 x y (1 : B) (1 : B)
        rwa [one_mul] at h
      map_zero' := by
        show (vnTensor A B).map 0 1 = 0
        rw [map_zero]
        rfl
      map_add' := vtmulLeft_add
      commutes' := fun r => by
        have hone : ((1 : A) ⊗ᵥ (1 : B)) = (1 : VNT A B) :=
          (vnTensor A B).isTensorProduct.miu.1
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          vtmulLeft_smul, hone]
      map_star' := fun a => by
        have h := (vnTensor A B).isTensorProduct.miu.2.2 a (1 : B)
        rw [star_one] at h
        exact h.symm }
  preservesDirSups' := preservesDirSups_vtmulLeft

@[simp] theorem nmiuTmulLeft_apply [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (a : A) :
    nmiuTmulLeft A B a = a ⊗ᵥ (1 : B) := rfl

theorem nmiuTmulLeft_injective [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [Nontrivial B] : Function.Injective ⇑(nmiuTmulLeft A B) := by
  intro x y hxy
  have h0 : (x - y) ⊗ᵥ (1 : B) = 0 := by
    have h2 : ((x - y) ⊗ᵥ (1 : B)) = x ⊗ᵥ (1 : B) - y ⊗ᵥ (1 : B) := by
      show (vnTensor A B).map (x - y) 1 = _
      rw [map_sub]
      rfl
    rw [h2, show (x ⊗ᵥ (1 : B)) = nmiuTmulLeft A B x from rfl,
      show (y ⊗ᵥ (1 : B)) = nmiuTmulLeft A B y from rfl, hxy, sub_self]
  have hn : ‖x - y‖ * ‖(1 : B)‖ = 0 := by
    rw [← norm_vtmul, h0, norm_zero]
  rw [norm_one, mul_one, norm_eq_zero, sub_eq_zero] at hn
  exact hn

theorem vnt_subsingleton {Cc Aa : Type*} [CStarAlgebra Cc] [PartialOrder Cc]
    [StarOrderedRing Cc] [VonNeumannAlgebra Cc] [CStarAlgebra Aa] [PartialOrder Aa]
    [StarOrderedRing Aa] [VonNeumannAlgebra Aa] [Subsingleton Aa] :
    Subsingleton (VNT Cc Aa) := by
  have h1 : ((1 : Cc) ⊗ᵥ (1 : Aa)) = 1 := (vnTensor Cc Aa).isTensorProduct.miu.1
  have h0 : ((1 : Cc) ⊗ᵥ (1 : Aa)) = 0 := by
    rw [show (1 : Aa) = 0 from Subsingleton.elim _ _]
    exact map_zero ((vnTensor Cc Aa).map 1)
  exact subsingleton_of_zero_eq_one (h1.symm.trans h0).symm

/-- Into a trivial von Neumann algebra there is an nmiu-map from anywhere. -/
def nmiuOfSubsingleton (Z₁ : Type v) (Z₂ : Type w)
    [CStarAlgebra Z₁] [PartialOrder Z₁] [StarOrderedRing Z₁]
    [CStarAlgebra Z₂] [PartialOrder Z₂] [StarOrderedRing Z₂] [Subsingleton Z₂] :
    NMIUMap Z₁ Z₂ where
  toStarAlgHom :=
    { toFun := fun _ => 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      map_zero' := Subsingleton.elim _ _
      map_add' := fun _ _ => Subsingleton.elim _ _
      commutes' := fun _ => Subsingleton.elim _ _
      map_star' := fun _ => Subsingleton.elim _ _ }
  preservesDirSups' := fun _ _ _ _ _ =>
    ⟨fun _ _ => le_of_eq (Subsingleton.elim _ _),
      fun _ _ => le_of_eq (Subsingleton.elim _ _)⟩

/-- The preimage of a von Neumann subalgebra along a normal ∗-hom. -/
theorem isVNSubalgebra_comap {X Y : Type u} [CStarAlgebra X] [PartialOrder X]
    [StarOrderedRing X] [VonNeumannAlgebra X] [CStarAlgebra Y] [PartialOrder Y]
    [StarOrderedRing Y] [VonNeumannAlgebra Y]
    (θ : X →⋆ₐ[ℂ] Y) (hθ : PreservesDirSups ⇑θ) (S : StarSubalgebra ℂ Y)
    (hS : IsVNSubalgebra Y S) : IsVNSubalgebra X (S.comap θ) := by
  have hsa : ∀ d : selfAdjoint X, IsSelfAdjoint (θ (d : X)) := by
    intro d
    show star (θ (d : X)) = θ (d : X)
    rw [← map_star, d.2.star_eq]
  constructor
  · have hc : Continuous ⇑θ :=
      AddMonoidHomClass.continuous_of_bound θ 1 fun a => by
        simpa using Theses.A.CStar.norm_mi_map_contractive θ a
    exact hS.isClosed.preimage hc
  · intro D s hDS hne hdir hlub
    set G : Set (selfAdjoint Y) :=
      (fun d : selfAdjoint X => (⟨θ (d : X), hsa d⟩ : selfAdjoint Y)) '' D with hG
    have hval : Subtype.val '' G = (fun d : selfAdjoint X => θ (d : X)) '' D := by
      rw [hG, ← Set.image_comp]; rfl
    have hlubG : IsLUB G (⟨θ (s : X), hsa s⟩ : selfAdjoint Y) := by
      refine isLUB_sa_of_isLUB ?_
      rw [hval]
      exact hθ D s hne hdir hlub
    have hGne : G.Nonempty := hne.image _
    have hGdir : DirectedOn (· ≤ ·) G := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
      exact ⟨_, ⟨c, hc, rfl⟩,
        Subtype.coe_le_coe.mp (starAlgHom_mono' θ (Subtype.coe_le_coe.mpr hac)),
        Subtype.coe_le_coe.mp (starAlgHom_mono' θ (Subtype.coe_le_coe.mpr hbc))⟩
    exact hS.dirSup_mem G _ (fun d hd => by
      obtain ⟨e, he, rfl⟩ := hd
      exact hDS e he) hGne hGdir hlubG

theorem tmapM_injective {A₁ A₂ B₁ B₂ : Type u}
    [CStarAlgebra A₁] [PartialOrder A₁] [StarOrderedRing A₁] [VonNeumannAlgebra A₁]
    [CStarAlgebra A₂] [PartialOrder A₂] [StarOrderedRing A₂] [VonNeumannAlgebra A₂]
    [CStarAlgebra B₁] [PartialOrder B₁] [StarOrderedRing B₁] [VonNeumannAlgebra B₁]
    [CStarAlgebra B₂] [PartialOrder B₂] [StarOrderedRing B₂] [VonNeumannAlgebra B₂]
    (f : NMIUMap A₁ A₂) (g : NMIUMap B₁ B₂) (hf : Function.Injective ⇑f)
    (hg : Function.Injective ⇑g) : Function.Injective ⇑(tmapM f g) :=
  tensor_injective f g hf hg (nmiuNCP (tmapM f g)) (fun a b => tmapM_apply f g a b)


/-- A von Neumann subalgebra of a von Neumann subalgebra is one of the
ambient algebra. -/
theorem vnsub_isVNSubalgebra_map [VonNeumannAlgebra A]
    {S : StarSubalgebra ℂ A} {hS : IsVNSubalgebra A S}
    (T : StarSubalgebra ℂ (VNSub A S hS)) (hT : IsVNSubalgebra (VNSub A S hS) T) :
    IsVNSubalgebra A (T.map (VNSub.valStarAlgHom (A := A) (S := S) (hS := hS))) := by
  have hce := (AddMonoidHomClass.isometry_of_norm
    (VNSub.valAddHom (A := A) (S := S) (hS := hS)) (fun _ => rfl)).isClosedEmbedding
  have hmem : ∀ x : A, x ∈ T.map (VNSub.valStarAlgHom (A := A) (S := S) (hS := hS)) ↔
      ∃ t : VNSub A S hS, t ∈ T ∧ t.val = x := by
    intro x
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  constructor
  · have hcoe : ((T.map (VNSub.valStarAlgHom (A := A) (S := S) (hS := hS))) : Set A)
        = VNSub.val '' (T : Set (VNSub A S hS)) := by
      ext x
      simp only [Set.mem_image, SetLike.mem_coe, hmem]
    rw [hcoe]
    exact hce.isClosedMap _ hT.isClosed
  · intro D s hDS hne hdir hlub
    have hlift : ∀ d ∈ D, ∃ t : selfAdjoint (VNSub A S hS),
        t.1 ∈ T ∧ VNSub.saMap t = d := by
      intro d hd
      obtain ⟨t, ht, hte⟩ := (hmem _).mp (hDS d hd)
      refine ⟨⟨t, ?_⟩, ht, Subtype.ext hte⟩
      exact VNSub.val_injective (by rw [VNSub.val_star, hte]; exact d.2)
    have hsS : (s : A) ∈ S := by
      refine hS.dirSup_mem D s (fun d hd => ?_) hne hdir hlub
      obtain ⟨t, ht, hte⟩ := hlift d hd
      exact hte ▸ t.1.property
    set s' : selfAdjoint (VNSub A S hS) :=
      ⟨⟨(s : A), hsS⟩, VNSub.val_injective s.2⟩ with hs'
    set D' : Set (selfAdjoint (VNSub A S hS)) :=
      {t | t.1 ∈ T ∧ VNSub.saMap t ∈ D} with hD'
    have hD'ne : D'.Nonempty := by
      obtain ⟨d, hd⟩ := hne
      obtain ⟨t, ht, hte⟩ := hlift d hd
      exact ⟨t, ht, hte ▸ hd⟩
    have hD'dir : DirectedOn (· ≤ ·) D' := by
      rintro t ⟨htT, htD⟩ u ⟨huT, huD⟩
      obtain ⟨v, hv, htv, huv⟩ := hdir _ htD _ huD
      obtain ⟨w, hw, hwe⟩ := hlift v hv
      exact ⟨w, ⟨hw, hwe ▸ hv⟩, by rw [← hwe] at htv; exact htv,
        by rw [← hwe] at huv; exact huv⟩
    have hD'lub : IsLUB D' s' := by
      constructor
      · rintro t ⟨-, htD⟩
        exact hlub.1 htD
      · intro u hu
        have h2 : s ≤ VNSub.saMap u := by
          refine hlub.2 ?_
          intro d hd
          obtain ⟨t, ht, hte⟩ := hlift d hd
          exact hte ▸ hu ⟨ht, hte ▸ hd⟩
        exact h2
    have := hT.dirSup_mem D' s' (fun t ht => ht.1) hD'ne hD'dir hD'lub
    exact (hmem _).mpr ⟨s'.1, this, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **The two-sided abstract form of 121II**: granted the concrete 121II,
for von Neumann subalgebras `𝒮₁, 𝒮₂ ⊆ 𝒜` and `𝒯₁, 𝒯₂ ⊆ 𝒞`,
`(𝒮₁ ⊗ 𝒯₁) ∩ (𝒮₂ ⊗ 𝒯₂) = (𝒮₁ ∩ 𝒮₂) ⊗ (𝒯₁ ∩ 𝒯₂)` inside the chosen
tensor product `𝒜 ⊗ 𝒞`.

This is `tensorSub_inf_of_intersectionTensorStatement` of
`QuantumLambda.lean` with both factors allowed to vary; 125IV needs the
two-sided form, because the intersection it takes is
`(𝒜̃ ⊗ B(ℋ)) ∩ (𝒜 ⊗ 𝒞)`. -/
theorem tensorSub₂_inf_of_intersectionTensorStatement
    {𝒜 𝒞 : Type u}
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
    [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞] [VonNeumannAlgebra 𝒞]
    (h121 : IntersectionTensorStatement.{u})
    (S₁ S₂ : StarSubalgebra ℂ 𝒜) (hS₁ : IsVNSubalgebra 𝒜 S₁)
    (hS₂ : IsVNSubalgebra 𝒜 S₂)
    (T₁ T₂ : StarSubalgebra ℂ 𝒞) (hT₁ : IsVNSubalgebra 𝒞 T₁)
    (hT₂ : IsVNSubalgebra 𝒞 T₂) :
    tensorSub₂ S₁ T₁ ⊓ tensorSub₂ S₂ T₂ = tensorSub₂ (S₁ ⊓ S₂) (T₁ ⊓ T₂) := by
  obtain ⟨ι, f, SA, hSA, hfmem, hfsurj, hfinj⟩ := ngns_ulift.{u, u} 𝒜
  obtain ⟨κ, g, SB, hSB, hgmem, hgsurj, hginj⟩ := ngns_ulift.{u, u} 𝒞
  set u₀ := nmiuCorestrict f SA hSA hfmem with hu₀
  have hu : Function.Bijective ⇑u₀ :=
    nmiuCorestrict_bijective f SA hSA hfmem hfinj hfsurj
  set v₀ := nmiuCorestrict g SB hSB hgmem with hv₀
  have hv : Function.Bijective ⇑v₀ :=
    nmiuCorestrict_bijective g SB hSB hgmem hginj hgsurj
  obtain ⟨Θ, hΘbij, hΘ⟩ := exists_vntEquiv u₀ hu v₀ hv
  -- the four images, first in the bundled subalgebras and then in `B(ℋ)`
  set SA₁ := (S₁.map u₀.toStarAlgHom).map VNSub.valStarAlgHom with hSA₁def
  set SA₂ := (S₂.map u₀.toStarAlgHom).map VNSub.valStarAlgHom with hSA₂def
  set SB₁ := (T₁.map v₀.toStarAlgHom).map VNSub.valStarAlgHom with hSB₁def
  set SB₂ := (T₂.map v₀.toStarAlgHom).map VNSub.valStarAlgHom with hSB₂def
  have hrA₁ : S₁.map u₀.toStarAlgHom = VNSub.restrict hSA SA₁ :=
    (VNSub.restrict_map_val _).symm
  have hrA₂ : S₂.map u₀.toStarAlgHom = VNSub.restrict hSA SA₂ :=
    (VNSub.restrict_map_val _).symm
  have hrB₁ : T₁.map v₀.toStarAlgHom = VNSub.restrict hSB SB₁ :=
    (VNSub.restrict_map_val _).symm
  have hrB₂ : T₂.map v₀.toStarAlgHom = VNSub.restrict hSB SB₂ :=
    (VNSub.restrict_map_val _).symm
  have hVNA₁ : IsVNSubalgebra _ SA₁ :=
    vnsub_isVNSubalgebra_map _ (isVNSubalgebra_nmiu_map u₀ hu S₁ hS₁)
  have hVNA₂ : IsVNSubalgebra _ SA₂ :=
    vnsub_isVNSubalgebra_map _ (isVNSubalgebra_nmiu_map u₀ hu S₂ hS₂)
  have hVNB₁ : IsVNSubalgebra _ SB₁ :=
    vnsub_isVNSubalgebra_map _ (isVNSubalgebra_nmiu_map v₀ hv T₁ hT₁)
  have hVNB₂ : IsVNSubalgebra _ SB₂ :=
    vnsub_isVNSubalgebra_map _ (isVNSubalgebra_nmiu_map v₀ hv T₂ hT₂)
  have hleA₁ : SA₁ ≤ SA := VNSub.map_val_le _
  have hleA₂ : SA₂ ≤ SA := VNSub.map_val_le _
  have hleB₁ : SB₁ ≤ SB := VNSub.map_val_le _
  have hleB₂ : SB₂ ≤ SB := VNSub.map_val_le _
  have key : ∀ (S : StarSubalgebra ℂ 𝒜) (T : StarSubalgebra ℂ 𝒞) (x : VNT 𝒜 𝒞),
      x ∈ tensorSub₂ S T ↔
        Θ x ∈ tensorSub₂ (S.map u₀.toStarAlgHom) (T.map v₀.toStarAlgHom) :=
    fun S T x => (mem_tensorSub₂_map u₀ v₀ Θ hΘbij hΘ S T x).symm
  have hmain := tensorSub₂_inf_of_intersection_tensor hSA hSB SA₁ SA₂ SB₁ SB₂
    hleA₁ hleA₂ hleB₁ hleB₂ (h121 SA₁ SA₂ SB₁ SB₂ hVNA₁ hVNA₂ hVNB₁ hVNB₂)
  have hA12 : (S₁ ⊓ S₂).map u₀.toStarAlgHom = VNSub.restrict hSA (SA₁ ⊓ SA₂) := by
    rw [starSubalgebra_map_inf u₀ hu, VNSub.restrict_inf, ← hrA₁, ← hrA₂]
  have hB12 : (T₁ ⊓ T₂).map v₀.toStarAlgHom = VNSub.restrict hSB (SB₁ ⊓ SB₂) := by
    rw [starSubalgebra_map_inf v₀ hv, VNSub.restrict_inf, ← hrB₁, ← hrB₂]
  refine SetLike.ext fun x => ?_
  have k1 := key S₁ T₁ x
  have k2 := key S₂ T₂ x
  have k3 := key (S₁ ⊓ S₂) (T₁ ⊓ T₂) x
  rw [hrA₁, hrB₁] at k1
  rw [hrA₂, hrB₂] at k2
  rw [hA12, hB12] at k3
  constructor
  · rintro ⟨h1, h2⟩
    refine k3.mpr ?_
    rw [← hmain]
    exact ⟨k1.mp h1, k2.mp h2⟩
  · intro h
    obtain ⟨h1, h2⟩ := (hmain ▸ k3.mp h : _ ∈ _ ⊓ _)
    exact ⟨k1.mpr h1, k2.mpr h2⟩



/-! ## The slice maps `r_ξ`

For a vector `ξ` of a Hilbert space `ℋ` the thesis's `r_ξ` is the np-map
`𝒜 ⊗ 𝒞 → 𝒜` with `r_ξ(a ⊗ c) = ⟪ξ, cξ⟫ a`.  Here it is rendered as the
ncp-map `𝒜 ⊗ B(ℋ) → 𝒜 ⊗ B(ℋ)` given by `id ⊗ (b ↦ ⟪ξ, bξ⟫·1)`, whose
values all lie in the copy `𝒜 ⊗ 1` of `𝒜`; that avoids having to build
the identification `𝒜 ⊗ ℂ ≅ 𝒜`. -/

section RSlice

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [VonNeumannAlgebra 𝒜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem vtmul_mul_vtmul {C₀ A₀ : Type u} [CStarAlgebra C₀] [PartialOrder C₀]
    [StarOrderedRing C₀] [VonNeumannAlgebra C₀] [CStarAlgebra A₀] [PartialOrder A₀]
    [StarOrderedRing A₀] [VonNeumannAlgebra A₀] (c c' : C₀) (a a' : A₀) :
    (c ⊗ᵥ a) * (c' ⊗ᵥ a') = (c * c') ⊗ᵥ (a * a') :=
  ((vnTensor C₀ A₀).isTensorProduct.miu.2.1 c c' a a').symm

theorem vtmul_smul_right {C₀ A₀ : Type u} [CStarAlgebra C₀] [PartialOrder C₀]
    [StarOrderedRing C₀] [VonNeumannAlgebra C₀] [CStarAlgebra A₀] [PartialOrder A₀]
    [StarOrderedRing A₀] [VonNeumannAlgebra A₀] (c : C₀) (r : ℂ) (a : A₀) :
    c ⊗ᵥ (r • a) = r • (c ⊗ᵥ a) :=
  map_smul ((vnTensor C₀ A₀).map c) r a

variable (𝒜)

/-- The slice `r_ξ`, as an ncp-endomorphism of `𝒜 ⊗ B(ℋ)`. -/
def rSlice (ξ : H) : NCPMap (VNT 𝒜 (H →L[ℂ] H)) (VNT 𝒜 (H →L[ℂ] H)) :=
  tmap (ncpId 𝒜) (npScalar (vectorNP ξ))

theorem rSlice_tmul (ξ : H) (a : 𝒜) (b : H →L[ℂ] H) :
    rSlice 𝒜 ξ (a ⊗ᵥ b) = (⟪ξ, b ξ⟫ : ℂ) • (a ⊗ᵥ (1 : H →L[ℂ] H)) := by
  rw [rSlice, tmap_apply, ncpId_apply, npScalar_apply, vectorNP_apply,
    Algebra.algebraMap_eq_smul_one, vtmul_smul_right]

/-- `r_ξ` as a linear map. -/
def rSliceL (ξ : H) : VNT 𝒜 (H →L[ℂ] H) →ₗ[ℂ] VNT 𝒜 (H →L[ℂ] H) :=
  (rSlice 𝒜 ξ).toCompletelyPositiveMap.toLinearMap

@[simp] theorem rSliceL_apply (ξ : H) (x : VNT 𝒜 (H →L[ℂ] H)) :
    rSliceL 𝒜 ξ x = rSlice 𝒜 ξ x := rfl

theorem rSliceL_continuous (ξ : H) :
    @Continuous (VNT 𝒜 (H →L[ℂ] H)) (VNT 𝒜 (H →L[ℂ] H))
      (ultraweak _) (ultraweak _) ⇑(rSliceL 𝒜 ξ) :=
  ((p_uwcont (ncpPositive (rSlice 𝒜 ξ))).out 2 0).mp (rSlice 𝒜 ξ).preservesDirSups'

/-- Every value of `r_ξ` lies in the copy `𝒜 ⊗ 1` of `𝒜`.  (The argument
of `atE_mem` in `QuantumLambda.lean`: the set of `x` whose image does is an
ultraweakly closed subspace containing the elementary tensors.) -/
theorem rSlice_mem (ξ : H) (x : VNT 𝒜 (H →L[ℂ] H)) :
    ∃ a : 𝒜, rSlice 𝒜 ξ x = a ⊗ᵥ (1 : H →L[ℂ] H) := by
  let _ : TopologicalSpace (VNT 𝒜 (H →L[ℂ] H)) := ultraweak (VNT 𝒜 (H →L[ℂ] H))
  have _ : T2Space (VNT 𝒜 (H →L[ℂ] H)) := vn_positive_basic_1.1
  obtain ⟨hRvn⟩ : Nonempty (IsVNSubalgebra (VNT 𝒜 (H →L[ℂ] H))
      (nmiuTmulLeft 𝒜 (H →L[ℂ] H)).toStarAlgHom.range) :=
    ⟨nmiu_image _⟩
  have hRcl : IsClosed
      ((nmiuTmulLeft 𝒜 (H →L[ℂ] H)).toStarAlgHom.range :
        Set (VNT 𝒜 (H →L[ℂ] H))) := (vnsac _ hRvn).2
  set W : Submodule ℂ (VNT 𝒜 (H →L[ℂ] H)) :=
    Submodule.comap (rSliceL 𝒜 ξ)
      (Subalgebra.toSubmodule
        (nmiuTmulLeft 𝒜 (H →L[ℂ] H)).toStarAlgHom.range.toSubalgebra) with hW
  have hWcl : IsClosed (W : Set (VNT 𝒜 (H →L[ℂ] H))) :=
    hRcl.preimage (rSliceL_continuous 𝒜 ξ)
  have hspan : (Submodule.span ℂ
      {t : VNT 𝒜 (H →L[ℂ] H) | ∃ a b, t = (vnTensor 𝒜 (H →L[ℂ] H)).map a b} :
        Set (VNT 𝒜 (H →L[ℂ] H))) ⊆ (W : Set (VNT 𝒜 (H →L[ℂ] H))) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, b, rfl⟩
    have hmem : rSlice 𝒜 ξ (a ⊗ᵥ b) ∈
        (nmiuTmulLeft 𝒜 (H →L[ℂ] H)).toStarAlgHom.range := by
      rw [rSlice_tmul, ← vtmulLeft_smul]
      exact ⟨(⟪ξ, b ξ⟫ : ℂ) • a, rfl⟩
    exact hmem
  have hx : x ∈ W := by
    have hd := (vnTensor 𝒜 (H →L[ℂ] H)).isTensorProduct.dense
    have hcl : x ∈ closure ((Submodule.span ℂ
        {t : VNT 𝒜 (H →L[ℂ] H) | ∃ a b, t = (vnTensor 𝒜 (H →L[ℂ] H)).map a b} :
          Set (VNT 𝒜 (H →L[ℂ] H)))) := by
      rw [hd.closure_eq]; trivial
    exact hWcl.closure_subset_iff.mpr hspan hcl
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha.symm⟩

end RSlice



/-! ## The rank-one compressions of `𝒜 ⊗ B(ℋ)`

`eq:polarisation-equaliser` of proc.tex:4930: the compression of `x` by the
matrix units `1 ⊗ |e_k⟩⟨e_k|` and `1 ⊗ |e_l⟩⟨e_l|` is a combination of four
values of `r_ξ`, times `1 ⊗ |e_k⟩⟨e_l|`. -/

section Compression

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [VonNeumannAlgebra 𝒜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ιH : Type u}

/-- The polarisation identity, transported into `𝒜 ⊗ B(ℋ)`. -/
theorem tensor_polarisation (e : HilbertBasis ιH ℂ H) (k l : ιH)
    (x : VNT 𝒜 (H →L[ℂ] H)) :
    ((1 : 𝒜) ⊗ᵥ bkU e k k) * x * ((1 : 𝒜) ⊗ᵥ bkU e l l)
      = ((4 : ℂ)⁻¹ • (rSlice 𝒜 (e k + e l) x
            + Complex.I • rSlice 𝒜 (Complex.I • e k + e l) x
            - rSlice 𝒜 ((-1 : ℂ) • e k + e l) x
            - Complex.I • rSlice 𝒜 ((-Complex.I) • e k + e l) x))
          * ((1 : 𝒜) ⊗ᵥ bkU e k l) := by
  let _ : TopologicalSpace (VNT 𝒜 (H →L[ℂ] H)) := ultraweak (VNT 𝒜 (H →L[ℂ] H))
  have _ : T2Space (VNT 𝒜 (H →L[ℂ] H)) := vn_positive_basic_1.1
  set v0 : H := e k + e l with hv0
  set v1 : H := Complex.I • e k + e l with hv1
  set v2 : H := (-1 : ℂ) • e k + e l with hv2
  set v3 : H := (-Complex.I) • e k + e l with hv3
  set Q : VNT 𝒜 (H →L[ℂ] H) →ₗ[ℂ] VNT 𝒜 (H →L[ℂ] H) :=
    (4 : ℂ)⁻¹ • (rSliceL 𝒜 v0 + Complex.I • rSliceL 𝒜 v1 - rSliceL 𝒜 v2
      - Complex.I • rSliceL 𝒜 v3) with hQ
  have hQapp : ∀ y : VNT 𝒜 (H →L[ℂ] H), Q y
      = (4 : ℂ)⁻¹ • (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y
          - rSlice 𝒜 v2 y - Complex.I • rSlice 𝒜 v3 y) := by
    intro y
    rw [hQ]
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      rSliceL_apply]
  set f : VNT 𝒜 (H →L[ℂ] H) →ₗ[ℂ] VNT 𝒜 (H →L[ℂ] H) :=
    (LinearMap.mulRight ℂ ((1 : 𝒜) ⊗ᵥ bkU e l l)).comp
      (LinearMap.mulLeft ℂ ((1 : 𝒜) ⊗ᵥ bkU e k k)) with hf
  set g : VNT 𝒜 (H →L[ℂ] H) →ₗ[ℂ] VNT 𝒜 (H →L[ℂ] H) :=
    (LinearMap.mulRight ℂ ((1 : 𝒜) ⊗ᵥ bkU e k l)).comp Q with hg
  have hcf : Continuous ⇑f := continuous_uw_mulmul _ _
  have hQc : Continuous ⇑Q := by
    refine continuous_ultraweak_of_forall _ fun ν => ?_
    have hcomp : ∀ v : H, @Continuous (VNT 𝒜 (H →L[ℂ] H)) ℂ
        (ultraweak _) _ (fun y => (ν (rSlice 𝒜 v y) : ℂ)) := fun v =>
      (continuous_ultraweak_npFunctional ν).comp (rSliceL_continuous 𝒜 v)
    have hrw : (fun y : VNT 𝒜 (H →L[ℂ] H) => (ν (Q y) : ℂ))
        = fun y => (4 : ℂ)⁻¹ * ((ν (rSlice 𝒜 v0 y) : ℂ)
            + Complex.I * (ν (rSlice 𝒜 v1 y) : ℂ)
            - (ν (rSlice 𝒜 v2 y) : ℂ)
            - Complex.I * (ν (rSlice 𝒜 v3 y) : ℂ)) := by
      funext y
      rw [hQapp y,
        show (ν ((4 : ℂ)⁻¹ • (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y
              - rSlice 𝒜 v2 y - Complex.I • rSlice 𝒜 v3 y)) : ℂ)
            = (4 : ℂ)⁻¹ * ν (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y
              - rSlice 𝒜 v2 y - Complex.I • rSlice 𝒜 v3 y) from
          ν.toPositiveLinearMap.map_smul _ _]
      congr 1
      rw [show (ν (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y
              - rSlice 𝒜 v2 y - Complex.I • rSlice 𝒜 v3 y) : ℂ)
            = ν (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y - rSlice 𝒜 v2 y)
              - ν (Complex.I • rSlice 𝒜 v3 y) from
          map_sub ν.toPositiveLinearMap _ _,
        show (ν (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y - rSlice 𝒜 v2 y) : ℂ)
            = ν (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y)
              - ν (rSlice 𝒜 v2 y) from map_sub ν.toPositiveLinearMap _ _,
        show (ν (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y) : ℂ)
            = ν (rSlice 𝒜 v0 y) + ν (Complex.I • rSlice 𝒜 v1 y) from
          map_add ν.toPositiveLinearMap _ _,
        show (ν (Complex.I • rSlice 𝒜 v1 y) : ℂ)
            = Complex.I * ν (rSlice 𝒜 v1 y) from
          ν.toPositiveLinearMap.map_smul _ _,
        show (ν (Complex.I • rSlice 𝒜 v3 y) : ℂ)
            = Complex.I * ν (rSlice 𝒜 v3 y) from
          ν.toPositiveLinearMap.map_smul _ _]
    rw [hrw]
    exact continuous_const.mul ((((hcomp v0).add
      (continuous_const.mul (hcomp v1))).sub (hcomp v2)).sub
        (continuous_const.mul (hcomp v3)))
  have hcg : Continuous ⇑g := by
    have h1 : Continuous (fun y : VNT 𝒜 (H →L[ℂ] H) =>
        1 * y * ((1 : 𝒜) ⊗ᵥ bkU e k l)) := continuous_uw_mulmul _ _
    simp only [one_mul] at h1
    exact h1.comp hQc
  have hQtmul : ∀ (a : 𝒜) (b : H →L[ℂ] H),
      Q (a ⊗ᵥ b) = (⟪e k, b (e l)⟫ : ℂ) • (a ⊗ᵥ (1 : H →L[ℂ] H)) := by
    intro a b
    rw [hQapp, rSlice_tmul, rSlice_tmul, rSlice_tmul, rSlice_tmul,
      smul_smul, smul_smul, ← add_smul, ← sub_smul, ← sub_smul, smul_smul]
    congr 1
    have hp := inner_polarisation b (e k) (e l)
    rw [hv0, hv1, hv2, hv3]
    linear_combination (4 : ℂ)⁻¹ * hp
  have hfg : f = g := by
    refine tensor_linear_ext (vnTensor 𝒜 (H →L[ℂ] H)).isTensorProduct f g hcf hcg ?_
    intro a b
    show ((1 : 𝒜) ⊗ᵥ bkU e k k) * (a ⊗ᵥ b) * ((1 : 𝒜) ⊗ᵥ bkU e l l)
      = Q (a ⊗ᵥ b) * ((1 : 𝒜) ⊗ᵥ bkU e k l)
    rw [vtmul_mul_vtmul, vtmul_mul_vtmul, one_mul, mul_one, bkU_mul_mul',
      vtmul_smul_right, hQtmul, smul_mul_assoc, vtmul_mul_vtmul, mul_one, one_mul]
  have h : f x = g x :=
    congrFun (congrArg
      (fun L : VNT 𝒜 (H →L[ℂ] H) →ₗ[ℂ] VNT 𝒜 (H →L[ℂ] H) => ⇑L) hfg) x
  have hfx : f x = ((1 : 𝒜) ⊗ᵥ bkU e k k) * x * ((1 : 𝒜) ⊗ᵥ bkU e l l) := rfl
  have hgx : g x = Q x * ((1 : 𝒜) ⊗ᵥ bkU e k l) := rfl
  rw [← hfx, h, hgx, hQapp]


/-! ### `1 ⊗ b` calculus -/

theorem vtmulR_mul (a a' : H →L[ℂ] H) :
    ((1 : 𝒜) ⊗ᵥ a) * ((1 : 𝒜) ⊗ᵥ a') = (1 : 𝒜) ⊗ᵥ (a * a') := by
  rw [vtmul_mul_vtmul, one_mul]

theorem vtmulR_star (a : H →L[ℂ] H) :
    star ((1 : 𝒜) ⊗ᵥ a) = (1 : 𝒜) ⊗ᵥ star a := by
  have h := (vnTensor 𝒜 (H →L[ℂ] H)).isTensorProduct.miu.2.2 (1 : 𝒜) a
  rw [star_one] at h
  exact h

theorem vtmulR_sub (a a' : H →L[ℂ] H) :
    (1 : 𝒜) ⊗ᵥ (a - a') = ((1 : 𝒜) ⊗ᵥ a) - ((1 : 𝒜) ⊗ᵥ a') :=
  map_sub ((vnTensor 𝒜 (H →L[ℂ] H)).map 1) a a'

theorem vtmulR_one : ((1 : 𝒜) ⊗ᵥ (1 : H →L[ℂ] H)) = 1 :=
  (vnTensor 𝒜 (H →L[ℂ] H)).isTensorProduct.miu.1

theorem vtmulR_mono {a a' : H →L[ℂ] H} (h : a ≤ a') :
    ((1 : 𝒜) ⊗ᵥ a) ≤ ((1 : 𝒜) ⊗ᵥ a') := by
  have h1 := vtmul_nonneg (1 : 𝒜) (a' - a) zero_le_one (sub_nonneg.mpr h)
  rw [vtmulR_sub] at h1
  exact sub_nonneg.mp h1

/-- The compressions `1 ⊗ p_F` converge ultraweakly to `1` from both
sides. -/
theorem compress_tendsto (e : HilbertBasis ιH ℂ H) (x : VNT 𝒜 (H →L[ℂ] H)) :
    UWTendsto (fun F : Finset ιH =>
        ((1 : 𝒜) ⊗ᵥ bkP e F) * x * ((1 : 𝒜) ⊗ᵥ bkP e F)) atTop x := by
  have hmain : UWTendsto (fun F : Finset ιH =>
      ((1 : 𝒜) ⊗ᵥ bkP e F) * x * ((1 : 𝒜) ⊗ᵥ bkP e F)) atTop
      ((1 : VNT 𝒜 (H →L[ℂ] H)) * x * 1) := by
    refine uw_compress_tendsto 1 (fun F => (1 : 𝒜) ⊗ᵥ bkP e F)
      (fun F => ?_) (fun F => ?_) (fun F => ?_) ?_ x
    · rw [vtmulR_star, vtmulR_mul, bkP_star, bkP_mul_self]
    · rw [← vtmulR_one, ← vtmulR_sub, vtmulR_star, vtmulR_mul, star_sub, star_one,
        bkP_star]
      congr 1
      rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, bkP_mul_self]
      abel
    · rw [← vtmulR_one]
      exact vtmulR_mono (bkP_le_one e F)
    · let _ : TopologicalSpace (H →L[ℂ] H) := ultraweak (H →L[ℂ] H)
      let _ : TopologicalSpace (VNT 𝒜 (H →L[ℂ] H)) := ultraweak (VNT 𝒜 (H →L[ℂ] H))
      have h : UWTendsto (bkP e) atTop (1 : H →L[ℂ] H) :=
        uwTendsto_of_isLUB (X := H →L[ℂ] H) (ι' := Finset ιH) (bkP e) 1
          (fun F => (bkP_star e F : star (bkP e F) = bkP e F))
          (fun F G hFG => bkP_mono e hFG) (bkP_isLUB e)
      have hcont : @Continuous (H →L[ℂ] H) (VNT 𝒜 (H →L[ℂ] H))
          (ultraweak (H →L[ℂ] H)) (ultraweak (VNT 𝒜 (H →L[ℂ] H)))
          (fun b : H →L[ℂ] H => (1 : 𝒜) ⊗ᵥ b) :=
        continuous_ultraweak_vtmul_right (1 : 𝒜)
      have h2 := (hcont.tendsto (1 : H →L[ℂ] H)).comp h
      rw [vtmulR_one] at h2
      exact h2
  rwa [one_mul, mul_one] at hmain

/-- The compression of `x` by `1 ⊗ p_F` is the finite sum of its rank-one
compressions. -/
theorem compress_eq_sum (e : HilbertBasis ιH ℂ H) (F : Finset ιH)
    (x : VNT 𝒜 (H →L[ℂ] H)) :
    ((1 : 𝒜) ⊗ᵥ bkP e F) * x * ((1 : 𝒜) ⊗ᵥ bkP e F)
      = ∑ k ∈ F, ∑ l ∈ F,
          ((1 : 𝒜) ⊗ᵥ bkU e k k) * x * ((1 : 𝒜) ⊗ᵥ bkU e l l) := by
  have hsum : ((1 : 𝒜) ⊗ᵥ bkP e F) = ∑ k ∈ F, ((1 : 𝒜) ⊗ᵥ bkU e k k) := by
    show (vnTensor 𝒜 (H →L[ℂ] H)).map 1 (∑ k ∈ F, bkU e k k) = _
    exact map_sum ((vnTensor 𝒜 (H →L[ℂ] H)).map 1) _ _
  rw [hsum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]

/-- **The containment step of proc.tex:4938**: if every slice `r_ξ(x)` of
`x` lands in `𝒮`, then `x ∈ 𝒮 ⊗ B(ℋ)`. -/
theorem mem_tensorSub_of_rSlice_mem (S : StarSubalgebra ℂ 𝒜)
    (e : HilbertBasis ιH ℂ H) (x : VNT 𝒜 (H →L[ℂ] H))
    (hx : ∀ (ξ : H) (a : 𝒜), rSlice 𝒜 ξ x = a ⊗ᵥ (1 : H →L[ℂ] H) → a ∈ S) :
    x ∈ tensorSub (H →L[ℂ] H) S := by
  let _ : TopologicalSpace (VNT 𝒜 (H →L[ℂ] H)) := ultraweak (VNT 𝒜 (H →L[ℂ] H))
  set T : StarSubalgebra ℂ (VNT 𝒜 (H →L[ℂ] H)) := tensorSub (H →L[ℂ] H) S with hT
  have hcl : @IsClosed (VNT 𝒜 (H →L[ℂ] H)) (ultraweak (VNT 𝒜 (H →L[ℂ] H)))
      ((T : StarSubalgebra ℂ (VNT 𝒜 (H →L[ℂ] H))) : Set (VNT 𝒜 (H →L[ℂ] H))) :=
    (vnsac _ (isVNSubalgebra_wstar _).1).2
  have hterm : ∀ (v : H) (k l : ιH),
      rSlice 𝒜 v x * ((1 : 𝒜) ⊗ᵥ bkU e k l) ∈ T := by
    intro v k l
    obtain ⟨a, ha⟩ := rSlice_mem 𝒜 v x
    rw [ha, vtmul_mul_vtmul, mul_one, one_mul]
    exact (isVNSubalgebra_wstar _).2 ⟨a, hx v a ha, bkU e k l, rfl⟩
  have hrank : ∀ k l : ιH,
      ((1 : 𝒜) ⊗ᵥ bkU e k k) * x * ((1 : 𝒜) ⊗ᵥ bkU e l l) ∈ T := by
    intro k l
    rw [tensor_polarisation e k l x, smul_mul_assoc, sub_mul, sub_mul, add_mul,
      smul_mul_assoc, smul_mul_assoc]
    exact SMulMemClass.smul_mem _
      (sub_mem (sub_mem (add_mem (hterm _ k l)
        (SMulMemClass.smul_mem _ (hterm _ k l))) (hterm _ k l))
        (SMulMemClass.smul_mem _ (hterm _ k l)))
  refine hcl.mem_of_tendsto (compress_tendsto e x)
    (Filter.Eventually.of_forall fun F => ?_)
  rw [SetLike.mem_coe, compress_eq_sum]
  exact sum_mem fun k _ => sum_mem fun l _ => hrank k l


end Compression



/-! ## Naturality of the slices, and the embedding `𝒜 ⊗ 𝒞 ↪ 𝒜 ⊗ B(ℋ)` -/

section Naturality

variable {𝒜 ℬ 𝒞 : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ] [VonNeumannAlgebra ℬ]
  [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞] [VonNeumannAlgebra 𝒞]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜] in
theorem isVNSubalgebra_top' :
    IsVNSubalgebra 𝒜 (⊤ : StarSubalgebra ℂ 𝒜) := by
  refine ⟨?_, fun _ _ _ _ _ _ => StarSubalgebra.mem_top⟩
  rw [StarSubalgebra.coe_top]
  exact isClosed_univ

/-- `f ⊗ id` intertwines the slices `r_ξ` — the identity
`f ∘ r_ξ = r'_ξ ∘ (f ⊗ id)` of proc.tex:4900. -/
theorem rSlice_natural (f : NMIUMap 𝒜 ℬ) (ξ : H) (y : VNT 𝒜 (H →L[ℂ] H)) :
    tmapM f (nmiuId (H →L[ℂ] H)) (rSlice 𝒜 ξ y)
      = rSlice ℬ ξ (tmapM f (nmiuId (H →L[ℂ] H)) y) := by
  have hcomm : ncpComp (nmiuNCP (tmapM f (nmiuId (H →L[ℂ] H))))
        (tmap (ncpId 𝒜) (npScalar (vectorNP ξ)))
      = ncpComp (tmap (ncpId ℬ) (npScalar (vectorNP ξ)))
        (nmiuNCP (tmapM f (nmiuId (H →L[ℂ] H)))) := by
    refine (exists_tmap (nmiuNCP f) (npScalar (vectorNP ξ))).unique
      (fun a b => ?_) (fun a b => ?_)
    · simp only [ncpComp_apply, tmap_apply, ncpId_apply, nmiuNCP_apply,
        tmapM_apply, nmiuId_apply]
    · simp only [ncpComp_apply, tmap_apply, ncpId_apply, nmiuNCP_apply,
        tmapM_apply, nmiuId_apply]
  have h := congrArg
    (fun F : NCPMap (VNT 𝒜 (H →L[ℂ] H)) (VNT ℬ (H →L[ℂ] H)) => F y) hcomm
  simp only [ncpComp_apply, nmiuNCP_apply] at h
  exact h

/-- The two ways of reading `f ⊗ ρ`. -/
theorem tmapM_swap (f : NMIUMap 𝒜 ℬ) (ρ : NMIUMap 𝒞 (H →L[ℂ] H))
    (y : VNT 𝒜 𝒞) :
    tmapM f (nmiuId (H →L[ℂ] H)) (tmapM (nmiuId 𝒜) ρ y)
      = tmapM (nmiuId ℬ) ρ (tmapM f (nmiuId 𝒞) y) := by
  have h : nmiuComp (tmapM f (nmiuId (H →L[ℂ] H))) (tmapM (nmiuId 𝒜) ρ)
      = nmiuComp (tmapM (nmiuId ℬ) ρ) (tmapM f (nmiuId 𝒞)) :=
    (exists_tmapM f ρ).unique
      (fun a b => by
        simp only [nmiuComp_apply, tmapM_apply, nmiuId_apply])
      (fun a b => by
        simp only [nmiuComp_apply, tmapM_apply, nmiuId_apply])
  exact congrArg (fun F : NMIUMap (VNT 𝒜 𝒞) (VNT ℬ (H →L[ℂ] H)) => F y) h

/-- The range of `id ⊗ ρ` lies in `𝒜 ⊗ ρ(𝒞)`. -/
theorem tmapM_right_range_le (ρ : NMIUMap 𝒞 (H →L[ℂ] H)) (y : VNT 𝒜 𝒞) :
    tmapM (nmiuId 𝒜) ρ y ∈
      tensorSub₂ (⊤ : StarSubalgebra ℂ 𝒜) ρ.toStarAlgHom.range := by
  have htop : wstar (VNT 𝒜 𝒞)
      {t : VNT 𝒜 𝒞 | ∃ a b, t = (vnTensor 𝒜 𝒞).map a b} = ⊤ :=
    wstar_eq_top_of_dense_span _ (vnTensor 𝒜 𝒞).isTensorProduct.dense
  have hle : wstar (VNT 𝒜 𝒞) {t : VNT 𝒜 𝒞 | ∃ a b, t = (vnTensor 𝒜 𝒞).map a b} ≤
      (tensorSub₂ (⊤ : StarSubalgebra ℂ 𝒜) ρ.toStarAlgHom.range).comap
        (tmapM (nmiuId 𝒜) ρ).toStarAlgHom := by
    refine sInf_le ⟨isVNSubalgebra_comap (tmapM (nmiuId 𝒜) ρ).toStarAlgHom
      (tmapM (nmiuId 𝒜) ρ).preservesDirSups' _ (isVNSubalgebra_wstar _).1, ?_⟩
    rintro _ ⟨a, c, rfl⟩
    show tmapM (nmiuId 𝒜) ρ (a ⊗ᵥ c) ∈
      tensorSub₂ (⊤ : StarSubalgebra ℂ 𝒜) ρ.toStarAlgHom.range
    rw [tmapM_apply, nmiuId_apply]
    exact (isVNSubalgebra_wstar _).2
      ⟨a, StarSubalgebra.mem_top, ρ c, ⟨c, rfl⟩, rfl⟩
  rw [htop, top_le_iff] at hle
  have hy : y ∈ (tensorSub₂ (⊤ : StarSubalgebra ℂ 𝒜) ρ.toStarAlgHom.range).comap
      (tmapM (nmiuId 𝒜) ρ).toStarAlgHom := by rw [hle]; trivial
  exact hy

/-- `𝒮 ⊗ ρ(𝒞)` is the image of `𝒮 ⊗ 𝒞` under `id ⊗ ρ`. -/
theorem exists_preimage_of_mem_tensorSub₂ (ρ : NMIUMap 𝒞 (H →L[ℂ] H))
    (hρ : Function.Injective ⇑ρ) (S : StarSubalgebra ℂ 𝒜)
    (z : VNT 𝒜 (H →L[ℂ] H))
    (hz : z ∈ tensorSub₂ S ρ.toStarAlgHom.range) :
    ∃ y ∈ tensorSub 𝒞 S, tmapM (nmiuId 𝒜) ρ y = z := by
  set J := tmapM (nmiuId 𝒜) ρ with hJ
  have hJinj : Function.Injective ⇑J :=
    tmapM_injective (nmiuId 𝒜) ρ (nmiuId_bijective (X := 𝒜)).1 hρ
  set R := J.toStarAlgHom.range with hR
  have hRvn : IsVNSubalgebra (VNT 𝒜 (H →L[ℂ] H)) R := nmiu_image J
  set u := nmiuCorestrict J R hRvn (fun y => ⟨y, rfl⟩) with hu
  have hubij : Function.Bijective ⇑u :=
    nmiuCorestrict_bijective J R hRvn (fun y => ⟨y, rfl⟩) hJinj
      (by rintro _ ⟨y, rfl⟩; exact ⟨y, rfl⟩)
  set W : StarSubalgebra ℂ (VNT 𝒜 (H →L[ℂ] H)) :=
    ((tensorSub 𝒞 S).map u.toStarAlgHom).map VNSub.valStarAlgHom with hW
  have hWvn : IsVNSubalgebra (VNT 𝒜 (H →L[ℂ] H)) W :=
    vnsub_isVNSubalgebra_map _
      (isVNSubalgebra_nmiu_map u hubij _ (isVNSubalgebra_wstar _).1)
  have hmemW : ∀ x : VNT 𝒜 (H →L[ℂ] H),
      x ∈ W ↔ ∃ y ∈ tensorSub 𝒞 S, J y = x := by
    intro x
    constructor
    · rintro ⟨t, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨u y, ⟨y, hy, rfl⟩, rfl⟩
  have hle : tensorSub₂ S ρ.toStarAlgHom.range ≤ W := by
    refine sInf_le ⟨hWvn, ?_⟩
    rintro _ ⟨a, ha, _, ⟨c, rfl⟩, rfl⟩
    refine (hmemW _).mpr ⟨a ⊗ᵥ c, ?_, ?_⟩
    · exact (isVNSubalgebra_wstar _).2 ⟨a, ha, c, rfl⟩
    · rw [hJ, tmapM_apply, nmiuId_apply]
      rfl
  exact (hmemW z).mp (hle hz)

/-- **The intersection step of proc.tex:4938**: granted 121II, an element
of `𝒜 ⊗ 𝒞` whose image in `𝒜 ⊗ B(ℋ)` lies in `𝒮 ⊗ B(ℋ)` already lies in
`𝒮 ⊗ 𝒞`.  This is `𝒮 ⊗ 𝒞 = (𝒮 ⊗ B(ℋ)) ∩ (𝒜 ⊗ 𝒞)`. -/
theorem mem_tensorSub_of_image (h121 : IntersectionTensorStatement.{u})
    (ρ : NMIUMap 𝒞 (H →L[ℂ] H)) (hρ : Function.Injective ⇑ρ)
    (S : StarSubalgebra ℂ 𝒜) (hS : IsVNSubalgebra 𝒜 S) (x : VNT 𝒜 𝒞)
    (hx : tmapM (nmiuId 𝒜) ρ x ∈ tensorSub (H →L[ℂ] H) S) :
    x ∈ tensorSub 𝒞 S := by
  rw [tensorSub_eq_tensorSub₂] at hx
  have hx2 := tmapM_right_range_le (𝒜 := 𝒜) ρ x
  have hinf := tensorSub₂_inf_of_intersectionTensorStatement
    (𝒜 := 𝒜) (𝒞 := H →L[ℂ] H) h121 S ⊤ hS isVNSubalgebra_top'
    (⊤ : StarSubalgebra ℂ (H →L[ℂ] H)) ρ.toStarAlgHom.range
    isVNSubalgebra_top' (nmiu_image ρ)
  have hmem : tmapM (nmiuId 𝒜) ρ x ∈
      tensorSub₂ (S ⊓ ⊤) ((⊤ : StarSubalgebra ℂ (H →L[ℂ] H)) ⊓
        ρ.toStarAlgHom.range) := by
    rw [← hinf]
    exact ⟨hx, hx2⟩
  rw [inf_top_eq, top_inf_eq] at hmem
  obtain ⟨y, hy, hyx⟩ := exists_preimage_of_mem_tensorSub₂ ρ hρ S _ hmem
  have hJinj : Function.Injective ⇑(tmapM (nmiuId 𝒜) ρ) :=
    tmapM_injective (nmiuId 𝒜) ρ (nmiuId_bijective (X := 𝒜)).1 hρ
  exact hJinj hyx ▸ hy

end Naturality



/-- The range of `ρ ⊗ id` is contained in `ρ(𝒞) ⊗ 𝒜` (`tmapM_range_le` of
`QuantumLambda.lean`). -/
theorem tmapM_left_range_le {C₀ D₀ A₀ : Type u}
    [CStarAlgebra C₀] [PartialOrder C₀] [StarOrderedRing C₀] [VonNeumannAlgebra C₀]
    [CStarAlgebra D₀] [PartialOrder D₀] [StarOrderedRing D₀] [VonNeumannAlgebra D₀]
    [CStarAlgebra A₀] [PartialOrder A₀] [StarOrderedRing A₀] [VonNeumannAlgebra A₀]
    (ρ : NMIUMap C₀ D₀) (y : VNT C₀ A₀) :
    tmapM ρ (nmiuId A₀) y ∈ tensorSub A₀ ρ.toStarAlgHom.range := by
  have htop : wstar (VNT C₀ A₀)
      {t : VNT C₀ A₀ | ∃ a b, t = (vnTensor C₀ A₀).map a b} = ⊤ :=
    wstar_eq_top_of_dense_span _ (vnTensor C₀ A₀).isTensorProduct.dense
  have hle : wstar (VNT C₀ A₀) {t : VNT C₀ A₀ | ∃ a b, t = (vnTensor C₀ A₀).map a b} ≤
      (tensorSub A₀ ρ.toStarAlgHom.range).comap (tmapM ρ (nmiuId A₀)).toStarAlgHom := by
    refine sInf_le ⟨isVNSubalgebra_comap (tmapM ρ (nmiuId A₀)).toStarAlgHom
      (tmapM ρ (nmiuId A₀)).preservesDirSups' _ (isVNSubalgebra_wstar _).1, ?_⟩
    rintro _ ⟨c, a, rfl⟩
    show tmapM ρ (nmiuId A₀) (c ⊗ᵥ a) ∈ tensorSub A₀ ρ.toStarAlgHom.range
    rw [tmapM_apply, nmiuId_apply]
    exact (isVNSubalgebra_wstar _).2 ⟨ρ c, ⟨c, rfl⟩, a, rfl⟩
  rw [htop, top_le_iff] at hle
  have hy : y ∈ (tensorSub A₀ ρ.toStarAlgHom.range).comap
      (tmapM ρ (nmiuId A₀)).toStarAlgHom := by rw [hle]; trivial
  exact hy

/-- The corestriction of a map landing in `𝒮 ⊗ 𝒞` to `(VNSub 𝒜 𝒮) ⊗ 𝒞`
(the device of `ha_tensor_closed`). -/
theorem exists_corestrict_tensorSub {A₀ C₀ D₀ : Type u}
    [CStarAlgebra A₀] [PartialOrder A₀] [StarOrderedRing A₀] [VonNeumannAlgebra A₀]
    [CStarAlgebra C₀] [PartialOrder C₀] [StarOrderedRing C₀] [VonNeumannAlgebra C₀]
    [CStarAlgebra D₀] [PartialOrder D₀] [StarOrderedRing D₀] [VonNeumannAlgebra D₀]
    (S : StarSubalgebra ℂ A₀) (hS : IsVNSubalgebra A₀ S) (h : NMIUMap D₀ (VNT A₀ C₀))
    (hmem : ∀ d : D₀, h d ∈ tensorSub C₀ S) :
    ∃ ht : NMIUMap D₀ (VNT (VNSub A₀ S hS) C₀),
      ∀ d : D₀, tmapM (VNSub.valNMIU (A := A₀) (S := S) (hS := hS)) (nmiuId C₀) (ht d)
        = h d := by
  have hIvn : IsVNSubalgebra (VNT A₀ C₀) (tensorSub C₀ S) :=
    (isVNSubalgebra_wstar _).1
  have hΞinj : Function.Injective
      ⇑(tmapM (VNSub.valNMIU (A := A₀) (S := S) (hS := hS)) (nmiuId C₀)) :=
    tmapM_injective _ _ VNSub.valNMIU_injective (nmiuId_bijective (X := C₀)).1
  have hΞmem : ∀ y : VNT (VNSub A₀ S hS) C₀,
      tmapM (VNSub.valNMIU (A := A₀) (S := S) (hS := hS)) (nmiuId C₀) y
        ∈ tensorSub C₀ S := by
    intro y
    have hy := tmapM_left_range_le (A₀ := C₀)
      (VNSub.valNMIU (A := A₀) (S := S) (hS := hS)) y
    rwa [VNSub.valNMIU_range] at hy
  have hΞsurj : ∀ z ∈ tensorSub C₀ S,
      ∃ y, tmapM (VNSub.valNMIU (A := A₀) (S := S) (hS := hS)) (nmiuId C₀) y = z := by
    have hle : tensorSub C₀ S ≤
        (tmapM (VNSub.valNMIU (A := A₀) (S := S) (hS := hS))
          (nmiuId C₀)).toStarAlgHom.range := by
      refine sInf_le ⟨nmiu_image _, ?_⟩
      rintro _ ⟨s, hs, c, rfl⟩
      refine ⟨(⟨s, hs⟩ : VNSub A₀ S hS) ⊗ᵥ c, ?_⟩
      show tmapM (VNSub.valNMIU (A := A₀) (S := S) (hS := hS)) (nmiuId C₀)
          ((⟨s, hs⟩ : VNSub A₀ S hS) ⊗ᵥ c) = s ⊗ᵥ c
      rw [tmapM_apply, nmiuId_apply]
      rfl
    intro z hz
    exact hle hz
  have hΛbij := nmiuCorestrict_bijective
    (tmapM (VNSub.valNMIU (A := A₀) (S := S) (hS := hS)) (nmiuId C₀))
    (tensorSub C₀ S) hIvn hΞmem hΞinj hΞsurj
  refine ⟨nmiuComp (nmiuSymm _ hΛbij)
    (nmiuCorestrict h (tensorSub C₀ S) hIvn hmem), fun d => ?_⟩
  exact congrArg VNSub.val (nmiuSymm_apply_apply' _ hΛbij
    (nmiuCorestrict h (tensorSub C₀ S) hIvn hmem d))



end EqL

/-! ## 125IV `equaliser-lemma`, granted 121II -/

open EqL in
set_option maxHeartbeats 1000000 in
/-- **125IV** (`equaliser-lemma`, proc.tex:4852, Lemma (Kornell)), granted
**121II** `intersection-tensor` (as `IntersectionTensorStatement`): every
nmiu-map `h : 𝒟 → 𝒜 ⊗ 𝒞` factors as `(ι ⊗ id) ∘ h̃` through `𝒜̃ ⊗ 𝒞` for a
von Neumann subalgebra `𝒜̃ ⊆ 𝒜` generated by at most `#𝒟 · 2^#𝒞`
elements, such that nmiu-maps `f, g : 𝒜 → ℬ` with
`(f ⊗ id) ∘ h = (g ⊗ id) ∘ h` agree on `𝒜̃`.

This is `equaliser_lemma` of `QuantumLambda.lean` with 121II as an
explicit hypothesis; `equaliser_lemma` itself is
`equaliser_lemma_of_intersectionTensorStatement intersection_tensor h`. -/
theorem equaliser_lemma_of_intersectionTensorStatement
    (h121 : IntersectionTensorStatement.{u})
    {A C D : Type u}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]
    [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C] [VonNeumannAlgebra C]
    [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [VonNeumannAlgebra D]
    (h : NMIUMap D (VNT A C)) :
    ∃ (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S) (G : Set A),
      S = wstar A G ∧ #G ≤ #D * (2 : Cardinal.{u}) ^ #C ∧
      ∃ (ι : NMIUMap (VNSub A S hS) A)
        (ht : NMIUMap D (VNT (VNSub A S hS) C)),
        (∀ x : VNSub A S hS, ι x = x.val) ∧
        (∀ d : D, h d = tmapM ι (nmiuId C) (ht d)) ∧
        ∀ (B : Type u) [CStarAlgebra B] [PartialOrder B]
          [StarOrderedRing B] [VonNeumannAlgebra B] (f g : NMIUMap A B),
          (∀ d : D, tmapM f (nmiuId C) (h d) =
            tmapM g (nmiuId C) (h d)) →
          ∀ x : VNSub A S hS, f (ι x) = g (ι x) := by
  classical
  -- the equaliser clause holds for any `S` of the form `wstar A G` as soon
  -- as `f` and `g` agree on `G`
  have hEq : ∀ (G : Set A) (Bb : Type u) [CStarAlgebra Bb] [PartialOrder Bb]
      [StarOrderedRing Bb] [VonNeumannAlgebra Bb] (f g : NMIUMap A Bb),
      (∀ a ∈ G, f a = g a) → ∀ a ∈ wstar A G, f a = g a := by
    intro G Bb _ _ _ _ f g hfg a ha
    obtain ⟨E, hE, hEset⟩ := vn_equalisers f g
    have hGE : G ⊆ (E : Set A) := by
      intro y hy
      rw [hEset]
      exact hfg y hy
    have hSE : wstar A G ≤ E := sInf_le ⟨hE, hGE⟩
    have hmem : a ∈ (E : Set A) := hSE ha
    rw [hEset] at hmem
    exact hmem
  rcases subsingleton_or_nontrivial C with hCsub | hCnt
  · -- degenerate case: `𝒞` is trivial, so `𝒜 ⊗ 𝒞` is
    have _ := hCsub
    have hVsub : Subsingleton (VNT A C) := vnt_subsingleton
    have hVsub' : ∀ (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S),
        Subsingleton (VNT (VNSub A S hS) C) := fun _ _ => vnt_subsingleton
    refine ⟨wstar A (∅ : Set A), (isVNSubalgebra_wstar _).1, ∅, rfl, ?_,
      VNSub.valNMIU, nmiuOfSubsingleton D _, fun _ => rfl, fun _ =>
        Subsingleton.elim _ _, ?_⟩
    · simp
    · intro Bb _ _ _ _ f g _ x
      exact hEq ∅ Bb f g (fun a ha => absurd ha (Set.notMem_empty a)) x.val x.property
  · -- the main case
    have _ := hCnt
    obtain ⟨rep, hcard⟩ := vn_gns_bound (A := C)
    have hntBH : Nontrivial (rep.space →L[ℂ] rep.space) :=
      ⟨⟨rep.rep 0, rep.rep 1, fun hc => zero_ne_one (rep.injective hc)⟩⟩
    obtain ⟨w, e, -⟩ := exists_hilbertBasis ℂ rep.space
    -- the elements `r_ξ(h(d))`
    have hchoice : ∀ p : D × rep.space, ∃ a : A,
        rSlice A p.2 (tmapM (nmiuId A) rep.rep (h p.1))
          = a ⊗ᵥ (1 : rep.space →L[ℂ] rep.space) :=
      fun p => rSlice_mem A p.2 _
    choose r hr using hchoice
    refine ⟨wstar A (Set.range r), (isVNSubalgebra_wstar _).1, Set.range r, rfl,
      ?_, ?_⟩
    · -- the cardinality bound
      refine le_trans Cardinal.mk_range_le ?_
      have hprod : #(D × rep.space) = #D * #rep.space := by
        simp [Cardinal.mk_prod]
      rw [hprod]
      exact mul_le_mul' le_rfl hcard
    · -- the factorisation and the equaliser clause
      have hgen : ∀ p : D × rep.space, r p ∈ wstar A (Set.range r) :=
        fun p => (isVNSubalgebra_wstar _).2 ⟨p, rfl⟩
      have hmemS : ∀ d : D, h d ∈ tensorSub C (wstar A (Set.range r)) := by
        intro d
        refine mem_tensorSub_of_image h121 rep.rep rep.injective _
          (isVNSubalgebra_wstar _).1 (h d) ?_
        refine mem_tensorSub_of_rSlice_mem _ e _ ?_
        intro ξ a ha
        have h1 : a ⊗ᵥ (1 : rep.space →L[ℂ] rep.space)
            = r (d, ξ) ⊗ᵥ (1 : rep.space →L[ℂ] rep.space) := by
          rw [← ha, hr (d, ξ)]
        rw [nmiuTmulLeft_injective h1]
        exact hgen (d, ξ)
      obtain ⟨ht, hht⟩ := exists_corestrict_tensorSub
        (wstar A (Set.range r)) (isVNSubalgebra_wstar _).1 h hmemS
      refine ⟨VNSub.valNMIU, ht, fun _ => rfl, fun d => (hht d).symm, ?_⟩
      intro Bb _ _ _ _ f g hfg x
      refine hEq (Set.range r) Bb f g ?_ x.val x.property
      rintro _ ⟨p, rfl⟩
      obtain ⟨d, ξ⟩ := p
      have hnat : ∀ k : NMIUMap A Bb,
          tmapM k (nmiuId (rep.space →L[ℂ] rep.space))
              (rSlice A ξ (tmapM (nmiuId A) rep.rep (h d)))
            = rSlice Bb ξ (tmapM (nmiuId Bb) rep.rep
                (tmapM k (nmiuId C) (h d))) := by
        intro k
        rw [rSlice_natural, tmapM_swap]
      have hval : ∀ k : NMIUMap A Bb,
          tmapM k (nmiuId (rep.space →L[ℂ] rep.space))
              (rSlice A ξ (tmapM (nmiuId A) rep.rep (h d)))
            = k (r (d, ξ)) ⊗ᵥ (1 : rep.space →L[ℂ] rep.space) := by
        intro k
        rw [hr (d, ξ), tmapM_apply, nmiuId_apply]
      have hkey : f (r (d, ξ)) ⊗ᵥ (1 : rep.space →L[ℂ] rep.space)
          = g (r (d, ξ)) ⊗ᵥ (1 : rep.space →L[ℂ] rep.space) := by
        rw [← hval f, ← hval g, hnat f, hnat g, hfg d]
      exact nmiuTmulLeft_injective hkey


end Theses.A.Proc
