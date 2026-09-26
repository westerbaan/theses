/-
FDS 2.5: the enveloping W*-algebra `A**`, discharging `IsRepEnvelope`.

PLAN (2026-09-26).  Goal: for every unital C*-algebra `𝒜 : Type u` a Kadison
von Neumann algebra `N : Type u` and `ι : 𝒜 → N` with `IsRepEnvelope ι`
(Envelope.lean), so that `nrep_equiv_rep` holds with no hypothesis.
* `N := W*(π_u(𝒜)) ⊆ B(H_u)` (= `π_u(𝒜)''`, tree 88VI `double_commutant`),
  bundled as the tree's `VNSub`, for the universal representation
  `π_u = ⊕_f π_f` over all positive functionals `f` (tree `dsumRep` of
  Mathlib's GNS representations).  No Kaplansky density, no cyclic
  decomposition (Zorn), no normality of reductions is needed:
* Extension of `π : 𝒜 → B(H)`.  Put `K = H_u ⊕ H`, `σ = π_u ⊕ π`,
  `M = W*(σ(𝒜)) = σ(𝒜)''`.  (a) the projections onto `H_u` and `H` lie in
  `σ(𝒜)'`, so `M` is block diagonal and the compressions `q₁ : M → B(H_u)`,
  `q₂ : M → B(H)` are *-homomorphisms.  (b) Every vector functional of `π`
  is one of `π_u`: `⟨η,π(·)η⟩ = f` is positive, `ξ = δ_f ⊗ [1]_f` has
  `⟨ξ,π_u(·)ξ⟩ = f`.  (c) Since `M` is the ultraweak closure of `σ(𝒜)`
  (88VI) and vector functionals are ultraweakly continuous,
  `⟨η, q₂(m) η⟩ = ⟨ξ, q₁(m) ξ⟩` for all `m ∈ M`.  Hence `q₁` is injective;
  it is normal (vector functionals), so its range is a von Neumann
  subalgebra (tree 48VI) containing `π_u(𝒜)`, hence `N`.
  `ρ := q₂ ∘ q₁⁻¹ : N → B(H)` extends `π` and is normal by (c) (its vector
  functionals are those of `N`).
* Uniqueness: the equaliser of two normal extensions is a von Neumann
  subalgebra of `N` (tree 47V `vn_equalisers`); its image in `B(H_u)` is one
  too (48VI) and contains `π_u(𝒜)`, hence `N`.
* Universe: `N` and the Hilbert spaces live in `𝒜`'s universe, which is the
  form `IsRepEnvelope`/`nrep_equiv_rep` take (`N : Type u`, `HilbObj.{u}`).
-/
import Papers.FDS.Envelope

open CategoryTheory
open scoped ComplexOrder ComplexInnerProductSpace
open Theses Theses.A.VN Complex

universe u

noncomputable section

namespace Papers.FDS

namespace Env

/-! ### Compressions to a block of a block-diagonal algebra -/

section Compress

variable {E K : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- An isometry `J : E → K`, with `J*J = 1`, and an operator commuting with
`JJ*` maps `J(E)` into itself: `n J = J J* n J`. -/
theorem apply_isometry_eq (J : E →L[ℂ] K)
    (hJ : ∀ x, ContinuousLinearMap.adjoint J (J x) = x) (n : K →L[ℂ] K)
    (hn : (J.comp (ContinuousLinearMap.adjoint J)) * n
      = n * (J.comp (ContinuousLinearMap.adjoint J))) (x : E) :
    n (J x) = J (ContinuousLinearMap.adjoint J (n (J x))) := by
  have h := congrArg (fun T : K →L[ℂ] K => T (J x)) hn
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hJ] at h
  exact h.symm

variable {S : StarSubalgebra ℂ (K →L[ℂ] K)} {hS : IsVNSubalgebra (K →L[ℂ] K) S}

/-- The compression `m ↦ J* m J` of a von Neumann subalgebra all of whose
elements commute with `JJ*` (`J` an isometry): a unital *-homomorphism. -/
def compress (J : E →L[ℂ] K) (hJ : ∀ x, ContinuousLinearMap.adjoint J (J x) = x)
    (hc : ∀ m : VNSub (K →L[ℂ] K) S hS, (J.comp (ContinuousLinearMap.adjoint J)) * m.val
      = m.val * (J.comp (ContinuousLinearMap.adjoint J))) :
    VNSub (K →L[ℂ] K) S hS →⋆ₐ[ℂ] (E →L[ℂ] E) where
  toFun m := (ContinuousLinearMap.adjoint J).comp (m.val.comp J)
  map_one' := ContinuousLinearMap.ext fun x => hJ x
  map_mul' m n := ContinuousLinearMap.ext fun x => by
    show ContinuousLinearMap.adjoint J (m.val (n.val (J x)))
      = ContinuousLinearMap.adjoint J (m.val (J (ContinuousLinearMap.adjoint J (n.val (J x)))))
    rw [← apply_isometry_eq J hJ n.val (hc n) x]
  map_zero' := ContinuousLinearMap.ext fun x => by
    show ContinuousLinearMap.adjoint J ((0 : K →L[ℂ] K) (J x)) = 0
    simp
  map_add' m n := ContinuousLinearMap.ext fun x => by
    show ContinuousLinearMap.adjoint J ((m.val + n.val) (J x))
      = ContinuousLinearMap.adjoint J (m.val (J x)) + ContinuousLinearMap.adjoint J (n.val (J x))
    simp
  commutes' c := ContinuousLinearMap.ext fun x => by
    show ContinuousLinearMap.adjoint J ((algebraMap ℂ (K →L[ℂ] K) c) (J x))
      = (algebraMap ℂ (E →L[ℂ] E) c) x
    simp [Algebra.algebraMap_eq_smul_one, hJ]
  map_star' m := by
    show (ContinuousLinearMap.adjoint J).comp ((star m.val).comp J)
      = star ((ContinuousLinearMap.adjoint J).comp (m.val.comp J))
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

theorem compress_apply (J : E →L[ℂ] K) (hJ : ∀ x, ContinuousLinearMap.adjoint J (J x) = x)
    (hc : ∀ m : VNSub (K →L[ℂ] K) S hS, (J.comp (ContinuousLinearMap.adjoint J)) * m.val
      = m.val * (J.comp (ContinuousLinearMap.adjoint J)))
    (m : VNSub (K →L[ℂ] K) S hS) (x : E) :
    compress J hJ hc m x = ContinuousLinearMap.adjoint J (m.val (J x)) := rfl

end Compress

/-! ### Two consequences of the bicommutant theorem (tree 88VI) -/

section Bicommutant

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- An element of `W*(S) = S''` commutes with every element of `S'`. -/
theorem commute_of_mem_wstar (S : StarSubalgebra ℂ (K →L[ℂ] K)) {m : K →L[ℂ] K}
    (hm : m ∈ wstar (K →L[ℂ] K) (S : Set (K →L[ℂ] K))) {t : K →L[ℂ] K}
    (ht : ∀ s ∈ S, s * t = t * s) : t * m = m * t := by
  have h : m ∈ commutant (K →L[ℂ] K) (commutant (K →L[ℂ] K) (S : Set (K →L[ℂ] K))) := by
    rw [(double_commutant S).2.2]
    exact hm
  exact Set.mem_centralizer_iff.mp h t (Set.mem_centralizer_iff.mpr fun s hs => ht s hs)

/-- Two vectors with the same vector functional on `S` have the same vector
functional on `W*(S)`: `W*(S)` is the ultraweak closure of `S` (88VI), and
vector functionals are ultraweakly continuous. -/
theorem inner_eq_of_mem_wstar (S : StarSubalgebra ℂ (K →L[ℂ] K)) (v w : K)
    (h : ∀ s ∈ S, ⟪v, s v⟫ = ⟪w, s w⟫) {m : K →L[ℂ] K}
    (hm : m ∈ wstar (K →L[ℂ] K) (S : Set (K →L[ℂ] K))) : ⟪v, m v⟫ = ⟪w, m w⟫ := by
  have hcl : m ∈ @closure _ (ultraweak (K →L[ℂ] K)) (S : Set (K →L[ℂ] K)) := by
    rw [← (double_commutant S).2.1, (double_commutant S).2.2]
    exact hm
  have hC : @IsClosed _ (ultraweak (K →L[ℂ] K))
      {T : K →L[ℂ] K | vectorNP v T = vectorNP w T} := by
    let _ : TopologicalSpace (K →L[ℂ] K) := ultraweak (K →L[ℂ] K)
    exact isClosed_eq (continuous_ultraweak_npFunctional (vectorNP v))
      (continuous_ultraweak_npFunctional (vectorNP w))
  have hsub : (S : Set (K →L[ℂ] K)) ⊆ {T : K →L[ℂ] K | vectorNP v T = vectorNP w T} :=
    fun s hs => by
      show vectorNP v s = vectorNP w s
      rw [vectorNP_apply, vectorNP_apply]
      exact h s hs
  have key : vectorNP v m = vectorNP w m := by
    let _ : TopologicalSpace (K →L[ℂ] K) := ultraweak (K →L[ℂ] K)
    exact closure_minimal hsub hC hcl
  rwa [vectorNP_apply, vectorNP_apply] at key

end Bicommutant

/-! ### The inclusions of a binary direct sum and their adjoints -/

section Inclusions

variable (H K : HilbObj.{u})

theorem adjoint_inlCLM_apply (z : H.prod K) :
    ContinuousLinearMap.adjoint (inlCLM H K) z = (WithLp.ofLp (z : WithLp 2 (H × K))).1 := by
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  show inner ℂ x (WithLp.ofLp (z : WithLp 2 (H × K))).1
      + inner ℂ (0 : K) (WithLp.ofLp (z : WithLp 2 (H × K))).2 = _
  rw [inner_zero_left, add_zero]

theorem adjoint_inrCLM_apply (z : H.prod K) :
    ContinuousLinearMap.adjoint (inrCLM H K) z = (WithLp.ofLp (z : WithLp 2 (H × K))).2 := by
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  show inner ℂ (0 : H) (WithLp.ofLp (z : WithLp 2 (H × K))).1
      + inner ℂ x (WithLp.ofLp (z : WithLp 2 (H × K))).2 = _
  rw [inner_zero_left, zero_add]

theorem adjoint_inlCLM_inl (x : H) : ContinuousLinearMap.adjoint (inlCLM H K) (inlCLM H K x) = x :=
  adjoint_inlCLM_apply H K _

theorem adjoint_inrCLM_inr (y : K) : ContinuousLinearMap.adjoint (inrCLM H K) (inrCLM H K y) = y :=
  adjoint_inrCLM_apply H K _

end Inclusions

/-! ### The universal representation -/

section Universal

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

variable (𝒜) in
/-- The universal Hilbert space `H_u = ⊕_f H_f`, over all positive linear
functionals `f` of `𝒜` (GNS spaces). -/
abbrev uHilb : HilbObj.{u} := ⟨lp (fun f : 𝒜 →ₚ[ℂ] ℂ => f.GNS) 2⟩

variable (𝒜) in
/-- The universal representation `π_u = ⊕_f π_f` (tree **30IX** `dsumRep`
of Mathlib's GNS representations). -/
def uRep : 𝒜 →⋆ₐ[ℂ] (uHilb 𝒜 →L[ℂ] uHilb 𝒜) :=
  Theses.A.CStar.dsumRep (fun f : 𝒜 →ₚ[ℂ] ℂ => f.gnsStarAlgHom)

open scoped Classical in
/-- The cyclic vector `[1]_f` of the GNS space of `f`, in the `f`-th summand. -/
def uVec (f : 𝒜 →ₚ[ℂ] ℂ) : uHilb 𝒜 :=
  (lp.single 2 f ((f.toPreGNS 1 : f.PreGNS) : f.GNS) : lp (fun f : 𝒜 →ₚ[ℂ] ℂ => f.GNS) 2)

/-- Every positive functional is a vector functional of `π_u`. -/
theorem inner_uVec (f : 𝒜 →ₚ[ℂ] ℂ) (a : 𝒜) : ⟪uVec f, uRep 𝒜 a (uVec f)⟫ = f a := by
  classical
  show @inner ℂ (lp (fun f : 𝒜 →ₚ[ℂ] ℂ => f.GNS) 2) _
      (lp.single 2 f ((f.toPreGNS 1 : f.PreGNS) : f.GNS))
      (uRep 𝒜 a (uVec f) : lp (fun f : 𝒜 →ₚ[ℂ] ℂ => f.GNS) 2) = f a
  rw [lp.inner_single_left]
  have h1 : ((uRep 𝒜 a (uVec f) : lp (fun f : 𝒜 →ₚ[ℂ] ℂ => f.GNS) 2) : ∀ g, g.GNS) f
      = f.gnsStarAlgHom a ((f.toPreGNS 1 : f.PreGNS) : f.GNS) := by
    show f.gnsStarAlgHom a (((lp.single 2 f ((f.toPreGNS 1 : f.PreGNS) : f.GNS) :
      lp (fun f : 𝒜 →ₚ[ℂ] ℂ => f.GNS) 2) : ∀ g, g.GNS) f) = _
    rw [lp.single_apply_self]
  rw [h1, Theses.A.CStar.gns_starAlgHom_apply, UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def]
  simp [PositiveLinearMap.ofPreGNS_toPreGNS]

/-- The vector functional `a ↦ ⟨η, π(a) η⟩` of a representation, as a positive
functional. -/
def vecFun {H : HilbObj.{u}} (π : 𝒜 →⋆ₐ[ℂ] (H →L[ℂ] H)) (η : H) : 𝒜 →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun a => ⟪η, π a η⟫
      map_add' := fun a b => by simp [map_add]
      map_smul' := fun c a => by simp [map_smul] }
    fun a ha => by
      have h := map_nonneg (vectorNP η).toPositiveLinearMap (starAlgHom_nonneg_general π ha)
      exact h

theorem vecFun_apply {H : HilbObj.{u}} (π : 𝒜 →⋆ₐ[ℂ] (H →L[ℂ] H)) (η : H) (a : 𝒜) :
    vecFun π η a = ⟪η, π a η⟫ := rfl

end Universal

/-! ### Bundled von Neumann subalgebras: the inclusion -/

theorem starAlgHom_mem_range {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y] {φ : X →⋆ₐ[ℂ] Y}
    {y : Y} : y ∈ φ.range ↔ ∃ x, φ x = y := Iff.rfl

section ValHom

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]
  {S : StarSubalgebra ℂ A} {hS : IsVNSubalgebra A S}

omit [VonNeumannAlgebra A] in
theorem vnSub_val_algebraMap (c : ℂ) :
    (algebraMap ℂ (VNSub A S hS) c).val = algebraMap ℂ A c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  rfl

/-- The inclusion of a von Neumann subalgebra, as a unital *-homomorphism. -/
def valHom : VNSub A S hS →⋆ₐ[ℂ] A where
  toFun := VNSub.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := vnSub_val_algebraMap c
  map_star' _ := rfl

omit [VonNeumannAlgebra A] in
theorem valHom_apply (x : VNSub A S hS) : valHom x = x.val := rfl

end ValHom

/-! ### The enveloping von Neumann algebra `A** = π_u(𝒜)''` -/

section Envelope

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

variable (𝒜) in
/-- `W*(π_u(𝒜))`, the least von Neumann subalgebra of `B(H_u)` containing
the image of the universal representation. -/
def envAlg : StarSubalgebra ℂ (uHilb 𝒜 →L[ℂ] uHilb 𝒜) :=
  wstar (uHilb 𝒜 →L[ℂ] uHilb 𝒜) ((uRep 𝒜).range : Set (uHilb 𝒜 →L[ℂ] uHilb 𝒜))

variable (𝒜) in
theorem envAlg_vn : IsVNSubalgebra (uHilb 𝒜 →L[ℂ] uHilb 𝒜) (envAlg 𝒜) :=
  (isVNSubalgebra_wstar _).1

variable (𝒜) in
/-- It is the bicommutant `π_u(𝒜)''` (tree **88VI**). -/
theorem envAlg_eq_bicommutant :
    (envAlg 𝒜 : Set (uHilb 𝒜 →L[ℂ] uHilb 𝒜)) =
      commutant (uHilb 𝒜 →L[ℂ] uHilb 𝒜) (commutant (uHilb 𝒜 →L[ℂ] uHilb 𝒜)
        ((uRep 𝒜).range : Set (uHilb 𝒜 →L[ℂ] uHilb 𝒜))) :=
  (double_commutant (uRep 𝒜).range).2.2.symm

variable (𝒜) in
/-- The enveloping von Neumann algebra `A** := π_u(𝒜)''`, bundled as a
(Kadison) von Neumann algebra (tree `VNSub`). -/
abbrev Bidual : Type u := VNSub (uHilb 𝒜 →L[ℂ] uHilb 𝒜) (envAlg 𝒜) (envAlg_vn 𝒜)

theorem uRep_mem_envAlg (a : 𝒜) : uRep 𝒜 a ∈ envAlg 𝒜 :=
  (isVNSubalgebra_wstar _).2 (starAlgHom_mem_range.mpr ⟨a, rfl⟩)

/-- The embedding `ι : 𝒜 → A**`, `a ↦ π_u(a)`. -/
def bidualEmb : 𝒜 →⋆ₐ[ℂ] Bidual 𝒜 where
  toFun a := ⟨uRep 𝒜 a, uRep_mem_envAlg a⟩
  map_one' := VNSub.val_injective (map_one (uRep 𝒜))
  map_mul' a b := VNSub.val_injective (map_mul (uRep 𝒜) a b)
  map_zero' := VNSub.val_injective (map_zero (uRep 𝒜))
  map_add' a b := VNSub.val_injective (map_add (uRep 𝒜) a b)
  commutes' c := VNSub.val_injective
    ((AlgHomClass.commutes (uRep 𝒜) c).trans (vnSub_val_algebraMap c).symm)
  map_star' a := VNSub.val_injective (map_star (uRep 𝒜) a)

theorem bidualEmb_val (a : 𝒜) : (bidualEmb a : Bidual 𝒜).val = uRep 𝒜 a := rfl

end Envelope

/-! ### The extension of a representation to `A**` -/

section Extension

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  (H : HilbObj.{u}) (π : 𝒜 →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- `σ = π_u ⊕ π` on `K = H_u ⊕ H`. -/
def sig : 𝒜 →⋆ₐ[ℂ] ((uHilb 𝒜).prod H →L[ℂ] (uHilb 𝒜).prod H) :=
  prodRep (⟨uHilb 𝒜, uRep 𝒜⟩ : RepObj 𝒜) ⟨H, π⟩

/-- `W*(σ(𝒜)) ⊆ B(H_u ⊕ H)`. -/
def sigAlg : StarSubalgebra ℂ ((uHilb 𝒜).prod H →L[ℂ] (uHilb 𝒜).prod H) :=
  wstar _ ((sig H π).range : Set ((uHilb 𝒜).prod H →L[ℂ] (uHilb 𝒜).prod H))

theorem sigAlg_vn : IsVNSubalgebra _ (sigAlg H π) := (isVNSubalgebra_wstar _).1

/-- `M = W*(σ(𝒜))` as a von Neumann algebra. -/
abbrev MAlg : Type u := VNSub ((uHilb 𝒜).prod H →L[ℂ] (uHilb 𝒜).prod H) (sigAlg H π) (sigAlg_vn H π)

theorem sig_mem (a : 𝒜) : sig H π a ∈ sigAlg H π :=
  (isVNSubalgebra_wstar _).2 (starAlgHom_mem_range.mpr ⟨a, rfl⟩)

theorem inl_proj_comm (s) (hs : s ∈ (sig H π).range) :
    s * ((inlCLM (uHilb 𝒜) H).comp (ContinuousLinearMap.adjoint (inlCLM (uHilb 𝒜) H)))
      = ((inlCLM (uHilb 𝒜) H).comp (ContinuousLinearMap.adjoint (inlCLM (uHilb 𝒜) H))) * s := by
  obtain ⟨a, rfl⟩ := starAlgHom_mem_range.mp hs
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  erw [adjoint_inlCLM_apply, adjoint_inlCLM_apply]
  show (WithLp.toLp 2 (uRep 𝒜 a (WithLp.ofLp (z : WithLp 2 (uHilb 𝒜 × H))).1, π a 0) :
      WithLp 2 (uHilb 𝒜 × H))
    = WithLp.toLp 2 (uRep 𝒜 a (WithLp.ofLp (z : WithLp 2 (uHilb 𝒜 × H))).1, 0)
  rw [map_zero]

theorem inr_proj_comm (s) (hs : s ∈ (sig H π).range) :
    s * ((inrCLM (uHilb 𝒜) H).comp (ContinuousLinearMap.adjoint (inrCLM (uHilb 𝒜) H)))
      = ((inrCLM (uHilb 𝒜) H).comp (ContinuousLinearMap.adjoint (inrCLM (uHilb 𝒜) H))) * s := by
  obtain ⟨a, rfl⟩ := starAlgHom_mem_range.mp hs
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  rw [adjoint_inrCLM_apply, adjoint_inrCLM_apply]
  show (WithLp.toLp 2 (uRep 𝒜 a 0, π a (WithLp.ofLp (z : WithLp 2 (uHilb 𝒜 × H))).2) :
      WithLp 2 (uHilb 𝒜 × H))
    = WithLp.toLp 2 (0, π a (WithLp.ofLp (z : WithLp 2 (uHilb 𝒜 × H))).2)
  rw [map_zero]

theorem inl_comm (m : MAlg H π) :
    ((inlCLM (uHilb 𝒜) H).comp (ContinuousLinearMap.adjoint (inlCLM (uHilb 𝒜) H))) * m.val
      = m.val * ((inlCLM (uHilb 𝒜) H).comp (ContinuousLinearMap.adjoint (inlCLM (uHilb 𝒜) H))) :=
  commute_of_mem_wstar _ m.property fun s hs => inl_proj_comm H π s hs

theorem inr_comm (m : MAlg H π) :
    ((inrCLM (uHilb 𝒜) H).comp (ContinuousLinearMap.adjoint (inrCLM (uHilb 𝒜) H))) * m.val
      = m.val * ((inrCLM (uHilb 𝒜) H).comp (ContinuousLinearMap.adjoint (inrCLM (uHilb 𝒜) H))) :=
  commute_of_mem_wstar _ m.property fun s hs => inr_proj_comm H π s hs

/-- The compression `q₁ : M → B(H_u)`. -/
def q1 : MAlg H π →⋆ₐ[ℂ] (uHilb 𝒜 →L[ℂ] uHilb 𝒜) :=
  compress (inlCLM (uHilb 𝒜) H) (adjoint_inlCLM_inl _ _) (inl_comm H π)

/-- The compression `q₂ : M → B(H)`. -/
def q2 : MAlg H π →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  compress (inrCLM (uHilb 𝒜) H) (adjoint_inrCLM_inr _ _) (inr_comm H π)

theorem q1_apply (m : MAlg H π) (x : uHilb 𝒜) :
    q1 H π m x = ContinuousLinearMap.adjoint (inlCLM (uHilb 𝒜) H) (m.val (inlCLM _ H x)) := rfl

theorem q2_apply (m : MAlg H π) (y : H) :
    q2 H π m y = ContinuousLinearMap.adjoint (inrCLM (uHilb 𝒜) H) (m.val (inrCLM _ H y)) := rfl

/-- The key identity: the vector functional of `η ∈ H` on `M` is that of
`ξ = [1]_{⟨η,π(·)η⟩} ∈ H_u`. -/
theorem inner_q2 (η : H) (m : MAlg H π) :
    ⟪η, q2 H π m η⟫ = ⟪uVec (vecFun π η), q1 H π m (uVec (vecFun π η))⟫ := by
  rw [q2_apply, q1_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]
  refine inner_eq_of_mem_wstar _ _ _ (fun s hs => ?_) m.property
  obtain ⟨a, rfl⟩ := starAlgHom_mem_range.mp hs
  show inner ℂ (0 : uHilb 𝒜) (uRep 𝒜 a 0) + inner ℂ η (π a η)
    = inner ℂ (uVec (vecFun π η)) (uRep 𝒜 a (uVec (vecFun π η))) + inner ℂ (0 : H) (π a 0)
  rw [inner_zero_left, inner_zero_left, zero_add, add_zero, inner_uVec, vecFun_apply]

theorem q1_injective : Function.Injective (q1 H π) := by
  intro m m' h
  set d := m - m' with hd
  have hq1 : q1 H π d = 0 := by rw [hd, map_sub, h, sub_self]
  have hq2 : q2 H π d = 0 := by
    have hz : ∀ x : H, (⟪((q2 H π d : H →L[ℂ] H) : H →ₗ[ℂ] H) x, x⟫ : ℂ) = 0 := by
      intro x
      have hx : ⟪x, q2 H π d x⟫ = 0 := by
        rw [inner_q2, hq1]
        simp
      rw [← inner_conj_symm] at hx
      simpa using congrArg (starRingEnd ℂ) hx
    refine ContinuousLinearMap.coe_injective ?_
    rw [ContinuousLinearMap.toLinearMap_zero]
    exact (inner_map_self_eq_zero _).mp hz
  have hv : d.val = 0 := by
    refine ContinuousLinearMap.ext fun z => ?_
    have e1 : ∀ x, d.val (inlCLM (uHilb 𝒜) H x) = 0 := by
      intro x
      rw [apply_isometry_eq _ (adjoint_inlCLM_inl _ _) _ (inl_comm H π d)]
      have : ContinuousLinearMap.adjoint (inlCLM (uHilb 𝒜) H) (d.val (inlCLM _ H x))
          = q1 H π d x := rfl
      rw [this, hq1, ContinuousLinearMap.zero_apply, map_zero]
    have e2 : ∀ y, d.val (inrCLM (uHilb 𝒜) H y) = 0 := by
      intro y
      rw [apply_isometry_eq _ (adjoint_inrCLM_inr _ _) _ (inr_comm H π d)]
      have : ContinuousLinearMap.adjoint (inrCLM (uHilb 𝒜) H) (d.val (inrCLM _ H y))
          = q2 H π d y := rfl
      rw [this, hq2, ContinuousLinearMap.zero_apply, map_zero]
    have hz := congrArg d.val (inl_add_inr (H := uHilb 𝒜) (K := H) z)
    rw [hz, map_add, e1, e2, add_zero]; rfl
  have : d = 0 := VNSub.val_injective hv
  exact sub_eq_zero.mp this

theorem q1_normal : PreservesDirSups ⇑(q1 H π) :=
  starAlgHom_preservesDirSups_of_vectors (q1 H π) Set.univ
    (fun R hR => ContinuousLinearMap.ext fun y => hR y trivial)
    (fun y _ => ⟨VNSub.restrictNP (vectorNP (inlCLM (uHilb 𝒜) H y)), fun m => by
      rw [VNSub.restrictNP_apply, vectorNP_apply, q1_apply,
        ContinuousLinearMap.adjoint_inner_right]⟩)

theorem q1_sig (a : 𝒜) : q1 H π ⟨sig H π a, sig_mem H π a⟩ = uRep 𝒜 a :=
  ContinuousLinearMap.ext fun y => by
    rw [q1_apply, adjoint_inlCLM_apply]
    rfl

theorem q2_sig (a : 𝒜) : q2 H π ⟨sig H π a, sig_mem H π a⟩ = π a :=
  ContinuousLinearMap.ext fun y => by
    rw [q2_apply, adjoint_inrCLM_apply]
    rfl

/-- `A** ⊆ q₁(M)`: the range of the injective normal `q₁` is a von Neumann
subalgebra (tree **48VI**) containing `π_u(𝒜)`. -/
theorem envAlg_le_range : envAlg 𝒜 ≤ (q1 H π).range := by
  refine sInf_le ⟨isVNSubalgebra_range_general (q1 H π) (q1_injective H π) (q1_normal H π),
    fun y hy => ?_⟩
  obtain ⟨a, rfl⟩ := starAlgHom_mem_range.mp hy
  exact starAlgHom_mem_range.mpr ⟨⟨sig H π a, sig_mem H π a⟩, q1_sig H π a⟩

theorem exists_pre (x : Bidual 𝒜) : ∃ m : MAlg H π, q1 H π m = x.val :=
  starAlgHom_mem_range.mp (envAlg_le_range H π x.property)

/-- `q₁⁻¹ : A** → M`. -/
def pre (x : Bidual 𝒜) : MAlg H π := (exists_pre H π x).choose

theorem q1_pre (x : Bidual 𝒜) : q1 H π (pre H π x) = x.val := (exists_pre H π x).choose_spec

/-- The extension `ρ = q₂ ∘ q₁⁻¹ : A** → B(H)` of `π`. -/
def extRep : Bidual 𝒜 →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun x := q2 H π (pre H π x)
  map_one' := by
    have : pre H π 1 = 1 := q1_injective H π (by rw [q1_pre, map_one]; rfl)
    rw [this, map_one]
  map_mul' x y := by
    have : pre H π (x * y) = pre H π x * pre H π y :=
      q1_injective H π (by rw [q1_pre, map_mul, q1_pre, q1_pre]; rfl)
    rw [this, map_mul]
  map_zero' := by
    have : pre H π 0 = 0 := q1_injective H π (by rw [q1_pre, map_zero]; rfl)
    rw [this, map_zero]
  map_add' x y := by
    have : pre H π (x + y) = pre H π x + pre H π y :=
      q1_injective H π (by rw [q1_pre, map_add, q1_pre, q1_pre]; rfl)
    rw [this, map_add]
  commutes' c := by
    have : pre H π (algebraMap ℂ (Bidual 𝒜) c) = algebraMap ℂ (MAlg H π) c :=
      q1_injective H π (by rw [q1_pre, AlgHomClass.commutes, vnSub_val_algebraMap])
    show q2 H π (pre H π (algebraMap ℂ (Bidual 𝒜) c)) = _
    rw [this, AlgHomClass.commutes]
  map_star' x := by
    have : pre H π (star x) = star (pre H π x) :=
      q1_injective H π (by rw [q1_pre, map_star, q1_pre]; rfl)
    show q2 H π (pre H π (star x)) = star (q2 H π (pre H π x))
    rw [this, map_star]

theorem extRep_apply (x : Bidual 𝒜) : extRep H π x = q2 H π (pre H π x) := rfl

/-- `ρ` extends `π`. -/
theorem extRep_emb (a : 𝒜) : extRep H π (bidualEmb a) = π a := by
  have : pre H π (bidualEmb a) = ⟨sig H π a, sig_mem H π a⟩ :=
    q1_injective H π (by rw [q1_pre, q1_sig]; rfl)
  rw [extRep_apply, this, q2_sig]

/-- `ρ` is normal: its vector functionals are vector functionals of `A**`. -/
theorem extRep_normal : PreservesDirSups ⇑(extRep H π) :=
  starAlgHom_preservesDirSups_of_vectors (extRep H π) Set.univ
    (fun R hR => ContinuousLinearMap.ext fun y => hR y trivial)
    (fun y _ => ⟨VNSub.restrictNP (vectorNP (uVec (vecFun π y))), fun x => by
      rw [extRep_apply, inner_q2, q1_pre, VNSub.restrictNP_apply, vectorNP_apply]⟩)

end Extension

/-! ### Uniqueness of normal extensions -/

section Unique

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- Two normal representations of `A**` that agree on `ι(𝒜)` are equal: their
equaliser is a von Neumann subalgebra (tree **47V**), whose image in `B(H_u)`
is one too (**48VI**) and contains `π_u(𝒜)`, hence `A**`. -/
theorem bidual_hom_ext {H : HilbObj.{u}} (ρ₁ ρ₂ : Bidual 𝒜 →⋆ₐ[ℂ] (H →L[ℂ] H))
    (h₁ : PreservesDirSups ⇑ρ₁) (h₂ : PreservesDirSups ⇑ρ₂)
    (h : ∀ a, ρ₁ (bidualEmb a) = ρ₂ (bidualEmb a)) : ρ₁ = ρ₂ := by
  obtain ⟨E, hE, hEset⟩ := vn_equalisers (⟨ρ₁, h₁⟩ : NMIUMap (Bidual 𝒜) (H →L[ℂ] H)) ⟨ρ₂, h₂⟩
  let φ : VNSub (Bidual 𝒜) E hE →⋆ₐ[ℂ] (uHilb 𝒜 →L[ℂ] uHilb 𝒜) := valHom.comp valHom
  have hφi : Function.Injective φ := fun z z' hz => VNSub.val_injective (VNSub.val_injective hz)
  have hφn : PreservesDirSups ⇑φ :=
    starAlgHom_preservesDirSups_of_vectors φ Set.univ
      (fun R hR => ContinuousLinearMap.ext fun y => hR y trivial)
      (fun y _ => ⟨VNSub.restrictNP (VNSub.restrictNP (vectorNP y)), fun z => rfl⟩)
  have hle : envAlg 𝒜 ≤ φ.range := by
    refine sInf_le ⟨isVNSubalgebra_range_general φ hφi hφn, fun y hy => ?_⟩
    obtain ⟨a, rfl⟩ := starAlgHom_mem_range.mp hy
    have hmem : bidualEmb a ∈ (E : Set (Bidual 𝒜)) := by
      rw [hEset]
      exact h a
    exact starAlgHom_mem_range.mpr ⟨⟨bidualEmb a, hmem⟩, rfl⟩
  refine StarAlgHom.ext fun x => ?_
  obtain ⟨z, hz⟩ := starAlgHom_mem_range.mp (hle x.property)
  have hzx : z.val = x := VNSub.val_injective hz
  have hx : x ∈ (E : Set (Bidual 𝒜)) := hzx ▸ z.property
  rw [hEset] at hx
  exact hx

end Unique

/-! ### FDS 2.5 without the named hypothesis -/

section Main

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **FDS 2.5** (`nrep_ex`, direct_sums.tex:315), the print's reason for
`NRep(A**) ≅ Rep(A)`, proved: `A** = π_u(𝒜)''` with `ι = π_u` satisfies
`IsRepEnvelope`: every representation of `𝒜` on a Hilbert space (in `𝒜`'s
universe) extends uniquely to a normal unital representation of `A**`. -/
theorem isRepEnvelope_bidual : IsRepEnvelope (bidualEmb (𝒜 := 𝒜)) := by
  intro H π
  refine ⟨extRep H π, ⟨extRep_normal H π, StarAlgHom.ext fun a => extRep_emb H π a⟩,
    fun ρ hρ => bidual_hom_ext ρ (extRep H π) hρ.1 (extRep_normal H π) fun a => ?_⟩
  rw [extRep_emb]
  exact DFunLike.congr_fun hρ.2 a

/-- The universal representation is faithful: `ι : 𝒜 → A**` is injective
(extend the Gelfand–Naimark representation, tree **30XIV**). -/
theorem bidualEmb_injective : Function.Injective (bidualEmb (𝒜 := 𝒜)) := by
  obtain ⟨H, i1, i2, i3, ρ, hρ⟩ := Theses.A.CStar.gelfand_naimark 𝒜
  obtain ⟨σ, ⟨-, hσ⟩, -⟩ := isRepEnvelope_bidual (@HilbObj.mk H i1 i2 i3) ρ
  intro a b hab
  apply hρ
  rw [← hσ, StarAlgHom.comp_apply, StarAlgHom.comp_apply, hab]

/-- **FDS 2.5** (`nrep_ex`, direct_sums.tex:315, Example), the clause
`NRep(A**) ≅ Rep(A)`, with no hypothesis: restriction along `ι : 𝒜 → A**`
is an equivalence `NRep(A**) ≌ Rep(𝒜)`, identity on intertwiners. -/
theorem nrep_bidual_equiv_rep :
    (restrictRep (bidualEmb (𝒜 := 𝒜))).IsEquivalence ∧
      (∀ {X Y : NRep (Bidual 𝒜)} (f : X ⟶ Y),
        (restrictRep (bidualEmb (𝒜 := 𝒜))).map f† = ((restrictRep bidualEmb).map f)†) ∧
      (∀ {X Y : NRep (Bidual 𝒜)} (f : X ⟶ Y),
        ‖(restrictRep (bidualEmb (𝒜 := 𝒜))).map f‖ = ‖f‖) :=
  nrep_equiv_rep isRepEnvelope_bidual

end Main

/-- For every unital C*-algebra there is an enveloping von Neumann algebra in
the sense of `IsRepEnvelope` (the order of `𝒜` is its C*-order). -/
theorem exists_isRepEnvelope (𝒜 : Type u) [CStarAlgebra 𝒜] :
    ∃ (N : Type u) (_ : CStarAlgebra N) (_ : PartialOrder N) (_ : StarOrderedRing N)
      (_ : VonNeumannAlgebra N) (ι : 𝒜 →⋆ₐ[ℂ] N), Function.Injective ι ∧ IsRepEnvelope ι := by
  let _ : PartialOrder 𝒜 := CStarAlgebra.spectralOrder 𝒜
  have _ : StarOrderedRing 𝒜 := CStarAlgebra.spectralOrderedRing 𝒜
  exact ⟨Bidual 𝒜, inferInstance, inferInstance, inferInstance, inferInstance, bidualEmb,
    bidualEmb_injective, isRepEnvelope_bidual⟩

end Env

end Papers.FDS
