/-
Thesis B companion: the note `wittrock-dil.tex`, **Proposition 8** and
**Corollary 14** — subalgebras of `𝓑(𝒦)` that split off their commutant, and
Wittrock dilations of ncp-maps into `𝓑(ℋ)`.

Like `Wittrock.lean` and `WittrockSplit.lean` this file has no thesis
counterpart and carries no DISP code.

The note's proof of Proposition 8, `⇒`, reduces to a factor `ℛ ⊆ 𝓑(𝒦)`
(Proposition 7 and `c𝓑(𝒦)c ≅ 𝓑(c𝒦)`), shows that the extension
`μ : ℛ ⊗ ℛ' → 𝓑(𝒦)` is an isomorphism, and then cites two facts from
Takesaki's *Theory of Operator Algebras I*: a tensor product of factors is
a factor, and a tensor factor of a type I factor is of type I.  Both are
proved here: the first (`isFactor_vnt`) from the tree's commutation
theorem, the second (`exists_bh_of_vnt_bh`: `𝒜 ⊗ ℬ ≅ 𝓑(𝒦)` gives
`𝒜 ≅ 𝓑(ℋ)`) with slice maps — `ℬ` has a minimal projection `q`, and
`𝒜 ≅ 𝒜 ⊗ q` is a corner of `𝓑(𝒦)`.  Nothing in this file uses `sorry`.
-/
import Theses.B.Dils.WittrockSplit
import Theses.B.Dils.SelfDual

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra TensorProduct ENNReal
open Filter Topology Theses Theses.A.VN Theses.A.Proc

noncomputable section

namespace Theses.B.Dils

universe u

/-! ## Small tools -/

section Tools

theorem vnsub_algebraMap_val {P : Type*} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
    {S : StarSubalgebra ℂ P} {hS : IsVNSubalgebra P S} (c : ℂ) :
    (algebraMap ℂ (Theses.A.Proc.VNSub P S hS) c).val = algebraMap ℂ P c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  rfl

/-- A ∗-isomorphism between two zero algebras. -/
def starAlgEquivOfSubsingleton {A' B' : Type*} [CStarAlgebra A'] [CStarAlgebra B']
    [Subsingleton A'] [Subsingleton B'] : A' ≃⋆ₐ[ℂ] B' where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _
  map_star' _ := Subsingleton.elim _ _
  map_smul' _ _ := Subsingleton.elim _ _

/-- Being a factor is invariant under ∗-isomorphisms. -/
theorem isFactor_of_starAlgEquiv {A' B' : Type*} [CStarAlgebra A'] [CStarAlgebra B']
    (e : A' ≃⋆ₐ[ℂ] B') (h : IsFactor A') : IsFactor B' := by
  intro z hz
  obtain ⟨c, hc⟩ := h (e.symm z) fun b => by
    have h1 : e (e.symm z * b) = e (b * e.symm z) := by
      rw [show e (e.symm z * b) = e (e.symm z) * e b from map_mul e _ _,
        show e (b * e.symm z) = e b * e (e.symm z) from map_mul e _ _,
        StarAlgEquiv.apply_symm_apply]
      exact hz (e b)
    exact e.injective h1
  refine ⟨c, ?_⟩
  rw [← e.apply_symm_apply z, hc]
  exact AlgHomClass.commutes e c

/-- An nmiu-map out of a factor into a non-zero algebra is injective: its
kernel is cut out by a central projection (**69IV**), which is `0` or `1`. -/
theorem nmiu_injective_of_isFactor {A' B' : Type u} [CStarAlgebra A'] [PartialOrder A']
    [StarOrderedRing A'] [VonNeumannAlgebra A'] [CStarAlgebra B'] [PartialOrder B']
    [StarOrderedRing B'] [VonNeumannAlgebra B'] [Nontrivial B'] (f : NMIUMap A' B')
    (hA : IsFactor A') : Function.Injective f := by
  have hf1 : f 1 = 1 := map_one f.toStarAlgHom
  obtain ⟨hcent, hker⟩ := carrier_miu f (nmiuP f) f.preservesDirSups' (fun _ => rfl)
  have hcrp := (carrier_spec (nmiuP f) f.preservesDirSups').1
  obtain ⟨l, hl⟩ := hA _ hcent
  have hAn : Nontrivial A' :=
    ⟨⟨1, 0, fun h => by
      have := congrArg f h
      rw [hf1, show f 0 = 0 from map_zero f.toStarAlgHom] at this
      exact one_ne_zero this⟩⟩
  have hl2 : l * l = l := (algebraMap ℂ A').injective (by
    rw [map_mul, ← hl, hcrp.isIdempotentElem.eq])
  rcases complex_idem hl2 with h0 | h1
  · exfalso
    have := (hker 1).mpr (by rw [hl, h0, map_zero, zero_mul])
    rw [hf1] at this
    exact one_ne_zero this
  · have hcr1 : carrier (nmiuP f) f.preservesDirSups' = 1 := by rw [hl, h1, map_one]
    intro a b hab
    have hab' : f (a - b) = 0 := by
      rw [show f (a - b) = f a - f b from map_sub f.toStarAlgHom a b, hab, sub_self]
    have := (hker (a - b)).mp hab'
    rw [hcr1, one_mul] at this
    exact sub_eq_zero.mp this

end Tools

/-! ## The corners of `𝓑(𝒦)` -/

section CornerIso

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `c𝓑(𝒦)c ≅ 𝓑(c𝒦)`, by compression `x ↦ sub^* x sub` with the corner
Hilbert space `c𝒦` of `A/Proc/CornerTensor.lean`. -/
def cornerBHEquiv (c : K →L[ℂ] K) [hc : Fact (IsStarProjection c)] :
    Corner (K →L[ℂ] K) c ≃⋆ₐ[ℂ] (Cnr c hc.out →L[ℂ] Cnr c hc.out) := by
  set r := cornerRep c hc.out
  have h : IsCorner r.sub c := r.isCorner
  refine StarAlgEquiv.ofBijective (({
      toFun := fun x => cmpr r.sub x.val
      map_one' := by
        change cmpr r.sub c = 1
        have := cmpr_mul_mid h 1 1
        rw [one_mul, mul_one, cmpr_one h, one_mul] at this
        exact this
      map_mul' := fun x y => by
        change cmpr r.sub (x.val * y.val) = cmpr r.sub x.val * cmpr r.sub y.val
        rw [← cmpr_mul_mid h, Corner.mul_right x]
      map_zero' := cmpr_zero _
      map_add' := fun _ _ => cmpr_add _ _ _
      commutes' := fun z => by
        change cmpr r.sub (algebraMap ℂ (Corner (K →L[ℂ] K) c) z).val = algebraMap ℂ _ z
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        change cmpr r.sub (z • c) = z • 1
        rw [cmpr_smul]
        congr 1
        have := cmpr_mul_mid h 1 1
        rw [one_mul, mul_one, cmpr_one h, one_mul] at this
        exact this
      map_star' := fun x => cmpr_star _ _ } :
        Corner (K →L[ℂ] K) c →⋆ₐ[ℂ] (Cnr c hc.out →L[ℂ] Cnr c hc.out)))
      ⟨fun x y hxy => ?_, fun y => ?_⟩
  · refine Corner.val_injective ?_
    have hx := cext_cmpr h x.val
    have hy := cext_cmpr h y.val
    rw [x.property] at hx
    rw [y.property] at hy
    rw [← hx, ← hy]
    exact congrArg (cext r.sub) hxy
  · refine ⟨⟨cext r.sub y, by rw [e_mul_cext h, cext_mul_e h]⟩, ?_⟩
    exact cmpr_cext h y

end CornerIso

/-! ## Slices, and a minimal projection of a tensor factor of `𝓑(𝒦)`

The slice maps `θ ⊗ id : 𝒜 ⊗ ℬ → ℬ` and `id ⊗ χ : 𝒜 ⊗ ℬ → 𝒜` by normal
states, and with them the first half of the proof of `exists_bh_of_vnt_bh`
below. -/

section Slices

/-- `ULift.down : ULift ℂ → ℂ` as an nmiu-map. -/
def uliftDownNMIU : NMIUMap (ULift.{u} ℂ) ℂ where
  toStarAlgHom :=
    { toFun := ULift.down
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl
      map_star' := fun _ => rfl }
  preservesDirSups' := uliftComplexDownNP.preservesDirSups'

@[simp] theorem uliftDownNMIU_apply (z : ULift.{u} ℂ) : uliftDownNMIU z = z.down := rfl

/-- A non-zero positive element is `1` under some np-functional: the
np-functionals are faithful (**42I**), and a positive multiple of one is one
(`smulNP`). -/
theorem exists_npFunctional_eq_one {P : Type*} [CStarAlgebra P] [PartialOrder P]
    [StarOrderedRing P] [VonNeumannAlgebra P] {p : P} (hp : 0 ≤ p) (hp0 : p ≠ 0) :
    ∃ ω : NPFunctional P, ω p = 1 := by
  obtain ⟨ω, hω⟩ : ∃ ω : NPFunctional P, ω p ≠ 0 := by
    by_contra h
    push Not at h
    exact hp0 (VonNeumannAlgebra.np_faithful p hp h)
  obtain ⟨hre, him⟩ := Complex.le_def.mp (npFunctional_nonneg ω hp)
  have hpos : 0 < (ω p).re := lt_of_le_of_ne (by simpa using hre) fun h =>
    hω (Complex.ext (by simp [← h]) (by simp [← him]))
  refine ⟨smulNP (inv_nonneg.mpr hpos.le) ω, ?_⟩
  change (((ω p).re⁻¹ : ℝ) : ℂ) * ω p = 1
  rw [← Complex.re_add_im (ω p), ← him]
  simp [hpos.ne']

variable {A B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [VonNeumannAlgebra B]

/-- An np-functional `ω` as the ncp-map `a ↦ ω(a)` into `ULift ℂ`, the copy
of the scalars in the universe of `𝒜`. -/
def npULift (ω : NPFunctional A) : NCPMap A (ULift.{u} ℂ) where
  toCompletelyPositiveMap :=
    { toLinearMap := (ULift.moduleEquiv (R := ℂ) (M := ℂ)).symm.toLinearMap.comp (npLin ω)
      map_cstarMatrix_nonneg' := (Theses.A.CStar.cp_iff _).out 0 1 |>.mp
        (Theses.A.CStar.cp_comp _ _
          (Theses.A.CStar.cp_commutative_cod _ fun a ha => npFunctional_nonneg ω ha)
          (Theses.A.CStar.cp_of_mi _ (fun _ _ => rfl) (fun _ => rfl))) }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have h := ω.preservesDirSups' D s hne hdir hlub
    refine ⟨?_, fun w hw => ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      exact h.1 ⟨d, hd, rfl⟩
    · exact h.2 fun _ ⟨d, hd, hdz⟩ => hdz ▸ hw ⟨d, hd, rfl⟩

omit [VonNeumannAlgebra A] in
@[simp] theorem npULift_apply (ω : NPFunctional A) (a : A) : npULift ω a = ULift.up (ω a) := rfl

/-- The slice `a ⊗ b ↦ ω(a) b : 𝒜 ⊗ ℬ → ℬ`: `ω ⊗ id` (**115II**) followed by
`ℂ ⊗ ℬ ≅ ℬ` (the left unitor, **119IVb**).  The scalars pass through their
copy `ULift ℂ`, as `tmap` wants its four algebras in one universe. -/
def sliceLeft (ω : NPFunctional A) : NCPMap (VNT A B) B :=
  ncpComp (nmiuNCP (nmiuComp (leftUnitor B) (tmapM uliftDownNMIU (nmiuId B))))
    (tmap (npULift ω) (ncpId B))

theorem sliceLeft_apply (ω : NPFunctional A) (a : A) (b : B) :
    sliceLeft ω (a ⊗ᵥ b) = ω a • b := by
  rw [sliceLeft, ncpComp_apply, tmap_apply, nmiuNCP_apply, nmiuComp_apply, tmapM_apply,
    leftUnitor_apply, npULift_apply, ncpId_apply, uliftDownNMIU_apply, nmiuId_apply]

/-- The slice `a ⊗ b ↦ ω(b) a : 𝒜 ⊗ ℬ → 𝒜`, the mirror of `sliceLeft`. -/
def sliceRight (ω : NPFunctional B) : NCPMap (VNT A B) A :=
  ncpComp (nmiuNCP (nmiuComp (rightUnitor A) (tmapM (nmiuId A) uliftDownNMIU)))
    (tmap (ncpId A) (npULift ω))

theorem sliceRight_apply (ω : NPFunctional B) (a : A) (b : B) :
    sliceRight ω (a ⊗ᵥ b) = ω b • a := by
  rw [sliceRight, ncpComp_apply, tmap_apply, nmiuNCP_apply, nmiuComp_apply, tmapM_apply,
    rightUnitor_apply, npULift_apply, ncpId_apply, uliftDownNMIU_apply, nmiuId_apply]

theorem vtmul_star' (a : A) (b : B) : star (a ⊗ᵥ b) = star a ⊗ᵥ star b :=
  (vnTensor A B).isTensorProduct.miu.2.2 a b

theorem vtmul_mul_vtmul' (a a' : A) (b b' : B) :
    (a ⊗ᵥ b) * (a' ⊗ᵥ b') = (a * a') ⊗ᵥ (b * b') :=
  ((vnTensor A B).isTensorProduct.miu.2.1 a a' b b').symm

/-- If `𝒜 ⊗ ℬ ≅ 𝓑(𝒦)` with `𝒜` and `ℬ` non-zero, then `ℬ` has a minimal
projection.  Identify `𝒜 ⊗ ℬ` with `𝓑(𝒦)` along `e`, and let
`S = θ ⊗ id : 𝒜 ⊗ ℬ → ℬ` be the slice by a normal state `θ` of `𝒜`
(`sliceLeft`); it satisfies `S((1 ⊗ q) w (1 ⊗ q)) = q S(w) q` (both sides
are ncp in `w`, `ncp_ext_vnt`).  Some vector `ξ` makes `y = S(|ξ⟩⟨ξ|)`
non-zero: for a normal state `ψ` of `ℬ`, the normal state `ψ ∘ S` of
`𝓑(𝒦)` is `∑ₙ ⟪xₙ, (·) xₙ⟫` (**39IX**), and `ξ = xₙ ≠ 0` will do.  For
a projection `q` of `ℬ` and `Q = 1 ⊗ q`, `Q|ξ⟩⟨ξ|Q = |Qξ⟩⟨Qξ| ≤ ‖Qξ‖² Q`,
so `qyq ≤ ν(q) q` with `ν(q) = ⟪ξ, Qξ⟫`, which is additive in `q`.  The
spectral projection `q₀ = ⌈(y − δ)⁺⌉` is non-zero for small `δ > 0` and has
`δ q₀ ≤ q₀ y q₀`, so `ν ≥ δ` on the non-zero projections below `q₀`.  One
of these whose `ν` is less than `δ` above the infimum is minimal: splitting
it into two non-zero projections would put its `ν` at least `δ` above the
infimum. -/
theorem exists_isMinimalProjection_of_vnt_bh [Nontrivial A] [Nontrivial B] {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : VNT A B ≃⋆ₐ[ℂ] (K →L[ℂ] K)) : ∃ q : B, IsMinimalProjection q := by
  obtain ⟨θ, hθ⟩ := exists_npFunctional_eq_one (P := A) zero_le_one one_ne_zero
  obtain ⟨ψ, hψ⟩ := exists_npFunctional_eq_one (P := B) zero_le_one one_ne_zero
  set S : NCPMap (VNT A B) B := sliceLeft θ
  have hone : (1 : A) ⊗ᵥ (1 : B) = 1 := (vnTensor A B).isTensorProduct.miu.1
  have hS1 : ∀ b : B, S ((1 : A) ⊗ᵥ b) = b := fun b => by
    rw [sliceLeft_apply, hθ, one_smul]
  -- `S` is a bimodule map over `1 ⊗ ℬ`
  have hbimod : ∀ (c : B) (w : VNT A B),
      S (star ((1 : A) ⊗ᵥ c) * w * ((1 : A) ⊗ᵥ c)) = star c * S w * c := by
    intro c w
    have h := ncp_ext_vnt (ncpComp S (adSelf ((1 : A) ⊗ᵥ c))) (ncpComp (adSelf c) S)
      fun a b => by
        rw [ncpComp_apply, ncpComp_apply, adSelf_apply, adSelf_apply, vtmul_star', star_one,
          vtmul_mul_vtmul', vtmul_mul_vtmul', one_mul, mul_one, sliceLeft_apply,
          sliceLeft_apply, mul_smul_comm, smul_mul_assoc]
    have h' := congrArg (fun f : NCPMap (VNT A B) B => f w) h
    simpa only [ncpComp_apply, adSelf_apply] using h'
  -- a vector `ξ` with `y = S(e⁻¹|ξ⟩⟨ξ|) ≠ 0`, from the vector form (**39IX**) of
  -- the normal state `ψ ∘ S ∘ e⁻¹` of `𝓑(𝒦)`
  set F : NCPMap (K →L[ℂ] K) B :=
    ncpComp S (nmiuNCP (nmiuOfBijective e.symm.toStarAlgHom e.symm.bijective))
  have hF : ∀ T, F T = S (e.symm T) := fun T => by
    rw [ncpComp_apply, nmiuNCP_apply]; rfl
  set ω : NPFunctional (K →L[ℂ] K) := compNP (ncpPositive F) F.preservesDirSups' ψ
  have hω : ∀ T, ω T = ψ (S (e.symm T)) := fun T => by
    rw [← hF]; rfl
  obtain ⟨x, hx, hx1⟩ := Theses.A.CStar.bh_np ω
  rw [hω, map_one, ← hone, hS1, hψ] at hx1
  obtain ⟨m, hm⟩ : ∃ m, x m ≠ 0 := by
    by_contra h
    push Not at h
    refine one_ne_zero (hx1.unique ?_)
    simp [h]
  set ξ := x m
  set X : K →L[ℂ] K := InnerProductSpace.rankOne ℂ ξ ξ
  have hX : 0 ≤ X := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (InnerProductSpace.isPositive_rankOne_self ξ)
  set y := S (e.symm X)
  have hy : 0 ≤ y := by
    have h := OrderHomClass.mono F.toCompletelyPositiveMap hX
    rw [map_zero] at h
    exact h.trans_eq (hF X)
  have hy0 : y ≠ 0 := by
    intro hy0
    have hre := Complex.hasSum_re (hx X)
    rw [hω] at hre
    change HasSum _ (ψ y).re at hre
    rw [hy0, npFunctional_zero] at hre
    have hterm : ∀ n, (⟪x n, X (x n)⟫).re = ‖⟪ξ, x n⟫‖ ^ 2 := fun n => by
      rw [InnerProductSpace.rankOne_apply, inner_smul_right, ← inner_conj_symm (x n) ξ,
        Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    have hle := le_hasSum hre m fun n _ => by rw [hterm]; positivity
    rw [hterm, Complex.zero_re] at hle
    have h0 : ⟪ξ, ξ⟫ = (0 : ℂ) := norm_eq_zero.mp (by nlinarith [norm_nonneg ⟪ξ, ξ⟫])
    exact hm (inner_self_eq_zero.mp h0)
  -- the additive weight `ν(q) = ⟪ξ, e(1 ⊗ q) ξ⟫`, and `q y q ≤ ν(q) q`
  set ν : B → ℝ := fun q => (⟪ξ, e ((1 : A) ⊗ᵥ q) ξ⟫).re
  have hνadd : ∀ a b : B, ν (a + b) = ν a + ν b := fun a b => by
    simp only [ν, vtmul_add_right', map_add, add_apply, inner_add_right, Complex.add_re]
  have hkey : ∀ q : B, IsStarProjection q → q * y * q ≤ ((ν q : ℝ) : ℂ) • q := by
    intro q hq
    have h1q : IsStarProjection ((1 : A) ⊗ᵥ q) :=
      ⟨by rw [IsIdempotentElem, vtmul_mul_vtmul', one_mul, hq.isIdempotentElem.eq],
        by rw [IsSelfAdjoint, vtmul_star', star_one, hq.isSelfAdjoint.star_eq]⟩
    set Q := e ((1 : A) ⊗ᵥ q)
    have hQ : IsStarProjection Q := h1q.map e
    -- `QXQ = |Qξ⟩⟨Qξ|`, of norm `‖Qξ‖² = ν(q)`
    have hQXQ : Q * X * Q = InnerProductSpace.rankOne ℂ (Q ξ) (Q ξ) := by
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
        InnerProductSpace.comp_rankOne, InnerProductSpace.rankOne_comp,
        ← ContinuousLinearMap.star_eq_adjoint, hQ.isSelfAdjoint.star_eq]
    have hnorm : ‖Q * X * Q‖ = ν q := by
      rw [hQXQ, InnerProductSpace.norm_rankOne, ← sq, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
      simp only [ν]
      rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
        hQ.isSelfAdjoint.star_eq, ← mul_apply_eq_comp, hQ.isIdempotentElem.eq]
      rfl
    have hop : Q * X * Q ≤ ((ν q : ℝ) : ℂ) • Q := by
      have h := (IsSelfAdjoint.of_nonneg (conjugate_nonneg_of_nonneg hX hQ.nonneg)
        ).le_algebraMap_norm_self
      have h2 := star_left_conjugate_le_conjugate h Q
      rw [hQ.isSelfAdjoint.star_eq, hnorm, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
        mul_one, smul_mul_assoc, hQ.isIdempotentElem.eq, ← Complex.coe_smul] at h2
      calc Q * X * Q = (Q * Q) * X * (Q * Q) := by rw [hQ.isIdempotentElem.eq]
        _ = Q * (Q * X * Q) * Q := by noncomm_ring
        _ ≤ _ := h2
    -- back through `e⁻¹` (an order isomorphism) and `S`
    have hback : ((1 : A) ⊗ᵥ q) * e.symm X * ((1 : A) ⊗ᵥ q)
        ≤ ((ν q : ℝ) : ℂ) • ((1 : A) ⊗ᵥ q) := by
      rw [← map_le_map_iff e, map_mul, map_mul, map_smul, StarAlgEquiv.apply_symm_apply]
      exact hop
    have h := OrderHomClass.mono S.toCompletelyPositiveMap hback
    change S _ ≤ S _ at h
    have hb := hbimod q (e.symm X)
    rw [h1q.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] at hb
    rwa [wncp_smul, hS1, hb] at h
  -- a spectral projection `q₀ = ⌈(y − δ)⁺⌉ ≠ 0`, with `δ q₀ ≤ q₀ y q₀`
  obtain ⟨δ, hδ, hδy⟩ : ∃ δ : ℝ, 0 < δ ∧ ¬ y ≤ (δ : ℂ) • (1 : B) := by
    by_contra h
    push Not at h
    have h0 : y ≤ ((0 : ℝ) : ℂ) • (1 : B) := le_smul_of_forall_gt h
    rw [Complex.ofReal_zero, zero_smul] at h0
    exact hy0 (le_antisymm h0 hy)
  set z := y - (δ : ℂ) • (1 : B)
  have hz : IsSelfAdjoint z := isSelfAdjoint_sub_smul_one (IsSelfAdjoint.of_nonneg hy) δ
  set q₀ := ceil (z⁺)
  have hq₀ : IsStarProjection q₀ := (ceil_spec (CFC.posPart_nonneg z)).1
  have hq₀0 : q₀ ≠ 0 := fun h => hδy ((le_smul_one_iff_posPart_eq_zero
    (IsSelfAdjoint.of_nonneg hy) δ).mpr ((ceil_basic_3 _ (CFC.posPart_nonneg z)).mpr h))
  have hq₀y : (δ : ℂ) • q₀ ≤ q₀ * y * q₀ := by
    -- `z⁻ q₀ = z⁻ ⌈z⁻⌉ ⌈z⁺⌉ = 0` (**59IV**), so `q₀ z q₀ = q₀ z⁺ q₀ ≥ 0`
    have hneg : z⁻ * q₀ = 0 := by
      have h1 := (ceil_spec (CFC.negPart_nonneg z)).2.1
      have h2 : ceil (z⁻) * q₀ = 0 := by
        have h3 := congrArg star (ceil_pos_part_1 z hz)
        rwa [star_mul, star_zero, (ceil_spec (CFC.posPart_nonneg z)).1.isSelfAdjoint.star_eq,
          (ceil_spec (CFC.negPart_nonneg z)).1.isSelfAdjoint.star_eq] at h3
      rw [← h1, mul_assoc, h2, mul_zero]
    have hpos : 0 ≤ q₀ * z * q₀ := by
      rw [← CFC.posPart_sub_negPart z hz, mul_sub, sub_mul, mul_assoc q₀ (z⁻), hneg, mul_zero,
        sub_zero]
      exact conjugate_nonneg_of_nonneg (CFC.posPart_nonneg z) hq₀.nonneg
    rwa [mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, hq₀.isIdempotentElem.eq,
      sub_nonneg] at hpos
  -- `ν ≥ δ` on the non-zero projections below `q₀`
  have hlow : ∀ q : B, IsStarProjection q → q ≠ 0 → q ≤ q₀ → δ ≤ ν q := by
    intro q hq hq0 hle
    have hqq₀ : q * q₀ = q := (hq.le_iff_mul_eq_left hq₀).mp hle
    have hq₀q : q₀ * q = q := (hq.le_iff_mul_eq_right hq₀).mp hle
    have h := star_left_conjugate_le_conjugate hq₀y q
    rw [hq.isSelfAdjoint.star_eq, mul_smul_comm, smul_mul_assoc, hqq₀, hq.isIdempotentElem.eq,
      show q * (q₀ * y * q₀) * q = q * y * q by
        rw [← mul_assoc, ← mul_assoc, hqq₀, mul_assoc, hq₀q]] at h
    have h2 : (0 : B) ≤ ((ν q - δ : ℝ) : ℂ) • q := by
      rw [Complex.ofReal_sub, sub_smul, sub_nonneg]
      exact h.trans (hkey q hq)
    linarith [(smul_nonneg_iff_of_ne_zero hq.nonneg hq0).mp h2]
  -- a projection below `q₀` whose `ν` is less than `δ` above the infimum is minimal
  set P : Set B := {q | IsStarProjection q ∧ q ≠ 0 ∧ q ≤ q₀}
  have hPne : (ν '' P).Nonempty := ⟨ν q₀, q₀, ⟨hq₀, hq₀0, le_rfl⟩, rfl⟩
  have hPbdd : BddBelow (ν '' P) :=
    ⟨δ, by rintro _ ⟨q, hq, rfl⟩; exact hlow q hq.1 hq.2.1 hq.2.2⟩
  obtain ⟨_, ⟨q, hqP, rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt hPne (lt_add_of_pos_right (sInf (ν '' P)) hδ)
  refine ⟨q, hqP.1, hqP.2.1, fun q' hq' hle => ?_⟩
  by_contra hcon
  push Not at hcon
  have hd : IsStarProjection (q - q') := (hq'.le_iff_sub hqP.1).mp hle
  have hm1 : sInf (ν '' P) ≤ ν q' :=
    csInf_le hPbdd ⟨q', ⟨hq', hcon.1, hle.trans hqP.2.2⟩, rfl⟩
  have hm2 : δ ≤ ν (q - q') := hlow _ hd (sub_ne_zero.mpr hcon.2.symm)
    ((sub_le_self q hq'.nonneg).trans hqP.2.2)
  have hsplit : ν q = ν q' + ν (q - q') := by rw [← hνadd, add_sub_cancel]
  linarith

end Slices

/-! ## The two facts from Takesaki

The first is proved from the commutation theorem, the second with the slice
maps of the previous section. -/

section Takesaki

variable {A B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [VonNeumannAlgebra B]

/-- The concrete tensor product `𝒜 ⊗̄ ℬ ⊆ 𝓑(ℋ ⊗ 𝒦)` of two von Neumann
algebras with trivial centres has trivial centre: its centre is
`(𝒜 ⊗̄ ℬ) ∩ (𝒜' ⊗̄ ℬ') = (𝒜 ∩ 𝒜') ⊗̄ (ℬ ∩ ℬ')` (the commutation theorem and
**121II**). -/
theorem isFactor_concreteTensor {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (SA : StarSubalgebra ℂ (H →L[ℂ] H)) (SB : StarSubalgebra ℂ (K →L[ℂ] K))
    (hA : IsVNSubalgebra _ SA) (hB : IsVNSubalgebra _ SB)
    (hcA : ∀ x ∈ SA, x ∈ vnComm SA → ∃ c : ℂ, x = c • 1)
    (hcB : ∀ x ∈ SB, x ∈ vnComm SB → ∃ c : ℂ, x = c • 1) :
    IsFactor (Theses.A.Proc.VNSub (HT H K →L[ℂ] HT H K) (concreteTensor H K SA SB)
      (isVNSubalgebra_concreteTensor _ _)) := by
  intro z hz
  have hzC : z.val ∈ vnComm (concreteTensor H K SA SB) :=
    mem_vnComm.mpr fun s hs => (congrArg Theses.A.Proc.VNSub.val (hz ⟨s, hs⟩)).symm
  rw [commutation_theorem SA SB hA hB] at hzC
  have hz2 : z.val ∈ concreteTensor H K SA SB ⊓ concreteTensor H K (vnComm SA) (vnComm SB) :=
    ⟨z.property, hzC⟩
  rw [intersection_tensor' SA (vnComm SA) SB (vnComm SB) hA (isVNSubalgebra_vnComm _) hB
    (isVNSubalgebra_vnComm _)] at hz2
  have hle : concreteTensor H K (SA ⊓ vnComm SA) (SB ⊓ vnComm SB)
      ≤ vnComm (⊤ : StarSubalgebra ℂ (HT H K →L[ℂ] HT H K)) := by
    refine sInf_le ⟨isVNSubalgebra_vnComm _, ?_⟩
    rintro _ ⟨a, ⟨haR, hac⟩, b, ⟨hbR, hbc⟩, rfl⟩
    obtain ⟨c, rfl⟩ := hcA a haR hac
    obtain ⟨d, rfl⟩ := hcB b hbR hbc
    refine mem_vnComm_top.mpr ⟨c * d, ?_⟩
    rw [opTensor_smul_left, opTensor_smul_right, opTensor_one, smul_smul]
  obtain ⟨c, hc⟩ := mem_vnComm_top.mp (hle hz2)
  exact ⟨c, Theses.A.Proc.VNSub.val_injective (by
    rw [hc, vnsub_algebraMap_val, Algebra.algebraMap_eq_smul_one])⟩

/-- A tensor product of factors is a factor (the first of the two facts the
note cites from Takesaki).  Represent `𝒜`, `ℬ` faithfully and normally
(**48VIII**) as `ℛ_𝒜 ⊆ 𝓑(ℋ)`, `ℛ_ℬ ⊆ 𝓑(𝒦)`; then `𝒜 ⊗ ℬ ≅ ℛ_𝒜 ⊗̄ ℛ_ℬ`
(**111VII**, **114II**), whose centre is
`(ℛ_𝒜 ⊗̄ ℛ_ℬ) ∩ (ℛ_𝒜' ⊗̄ ℛ_ℬ') = (ℛ_𝒜 ∩ ℛ_𝒜') ⊗̄ (ℛ_ℬ ∩ ℛ_ℬ') = ℂ`
by the commutation theorem and **121II** (`commutation_theorem`,
`intersection_tensor'`). -/
theorem isFactor_vnt (hA : IsFactor A) (hB : IsFactor B) : IsFactor (VNT A B) := by
  obtain ⟨ιA, fA, hfA, hRA⟩ := ngns A
  obtain ⟨ιB, fB, hfB, hRB⟩ := ngns B
  set RA := fA.toStarAlgHom.range
  set RB := fB.toStarAlgHom.range
  set φA := nmiuCorestrict fA RA hRA (fun a => ⟨a, rfl⟩)
  have hφA : Function.Bijective φA :=
    nmiuCorestrict_bijective _ _ _ _ hfA (fun _ ⟨a, ha⟩ => ⟨a, ha⟩)
  set φB := nmiuCorestrict fB RB hRB (fun b => ⟨b, rfl⟩)
  have hφB : Function.Bijective φB :=
    nmiuCorestrict_bijective _ _ _ _ hfB (fun _ ⟨b, hb⟩ => ⟨b, hb⟩)
  obtain ⟨γ₀, -, hγ₀⟩ := special_tensor RA RB hRA hRB
  have hγ₁ := isTensorProduct_comp φA hφA φB hφB hγ₀
  obtain ⟨Ψ, -, hΨb, -⟩ :=
    tensor_uniqueness (vnTensor A B).map _ (vnTensor A B).isTensorProduct hγ₁
  -- the centres of `ℛ_𝒜` and `ℛ_ℬ` are `ℂ`
  have hcen : ∀ {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
      [VonNeumannAlgebra C] {ι : Type u} (f : NMIUMap C (lp (fun _ : ι => ℂ) 2 →L[ℂ]
        lp (fun _ : ι => ℂ) 2)), Function.Injective f → IsFactor C →
      ∀ x, x ∈ f.toStarAlgHom.range → x ∈ vnComm f.toStarAlgHom.range →
        ∃ c : ℂ, x = c • 1 := by
    intro C _ _ _ _ ι f hf hC x hx hxc
    obtain ⟨a, rfl⟩ := hx
    have hfm : ∀ a b, f (a * b) = f a * f b := fun a b => map_mul f.toStarAlgHom a b
    obtain ⟨c, hc⟩ := hC a fun b => hf (by
      rw [hfm, hfm]
      exact (mem_vnComm.mp hxc _ ⟨b, rfl⟩).symm)
    refine ⟨c, ?_⟩
    change f a = c • 1
    rw [hc, show f (algebraMap ℂ C c) = algebraMap ℂ _ c from f.toStarAlgHom.commutes c,
      Algebra.algebraMap_eq_smul_one]
  have hfacT := isFactor_concreteTensor RA RB hRA hRB (hcen fA hfA hA) (hcen fB hfB hB)
  exact isFactor_of_starAlgEquiv (StarAlgEquiv.ofBijective Ψ.toStarAlgHom hΨb).symm hfacT

/-- The second of the two facts the note cites from Takesaki (*Theory of
Operator Algebras I*, Ch. V): a tensor factor of a type I factor is of type I.
Precisely: if `𝒜 ⊗ ℬ ≅ 𝓑(𝒦)` as ∗-algebras, with `𝒜` and `ℬ` non-zero,
then `𝒜 ≅ 𝓑(ℋ)` for a Hilbert space `ℋ` in the universe of `𝒜`.

Identify `𝒜 ⊗ ℬ` with `𝓑(𝒦)` along `e`.  `ℬ` has a minimal projection `q`
(`exists_isMinimalProjection_of_vnt_bh`), so `qbq = χ(b) q` for a normal
state `χ` of `ℬ` (`IsMinimalProjection.corner_eq_smul`), and
`(1 ⊗ q) w (1 ⊗ q) = (id ⊗ χ)(w) ⊗ q` for all `w` (both sides are ncp in
`w`, `ncp_ext_vnt`; `id ⊗ χ` is `sliceRight`).  So `a ↦ a ⊗ q` maps `𝒜`
onto the corner of `𝓑(𝒦)` at the projection `Q = 1 ⊗ q`, which is
`𝓑(Q𝒦)` (`cornerBHEquiv`); it is injective as `‖a ⊗ q‖ = ‖a‖ ‖q‖`
(**116III**.2).  That `ℬ` is a factor is not needed.  Used through the
factor case `exists_bh_of_factor_splits`, i.e. by Proposition 8, `⇒`, and
Corollary 14, `⇒` and its "in particular". -/
theorem exists_bh_of_vnt_bh [Nontrivial A] [Nontrivial B] {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : VNT A B ≃⋆ₐ[ℂ] (K →L[ℂ] K)) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H), Nonempty (A ≃⋆ₐ[ℂ] (H →L[ℂ] H)) := by
  obtain ⟨q, hq⟩ := exists_isMinimalProjection_of_vnt_bh e
  have hqp := hq.isStarProjection
  have hsmul : ∀ (c : ℂ) (a : A) (b : B), (c • a) ⊗ᵥ b = c • (a ⊗ᵥ b) := fun c a b => by
    change (vnTensor A B).map (c • a) b = c • (vnTensor A B).map a b
    rw [map_smul, LinearMap.smul_apply]
  have hadd : ∀ (a a' : A) (b : B), (a + a') ⊗ᵥ b = a ⊗ᵥ b + a' ⊗ᵥ b := fun a a' b => by
    change (vnTensor A B).map (a + a') b = (vnTensor A B).map a b + (vnTensor A B).map a' b
    rw [map_add, LinearMap.add_apply]
  -- `qbq = χq(b) q` for the normal functional `χq(b) = χ(qbq)`, where `χ(q) = 1`
  obtain ⟨χ, hχ⟩ := exists_npFunctional_eq_one hqp.nonneg hq.ne_zero
  set χq : NPFunctional B := compNP (ncpPositive (adSelf q)) (adSelf q).preservesDirSups' χ
  have hcorner_q : ∀ b : B, q * b * q = χq b • q := by
    intro b
    have hsa : ∀ x : B, IsSelfAdjoint x → ∃ r : ℝ, q * x * q = (r : ℂ) • q := by
      intro x hx
      refine hq.corner_eq_smul (by rw [IsSelfAdjoint, star_mul, star_mul, hx.star_eq,
        hqp.isSelfAdjoint.star_eq, mul_assoc]) ?_
      calc q * (q * x * q) * q = (q * q) * x * (q * q) := by noncomm_ring
        _ = q * x * q := by rw [hqp.isIdempotentElem.eq]
    obtain ⟨r₁, h₁⟩ := hsa _ (realPart b).property
    obtain ⟨r₂, h₂⟩ := hsa _ (imaginaryPart b).property
    have hc : q * b * q = ((r₁ : ℂ) + Complex.I * r₂) • q := by
      conv_lhs => rw [← realPart_add_I_smul_imaginaryPart b]
      rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, h₁, h₂, smul_smul, add_smul]
    have hχc : χq b = (r₁ : ℂ) + Complex.I * r₂ := by
      change χ (adSelf q b) = _
      rw [adSelf_apply, hqp.isSelfAdjoint.star_eq, hc]
      have h : χ (((r₁ : ℂ) + Complex.I * r₂) • q) = ((r₁ : ℂ) + Complex.I * r₂) • χ q :=
        map_smul χ.toPositiveLinearMap _ q
      rw [h, hχ, smul_eq_mul, mul_one]
    rw [hc, hχc]
  -- the corner of `𝒜 ⊗ ℬ` at `1 ⊗ q` is `𝒜 ⊗ q`: `(1 ⊗ q) w (1 ⊗ q) = T(w) ⊗ q`
  set T : NCPMap (VNT A B) A := sliceRight χq
  have h1q : IsSelfAdjoint ((1 : A) ⊗ᵥ q) := by
    rw [IsSelfAdjoint, vtmul_star', star_one, hqp.isSelfAdjoint.star_eq]
  have hcorner : ∀ w : VNT A B, ((1 : A) ⊗ᵥ q) * w * ((1 : A) ⊗ᵥ q) = T w ⊗ᵥ q := by
    intro w
    have h := ncp_ext_vnt (adSelf ((1 : A) ⊗ᵥ q))
      (ncpComp (adSelf ((1 : A) ⊗ᵥ q)) (ncpComp (nmiuNCP (vtmulOneNMIU A B)) T)) fun a b => by
        rw [ncpComp_apply, ncpComp_apply, adSelf_apply, adSelf_apply, h1q.star_eq, nmiuNCP_apply,
          vtmulOneNMIU_apply, sliceRight_apply, vtmul_mul_vtmul', vtmul_mul_vtmul',
          vtmul_mul_vtmul', vtmul_mul_vtmul', hcorner_q]
        simp only [one_mul, mul_one, hqp.isIdempotentElem.eq, hsmul, vtmul_smul_right']
    have h' := congrArg (fun f : NCPMap (VNT A B) (VNT A B) => f w) h
    simp only [ncpComp_apply, adSelf_apply, h1q.star_eq, nmiuNCP_apply, vtmulOneNMIU_apply,
      vtmul_mul_vtmul', one_mul, mul_one, hqp.isIdempotentElem.eq] at h'
    exact h'
  -- `a ↦ e(a ⊗ q)` is a ∗-isomorphism of `𝒜` onto the corner at `Q = e(1 ⊗ q)`
  set Q := e ((1 : A) ⊗ᵥ q)
  have hQ : IsStarProjection Q :=
    (⟨by rw [IsIdempotentElem, vtmul_mul_vtmul', one_mul, hqp.isIdempotentElem.eq], h1q⟩ :
      IsStarProjection ((1 : A) ⊗ᵥ q)).map e
  have : Fact (IsStarProjection Q) := ⟨hQ⟩
  have hmem : ∀ a : A, Q * e (a ⊗ᵥ q) * Q = e (a ⊗ᵥ q) := fun a => by
    rw [← map_mul, ← map_mul, vtmul_mul_vtmul', vtmul_mul_vtmul', one_mul, mul_one,
      hqp.isIdempotentElem.eq, hqp.isIdempotentElem.eq]
  let π : A →⋆ₐ[ℂ] Corner (K →L[ℂ] K) Q :=
    { toFun := fun a => ⟨e (a ⊗ᵥ q), hmem a⟩
      map_one' := rfl
      map_mul' := fun a a' => Corner.val_injective (by
        change e ((a * a') ⊗ᵥ q) = e (a ⊗ᵥ q) * e (a' ⊗ᵥ q)
        rw [← map_mul, vtmul_mul_vtmul', hqp.isIdempotentElem.eq])
      map_zero' := Corner.val_injective (by
        change e ((0 : A) ⊗ᵥ q) = 0
        rw [← zero_smul ℂ (0 : A), hsmul, zero_smul, map_zero])
      map_add' := fun a a' => Corner.val_injective (by
        change e ((a + a') ⊗ᵥ q) = e (a ⊗ᵥ q) + e (a' ⊗ᵥ q)
        rw [hadd, map_add])
      commutes' := fun r => Corner.val_injective (by
        change e (algebraMap ℂ A r ⊗ᵥ q) = (algebraMap ℂ (Corner (K →L[ℂ] K) Q) r).val
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Corner.val_smul,
          Corner.val_one, hsmul, map_smul])
      map_star' := fun a => Corner.val_injective (by
        change e (star a ⊗ᵥ q) = star (e (a ⊗ᵥ q))
        rw [← map_star, vtmul_star', hqp.isSelfAdjoint.star_eq]) }
  have hinj : Function.Injective π := fun a a' h => by
    have h1 : (a - a') ⊗ᵥ q = 0 := by
      rw [sub_eq_add_neg, hadd, ← neg_one_smul ℂ a', hsmul, e.injective (congrArg Corner.val h),
        neg_one_smul, add_neg_cancel]
    have h2 := norm_vtmul (a - a') q
    rw [h1, norm_zero, eq_comm, mul_eq_zero, norm_eq_zero, norm_eq_zero] at h2
    exact sub_eq_zero.mp (h2.resolve_right hq.ne_zero)
  have hsurj : Function.Surjective π := fun t => by
    have hz : ((1 : A) ⊗ᵥ q) * e.symm t.val * ((1 : A) ⊗ᵥ q) = e.symm t.val := by
      conv_rhs => rw [← t.property]
      have hQs : e.symm Q = (1 : A) ⊗ᵥ q := e.symm_apply_apply _
      rw [map_mul e.symm, map_mul e.symm, hQs]
    refine ⟨T (e.symm t.val), Corner.val_injective ?_⟩
    change e (T (e.symm t.val) ⊗ᵥ q) = t.val
    rw [← hcorner, hz, e.apply_symm_apply]
  exact ⟨_, inferInstance, inferInstance, inferInstance,
    ⟨(StarAlgEquiv.ofBijective π ⟨hinj, hsurj⟩).trans (cornerBHEquiv Q)⟩⟩

end Takesaki


/-! ## The factor case of Proposition 8 -/

section FactorCase

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The commutant within `𝓑(𝒦)` is the ordinary commutant. -/
theorem relComm_eq_vnComm (S : StarSubalgebra ℂ (K →L[ℂ] K)) : relComm S = vnComm S := rfl

/-- The factor case of the note's **Proposition 8**, `⇒`: a factor
`ℛ ⊆ 𝓑(𝒦)` that splits off its commutant is a type I factor.  The
extension `μ : ℛ ⊗ ℛ' → 𝓑(𝒦)` is injective because its domain is a factor
(`isFactor_vnt`; the kernel of an nmiu-map is cut out by a central
projection, **69IV**), and surjective because its range is a von Neumann
subalgebra (**69IVb**) containing `ℛ` and `ℛ'`, whose commutant therefore
lies in `ℛ' ∩ ℛ'' = ℂ` (**88VI**).  So `ℛ ⊗ ℛ' ≅ 𝓑(𝒦)`, and
`exists_bh_of_vnt_bh` applies. -/
theorem exists_bh_of_factor_splits (F : StarSubalgebra ℂ (K →L[ℂ] K))
    (hF : IsVNSubalgebra _ F) (hfac : IsFactor (SubVN F hF)) (hs : SplitsOffCommutant F hF) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H),
      Nonempty (SubVN F hF ≃⋆ₐ[ℂ] (H →L[ℂ] H)) := by
  by_cases hK : Nontrivial K
  swap
  · rw [not_nontrivial_iff_subsingleton] at hK
    have : Subsingleton (K →L[ℂ] K) :=
      ⟨fun a b => ContinuousLinearMap.ext fun x => Subsingleton.elim _ _⟩
    have : Subsingleton (SubVN F hF) :=
      ⟨fun a b => Theses.A.Proc.VNSub.val_injective (Subsingleton.elim _ _)⟩
    exact ⟨K, inferInstance, inferInstance, inferInstance, ⟨starAlgEquivOfSubsingleton⟩⟩
  obtain ⟨μ, hμ⟩ := hs
  have hFn : Nontrivial (SubVN F hF) :=
    ⟨⟨1, 0, fun h => one_ne_zero (congrArg Theses.A.Proc.VNSub.val h)⟩⟩
  have hCn : Nontrivial (CommVN F) :=
    ⟨⟨1, 0, fun h => one_ne_zero (congrArg Theses.A.Proc.VNSub.val h)⟩⟩
  have hcomm_eq : vnComm (relComm F) = F := vnComm_vnComm F hF
  -- the centre of `ℛ` is `ℂ`
  have hscalar : ∀ x : K →L[ℂ] K, x ∈ F → x ∈ relComm F → ∃ c : ℂ, x = algebraMap ℂ _ c := by
    intro x hxF hxC
    obtain ⟨c, hc⟩ := hfac ⟨x, hxF⟩ fun b =>
      Theses.A.Proc.VNSub.val_injective (mem_relComm.mp hxC b.val b.property).symm
    exact ⟨c, by rw [← vnsub_algebraMap_val (hS := hF), ← hc]⟩
  -- so is the centre of `ℛ'`, as `ℛ'' = ℛ`
  have hfacC : IsFactor (CommVN F) := by
    intro z hz
    have hz1 : z.val ∈ vnComm (relComm F) := mem_vnComm.mpr fun t ht =>
      (congrArg Theses.A.Proc.VNSub.val (hz ⟨t, ht⟩)).symm
    rw [hcomm_eq] at hz1
    obtain ⟨c, hc⟩ := hscalar z.val hz1 z.property
    exact ⟨c, Theses.A.Proc.VNSub.val_injective (by rw [hc, vnsub_algebraMap_val])⟩
  have hTfac := isFactor_vnt hfac hfacC
  have hμ1 : μ 1 = 1 := map_one μ.toStarAlgHom
  -- `μ` is injective
  have hinj : Function.Injective μ := nmiu_injective_of_isFactor μ hTfac
  -- `μ` is surjective
  have hone : ((1 : SubVN F hF) ⊗ᵥ (1 : CommVN F)) = 1 :=
    (vnTensor (SubVN F hF) (CommVN F)).isTensorProduct.miu.1
  have hsurj : Function.Surjective μ := by
    intro y
    have hFM : ∀ a ∈ F, a ∈ rangeSub μ := fun a ha =>
      ⟨⟨a, ha⟩ ⊗ᵥ (1 : CommVN F), by
        change μ (_ ⊗ᵥ _) = a; rw [hμ]; exact mul_one _⟩
    have hCM : ∀ t ∈ relComm F, t ∈ rangeSub μ := fun t ht =>
      ⟨(1 : SubVN F hF) ⊗ᵥ (⟨t, ht⟩ : CommVN F), by
        change μ (_ ⊗ᵥ _) = t; rw [hμ]; exact one_mul _⟩
    have hy : y ∈ vnComm (vnComm (rangeSub μ)) := mem_vnComm.mpr fun x hx => by
      have hxC : x ∈ relComm F := mem_relComm.mpr fun a ha => mem_vnComm.mp hx a (hFM a ha)
      have hxF : x ∈ F := by
        rw [← hcomm_eq]
        exact mem_vnComm.mpr fun t ht => mem_vnComm.mp hx t (hCM t ht)
      obtain ⟨c, hc⟩ := hscalar x hxF hxC
      rw [hc]
      exact Algebra.commutes c y
    rw [vnComm_vnComm _ (nmiu_image μ)] at hy
    obtain ⟨w, hw⟩ := hy
    exact ⟨w, hw⟩
  obtain ⟨H, i1, i2, i3, ⟨e⟩⟩ :=
    exists_bh_of_vnt_bh (StarAlgEquiv.ofBijective μ.toStarAlgHom ⟨hinj, hsurj⟩)
  exact ⟨H, i1, i2, i3, ⟨e⟩⟩

end FactorCase

/-! ## Transport along ∗-isomorphisms -/

section Transport

variable {P P' : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  [VonNeumannAlgebra P] [CStarAlgebra P'] [PartialOrder P'] [StarOrderedRing P']
  [VonNeumannAlgebra P']

/-- The image of `ℛ ⊆ 𝒫` under a ∗-isomorphism `Θ : 𝒫 ≅ 𝒫'`, as the range of
the nmiu-map `Θ ∘ val`. -/
def transportMap (Θ : P ≃⋆ₐ[ℂ] P') (R : StarSubalgebra ℂ P) (hR : IsVNSubalgebra P R) :
    NMIUMap (SubVN R hR) P' :=
  nmiuComp (nmiuOfBijective Θ.toStarAlgHom Θ.bijective) Theses.A.Proc.VNSub.valNMIU

omit [VonNeumannAlgebra P'] in
theorem transportMap_apply (Θ : P ≃⋆ₐ[ℂ] P') (R : StarSubalgebra ℂ P)
    (hR : IsVNSubalgebra P R) (x : SubVN R hR) : transportMap Θ R hR x = Θ x.val := rfl

/-- Splitting off the commutant survives ∗-isomorphisms of the ambient
algebra (via Lemma 9 for `Θ ∘ val`). -/
theorem splitsOffCommutant_transport (Θ : P ≃⋆ₐ[ℂ] P') {R : StarSubalgebra ℂ P}
    {hR : IsVNSubalgebra P R} (hs : SplitsOffCommutant R hR) :
    SplitsOffCommutant (rangeSub (transportMap Θ R hR)) (nmiu_image (transportMap Θ R hR)) := by
  obtain ⟨μ, hμ⟩ := hs
  rw [splitsOffCommutant_range_iff]
  set ρ := transportMap Θ R hR
  set Θn := nmiuOfBijective Θ.toStarAlgHom Θ.bijective
  set Θi := nmiuOfBijective Θ.symm.toStarAlgHom Θ.symm.bijective
  have hmem : ∀ t : PaschkeE ρ, Θi (Theses.A.Proc.VNSub.valNMIU t) ∈ relComm R := by
    intro t
    rw [mem_relComm]
    intro a ha
    have hc := mem_paschkeComm.mp t.property ⟨a, ha⟩
    rw [transportMap_apply] at hc
    apply Θ.injective
    change Θ (a * Θ.symm t.val) = Θ (Θ.symm t.val * a)
    rw [map_mul, map_mul, StarAlgEquiv.apply_symm_apply]
    exact hc
  set β := nmiuCorestrict (nmiuComp Θi Theses.A.Proc.VNSub.valNMIU) (relComm R)
    (isVNSubalgebra_relComm R) hmem
  refine ⟨nmiuComp Θn (nmiuComp μ (tmapM (nmiuId _) β)), fun x t => ?_⟩
  rw [nmiuComp_apply, nmiuComp_apply, tmapM_apply, nmiuId_apply, hμ, transportMap_apply]
  change Θ (x.val * Θ.symm t.val) = Θ x.val * t.val
  rw [map_mul, StarAlgEquiv.apply_symm_apply]

/-- `ℛ` is ∗-isomorphic to its image under `Θ`. -/
def transportEquiv (Θ : P ≃⋆ₐ[ℂ] P') (R : StarSubalgebra ℂ P) (hR : IsVNSubalgebra P R) :
    SubVN R hR ≃⋆ₐ[ℂ]
      SubVN (rangeSub (transportMap Θ R hR)) (nmiu_image (transportMap Θ R hR)) :=
  StarAlgEquiv.ofBijective
    (nmiuCorestrict (transportMap Θ R hR) (rangeSub (transportMap Θ R hR))
      (nmiu_image (transportMap Θ R hR)) fun x => ⟨x, rfl⟩).toStarAlgHom
    (nmiuCorestrict_bijective _ _ _ _
      (fun _ _ hxy => Theses.A.Proc.VNSub.val_injective (Θ.injective hxy))
      (fun _ ⟨x, hx⟩ => ⟨x, hx⟩))

end Transport

/-! ## Minimal central corners are factors -/

section MinCentral

variable {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  [VonNeumannAlgebra P] {R : StarSubalgebra ℂ P} {hR : IsVNSubalgebra P R}

/-- For the image `c = g(δᵢ)` of a minimal projection of `ℓ^∞(I) ≅ 𝒵(ℛ)`,
the corner `cℛ` is a factor: a central element of `cℛ` is central in `ℛ`
and absorbed by `c`, hence a multiple of `c`. -/
theorem isFactor_cornerSub {I : Type u} (f : NMIUMap (CentreVN R hR) (linf I))
    (hf : Function.Bijective f) (i : I)
    [Fact (IsStarProjection (nmiuSymm f hf (lpKappa i (1 : ℂ))).val)] :
    IsFactor (SubVN (cornerSub R (nmiuSymm f hf (lpKappa i (1 : ℂ))).val
      (nmiuSymm f hf (lpKappa i (1 : ℂ))).property.1)
      (isVNSubalgebra_cornerSub hR _ (nmiuSymm f hf (lpKappa i (1 : ℂ))).property.1)) := by
  classical
  set g := nmiuSymm f hf
  set p := g (lpKappa i (1 : ℂ))
  set c := p.val
  have hcp : IsStarProjection c := Fact.out
  have hcR : c ∈ R := p.property.1
  have hcC : c ∈ relComm R := p.property.2
  have hcc : ∀ a ∈ R, c * a = a * c := fun a ha => (mem_relComm.mp hcC a ha).symm
  intro z hz
  set w := z.val.val
  have hwR : w ∈ R := z.property
  have hwc : c * w = w := Corner.mul_left z.val
  have hwc' : w * c = w := Corner.mul_right z.val
  -- `w` is central in `ℛ`
  have hwC : w ∈ relComm R := by
    rw [mem_relComm]
    intro a ha
    have hmem : (⟨c * a * c, by
        rw [← mul_assoc, ← mul_assoc, hcp.isIdempotentElem.eq, mul_assoc,
          hcp.isIdempotentElem.eq]⟩ : Corner P c) ∈ cornerSub R c hcR :=
      mem_cornerSub.mpr (mul_mem (mul_mem hcR ha) hcR)
    have hz' := congrArg (fun y => y.val.val) (hz ⟨_, hmem⟩)
    change w * (c * a * c) = c * a * c * w at hz'
    have e1 : w * (c * a * c) = w * a := by
      rw [← mul_assoc, ← mul_assoc, hwc', mul_assoc, ← hcc a ha, ← mul_assoc, hwc']
    have e2 : c * a * c * w = a * w := by
      rw [mul_assoc, hwc, hcc a ha, mul_assoc, hwc]
    rw [e1, e2] at hz'
    exact hz'.symm
  set wz : CentreVN R hR := ⟨w, hwR, hwC⟩
  have hwp : wz * p = wz := Theses.A.Proc.VNSub.val_injective hwc'
  -- in `ℓ^∞(I)`, `f(w) δᵢ = f(w)` forces `f(w) = f(w)ᵢ δᵢ`
  set l := ((f wz : linf I) : ∀ _ : I, ℂ) i
  have hfp : f p = lpKappa i (1 : ℂ) := nmiuSymm_apply_apply' f hf _
  have hfw : f wz = l • lpKappa i (1 : ℂ) := by
    have h1 : f wz * lpKappa i (1 : ℂ) = f wz := by
      rw [← hfp, ← show f (wz * p) = f wz * f p from map_mul f.toStarAlgHom wz p]
      exact congrArg f hwp
    refine lp.ext (funext fun j => ?_)
    have h2 := congrArg (fun v : linf I => (v : ∀ _ : I, ℂ) j) h1
    simp only [lp.infty_coeFn_mul, Pi.mul_apply] at h2
    rw [lp.coeFn_smul, Pi.smul_apply]
    by_cases hj : j = i
    · subst hj
      rw [lpKappa_apply_self, smul_eq_mul, mul_one]
    · rw [lpKappa_apply_ne _ _ hj, smul_zero]
      rw [lpKappa_apply_ne _ _ hj, mul_zero] at h2
      exact h2.symm
  have hwz : wz = l • p := by
    apply hf.1
    rw [hfw, show f (l • p) = l • f p from map_smul f.toStarAlgHom l p, hfp]
  refine ⟨l, Theses.A.Proc.VNSub.val_injective (Corner.val_injective ?_)⟩
  rw [vnsub_algebraMap_val, Algebra.algebraMap_eq_smul_one, Corner.val_smul, Corner.val_one]
  exact congrArg Theses.A.Proc.VNSub.val hwz

end MinCentral

/-! ## Proposition 8 -/

section CornerCompress

variable {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  [VonNeumannAlgebra P] {R : StarSubalgebra ℂ P} {hR : IsVNSubalgebra P R}

/-- The compression `a ↦ ca : ℛ → cℛ` for a central projection `c` of `ℛ`, as
a ∗-homomorphism. -/
def cornerCompress (c : P) [Fact (IsStarProjection c)] (hc : c ∈ centreSub R) :
    SubVN R hR →⋆ₐ[ℂ] SubVN (cornerSub R c hc.1) (isVNSubalgebra_cornerSub hR c hc.1) :=
  have hcp : IsStarProjection c := Fact.out
  have hcc : ∀ a ∈ R, c * a = a * c := fun a ha => (mem_relComm.mp hc.2 a ha).symm
  have hprop : ∀ x : SubVN R hR, c * (c * x.val) * c = c * x.val := fun x => by
    rw [← mul_assoc, hcp.isIdempotentElem.eq, mul_assoc, ← hcc _ x.property, ← mul_assoc,
      hcp.isIdempotentElem.eq]
  { toFun := fun x => ⟨⟨c * x.val, hprop x⟩, mem_cornerSub.mpr (mul_mem hc.1 x.property)⟩
    map_one' := Theses.A.Proc.VNSub.val_injective (Corner.val_injective (mul_one c))
    map_mul' := fun x y => Theses.A.Proc.VNSub.val_injective (Corner.val_injective (by
      change c * (x.val * y.val) = c * x.val * (c * y.val)
      calc c * (x.val * y.val) = (c * c) * x.val * y.val := by
            rw [hcp.isIdempotentElem.eq, mul_assoc]
        _ = c * (c * x.val) * y.val := by noncomm_ring
        _ = c * (x.val * c) * y.val := by rw [hcc _ x.property]
        _ = c * x.val * (c * y.val) := by noncomm_ring))
    map_zero' := Theses.A.Proc.VNSub.val_injective (Corner.val_injective (mul_zero c))
    map_add' := fun x y => Theses.A.Proc.VNSub.val_injective (Corner.val_injective (mul_add c _ _))
    commutes' := fun r => Theses.A.Proc.VNSub.val_injective (Corner.val_injective (by
      change c * (algebraMap ℂ (SubVN R hR) r).val = ((algebraMap ℂ _ r : SubVN
        (cornerSub R c hc.1) (isVNSubalgebra_cornerSub hR c hc.1)).val).val
      rw [vnsub_algebraMap_val, vnsub_algebraMap_val, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, Corner.val_smul, Corner.val_one, mul_smul_comm, mul_one]))
    map_star' := fun x => Theses.A.Proc.VNSub.val_injective (Corner.val_injective (by
      change c * star x.val = star (c * x.val)
      rw [star_mul, hcp.isSelfAdjoint.star_eq, hcc _ (star_mem x.property)])) }

theorem cornerCompress_val (c : P) [Fact (IsStarProjection c)] (hc : c ∈ centreSub R)
    (x : SubVN R hR) : (cornerCompress (hR := hR) c hc x).val.val = c * x.val := rfl

end CornerCompress


section LpFamily

/-- A norm-decreasing family of ∗-homomorphisms `A → Bᵢ` into the direct sum
`⊕ᵢ Bᵢ = ℓ^∞`. -/
def lpOfFamily {A : Type*} [CStarAlgebra A] {ι : Type*} {B : ι → Type*}
    [∀ i, CStarAlgebra (B i)] [∀ i, Nontrivial (B i)] (φ : ∀ i, A →⋆ₐ[ℂ] B i)
    (hφ : ∀ x i, ‖φ i x‖ ≤ ‖x‖) : A →⋆ₐ[ℂ] lp B ∞ where
  toFun x := ⟨fun i => φ i x, memℓp_infty ⟨‖x‖, by rintro _ ⟨i, rfl⟩; exact hφ x i⟩⟩
  map_one' := lp.ext (funext fun i => by
    rw [lp.infty_coeFn_one, Pi.one_apply]; exact map_one (φ i))
  map_mul' x y := lp.ext (funext fun i => by
    rw [lp.infty_coeFn_mul, Pi.mul_apply]; exact map_mul (φ i) x y)
  map_zero' := lp.ext (funext fun i => by
    rw [lp.coeFn_zero, Pi.zero_apply]; exact map_zero (φ i))
  map_add' x y := lp.ext (funext fun i => by
    rw [lp.coeFn_add, Pi.add_apply]; exact map_add (φ i) x y)
  commutes' r := lp.ext (funext fun i => by
    rw [Algebra.algebraMap_eq_smul_one (A := lp B ∞), lp.coeFn_smul, lp.infty_coeFn_one,
      Pi.smul_apply, Pi.one_apply, ← Algebra.algebraMap_eq_smul_one]
    exact AlgHomClass.commutes (φ i) r)
  map_star' x := lp.ext (funext fun i => by
    rw [lp.coeFn_star, Pi.star_apply]; exact map_star (φ i) x)

theorem lpOfFamily_apply {A : Type*} [CStarAlgebra A] {ι : Type*} {B : ι → Type*}
    [∀ i, CStarAlgebra (B i)] [∀ i, Nontrivial (B i)] (φ : ∀ i, A →⋆ₐ[ℂ] B i)
    (hφ : ∀ x i, ‖φ i x‖ ≤ ‖x‖) (x : A) (i : ι) :
    ((lpOfFamily φ hφ x : lp B ∞) : ∀ i, B i) i = φ i x := rfl

end LpFamily

section Prop7

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- For the minimal central projections `c = g(δᵢ)` of a subalgebra
`ℛ ⊆ 𝓑(𝒦)` that splits off its commutant, the corner `cℛ` is a type I
factor: it splits off its commutant in `c𝓑(𝒦)c ≅ 𝓑(c𝒦)` (Proposition 7,
`cornerBHEquiv`) and is a factor (`isFactor_cornerSub`), so the factor case
applies. -/
theorem exists_corner_bh {R : StarSubalgebra ℂ (K →L[ℂ] K)} {hR : IsVNSubalgebra _ R}
    (hs : SplitsOffCommutant R hR) {I : Type u}
    (f : NMIUMap (CentreVN R hR) (linf I)) (hf : Function.Bijective f) (i : I)
    [Fact (IsStarProjection (nmiuSymm f hf (lpKappa i (1 : ℂ))).val)] :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H),
      Nonempty (SubVN (cornerSub R (nmiuSymm f hf (lpKappa i (1 : ℂ))).val
        (nmiuSymm f hf (lpKappa i (1 : ℂ))).property.1)
        (isVNSubalgebra_cornerSub hR _ (nmiuSymm f hf (lpKappa i (1 : ℂ))).property.1)
        ≃⋆ₐ[ℂ] (H →L[ℂ] H)) := by
  set c := (nmiuSymm f hf (lpKappa i (1 : ℂ))).val
  have hc : c ∈ centreSub R := (nmiuSymm f hf (lpKappa i (1 : ℂ))).property
  have hsc := splitsOffCommutant_corner hs c hc
  set Θ := cornerBHEquiv (K := K) c
  have hsT := splitsOffCommutant_transport Θ hsc
  have hfac := isFactor_cornerSub f hf i
  have hfacT := isFactor_of_starAlgEquiv (transportEquiv Θ _ _) hfac
  obtain ⟨H, i1, i2, i3, ⟨e⟩⟩ := exists_bh_of_factor_splits _ _ hfacT hsT
  exact ⟨H, i1, i2, i3, ⟨(transportEquiv Θ _ _).trans e⟩⟩

/-- The note's **Proposition 8**, `⇒`: a von Neumann subalgebra `ℛ` of
`𝓑(𝒦)` that splits off its commutant is a direct sum of type I factors.
Its centre is `≅ ℓ^∞(I)` and every minimal central corner `cᵢℛ` is a type I
factor (`exists_corner_bh`); **67IV** (`central_projections_sums_2`)
assembles `ℛ ≅ ⊕ᵢ cᵢℛ ≅ ⊕ᵢ 𝓑(ℋᵢ)`. -/
theorem atomicTypeI_of_splitsOffCommutant_bh {R : StarSubalgebra ℂ (K →L[ℂ] K)}
    {hR : IsVNSubalgebra _ R} (hs : SplitsOffCommutant R hR) : AtomicTypeI (SubVN R hR) := by
  classical
  obtain ⟨I, f, hf⟩ := centre_linf_of_splitsOffCommutant hs
  set g := nmiuSymm f hf
  set c : I → (K →L[ℂ] K) := fun i => (g (lpKappa i (1 : ℂ))).val
  have hmin : ∀ i, IsMinCentralProj R (c i) :=
    fun i => isMinCentralProj_of_isMinProj (isMinProj_symm_linf f hf i)
  have hcp : ∀ i, IsStarProjection (c i) := fun i => (hmin i).2.1
  have hfact : ∀ i, Fact (IsStarProjection (c i)) := fun i => ⟨hcp i⟩
  have hcc : ∀ i, ∀ a ∈ R, c i * a = a * c i :=
    fun i a ha => (mem_relComm.mp (hmin i).1.2 a ha).symm
  have hcorner := fun i => exists_corner_bh hs f hf i
  choose H i1 i2 i3 he using hcorner
  set E := fun i => (he i).some
  set π := fun i => cornerCompress (hR := hR) (c i) (hmin i).1
  -- the `Hᵢ` are non-zero
  have hnt : ∀ i, Nontrivial (H i) := by
    intro i
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : Subsingleton (H i →L[ℂ] H i) :=
      ⟨fun a b => ContinuousLinearMap.ext fun x => Subsingleton.elim _ _⟩
    have h10 : (E i).symm 1 = (E i).symm 0 := congrArg (E i).symm (Subsingleton.elim _ _)
    rw [map_one, map_zero] at h10
    exact (hmin i).2.2.1 (congrArg (fun y => y.val.val) h10)
  -- the hypotheses of **67IV** for `c' i = cᵢ ∈ ℛ`
  set c' : I → SubVN R hR := fun i => ⟨c i, (hmin i).1.1⟩
  have hc'val : ∀ i, (c' i).val = c i := fun i => rfl
  have hc'pc : ∀ i, IsStarProjection (c' i) ∧ IsCentral (SubVN R hR) (c' i) := fun i =>
    ⟨⟨Theses.A.Proc.VNSub.val_injective (hcp i).isIdempotentElem.eq,
      Theses.A.Proc.VNSub.val_injective (hcp i).isSelfAdjoint.star_eq⟩,
      fun b => Theses.A.Proc.VNSub.val_injective (hcc i _ b.property)⟩
  have hδ : ∀ i j, i ≠ j → lpKappa i (1 : ℂ) * lpKappa j (1 : ℂ) = (0 : linf I) := by
    intro i j hij
    refine lp.ext (funext fun k => ?_)
    rw [lp.infty_coeFn_mul, Pi.mul_apply, lp.coeFn_zero, Pi.zero_apply]
    by_cases hk : k = i
    · subst hk; rw [lpKappa_apply_ne _ _ hij, mul_zero]
    · rw [lpKappa_apply_ne _ _ hk, zero_mul]
  have horth : Pairwise fun i j => c' i * c' j = 0 := by
    intro i j hij
    refine Theses.A.Proc.VNSub.val_injective ?_
    change (g (lpKappa i 1)).val * (g (lpKappa j 1)).val = 0
    rw [← Theses.A.Proc.VNSub.val_mul, ← show g (lpKappa i 1 * lpKappa j 1)
      = g (lpKappa i 1) * g (lpKappa j 1) from map_mul g.toStarAlgHom _ _, hδ i j hij,
      show g 0 = 0 from map_zero g.toStarAlgHom]
    rfl
  -- `∑ᵢ cᵢ = 1` ultraweakly, whence `⋁ᵢ cᵢ = 1`
  set h := nmiuComp (Theses.A.Proc.VNSub.valNMIU (A := K →L[ℂ] K) (S := centreSub R)
    (hS := isVNSubalgebra_centreSub hR)) g
  have h1i : ∀ i, ((1 : linf I) : ∀ _ : I, ℂ) i = 1 := fun i => by
    rw [lp.infty_coeFn_one, Pi.one_apply]
  have hsum : ∀ F : Finset I, ∑ i ∈ F, c i = h (∑ i ∈ F, lpKappa i (1 : ℂ)) := fun F =>
    (map_sum h.toStarAlgHom (fun i => lpKappa (𝒜 := fun _ : I => ℂ) i (1 : ℂ)) F).symm
  have hsup : projSup (Set.range c') = 1 := by
    refine projSup_eq (by rintro _ ⟨i, rfl⟩; exact (hc'pc i).1) (IsStarProjection.one _)
      (by rintro _ ⟨i, rfl⟩; exact (hc'pc i).1.le_one) (fun q hq hub => ?_)
    suffices hq1 : q.val = 1 by
      rw [show q = 1 from Theses.A.Proc.VNSub.val_injective hq1]
    have hqp : IsStarProjection q.val :=
      ⟨congrArg Theses.A.Proc.VNSub.val hq.isIdempotentElem.eq,
        congrArg Theses.A.Proc.VNSub.val hq.isSelfAdjoint.star_eq⟩
    have hcq : ∀ i, c i * q.val = c i := fun i =>
      (IsStarProjection.le_iff_mul_eq_left (hcp i) hqp).mp (hub (c' i) (Set.mem_range_self i))
    let _ : TopologicalSpace (K →L[ℂ] K) := ultraweak _
    let _ : TopologicalSpace (linf I) := ultraweak _
    have hT := uwTendsto_lpRestrict (1 : linf I)
    have hc1 : @Continuous (linf I) (K →L[ℂ] K) (ultraweak _) (ultraweak _) fun z => h z :=
      nmiu_uwContinuous h
    have hc2 : @Continuous (linf I) (K →L[ℂ] K) (ultraweak _) (ultraweak _)
        fun z => h z * q.val :=
      @Continuous.comp _ _ _ (ultraweak _) (ultraweak _) (ultraweak _) _ _
        (mult_uws_cont _).2.1 (nmiu_uwContinuous h)
    have l1 := (hc1.tendsto 1).comp hT
    have l2 := (hc2.tendsto 1).comp hT
    rw [show h 1 = 1 from map_one h.toStarAlgHom] at l1 l2
    rw [one_mul] at l2
    refine uwTendsto_unique l2 (l1.congr fun F => ?_)
    simp only [Function.comp_apply, h1i]
    rw [← hsum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (hcq i).symm
  -- the ∗-homomorphism `ℛ → ⊕ᵢ 𝓑(ℋᵢ)`
  have hbd : ∀ (x : SubVN R hR) (i : I), ‖E i (π i x)‖ ≤ ‖x‖ := by
    intro x i
    rw [StarAlgEquiv.norm_map]
    change ‖c i * x.val‖ ≤ ‖x.val‖
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _)
      (IsStarProjection.norm_le _ (hcp i)))
  set Ψ := lpOfFamily (B := fun i => H i →L[ℂ] H i)
    (fun i => (E i).toStarAlgHom.comp (π i)) hbd
  have hΨ : ∀ x i, ((Ψ x : lp (fun i => H i →L[ℂ] H i) ∞) : ∀ i, H i →L[ℂ] H i) i
      = E i (π i x) := fun _ _ => rfl
  have hinj : Function.Injective Ψ := by
    intro x y hxy
    have hxy' : ∀ i, c' i * x = c' i * y := by
      intro i
      have := congrArg (fun v : lp (fun i => H i →L[ℂ] H i) ∞ =>
        (v : ∀ i, H i →L[ℂ] H i) i) hxy
      simp only [hΨ] at this
      have h2 := congrArg (fun y => y.val.val) ((E i).injective this)
      exact Theses.A.Proc.VNSub.val_injective h2
    obtain ⟨a, -, ha⟩ := central_projections_sums_2 c' hc'pc horth hsup (fun i => c' i * x)
      (fun i => by rw [← mul_assoc, (hc'pc i).1.isIdempotentElem.eq])
      ⟨‖x‖, by
        rintro _ ⟨i, rfl⟩
        exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _)
          (IsStarProjection.norm_le _ (hc'pc i).1))⟩
    exact (ha x fun i => rfl).trans (ha y fun i => (hxy' i).symm).symm
  have hsurj : Function.Surjective Ψ := by
    intro v
    set b := fun i => (E i).symm ((v : ∀ i, H i →L[ℂ] H i) i)
    set b' : I → SubVN R hR := fun i => ⟨(b i).val.val, mem_cornerSub.mp (b i).property⟩
    obtain ⟨a, ha, -⟩ := central_projections_sums_2 c' hc'pc horth hsup b'
      (fun i => Theses.A.Proc.VNSub.val_injective (Corner.mul_left (b i).val))
      ⟨‖v‖, by
        rintro _ ⟨i, rfl⟩
        change ‖(b i).val.val‖ ≤ ‖v‖
        rw [show ‖(b i).val.val‖ = ‖b i‖ from rfl, StarAlgEquiv.norm_map]
        exact lp.norm_apply_le_norm ENNReal.top_ne_zero v i⟩
    refine ⟨a, lp.ext (funext fun i => ?_)⟩
    rw [hΨ]
    have hπ : π i a = b i :=
      Theses.A.Proc.VNSub.val_injective (Corner.val_injective (congrArg
        Theses.A.Proc.VNSub.val (ha i)))
    rw [hπ, StarAlgEquiv.apply_symm_apply]
  exact ⟨AtomicTypeIRep.mk I H (StarAlgEquiv.ofBijective Ψ ⟨hinj, hsurj⟩)⟩

/-- The note's **Proposition 8**: a von Neumann subalgebra `ℛ` of `𝓑(𝒦)`
splits off its commutant in `𝓑(𝒦)` iff it is a direct sum of type I
factors.  `⇐` is Proposition 7's "in particular"; `⇒` is
`atomicTypeI_of_splitsOffCommutant_bh`. -/
theorem splitsOffCommutant_bh_iff {R : StarSubalgebra ℂ (K →L[ℂ] K)}
    {hR : IsVNSubalgebra _ R} : SplitsOffCommutant R hR ↔ AtomicTypeI (SubVN R hR) :=
  ⟨atomicTypeI_of_splitsOffCommutant_bh, splitsOffCommutant_of_atomicTypeI R hR⟩

end Prop7

/-! ## Corollary 14 -/

section Cor13

variable {X : Type u} [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [VonNeumannAlgebra X]
  {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The note's **Corollary 14**: for an ncp-map `φ : 𝒳 → 𝓑(ℋ)` with minimal
normal Stinespring dilation `(𝒦, ϱ, V)` (**139I**), `φ` has a Wittrock
dilation iff `ϱ(𝒳)` is a direct sum of type I factors — **140III**
(`stinespring_is_paschke`), Theorem 10 and Proposition 8. -/
theorem wittrock_iff_atomicTypeI_stinespring (φ : NCPMap X (H →L[ℂ] H))
    (D : StinespringDilation ⇑φ) (hmin : D.Minimal) :
    (∃ (E : Type u) (_ : CStarAlgebra E) (_ : PartialOrder E) (_ : StarOrderedRing E)
      (_ : VonNeumannAlgebra E) (h : NCPMap (VNT X E) (H →L[ℂ] H)),
        IsWittrockDilationOf ⇑φ E h) ↔
      AtomicTypeI (SubVN (rangeSub D.ρ) (nmiu_image D.ρ)) := by
  obtain ⟨vnK, hA, -, hD⟩ := stinespring_is_paschke φ D hmin
  exact (wittrock_iff_splitsOffCommutant φ D.ρ hA hD).trans splitsOffCommutant_bh_iff

/-- Corollary 14, `⇐`, on its own: Theorem 10 with Proposition 7's "in
particular", without Proposition 8, `⇒`. -/
theorem exists_wittrock_of_atomicTypeI_stinespring (φ : NCPMap X (H →L[ℂ] H))
    (D : StinespringDilation ⇑φ) (hmin : D.Minimal)
    (hI : AtomicTypeI (SubVN (rangeSub D.ρ) (nmiu_image D.ρ))) :
    ∃ (E : Type u) (_ : CStarAlgebra E) (_ : PartialOrder E) (_ : StarOrderedRing E)
      (_ : VonNeumannAlgebra E) (h : NCPMap (VNT X E) (H →L[ℂ] H)),
        IsWittrockDilationOf ⇑φ E h := by
  obtain ⟨vnK, hA, -, hD⟩ := stinespring_is_paschke φ D hmin
  exact (wittrock_iff_splitsOffCommutant φ D.ρ hA hD).mpr
    (splitsOffCommutant_of_atomicTypeI _ _ hI)

/-- The note's **Corollary 14**, "in particular": no non-zero ncp-map
`𝒳 → 𝓑(ℋ)` on a factor `𝒳` that is not of type I has a Wittrock dilation.
Here the factor case of Proposition 8 is applied to `ϱ(𝒳) ≅ 𝒳` directly
(`ϱ` is injective, `𝒳` being a factor). -/
theorem not_wittrock_of_factor_not_typeI (φ : NCPMap X (H →L[ℂ] H)) (hφ : ∃ x, φ x ≠ 0)
    (hX : IsFactor X)
    (hnI : ¬ ∃ (H' : Type u) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H')
      (_ : CompleteSpace H'), Nonempty (X ≃⋆ₐ[ℂ] (H' →L[ℂ] H'))) :
    ¬ ∃ (E : Type u) (_ : CStarAlgebra E) (_ : PartialOrder E) (_ : StarOrderedRing E)
      (_ : VonNeumannAlgebra E) (h : NCPMap (VNT X E) (H →L[ℂ] H)),
        IsWittrockDilationOf ⇑φ E h := by
  intro hW
  obtain ⟨D, hmin⟩ := exists_minimal_stinespringDilation φ
  obtain ⟨vnK, hA, -, hD⟩ := stinespring_is_paschke φ D hmin
  have hs := (wittrock_iff_splitsOffCommutant φ D.ρ hA hD).mp hW
  have hKn : Nontrivial (D.K →L[ℂ] D.K) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    obtain ⟨x, hx⟩ := hφ
    apply hx
    rw [← hD.1 x, show D.ρ x = 0 from Subsingleton.elim _ _]
    exact wncp_zero hA
  have hinj : Function.Injective D.ρ := nmiu_injective_of_isFactor D.ρ hX
  set e := StarAlgEquiv.ofBijective
    (nmiuCorestrict D.ρ (rangeSub D.ρ) (nmiu_image D.ρ) fun x => ⟨x, rfl⟩).toStarAlgHom
    (nmiuCorestrict_bijective _ _ _ _ hinj fun _ ⟨x, hx⟩ => ⟨x, hx⟩)
  have hfac := isFactor_of_starAlgEquiv e hX
  obtain ⟨H', i1, i2, i3, ⟨e'⟩⟩ := exists_bh_of_factor_splits _ _ hfac hs
  exact hnI ⟨H', i1, i2, i3, ⟨e.trans e'⟩⟩

end Cor13

end Theses.B.Dils
