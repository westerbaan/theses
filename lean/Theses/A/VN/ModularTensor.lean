/-
**The tensor factorisation of the modular data**, in the bounded-operator formulation of

  M. A. Rieffel and A. van Daele, *A bounded operator approach to
  Tomita–Takesaki theory*, Pacific J. Math. **69** (1977) 187–221.

**This file has no thesis counterpart.**  It is the step described in
`docs/COMMUTATION-THEOREM.md` §4 as "the step that decides it": for von Neumann
algebras `M ⊆ B(ℋ)` and `N ⊆ B(𝒦)` with cyclic separating vectors `ω`, `ω'` and
`ξ := ω ⊗ ω'`,

    J_ξ = J_ω ⊗ J_{ω'}    and    Δ_ξ^{1/2} = closure (Δ_ω^{1/2} ⊙ Δ_{ω'}^{1/2}).

Classically this needs the spectral theorem for unbounded operators and product
spectral measures.  Here everything is done with bounded operators.
-/
import Theses.A.VN.Tomita
import Theses.A.Proc.Tensor

open Complex ClosedSubmodule Theses.A.VN Theses.A.Proc
open scoped ComplexInnerProductSpace ComplexOrder Theses.A.Proc

namespace Theses.RvD

/-! ## Part 0: general facts about closed operators and modular pairs -/

section Helpers

variable {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

omit [CompleteSpace ℋ] in
/-- Being a core, in terms of the closure of the graph. -/
theorem hasCore_iff_closure_graph {D : ℋ →ₗ.[ℂ] ℋ} (hD : D.IsClosed) {S : Submodule ℂ ℋ}
    (hS : S ≤ D.domain) :
    D.HasCore S ↔
      closure ((D.domRestrict S).graph : Set (ℋ × ℋ)) = (D.graph : Set (ℋ × ℋ)) := by
  have hres_le : D.domRestrict S ≤ D := LinearPMap.domRestrict_le
  have hcl : (D.domRestrict S).IsClosable := hD.isClosable.leIsClosable hres_le
  constructor
  · rintro ⟨-, h⟩
    have := hcl.graph_closure_eq_closure_graph
    rw [h] at this
    rw [← Submodule.topologicalClosure_coe, this]
  · intro h
    refine ⟨hS, LinearPMap.eq_of_eq_graph ?_⟩
    rw [← hcl.graph_closure_eq_closure_graph]
    refine SetLike.ext' ?_
    rw [Submodule.topologicalClosure_coe]
    exact h

/-- A self-adjoint bounded operator with dense range is injective. -/
theorem injective_of_denseRange {a : ℋ →L[ℂ] ℋ} (hsa : IsSelfAdjoint a)
    (hd : Dense ((LinearMap.range (a : ℋ →ₗ[ℂ] ℋ) : Submodule ℂ ℋ) : Set ℋ)) :
    Function.Injective a := by
  have hbot : (LinearMap.range (a : ℋ →ₗ[ℂ] ℋ))ᗮ = ⊥ := by
    rw [← Submodule.topologicalClosure_eq_top_iff,
      ← Submodule.dense_iff_topologicalClosure_eq_top]
    exact hd
  have hzero : ∀ x : ℋ, a x = 0 → x = 0 := by
    intro x hx
    have hmem : x ∈ (LinearMap.range (a : ℋ →ₗ[ℂ] ℋ))ᗮ := by
      rw [Submodule.mem_orthogonal]
      rintro _ ⟨y, rfl⟩
      have : ⟪(a : ℋ →ₗ[ℂ] ℋ) y, x⟫ = ⟪y, a x⟫ :=
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa) y x
      rw [this, hx, inner_zero_right]
    rw [hbot] at hmem
    simpa using hmem
  intro u v huv
  have : a (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have := hzero _ this
  exact sub_eq_zero.1 this


/-- A bounded operator vanishing on a set with dense span is zero. -/
theorem clm_eq_zero_of_span_dense {S : Set ℋ}
    (hS : Dense ((Submodule.span ℂ S : Submodule ℂ ℋ) : Set ℋ)) {z : ℋ →L[ℂ] ℋ}
    (h : ∀ v ∈ S, z v = 0) : z = 0 := by
  refine clm_ext_of_dense hS ?_
  intro v hv
  show z v = (0 : ℋ →L[ℂ] ℋ) v
  simp only [zero_apply]
  refine Submodule.span_induction (p := fun w _ => z w = 0) (fun x hx => h x hx) ?_ ?_ ?_ hv
  · simp
  · intro u u' _ _ hu hu'; rw [map_add, hu, hu', add_zero]
  · intro c u _ hu; rw [map_smul, hu, smul_zero]

namespace IsModularPair

variable {a b : ℋ →L[ℂ] ℋ}

/-- The map `ζ ↦ (aζ, bζ)` is bounded below: `‖ζ‖ ≤ √2 ‖(aζ, bζ)‖`. -/
theorem norm_le_norm_prod (h : IsModularPair a b) (ζ : ℋ) :
    ‖ζ‖ ≤ Real.sqrt 2 * ‖((a ζ, b ζ) : ℋ × ℋ)‖ := by
  have hn := h.norm_sq_add_norm_sq ζ
  have hmax : ‖((a ζ, b ζ) : ℋ × ℋ)‖ = max ‖a ζ‖ ‖b ζ‖ := rfl
  have h1 : ‖a ζ‖ ≤ ‖((a ζ, b ζ) : ℋ × ℋ)‖ := by rw [hmax]; exact le_max_left _ _
  have h2 : ‖b ζ‖ ≤ ‖((a ζ, b ζ) : ℋ × ℋ)‖ := by rw [hmax]; exact le_max_right _ _
  have hnn : (0:ℝ) ≤ ‖((a ζ, b ζ) : ℋ × ℋ)‖ := norm_nonneg _
  have hA : ‖a ζ‖ ^ 2 ≤ ‖((a ζ, b ζ) : ℋ × ℋ)‖ ^ 2 := by
    nlinarith [norm_nonneg (a ζ)]
  have hB : ‖b ζ‖ ^ 2 ≤ ‖((a ζ, b ζ) : ℋ × ℋ)‖ ^ 2 := by
    nlinarith [norm_nonneg (b ζ)]
  have hz : ‖ζ‖ ^ 2 ≤ 2 * ‖((a ζ, b ζ) : ℋ × ℋ)‖ ^ 2 := by linarith
  have h1 : ‖ζ‖ = Real.sqrt (‖ζ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg ζ)).symm
  have h2 : Real.sqrt 2 * ‖((a ζ, b ζ) : ℋ × ℋ)‖
      = Real.sqrt (2 * ‖((a ζ, b ζ) : ℋ × ℋ)‖ ^ 2) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hnn]
  rw [h1, h2]
  exact Real.sqrt_le_sqrt hz

/-- **The key density transfer.**  If `S` is a core for `D_{a,b}`, then `a⁻¹(S)` is dense.
The graph of `D` is the image of `ℋ` under the bounded-below map `ζ ↦ (aζ, bζ)`, and the
graph of the restriction to `S` is the image of `a⁻¹(S)`; a core is exactly a dense image. -/
theorem dense_comap_of_hasCore (h : IsModularPair a b) {S : Submodule ℂ ℋ}
    (hS : h.D.HasCore S) :
    Dense ((S.comap (a : ℋ →ₗ[ℂ] ℋ) : Submodule ℂ ℋ) : Set ℋ) := by
  have hgr := (hasCore_iff_closure_graph h.isClosed hS.le_domain).1 hS
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_forall fun η => ?_
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  have hηg : ((a η, b η) : ℋ × ℋ) ∈ (h.D.graph : Set (ℋ × ℋ)) := by
    refine (LinearPMap.mem_graph_iff' _).2 ⟨⟨a η, h.mem_D_domain η⟩, ?_⟩
    exact Prod.ext rfl (h.D_apply η)
  rw [← hgr] at hηg
  have hs0 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨q, hq, hqd⟩ := Metric.mem_closure_iff.1 hηg (ε / Real.sqrt 2) (by positivity)
  obtain ⟨z, hz⟩ := (LinearPMap.mem_graph_iff' _).1 hq
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℋ, a ζ = (z : ℋ) := z.2.2
  have hqval : q = ((a ζ, b ζ) : ℋ × ℋ) := by
    rw [← hz]
    refine Prod.ext hζ.symm ?_
    show ((h.D.domRestrict S) z : ℋ) = b ζ
    rw [LinearPMap.domRestrict_apply (y := (⟨(z : ℋ), z.2.2⟩ : h.D.domain)) rfl]
    exact h.D_apply' _ ζ hζ
  refine ⟨ζ, ?_, ?_⟩
  · show ζ ∈ (S.comap (a : ℋ →ₗ[ℂ] ℋ) : Submodule ℂ ℋ)
    have : a ζ ∈ S := hζ ▸ z.2.1
    exact this
  · have hdd : dist η ζ ≤ Real.sqrt 2 * dist ((a η, b η) : ℋ × ℋ) q := by
      rw [dist_eq_norm, dist_eq_norm, hqval]
      have := h.norm_le_norm_prod (η - ζ)
      have he : ((a (η - ζ), b (η - ζ)) : ℋ × ℋ)
          = ((a η, b η) : ℋ × ℋ) - ((a ζ, b ζ) : ℋ × ℋ) := by
        simp [map_sub]
      rwa [he] at this
    calc dist η ζ ≤ Real.sqrt 2 * dist ((a η, b η) : ℋ × ℋ) q := hdd
      _ < Real.sqrt 2 * (ε / Real.sqrt 2) := mul_lt_mul_of_pos_left hqd hs0
      _ = ε := by field_simp

end IsModularPair

omit [CompleteSpace ℋ] in
/-- **Two closed operators with a common core, related by a bounded operator on that core.**
`Φ_V (x, y) = (x, V y)` carries the graph of `D₁` into the graph of `D₂`. -/
theorem graph_map_of_hasCore {D₁ D₂ : ℋ →ₗ.[ℂ] ℋ} (h₁ : D₁.IsClosed) (h₂ : D₂.IsClosed)
    {S : Submodule ℂ ℋ} (hS₁ : D₁.HasCore S) (hS₂ : S ≤ D₂.domain) {V : ℋ →L[ℂ] ℋ}
    (hag : ∀ (ζ : ℋ) (_hζS : ζ ∈ S) (h1 : ζ ∈ D₁.domain) (h2 : ζ ∈ D₂.domain),
      (D₂ ⟨ζ, h2⟩ : ℋ) = V (D₁ ⟨ζ, h1⟩)) :
    ∀ p ∈ (D₁.graph : Set (ℋ × ℋ)), (p.1, V p.2) ∈ (D₂.graph : Set (ℋ × ℋ)) := by
  set Φ : ℋ × ℋ → ℋ × ℋ := fun p => (p.1, V p.2) with hΦ
  have hΦcont : Continuous Φ := by fun_prop
  have hstep : Φ '' ((D₁.domRestrict S).graph : Set (ℋ × ℋ)) ⊆ (D₂.graph : Set (ℋ × ℋ)) := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨z, hz⟩ := (LinearPMap.mem_graph_iff' _).1 hp
    have hzS : (z : ℋ) ∈ S := z.2.1
    have hz1 : (z : ℋ) ∈ D₁.domain := z.2.2
    have hz2 : (z : ℋ) ∈ D₂.domain := hS₂ hzS
    refine (LinearPMap.mem_graph_iff' _).2 ⟨⟨(z : ℋ), hz2⟩, ?_⟩
    rw [← hz]
    refine Prod.ext rfl ?_
    show (D₂ ⟨(z : ℋ), hz2⟩ : ℋ) = V ((D₁.domRestrict S) z)
    rw [LinearPMap.domRestrict_apply (y := (⟨(z : ℋ), hz1⟩ : D₁.domain)) rfl]
    exact hag (z : ℋ) hzS hz1 hz2
  have hgr := (hasCore_iff_closure_graph h₁ hS₁.le_domain).1 hS₁
  intro p hp
  rw [← hgr] at hp
  have : Φ '' closure ((D₁.domRestrict S).graph : Set (ℋ × ℋ))
      ⊆ closure (Φ '' ((D₁.domRestrict S).graph : Set (ℋ × ℋ))) :=
    image_closure_subset_closure_image hΦcont
  have hmem : Φ p ∈ closure ((D₂.graph : Set (ℋ × ℋ))) :=
    closure_mono hstep (this ⟨p, hp, rfl⟩)
  rwa [h₂.closure_eq] at hmem


omit [CompleteSpace ℋ] in
/-- Reading off a domain inclusion and the pointwise identity from the graph inclusion. -/
theorem domain_mem_of_graph_map {D₁ D₂ : ℋ →ₗ.[ℂ] ℋ} {V : ℋ →L[ℂ] ℋ}
    (h : ∀ p ∈ (D₁.graph : Set (ℋ × ℋ)), (p.1, V p.2) ∈ (D₂.graph : Set (ℋ × ℋ)))
    (y : D₁.domain) :
    ∃ h2 : (y : ℋ) ∈ D₂.domain, (D₂ ⟨(y : ℋ), h2⟩ : ℋ) = V (D₁ y) := by
  have hp : ((y : ℋ), (D₁ y : ℋ)) ∈ (D₁.graph : Set (ℋ × ℋ)) :=
    (LinearPMap.mem_graph_iff' _).2 ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := (LinearPMap.mem_graph_iff' _).1 (h _ hp)
  have hz1 : (z : ℋ) = (y : ℋ) := congrArg Prod.fst hz
  have hz2 : (D₂ z : ℋ) = V (D₁ y) := congrArg Prod.snd hz
  refine ⟨hz1 ▸ z.2, ?_⟩
  have hcast : (⟨(y : ℋ), hz1 ▸ z.2⟩ : D₂.domain) = z := Subtype.ext hz1.symm
  rw [hcast, hz2]

end Helpers

/-! ## Part 1: elementary facts about the Hilbert space tensor product -/

section Tensor

variable {ℋ 𝒦 : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]

/-- `x ↦ x ⊗ y`, as a bounded operator. -/
noncomputable def htmulL (y : 𝒦) : ℋ →L[ℂ] HT ℋ 𝒦 :=
  LinearMap.mkContinuous ((hilbTensor ℋ 𝒦).map.flip y) ‖y‖ fun x => by
    show ‖x ⊗ₕ y‖ ≤ ‖y‖ * ‖x‖
    rw [norm_htmul, mul_comm]

@[simp] theorem htmulL_apply (y : 𝒦) (x : ℋ) : htmulL y x = x ⊗ₕ y := rfl

/-- `y ↦ x ⊗ y`, as a bounded operator. -/
noncomputable def htmulR (x : ℋ) : 𝒦 →L[ℂ] HT ℋ 𝒦 :=
  LinearMap.mkContinuous ((hilbTensor ℋ 𝒦).map x) ‖x‖ fun y => by
    show ‖x ⊗ₕ y‖ ≤ ‖x‖ * ‖y‖
    rw [norm_htmul]

@[simp] theorem htmulR_apply (x : ℋ) (y : 𝒦) : htmulR x y = x ⊗ₕ y := rfl

/-- The span of `{u ⊗ v : u ∈ S, v ∈ T}` is dense as soon as `S` and `T` are. -/
theorem dense_span_htmul {S : Submodule ℂ ℋ} {T : Submodule ℂ 𝒦}
    (hS : Dense (S : Set ℋ)) (hT : Dense (T : Set 𝒦)) :
    Dense ((Submodule.span ℂ {t : HT ℋ 𝒦 | ∃ u ∈ S, ∃ v ∈ T, t = u ⊗ₕ v} :
      Submodule ℂ (HT ℋ 𝒦)) : Set (HT ℋ 𝒦)) := by
  set G : Set (HT ℋ 𝒦) := {t : HT ℋ 𝒦 | ∃ u ∈ S, ∃ v ∈ T, t = u ⊗ₕ v} with hG
  set C : Submodule ℂ (HT ℋ 𝒦) := (Submodule.span ℂ G).topologicalClosure with hC
  have hCclosed : IsClosed (C : Set (HT ℋ 𝒦)) := Submodule.isClosed_topologicalClosure _
  have hGC : ∀ t ∈ G, t ∈ C := fun t ht =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ht)
  -- Step 1: `x ⊗ v ∈ C` for every `x` and every `v ∈ T`.
  have hstep1 : ∀ v ∈ T, ∀ x : ℋ, x ⊗ₕ v ∈ C := by
    intro v hv x
    set Sub : Submodule ℂ ℋ := C.comap ((htmulL v : ℋ →L[ℂ] HT ℋ 𝒦) : ℋ →ₗ[ℂ] HT ℋ 𝒦) with hSub
    have hSubClosed : IsClosed (Sub : Set ℋ) :=
      hCclosed.preimage (htmulL v).continuous
    have hSle : (S : Set ℋ) ⊆ (Sub : Set ℋ) := by
      intro u hu
      exact hGC _ ⟨u, hu, v, hv, rfl⟩
    have : (Set.univ : Set ℋ) ⊆ (Sub : Set ℋ) := by
      rw [← hS.closure_eq]
      exact hSubClosed.closure_subset_iff.2 hSle
    exact this (Set.mem_univ x)
  -- Step 2: `x ⊗ y ∈ C` for all `x`, `y`.
  have hstep2 : ∀ (x : ℋ) (y : 𝒦), x ⊗ₕ y ∈ C := by
    intro x y
    set Sub : Submodule ℂ 𝒦 := C.comap ((htmulR x : 𝒦 →L[ℂ] HT ℋ 𝒦) : 𝒦 →ₗ[ℂ] HT ℋ 𝒦) with hSub
    have hSubClosed : IsClosed (Sub : Set 𝒦) :=
      hCclosed.preimage (htmulR x).continuous
    have hTle : (T : Set 𝒦) ⊆ (Sub : Set 𝒦) := fun v hv => hstep1 v hv x
    have : (Set.univ : Set 𝒦) ⊆ (Sub : Set 𝒦) := by
      rw [← hT.closure_eq]
      exact hSubClosed.closure_subset_iff.2 hTle
    exact this (Set.mem_univ y)
  -- Conclude.
  have htop : (Submodule.span ℂ {t : HT ℋ 𝒦 | ∃ x y, t = (hilbTensor ℋ 𝒦).map x y}) ≤ C := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, y, rfl⟩
    exact hstep2 x y
  have hdense := (hilbTensor ℋ 𝒦).isTensor.dense
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_univ_subset ?_
  calc (Set.univ : Set (HT ℋ 𝒦))
      = closure ((Submodule.span ℂ {t : HT ℋ 𝒦 | ∃ x y, t = (hilbTensor ℋ 𝒦).map x y} :
          Submodule ℂ (HT ℋ 𝒦)) : Set (HT ℋ 𝒦)) := hdense.closure_eq.symm
    _ ⊆ closure (C : Set (HT ℋ 𝒦)) := closure_mono htop
    _ = (C : Set (HT ℋ 𝒦)) := hCclosed.closure_eq
    _ = closure ((Submodule.span ℂ G : Submodule ℂ (HT ℋ 𝒦)) : Set (HT ℋ 𝒦)) :=
        Submodule.topologicalClosure_coe _

/-- The tensor product of two positive operators is positive. -/
theorem opTensor_nonneg {f : ℋ →L[ℂ] ℋ} {g : 𝒦 →L[ℂ] 𝒦} (hf : 0 ≤ f) (hg : 0 ≤ g) :
    (0 : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) ≤ opTensor f g := by
  have hfs : CFC.sqrt f * CFC.sqrt f = f := CFC.sqrt_mul_sqrt_self f hf
  have hgs : CFC.sqrt g * CFC.sqrt g = g := CFC.sqrt_mul_sqrt_self g hg
  have hfsa : IsSelfAdjoint (CFC.sqrt f) := .of_nonneg (CFC.sqrt_nonneg f)
  have hgsa : IsSelfAdjoint (CFC.sqrt g) := .of_nonneg (CFC.sqrt_nonneg g)
  have hstar : star (opTensor (CFC.sqrt f) (CFC.sqrt g)) = opTensor (CFC.sqrt f) (CFC.sqrt g) := by
    rw [opTensor_star, hfsa.star_eq, hgsa.star_eq]
  have : opTensor f g
      = star (opTensor (CFC.sqrt f) (CFC.sqrt g)) * opTensor (CFC.sqrt f) (CFC.sqrt g) := by
    rw [hstar, ← opTensor_mul, hfs, hgs]
  rw [this]
  exact star_mul_self_nonneg _

/-- The tensor product of two operators with dense range has dense range. -/
theorem denseRange_opTensor {f : ℋ →L[ℂ] ℋ} {g : 𝒦 →L[ℂ] 𝒦}
    (hf : Dense ((LinearMap.range (f : ℋ →ₗ[ℂ] ℋ) : Submodule ℂ ℋ) : Set ℋ))
    (hg : Dense ((LinearMap.range (g : 𝒦 →ₗ[ℂ] 𝒦) : Submodule ℂ 𝒦) : Set 𝒦)) :
    Dense ((LinearMap.range ((opTensor f g : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) : HT ℋ 𝒦 →ₗ[ℂ] HT ℋ 𝒦) :
      Submodule ℂ (HT ℋ 𝒦)) : Set (HT ℋ 𝒦)) := by
  have hsub : (Submodule.span ℂ {t : HT ℋ 𝒦 | ∃ u ∈ LinearMap.range (f : ℋ →ₗ[ℂ] ℋ),
      ∃ v ∈ LinearMap.range (g : 𝒦 →ₗ[ℂ] 𝒦), t = u ⊗ₕ v}) ≤
      LinearMap.range ((opTensor f g : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) : HT ℋ 𝒦 →ₗ[ℂ] HT ℋ 𝒦) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, rfl⟩
    exact ⟨x ⊗ₕ y, opTensor_apply f g x y⟩
  exact Dense.mono (SetLike.coe_subset_coe.2 hsub) (dense_span_htmul hf hg)


/-- **The commuting pair behind the tensor factorisation.**  If `(a, b)` and `(a', b')` are
modular pairs then `c = a ⊗ a'` and `d = b ⊗ b'` are positive, commuting and injective — but
`c² + d² ≠ 1`, which is exactly why the tensor product of the two `Δ^{1/2}` is not closed. -/
theorem isCommutingPair_opTensor {a b : ℋ →L[ℂ] ℋ} {a' b' : 𝒦 →L[ℂ] 𝒦}
    (h : IsModularPair a b) (h' : IsModularPair a' b') :
    IsCommutingPair (opTensor a a') (opTensor b b') := by
  have hda : Dense ((LinearMap.range ((opTensor a a' : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) :
      HT ℋ 𝒦 →ₗ[ℂ] HT ℋ 𝒦) : Submodule ℂ (HT ℋ 𝒦)) : Set (HT ℋ 𝒦)) :=
    denseRange_opTensor (dense_range_of_nonneg_injective h.nonneg_fst h.injective_fst)
      (dense_range_of_nonneg_injective h'.nonneg_fst h'.injective_fst)
  have hdb : Dense ((LinearMap.range ((opTensor b b' : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) :
      HT ℋ 𝒦 →ₗ[ℂ] HT ℋ 𝒦) : Submodule ℂ (HT ℋ 𝒦)) : Set (HT ℋ 𝒦)) :=
    denseRange_opTensor (dense_range_of_nonneg_injective h.nonneg_snd h.injective_snd)
      (dense_range_of_nonneg_injective h'.nonneg_snd h'.injective_snd)
  have hna : (0 : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) ≤ opTensor a a' :=
    opTensor_nonneg h.nonneg_fst h'.nonneg_fst
  have hnb : (0 : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) ≤ opTensor b b' :=
    opTensor_nonneg h.nonneg_snd h'.nonneg_snd
  refine ⟨hna, hnb, ?_, ?_, ?_⟩
  · show opTensor a a' * opTensor b b' = opTensor b b' * opTensor a a'
    rw [← opTensor_mul, ← opTensor_mul, h.commute.eq, h'.commute.eq]
  · exact injective_of_denseRange (IsSelfAdjoint.of_nonneg hna) hda
  · exact injective_of_denseRange (IsSelfAdjoint.of_nonneg hnb) hdb

end Tensor

/-! ## Part 2: the ℂ-linear unitary `W`

The map `(ζ, ζ') ↦ J_ξ (J_ω ζ ⊗ J_{ω'} ζ')` is ℂ-**bi**linear, because two conjugations
compose; so it factors through `ℋ ⊗ 𝒦` by the universal property, and the resulting `W` is
unitary.  **No antilinear tensor product is built anywhere**: `J_ω ⊗ J_{ω'}` is only
ℝ-bilinear, so it does not factor through `ℋ ⊗_ℂ 𝒦`. -/

section Conj

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A vector orthogonal to a set whose span is dense is zero. -/
theorem eq_zero_of_inner_span_dense {S : Set H}
    (hS : Dense ((Submodule.span ℂ S : Submodule ℂ H) : Set H)) {w : H}
    (h : ∀ v ∈ S, ⟪w, v⟫ = 0) : w = 0 := by
  have hker : Submodule.span ℂ S ≤
      LinearMap.ker ((innerSL ℂ w : H →L[ℂ] ℂ) : H →ₗ[ℂ] ℂ) := by
    refine Submodule.span_le.2 fun v hv => ?_
    simpa [LinearMap.mem_ker] using h v hv
  have hcont : Continuous fun v : H => ⟪w, v⟫ := (innerSL ℂ w).continuous
  have heq : Set.EqOn (fun v : H => ⟪w, v⟫) (fun _ : H => (0 : ℂ))
      ((Submodule.span ℂ S : Submodule ℂ H) : Set H) := by
    intro v hv
    simpa [LinearMap.mem_ker] using hker hv
  have hfun := Continuous.ext_on hS hcont continuous_const heq
  exact inner_self_eq_zero.1 (congrFun hfun w)

omit [CompleteSpace H] in
/-- Two vectors with the same inner products against a spanning dense set are equal. -/
theorem eq_of_inner_span_dense {S : Set H}
    (hS : Dense ((Submodule.span ℂ S : Submodule ℂ H) : Set H)) {u₁ u₂ : H}
    (h : ∀ v ∈ S, ⟪u₁, v⟫ = ⟪u₂, v⟫) : u₁ = u₂ := by
  have : u₁ - u₂ = 0 := by
    refine eq_zero_of_inner_span_dense hS fun v hv => ?_
    rw [inner_sub_left, h v hv, sub_self]
  exact sub_eq_zero.1 this

variable (K : ClosedSubmodule ℝ H) (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤)

include hsep hcyc

/-- `J` is antiunitary: `⟪J x, J y⟫ = conj ⟪x, y⟫`. -/
theorem J_inner (x y : H) : ⟪J K x, J K y⟫ = (starRingEnd ℂ) ⟪x, y⟫ := by
  refine Complex.ext ?_ ?_
  · have h1 : (⟪J K x, J K y⟫).re = inner ℝ (J K x) (J K y) := rfl
    have h2 : (⟪x, y⟫).re = inner ℝ x y := rfl
    rw [Complex.conj_re, h1, h2]
    exact J_inner_real K hsep hcyc x y
  · rw [Complex.conj_im, im_inner, im_inner]
    have hIy : (-I) • J K y = J K (I • y) := by
      rw [J_smul_I K hsep hcyc, neg_smul]
    rw [hIy, J_inner_real K hsep hcyc]
    have hneg : (I : ℂ) • y = -((-I : ℂ) • y) := by module
    rw [hneg, inner_neg_right]

end Conj

section W

variable {ℋ 𝒦 : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]

theorem htmul_add_right (x : ℋ) (y y' : 𝒦) : x ⊗ₕ (y + y') = x ⊗ₕ y + x ⊗ₕ y' := by
  show (hilbTensor ℋ 𝒦).map x (y + y') = _
  rw [map_add]; rfl

variable (ℋ 𝒦) in
/-- The set of elementary tensors; its span is dense. -/
def elemTensors : Set (HT ℋ 𝒦) := {t : HT ℋ 𝒦 | ∃ (x : ℋ) (y : 𝒦), t = x ⊗ₕ y}

theorem dense_span_elemTensors :
    Dense ((Submodule.span ℂ (elemTensors ℋ 𝒦) : Submodule ℂ (HT ℋ 𝒦)) : Set (HT ℋ 𝒦)) :=
  (hilbTensor ℋ 𝒦).isTensor.dense

/-- **The ℂ-linear unitary `W`.**  Given conjugate-linear isometric involutions `Jh`, `Jk`,
`Jt` of `ℋ`, `𝒦` and `ℋ ⊗ 𝒦`, there is a unitary `W` on `ℋ ⊗ 𝒦` with
`W (x ⊗ y) = Jt (Jh x ⊗ Jk y)`. -/
theorem exists_conjTensor (Jh : ℋ →L[ℝ] ℋ) (Jk : 𝒦 →L[ℝ] 𝒦)
    (Jt : HT ℋ 𝒦 →L[ℝ] HT ℋ 𝒦)
    (hJhs : ∀ (c : ℂ) (x : ℋ), Jh (c • x) = (starRingEnd ℂ) c • Jh x)
    (hJks : ∀ (c : ℂ) (y : 𝒦), Jk (c • y) = (starRingEnd ℂ) c • Jk y)
    (hJts : ∀ (c : ℂ) (t : HT ℋ 𝒦), Jt (c • t) = (starRingEnd ℂ) c • Jt t)
    (hJhi : ∀ x y : ℋ, ⟪Jh x, Jh y⟫ = (starRingEnd ℂ) ⟪x, y⟫)
    (hJki : ∀ x y : 𝒦, ⟪Jk x, Jk y⟫ = (starRingEnd ℂ) ⟪x, y⟫)
    (hJti : ∀ x y : HT ℋ 𝒦, ⟪Jt x, Jt y⟫ = (starRingEnd ℂ) ⟪x, y⟫)
    (hJtn : ∀ t : HT ℋ 𝒦, ‖Jt t‖ = ‖t‖)
    (hJhJ : ∀ x : ℋ, Jh (Jh x) = x) (hJkJ : ∀ y : 𝒦, Jk (Jk y) = y)
    (hJtJ : ∀ t : HT ℋ 𝒦, Jt (Jt t) = t) :
    ∃ W : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦,
      (∀ (x : ℋ) (y : 𝒦), W (x ⊗ₕ y) = Jt (Jh x ⊗ₕ Jk y)) ∧
        W ∈ unitary (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) := by
  classical
  -- the ℂ-bilinear map `β (x, y) = Jt (Jh x ⊗ Jk y)`
  set β : ℋ →ₗ[ℂ] 𝒦 →ₗ[ℂ] HT ℋ 𝒦 :=
    { toFun := fun x =>
        { toFun := fun y => Jt (Jh x ⊗ₕ Jk y)
          map_add' := fun y y' => by
            simp only [map_add, htmul_add_right]
          map_smul' := fun c y => by
            simp only [RingHom.id_apply]
            rw [hJks, htmul_smul_right, hJts, starRingEnd_self_apply] }
      map_add' := fun x x' => by
        refine LinearMap.ext fun y => ?_
        show Jt ((Jh (x + x')) ⊗ₕ Jk y) = Jt (Jh x ⊗ₕ Jk y) + Jt (Jh x' ⊗ₕ Jk y)
        rw [map_add, htmul_add_left, map_add]
      map_smul' := fun c x => by
        refine LinearMap.ext fun y => ?_
        show Jt ((Jh (c • x)) ⊗ₕ Jk y) = c • Jt (Jh x ⊗ₕ Jk y)
        rw [hJhs, htmul_smul_left, hJts, starRingEnd_self_apply] } with hβdef
  have hβ_apply : ∀ (x : ℋ) (y : 𝒦), β x y = Jt (Jh x ⊗ₕ Jk y) := fun _ _ => rfl
  -- `β` is ℓ²-bounded by `1`
  have hbdd : L2Bounded β 1 := by
    refine ⟨zero_le_one, fun n x y => ?_⟩
    have hsum : ∑ i, β (x i) (y i) = Jt (∑ i, Jh (x i) ⊗ₕ Jk (y i)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => hβ_apply (x i) (y i)
    rw [hsum, hJtn, one_pow, one_mul]
    have hgram := (hilbTensor ℋ 𝒦).isTensor.gram_sum_re n (fun i => Jh (x i)) (fun i => Jk (y i))
    have hconv : ∑ i, Jh (x i) ⊗ₕ Jk (y i)
        = ∑ i, (hilbTensor ℋ 𝒦).map (Jh (x i)) (Jk (y i)) := rfl
    rw [hconv, ← hgram]
    have hterm : ∀ i j, ⟪Jh (x i), Jh (x j)⟫ * ⟪Jk (y i), Jk (y j)⟫
        = (starRingEnd ℂ) (⟪x i, x j⟫ * ⟪y i, y j⟫) := by
      intro i j
      rw [hJhi, hJki, map_mul]
    simp only [hterm]
    have hconj : (∑ i, ∑ j, (starRingEnd ℂ) (⟪x i, x j⟫ * ⟪y i, y j⟫))
        = (starRingEnd ℂ) (∑ i, ∑ j, ⟪x i, x j⟫ * ⟪y i, y j⟫) := by
      simp only [map_sum]
    rw [hconj, Complex.conj_re]
  obtain ⟨-, huniv⟩ := hilb_tensor_universal_property (L := HT ℋ 𝒦)
    (hilbTensor ℋ 𝒦).map (hilbTensor ℋ 𝒦).isTensor
  obtain ⟨W, hW, -, -⟩ := huniv β 1 hbdd
  have hWapply : ∀ (x : ℋ) (y : 𝒦), W (x ⊗ₕ y) = Jt (Jh x ⊗ₕ Jk y) := fun x y =>
    (hW x y).trans (hβ_apply x y)
  refine ⟨W, hWapply, ?_⟩
  -- `W` preserves inner products
  have hstarW : star W * W = 1 := by
    refine ext_htmul fun x y => ?_
    show (star W) (W (x ⊗ₕ y)) = (1 : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) (x ⊗ₕ y)
    refine eq_of_inner_span_dense (dense_span_elemTensors (ℋ := ℋ) (𝒦 := 𝒦)) ?_
    rintro _ ⟨x', y', rfl⟩
    have hleft : ⟪(star W) (W (x ⊗ₕ y)), x' ⊗ₕ y'⟫ = ⟪W (x ⊗ₕ y), W (x' ⊗ₕ y')⟫ := by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ContinuousLinearMap.adjoint_inner_left W (x' ⊗ₕ y') (W (x ⊗ₕ y))
    rw [hleft, hWapply, hWapply, hJti, htmul_inner, hJhi, hJki, map_mul,
      starRingEnd_self_apply, starRingEnd_self_apply, ← htmul_inner]
    rfl
  refine Unitary.mem_iff.2 ⟨hstarW, ?_⟩
  -- the range of `W` is dense, so `W (star W) = 1` too
  have hJtRW : ∀ v ∈ Submodule.span ℂ (elemTensors ℋ 𝒦),
      Jt v ∈ Set.range (W : HT ℋ 𝒦 → HT ℋ 𝒦) := by
    intro v hv
    refine Submodule.span_induction
      (p := fun w _ => Jt w ∈ Set.range (W : HT ℋ 𝒦 → HT ℋ 𝒦)) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨x, y, rfl⟩
      refine ⟨Jh x ⊗ₕ Jk y, ?_⟩
      show W (Jh x ⊗ₕ Jk y) = Jt (x ⊗ₕ y)
      rw [hWapply, hJhJ, hJkJ]
    · exact ⟨0, by simp⟩
    · rintro u u' - - ⟨s, hs⟩ ⟨s', hs'⟩
      exact ⟨s + s', by rw [map_add, hs, hs', map_add]⟩
    · rintro c u - ⟨s, hs⟩
      exact ⟨(starRingEnd ℂ) c • s, by rw [map_smul, hs, hJts]⟩
  have hrange : Dense (Set.range (W : HT ℋ 𝒦 → HT ℋ 𝒦)) := by
    have hcl := (dense_span_elemTensors (ℋ := ℋ) (𝒦 := 𝒦)).closure_eq
    have h1 : Jt '' closure ((Submodule.span ℂ (elemTensors ℋ 𝒦) :
          Submodule ℂ (HT ℋ 𝒦)) : Set (HT ℋ 𝒦))
        ⊆ closure (Jt '' ((Submodule.span ℂ (elemTensors ℋ 𝒦) :
          Submodule ℂ (HT ℋ 𝒦)) : Set (HT ℋ 𝒦))) :=
      image_closure_subset_closure_image Jt.continuous
    have h2 : Jt '' ((Submodule.span ℂ (elemTensors ℋ 𝒦) :
        Submodule ℂ (HT ℋ 𝒦)) : Set (HT ℋ 𝒦)) ⊆ Set.range (W : HT ℋ 𝒦 → HT ℋ 𝒦) := by
      rintro _ ⟨v, hv, rfl⟩
      exact hJtRW v hv
    refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset fun z _ => ?_)
    have hmem : z ∈ Jt '' closure ((Submodule.span ℂ (elemTensors ℋ 𝒦) :
        Submodule ℂ (HT ℋ 𝒦)) : Set (HT ℋ 𝒦)) := by
      refine ⟨Jt z, ?_, hJtJ z⟩
      rw [hcl]
      trivial
    exact closure_mono h2 (h1 hmem)
  refine clm_ext_of_dense hrange ?_
  rintro w hw
  obtain ⟨t, rfl⟩ : ∃ t, W t = w := hw
  show W ((star W) (W t)) = (1 : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) (W t)
  have hst : (star W) (W t) = ((star W * W) : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) t := rfl
  rw [hst, hstarW]
  rfl

end W

/-! ## Part 3: `ξ = ω ⊗ ω'` is cyclic and separating for `M ⊗̄ N`

Cyclic because `span {xω ⊗ yω'}` is dense; separating because `ξ` is cyclic for the
*easy* part `M' ⊙ N'` of the commutant — **no commutation theorem is used**. -/

section VNTensor

variable {ℋ 𝒦 : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (N : StarSubalgebra ℂ (𝒦 →L[ℂ] 𝒦))

/-- `M ⊗̄ N`: the von Neumann algebra generated by `{x ⊗ y : x ∈ M, y ∈ N}` in `B(ℋ ⊗ 𝒦)`. -/
noncomputable def vnTensor : StarSubalgebra ℂ (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) :=
  wstar (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) (spatialSpan M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦))

theorem spatialSpan_le_vnTensor :
    (spatialSpan M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) ⊆ (vnTensor M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) :=
  (isVNSubalgebra_wstar (spatialSpan M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦))).2

theorem opTensor_mem_vnTensor {x : ℋ →L[ℂ] ℋ} (hx : x ∈ M) {y : 𝒦 →L[ℂ] 𝒦} (hy : y ∈ N) :
    opTensor x y ∈ vnTensor M N :=
  spatialSpan_le_vnTensor M N (Submodule.subset_span ⟨x, hx, y, hy, rfl⟩)

/-- `(M ⊗̄ N)□ = (M ⊙ N)□`. -/
theorem commutant_vnTensor :
    commutant (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) (vnTensor M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦))
      = commutant (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) (spatialSpan M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) := by
  have hdc := (double_commutant (spatialSpan M N)).2.2
  rw [vnTensor, ← hdc]
  exact (commutant_basic_1 (spatialSpan M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦))
    (spatialSpan M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦))).2.2.2

/-- `(M ⊗̄ N)□□ = M ⊗̄ N`: the tensor product is a von Neumann algebra. -/
theorem bicommutant_vnTensor :
    commutant (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)
        (commutant (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) (vnTensor M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)))
      = (vnTensor M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) := by
  rw [commutant_vnTensor]
  exact (double_commutant (spatialSpan M N)).2.2

/-- The easy inclusion `M□ ⊙ N□ ⊆ (M ⊗̄ N)□`. -/
theorem opTensor_mem_commutant_vnTensor {u : ℋ →L[ℂ] ℋ}
    (hu : u ∈ commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ))) {v : 𝒦 →L[ℂ] 𝒦}
    (hv : v ∈ commutant (𝒦 →L[ℂ] 𝒦) (N : Set (𝒦 →L[ℂ] 𝒦))) :
    opTensor u v ∈ commutant (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) (vnTensor M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) := by
  rw [commutant_vnTensor]
  intro s hs
  show s * opTensor u v = opTensor u v * s
  have hs' : s ∈ Submodule.span ℂ {x : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦 |
      ∃ a ∈ M, ∃ b ∈ N, x = opTensor a b} := hs
  refine Submodule.span_induction
    (p := fun w _ => w * opTensor u v = opTensor u v * w) ?_ ?_ ?_ ?_ hs'
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [← opTensor_mul, ← opTensor_mul, hu x hx, hv y hy]
  · rw [zero_mul, mul_zero]
  · intro w w' _ _ hw hw'
    rw [add_mul, mul_add, hw, hw']
  · intro c w _ hw
    rw [smul_mul_assoc, mul_smul_comm, hw]

variable (ω : ℋ) (ω' : 𝒦)

/-- The generators `x ω ⊗ y ω'` of the orbit of `ξ` under `M ⊙ N`. -/
def orbitGen : Set (HT ℋ 𝒦) := {t : HT ℋ 𝒦 | ∃ x ∈ M, ∃ y ∈ N, t = x ω ⊗ₕ y ω'}

theorem orbitGen_subset_orbitSub :
    orbitGen M N ω ω' ⊆ (orbitSub (vnTensor M N) (ω ⊗ₕ ω') : Set (HT ℋ 𝒦)) := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact ⟨opTensor x y, opTensor_mem_vnTensor M N hx hy, (opTensor_apply x y ω ω').symm⟩

/-- **`ξ = ω ⊗ ω'` is cyclic for `M ⊗̄ N`.** -/
theorem isCyclicVector_htmul (hM : IsCyclicVector M ω) (hN : IsCyclicVector N ω') :
    IsCyclicVector (vnTensor M N) (ω ⊗ₕ ω') := by
  have hspan : Dense ((Submodule.span ℂ (orbitGen M N ω ω') :
      Submodule ℂ (HT ℋ 𝒦)) : Set (HT ℋ 𝒦)) := by
    have := dense_span_htmul (S := orbitSub M ω) (T := orbitSub N ω') hM hN
    refine this.mono ?_
    refine SetLike.coe_subset_coe.2 (Submodule.span_mono ?_)
    rintro _ ⟨u, hu, v, hv, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨x, hx, y, hy, rfl⟩
  refine hspan.mono ?_
  refine (Submodule.span_le.2 ?_ : Submodule.span ℂ (orbitGen M N ω ω') ≤
    orbitSub (vnTensor M N) (ω ⊗ₕ ω'))
  exact orbitGen_subset_orbitSub M N ω ω'

/-- **`ξ = ω ⊗ ω'` is separating for `M ⊗̄ N`.**  Because `ξ` is cyclic for `M□ ⊙ N□`, which
is contained in `(M ⊗̄ N)□` by the *elementary* inclusion. -/
theorem isSeparatingVector_htmul
    (hM : Dense {y : ℋ | ∃ x ∈ commutantSA M, y = x ω})
    (hN : Dense {y : 𝒦 | ∃ x ∈ commutantSA N, y = x ω'}) :
    IsSeparatingVector (vnTensor M N) (ω ⊗ₕ ω') := by
  intro z hz hzξ
  have hspan : Dense ((Submodule.span ℂ (orbitGen (commutantSA M) (commutantSA N) ω ω') :
      Submodule ℂ (HT ℋ 𝒦)) : Set (HT ℋ 𝒦)) := by
    have := dense_span_htmul (S := orbitSub (commutantSA M) ω)
      (T := orbitSub (commutantSA N) ω') hM hN
    refine this.mono ?_
    refine SetLike.coe_subset_coe.2 (Submodule.span_mono ?_)
    rintro _ ⟨u, hu, v, hv, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨x, hx, y, hy, rfl⟩
  refine clm_eq_zero_of_span_dense hspan ?_
  rintro _ ⟨u, hu, v, hv, rfl⟩
  have hcomm : opTensor u v ∈ commutant (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)
      (vnTensor M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) :=
    opTensor_mem_commutant_vnTensor M N hu hv
  have hzc : z * opTensor u v = opTensor u v * z := hcomm z hz
  have : z ((opTensor u v) (ω ⊗ₕ ω')) = (opTensor u v) (z (ω ⊗ₕ ω')) := by
    have := congrArg (fun w : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦 => w (ω ⊗ₕ ω')) hzc
    exact this
  rw [opTensor_apply] at this
  rw [this, hzξ, map_zero]

end VNTensor

/-! ## Part 4: `span (Mω ⊙ Nω')` is a core for both operators -/

section Main

variable {ℋ 𝒦 : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (N : StarSubalgebra ℂ (𝒦 →L[ℂ] 𝒦))
variable (ω : ℋ) (ω' : 𝒦)

/-- `E₀ = span (M ω ⊙ N ω')`, the orbit of `ξ` under the algebraic tensor product. -/
noncomputable def orbitSpan : Submodule ℂ (HT ℋ 𝒦) := Submodule.span ℂ (orbitGen M N ω ω')

theorem mem_orbitSpan_of_gen {x : ℋ →L[ℂ] ℋ} (hx : x ∈ M) {y : 𝒦 →L[ℂ] 𝒦} (hy : y ∈ N) :
    x ω ⊗ₕ y ω' ∈ orbitSpan M N ω ω' :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

section Std

variable (hsM : Ksub M ω ⊓ (Ksub M ω).mulI = ⊥) (hcM : Ksub M ω ⊔ (Ksub M ω).mulI = ⊤)
variable (hsN : Ksub N ω' ⊓ (Ksub N ω').mulI = ⊥) (hcN : Ksub N ω' ⊔ (Ksub N ω').mulI = ⊤)

include hsM hcM hsN hcN

/-- The commuting pair `c = a_ω ⊗ a_{ω'}`, `d = b_ω ⊗ b_{ω'}`. -/
theorem isCommutingPair_ab :
    IsCommutingPair (opTensor (a (Ksub M ω)) (a (Ksub N ω')))
      (opTensor (b (Ksub M ω)) (b (Ksub N ω'))) :=
  isCommutingPair_opTensor (mp (Ksub M ω) hsM hcM) (mp (Ksub N ω') hsN hcN)

/-- **`E₀ = c(E)` for a dense `E`.**  The candidate `E = a⁻¹(Mω) ⊙ a'⁻¹(Nω')` is dense
precisely because `Mω` is a core for `Δ_ω^{1/2}`, which `Tomita.lean`'s `orbit_hasCore`
proves outright; so the normalisation lemma's `hasCore` applies and is *not* circular. -/
theorem orbitSpan_hasCore_comm :
    (isCommutingPair_ab M N ω ω' hsM hcM hsN hcN).isModularPair.D.HasCore
      (orbitSpan M N ω ω') := by
  have hEM : Dense (((orbitSub M ω).comap ((a (Ksub M ω)) : ℋ →ₗ[ℂ] ℋ) :
      Submodule ℂ ℋ) : Set ℋ) :=
    IsModularPair.dense_comap_of_hasCore (mp (Ksub M ω) hsM hcM) (orbit_hasCore M ω hsM hcM)
  have hEN : Dense (((orbitSub N ω').comap ((a (Ksub N ω')) : 𝒦 →ₗ[ℂ] 𝒦) :
      Submodule ℂ 𝒦) : Set 𝒦) :=
    IsModularPair.dense_comap_of_hasCore (mp (Ksub N ω') hsN hcN) (orbit_hasCore N ω' hsN hcN)
  have hEd := dense_span_htmul hEM hEN
  have hmap : (Submodule.span ℂ {t : HT ℋ 𝒦 |
        ∃ u ∈ (orbitSub M ω).comap ((a (Ksub M ω)) : ℋ →ₗ[ℂ] ℋ),
        ∃ v ∈ (orbitSub N ω').comap ((a (Ksub N ω')) : 𝒦 →ₗ[ℂ] 𝒦), t = u ⊗ₕ v}).map
      ((opTensor (a (Ksub M ω)) (a (Ksub N ω')) : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) :
        HT ℋ 𝒦 →ₗ[ℂ] HT ℋ 𝒦) = orbitSpan M N ω ω' := by
    rw [orbitSpan, Submodule.map_span]
    congr 1
    ext t
    constructor
    · rintro ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
      obtain ⟨x, hx, hxe⟩ := hu
      obtain ⟨y, hy, hye⟩ := hv
      have hxe' : a (Ksub M ω) u = x ω := hxe
      have hye' : a (Ksub N ω') v = y ω' := hye
      refine ⟨x, hx, y, hy, ?_⟩
      show opTensor (a (Ksub M ω)) (a (Ksub N ω')) (u ⊗ₕ v) = x ω ⊗ₕ y ω'
      rw [opTensor_apply, hxe', hye']
    · rintro ⟨x, hx, y, hy, rfl⟩
      obtain ⟨u, hu⟩ : ∃ u : ℋ, a (Ksub M ω) u = x ω := orbit_mem_domain M ω hsM hcM hx
      obtain ⟨v, hv⟩ : ∃ v : 𝒦, a (Ksub N ω') v = y ω' := orbit_mem_domain N ω' hsN hcN hy
      refine ⟨u ⊗ₕ v, ⟨u, ?_, v, ?_, rfl⟩, ?_⟩
      · show a (Ksub M ω) u ∈ orbitSub M ω
        exact hu ▸ ⟨x, hx, rfl⟩
      · show a (Ksub N ω') v ∈ orbitSub N ω'
        exact hv ▸ ⟨y, hy, rfl⟩
      · show opTensor (a (Ksub M ω)) (a (Ksub N ω')) (u ⊗ₕ v) = x ω ⊗ₕ y ω'
        rw [opTensor_apply, hu, hv]
  have := (isCommutingPair_ab M N ω ω' hsM hcM hsN hcN).hasCore hEd
  rwa [hmap] at this

end Std

section Tens

variable (hsT : Ksub (vnTensor M N) (ω ⊗ₕ ω') ⊓ (Ksub (vnTensor M N) (ω ⊗ₕ ω')).mulI = ⊥)
variable (hcT : Ksub (vnTensor M N) (ω ⊗ₕ ω') ⊔ (Ksub (vnTensor M N) (ω ⊗ₕ ω')).mulI = ⊤)

include hsT hcT

theorem orbitSpan_le_domain :
    orbitSpan M N ω ω' ≤ (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have h := orbit_mem_domain (vnTensor M N) (ω ⊗ₕ ω') hsT hcT (opTensor_mem_vnTensor M N hx hy)
  rwa [opTensor_apply] at h

/-- On the orbit of `ξ`, `Δ_ξ^{1/2} (z ξ) = J_ξ (z* ξ)` — this is `S_ξ = J_ξ Δ_ξ^{1/2}`
rearranged, and it is what makes the graph of the restriction the image of a *linear* map. -/
theorem D_orbit_eq (z : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) (hz : z ∈ vnTensor M N)
    (h : z (ω ⊗ₕ ω') ∈ (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain) :
    ((mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D ⟨z (ω ⊗ₕ ω'), h⟩ : HT ℋ 𝒦)
      = J (Ksub (vnTensor M N) (ω ⊗ₕ ω')) ((star z) (ω ⊗ₕ ω')) := by
  have hJ := J_D_orbit (vnTensor M N) (ω ⊗ₕ ω') hsT hcT hz h
  rw [← hJ, J_J _ hsT hcT]

/-- **`span (Mω ⊙ Nω')` is a core for `Δ_ξ^{1/2}`.**  This is the only place where von
Neumann algebra theory enters: `kaplansky_sa` (74IV) approximates a self-adjoint `z ∈ M ⊗̄ N`
ultrastrongly by self-adjoint elements of the norm closure of `M ⊙ N`, and testing against
the vector functional at `ξ` gives `zᵢ ξ → z ξ` **and** `zᵢ* ξ → z* ξ` at once. -/
theorem orbitSpan_hasCore_tensor :
    (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.HasCore (orbitSpan M N ω ω') := by
  classical
  set K := Ksub (vnTensor M N) (ω ⊗ₕ ω') with hK
  set DD := (mp K hsT hcT).D with hDD
  set S := orbitSpan M N ω ω' with hS
  have hSle : S ≤ DD.domain := orbitSpan_le_domain M N ω ω' hsT hcT
  have hDclosed : DD.IsClosed := (mp K hsT hcT).isClosed
  rw [hasCore_iff_closure_graph hDclosed hSle]
  set Gcl : Submodule ℂ (HT ℋ 𝒦 × HT ℋ 𝒦) := (DD.domRestrict S).graph.topologicalClosure with hGcl
  have hGcoe : (Gcl : Set (HT ℋ 𝒦 × HT ℋ 𝒦))
      = closure ((DD.domRestrict S).graph : Set (HT ℋ 𝒦 × HT ℋ 𝒦)) :=
    Submodule.topologicalClosure_coe _
  have hGclosed : IsClosed (Gcl : Set (HT ℋ 𝒦 × HT ℋ 𝒦)) := by
    rw [hGcoe]; exact isClosed_closure
  -- the linear map `z ↦ (z ξ, J_ξ (z* ξ))`
  set Φ : (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦) → (HT ℋ 𝒦 × HT ℋ 𝒦) :=
    fun z => (z (ω ⊗ₕ ω'), J K ((star z) (ω ⊗ₕ ω'))) with hΦ
  have hΦ1 : Continuous fun z : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦 => z (ω ⊗ₕ ω') :=
    (ContinuousLinearMap.apply ℂ (HT ℋ 𝒦) (ω ⊗ₕ ω')).continuous
  have hΦcont : Continuous Φ :=
    hΦ1.prodMk ((J K).continuous.comp (hΦ1.comp continuous_star))
  -- `Φ` lands in the graph of the restriction on `M ⊙ N`
  have hΦspan : ∀ s ∈ spatialSpan M N, Φ s ∈ (DD.domRestrict S).graph := by
    intro s hs
    have hsT' : s ∈ vnTensor M N := spatialSpan_le_vnTensor M N hs
    have hs' : s ∈ Submodule.span ℂ {x : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦 |
        ∃ a ∈ M, ∃ b ∈ N, x = opTensor a b} := hs
    have hmemS : s (ω ⊗ₕ ω') ∈ S := by
      refine Submodule.span_induction (p := fun w _ => w (ω ⊗ₕ ω') ∈ S) ?_ ?_ ?_ ?_ hs'
      · rintro _ ⟨x, hx, y, hy, rfl⟩
        rw [opTensor_apply]
        exact mem_orbitSpan_of_gen M N ω ω' hx hy
      · simp
      · intro u v _ _ hu hv
        simp only [add_apply]
        exact Submodule.add_mem _ hu hv
      · intro c u _ hu
        simp only [smul_apply]
        exact Submodule.smul_mem _ _ hu
    have hmemD : s (ω ⊗ₕ ω') ∈ DD.domain := hSle hmemS
    refine (LinearPMap.mem_graph_iff' _).2 ⟨⟨s (ω ⊗ₕ ω'), ⟨hmemS, hmemD⟩⟩, ?_⟩
    refine Prod.ext rfl ?_
    show ((DD.domRestrict S) ⟨s (ω ⊗ₕ ω'), ⟨hmemS, hmemD⟩⟩ : HT ℋ 𝒦)
      = J K ((star s) (ω ⊗ₕ ω'))
    have hval : (DD.domRestrict S) ⟨s (ω ⊗ₕ ω'), ⟨hmemS, hmemD⟩⟩
        = DD ⟨s (ω ⊗ₕ ω'), hmemD⟩ := LinearPMap.domRestrict_apply rfl
    rw [hval]
    exact D_orbit_eq M N ω ω' hsT hcT s hsT' hmemD
  -- and hence on its norm closure
  have hnormcl : ∀ s ∈ StarSubalgebra.topologicalClosure (spatialSpan M N), Φ s ∈ Gcl := by
    intro s hs
    have hsub : (spatialSpan M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦))
        ⊆ {z : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦 | Φ z ∈ Gcl} := by
      intro z hz
      exact Submodule.le_topologicalClosure _ (hΦspan z hz)
    have hcl : IsClosed {z : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦 | Φ z ∈ Gcl} := hGclosed.preimage hΦcont
    have hmem : s ∈ closure (spatialSpan M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) := by
      rw [← StarSubalgebra.topologicalClosure_coe]
      exact hs
    exact hcl.closure_subset_iff.2 hsub hmem
  -- Kaplansky: every self-adjoint `z ∈ M ⊗̄ N` is reached
  have hkap : ∀ z ∈ vnTensor M N, IsSelfAdjoint z → Φ z ∈ Gcl := by
    intro z hz hzsa
    have hSbclosed : IsClosed ((StarSubalgebra.topologicalClosure (spatialSpan M N) :
        StarSubalgebra ℂ (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) := by
      rw [StarSubalgebra.topologicalClosure_coe]; exact isClosed_closure
    have hz0 : z ∈ (vnTensor M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) := hz
    rw [vnTensor, ← (double_commutant (spatialSpan M N)).2.2,
      (double_commutant (spatialSpan M N)).1] at hz0
    have hzus : z ∈ @closure _ (ultrastrong (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦))
        ((StarSubalgebra.topologicalClosure (spatialSpan M N) :
          StarSubalgebra ℂ (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) := by
      have hsub : (spatialSpan M N : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦))
          ⊆ ((StarSubalgebra.topologicalClosure (spatialSpan M N) :
            StarSubalgebra ℂ (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) : Set (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) := by
        rw [StarSubalgebra.topologicalClosure_coe]
        exact subset_closure
      exact (@closure_mono _ (ultrastrong (HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) _ _ hsub) hz0
    obtain ⟨ι, l, hl, f, hf, hlim⟩ :=
      kaplansky_sa (StarSubalgebra.topologicalClosure (spatialSpan M N)) hSbclosed z hzus hzsa
    have : l.NeBot := hl
    have hvec : Filter.Tendsto (fun i => f i (ω ⊗ₕ ω')) l (nhds (z (ω ⊗ₕ ω'))) := by
      have hus := (usTendsto_iff f l z).1 hlim (vectorNP (ω ⊗ₕ ω'))
      simp only [omegaNorm_vectorNP] at hus
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simpa only [sub_apply] using hus
    have hΦf : ∀ i, Φ (f i) = ((f i) (ω ⊗ₕ ω'), J K ((f i) (ω ⊗ₕ ω'))) := by
      intro i
      simp only [hΦ, (hf i).2.2.star_eq]
    have hΦz : Φ z = (z (ω ⊗ₕ ω'), J K (z (ω ⊗ₕ ω'))) := by
      simp only [hΦ, hzsa.star_eq]
    have hconv : Filter.Tendsto (fun i => Φ (f i)) l (nhds (Φ z)) := by
      rw [hΦz]
      simp only [hΦf]
      exact hvec.prodMk_nhds (((J K).continuous.tendsto _).comp hvec)
    have hmem : Φ z ∈ closure (Gcl : Set (HT ℋ 𝒦 × HT ℋ 𝒦)) :=
      mem_closure_of_tendsto hconv (Filter.Eventually.of_forall
        fun i => hnormcl (f i) (hf i).1)
    rwa [hGclosed.closure_eq] at hmem
  -- and hence every `z ∈ M ⊗̄ N`, by splitting into self-adjoint parts
  have hgen : ∀ z ∈ vnTensor M N, Φ z ∈ Gcl := by
    intro z hz
    obtain ⟨h, hh, k, hk, hhs, hks, rfl⟩ := exists_sa_decomp (vnTensor M N) z hz
    have e1 := hkap h hh hhs
    have e2 := hkap k hk hks
    have hsplit : Φ (h + I • k) = Φ h + I • Φ k := by
      have hst : star (h + I • k) = h - I • k := by
        rw [star_add, star_smul, hhs.star_eq, hks.star_eq, Complex.star_def, Complex.conj_I,
          neg_smul, ← sub_eq_add_neg]
      refine Prod.ext ?_ ?_
      · show (h + I • k) (ω ⊗ₕ ω') = h (ω ⊗ₕ ω') + I • (k (ω ⊗ₕ ω'))
        rw [add_apply, smul_apply]
      · show J K ((star (h + I • k)) (ω ⊗ₕ ω'))
          = J K ((star h) (ω ⊗ₕ ω')) + I • J K ((star k) (ω ⊗ₕ ω'))
        rw [hst, hhs.star_eq, hks.star_eq, sub_apply,
          smul_apply, map_sub, J_smul K hsT hcT, Complex.conj_I,
          neg_smul, sub_neg_eq_add]
    rw [hsplit]
    exact Submodule.add_mem _ e1 (Submodule.smul_mem _ _ e2)
  -- conclude
  refine Set.Subset.antisymm ?_ ?_
  · calc closure ((DD.domRestrict S).graph : Set (HT ℋ 𝒦 × HT ℋ 𝒦))
        ⊆ closure ((DD.graph : Submodule ℂ (HT ℋ 𝒦 × HT ℋ 𝒦)) : Set (HT ℋ 𝒦 × HT ℋ 𝒦)) :=
          closure_mono (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le)
      _ = _ := hDclosed.closure_eq
  · have horb := orbit_hasCore (vnTensor M N) (ω ⊗ₕ ω') hsT hcT
    have horbgr := (hasCore_iff_closure_graph hDclosed horb.le_domain).1 horb
    rw [← horbgr, ← hGcoe]
    refine closure_minimal ?_ hGclosed
    rintro q hq
    obtain ⟨w, hw⟩ := (LinearPMap.mem_graph_iff' _).1 hq
    obtain ⟨z, hz, hzeq⟩ := w.2.1
    have hwD : (w : HT ℋ 𝒦) ∈ DD.domain := w.2.2
    have hzd : z (ω ⊗ₕ ω') ∈ DD.domain := by rw [← hzeq]; exact hwD
    have h2 : ((DD.domRestrict (orbitSub (vnTensor M N) (ω ⊗ₕ ω'))) w : HT ℋ 𝒦)
        = J K ((star z) (ω ⊗ₕ ω')) := by
      have hval : (DD.domRestrict (orbitSub (vnTensor M N) (ω ⊗ₕ ω'))) w
          = DD ⟨(w : HT ℋ 𝒦), hwD⟩ := LinearPMap.domRestrict_apply rfl
      rw [hval]
      have hcast : (⟨(w : HT ℋ 𝒦), hwD⟩ : DD.domain) = ⟨z (ω ⊗ₕ ω'), hzd⟩ :=
        Subtype.ext hzeq
      rw [hcast]
      exact D_orbit_eq M N ω ω' hsT hcT z hz hzd
    have hqval : q = Φ z := by
      have hΦz' : Φ z = (z (ω ⊗ₕ ω'), J K ((star z) (ω ⊗ₕ ω'))) := rfl
      rw [← hw, hΦz']
      exact Prod.ext hzeq h2
    rw [hqval]
    exact hgen z hz

end Tens

/-! ## Part 5: the factorisation -/

section Full

variable (hsM : Ksub M ω ⊓ (Ksub M ω).mulI = ⊥) (hcM : Ksub M ω ⊔ (Ksub M ω).mulI = ⊤)
variable (hsN : Ksub N ω' ⊓ (Ksub N ω').mulI = ⊥) (hcN : Ksub N ω' ⊔ (Ksub N ω').mulI = ⊤)
variable (hsT : Ksub (vnTensor M N) (ω ⊗ₕ ω') ⊓ (Ksub (vnTensor M N) (ω ⊗ₕ ω')).mulI = ⊥)
variable (hcT : Ksub (vnTensor M N) (ω ⊗ₕ ω') ⊔ (Ksub (vnTensor M N) (ω ⊗ₕ ω')).mulI = ⊤)

include hsM hcM hsN hcN hsT hcT

/-- **The tensor factorisation of the modular data.**  With `ξ = ω ⊗ ω'`:

* `J_ξ (ζ ⊗ ζ') = J_ω ζ ⊗ J_{ω'} ζ'`, and
* `Δ_ξ^{1/2} = D_{c̃,d̃}` for `c = a_ω ⊗ a_{ω'}`, `d = b_ω ⊗ b_{ω'}` — i.e. `Δ_ξ^{1/2}` is
  the closure of `Δ_ω^{1/2} ⊙ Δ_{ω'}^{1/2}`, exhibited explicitly by the normalisation
  lemma.

The proof compares `Δ_ξ^{1/2}` with `W · D_{c̃,d̃}` on the common core `span (Mω ⊙ Nω')` and
applies Rieffel–van Daele polar rigidity (`Modular.lean`'s Lemma D). -/
theorem tensor_factorisation :
    (∀ (ζ : ℋ) (ζ' : 𝒦), J (Ksub (vnTensor M N) (ω ⊗ₕ ω')) (ζ ⊗ₕ ζ')
        = J (Ksub M ω) ζ ⊗ₕ J (Ksub N ω') ζ')
      ∧ normFst (opTensor (a (Ksub M ω)) (a (Ksub N ω')))
            (opTensor (b (Ksub M ω)) (b (Ksub N ω')))
          = a (Ksub (vnTensor M N) (ω ⊗ₕ ω'))
      ∧ normSnd (opTensor (a (Ksub M ω)) (a (Ksub N ω')))
            (opTensor (b (Ksub M ω)) (b (Ksub N ω')))
          = b (Ksub (vnTensor M N) (ω ⊗ₕ ω')) := by
  classical
  obtain ⟨W, hWap, hWu⟩ := exists_conjTensor (J (Ksub M ω)) (J (Ksub N ω'))
    (J (Ksub (vnTensor M N) (ω ⊗ₕ ω')))
    (J_smul (Ksub M ω) hsM hcM) (J_smul (Ksub N ω') hsN hcN)
    (J_smul (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT)
    (J_inner (Ksub M ω) hsM hcM) (J_inner (Ksub N ω') hsN hcN)
    (J_inner (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT)
    (J_norm (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT)
    (J_J (Ksub M ω) hsM hcM) (J_J (Ksub N ω') hsN hcN)
    (J_J (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT)
  have hW1 : star W * W = 1 := Unitary.star_mul_self_of_mem hWu
  have hpair := isCommutingPair_ab M N ω ω' hsM hcM hsN hcN
  have hcore₁ := orbitSpan_hasCore_comm M N ω ω' hsM hcM hsN hcN
  have hcore₂ := orbitSpan_hasCore_tensor M N ω ω' hsT hcT
  have hclosed₁ : hpair.isModularPair.D.IsClosed := hpair.isModularPair.isClosed
  have hclosed₂ : (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.IsClosed :=
    (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).isClosed
  -- **Agreement on the generators of the common core.**
  have hgen : ∀ (x : ℋ →L[ℂ] ℋ), x ∈ M → ∀ (y : 𝒦 →L[ℂ] 𝒦), y ∈ N →
      ∀ (h1 : x ω ⊗ₕ y ω' ∈ hpair.isModularPair.D.domain)
        (h2 : x ω ⊗ₕ y ω' ∈ (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain),
        ((mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D ⟨x ω ⊗ₕ y ω', h2⟩ : HT ℋ 𝒦)
          = W (hpair.isModularPair.D ⟨x ω ⊗ₕ y ω', h1⟩) := by
    intro x hx y hy h1 h2
    obtain ⟨u, hu⟩ : ∃ u : ℋ, a (Ksub M ω) u = x ω := orbit_mem_domain M ω hsM hcM hx
    obtain ⟨v, hv⟩ : ∃ v : 𝒦, a (Ksub N ω') v = y ω' := orbit_mem_domain N ω' hsN hcN hy
    -- the left-hand side, via `S_ξ = J_ξ Δ_ξ^{1/2}` on the orbit
    have hxyξ : (opTensor x y) (ω ⊗ₕ ω') = x ω ⊗ₕ y ω' := opTensor_apply x y ω ω'
    have h2' : (opTensor x y) (ω ⊗ₕ ω') ∈
        (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain := by rw [hxyξ]; exact h2
    have hlhs : ((mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D ⟨x ω ⊗ₕ y ω', h2⟩ : HT ℋ 𝒦)
        = J (Ksub (vnTensor M N) (ω ⊗ₕ ω')) ((star x) ω ⊗ₕ (star y) ω') := by
      have hcast : (⟨x ω ⊗ₕ y ω', h2⟩ :
          (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain)
          = ⟨(opTensor x y) (ω ⊗ₕ ω'), h2'⟩ := Subtype.ext hxyξ.symm
      rw [hcast, D_orbit_eq M N ω ω' hsT hcT (opTensor x y)
        (opTensor_mem_vnTensor M N hx hy) h2', opTensor_star, opTensor_apply]
    -- the right-hand side, via `S_ω = J_ω Δ_ω^{1/2}` in each factor
    have hbu : J (Ksub M ω) (b (Ksub M ω) u) = (star x) ω := by
      have hmem : x ω ∈ (mp (Ksub M ω) hsM hcM).D.domain := orbit_mem_domain M ω hsM hcM hx
      have hval : (mp (Ksub M ω) hsM hcM).D ⟨x ω, hmem⟩ = b (Ksub M ω) u :=
        (mp (Ksub M ω) hsM hcM).D_apply' _ u hu
      rw [← hval]
      exact J_D_orbit M ω hsM hcM hx hmem
    have hbv : J (Ksub N ω') (b (Ksub N ω') v) = (star y) ω' := by
      have hmem : y ω' ∈ (mp (Ksub N ω') hsN hcN).D.domain := orbit_mem_domain N ω' hsN hcN hy
      have hval : (mp (Ksub N ω') hsN hcN).D ⟨y ω', hmem⟩ = b (Ksub N ω') v :=
        (mp (Ksub N ω') hsN hcN).D_apply' _ v hv
      rw [← hval]
      exact J_D_orbit N ω' hsN hcN hy hmem
    have hcu : opTensor (a (Ksub M ω)) (a (Ksub N ω')) (u ⊗ₕ v) = x ω ⊗ₕ y ω' := by
      rw [opTensor_apply, hu, hv]
    have h1' : opTensor (a (Ksub M ω)) (a (Ksub N ω')) (u ⊗ₕ v)
        ∈ hpair.isModularPair.D.domain := hpair.mem_domain (u ⊗ₕ v)
    have hrhs : (hpair.isModularPair.D ⟨x ω ⊗ₕ y ω', h1⟩ : HT ℋ 𝒦)
        = b (Ksub M ω) u ⊗ₕ b (Ksub N ω') v := by
      have hcast : (⟨x ω ⊗ₕ y ω', h1⟩ : hpair.isModularPair.D.domain)
          = ⟨opTensor (a (Ksub M ω)) (a (Ksub N ω')) (u ⊗ₕ v), h1'⟩ := Subtype.ext hcu.symm
      rw [hcast, hpair.D_apply (u ⊗ₕ v), opTensor_apply]
    rw [hlhs, hrhs, hWap, hbu, hbv]
  -- **Agreement on the whole core**, by linearity.
  have hagree : ∀ t ∈ orbitSpan M N ω ω',
      ∀ (h1 : t ∈ hpair.isModularPair.D.domain)
        (h2 : t ∈ (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain),
        ((mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D ⟨t, h2⟩ : HT ℋ 𝒦)
          = W (hpair.isModularPair.D ⟨t, h1⟩) := by
    have key : ∀ t ∈ orbitSpan M N ω ω',
        ∃ (h1 : t ∈ hpair.isModularPair.D.domain)
          (h2 : t ∈ (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain),
          ((mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D ⟨t, h2⟩ : HT ℋ 𝒦)
            = W (hpair.isModularPair.D ⟨t, h1⟩) := by
      intro t ht
      refine Submodule.span_induction (p := fun w _ =>
        ∃ (h1 : w ∈ hpair.isModularPair.D.domain)
          (h2 : w ∈ (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain),
          ((mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D ⟨w, h2⟩ : HT ℋ 𝒦)
            = W (hpair.isModularPair.D ⟨w, h1⟩)) ?_ ?_ ?_ ?_ ht
      · rintro _ ⟨x, hx, y, hy, rfl⟩
        obtain ⟨u, hu⟩ : ∃ u : ℋ, a (Ksub M ω) u = x ω := orbit_mem_domain M ω hsM hcM hx
        obtain ⟨v, hv⟩ : ∃ v : 𝒦, a (Ksub N ω') v = y ω' := orbit_mem_domain N ω' hsN hcN hy
        have h1 : x ω ⊗ₕ y ω' ∈ hpair.isModularPair.D.domain := by
          have := hpair.mem_domain (u ⊗ₕ v)
          rwa [opTensor_apply, hu, hv] at this
        have h2 : x ω ⊗ₕ y ω' ∈
            (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain :=
          orbitSpan_le_domain M N ω ω' hsT hcT (mem_orbitSpan_of_gen M N ω ω' hx hy)
        exact ⟨h1, h2, hgen x hx y hy h1 h2⟩
      · refine ⟨Submodule.zero_mem _, Submodule.zero_mem _, ?_⟩
        have e1 : (⟨(0 : HT ℋ 𝒦), Submodule.zero_mem _⟩ :
            (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain) = 0 := rfl
        have e2 : (⟨(0 : HT ℋ 𝒦), Submodule.zero_mem _⟩ :
            hpair.isModularPair.D.domain) = 0 := rfl
        rw [e1, e2, LinearPMap.map_zero, LinearPMap.map_zero, map_zero]
      · rintro t t' - - ⟨p1, p2, pe⟩ ⟨q1, q2, qe⟩
        refine ⟨Submodule.add_mem _ p1 q1, Submodule.add_mem _ p2 q2, ?_⟩
        have e1 : (⟨t + t', Submodule.add_mem _ p2 q2⟩ :
              (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain)
            = ⟨t, p2⟩ + ⟨t', q2⟩ := rfl
        have e2 : (⟨t + t', Submodule.add_mem _ p1 q1⟩ : hpair.isModularPair.D.domain)
            = ⟨t, p1⟩ + ⟨t', q1⟩ := rfl
        rw [e1, e2, LinearPMap.map_add, LinearPMap.map_add, map_add, pe, qe]
      · rintro c t - ⟨p1, p2, pe⟩
        refine ⟨Submodule.smul_mem _ _ p1, Submodule.smul_mem _ _ p2, ?_⟩
        have e1 : (⟨c • t, Submodule.smul_mem _ c p2⟩ :
              (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain) = c • ⟨t, p2⟩ := rfl
        have e2 : (⟨c • t, Submodule.smul_mem _ c p1⟩ : hpair.isModularPair.D.domain)
            = c • ⟨t, p1⟩ := rfl
        rw [e1, e2, LinearPMap.map_smul, LinearPMap.map_smul, map_smul, pe]
    intro t ht h1 h2
    obtain ⟨h1', h2', he⟩ := key t ht
    exact he
  -- **The two graph inclusions.**
  have hle₂ : orbitSpan M N ω ω' ≤ (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain :=
    orbitSpan_le_domain M N ω ω' hsT hcT
  have hgm₁ := graph_map_of_hasCore hclosed₁ hclosed₂ hcore₁ hle₂
    (V := W) (fun ζ hζ h1 h2 => hagree ζ hζ h1 h2)
  have hgm₂ := graph_map_of_hasCore hclosed₂ hclosed₁ hcore₂ hcore₁.le_domain
    (V := star W) (fun ζ hζ h2 h1 => by
      rw [hagree ζ hζ h1 h2]
      show (hpair.isModularPair.D ⟨ζ, h1⟩ : HT ℋ 𝒦)
        = (star W) (W (hpair.isModularPair.D ⟨ζ, h1⟩))
      have : (star W) (W (hpair.isModularPair.D ⟨ζ, h1⟩))
          = ((star W * W : HT ℋ 𝒦 →L[ℂ] HT ℋ 𝒦)) (hpair.isModularPair.D ⟨ζ, h1⟩) := rfl
      rw [this, hW1]
      rfl)
  -- **Domain equality and the pointwise identity.**
  have hdom : (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain
      = hpair.isModularPair.D.domain := by
    refine le_antisymm (fun t ht => ?_) (fun t ht => ?_)
    · obtain ⟨h1, -⟩ := domain_mem_of_graph_map hgm₂ ⟨t, ht⟩
      exact h1
    · obtain ⟨h2, -⟩ := domain_mem_of_graph_map hgm₁ ⟨t, ht⟩
      exact h2
  have hap : ∀ (x : (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain)
      (y : hpair.isModularPair.D.domain), (x : HT ℋ 𝒦) = (y : HT ℋ 𝒦) →
      ((mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D x : HT ℋ 𝒦)
        = W (hpair.isModularPair.D y) := by
    intro x y hxy
    obtain ⟨h2, he⟩ := domain_mem_of_graph_map hgm₁ y
    have hcast : x = ⟨(y : HT ℋ 𝒦), h2⟩ := Subtype.ext hxy
    rw [hcast, he]
  obtain ⟨hW, ha, hb⟩ := IsModularPair.eq_one_of_comp hpair.isModularPair
    (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT) hWu hdom hap
  refine ⟨?_, ha, hb⟩
  intro ζ ζ'
  have h0 := hWap (J (Ksub M ω) ζ) (J (Ksub N ω') ζ')
  rw [hW] at h0
  rw [J_J (Ksub M ω) hsM hcM, J_J (Ksub N ω') hsN hcN] at h0
  exact h0.symm


/-- `Δ_ξ^{1/2}` is defined on the range of `c = a_ω ⊗ a_{ω'}`. -/
theorem opTensor_mem_modularSqrt_domain (ζ : HT ℋ 𝒦) :
    opTensor (a (Ksub M ω)) (a (Ksub N ω')) ζ
      ∈ (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain := by
  obtain ⟨-, hfa, -⟩ := tensor_factorisation M N ω ω' hsM hcM hsN hcN hsT hcT
  refine ⟨sqrtSumSq (opTensor (a (Ksub M ω)) (a (Ksub N ω')))
    (opTensor (b (Ksub M ω)) (b (Ksub N ω'))) ζ, ?_⟩
  show a (Ksub (vnTensor M N) (ω ⊗ₕ ω')) (sqrtSumSq _ _ ζ)
    = opTensor (a (Ksub M ω)) (a (Ksub N ω')) ζ
  rw [← hfa]
  exact (isCommutingPair_ab M N ω ω' hsM hcM hsN hcN).normFst_apply ζ

/-- **`Δ_ξ^{1/2} = closure (Δ_ω^{1/2} ⊙ Δ_{ω'}^{1/2})`**, in the concrete form supplied by the
normalisation lemma: on the range of `a_ω ⊗ a_{ω'}` the modular operator of `ξ` is
`b_ω ⊗ b_{ω'}`. -/
theorem modularSqrt_opTensor (ζ : HT ℋ 𝒦)
    (h : opTensor (a (Ksub M ω)) (a (Ksub N ω')) ζ
      ∈ (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain) :
    ((mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D
        ⟨opTensor (a (Ksub M ω)) (a (Ksub N ω')) ζ, h⟩ : HT ℋ 𝒦)
      = opTensor (b (Ksub M ω)) (b (Ksub N ω')) ζ := by
  obtain ⟨-, hfa, hfb⟩ := tensor_factorisation M N ω ω' hsM hcM hsN hcN hsT hcT
  have hp := isCommutingPair_ab M N ω ω' hsM hcM hsN hcN
  have hfst : a (Ksub (vnTensor M N) (ω ⊗ₕ ω'))
      (sqrtSumSq (opTensor (a (Ksub M ω)) (a (Ksub N ω')))
        (opTensor (b (Ksub M ω)) (b (Ksub N ω'))) ζ)
      = opTensor (a (Ksub M ω)) (a (Ksub N ω')) ζ := by
    rw [← hfa]; exact hp.normFst_apply ζ
  rw [(mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D_apply' _ _ hfst, ← hfb]
  exact hp.normSnd_apply ζ

/-- The same on elementary tensors: `Δ_ξ^{1/2} (a_ω ζ ⊗ a_{ω'} ζ') = b_ω ζ ⊗ b_{ω'} ζ'`. -/
theorem modularSqrt_htmul (ζ : ℋ) (ζ' : 𝒦)
    (h : a (Ksub M ω) ζ ⊗ₕ a (Ksub N ω') ζ'
      ∈ (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain) :
    ((mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D
        ⟨a (Ksub M ω) ζ ⊗ₕ a (Ksub N ω') ζ', h⟩ : HT ℋ 𝒦)
      = b (Ksub M ω) ζ ⊗ₕ b (Ksub N ω') ζ' := by
  have hζ : opTensor (a (Ksub M ω)) (a (Ksub N ω')) (ζ ⊗ₕ ζ')
      = a (Ksub M ω) ζ ⊗ₕ a (Ksub N ω') ζ' := opTensor_apply _ _ ζ ζ'
  have hmem : opTensor (a (Ksub M ω)) (a (Ksub N ω')) (ζ ⊗ₕ ζ')
      ∈ (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain := by rw [hζ]; exact h
  have hcast : (⟨a (Ksub M ω) ζ ⊗ₕ a (Ksub N ω') ζ', h⟩ :
      (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain)
      = ⟨opTensor (a (Ksub M ω)) (a (Ksub N ω')) (ζ ⊗ₕ ζ'), hmem⟩ := Subtype.ext hζ.symm
  rw [hcast, modularSqrt_opTensor M N ω ω' hsM hcM hsN hcN hsT hcT, opTensor_apply]

/-- **The factorisation on the orbit**: for `x ∈ M` and `y ∈ N`,
`Δ_ξ^{1/2} (xω ⊗ yω') = Δ_ω^{1/2}(xω) ⊗ Δ_{ω'}^{1/2}(yω')`. -/
theorem modularSqrt_orbit {x : ℋ →L[ℂ] ℋ} {y : 𝒦 →L[ℂ] 𝒦}
    (h : x ω ⊗ₕ y ω' ∈ (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain)
    (hxm : x ω ∈ (mp (Ksub M ω) hsM hcM).D.domain)
    (hym : y ω' ∈ (mp (Ksub N ω') hsN hcN).D.domain) :
    ((mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D ⟨x ω ⊗ₕ y ω', h⟩ : HT ℋ 𝒦)
      = ((mp (Ksub M ω) hsM hcM).D ⟨x ω, hxm⟩ : ℋ)
          ⊗ₕ ((mp (Ksub N ω') hsN hcN).D ⟨y ω', hym⟩ : 𝒦) := by
  obtain ⟨u, hu⟩ : ∃ u : ℋ, a (Ksub M ω) u = x ω := id hxm
  obtain ⟨v, hv⟩ : ∃ v : 𝒦, a (Ksub N ω') v = y ω' := id hym
  have hval1 : ((mp (Ksub M ω) hsM hcM).D ⟨x ω, hxm⟩ : ℋ) = b (Ksub M ω) u :=
    (mp (Ksub M ω) hsM hcM).D_apply' _ u hu
  have hval2 : ((mp (Ksub N ω') hsN hcN).D ⟨y ω', hym⟩ : 𝒦) = b (Ksub N ω') v :=
    (mp (Ksub N ω') hsN hcN).D_apply' _ v hv
  have hxy : a (Ksub M ω) u ⊗ₕ a (Ksub N ω') v = x ω ⊗ₕ y ω' := by rw [hu, hv]
  have hmem2 : a (Ksub M ω) u ⊗ₕ a (Ksub N ω') v
      ∈ (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain := hxy ▸ h
  have hcast : (⟨x ω ⊗ₕ y ω', h⟩ :
      (mp (Ksub (vnTensor M N) (ω ⊗ₕ ω')) hsT hcT).D.domain)
      = ⟨a (Ksub M ω) u ⊗ₕ a (Ksub N ω') v, hmem2⟩ := Subtype.ext hxy.symm
  rw [hcast, modularSqrt_htmul M N ω ω' hsM hcM hsN hcN hsT hcT, hval1, hval2]

end Full

/-! ## Part 6: the package

The hypotheses in their original form — `ω` and `ω'` cyclic and separating, `M'' = M`,
`N'' = N` — with the standardness of `𝒦_ξ` derived rather than assumed. -/

section Package

variable (hcycM : IsCyclicVector M ω) (hsepM : IsSeparatingVector M ω)
  (hMbi : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
    = (M : Set (ℋ →L[ℂ] ℋ)))
variable (hcycN : IsCyclicVector N ω') (hsepN : IsSeparatingVector N ω')
  (hNbi : commutant (𝒦 →L[ℂ] 𝒦) (commutant (𝒦 →L[ℂ] 𝒦) (N : Set (𝒦 →L[ℂ] 𝒦)))
    = (N : Set (𝒦 →L[ℂ] 𝒦)))

include hcycM hcycN in
/-- **`ξ = ω ⊗ ω'` is cyclic for `M ⊗̄ N`.** -/
theorem isCyclicVector_vnTensor : IsCyclicVector (vnTensor M N) (ω ⊗ₕ ω') :=
  isCyclicVector_htmul M N ω ω' hcycM hcycN

include hsepM hMbi hsepN hNbi in
/-- **`ξ = ω ⊗ ω'` is separating for `M ⊗̄ N`** — via the easy inclusion only. -/
theorem isSeparatingVector_vnTensor : IsSeparatingVector (vnTensor M N) (ω ⊗ₕ ω') :=
  isSeparatingVector_htmul M N ω ω' (dense_commutant_orbit M ω hsepM hMbi)
    (dense_commutant_orbit N ω' hsepN hNbi)

include hcycM hsepM hMbi hcycN hsepN hNbi in
/-- **RvD Prop. 4.1 for `M ⊗̄ N`**: `𝒦_ξ = closure ((M ⊗̄ N)_sa ξ)` is standard. -/
theorem isStandard_vnTensor :
    Ksub (vnTensor M N) (ω ⊗ₕ ω') ⊓ (Ksub (vnTensor M N) (ω ⊗ₕ ω')).mulI = ⊥
      ∧ Ksub (vnTensor M N) (ω ⊗ₕ ω') ⊔ (Ksub (vnTensor M N) (ω ⊗ₕ ω')).mulI = ⊤ :=
  isStandard (vnTensor M N) (ω ⊗ₕ ω')
    (isCyclicVector_vnTensor M N ω ω' hcycM hcycN)
    (isSeparatingVector_vnTensor M N ω ω' hsepM hMbi hsepN hNbi)
    (bicommutant_vnTensor M N)

include hcycM hsepM hMbi hcycN hsepN hNbi in
/-- **`J_ξ = J_ω ⊗ J_{ω'}`.**  The Tomita conjugation of `M ⊗̄ N` at `ω ⊗ ω'` is the tensor
product of the two Tomita conjugations — the statement `docs/COMMUTATION-THEOREM.md` §4 calls
"the step that decides it". -/
theorem modularConj_htmul (ζ : ℋ) (ζ' : 𝒦) :
    modularConj (vnTensor M N) (ω ⊗ₕ ω')
        (isCyclicVector_vnTensor M N ω ω' hcycM hcycN)
        (isSeparatingVector_vnTensor M N ω ω' hsepM hMbi hsepN hNbi)
        (bicommutant_vnTensor M N) (ζ ⊗ₕ ζ')
      = modularConj M ω hcycM hsepM hMbi ζ ⊗ₕ modularConj N ω' hcycN hsepN hNbi ζ' :=
  (tensor_factorisation M N ω ω'
    (isStandard M ω hcycM hsepM hMbi).1 (isStandard M ω hcycM hsepM hMbi).2
    (isStandard N ω' hcycN hsepN hNbi).1 (isStandard N ω' hcycN hsepN hNbi).2
    (isStandard_vnTensor M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi).1
    (isStandard_vnTensor M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi).2).1 ζ ζ'

include hcycM hsepM hMbi hcycN hsepN hNbi in
/-- **`span (Mω ⊙ Nω')` is a core for `Δ_ξ^{1/2}`.** -/
theorem modularSqrt_hasCore_orbitSpan :
    (modularSqrt (vnTensor M N) (ω ⊗ₕ ω')
        (isCyclicVector_vnTensor M N ω ω' hcycM hcycN)
        (isSeparatingVector_vnTensor M N ω ω' hsepM hMbi hsepN hNbi)
        (bicommutant_vnTensor M N)).HasCore (orbitSpan M N ω ω') :=
  orbitSpan_hasCore_tensor M N ω ω'
    (isStandard_vnTensor M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi).1
    (isStandard_vnTensor M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi).2

include hcycM hsepM hMbi hcycN hsepN hNbi in
/-- **`Δ_ξ^{1/2} = closure (Δ_ω^{1/2} ⊙ Δ_{ω'}^{1/2})`**, evaluated: on `ran a_ω ⊙ ran a_{ω'}`
the modular operator of `ξ` is `b_ω ⊗ b_{ω'}`.  Together with
`modularSqrt_hasCore_orbitSpan` and the explicit closure supplied by the normalisation lemma
this *is* the second half of the factorisation. -/
theorem modularSqrt_htmul_pkg (ζ : ℋ) (ζ' : 𝒦)
    (h : a (Ksub M ω) ζ ⊗ₕ a (Ksub N ω') ζ'
      ∈ (modularSqrt (vnTensor M N) (ω ⊗ₕ ω')
          (isCyclicVector_vnTensor M N ω ω' hcycM hcycN)
          (isSeparatingVector_vnTensor M N ω ω' hsepM hMbi hsepN hNbi)
          (bicommutant_vnTensor M N)).domain) :
    ((modularSqrt (vnTensor M N) (ω ⊗ₕ ω')
        (isCyclicVector_vnTensor M N ω ω' hcycM hcycN)
        (isSeparatingVector_vnTensor M N ω ω' hsepM hMbi hsepN hNbi)
        (bicommutant_vnTensor M N)) ⟨a (Ksub M ω) ζ ⊗ₕ a (Ksub N ω') ζ', h⟩ : HT ℋ 𝒦)
      = b (Ksub M ω) ζ ⊗ₕ b (Ksub N ω') ζ' :=
  modularSqrt_htmul M N ω ω'
    (isStandard M ω hcycM hsepM hMbi).1 (isStandard M ω hcycM hsepM hMbi).2
    (isStandard N ω' hcycN hsepN hNbi).1 (isStandard N ω' hcycN hsepN hNbi).2
    (isStandard_vnTensor M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi).1
    (isStandard_vnTensor M N ω ω' hcycM hsepM hMbi hcycN hsepN hNbi).2 ζ ζ' h

end Package

end Main

end Theses.RvD

