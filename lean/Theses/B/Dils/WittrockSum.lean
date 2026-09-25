/-
Thesis B companion to the note `wittrock-dil.tex`: Wittrock dilations are
closed under direct sums of the domain.  If each `hᵢ : 𝒳ᵢ ⊗ ℰᵢ → 𝒜` is a
Wittrock dilation of `φ ∘ κᵢ`, then `h = ∑ᵢ hᵢ ∘ (πᵢ ⊗ πᵢ)` is a Wittrock
dilation of `φ : ⊕ᵢ 𝒳ᵢ → 𝒜` (`isWittrockDilationOf_wsum`); so `φ` has a
Wittrock dilation as soon as every `φ ∘ κᵢ` has a non-zero one
(`exists_wittrockDilation_of_sum`).  The note does not contain this result.

The sum `h` converges ultraweakly by `exists_ncp_uwsum` (`WittrockSplit.lean`).
Direct sums are `lp 𝒳ᵢ ∞`, with the index type and all algebras in one
universe.  Mathlib's unital C*-structure on `lp` needs every summand
non-zero, the same binder the tree's **47IV** carries, so the `𝒳ᵢ` and `ℰᵢ`
are assumed `Nontrivial`.  For the `ℰᵢ` this excludes exactly the summands
with `φ ∘ κᵢ = 0`, whose Wittrock dilation is `{0}`.

Like the other Wittrock files this one has no thesis counterpart and
carries no DISP code.  Nothing in this file uses `sorry`.
-/
import Theses.B.Dils.WittrockSplit

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra TensorProduct ENNReal
open Filter Topology Theses Theses.A.VN Theses.A.Proc

noncomputable section

namespace Theses.B.Dils

universe u

theorem wncp_sum {B C : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C] {ι : Type*} (f : NCPMap B C)
    (s : Finset ι) (x : ι → B) : f (∑ i ∈ s, x i) = ∑ i ∈ s, f (x i) :=
  map_sum f.toCompletelyPositiveMap x s

private theorem vtmul_sum_left {X E : Type*}
    [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
    [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E] [VonNeumannAlgebra E]
    {ι : Type*} (s : Finset ι) (x : ι → X) (e : E) :
    (∑ i ∈ s, x i) ⊗ᵥ e = ∑ i ∈ s, x i ⊗ᵥ e :=
  LinearMap.map_sum₂ _ _ _ _

section DirectSum

variable {I : Type u} {Xs : I → Type u} {Es : I → Type u}
  [∀ i, CStarAlgebra (Xs i)] [∀ i, Nontrivial (Xs i)] [∀ i, PartialOrder (Xs i)]
  [∀ i, StarOrderedRing (Xs i)] [∀ i, VonNeumannAlgebra (Xs i)]
  [∀ i, CStarAlgebra (Es i)] [∀ i, Nontrivial (Es i)] [∀ i, PartialOrder (Es i)]
  [∀ i, StarOrderedRing (Es i)] [∀ i, VonNeumannAlgebra (Es i)]
  {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]

/-- The diagonal block `πᵢ ⊗ πᵢ : (⊕ⱼ 𝒳ⱼ) ⊗ (⊕ⱼ ℰⱼ) → 𝒳ᵢ ⊗ ℰᵢ` (**115II**). -/
def diagBlock (i : I) : NCPMap (VNT (lp Xs ∞) (lp Es ∞)) (VNT (Xs i) (Es i)) :=
  tmap (nmiuNCP (lpProjNMIU i)) (nmiuNCP (lpProjNMIU i))

theorem diagBlock_apply (i : I) (x : lp Xs ∞) (e : lp Es ∞) :
    diagBlock i (x ⊗ᵥ e) = (x : ∀ j, Xs j) i ⊗ᵥ (e : ∀ j, Es j) i := by
  rw [diagBlock, tmap_apply]; rfl

theorem diagBlock_one (i : I) : diagBlock (Xs := Xs) (Es := Es) i 1 = 1 :=
  (tensor_functorial _ _).2.2.1
    (by rw [nmiuNCP_apply]; exact map_one (lpProjNMIU i).toStarAlgHom)
    (by rw [nmiuNCP_apply]; exact map_one (lpProjNMIU i).toStarAlgHom)

/-- `h = ∑ᵢ hᵢ ∘ (πᵢ ⊗ πᵢ)` converges ultraweakly to an ncp-map
(`exists_ncp_uwsum`, **96III**): its partial sums at `1` are
`φ(∑_{i∈F} κᵢ(1)) ≤ φ(1)`. -/
theorem exists_wsum (φ : NCPMap (lp Xs ∞) A) (hs : ∀ i, NCPMap (VNT (Xs i) (Es i)) A)
    (hφ : ∀ i (x : Xs i), hs i (x ⊗ᵥ (1 : Es i)) = φ (lpKappa i x)) :
    ∃ h : NCPMap (VNT (lp Xs ∞) (lp Es ∞)) A,
      ∀ b, UWTendsto (fun F => ∑ i ∈ F, hs i (diagBlock i b)) atTop (h b) := by
  classical
  have hb : ∀ F : Finset I, ∑ i ∈ F, ncpComp (hs i) (diagBlock i) 1 ≤ φ 1 := by
    intro F
    have he : ∑ i ∈ F, ncpComp (hs i) (diagBlock i) 1 = φ (∑ i ∈ F, lpKappa i (1 : Xs i)) := by
      rw [wncp_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ncpComp_apply, diagBlock_one, ← (vnTensor (Xs i) (Es i)).isTensorProduct.miu.1]
      exact hφ i 1
    have hle : ∑ i ∈ F, lpKappa i (1 : Xs i) ≤ 1 := by
      rw [lp_infty_le_iff]
      intro k
      have h := lpKappa_sum_apply (1 : lp Xs ∞) F k
      simp only [lp.infty_coeFn_one, Pi.one_apply] at h
      rw [h]
      split_ifs
      · exact le_rfl
      · exact zero_le_one
    rw [he]
    exact OrderHomClass.mono φ.toCompletelyPositiveMap hle
  obtain ⟨L, hL⟩ := exists_ncp_uwsum (fun i => ncpComp (hs i) (diagBlock i)) (φ 1) hb
  exact ⟨L, fun b => (hL b).congr fun F =>
    Finset.sum_congr rfl fun i _ => ncpComp_apply (hs i) (diagBlock i) b⟩

/-- The ncp-map `h = ∑ᵢ hᵢ ∘ (πᵢ ⊗ πᵢ)`, by choice. -/
def wsum (φ : NCPMap (lp Xs ∞) A) (hs : ∀ i, NCPMap (VNT (Xs i) (Es i)) A)
    (hφ : ∀ i (x : Xs i), hs i (x ⊗ᵥ (1 : Es i)) = φ (lpKappa i x)) :
    NCPMap (VNT (lp Xs ∞) (lp Es ∞)) A :=
  (exists_wsum φ hs hφ).choose

theorem wsum_spec (φ : NCPMap (lp Xs ∞) A) (hs : ∀ i, NCPMap (VNT (Xs i) (Es i)) A)
    (hφ : ∀ i (x : Xs i), hs i (x ⊗ᵥ (1 : Es i)) = φ (lpKappa i x))
    (b : VNT (lp Xs ∞) (lp Es ∞)) :
    UWTendsto (fun F => ∑ i ∈ F, hs i (diagBlock i b)) atTop (wsum φ hs hφ b) :=
  (exists_wsum φ hs hφ).choose_spec b

/-- `h(κᵢ(x) ⊗ e) = hᵢ(x ⊗ πᵢ(e))`: only the `i`-th term survives. -/
theorem wsum_kappa (φ : NCPMap (lp Xs ∞) A) (hs : ∀ i, NCPMap (VNT (Xs i) (Es i)) A)
    (hφ : ∀ i (x : Xs i), hs i (x ⊗ᵥ (1 : Es i)) = φ (lpKappa i x))
    (i : I) (x : Xs i) (e : lp Es ∞) :
    wsum φ hs hφ (lpKappa i x ⊗ᵥ e) = hs i (x ⊗ᵥ (e : ∀ j, Es j) i) := by
  classical
  let _ : TopologicalSpace A := ultraweak A
  refine uwTendsto_unique (wsum_spec φ hs hφ _) ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop {i}] with F hF
  have hi : i ∈ F := hF (Finset.mem_singleton_self i)
  rw [Finset.sum_eq_single_of_mem i hi]
  · rw [diagBlock_apply, lpKappa_apply_self]
  · intro j _ hji
    rw [diagBlock_apply, lpKappa_apply_ne _ _ hji]
    change hs j ((vnTensor (Xs j) (Es j)).map 0 _) = 0
    rw [LinearMap.map_zero₂, wncp_zero]

/-- `h(x ⊗ 1) = φ(x)`: `h` dilates `φ`. -/
theorem wsum_one (φ : NCPMap (lp Xs ∞) A) (hs : ∀ i, NCPMap (VNT (Xs i) (Es i)) A)
    (hφ : ∀ i (x : Xs i), hs i (x ⊗ᵥ (1 : Es i)) = φ (lpKappa i x)) (x : lp Xs ∞) :
    wsum φ hs hφ (x ⊗ᵥ (1 : lp Es ∞)) = φ x := by
  let _ : TopologicalSpace A := ultraweak A
  let _ : TopologicalSpace (lp Xs ∞) := ultraweak _
  refine uwTendsto_unique (wsum_spec φ hs hφ _) ?_
  have h := ((wit_ncp_continuous φ).tendsto x).comp (uwTendsto_lpRestrict x)
  refine h.congr fun F => ?_
  simp only [Function.comp_apply, wncp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diagBlock_apply, lp.infty_coeFn_one, Pi.one_apply, hφ]

/-- If each `hᵢ : 𝒳ᵢ ⊗ ℰᵢ → 𝒜` is a Wittrock dilation of `φ ∘ κᵢ`, then
`h = ∑ᵢ hᵢ ∘ (πᵢ ⊗ πᵢ)` is a Wittrock dilation of `φ : ⊕ᵢ 𝒳ᵢ → 𝒜`.  The
mediating map is `τ = (τᵢ)ᵢ` of
**47IV**.  Uniqueness is argued without first showing that a competitor
`τ̃` is unital: `πᵢ ⊗ πᵢ` is applied to its triangle directly. -/
theorem isWittrockDilationOf_wsum (φ : NCPMap (lp Xs ∞) A)
    (hs : ∀ i, NCPMap (VNT (Xs i) (Es i)) A)
    (hW : ∀ i, IsWittrockDilationOf (fun x : Xs i => φ (lpKappa i x)) (Es i) (hs i)) :
    IsWittrockDilationOf φ (lp Es ∞) (wsum φ hs fun i => (hW i).1) := by
  classical
  set hφ : ∀ i (x : Xs i), hs i (x ⊗ᵥ (1 : Es i)) = φ (lpKappa i x) := fun i => (hW i).1
  set h := wsum φ hs hφ
  refine ⟨wsum_one φ hs hφ, fun E' _ _ _ _ h' hh' => ?_⟩
  -- `h'ᵢ = h' ∘ (κᵢ ⊗ id)`
  set h'i : ∀ i, NCPMap (VNT (Xs i) E') A := fun i =>
    ncpComp h' (tmap (lpKappaNCP i) (ncpId E'))
  have h'i_apply : ∀ i (x : Xs i) (e : E'), h'i i (x ⊗ᵥ e) = h' (lpKappa i x ⊗ᵥ e) :=
    fun i x e => by rw [ncpComp_apply, tmap_apply, lpKappaNCP_apply, ncpId_apply]
  have hh'i : ∀ i (x : Xs i), h'i i (x ⊗ᵥ (1 : E')) = φ (lpKappa i x) :=
    fun i x => by rw [h'i_apply, hh']
  choose τs hτs hτu using fun i => (hW i).2 E' (h'i i) (hh'i i)
  have hτs' := fun i => (isWittrockMediator_iff_tmap _ _ _).mp (hτs i)
  have hτ1 : ∀ i, τs i 1 = 1 := fun i => by
    refine one_vtmul_injective (X := Xs i) ?_
    have := (hτs' i).1 1
    rwa [tmap_apply, ncpId_apply] at this
  -- `τ = (τᵢ)ᵢ : ℰ' → ⊕ᵢ ℰᵢ` (**47IV**)
  obtain ⟨τsu, hτsu, -⟩ := vn_products_ncpsu Es
    (fun i => (⟨τs i, (hτ1 i).le⟩ : NCPSUMap E' (Es i)))
  set τ := τsu.toNCPMap
  have hτc : ∀ i e, ((τ e : lp Es ∞) : ∀ j, Es j) i = τs i e := hτsu
  have hτ_1 : τ 1 = 1 := by
    refine lp.ext (funext fun i => ?_)
    rw [hτc, hτ1, lp.infty_coeFn_one, Pi.one_apply]
  -- continuity of `x ↦ h'(x ⊗ e)`, for the normality step
  have hcont : ∀ e : E', @Continuous (lp Xs ∞) A (ultraweak _) (ultraweak A)
      fun x => h' (x ⊗ᵥ e) := fun e =>
    @Continuous.comp _ _ _ (ultraweak _) (ultraweak _) (ultraweak A) _ _
      (wit_ncp_continuous h') (continuous_ultraweak_vtmul_left e)
  refine ⟨τ, (isWittrockMediator_iff_tmap _ _ _).mpr ⟨fun x => ?_, fun z => ?_⟩, ?_⟩
  · rw [tmap_apply, ncpId_apply, hτ_1]
  · -- `h ∘ (id ⊗ τ) = h'` on elementary tensors, then by density
    have key : ncpComp h (tmap (ncpId (lp Xs ∞)) τ) = h' := by
      refine ncp_ext_vnt _ _ fun x e => ?_
      rw [ncpComp_apply, tmap_apply, ncpId_apply]
      let _ : TopologicalSpace A := ultraweak A
      let _ : TopologicalSpace (lp Xs ∞) := ultraweak _
      refine uwTendsto_unique (wsum_spec φ hs hφ _) ?_
      refine ((hcont e).tendsto x |>.comp (uwTendsto_lpRestrict x)).congr fun F => ?_
      simp only [Function.comp_apply]
      rw [vtmul_sum_left, wncp_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [diagBlock_apply, hτc, ← h'i_apply]
      have := (hτs' i).2 ((x : ∀ j, Xs j) i ⊗ᵥ e)
      rw [tmap_apply, ncpId_apply] at this
      exact this.symm
    rw [← key, ncpComp_apply]
  · -- uniqueness
    intro τ' hτ'
    obtain ⟨σ', hσ'e, hσ'1, hσ'h⟩ := hτ'
    have hcomp : ∀ i, ncpComp (nmiuNCP (lpProjNMIU i)) τ' = τs i := by
      intro i
      refine hτu i _ ((isWittrockMediator_iff_tmap _ _ _).mpr ⟨fun x => ?_, fun z => ?_⟩)
      · rw [tmap_apply, ncpId_apply, ncpComp_apply, nmiuNCP_apply, lpProjNMIU_apply]
        have := congrArg (diagBlock i) ((hσ'e (lpKappa i x) 1).symm.trans (hσ'1 _))
        rwa [diagBlock_apply, diagBlock_apply, lpKappa_apply_self, lp.infty_coeFn_one,
          Pi.one_apply] at this
      · have key : ncpComp (hs i) (tmap (ncpId (Xs i))
            (ncpComp (nmiuNCP (lpProjNMIU i)) τ')) = h'i i := by
          refine ncp_ext_vnt _ _ fun x e => ?_
          rw [ncpComp_apply, tmap_apply, ncpId_apply, ncpComp_apply, nmiuNCP_apply,
            lpProjNMIU_apply, h'i_apply, ← hσ'h, hσ'e, wsum_kappa]
        rw [← key, ncpComp_apply]
    refine DFunLike.ext _ _ fun e => lp.ext (funext fun i => ?_)
    rw [hτc, ← hcomp i, ncpComp_apply, nmiuNCP_apply, lpProjNMIU_apply]

end DirectSum

/-- `φ : ⊕ᵢ 𝒳ᵢ → 𝒜` has a Wittrock dilation provided every `φ ∘ κᵢ` has a
non-zero one (`isWittrockDilationOf_wsum`; the non-zero `ℰᵢ` are forced by
`lp`, see the file header). -/
theorem exists_wittrockDilation_of_sum {I : Type u} {Xs : I → Type u}
    [∀ i, CStarAlgebra (Xs i)] [∀ i, Nontrivial (Xs i)] [∀ i, PartialOrder (Xs i)]
    [∀ i, StarOrderedRing (Xs i)] [∀ i, VonNeumannAlgebra (Xs i)]
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]
    (φ : NCPMap (lp Xs ∞) A)
    (hW : ∀ i, ∃ (E : Type u) (_ : CStarAlgebra E) (_ : Nontrivial E) (_ : PartialOrder E)
      (_ : StarOrderedRing E) (_ : VonNeumannAlgebra E) (h : NCPMap (VNT (Xs i) E) A),
      IsWittrockDilationOf (fun x => φ (lpKappa i x)) E h) :
    ∃ (E : Type u) (_ : CStarAlgebra E) (_ : PartialOrder E) (_ : StarOrderedRing E)
      (_ : VonNeumannAlgebra E) (h : NCPMap (VNT (lp Xs ∞) E) A),
      IsWittrockDilationOf ⇑φ E h := by
  choose Es i1 i2 i3 i4 i5 hs hW using hW
  exact ⟨lp Es ∞, inferInstance, inferInstance, inferInstance, inferInstance, _,
    isWittrockDilationOf_wsum φ hs hW⟩

end Theses.B.Dils
