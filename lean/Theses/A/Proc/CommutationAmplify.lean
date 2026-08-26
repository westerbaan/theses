/-
Thesis A, chapter "Assorted Structure in W*_cpsu" (proc.tex): the **`ℂⁿ`
amplification** step of the reduction of the commutation theorem
`CT 𝒜 ℬ : (𝒜 ⊗̄ ℬ)^□ = 𝒜^□ ⊗̄ ℬ^□` (Takesaki I, Thm IV.5.9).

`A/Proc/CommutationReduction.lean` reduces `CT` for arbitrary pairs of
von Neumann subalgebras to pairs admitting a **finite jointly cyclic
family**.  This file carries that one step further, to pairs admitting a
single **cyclic vector**:

`CT_of_CT_cyclic`: *if `CT X Y` holds for every pair of von Neumann
algebras each of which has a cyclic vector, then `CT 𝒜 ℬ` holds for all
von Neumann subalgebras `𝒜 ⊆ B(ℋ)`, `ℬ ⊆ B(𝒦)`.*

## The three ingredients

1. **`opTensor_one_mem_of_mem_wstar`** — the normality of `a ↦ a ⊗ 1`,
   in the only form needed: a von Neumann subalgebra of `B(ℋ ⊗ 𝒦)` that
   contains `a ⊗ 1` for every `a` in a set `G` contains it for every
   `a ∈ W*(G)`.  No ultraweak continuity argument: by 88VI the set
   `{a | a ⊗ 1 ∈ 𝒲}` is `{a | ∀ u ∈ 𝒲^□, (a⊗1)u = u(a⊗1)}`, and `a ⊗ 1`
   commutes with `u` exactly when `a` commutes with all the **slices**
   `Q_y^* u Q_{y'}` of `u` (`opTensor_one_comm_iff`) — so the set is
   literally a commutant, hence a von Neumann subalgebra by 65III.
   Consequence: **`W*(G₁) ⊗̄ W*(G₂) = W*(G₁ ⊙ G₂)`**
   (`concreteTensor_wstar`), which is what makes a rearrangement of a
   tensor product checkable on elementary tensors alone.
2. **`CT_of_CT_ampLeft` / `CT_of_CT_amp`** — `CT` descends along an
   amplification: `CT (𝒜 ⊗̄ B(ℒ)) (ℬ ⊗̄ B(ℒ')) → CT 𝒜 ℬ` for
   `ℒ, ℒ' ≠ 0`.  The transport is the interchange unitary
   `(ℋ ⊗ ℒ) ⊗ 𝒦 ≅ (ℋ ⊗ 𝒦) ⊗ ℒ` (`htInterchange`, associator–flip–
   associator), plus `commutant_concreteTensor_top` twice and the
   injectivity of `a ↦ a ⊗ 1`.  Only *one* factor is amplified at a
   time; the two-factor form comes from `CT_comm`.  This keeps the
   rearrangement three-fold instead of the four-fold middle interchange.
3. **`hasCyclic_concreteTensor_top`** — if `ξ_1, …, ξ_n` are jointly
   cyclic for `𝒜 ⊆ B(ℋ)` then `∑ᵢ ξᵢ ⊗ δᵢ` is cyclic for `𝒜 ⊗̄ B(ℂⁿ)`:
   `(x ⊗ |δ_j⟩⟨δ_i|)(∑ₖ ξₖ ⊗ δₖ) = x ξ_i ⊗ δ_j`.

A by-product, and it removes a caveat: **`CT_iff_bicommutant`**,
`CT 𝒜 ℬ ↔ CT 𝒜^□□ ℬ^□□`.  It is immediate from ingredient 1
(`𝒜 ⊗̄ ℬ = 𝒜^□□ ⊗̄ ℬ^□□`, `concreteTensor_vnComm_vnComm`) and is exactly
what the header of `A/Proc/CommutationReduction.lean` records as missing
— it is why the hypothesis of `CT_of_CT_finCyclic` has to quantify over
arbitrary ∗-subalgebras, and it is now available.  (The brief for this
round expected it to need the right-handed amplification
`{1 ⊗ b}^□ = B(ℋ) ⊗̄ ℬ^□`; it does not.)

## The target is `cyclic`, not `cyclic and separating` — and that is not
## a shortfall of this file

The plan this round was written to execute said: amplify by `ℂⁿ`, get a
vector cyclic for `𝒜 ⊗̄ B(ℂⁿ)`, hence separating for `𝒜^□ ⊗ 1`, and let
`cyclic_and_separating_of_separating` finish — the only missing piece
being the tensor transport.  **That is wrong, and the amplification
cannot reach the cyclic-and-separating case.**  Two independent reasons:

* *Amplification never manufactures a separating vector.*  For
  `𝒜 = B(ℋ)` with `dim ℋ = ∞`, every nonzero vector is cyclic (so
  `HasFinCyclic` holds), and `𝒜 ⊗̄ B(ℒ) = B(ℋ ⊗ ℒ)`
  (`concreteTensor_top_top`), which has a separating vector only when
  `dim (ℋ ⊗ ℒ) ≤ 1`.  So "finitely cyclic ⟹ cyclic and separating after
  amplifying" is false as stated.
* *Nor can the cutting machinery reach it.*  The cuts `CT_of_relCT`
  admits are projections `e ∈ 𝒜^□`, and the corner algebra `𝒜_e` has a
  cyclic **and** separating vector `ξ` exactly when `[𝒜ξ] = e = [𝒜^□ξ]`
  — the first forces `e ∈ 𝒜^□`, the second `e ∈ 𝒜` (88IV plus 88VI), so
  `e ∈ Z(𝒜)`.  For a factor without a separating vector the only central
  cuts are `0` and `1`, and neither works.  So **no** net of cuts, in
  either orientation, reaches the cyclic-and-separating case.

What `cyclic_and_separating_of_separating` does deliver is a cyclic and
separating vector for the *reduced* algebra `(𝒜^□ ⊗ 1)f` at the single
cut `f = [(𝒜^□ ⊗ 1)ξ]`, which lies in the **algebra** `𝒜 ⊗̄ B(ℂⁿ)`, not
in its commutant.  Its central carrier is `1` — that *is* what the
amplification buys, since `ξ` cyclic for `𝒜 ⊗̄ B(ℂⁿ)` gives
`[(𝒜 ⊗̄ B(ℂⁿ)) f ℋ] = 1` — so `x ↦ x f` is injective on the commutant
and one cut suffices *in principle*.  But transporting `CT` across a cut
inside the algebra needs the relative commutant of the **compressed**
algebra, `(f 𝒯 f)^□ = 𝒯^□ f`, i.e. that `𝒯^□ f` is ultraweakly closed —
the *hard* half of the reduction theorem, equivalently the normality of
`w ↦ P w P^*`, which `A/Proc/CornerTensor.lean` deliberately avoids and
the tree does not have.  (`mem_vnComm_cornerAlg` is the *easy* half: it
computes the commutant of the **reduced** algebra, which is the case
`e ∈ 𝒜^□`.)

So the remaining gap between this file and the input RvD's theorem wants
is exactly: **"the compression of a von Neumann algebra is a von Neumann
algebra"** — `(f𝒯f)^□ = 𝒯^□f` for `f ∈ 𝒯`.  With it, one further cut at
the amplified level closes the reduction; without it, `CT_of_CT_cyclic`
is where the cutting-and-amplifying architecture stops.  It is a
self-contained piece (the classical proof extends `y ∈ (f𝒯f)^□` to
`ŷ(x f ζ) := x ỹ f ζ` on the dense `𝒯 f ℋ`), and it is the honest next
brief.
-/
import Theses.A.Proc.CommutationReduction
import Theses.A.Proc.TensorTransport

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
  TensorProduct ENNReal
open Filter Topology Theses Theses.A.VN

noncomputable section

namespace Theses.A.Proc

universe u

section Basic

variable {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mem_vnComm_coe {S : StarSubalgebra ℂ (H →L[ℂ] H)} {x : H →L[ℂ] H} :
    x ∈ vnComm S ↔ x ∈ commutant (H →L[ℂ] H) (S : Set (H →L[ℂ] H)) := by
  rw [← SetLike.mem_coe, coe_vnComm]

theorem coe_vnComm_vnComm {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hS : IsVNSubalgebra (H →L[ℂ] H) S) :
    commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) (S : Set (H →L[ℂ] H)))
      = (S : Set (H →L[ℂ] H)) := by
  have := congrArg (fun T : StarSubalgebra ℂ (H →L[ℂ] H) => (T : Set (H →L[ℂ] H)))
    (vnComm_vnComm S hS)
  rwa [coe_vnComm, coe_vnComm] at this

end Basic

/-! ## Slices, and the normality of `a ↦ a ⊗ 1`

The one tool the amplification transport needs and the tree lacks: the
set `{a | a ⊗ 1 ∈ 𝒲}` is, for a von Neumann subalgebra `𝒲` of
`B(ℋ ⊗ 𝒦)`, again a von Neumann subalgebra of `B(ℋ)`.  No ultraweak
continuity argument is used: by the double commutant theorem the set is
`{a | ∀ u ∈ 𝒲^□, (a ⊗ 1) u = u (a ⊗ 1)}`, and `a ⊗ 1` commutes with `u`
exactly when `a` commutes with every **slice** `Q_y^* u Q_{y'}` of `u`.
So the set is literally a commutant. -/

section Slice

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The **slice** `Q_y^* T Q_{y'} : ℋ → ℋ` of an operator
`T ∈ B(ℋ ⊗ 𝒦)` at a pair of vectors of `𝒦`. -/
def htSlice (T : HT H K →L[ℂ] HT H K) (y y' : K) : H →L[ℂ] H :=
  (ContinuousLinearMap.adjoint (htKet (H := H) y)).comp (T.comp (htKet (H := H) y'))

theorem inner_htSlice (T : HT H K →L[ℂ] HT H K) (y y' : K) (w x : H) :
    ⟪w, htSlice T y y' x⟫ = ⟪w ⊗ₕ y, T (x ⊗ₕ y')⟫ := by
  show ⟪w, ContinuousLinearMap.adjoint (htKet (H := H) y) (T (x ⊗ₕ y'))⟫ = _
  rw [ContinuousLinearMap.adjoint_inner_right, htKet_apply]

/-- The slice of the adjoint is the adjoint of the flipped slice. -/
theorem htSlice_star (T : HT H K →L[ℂ] HT H K) (y y' : K) :
    htSlice (star T) y y' = star (htSlice T y' y) := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine ext_inner_left ℂ fun w => ?_
  rw [inner_htSlice]
  show ⟪w ⊗ₕ y, ContinuousLinearMap.adjoint T (x ⊗ₕ y')⟫
      = ⟪w, ContinuousLinearMap.adjoint (htSlice T y' y) x⟫
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    ← inner_conj_symm (htSlice T y' y w), ← inner_conj_symm (T (w ⊗ₕ y))]
  rw [inner_htSlice]

/-- **`a ⊗ 1` commutes with `T` exactly when `a` commutes with every slice
of `T`.**  This is the whole content of the normality of `a ↦ a ⊗ 1`. -/
theorem opTensor_one_comm_iff (T : HT H K →L[ℂ] HT H K) (a : H →L[ℂ] H) :
    opTensor a (1 : K →L[ℂ] K) * T = T * opTensor a (1 : K →L[ℂ] K)
      ↔ ∀ y y' : K, a * htSlice T y y' = htSlice T y y' * a := by
  constructor
  · intro h y y'
    refine ContinuousLinearMap.ext fun x => ?_
    refine ext_inner_left ℂ fun w => ?_
    show ⟪w, a (htSlice T y y' x)⟫ = ⟪w, htSlice T y y' (a x)⟫
    rw [← ContinuousLinearMap.adjoint_inner_left, inner_htSlice, inner_htSlice]
    have h1 : (ContinuousLinearMap.adjoint a w) ⊗ₕ y
        = ContinuousLinearMap.adjoint (opTensor a (1 : K →L[ℂ] K)) (w ⊗ₕ y) := by
      rw [opTensor_adjoint, opTensor_apply, ContinuousLinearMap.adjoint_one]
      rfl
    rw [h1, ContinuousLinearMap.adjoint_inner_left]
    have h2 := congrArg (fun L : HT H K →L[ℂ] HT H K => L (x ⊗ₕ y')) h
    simp only [clm_mul_apply] at h2
    rw [h2, opTensor_apply]
    rfl
  · intro h
    refine ext_htmul fun x y' => ?_
    show opTensor a (1 : K →L[ℂ] K) (T (x ⊗ₕ y')) = T (opTensor a 1 (x ⊗ₕ y'))
    refine eq_of_inner_htmul fun w y => ?_
    have h1 : ⟪w ⊗ₕ y, opTensor a (1 : K →L[ℂ] K) (T (x ⊗ₕ y'))⟫
        = ⟪(ContinuousLinearMap.adjoint a w) ⊗ₕ y, T (x ⊗ₕ y')⟫ := by
      have h2 : (ContinuousLinearMap.adjoint a w) ⊗ₕ y
          = ContinuousLinearMap.adjoint (opTensor a (1 : K →L[ℂ] K)) (w ⊗ₕ y) := by
        rw [opTensor_adjoint, opTensor_apply, ContinuousLinearMap.adjoint_one]
        rfl
      rw [h2, ContinuousLinearMap.adjoint_inner_left]
    rw [h1, ← inner_htSlice, opTensor_apply]
    show ⟪ContinuousLinearMap.adjoint a w, htSlice T y y' x⟫ = ⟪w ⊗ₕ y, T (a x ⊗ₕ (1 : K →L[ℂ] K) y')⟫
    rw [ContinuousLinearMap.adjoint_inner_left]
    show ⟪w, a (htSlice T y y' x)⟫ = ⟪w ⊗ₕ y, T (a x ⊗ₕ y')⟫
    have h3 := congrArg (fun L : H →L[ℂ] H => L x) (h y y')
    simp only [clm_mul_apply] at h3
    rw [h3, inner_htSlice]

/-- **The amplification `a ↦ a ⊗ 1` is normal**, in the only form the
transport needs: if a von Neumann subalgebra `𝒲 ⊆ B(ℋ ⊗ 𝒦)` contains
`a ⊗ 1` for every `a` in a set `G`, it contains `a ⊗ 1` for every `a` in
the von Neumann algebra `W*(G)` generated by `G`.

The proof never mentions the ultraweak topology: `{a | a ⊗ 1 ∈ 𝒲}` is,
by the double commutant theorem, the commutant of the ∗-closed set of all
slices of all elements of `𝒲^□`. -/
theorem opTensor_one_mem_of_mem_wstar
    {W : StarSubalgebra ℂ (HT H K →L[ℂ] HT H K)}
    (hW : IsVNSubalgebra (HT H K →L[ℂ] HT H K) W)
    {G : Set (H →L[ℂ] H)} (hG : ∀ a ∈ G, opTensor a (1 : K →L[ℂ] K) ∈ W)
    {a : H →L[ℂ] H} (ha : a ∈ wstar (H →L[ℂ] H) G) :
    opTensor a (1 : K →L[ℂ] K) ∈ W := by
  classical
  set S : Set (H →L[ℂ] H) :=
    {s | ∃ u ∈ vnComm W, ∃ y y' : K, s = htSlice u y y'} with hS
  have hSstar : ∀ s ∈ S, star s ∈ S := by
    rintro _ ⟨u, hu, y, y', rfl⟩
    exact ⟨star u, star_mem hu, y', y, (htSlice_star u y' y).symm⟩
  obtain ⟨Z, hZvn, hZset⟩ := (commutant_basic_3' S hSstar).1
  have hmem : ∀ b : H →L[ℂ] H,
      b ∈ Z ↔ opTensor b (1 : K →L[ℂ] K) ∈ W := by
    intro b
    have h1 : b ∈ Z ↔ b ∈ commutant (H →L[ℂ] H) S := by
      constructor
      · intro hb; rw [← hZset]; exact hb
      · intro hb; have : b ∈ (Z : Set (H →L[ℂ] H)) := by rw [hZset]; exact hb
        exact this
    rw [h1]
    constructor
    · intro hb
      have h2 : opTensor b (1 : K →L[ℂ] K) ∈ vnComm (vnComm W) := by
        refine mem_vnComm.mpr fun u hu => ?_
        refine ((opTensor_one_comm_iff u b).mpr fun y y' => ?_).symm
        exact (hb _ ⟨u, hu, y, y', rfl⟩).symm
      rwa [vnComm_vnComm W hW] at h2
    · intro hb
      rintro _ ⟨u, hu, y, y', rfl⟩
      have h3 : opTensor b (1 : K →L[ℂ] K) * u = u * opTensor b (1 : K →L[ℂ] K) :=
        mul_comm_of_mem_vnComm hu hb
      exact ((opTensor_one_comm_iff u b).mp h3 y y').symm
  have hGZ : G ⊆ (Z : Set (H →L[ℂ] H)) := fun x hx => (hmem x).mpr (hG x hx)
  have hle : wstar (H →L[ℂ] H) G ≤ Z := sInf_le ⟨hZvn, hGZ⟩
  exact (hmem a).mp (hle ha)

/-- The mirror of `opTensor_one_mem_of_mem_wstar` for the second factor,
obtained by conjugating with the flip unitary. -/
theorem one_opTensor_mem_of_mem_wstar
    {W : StarSubalgebra ℂ (HT H K →L[ℂ] HT H K)}
    (hW : IsVNSubalgebra (HT H K →L[ℂ] HT H K) W)
    {G : Set (K →L[ℂ] K)} (hG : ∀ b ∈ G, opTensor (1 : H →L[ℂ] H) b ∈ W)
    {b : K →L[ℂ] K} (hb : b ∈ wstar (K →L[ℂ] K) G) :
    opTensor (1 : H →L[ℂ] H) b ∈ W := by
  have hU : IsUnitaryCLM (htFlip H K) := isUnitaryCLM_htFlip H K
  set W' : StarSubalgebra ℂ (HT K H →L[ℂ] HT K H) := uconj hU W with hW'
  have hW'vn : IsVNSubalgebra (HT K H →L[ℂ] HT K H) W' := isVNSubalgebra_uconj hU hW
  have hG' : ∀ c ∈ G, opTensor c (1 : H →L[ℂ] H) ∈ W' := by
    intro c hc
    have h := cext_mem_uconj hU (hG c hc)
    rwa [cext_htFlip_opTensor] at h
  have h := opTensor_one_mem_of_mem_wstar hW'vn hG' hb
  rw [hW'] at h
  have h2 := (mem_uconj hU).mp h
  rwa [← cext_htFlip_opTensor (1 : H →L[ℂ] H) b, cmpr_cext hU] at h2

end Slice

/-! ## `W*(G₁) ⊗̄ W*(G₂) = W*(G₁ ⊙ G₂)`

The concrete tensor product of two generated von Neumann algebras is
generated by the elementary tensors of the *generators*.  This is what
lets a four-fold rearrangement be checked on elementary tensors only. -/

section Generation

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem concreteTensor_wstar_le
    {W : StarSubalgebra ℂ (HT H K →L[ℂ] HT H K)}
    (hW : IsVNSubalgebra (HT H K →L[ℂ] HT H K) W)
    {G₁ : Set (H →L[ℂ] H)} {G₂ : Set (K →L[ℂ] K)}
    (h1 : ∀ a ∈ G₁, opTensor a (1 : K →L[ℂ] K) ∈ W)
    (h2 : ∀ b ∈ G₂, opTensor (1 : H →L[ℂ] H) b ∈ W) :
    concreteTensor H K (wstar (H →L[ℂ] H) G₁) (wstar (K →L[ℂ] K) G₂) ≤ W := by
  refine concreteTensor_le hW fun a ha b hb => ?_
  have ha' := opTensor_one_mem_of_mem_wstar hW h1 ha
  have hb' := one_opTensor_mem_of_mem_wstar hW h2 hb
  have hsplit : opTensor a b
      = opTensor a (1 : K →L[ℂ] K) * opTensor (1 : H →L[ℂ] H) b := by
    rw [← opTensor_mul, mul_one, one_mul]
  rw [hsplit]
  exact mul_mem ha' hb'

/-- **`W*(G₁) ⊗̄ W*(G₂) = W*({a ⊗ b : a ∈ G₁, b ∈ G₂})`** for generating
sets containing `1`. -/
theorem concreteTensor_wstar (G₁ : Set (H →L[ℂ] H)) (G₂ : Set (K →L[ℂ] K))
    (h1 : (1 : H →L[ℂ] H) ∈ G₁) (h2 : (1 : K →L[ℂ] K) ∈ G₂) :
    concreteTensor H K (wstar (H →L[ℂ] H) G₁) (wstar (K →L[ℂ] K) G₂)
      = wstar (HT H K →L[ℂ] HT H K)
          {x : HT H K →L[ℂ] HT H K | ∃ a ∈ G₁, ∃ b ∈ G₂, x = opTensor a b} := by
  refine le_antisymm ?_ ?_
  · refine concreteTensor_wstar_le (isVNSubalgebra_wstar _).1 ?_ ?_
    · exact fun a ha => (isVNSubalgebra_wstar _).2 ⟨a, ha, 1, h2, rfl⟩
    · exact fun b hb => (isVNSubalgebra_wstar _).2 ⟨1, h1, b, hb, rfl⟩
  · refine sInf_le ⟨isVNSubalgebra_concreteTensor _ _, ?_⟩
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact opTensor_mem_concreteTensor
      ((isVNSubalgebra_wstar _).2 ha) ((isVNSubalgebra_wstar _).2 hb)

end Generation

/-! ## The interchange unitary `(ℋ ⊗ ℒ) ⊗ 𝒦 ≅ (ℋ ⊗ 𝒦) ⊗ ℒ`

The rearrangement that moves an amplifying factor `ℒ` out of the first
tensorand and to the outside — associator, flip, associator. -/

section Interchange

variable {H H' H'' K L : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [NormedAddCommGroup H''] [InnerProductSpace ℂ H''] [CompleteSpace H'']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem isUnitaryCLM_comp {U : H →L[ℂ] H'} {V : H' →L[ℂ] H''}
    (hU : IsUnitaryCLM U) (hV : IsUnitaryCLM V) : IsUnitaryCLM (V ∘L U) := by
  refine ⟨?_, ?_⟩
  · rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc (ContinuousLinearMap.adjoint V) V U,
      hV.adjoint_comp]
    have h1 : (1 : H' →L[ℂ] H') ∘L U = U := by ext v; rfl
    rw [h1]; exact hU.adjoint_comp
  · rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc U (ContinuousLinearMap.adjoint U)
        (ContinuousLinearMap.adjoint V), hU.comp_adjoint]
    have h1 : (1 : H' →L[ℂ] H') ∘L ContinuousLinearMap.adjoint V
        = ContinuousLinearMap.adjoint V := by ext v; rfl
    rw [h1]; exact hV.comp_adjoint

theorem cext_comp (U : H →L[ℂ] H') (V : H' →L[ℂ] H'') (x : H →L[ℂ] H) :
    cext (V ∘L U) x = cext V (cext U x) := by
  show (V ∘L U) ∘L x ∘L ContinuousLinearMap.adjoint (V ∘L U)
      = V ∘L (U ∘L x ∘L ContinuousLinearMap.adjoint U) ∘L
        ContinuousLinearMap.adjoint V
  rw [ContinuousLinearMap.adjoint_comp]
  simp only [ContinuousLinearMap.comp_assoc]

@[simp] theorem cext_one_left (y : H →L[ℂ] H) : cext (1 : H →L[ℂ] H) y = y := by
  show (1 : H →L[ℂ] H) ∘L y ∘L ContinuousLinearMap.adjoint (1 : H →L[ℂ] H) = y
  rw [ContinuousLinearMap.adjoint_one]
  rfl

theorem isUnitaryCLM_one : IsUnitaryCLM (1 : H →L[ℂ] H) := isCorner_one

variable (H K L) in
/-- The **interchange unitary** `(ℋ ⊗ ℒ) ⊗ 𝒦 ≅ (ℋ ⊗ 𝒦) ⊗ ℒ`,
`(x ⊗ z) ⊗ y ↦ (x ⊗ y) ⊗ z`. -/
def htInterchange : HT (HT H L) K →L[ℂ] HT (HT H K) L :=
  (ContinuousLinearMap.adjoint (htAssoc H K L)) ∘L
    ((opTensor (1 : H →L[ℂ] H) (htFlip L K)) ∘L (htAssoc H L K))

variable (H K L) in
theorem isUnitaryCLM_htInterchange : IsUnitaryCLM (htInterchange H K L) :=
  isUnitaryCLM_comp
    (isUnitaryCLM_comp (isUnitaryCLM_htAssoc H L K)
      (isUnitaryCLM_one.opTensor (isUnitaryCLM_htFlip L K)))
    (isUnitaryCLM_htAssoc H K L).adjoint

/-- **The interchange on operators**: `(a ⊗ c) ⊗ b ↦ (a ⊗ b) ⊗ c`. -/
theorem cext_htInterchange_opTensor (a : H →L[ℂ] H) (b : K →L[ℂ] K)
    (c : L →L[ℂ] L) :
    cext (htInterchange H K L) (opTensor (opTensor a c) b)
      = opTensor (opTensor a b) c := by
  rw [htInterchange, cext_comp, cext_comp, cext_htAssoc_opTensor,
    cext_opTensor, cext_one_left, cext_htFlip_opTensor, cext_adjoint]
  have h := cext_htAssoc_opTensor (H := H) (K := K) (L := L) a b c
  rw [← h, cmpr_cext (isUnitaryCLM_htAssoc H K L)]

end Interchange

/-! ## The transport of `CT` across an amplification -/

section Transport

variable {H K L : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- The interchange unitary carries `(𝒜 ⊗̄ B(ℒ)) ⊗̄ ℬ` to
`(𝒜 ⊗̄ ℬ) ⊗̄ B(ℒ)`. -/
theorem uconj_htInterchange_concreteTensor (X : StarSubalgebra ℂ (H →L[ℂ] H))
    {Y : StarSubalgebra ℂ (K →L[ℂ] K)} (hY : IsVNSubalgebra (K →L[ℂ] K) Y) :
    uconj (isUnitaryCLM_htInterchange H K L)
        (concreteTensor (HT H L) K
          (concreteTensor H L X (⊤ : StarSubalgebra ℂ (L →L[ℂ] L))) Y)
      = concreteTensor (HT H K) L (concreteTensor H K X Y)
          (⊤ : StarSubalgebra ℂ (L →L[ℂ] L)) := by
  classical
  set G₁ : Set (HT H L →L[ℂ] HT H L) :=
    {x | ∃ a ∈ X, ∃ c ∈ (⊤ : StarSubalgebra ℂ (L →L[ℂ] L)), x = opTensor a c} with hG₁
  set G₁' : Set (HT H K →L[ℂ] HT H K) :=
    {x | ∃ a ∈ X, ∃ b ∈ Y, x = opTensor a b} with hG₁'
  have hone₁ : (1 : HT H L →L[ℂ] HT H L) ∈ G₁ :=
    ⟨1, one_mem X, 1, StarSubalgebra.mem_top, opTensor_one.symm⟩
  have hone₁' : (1 : HT H K →L[ℂ] HT H K) ∈ G₁' :=
    ⟨1, one_mem X, 1, one_mem Y, opTensor_one.symm⟩
  have hYw : Y = wstar (K →L[ℂ] K) (Y : Set (K →L[ℂ] K)) :=
    (wstar_eq_of_isVNSubalgebra Y hY).symm
  have hTw : (⊤ : StarSubalgebra ℂ (L →L[ℂ] L))
      = wstar (L →L[ℂ] L) ((⊤ : StarSubalgebra ℂ (L →L[ℂ] L)) : Set (L →L[ℂ] L)) :=
    (wstar_eq_of_isVNSubalgebra _ isVNSubalgebra_top).symm
  have hL : concreteTensor (HT H L) K
        (concreteTensor H L X (⊤ : StarSubalgebra ℂ (L →L[ℂ] L))) Y
      = wstar (HT (HT H L) K →L[ℂ] HT (HT H L) K)
          {x | ∃ w ∈ G₁, ∃ b ∈ (Y : Set (K →L[ℂ] K)), x = opTensor w b} := by
    conv_lhs => rw [concreteTensor_def X (⊤ : StarSubalgebra ℂ (L →L[ℂ] L)), hYw]
    exact concreteTensor_wstar G₁ _ hone₁ (one_mem Y)
  have hR : concreteTensor (HT H K) L (concreteTensor H K X Y)
        (⊤ : StarSubalgebra ℂ (L →L[ℂ] L))
      = wstar (HT (HT H K) L →L[ℂ] HT (HT H K) L)
          {x | ∃ u ∈ G₁', ∃ c ∈ ((⊤ : StarSubalgebra ℂ (L →L[ℂ] L)) :
            Set (L →L[ℂ] L)), x = opTensor u c} := by
    conv_lhs => rw [concreteTensor_def X Y, hTw]
    exact concreteTensor_wstar G₁' _ hone₁' StarSubalgebra.mem_top
  rw [hL, hR, uconj_wstar]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨_, ⟨a, ha, c, -, rfl⟩, b, hb, rfl⟩, rfl⟩
    exact ⟨opTensor a b, ⟨a, ha, b, hb, rfl⟩, c, StarSubalgebra.mem_top,
      cext_htInterchange_opTensor a b c⟩
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, c, -, rfl⟩
    exact ⟨opTensor (opTensor a c) b,
      ⟨opTensor a c, ⟨a, ha, c, StarSubalgebra.mem_top, rfl⟩, b, hb, rfl⟩,
      cext_htInterchange_opTensor a b c⟩

/-- The interchange unitary carries `(𝒜 ⊗̄ B(ℒ))^□ ⊗̄ ℬ^□` to the algebra
generated by `(a ⊗ b) ⊗ 1`, `a ∈ 𝒜^□`, `b ∈ ℬ^□`. -/
theorem uconj_htInterchange_vnComm {X : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hX : IsVNSubalgebra (H →L[ℂ] H) X) (Y : StarSubalgebra ℂ (K →L[ℂ] K)) :
    uconj (isUnitaryCLM_htInterchange H K L)
        (concreteTensor (HT H L) K
          (vnComm (concreteTensor H L X (⊤ : StarSubalgebra ℂ (L →L[ℂ] L))))
          (vnComm Y))
      = wstar (HT (HT H K) L →L[ℂ] HT (HT H K) L)
          {x | ∃ a ∈ vnComm X, ∃ b ∈ vnComm Y,
            x = opTensor (opTensor a b) (1 : L →L[ℂ] L)} := by
  classical
  have hamp : ∀ w : HT H L →L[ℂ] HT H L,
      w ∈ vnComm (concreteTensor H L X (⊤ : StarSubalgebra ℂ (L →L[ℂ] L)))
        ↔ ∃ a ∈ vnComm X, w = opTensor a (1 : L →L[ℂ] L) := by
    intro w
    rw [mem_vnComm_coe, commutant_concreteTensor_top X hX]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, mem_vnComm_coe.mpr ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, mem_vnComm_coe.mp ha, rfl⟩
  rw [concreteTensor_def, uconj_wstar]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨w, hw, z, hz, rfl⟩, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (hamp w).mp hw
    exact ⟨a, ha, z, hz, cext_htInterchange_opTensor a z 1⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨opTensor (opTensor a (1 : L →L[ℂ] L)) b,
      ⟨opTensor a (1 : L →L[ℂ] L), (hamp _).mpr ⟨a, ha, rfl⟩, b, hb, rfl⟩,
      cext_htInterchange_opTensor a b 1⟩

/-- **The commutation theorem descends along an amplification of the
first factor**: `CT (𝒜 ⊗̄ B(ℒ)) ℬ → CT 𝒜 ℬ` for `ℒ ≠ 0`. -/
theorem CT_of_CT_ampLeft {X : StarSubalgebra ℂ (H →L[ℂ] H)}
    {Y : StarSubalgebra ℂ (K →L[ℂ] K)}
    (hX : IsVNSubalgebra (H →L[ℂ] H) X) (hY : IsVNSubalgebra (K →L[ℂ] K) Y)
    {z₀ : L} (hz₀ : z₀ ≠ 0)
    (h : CT (concreteTensor H L X (⊤ : StarSubalgebra ℂ (L →L[ℂ] L))) Y) :
    CT X Y := by
  classical
  set hU := isUnitaryCLM_htInterchange H K L with hUdef
  set N : StarSubalgebra ℂ (HT H K →L[ℂ] HT H K) :=
    concreteTensor H K (vnComm X) (vnComm Y) with hN
  have hNvn : IsVNSubalgebra (HT H K →L[ℂ] HT H K) N :=
    isVNSubalgebra_concreteTensor _ _
  -- transport `CT` along the interchange
  have h1 : vnComm (concreteTensor (HT H L) K
        (concreteTensor H L X (⊤ : StarSubalgebra ℂ (L →L[ℂ] L))) Y)
      = concreteTensor (HT H L) K
        (vnComm (concreteTensor H L X (⊤ : StarSubalgebra ℂ (L →L[ℂ] L))))
        (vnComm Y) := h
  have h2 := congrArg (uconj hU) h1
  rw [← vnComm_uconj hU, uconj_htInterchange_concreteTensor X hY,
    uconj_htInterchange_vnComm hX Y] at h2
  -- the right-hand side sits inside `{u ⊗ 1 : u ∈ 𝒜^□ ⊗̄ ℬ^□}`
  set W : StarSubalgebra ℂ (HT (HT H K) L →L[ℂ] HT (HT H K) L) :=
    vnComm (concreteTensor (HT H K) L (vnComm N)
      (⊤ : StarSubalgebra ℂ (L →L[ℂ] L))) with hW
  have hWset : (W : Set (HT (HT H K) L →L[ℂ] HT (HT H K) L))
      = {z | ∃ u ∈ (N : Set (HT H K →L[ℂ] HT H K)),
          z = opTensor u (1 : L →L[ℂ] L)} := by
    rw [hW, coe_vnComm,
      commutant_concreteTensor_top (vnComm N) (isVNSubalgebra_vnComm N), coe_vnComm]
    rw [coe_vnComm_vnComm hNvn]
  have hle : wstar (HT (HT H K) L →L[ℂ] HT (HT H K) L)
      {x | ∃ a ∈ vnComm X, ∃ b ∈ vnComm Y,
        x = opTensor (opTensor a b) (1 : L →L[ℂ] L)} ≤ W := by
    refine sInf_le ⟨isVNSubalgebra_vnComm _, ?_⟩
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have : opTensor (opTensor a b) (1 : L →L[ℂ] L)
        ∈ (W : Set (HT (HT H K) L →L[ℂ] HT (HT H K) L)) := by
      rw [hWset]
      exact ⟨opTensor a b, opTensor_mem_concreteTensor ha hb, rfl⟩
    exact this
  -- read off the conclusion
  rw [CT_iff_le]
  intro T hT
  have hT1 : opTensor T (1 : L →L[ℂ] L)
      ∈ vnComm (concreteTensor (HT H K) L (concreteTensor H K X Y)
        (⊤ : StarSubalgebra ℂ (L →L[ℂ] L))) := by
    have hmem : opTensor T (1 : L →L[ℂ] L)
        ∈ commutant (HT (HT H K) L →L[ℂ] HT (HT H K) L)
          ((concreteTensor (HT H K) L (concreteTensor H K X Y)
            (⊤ : StarSubalgebra ℂ (L →L[ℂ] L)) :
            StarSubalgebra ℂ (HT (HT H K) L →L[ℂ] HT (HT H K) L)) :
            Set (HT (HT H K) L →L[ℂ] HT (HT H K) L)) := by
      rw [commutant_concreteTensor_top _ (isVNSubalgebra_concreteTensor X Y)]
      exact ⟨T, mem_vnComm_coe.mp hT, rfl⟩
    exact mem_vnComm_coe.mpr hmem
  rw [h2] at hT1
  have hTW : opTensor T (1 : L →L[ℂ] L)
      ∈ (W : Set (HT (HT H K) L →L[ℂ] HT (HT H K) L)) := hle hT1
  rw [hWset] at hTW
  obtain ⟨u, hu, hTu⟩ := hTW
  have : T = u := opTensor_one_right_inj hz₀ hTu
  rw [this]
  exact hu

/-- **The commutation theorem descends along an amplification of both
factors**: `CT (𝒜 ⊗̄ B(ℒ)) (ℬ ⊗̄ B(ℒ')) → CT 𝒜 ℬ` for `ℒ, ℒ' ≠ 0`. -/
theorem CT_of_CT_amp {L' : Type u} [NormedAddCommGroup L'] [InnerProductSpace ℂ L']
    [CompleteSpace L'] {X : StarSubalgebra ℂ (H →L[ℂ] H)}
    {Y : StarSubalgebra ℂ (K →L[ℂ] K)}
    (hX : IsVNSubalgebra (H →L[ℂ] H) X) (hY : IsVNSubalgebra (K →L[ℂ] K) Y)
    {z₀ : L} (hz₀ : z₀ ≠ 0) {z₁ : L'} (hz₁ : z₁ ≠ 0)
    (h : CT (concreteTensor H L X (⊤ : StarSubalgebra ℂ (L →L[ℂ] L)))
          (concreteTensor K L' Y (⊤ : StarSubalgebra ℂ (L' →L[ℂ] L')))) :
    CT X Y := by
  have h1 : CT (concreteTensor K L' Y (⊤ : StarSubalgebra ℂ (L' →L[ℂ] L')))
      (concreteTensor H L X (⊤ : StarSubalgebra ℂ (L →L[ℂ] L))) :=
    (CT_comm _ _).mp h
  have h2 : CT Y (concreteTensor H L X (⊤ : StarSubalgebra ℂ (L →L[ℂ] L))) :=
    CT_of_CT_ampLeft hY (isVNSubalgebra_concreteTensor X _) hz₁ h1
  exact CT_of_CT_ampLeft hX hY hz₀ ((CT_comm _ _).mp h2)

end Transport

/-! ## `n` jointly cyclic vectors become one after amplifying by `ℂⁿ` -/

section Amplify

variable {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `HasCyclic S` : the set `S` of operators has a **cyclic vector**. -/
def HasCyclic (S : Set (H →L[ℂ] H)) : Prop :=
  ∃ ξ : H, Dense ((Submodule.span ℂ {y : H | ∃ x ∈ S, y = x ξ} : Submodule ℂ H) : Set H)

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The matrix unit `|δ_j⟩⟨δ_i|` of `B(ℂ^ι)`. -/
def euclidRankOne (i j : ι) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  (innerSL ℂ (EuclideanSpace.single i (1 : ℂ))).smulRight
    (EuclideanSpace.single j (1 : ℂ))

theorem euclidRankOne_single (i j k : ι) :
    euclidRankOne i j (EuclideanSpace.single k (1 : ℂ))
      = if i = k then EuclideanSpace.single j (1 : ℂ) else 0 := by
  have hin : ⟪EuclideanSpace.single i (1 : ℂ), EuclideanSpace.single k (1 : ℂ)⟫
      = if i = k then (1 : ℂ) else 0 := by
    rw [EuclideanSpace.inner_single_left, PiLp.single_apply]
    simp
  show ⟪EuclideanSpace.single i (1 : ℂ), EuclideanSpace.single k (1 : ℂ)⟫ •
      EuclideanSpace.single j (1 : ℂ) = _
  rw [hin]
  split_ifs with h <;> simp

/-- **The amplification of a finite jointly cyclic family is cyclic.**
If `ξ_1, …, ξ_n` are jointly cyclic for a ∗-subalgebra `𝒜 ⊆ B(ℋ)`, then
`∑ᵢ ξᵢ ⊗ δᵢ` is a cyclic vector for `𝒜 ⊗̄ B(ℂⁿ)`. -/
theorem hasCyclic_concreteTensor_top {X : StarSubalgebra ℂ (H →L[ℂ] H)} (ξ : ι → H)
    (hcyc : Dense ((Submodule.span ℂ
      {y : H | ∃ x ∈ X, ∃ i : ι, y = x (ξ i)} : Submodule ℂ H) : Set H)) :
    HasCyclic ((concreteTensor H (EuclideanSpace ℂ ι) X
        (⊤ : StarSubalgebra ℂ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) :
        StarSubalgebra ℂ (HT H (EuclideanSpace ℂ ι) →L[ℂ] HT H (EuclideanSpace ℂ ι))) :
      Set (HT H (EuclideanSpace ℂ ι) →L[ℂ] HT H (EuclideanSpace ℂ ι))) := by
  classical
  set δ : ι → EuclideanSpace ℂ ι := fun i => EuclideanSpace.single i (1 : ℂ) with hδ
  set Ξ : HT H (EuclideanSpace ℂ ι) := ∑ i : ι, ξ i ⊗ₕ δ i with hΞ
  refine ⟨Ξ, ?_⟩
  set S : Set (HT H (EuclideanSpace ℂ ι)) :=
    {y | ∃ w ∈ (concreteTensor H (EuclideanSpace ℂ ι) X
      (⊤ : StarSubalgebra ℂ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) :
      Set (HT H (EuclideanSpace ℂ ι) →L[ℂ] HT H (EuclideanSpace ℂ ι))), y = w Ξ}
    with hS
  set D : Submodule ℂ (HT H (EuclideanSpace ℂ ι)) :=
    (Submodule.span ℂ S).topologicalClosure with hD
  -- the compressions of `Ξ` by the matrix units
  have hcomp : ∀ (i j : ι) (x : H →L[ℂ] H),
      opTensor x (euclidRankOne i j) Ξ = (x (ξ i)) ⊗ₕ δ j := by
    intro i j x
    rw [hΞ, map_sum]
    have hterm : ∀ k : ι, opTensor x (euclidRankOne i j) (ξ k ⊗ₕ δ k)
        = if i = k then (x (ξ k)) ⊗ₕ δ j else 0 := by
      intro k
      rw [opTensor_apply, euclidRankOne_single]
      split_ifs with h
      · rfl
      · exact htmul_zero_right _
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_ite_eq Finset.univ i
      (fun k => (x (ξ k)) ⊗ₕ δ j)]
    simp
  have hgen : ∀ (i j : ι) (x : H →L[ℂ] H), x ∈ X →
      (x (ξ i)) ⊗ₕ δ j ∈ Submodule.span ℂ S := by
    intro i j x hx
    refine Submodule.subset_span ⟨opTensor x (euclidRankOne i j), ?_, (hcomp i j x).symm⟩
    exact opTensor_mem_concreteTensor hx StarSubalgebra.mem_top
  -- every `u ⊗ δ_j` lies in the closure
  have hstep1 : ∀ (j : ι) (u : H), u ⊗ₕ δ j ∈ D := by
    intro j u
    set Z : Submodule ℂ H :=
      (D.comap (htKet (H := H) (δ j) : H →ₗ[ℂ] HT H (EuclideanSpace ℂ ι))) with hZ
    have hZclosed : IsClosed (Z : Set H) := by
      have : (Z : Set H) = (htKet (H := H) (δ j)) ⁻¹' (D : Set (HT H (EuclideanSpace ℂ ι))) :=
        rfl
      rw [this]
      exact IsClosed.preimage (htKet (H := H) (δ j)).continuous
        (Submodule.isClosed_topologicalClosure (Submodule.span ℂ S))
    have hsub : {y : H | ∃ x ∈ X, ∃ i : ι, y = x (ξ i)} ⊆ (Z : Set H) := by
      rintro _ ⟨x, hx, i, rfl⟩
      exact Submodule.le_topologicalClosure _ (hgen i j x hx)
    have hspanle : Submodule.span ℂ {y : H | ∃ x ∈ X, ∃ i : ι, y = x (ξ i)} ≤ Z :=
      Submodule.span_le.mpr hsub
    have : u ∈ (Z : Set H) :=
      hZclosed.closure_subset (closure_mono (fun z hz => hspanle hz) (hcyc u))
    exact this
  -- hence every elementary tensor
  have hstep2 : ∀ (u : H) (v : EuclideanSpace ℂ ι), u ⊗ₕ v ∈ D := by
    intro u v
    set Y : Submodule ℂ (EuclideanSpace ℂ ι) :=
      (D.comap (htKetL (K := EuclideanSpace ℂ ι) u :
        EuclideanSpace ℂ ι →ₗ[ℂ] HT H (EuclideanSpace ℂ ι))) with hY
    have hrange : Set.range δ ⊆ (Y : Set (EuclideanSpace ℂ ι)) := by
      rintro _ ⟨j, rfl⟩
      exact hstep1 j u
    have hspan : Submodule.span ℂ (Set.range δ) = ⊤ := by
      have h := (EuclideanSpace.basisFun ι ℂ).toBasis.span_eq
      have he : δ = ⇑(EuclideanSpace.basisFun ι ℂ) := by
        funext j; rw [EuclideanSpace.basisFun_apply]
      rw [he]
      simpa using h
    have hYtop : Y = ⊤ := by
      rw [← top_le_iff, ← hspan]
      exact Submodule.span_le.mpr hrange
    have : v ∈ Y := hYtop ▸ Submodule.mem_top
    exact this
  -- and the elementary tensors are total
  rw [← dense_closure]
  refine (hilbTensor H (EuclideanSpace ℂ ι)).isTensor.dense.mono ?_
  intro z hz
  have hz' : z ∈ D := by
    refine Submodule.span_le.mpr ?_ hz
    rintro _ ⟨u, v, rfl⟩
    exact hstep2 u v
  rw [← SetLike.mem_coe, hD, Submodule.topologicalClosure_coe] at hz'
  exact hz'

end Amplify

/-! ## `CT` only depends on the bicommutants

A corollary of the generation lemma that removes the caveat recorded in
the header of `A/Proc/CommutationReduction.lean`: `𝒜 ⊗̄ ℬ` is unchanged
when `𝒜` and `ℬ` are replaced by their bicommutants, so `CT` is too. -/

section Bicommutant

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem wstar_coe_eq_vnComm_vnComm (X : StarSubalgebra ℂ (H →L[ℂ] H)) :
    wstar (H →L[ℂ] H) (X : Set (H →L[ℂ] H)) = vnComm (vnComm X) := by
  refine SetLike.ext' ?_
  rw [coe_vnComm, coe_vnComm]
  exact ((double_commutant X).2.2).symm

/-- **`𝒜 ⊗̄ ℬ = 𝒜^□□ ⊗̄ ℬ^□□`.** -/
theorem concreteTensor_vnComm_vnComm (X : StarSubalgebra ℂ (H →L[ℂ] H))
    (Y : StarSubalgebra ℂ (K →L[ℂ] K)) :
    concreteTensor H K (vnComm (vnComm X)) (vnComm (vnComm Y))
      = concreteTensor H K X Y := by
  rw [← wstar_coe_eq_vnComm_vnComm, ← wstar_coe_eq_vnComm_vnComm,
    concreteTensor_wstar _ _ (one_mem X) (one_mem Y), concreteTensor_def]
  rfl

/-- **`CT 𝒜 ℬ ↔ CT 𝒜^□□ ℬ^□□`.** -/
theorem CT_iff_bicommutant (X : StarSubalgebra ℂ (H →L[ℂ] H))
    (Y : StarSubalgebra ℂ (K →L[ℂ] K)) :
    CT X Y ↔ CT (vnComm (vnComm X)) (vnComm (vnComm Y)) := by
  show vnComm (concreteTensor H K X Y) = concreteTensor H K (vnComm X) (vnComm Y) ↔
    vnComm (concreteTensor H K (vnComm (vnComm X)) (vnComm (vnComm Y)))
      = concreteTensor H K (vnComm (vnComm (vnComm X))) (vnComm (vnComm (vnComm Y)))
  rw [concreteTensor_vnComm_vnComm, vnComm_vnComm _ (isVNSubalgebra_vnComm X),
    vnComm_vnComm _ (isVNSubalgebra_vnComm Y)]

end Bicommutant

/-! ## The capstone -/

section Capstone

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The hypothesis "`CT` holds whenever both algebras have a cyclic
vector", as a `Prop` in one universe. -/
def CyclicCTStatement : Prop :=
  ∀ {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (X : StarSubalgebra ℂ (E →L[ℂ] E)) (Y : StarSubalgebra ℂ (F →L[ℂ] F)),
    IsVNSubalgebra (E →L[ℂ] E) X → IsVNSubalgebra (F →L[ℂ] F) Y →
    HasCyclic (X : Set (E →L[ℂ] E)) → HasCyclic (Y : Set (F →L[ℂ] F)) → CT X Y

/-- **Finitely cyclic reduces to cyclic.**  Given the commutation theorem
for pairs of von Neumann algebras with cyclic vectors, it holds for every
pair of ∗-subalgebras with a finite jointly cyclic family.

`n` jointly cyclic vectors become one after amplifying by `ℂⁿ`
(`hasCyclic_concreteTensor_top`), and `CT` descends along the
amplification (`CT_of_CT_amp`).  The passage from `X` to `X^□□`, needed
because the algebras handed over by the cutting machinery are not known
to be ultraweakly closed, is `CT_iff_bicommutant`. -/
theorem CT_of_CT_cyclic_finCyclic (hyp : CyclicCTStatement.{u})
    {X : StarSubalgebra ℂ (H →L[ℂ] H)} {Y : StarSubalgebra ℂ (K →L[ℂ] K)}
    (hX : HasFinCyclic (X : Set (H →L[ℂ] H)))
    (hY : HasFinCyclic (Y : Set (K →L[ℂ] K))) : CT X Y := by
  classical
  rw [CT_iff_bicommutant]
  set X' : StarSubalgebra ℂ (H →L[ℂ] H) := vnComm (vnComm X) with hX'
  set Y' : StarSubalgebra ℂ (K →L[ℂ] K) := vnComm (vnComm Y) with hY'
  have hX'vn : IsVNSubalgebra (H →L[ℂ] H) X' := isVNSubalgebra_vnComm _
  have hY'vn : IsVNSubalgebra (K →L[ℂ] K) Y' := isVNSubalgebra_vnComm _
  obtain ⟨s, hsfin, hscyc⟩ :=
    hasFinCyclic_mono (S := (X : Set (H →L[ℂ] H))) (T := (X' : Set (H →L[ℂ] H)))
      (fun a ha => le_vnComm_vnComm X ha) hX
  obtain ⟨t, htfin, htcyc⟩ :=
    hasFinCyclic_mono (S := (Y : Set (K →L[ℂ] K))) (T := (Y' : Set (K →L[ℂ] K)))
      (fun a ha => le_vnComm_vnComm Y ha) hY
  have : Fintype ↥s := hsfin.fintype
  have : Fintype ↥t := htfin.fintype
  -- the index types of the two amplifications
  have : DecidableEq (Option ↥s) := Classical.decEq _
  have : DecidableEq (Option ↥t) := Classical.decEq _
  set ξ : Option ↥s → H := fun i => i.elim 0 Subtype.val with hξ
  set η : Option ↥t → K := fun j => j.elim 0 Subtype.val with hη
  have hXd : Dense ((Submodule.span ℂ
      {y : H | ∃ x ∈ X', ∃ i : Option ↥s, y = x (ξ i)} : Submodule ℂ H) : Set H) := by
    refine hscyc.mono (Submodule.span_mono ?_)
    rintro _ ⟨x, hx, ζ, hζ, rfl⟩
    exact ⟨x, hx, some ⟨ζ, hζ⟩, rfl⟩
  have hYd : Dense ((Submodule.span ℂ
      {y : K | ∃ x ∈ Y', ∃ j : Option ↥t, y = x (η j)} : Submodule ℂ K) : Set K) := by
    refine htcyc.mono (Submodule.span_mono ?_)
    rintro _ ⟨x, hx, ζ, hζ, rfl⟩
    exact ⟨x, hx, some ⟨ζ, hζ⟩, rfl⟩
  have hXc := hasCyclic_concreteTensor_top (X := X') ξ hXd
  have hYc := hasCyclic_concreteTensor_top (X := Y') η hYd
  have hz₀ : EuclideanSpace.single (none : Option ↥s) (1 : ℂ)
      ≠ (0 : EuclideanSpace ℂ (Option ↥s)) := by
    simp [PiLp.single_eq_zero_iff]
  have hz₁ : EuclideanSpace.single (none : Option ↥t) (1 : ℂ)
      ≠ (0 : EuclideanSpace ℂ (Option ↥t)) := by
    simp [PiLp.single_eq_zero_iff]
  exact CT_of_CT_amp hX'vn hY'vn hz₀ hz₁
    (hyp _ _ (isVNSubalgebra_concreteTensor _ _) (isVNSubalgebra_concreteTensor _ _)
      hXc hYc)

/-- **The commutation theorem from the cyclic case.**  If `CT` holds for
every pair of von Neumann algebras each of which has a **cyclic vector**,
then it holds for **every** pair of von Neumann subalgebras
`𝒜 ⊆ B(ℋ)`, `ℬ ⊆ B(𝒦)`.

This is `CT_of_CT_finCyclic` (`A/Proc/CommutationReduction.lean`) — the
whole amplify-and-cut reduction — composed with the `ℂⁿ` amplification of
this file. -/
theorem CT_of_CT_cyclic (hyp : CyclicCTStatement.{u})
    {SA : StarSubalgebra ℂ (H →L[ℂ] H)} {SB : StarSubalgebra ℂ (K →L[ℂ] K)}
    (hA : IsVNSubalgebra (H →L[ℂ] H) SA) (hB : IsVNSubalgebra (K →L[ℂ] K) SB) :
    CT SA SB := by
  refine CT_of_CT_finCyclic ?_ hA hB
  intro E F _ _ _ _ _ _ X Y hX hY
  exact CT_of_CT_cyclic_finCyclic hyp hX hY

end Capstone

end Theses.A.Proc
