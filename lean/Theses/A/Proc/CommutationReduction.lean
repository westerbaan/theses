/-
Thesis A, chapter "Assorted Structure in W*_cpsu" (proc.tex): the
**capstone of the amplify-and-cut reduction** for the commutation theorem
`CT 𝒜 ℬ : (𝒜 ⊗̄ ℬ)^□ = 𝒜^□ ⊗̄ ℬ^□` (Takesaki I, Thm IV.5.9).

`A/Proc/Commutation.lean` supplies the cutting principle and the Zorn
argument, `A/Proc/CornerTensor.lean` the corner Hilbert space and the
passage from the commutation theorem *for the corners* to the relative
form at a cut.  This file glues them: it produces the net of cuts, and
identifies the class of algebras the reduction actually reaches.

## The result

`CT_of_CT_finCyclic`: **if `CT X Y` holds for every pair of von Neumann
subalgebras `X ⊆ B(E)`, `Y ⊆ B(F)` admitting a finite jointly cyclic
family of vectors, then `CT 𝒜 ℬ` holds for all von Neumann subalgebras
`𝒜 ⊆ B(ℋ)`, `ℬ ⊆ B(𝒦)`.**

## Why the hypothesis is *finitely* cyclic and not cyclic-and-separating

The cutting principle `mem_of_compress_mem` consumes a **monotone** net of
projections with supremum `1`; so the cuts `e` admissible for
`CT_of_relCT` must form a *directed* family exhausting `1`.  The corner
`𝒜_e = e𝒜e` of a cut `e = [𝒜^□ ξ] ∈ 𝒜` does have `ξ` cyclic for its
commutant `(𝒜^□)_e`; but `e ∨ f` is never again of that form, and it is
of the form "`n` vectors are jointly cyclic".  Concretely: the family
`{[𝒜^□ξ] : ξ ∈ ℋ}` is not directed —

* for `𝒜 = ℂ·1 ⊆ B(ℋ)` one has `[𝒜^□ξ] = [B(ℋ)ξ] = 1` for every `ξ ≠ 0`,
  so the only cut is `e = 1` and the corner is `B(ℋ)`, which has **no**
  separating vector once `dim ℋ ≥ 2`;
* dually for `𝒜 = B(ℋ)`, where `ξ` is separating for `e𝒜e = B(eℋ)` only
  when `dim eℋ = 1`, and the rank-one projections do not increase to `1`.

So **no** increasing net of cuts can reach the cyclic-and-separating case
— for either orientation of the cut, and for any choice of the Zorn
family.  What survives finite joins is exactly *finite joint cyclicity*,
and that is what is proved here.  The step that follows is the genuine
**amplification** `ℋ ⇝ ℋ ⊗ ℂⁿ` of `A/Proc/CommutationAmplify.lean`: if
`ξ_1, …, ξ_n` are jointly cyclic for `X ⊆ B(ℋ)` then `ξ = ∑ ξ_i ⊗ δ_i` is
a *cyclic* vector for `X ⊗̄ B(ℂⁿ)`, and `CT` descends along the
amplification, so finite joint cyclicity reduces to a single **cyclic**
vector.  It does *not* reach cyclic-and-separating — see that file's
header for why no amplification and no net of cuts can — which is instead
reached by one cut *inside* the algebra
(`A/Proc/Compression.lean`, `A/Proc/CommutationCyclic.lean`).  See
`docs/COMMUTATION-THEOREM.md` §4.

## One caveat inherited from `relCT_of_CT`

The hypothesis of `CT_of_CT_finCyclic` quantifies over *arbitrary*
`∗`-subalgebras `X`, `Y` with a finite jointly cyclic family, not only
over von Neumann ones.  That is forced by `relCT_of_CT`, whose hypothesis
is `CT` for the compressed algebras `𝒜_e = cmpr '' 𝒜` — and `𝒜_e` is not
known here to be ultraweakly closed: for a cut `e ∈ 𝒜^□` that is exactly
the normality of `x ↦ e x e`, deliberately avoided in
`A/Proc/CornerTensor.lean` (see its header).  The quantifier costs
nothing: `hasFinCyclic_mono` says the hypothesis stays available after
enlarging `X` to its bicommutant, and `CT_iff_bicommutant`
(`A/Proc/CommutationAmplify.lean`) says `CT X Y` and `CT X^□□ Y^□□` are
the same statement.
-/
import Theses.A.Proc.CornerTensor

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
  TensorProduct ENNReal
open Filter Topology Theses Theses.A.VN

noncomputable section

namespace Theses.A.Proc

universe u

/-! ## Finite joint cyclicity -/

section Cyclic

variable {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `CyclicSet S s` : the set `s ⊆ ℋ` of vectors is **jointly cyclic** for
the set `S` of operators — the span of `S s` is dense. -/
def CyclicSet (S : Set (H →L[ℂ] H)) (s : Set H) : Prop :=
  Dense ((Submodule.span ℂ {y : H | ∃ x ∈ S, ∃ ξ ∈ s, y = x ξ} : Submodule ℂ H) : Set H)

/-- `HasFinCyclic S` : some **finite** family of vectors is jointly cyclic
for `S`.  For a singleton this is the existence of a cyclic vector. -/
def HasFinCyclic (S : Set (H →L[ℂ] H)) : Prop :=
  ∃ s : Set H, s.Finite ∧ CyclicSet S s

omit [CompleteSpace H] in
/-- Finite joint cyclicity is monotone: a larger set of operators inherits
it.  (In particular a finitely cyclic `∗`-subalgebra stays finitely cyclic
inside its bicommutant.) -/
theorem hasFinCyclic_mono {S T : Set (H →L[ℂ] H)} (hST : S ⊆ T)
    (h : HasFinCyclic S) : HasFinCyclic T := by
  obtain ⟨s, hsfin, hcyc⟩ := h
  refine ⟨s, hsfin, hcyc.mono ?_⟩
  refine Submodule.span_mono ?_
  rintro y ⟨x, hx, η, hη, rfl⟩
  exact ⟨x, hST hx, η, hη, rfl⟩

end Cyclic

/-! ## A separating vector for the corner pins the corner down

If `e ∈ M` is a projection fixing `ξ` and `ξ` is separating for the corner
`e M e`, then `e` *is* the cyclic projection `[M^□ ξ]`.  (The projection
`q = [M^□ ξ]` always satisfies `q ≤ e`; the difference `e − q` lies in `M`,
sits in the corner and kills `ξ`.)  This is what upgrades the output of
`exists_separating_corner`/`exists_orthogonal_separating_family` from a
separation statement to the *cyclicity* statement the reduction needs. -/

section RangeOfCorner

variable {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem range_eq_closure_of_separating {M : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hM : IsVNSubalgebra (H →L[ℂ] H) M) {e : H →L[ℂ] H} (he : IsStarProjection e)
    (heM : e ∈ M) {ξ : H} (hξ : e ξ = ξ)
    (hsep : SeparatingFor (compressedSet e (M : Set (H →L[ℂ] H))) ξ) :
    {y : H | e y = y} = closure {y : H | ∃ T ∈ vnComm M, y = T ξ} := by
  obtain ⟨q, hqproj, hqcomm, hqξ, hfix⟩ := exists_cyclic_projection (vnComm M) ξ
  have hqM : q ∈ M := by
    have h1 : q ∈ (vnComm (vnComm M) : Set (H →L[ℂ] H)) := by
      rw [coe_vnComm]; exact hqcomm
    rwa [vnComm_vnComm M hM] at h1
  -- `e` fixes the closure of `M^□ ξ`, hence `e q = q`
  have heq : e * q = q := by
    have hfixcl : ∀ y ∈ closure {y : H | ∃ T ∈ vnComm M, y = T ξ}, e y = y := by
      intro y hy
      have hcl : IsClosed {y : H | e y = y} := isClosed_fixed e
      refine hcl.closure_subset (closure_mono ?_ hy)
      rintro _ ⟨T, hT, rfl⟩
      have hcomm : e * T = T * e := mem_vnComm.mp hT e heM
      have hap := congrArg (fun L : H →L[ℂ] H => L ξ) hcomm
      simp only [clm_mul_apply] at hap
      show e (T ξ) = T ξ
      rw [hap, hξ]
    ext w
    show e (q w) = q w
    refine hfixcl _ ?_
    rw [← hfix]
    show q (q w) = q w
    rw [← clm_mul_apply, hqproj.isIdempotentElem]
  have hqe : q * e = q := by
    have h := congrArg star heq
    rwa [star_mul, hqproj.isSelfAdjoint, he.isSelfAdjoint] at h
  -- `e − q` lies in the corner and is killed by `ξ`
  have hsq : e - q ∈ M := sub_mem heM hqM
  have hmid : e * (e - q) * e = e - q := by
    calc e * (e - q) * e = (e * e - e * q) * e := by noncomm_ring
      _ = (e - q) * e := by rw [he.isIdempotentElem, heq]
      _ = e * e - q * e := by noncomm_ring
      _ = e - q := by rw [he.isIdempotentElem, hqe]
  have hkill : (e * (e - q) * e) ξ = 0 := by
    rw [hmid]
    show e ξ - q ξ = 0
    rw [hξ, hqξ, sub_self]
  have hzero : e * (e - q) * e = 0 := hsep _ ⟨e - q, hsq, rfl⟩ hkill
  have heqq : e = q := sub_eq_zero.mp (hmid.symm.trans hzero)
  rw [heqq, hfix]

end RangeOfCorner

/-! ## The corner of a finite orthogonal sum is finitely cyclic

If `p = ∑_{i ∈ F} q_i` with the `q_i` orthogonal projections whose ranges
are the cyclic subspaces `closure (𝒜 ξ_i)`, then the compressions
`sub^* ξ_i` are jointly cyclic for the compressed algebra `𝒜_p ⊆ B(pℋ)`:
every `w ∈ pℋ` decomposes as `∑_i q_i w`, and each summand is approximated
inside `𝒜 ξ_i`. -/

section CornerCyclic

variable {H E : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem hasFinCyclic_cornerAlg {SA : StarSubalgebra ℂ (H →L[ℂ] H)} {p : H →L[ℂ] H}
    {sub : E →L[ℂ] H} (hsub : IsCorner sub p) (hp : p ∈ vnComm SA)
    {ι : Type*} (F : Finset ι) (q : ι → H →L[ℂ] H)
    (hq : ∀ i ∈ F, IsStarProjection (q i)) (ξ : ι → H)
    (hsum : p = ∑ i ∈ F, q i) (hpξ : ∀ i ∈ F, p (ξ i) = ξ i)
    (hran : ∀ i ∈ F, {y : H | q i y = y} = closure {y : H | ∃ a ∈ SA, y = a (ξ i)}) :
    HasFinCyclic ((cornerAlg hsub SA hp : StarSubalgebra ℂ (E →L[ℂ] E)) :
      Set (E →L[ℂ] E)) := by
  classical
  set s : Set E := (fun i => ContinuousLinearMap.adjoint sub (ξ i)) '' (F : Set ι) with hs
  refine ⟨s, (F.finite_toSet).image _, ?_⟩
  set W : Submodule ℂ E := Submodule.span ℂ
    {y : E | ∃ x ∈ ((cornerAlg hsub SA hp : StarSubalgebra ℂ (E →L[ℂ] E)) :
      Set (E →L[ℂ] E)), ∃ η ∈ s, y = x η} with hW
  have hWc : IsClosed ((W.topologicalClosure : Submodule ℂ E) : Set E) :=
    W.isClosed_topologicalClosure
  -- the compressed generators
  have hgen : ∀ i ∈ F, ∀ a ∈ SA, ContinuousLinearMap.adjoint sub (a (ξ i)) ∈ W := by
    intro i hi a ha
    have hcm : cmpr sub a (ContinuousLinearMap.adjoint sub (ξ i))
        = ContinuousLinearMap.adjoint sub (a (ξ i)) := by
      rw [cmpr_apply, hsub.sub_adjoint_apply, hpξ i hi]
    exact Submodule.subset_span
      ⟨cmpr sub a, cmpr_mem_cornerAlg ha, _, ⟨i, hi, rfl⟩, hcm.symm⟩
  -- the whole range of `q i` compresses into the closure
  have hstep : ∀ i ∈ F, ∀ y : H, q i y = y →
      ContinuousLinearMap.adjoint sub y ∈ W.topologicalClosure := by
    intro i hi y hy
    have hpre : IsClosed ((ContinuousLinearMap.adjoint sub) ⁻¹'
        ((W.topologicalClosure : Submodule ℂ E) : Set E)) :=
      hWc.preimage (ContinuousLinearMap.adjoint sub).continuous
    have hsubset : {z : H | ∃ a ∈ SA, z = a (ξ i)} ⊆
        (ContinuousLinearMap.adjoint sub) ⁻¹'
          ((W.topologicalClosure : Submodule ℂ E) : Set E) := by
      rintro _ ⟨a, ha, rfl⟩
      exact W.le_topologicalClosure (hgen i hi a ha)
    have hmem : y ∈ closure {z : H | ∃ a ∈ SA, z = a (ξ i)} := by
      rw [← hran i hi]; exact hy
    exact hpre.closure_subset (closure_mono hsubset hmem)
  -- every vector of `E` is reached
  intro w
  have hsw : ContinuousLinearMap.adjoint sub (sub w) = w := hsub.apply_adjoint_apply w
  have hpsw : p (sub w) = sub w := by
    have h := congrArg (fun T : E →L[ℂ] H => T w) hsub.mul_sub
    simpa using h
  have hdecomp : sub w = ∑ i ∈ F, q i (sub w) := by
    conv_lhs => rw [← hpsw, hsum]
    simp
  have hfin : w ∈ W.topologicalClosure := by
    have hexp : ContinuousLinearMap.adjoint sub (sub w)
        = ∑ i ∈ F, ContinuousLinearMap.adjoint sub (q i (sub w)) :=
      calc ContinuousLinearMap.adjoint sub (sub w)
          = ContinuousLinearMap.adjoint sub (∑ i ∈ F, q i (sub w)) := by rw [← hdecomp]
        _ = ∑ i ∈ F, ContinuousLinearMap.adjoint sub (q i (sub w)) := map_sum _ _ _
    rw [hsw] at hexp
    rw [hexp]
    refine Submodule.sum_mem _ fun i hi => hstep i hi _ ?_
    rw [← clm_mul_apply, (hq i hi).isIdempotentElem]
  exact hfin

end CornerCyclic

/-! ## The net of cuts

The Zorn family of `exists_orthogonal_separating_family`, upgraded by
`range_eq_closure_of_separating` to a family of *cyclic* projections and
summed over finite subsets by `isLUB_range_finsetSum`. -/

section Net

variable {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Step 2, in cyclic form.**  Every von Neumann subalgebra
`𝒜 ⊆ B(ℋ)` carries an orthogonal family of projections of `𝒜^□` with
supremum `1`, each of which is the cyclic projection `[𝒜 ξ]` of a
vector `ξ` it fixes. -/
theorem exists_orthogonal_cyclic_family (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsVNSubalgebra (H →L[ℂ] H) SA) :
    ∃ E : Set (H →L[ℂ] H),
      (∀ e ∈ E, IsStarProjection e ∧ e ∈ vnComm SA ∧
        ∃ ξ : H, e ξ = ξ ∧
          {y : H | e y = y} = closure {y : H | ∃ a ∈ SA, y = a ξ}) ∧
      (∀ e ∈ E, ∀ f ∈ E, e ≠ f → e * f = 0) ∧ projSup E = 1 := by
  obtain ⟨E, hgood, horth, hsup⟩ :=
    exists_orthogonal_separating_family (vnComm SA) (isVNSubalgebra_vnComm SA)
  refine ⟨E, fun e he => ?_, horth, hsup⟩
  obtain ⟨hproj, hmem, _, ξ, hξ, _, hsep⟩ := hgood e he
  refine ⟨hproj, hmem, ξ, hξ, ?_⟩
  have h := range_eq_closure_of_separating (isVNSubalgebra_vnComm SA) hproj hmem hξ hsep
  rwa [vnComm_vnComm SA hA] at h

/-- **The net of cuts.**  For a von Neumann subalgebra `𝒜 ⊆ B(ℋ)` there is
a set `E` of orthogonal projections of `𝒜^□` whose finite partial sums
form a monotone net of projections of `𝒜^□` with supremum `1`, and whose
corner algebras `𝒜_{e_F} ⊆ B(e_Fℋ)` are all **finitely cyclic**. -/
theorem exists_cut_net (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsVNSubalgebra (H →L[ℂ] H) SA) :
    ∃ (E : Set (H →L[ℂ] H))
      (he : ∀ F : Finset ↥E, IsStarProjection (∑ i ∈ F, (i : H →L[ℂ] H)))
      (hemem : ∀ F : Finset ↥E, (∑ i ∈ F, (i : H →L[ℂ] H)) ∈ vnComm SA),
      Monotone (fun F : Finset ↥E => ∑ i ∈ F, (i : H →L[ℂ] H)) ∧
      IsLUB (Set.range fun F : Finset ↥E => ∑ i ∈ F, (i : H →L[ℂ] H)) 1 ∧
      ∀ F : Finset ↥E, HasFinCyclic
        ((cornerAlg (cornerRep _ (he F)).isCorner SA (hemem F) :
          StarSubalgebra ℂ (Cnr _ (he F) →L[ℂ] Cnr _ (he F))) :
          Set (Cnr _ (he F) →L[ℂ] Cnr _ (he F))) := by
  classical
  obtain ⟨E, hgood, horth, hsup⟩ := exists_orthogonal_cyclic_family SA hA
  have hg : ∀ i : ↥E, IsStarProjection (i : H →L[ℂ] H) ∧ (i : H →L[ℂ] H) ∈ vnComm SA ∧
      ∃ ξ : H, (i : H →L[ℂ] H) ξ = ξ ∧
        {y : H | (i : H →L[ℂ] H) y = y}
          = closure {y : H | ∃ a ∈ SA, y = a ξ} := fun i => hgood i i.2
  choose ξ hξfix hξran using fun i : ↥E => (hg i).2.2
  have hproj : ∀ i : ↥E, IsStarProjection (i : H →L[ℂ] H) := fun i => (hg i).1
  have horth' : ∀ i j : ↥E, i ≠ j → (i : H →L[ℂ] H) * (j : H →L[ℂ] H) = 0 := by
    intro i j hij
    exact horth i i.2 j j.2 fun h => hij (Subtype.ext h)
  have hrange : (Set.range fun i : ↥E => (i : H →L[ℂ] H)) = E := Subtype.range_coe
  have hsup' : projSup (Set.range fun i : ↥E => (i : H →L[ℂ] H)) = 1 := by
    rw [hrange]; exact hsup
  obtain ⟨hFproj, hFmono, hFlub⟩ :=
    isLUB_range_finsetSum (fun i : ↥E => (i : H →L[ℂ] H)) hproj horth' hsup'
  have hFmem : ∀ F : Finset ↥E, (∑ i ∈ F, (i : H →L[ℂ] H)) ∈ vnComm SA := fun F =>
    sum_mem fun i _ => (hg i).2.1
  refine ⟨E, hFproj, hFmem, hFmono, hFlub, fun F => ?_⟩
  refine hasFinCyclic_cornerAlg _ _ F (fun i => (i : H →L[ℂ] H))
    (fun i _ => hproj i) ξ rfl ?_ (fun i _ => hξran i)
  intro i hi
  have hzero : ∀ j ∈ F, j ≠ i → (j : H →L[ℂ] H) (ξ i) = 0 := by
    intro j _ hji
    have h := congrArg (fun T : H →L[ℂ] H => T (ξ i)) (horth' j i hji)
    simp only [clm_mul_apply] at h
    rw [hξfix i] at h
    simpa using h
  have hap : (∑ j ∈ F, (j : H →L[ℂ] H)) (ξ i) = ∑ j ∈ F, (j : H →L[ℂ] H) (ξ i) := by
    simp
  rw [hap, Finset.sum_eq_single_of_mem i hi hzero, hξfix i]

end Net

/-! ## The capstone -/

section Capstone

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **The amplify-and-cut reduction, assembled.**  If the commutation
theorem holds for every pair of von Neumann subalgebras admitting a
*finite jointly cyclic family* of vectors, then it holds for **all** pairs
of von Neumann subalgebras `𝒜 ⊆ B(ℋ)`, `ℬ ⊆ B(𝒦)`.

The proof is the whole chain: `exists_orthogonal_separating_family`
(Zorn) → `range_eq_closure_of_separating` (each cut is a cyclic
projection) → `isLUB_range_finsetSum` (finite sums increase to `1`) →
`hasFinCyclic_cornerAlg` (the corner at a finite sum is finitely cyclic)
→ `relCT_of_CT` and `CT_of_relCT` (cutting), packaged as
`CT_of_CT_corner`.

See the file header for why the hypothesis is finite joint cyclicity and
not "cyclic and separating". -/
theorem CT_of_CT_finCyclic
    (hyp : ∀ {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
        [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
        [CompleteSpace F] (X : StarSubalgebra ℂ (E →L[ℂ] E))
        (Y : StarSubalgebra ℂ (F →L[ℂ] F)),
        HasFinCyclic (X : Set (E →L[ℂ] E)) → HasFinCyclic (Y : Set (F →L[ℂ] F)) →
        CT X Y)
    {SA : StarSubalgebra ℂ (H →L[ℂ] H)} {SB : StarSubalgebra ℂ (K →L[ℂ] K)}
    (hA : IsVNSubalgebra (H →L[ℂ] H) SA) (hB : IsVNSubalgebra (K →L[ℂ] K) SB) :
    CT SA SB := by
  classical
  obtain ⟨E, he, hemem, hemono, helub, hecyc⟩ := exists_cut_net SA hA
  obtain ⟨F, hf, hfmem, hfmono, hflub, hfcyc⟩ := exists_cut_net SB hB
  exact CT_of_CT_corner _ he hemem hemono helub _ hf hfmem hfmono hflub
    fun i j => hyp _ _ (hecyc i) (hfcyc j)

end Capstone

end Theses.A.Proc
