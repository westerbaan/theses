/-
Thesis A, chapter "Assorted Structure in W*_cpsu" (proc.tex): the
reduction of the **commutation theorem** `(𝒜 ⊗̄ ℬ)^□ = 𝒜^□ ⊗̄ ℬ^□`
(Takesaki I, Thm IV.5.9 — equivalently 121II `intersection_tensor`) to
the case where cyclic and separating vectors are available.

Nothing here is modular theory.  The file collects the *elementary* von
Neumann algebra theory that every route to the commutation theorem
consumes:

* `vnComm`, the commutant of a von Neumann subalgebra of `B(ℋ)` as a
  bundled `StarSubalgebra`, with `vnComm_vnComm` (88VI in bundled form);
* `CT`, the statement of the commutation theorem for a pair of von
  Neumann subalgebras;
* the **reduction theorem** `(R_p)^□ = (R^□)_p` for a projection
  `p ∈ R^□`, in the form that never leaves `B(ℋ)`: the commutant of
  `R p` *inside the corner* `p B(ℋ) p` is `R^□ p`.  The proof is
  extension by zero;
* the **compression limit**: `p x p → x` ultraweakly along an increasing
  net of projections with supremum `1`, hence the cutting principle
  "if `p x p ∈ T` for a cofinal family of projections `p ∈ T` increasing
  to `1`, and `T` is ultraweakly closed, then `x ∈ T`";
* **σ-finite corners**: for a von Neumann subalgebra `M ⊆ B(ℋ)` and a
  unit vector `ξ`, the projection `e = [M^□ ξ]` onto `closure (M^□ ξ)`
  lies in `M`, is dominated by any projection of `M` fixing `ξ`, and `ξ`
  is *separating* for the corner `e M e`; and the Zorn argument that
  produces an orthogonal family of such `e` with supremum `1`.

See `docs/COMMUTATION-THEOREM.md` §4 for the route this file is a part
of.  The corner Hilbert space `eℋ` and the identification
`(e ⊗ f)(ℋ ⊗ 𝒦) ≅ eℋ ⊗ f𝒦`, without which the cutting step cannot be
*stated* for the tensor product, are `A/Proc/CornerTensor.lean`; the
reduction is run over a net of cuts in `A/Proc/CommutationReduction.lean`
and carried to the cyclic-and-separating case by
`CommutationAmplify.lean`, `Compression.lean` and
`CommutationCyclic.lean`; the unconditional theorem is
`A/Proc/CommutationTheorem.lean`.
-/
import Theses.A.Proc.Tensor

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
  TensorProduct ENNReal
open Filter Topology Theses Theses.A.VN

noncomputable section

namespace Theses.A.Proc

universe u

/-! ## The commutant as a bundled von Neumann subalgebra -/

section BundledCommutant

variable {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The commutant `S^□` of a ∗-subalgebra `S ⊆ B(ℋ)`, bundled as a
`StarSubalgebra`.  (`commutant` itself is a `Set`; `commutant_basic_3'`
supplies the algebra structure, but only through an existential.) -/
def vnComm (S : StarSubalgebra ℂ (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  ((commutant_basic_3' (S : Set (H →L[ℂ] H)) (fun _ ha => star_mem ha)).1).choose

@[simp] theorem coe_vnComm (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (vnComm S : Set (H →L[ℂ] H)) = commutant (H →L[ℂ] H) (S : Set (H →L[ℂ] H)) :=
  ((commutant_basic_3' (S : Set (H →L[ℂ] H)) (fun _ ha => star_mem ha)).1).choose_spec.2

theorem isVNSubalgebra_vnComm (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    IsVNSubalgebra (H →L[ℂ] H) (vnComm S) :=
  ((commutant_basic_3' (S : Set (H →L[ℂ] H)) (fun _ ha => star_mem ha)).1).choose_spec.1

theorem mem_vnComm {S : StarSubalgebra ℂ (H →L[ℂ] H)} {x : H →L[ℂ] H} :
    x ∈ vnComm S ↔ ∀ s ∈ S, s * x = x * s := by
  have h : x ∈ (vnComm S : Set (H →L[ℂ] H)) ↔
      x ∈ commutant (H →L[ℂ] H) (S : Set (H →L[ℂ] H)) := by rw [coe_vnComm]
  exact h

theorem mul_comm_of_mem_vnComm {S : StarSubalgebra ℂ (H →L[ℂ] H)} {x : H →L[ℂ] H}
    (hx : x ∈ vnComm S) {s : H →L[ℂ] H} (hs : s ∈ S) : s * x = x * s :=
  mem_vnComm.mp hx s hs

theorem vnComm_antitone {S T : StarSubalgebra ℂ (H →L[ℂ] H)} (h : S ≤ T) :
    vnComm T ≤ vnComm S := by
  intro x hx
  exact mem_vnComm.mpr fun s hs => mem_vnComm.mp hx s (h hs)

theorem le_vnComm_vnComm (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    S ≤ vnComm (vnComm S) := by
  intro s hs
  refine mem_vnComm.mpr fun y hy => ?_
  exact (mem_vnComm.mp hy s hs).symm

/-- **88VI** in bundled form: `S^□□ = S` for a von Neumann subalgebra. -/
theorem vnComm_vnComm (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hS : IsVNSubalgebra (H →L[ℂ] H) S) : vnComm (vnComm S) = S := by
  refine SetLike.ext' ?_
  rw [coe_vnComm, coe_vnComm]
  have h := (double_commutant S).2.2
  rwa [wstar_eq_of_isVNSubalgebra S hS] at h

end BundledCommutant

/-! ## The reduction theorem, `(R_p)^□ = (R^□)_p`

For a projection `p` in the commutant of `R` the *reduced* algebra
`R_p = {x p : x ∈ R}` acts on `p ℋ`, and its commutant computed there is
`(R^□)_p`.  Nothing here needs the Hilbert space `p ℋ` as a separate
object: the statement is about the corner `p B(ℋ) p` of `B(ℋ)`, and the
proof is extension by zero (`y ↦ y ⊕ 0`, which is `y` itself once
`p y p = y`). -/

section Reduction

variable {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The corner `p R^□ p` of the commutant sits inside the commutant. -/
theorem mem_vnComm_of_corner {R : StarSubalgebra ℂ (H →L[ℂ] H)} {p : H →L[ℂ] H}
    (hpR : p ∈ vnComm R) {c : H →L[ℂ] H} (hc : c ∈ vnComm R) :
    p * c * p ∈ vnComm R := by
  refine mem_vnComm.mpr fun x hx => ?_
  have hxp : x * p = p * x := mem_vnComm.mp hpR x hx
  have hxc : x * c = c * x := mem_vnComm.mp hc x hx
  calc x * (p * c * p) = x * p * c * p := by noncomm_ring
    _ = p * x * c * p := by rw [hxp]
    _ = p * (x * c) * p := by noncomm_ring
    _ = p * (c * x) * p := by rw [hxc]
    _ = p * c * (x * p) := by noncomm_ring
    _ = p * c * (p * x) := by rw [hxp]
    _ = p * c * p * x := by noncomm_ring

/-- **The reduction theorem** `(R_p)^□ = (R^□)_p`, for a projection `p`
in the commutant of `R`, stated inside `B(ℋ)`: an operator `y` of the
corner `p B(ℋ) p` commutes with the reduced algebra `R_p = {x p : x ∈ R}`
if and only if it lies in `R^□`.

Both directions are two-line computations once `p y p = y` is unfolded to
`p y = y = y p`; the substance is that no extension step is needed —
`y ⊕ 0` *is* `y`. -/
theorem mem_vnComm_iff_comm_reduced {R : StarSubalgebra ℂ (H →L[ℂ] H)}
    {p : H →L[ℂ] H} (hp : p * p = p) (hpR : p ∈ vnComm R) {y : H →L[ℂ] H}
    (hy : p * y * p = y) :
    (∀ x ∈ R, (x * p) * y = y * (x * p)) ↔ y ∈ vnComm R := by
  have hyp : y * p = y := by
    calc y * p = p * y * p * p := by rw [hy]
      _ = p * y * (p * p) := by noncomm_ring
      _ = p * y * p := by rw [hp]
      _ = y := hy
  have hpy : p * y = y := by
    calc p * y = p * (p * y * p) := by rw [hy]
      _ = p * p * y * p := by noncomm_ring
      _ = p * y * p := by rw [hp]
      _ = y := hy
  constructor
  · intro h
    refine mem_vnComm.mpr fun x hx => ?_
    have hxp : x * p = p * x := mem_vnComm.mp hpR x hx
    calc x * y = x * (p * y) := by rw [hpy]
      _ = x * p * y := by noncomm_ring
      _ = y * (x * p) := h x hx
      _ = y * p * x := by rw [hxp]; noncomm_ring
      _ = y * x := by rw [hyp]
  · intro hyc x hx
    have hxy : x * y = y * x := mem_vnComm.mp hyc x hx
    calc x * p * y = x * (p * y) := by noncomm_ring
      _ = x * y := by rw [hpy]
      _ = y * x := hxy
      _ = y * p * x := by rw [hyp]
      _ = y * (p * x) := by noncomm_ring
      _ = y * (x * p) := by rw [mem_vnComm.mp hpR x hx]

end Reduction

/-! ## The commutation theorem as a statement, and its self-duality -/

section Statement

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `CT 𝒜 ℬ` is the **commutation theorem** for the pair `(𝒜, ℬ)`:
`(𝒜 ⊗̄ ℬ)^□ = 𝒜^□ ⊗̄ ℬ^□`, with `⊗̄` the concrete tensor product
`concreteTensor` (121II) and `(·)^□` the commutant.  Takesaki I, Thm
IV.5.9; 121II `intersection_tensor` is equivalent to it (see
`docs/COMMUTATION-THEOREM.md` §1). -/
def CT (SA : StarSubalgebra ℂ (H →L[ℂ] H)) (SB : StarSubalgebra ℂ (K →L[ℂ] K)) :
    Prop :=
  vnComm (concreteTensor H K SA SB) = concreteTensor H K (vnComm SA) (vnComm SB)

/-- The Galois connection for the bundled commutant. -/
theorem le_vnComm_comm {S T : StarSubalgebra ℂ (H →L[ℂ] H)} :
    S ≤ vnComm T ↔ T ≤ vnComm S :=
  ⟨fun h _t ht => mem_vnComm.mpr fun _s hs => (mem_vnComm.mp (h hs) _t ht).symm,
    fun h _s hs => mem_vnComm.mpr fun _t ht => (mem_vnComm.mp (h ht) _s hs).symm⟩

/-- Two concrete tensor products commute as soon as their elementary
tensors do.  (Two applications of the universal property of `W*(-)`,
with the Galois connection in between.) -/
theorem concreteTensor_le_vnComm_concreteTensor
    {SA SC : StarSubalgebra ℂ (H →L[ℂ] H)} {SB SD : StarSubalgebra ℂ (K →L[ℂ] K)}
    (h : ∀ a ∈ SA, ∀ b ∈ SB, ∀ c ∈ SC, ∀ d ∈ SD,
      opTensor a b * opTensor c d = opTensor c d * opTensor a b) :
    concreteTensor H K SA SB ≤ vnComm (concreteTensor H K SC SD) := by
  -- Step 1: everything in `𝒜 ⊗̄ ℬ` commutes with each elementary tensor of
  -- `𝒞 ⊗̄ 𝒟`, because the commutant of the generating set is a von Neumann
  -- subalgebra containing the elementary tensors of `𝒜 ⊗̄ ℬ`.
  have hcomm : (vnComm (spatialSpan SC SD) : Set (HT H K →L[ℂ] HT H K))
      = commutant (HT H K →L[ℂ] HT H K)
          {x : HT H K →L[ℂ] HT H K | ∃ c ∈ SC, ∃ d ∈ SD, x = opTensor c d} := by
    rw [coe_vnComm, coe_spatialSpan, commutant_span]
  have hstep1 : concreteTensor H K SA SB ≤ vnComm (spatialSpan SC SD) := by
    refine concreteTensor_le (isVNSubalgebra_vnComm _) fun a ha b hb => ?_
    have : opTensor a b ∈ (vnComm (spatialSpan SC SD) : Set (HT H K →L[ℂ] HT H K)) := by
      rw [hcomm]
      rintro _ ⟨c, hc, d, hd, rfl⟩
      exact (h a ha b hb c hc d hd).symm
    exact this
  -- Step 2: hence each such elementary tensor lies in `(𝒜 ⊗̄ ℬ)^□`, so all of
  -- `𝒞 ⊗̄ 𝒟` does; the Galois connection turns that around.
  refine le_vnComm_comm.mpr (concreteTensor_le (isVNSubalgebra_vnComm _) ?_)
  intro c hc d hd
  refine mem_vnComm.mpr fun s hs => ?_
  have hs' : s ∈ (vnComm (spatialSpan SC SD) : Set (HT H K →L[ℂ] HT H K)) := hstep1 hs
  rw [hcomm] at hs'
  exact (hs' _ ⟨c, hc, d, hd, rfl⟩).symm

/-- The easy half of the commutation theorem: `𝒜^□ ⊗̄ ℬ^□ ⊆ (𝒜 ⊗̄ ℬ)^□`. -/
theorem concreteTensor_vnComm_le (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K)) :
    concreteTensor H K (vnComm SA) (vnComm SB) ≤ vnComm (concreteTensor H K SA SB) :=
  concreteTensor_le_vnComm_concreteTensor fun a ha b hb c hc d hd => by
    rw [← opTensor_mul, ← opTensor_mul, mul_comm_of_mem_vnComm ha hc,
      mul_comm_of_mem_vnComm hb hd]

/-- **Step 0**: `CT(𝒜,ℬ)` implies `CT(𝒜^□,ℬ^□)` — take commutants of both
sides and use the double commutant theorem. -/
theorem CT_vnComm {SA : StarSubalgebra ℂ (H →L[ℂ] H)}
    {SB : StarSubalgebra ℂ (K →L[ℂ] K)}
    (hA : IsVNSubalgebra (H →L[ℂ] H) SA) (hB : IsVNSubalgebra (K →L[ℂ] K) SB)
    (h : CT SA SB) : CT (vnComm SA) (vnComm SB) := by
  have h0 : vnComm (concreteTensor H K SA SB)
      = concreteTensor H K (vnComm SA) (vnComm SB) := h
  have h1 := congrArg vnComm h0
  rw [vnComm_vnComm _ (isVNSubalgebra_concreteTensor SA SB)] at h1
  show vnComm (concreteTensor H K (vnComm SA) (vnComm SB))
      = concreteTensor H K (vnComm (vnComm SA)) (vnComm (vnComm SB))
  rw [← h1, vnComm_vnComm _ hA, vnComm_vnComm _ hB]

/-- `CT(𝒜,ℬ) ↔ CT(𝒜^□,ℬ^□)`.

*On the record only.*  Neither this nor its feeder `CT_vnComm` has a consumer
anywhere in `Theses/`: the reduction runs on `CT_comm` and
`CT_iff_bicommutant`, and since `commutation_theorem` is unconditional both
sides of this iff are theorems.  See `docs/DEAD-LIMBS.md` §7. -/
theorem CT_iff_vnComm {SA : StarSubalgebra ℂ (H →L[ℂ] H)}
    {SB : StarSubalgebra ℂ (K →L[ℂ] K)}
    (hA : IsVNSubalgebra (H →L[ℂ] H) SA) (hB : IsVNSubalgebra (K →L[ℂ] K) SB) :
    CT SA SB ↔ CT (vnComm SA) (vnComm SB) := by
  refine ⟨CT_vnComm hA hB, fun h => ?_⟩
  have h2 := CT_vnComm (isVNSubalgebra_vnComm SA) (isVNSubalgebra_vnComm SB) h
  rwa [vnComm_vnComm _ hA, vnComm_vnComm _ hB] at h2

/-- `CT(𝒜,ℬ)` unfolds to the one inclusion that has content: the easy
inclusion `𝒜^□ ⊗̄ ℬ^□ ⊆ (𝒜 ⊗̄ ℬ)^□` is `concreteTensor_vnComm_le`. -/
theorem CT_iff_le (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K)) :
    CT SA SB ↔
      vnComm (concreteTensor H K SA SB) ≤ concreteTensor H K (vnComm SA) (vnComm SB) :=
  ⟨fun h => le_of_eq h, fun h => le_antisymm h (concreteTensor_vnComm_le SA SB)⟩

end Statement

/-! ## Compression along an increasing net of projections

The cutting step of the reduction needs: if `p_i ↑ 1` is an increasing net
of projections and `p_i x p_i` lies in an ultraweakly closed set `T` for
every `i`, then `x ∈ T`.  Ultraweak convergence `p_i → 1` alone does not
give `p_i x p_i → x` — multiplication is not jointly ultraweakly
continuous — but for a monotone net of *projections* Cauchy–Schwarz
(**43I**.1, `norm_apply_star_mul_le`) does it, with
`‖1 − p_i‖_ω = ω(1 − p_i)^{1/2} → 0` as the only estimate.

Both ingredients — `uwTendsto_of_isLUB` (a repackaging of **44VI**
`vna_supremum_uwlimit`) and `uw_compress_tendsto` itself — live in
`A/Proc/Tensor.lean` and are used from here directly rather than copied. -/

section Compression

variable {X : Type u} [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [VonNeumannAlgebra X]

/-- **The cutting principle.**  Let `(p_i)` be a monotone net of
projections with supremum `1`.  Any `x` all of whose compressions
`p_i x p_i` lie in an ultraweakly closed set `T` lies in `T`. -/
theorem mem_of_compress_mem {ι' : Type*} [Nonempty ι'] [Preorder ι']
    [IsDirected ι' (· ≤ ·)] (P : ι' → X) (hP : ∀ i, IsStarProjection (P i))
    (hmono : Monotone P) (hlub : IsLUB (Set.range P) 1) {T : Set X}
    (hT : @IsClosed X (ultraweak X) T) {x : X} (hmem : ∀ i, P i * x * P i ∈ T) :
    x ∈ T := by
  let _ : TopologicalSpace X := ultraweak X
  have hsub : ∀ i, (1 - P i) * (1 - P i) = 1 - P i := fun i => by
    have hpp : P i * P i = P i := (hP i).isIdempotentElem
    calc (1 - P i) * (1 - P i) = 1 - P i - P i + P i * P i := by noncomm_ring
      _ = 1 - P i := by rw [hpp]; abel
  have hsubsa : ∀ i, star (1 - P i) = 1 - P i := fun i => by
    have h : star (P i) = P i := (hP i).isSelfAdjoint
    rw [star_sub, star_one, h]
  have hstar : ∀ i, star ((1 : X) - P i) * (1 - P i) = 1 - P i := fun i => by
    rw [hsubsa i, hsub i]
  have hle : ∀ i, P i ≤ (1 : X) := fun i => by
    have h0 : (0 : X) ≤ star ((1 : X) - P i) * (1 - P i) := star_mul_self_nonneg _
    rw [hstar i] at h0
    exact sub_nonneg.mp h0
  have huw : UWTendsto P atTop (1 : X) :=
    uwTendsto_of_isLUB P 1 (fun i => (hP i).isSelfAdjoint) hmono hlub
  have hcomp := uw_compress_tendsto (1 : X) P
    (fun i => by rw [(hP i).isSelfAdjoint]; exact (hP i).isIdempotentElem)
    hstar hle huw x
  rw [one_mul, mul_one] at hcomp
  exact hT.mem_of_tendsto hcomp (Filter.Eventually.of_forall hmem)

end Compression

/-! ## Separating vectors and σ-finite corners

**Step 2 of the reduction.**  Every nonzero projection `p ∈ M` dominates
a projection `e ∈ M` whose corner `e M e` has a *separating vector*: take
a unit vector `ξ ∈ p ℋ` and put `e = [M^□ ξ]`, the projection onto
`closure (M^□ ξ)`, which lies in `M^□□ = M` by **88IV**
`exists_cyclic_projection`.

A separating vector is stronger than σ-finiteness (which is all the
classical argument extracts from it), and getting one directly is what
makes the passage to a cyclic *and* separating vector cheap: see
`cyclic_and_separating_of_separating` below. -/

section Separating

variable {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem clm_mul_apply (a b : H →L[ℂ] H) (x : H) : (a * b) x = a (b x) := rfl

/-- `ξ` is **separating** for a set `S` of operators: no nonzero member of
`S` kills `ξ`. -/
def SeparatingFor (S : Set (H →L[ℂ] H)) (ξ : H) : Prop :=
  ∀ x ∈ S, x ξ = 0 → x = 0

/-- The compression `q S q = {q x q : x ∈ S}`.  (Not `cornerSet`, which is
the fixed-point description `{a | q a q = a}` of `A/Proc/Measurement.lean`
and does not remember `S`.) -/
def compressedSet (q : H →L[ℂ] H) (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  {y : H →L[ℂ] H | ∃ x ∈ S, y = q * x * q}

/-- The reduction `S_q = {x q : x ∈ S}` (used when `q` lies in `S^□`). -/
def reducedSet (q : H →L[ℂ] H) (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  {y : H →L[ℂ] H | ∃ x ∈ S, y = x * q}

omit [CompleteSpace H] in
/-- The fixed-point set of a projection is closed. -/
theorem isClosed_fixed (p : H →L[ℂ] H) : IsClosed {y : H | p y = y} :=
  isClosed_eq p.continuous continuous_id

/-- **Step 2.**  For a von Neumann subalgebra `M ⊆ B(ℋ)` and a vector `ξ`,
the projection `e = [M^□ ξ]` onto `closure (M^□ ξ)` lies in `M`, fixes
`ξ`, is dominated by every projection of `M` fixing `ξ` (in the form
`p e = e`), and `ξ` is separating for the corner `e M e`. -/
theorem exists_separating_corner (M : StarSubalgebra ℂ (H →L[ℂ] H))
    (hM : IsVNSubalgebra (H →L[ℂ] H) M) (ξ : H) :
    ∃ e : H →L[ℂ] H, IsStarProjection e ∧ e ∈ M ∧ e ξ = ξ ∧
      SeparatingFor (compressedSet e (M : Set (H →L[ℂ] H))) ξ ∧
      (∀ p : H →L[ℂ] H, p ∈ M → p ξ = ξ → p * e = e) := by
  obtain ⟨q, hqproj, hqcomm, hqξ, hfix⟩ :=
    exists_cyclic_projection (vnComm M) ξ
  -- `q ∈ (M^□)^□ = M`
  have hqcc : q ∈ vnComm (vnComm M) := by
    have h1 : q ∈ (vnComm (vnComm M) : Set (H →L[ℂ] H)) := by
      rw [coe_vnComm]; exact hqcomm
    exact h1
  have hqM : q ∈ M := by rwa [vnComm_vnComm M hM] at hqcc
  -- `q` commutes with `M^□`
  have hqy : ∀ y ∈ vnComm M, y * q = q * y := fun y hy => mem_vnComm.mp hqcc y hy
  have hqq : q * q = q := hqproj.isIdempotentElem
  have hqfix : ∀ w : H, q (q w) = q w := fun w => by
    rw [← clm_mul_apply, hqq]
  refine ⟨q, hqproj, hqM, hqξ, ?_, ?_⟩
  · -- `ξ` is separating for `q M q`
    rintro _ ⟨x, hx, rfl⟩ h0
    have h3 : q (x ξ) = 0 := by
      have h2 : (q * x * q) ξ = q (x ξ) := by
        rw [clm_mul_apply, clm_mul_apply, hqξ]
      rw [← h2]; exact h0
    have hkill : ∀ y ∈ vnComm M, (q * x * q) (y ξ) = 0 := by
      intro y hy
      have hxy : x * y = y * x := mem_vnComm.mp hy x hx
      have h1 : q (y ξ) = y ξ := by
        have h := congrArg (fun T : H →L[ℂ] H => T ξ) (hqy y hy)
        simp only [clm_mul_apply] at h
        rw [← h, hqξ]
      have hcomm1 : x (y ξ) = y (x ξ) := by
        have h := congrArg (fun T : H →L[ℂ] H => T ξ) hxy
        simpa only [clm_mul_apply] using h
      have hcomm2 : q (y (x ξ)) = y (q (x ξ)) := by
        have h := congrArg (fun T : H →L[ℂ] H => T (x ξ)) (hqy y hy)
        simpa only [clm_mul_apply] using h.symm
      calc (q * x * q) (y ξ) = q (x (q (y ξ))) := by
            rw [clm_mul_apply, clm_mul_apply]
        _ = q (x (y ξ)) := by rw [h1]
        _ = q (y (x ξ)) := by rw [hcomm1]
        _ = y (q (x ξ)) := hcomm2
        _ = 0 := by rw [h3, map_zero]
    -- hence `q x q` vanishes on `closure (M^□ ξ) = ran q`
    have hzero : ∀ z : H, q z = z → (q * x * q) z = 0 := by
      intro z hz
      have hzmem : z ∈ closure {y : H | ∃ T ∈ vnComm M, y = T ξ} := by
        rw [← hfix]; exact hz
      have hcl : IsClosed {z : H | (q * x * q) z = 0} :=
        isClosed_eq (q * x * q).continuous continuous_const
      refine hcl.closure_subset (closure_mono ?_ hzmem)
      rintro _ ⟨T, hT, rfl⟩
      exact hkill T hT
    ext w
    have h5 : (q * x * q) w = (q * x * q) (q w) := by
      rw [clm_mul_apply, clm_mul_apply, clm_mul_apply, clm_mul_apply, hqfix w]
    rw [h5, hzero _ (hqfix w)]
    rfl
  · -- `p q = q` for every projection `p ∈ M` fixing `ξ`
    intro p hpM hpξ
    have hsub : closure {y : H | ∃ T ∈ vnComm M, y = T ξ} ⊆ {y : H | p y = y} := by
      refine (isClosed_fixed p).closure_subset_iff.mpr ?_
      rintro _ ⟨T, hT, rfl⟩
      have hTp : T * p = p * T := mem_vnComm.mp (le_vnComm_vnComm M hpM) T hT
      have h := congrArg (fun L : H →L[ℂ] H => L ξ) hTp
      simp only [clm_mul_apply] at h
      show p (T ξ) = T ξ
      rw [← h, hpξ]
    ext w
    have hmem : q w ∈ closure {y : H | ∃ T ∈ vnComm M, y = T ξ} := by
      rw [← hfix]; exact hqfix w
    have h := hsub hmem
    show p (q w) = q w
    exact h

/-- If `ξ` is separating for `M` then, for `f = [M ξ] ∈ M^□`, the vector
`ξ` is **cyclic and separating** for the reduction `M_f = {x f : x ∈ M}`.

This is the whole of step 3 of the reduction when a separating vector is
already available — no amplification by `ℓ²(ℕ)` and no σ-finiteness are
needed.  (Cyclicity is the defining property of `f = [M ξ]`; separation
is inherited because `f ξ = ξ`.) -/
theorem cyclic_and_separating_of_separating (M : StarSubalgebra ℂ (H →L[ℂ] H))
    {ξ : H} (hsep : SeparatingFor (M : Set (H →L[ℂ] H)) ξ) :
    ∃ f : H →L[ℂ] H, IsStarProjection f ∧ f ∈ vnComm M ∧ f ξ = ξ ∧
      {y : H | f y = y}
          = closure {y : H | ∃ x ∈ reducedSet f (M : Set (H →L[ℂ] H)), y = x ξ} ∧
      SeparatingFor (reducedSet f (M : Set (H →L[ℂ] H))) ξ := by
  obtain ⟨f, hfproj, hfcomm, hfξ, hfix⟩ := exists_cyclic_projection M ξ
  have hfM : f ∈ vnComm M := by
    have h : f ∈ (vnComm M : Set (H →L[ℂ] H)) := by rw [coe_vnComm]; exact hfcomm
    exact h
  refine ⟨f, hfproj, hfM, hfξ, ?_, ?_⟩
  · rw [hfix]
    congr 1
    ext y
    constructor
    · rintro ⟨T, hT, rfl⟩
      exact ⟨T * f, ⟨T, hT, rfl⟩, by rw [clm_mul_apply, hfξ]⟩
    · rintro ⟨_, ⟨T, hT, rfl⟩, rfl⟩
      exact ⟨T, hT, by rw [clm_mul_apply, hfξ]⟩
  · rintro _ ⟨x, hx, rfl⟩ h0
    have h1 : x ξ = 0 := by
      have h : (x * f) ξ = x ξ := by rw [clm_mul_apply, hfξ]
      rw [← h]; exact h0
    rw [hsep x hx h1, zero_mul]

end Separating

/-! ## Amplification: the commutant of `M ⊗̄ B(𝒦)`, and cancellation

Step 4 of the reduction needs `𝒜 ⊗̄ B(L) = 𝒞 ⊗̄ B(L) ⟹ 𝒜 = 𝒞`.  With the
amplification theorem in the tree this is short: the commutant of
`M ⊗̄ B(𝒦)` is `{a ⊗ 1 : a ∈ M^□}`, and `a ↦ a ⊗ 1` is injective. -/

section Amplification

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The generating set of `concreteTensor H K M ⊤` is `{a ⊗ b : a ∈ M}`. -/
theorem concreteTensor_top_gen (M : StarSubalgebra ℂ (H →L[ℂ] H)) :
    {x : HT H K →L[ℂ] HT H K |
        ∃ a ∈ M, ∃ b ∈ (⊤ : StarSubalgebra ℂ (K →L[ℂ] K)), x = opTensor a b}
      = {x : HT H K →L[ℂ] HT H K | ∃ a ∈ (M : Set (H →L[ℂ] H)),
          ∃ b : K →L[ℂ] K, x = opTensor a b} := by
  ext x
  exact ⟨fun ⟨a, ha, b, _, h⟩ => ⟨a, ha, b, h⟩,
    fun ⟨a, ha, b, h⟩ => ⟨a, ha, b, StarSubalgebra.mem_top, h⟩⟩

/-- `M ⊗̄ B(𝒦)` is the double commutant of its generating set. -/
theorem coe_concreteTensor_top (M : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (concreteTensor H K M (⊤ : StarSubalgebra ℂ (K →L[ℂ] K)) :
        Set (HT H K →L[ℂ] HT H K))
      = commutant (HT H K →L[ℂ] HT H K)
          (commutant (HT H K →L[ℂ] HT H K)
            {x : HT H K →L[ℂ] HT H K | ∃ a ∈ (M : Set (H →L[ℂ] H)),
              ∃ b : K →L[ℂ] K, x = opTensor a b}) := by
  have hdc := (double_commutant (spatialSpan M (⊤ : StarSubalgebra ℂ (K →L[ℂ] K)))).2.2
  rw [wstar_spatialSpan M (⊤ : StarSubalgebra ℂ (K →L[ℂ] K))] at hdc
  rw [coe_spatialSpan, commutant_span] at hdc
  rw [concreteTensor_top_gen M] at hdc
  rw [concreteTensor_def, concreteTensor_top_gen M]
  exact hdc.symm

/-- **The commutant of an amplification**: `(M ⊗̄ B(𝒦))^□ = M^□ ⊗ 1`. -/
theorem commutant_concreteTensor_top (M : StarSubalgebra ℂ (H →L[ℂ] H))
    (hM : IsVNSubalgebra (H →L[ℂ] H) M) :
    commutant (HT H K →L[ℂ] HT H K)
        ((concreteTensor H K M (⊤ : StarSubalgebra ℂ (K →L[ℂ] K)) :
          StarSubalgebra ℂ (HT H K →L[ℂ] HT H K)) : Set (HT H K →L[ℂ] HT H K))
      = {z : HT H K →L[ℂ] HT H K |
          ∃ a ∈ commutant (H →L[ℂ] H) (M : Set (H →L[ℂ] H)),
            z = opTensor a (1 : K →L[ℂ] K)} := by
  have hamp := amplification_commutant (K := K) (vnComm M) (isVNSubalgebra_vnComm M)
  have hMdc : commutant (H →L[ℂ] H)
      ((vnComm M : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H))
      = (M : Set (H →L[ℂ] H)) := by
    rw [coe_vnComm]
    have h := (double_commutant M).2.2
    rwa [wstar_eq_of_isVNSubalgebra M hM] at h
  rw [hMdc, coe_vnComm] at hamp
  have h3 := (commutant_basic_1 (A := HT H K →L[ℂ] HT H K)
    {x : HT H K →L[ℂ] HT H K | ∃ a ∈ (M : Set (H →L[ℂ] H)),
      ∃ b : K →L[ℂ] K, x = opTensor a b}
    {x : HT H K →L[ℂ] HT H K | ∃ a ∈ (M : Set (H →L[ℂ] H)),
      ∃ b : K →L[ℂ] K, x = opTensor a b}).2.2.2
  rw [coe_concreteTensor_top M, h3, ← hamp]

end Amplification

/-! ## The Zorn step: an orthogonal family of separating corners

Iterating `exists_separating_corner` with Zorn's lemma produces a maximal
orthogonal family `{e_i} ⊆ M` of nonzero projections, each of whose corners
`e_i M e_i` has a separating vector, and with `⋃ e_i = 1`.  Maximality is
turned into `⋃ e_i = 1` through the Hilbert space: a vector killed by every
`e_i` would produce a further, orthogonal, `e = [M^□ ξ]`. -/

section ZornFamily

variable {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Step 2, completed.**  Every von Neumann subalgebra `M ⊆ B(ℋ)` carries
an orthogonal family of nonzero projections with supremum `1`, each of
whose corners has a separating vector. -/
theorem exists_orthogonal_separating_family (M : StarSubalgebra ℂ (H →L[ℂ] H))
    (hM : IsVNSubalgebra (H →L[ℂ] H) M) :
    ∃ E : Set (H →L[ℂ] H),
      (∀ e ∈ E, IsStarProjection e ∧ e ∈ M ∧ e ≠ 0 ∧
        ∃ ξ : H, e ξ = ξ ∧ ξ ≠ 0 ∧
          SeparatingFor (compressedSet e (M : Set (H →L[ℂ] H))) ξ) ∧
      (∀ e ∈ E, ∀ f ∈ E, e ≠ f → e * f = 0) ∧
      projSup E = 1 := by
  classical
  set good : Set (H →L[ℂ] H) := {e : H →L[ℂ] H | IsStarProjection e ∧ e ∈ M ∧ e ≠ 0 ∧
    ∃ ξ : H, e ξ = ξ ∧ ξ ≠ 0 ∧
      SeparatingFor (compressedSet e (M : Set (H →L[ℂ] H))) ξ} with hgood
  set Fam : Set (Set (H →L[ℂ] H)) :=
    {E : Set (H →L[ℂ] H) | E ⊆ good ∧ ∀ e ∈ E, ∀ f ∈ E, e ≠ f → e * f = 0} with hP
  -- chains have upper bounds
  have hchain : ∀ c ⊆ Fam, IsChain (· ⊆ ·) c → ∃ ub ∈ Fam, ∀ t ∈ c, t ⊆ ub := by
    intro c hc hcc
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun t ht => Set.subset_sUnion_of_mem ht⟩
    · rintro e ⟨t, ht, het⟩
      exact (hc ht).1 het
    · rintro e ⟨t, ht, het⟩ f ⟨t', ht', hft'⟩ hef
      rcases hcc.total ht ht' with h | h
      · exact (hc ht').2 e (h het) f hft' hef
      · exact (hc ht).2 e het f (h hft') hef
  obtain ⟨E, hEmax⟩ := zorn_subset Fam hchain
  obtain ⟨hEgood, hEorth⟩ := hEmax.prop
  have hEproj : ∀ e ∈ E, IsStarProjection e := fun e he => (hEgood he).1
  -- maximality: no nonzero vector is killed by all of `E`
  have hker : ∀ ξ : H, (∀ e ∈ E, e ξ = 0) → ξ = 0 := by
    intro ξ hξ
    by_contra hξ0
    obtain ⟨e₀, he₀proj, he₀M, he₀ξ, he₀sep, he₀dom⟩ :=
      exists_separating_corner M hM ξ
    have he₀ne : e₀ ≠ 0 := by
      intro h
      apply hξ0
      rw [← he₀ξ, h]
      rfl
    -- `e₀` is orthogonal to every member of `E`
    have horth : ∀ e ∈ E, e * e₀ = 0 := by
      intro e he
      have h1 : (1 - e) ∈ M := sub_mem (one_mem M) (hEgood he).2.1
      have h2 : ((1 : H →L[ℂ] H) - e) ξ = ξ := by
        have : ((1 : H →L[ℂ] H) - e) ξ = ξ - e ξ := rfl
        rw [this, hξ e he, sub_zero]
      have h3 := he₀dom (1 - e) h1 h2
      have hexp : ((1 : H →L[ℂ] H) - e) * e₀ = e₀ - e * e₀ := by
        rw [sub_mul, one_mul]
      have h4 : e₀ - e * e₀ = e₀ := by rw [← hexp]; exact h3
      have h5 : e * e₀ = 0 := by
        have := sub_eq_self.mp h4
        exact this
      exact h5
    have he₀notin : e₀ ∉ E := by
      intro h
      have := horth e₀ h
      rw [he₀proj.isIdempotentElem] at this
      exact he₀ne this
    have hmem : E ∪ {e₀} ∈ Fam := by
      refine ⟨?_, ?_⟩
      · rintro e (he | he)
        · exact hEgood he
        · rw [Set.mem_singleton_iff] at he
          subst he
          exact ⟨he₀proj, he₀M, he₀ne, ξ, he₀ξ, hξ0, he₀sep⟩
      · rintro e (he | he) f (hf | hf) hef
        · exact hEorth e he f hf hef
        · rw [Set.mem_singleton_iff] at hf
          subst hf
          have := horth e he
          exact this
        · rw [Set.mem_singleton_iff] at he
          subst he
          have hstar := congrArg star (horth f hf)
          rw [star_mul, star_zero, he₀proj.isSelfAdjoint, (hEgood hf).1.isSelfAdjoint] at hstar
          exact hstar
        · rw [Set.mem_singleton_iff] at he hf
          exact absurd (he.trans hf.symm) hef
    have hsub := hEmax.le_of_ge (y := E ∪ {e₀}) hmem Set.subset_union_left
    exact he₀notin (hsub (Or.inr rfl))
  -- and therefore `⋃ E = 1`
  refine ⟨E, hEgood, hEorth, ?_⟩
  obtain ⟨hsproj, hsub, hsleast⟩ := projSup_spec hEproj
  have hs1 : projSup E ≤ 1 :=
    hsleast 1 (IsStarProjection.one _) fun p hp => (hEproj p hp).le_one
  have hcomp : ∀ e ∈ E, e * (1 - projSup E) = 0 := by
    intro e he
    have h := ((hEproj e he).le_iff_mul_eq_left hsproj).mp (hsub e he)
    rw [mul_sub, mul_one, h, sub_self]
  have hzero : (1 : H →L[ℂ] H) - projSup E = 0 := by
    ext w
    have hkill : ∀ e ∈ E, e (((1 : H →L[ℂ] H) - projSup E) w) = 0 := by
      intro e he
      rw [← clm_mul_apply, hcomp e he]
      rfl
    rw [hker _ hkill]
    rfl
  have := sub_eq_zero.mp hzero
  exact this.symm

end ZornFamily

/-! ## Increasing nets of projections on a tensor product

For the cutting step the compressions are `e ⊗ f` with `e ∈ M^□`,
`f ∈ N^□` running through increasing families with supremum `1`.  What
`mem_of_compress_mem` needs of them is `IsLUB (range ·) 1` *in the operator
order*, and that is supplied here: a directed family of projections has its
`projSup` as a supremum in `B(ℋ ⊗ 𝒦)` (`isLUB_projSup_of_directed`), and
`projSup {e_i ⊗ 1} = 1` because `e_i x → x` in norm, so any projection
fixing every `e_i x ⊗ y` fixes every `x ⊗ y`. -/

section OpTensorNets

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem isStarProjection_opTensor {a : H →L[ℂ] H} {b : K →L[ℂ] K}
    (ha : IsStarProjection a) (hb : IsStarProjection b) :
    IsStarProjection (opTensor a b) := by
  refine ⟨?_, ?_⟩
  · show opTensor a b * opTensor a b = opTensor a b
    rw [← opTensor_mul, ha.isIdempotentElem, hb.isIdempotentElem]
  · show star (opTensor a b) = opTensor a b
    rw [opTensor_star, ha.isSelfAdjoint.star_eq, hb.isSelfAdjoint.star_eq]

theorem opTensor_le_opTensor_left {a a' : H →L[ℂ] H} {b : K →L[ℂ] K}
    (ha : IsStarProjection a) (ha' : IsStarProjection a') (hb : IsStarProjection b)
    (h : a ≤ a') : opTensor a b ≤ opTensor a' b := by
  refine ((isStarProjection_opTensor ha hb).le_iff_mul_eq_right
    (isStarProjection_opTensor ha' hb)).mpr ?_
  rw [← opTensor_mul, (ha.le_iff_mul_eq_right ha').mp h, hb.isIdempotentElem]

theorem opTensor_le_opTensor_right {a : H →L[ℂ] H} {b b' : K →L[ℂ] K}
    (ha : IsStarProjection a) (hb : IsStarProjection b) (hb' : IsStarProjection b')
    (h : b ≤ b') : opTensor a b ≤ opTensor a b' := by
  refine ((isStarProjection_opTensor ha hb).le_iff_mul_eq_right
    (isStarProjection_opTensor ha hb')).mpr ?_
  rw [← opTensor_mul, (hb.le_iff_mul_eq_right hb').mp h, ha.isIdempotentElem]

/-- A monotone net of projections with supremum `1` converges *strongly*:
`P i x → x` in norm.  (`‖x − P i x‖² = ω_x(1 − P i) → 0`, with `ω_x` the
vector np-functional.) -/
theorem tendsto_apply_of_isLUB_proj {ι : Type*} [Nonempty ι] [Preorder ι]
    [IsDirected ι (· ≤ ·)] (P : ι → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i))
    (hmono : Monotone P) (hlub : IsLUB (Set.range P) 1) (x : H) :
    Tendsto (fun i => P i x) atTop (𝓝 x) := by
  have huw : UWTendsto P atTop (1 : H →L[ℂ] H) :=
    uwTendsto_of_isLUB P 1 (fun i => (hP i).isSelfAdjoint) hmono hlub
  have hg := (uwTendsto_iff P atTop (1 : H →L[ℂ] H)).mp huw (vectorNP x)
  simp only [vectorNP_apply] at hg
  rw [show ((1 : H →L[ℂ] H) x) = x from rfl] at hg
  -- `⟪P x, P x⟫ = ⟪P x, x⟫ = ⟪x, P x⟫`
  have hadj : ∀ i, ContinuousLinearMap.adjoint (P i) = P i := fun i => by
    have h := (hP i).isSelfAdjoint.star_eq
    rwa [ContinuousLinearMap.star_eq_adjoint] at h
  have hidem : ∀ (i : ι) (w : H), P i (P i w) = P i w := fun i w => by
    rw [← clm_mul_apply, (hP i).isIdempotentElem]
  have hsq : ∀ i, (⟪P i x, P i x⟫ : ℂ) = ⟪x, P i x⟫ := fun i => by
    have h1 := ContinuousLinearMap.adjoint_inner_right (P i) x (P i x)
    rw [hadj i, hidem i] at h1
    exact h1.symm
  have hcross : ∀ i, (⟪P i x, x⟫ : ℂ) = ⟪x, P i x⟫ := fun i => by
    have h1 := ContinuousLinearMap.adjoint_inner_left (P i) x x
    rwa [hadj i] at h1
  have hexp : ∀ i, (⟪x - P i x, x - P i x⟫ : ℂ) = ⟪x, x⟫ - ⟪x, P i x⟫ := fun i => by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hsq i, hcross i]
    ring
  have hnorm : ∀ i, (‖x - P i x‖ : ℝ) ^ 2
      = RCLike.re ((⟪x, x⟫ : ℂ) - ⟪x, P i x⟫) := fun i => by
    rw [← hexp i]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (x - P i x)).symm
  have hre : Tendsto (fun i => RCLike.re ((⟪x, x⟫ : ℂ) - ⟪x, P i x⟫)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun i => (⟪x, x⟫ : ℂ) - ⟪x, P i x⟫) atTop (𝓝 0) := by
      have hc : Tendsto (fun _ : ι => (⟪x, x⟫ : ℂ)) atTop (𝓝 (⟪x, x⟫ : ℂ)) :=
        tendsto_const_nhds
      have h2 := hc.sub hg
      rwa [sub_self] at h2
    have h3 := (Complex.reCLM.continuous.tendsto 0).comp h1
    simpa [Function.comp_def] using h3
  have hsq0 : Tendsto (fun i => (‖x - P i x‖ : ℝ) ^ 2) atTop (𝓝 0) := by
    refine hre.congr fun i => (hnorm i).symm
  have h0 : Tendsto (fun i => (‖x - P i x‖ : ℝ)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq0
    simp only [Function.comp_def, Real.sqrt_zero] at h
    refine h.congr fun i => ?_
    exact Real.sqrt_sq (norm_nonneg _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact h0.congr fun i => norm_sub_rev _ _

/-- A projection of `B(ℋ ⊗ 𝒦)` fixing every elementary tensor is `1`. -/
theorem eq_one_of_fix_htmul (Q : HT H K →L[ℂ] HT H K)
    (hQ : ∀ (x : H) (y : K), Q (x ⊗ₕ y) = x ⊗ₕ y) : Q = 1 := by
  have hker : Submodule.span ℂ {t : HT H K | ∃ (x : H) (y : K), t = x ⊗ₕ y}
      ≤ LinearMap.ker ((Q - 1 : HT H K →L[ℂ] HT H K) : HT H K →ₗ[ℂ] HT H K) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, y, rfl⟩
    show (Q - 1 : HT H K →L[ℂ] HT H K) (x ⊗ₕ y) = 0
    have : (Q - 1 : HT H K →L[ℂ] HT H K) (x ⊗ₕ y) = Q (x ⊗ₕ y) - x ⊗ₕ y := rfl
    rw [this, hQ x y, sub_self]
  have hdense : Dense (Submodule.span ℂ
      {t : HT H K | ∃ (x : H) (y : K), t = x ⊗ₕ y} : Set (HT H K)) :=
    (hilbTensor H K).isTensor.dense
  have hcl : IsClosed ((LinearMap.ker
      ((Q - 1 : HT H K →L[ℂ] HT H K) : HT H K →ₗ[ℂ] HT H K) :
      Submodule ℂ (HT H K)) : Set (HT H K)) :=
    (Q - 1 : HT H K →L[ℂ] HT H K).isClosed_ker
  have hall : ∀ z : HT H K, (Q - 1 : HT H K →L[ℂ] HT H K) z = 0 := by
    intro z
    have hz : z ∈ closure (Submodule.span ℂ
        {t : HT H K | ∃ (x : H) (y : K), t = x ⊗ₕ y} : Set (HT H K)) := by
      rw [hdense.closure_eq]; trivial
    exact hcl.closure_subset (closure_mono hker hz)
  ext z
  have := hall z
  have h2 : (Q - 1 : HT H K →L[ℂ] HT H K) z = Q z - z := rfl
  rw [h2, sub_eq_zero] at this
  exact this

/-- `{e_i ⊗ 1}` increases to `1` in `B(ℋ ⊗ 𝒦)` when `{e_i}` increases to
`1` in `B(ℋ)`. -/
theorem isLUB_range_opTensor_left {ι : Type*} [Nonempty ι] [Preorder ι]
    [IsDirected ι (· ≤ ·)] (P : ι → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i))
    (hmono : Monotone P) (hlub : IsLUB (Set.range P) 1) :
    IsLUB (Set.range fun i => opTensor (P i) (1 : K →L[ℂ] K))
      (1 : HT H K →L[ℂ] HT H K) := by
  classical
  set D : Set (HT H K →L[ℂ] HT H K) :=
    Set.range (fun i => opTensor (P i) (1 : K →L[ℂ] K)) with hD
  have hone : IsStarProjection (1 : K →L[ℂ] K) := IsStarProjection.one _
  have hDproj : ∀ p ∈ D, IsStarProjection p := by
    rintro _ ⟨i, rfl⟩; exact isStarProjection_opTensor (hP i) hone
  have hne : D.Nonempty := ⟨_, Set.mem_range_self (Classical.arbitrary ι)⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    exact ⟨_, Set.mem_range_self k,
      opTensor_le_opTensor_left (hP i) (hP k) hone (hmono hik),
      opTensor_le_opTensor_left (hP j) (hP k) hone (hmono hjk)⟩
  have hlubD : IsLUB D (projSup D) := isLUB_projSup_of_directed D hDproj hne hdir
  have hsup : projSup D = 1 := by
    refine projSup_eq hDproj (IsStarProjection.one _) (fun p hp => (hDproj p hp).le_one) ?_
    intro Q hQ hub
    refine le_of_eq ?_
    refine (eq_one_of_fix_htmul Q ?_).symm
    intro x y
    have hfixi : ∀ i, Q (P i x ⊗ₕ y) = P i x ⊗ₕ y := by
      intro i
      have hle := hub _ (Set.mem_range_self i)
      have hmul := ((hDproj _ (Set.mem_range_self i)).le_iff_mul_eq_right hQ).mp hle
      have := congrArg (fun T : HT H K →L[ℂ] HT H K => T (x ⊗ₕ y)) hmul
      simp only [clm_mul_apply, opTensor_apply] at this
      exact this
    have htend : Tendsto (fun i => P i x ⊗ₕ y) atTop (𝓝 (x ⊗ₕ y)) := by
      have h := (htKet (H := H) y).continuous.tendsto x
      exact h.comp (tendsto_apply_of_isLUB_proj P hP hmono hlub x)
    exact (isClosed_fixed Q).mem_of_tendsto htend (Filter.Eventually.of_forall hfixi)
  rwa [hsup] at hlubD

/-- `{1 ⊗ f_j}` increases to `1` in `B(ℋ ⊗ 𝒦)` when `{f_j}` increases to
`1` in `B(𝒦)`. -/
theorem isLUB_range_opTensor_right {κ : Type*} [Nonempty κ] [Preorder κ]
    [IsDirected κ (· ≤ ·)] (P : κ → K →L[ℂ] K) (hP : ∀ j, IsStarProjection (P j))
    (hmono : Monotone P) (hlub : IsLUB (Set.range P) 1) :
    IsLUB (Set.range fun j => opTensor (1 : H →L[ℂ] H) (P j))
      (1 : HT H K →L[ℂ] HT H K) := by
  classical
  set D : Set (HT H K →L[ℂ] HT H K) :=
    Set.range (fun j => opTensor (1 : H →L[ℂ] H) (P j)) with hD
  have hone : IsStarProjection (1 : H →L[ℂ] H) := IsStarProjection.one _
  have hDproj : ∀ p ∈ D, IsStarProjection p := by
    rintro _ ⟨j, rfl⟩; exact isStarProjection_opTensor hone (hP j)
  have hne : D.Nonempty := ⟨_, Set.mem_range_self (Classical.arbitrary κ)⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    exact ⟨_, Set.mem_range_self k,
      opTensor_le_opTensor_right hone (hP i) (hP k) (hmono hik),
      opTensor_le_opTensor_right hone (hP j) (hP k) (hmono hjk)⟩
  have hlubD : IsLUB D (projSup D) := isLUB_projSup_of_directed D hDproj hne hdir
  have hsup : projSup D = 1 := by
    refine projSup_eq hDproj (IsStarProjection.one _) (fun p hp => (hDproj p hp).le_one) ?_
    intro Q hQ hub
    refine le_of_eq ?_
    refine (eq_one_of_fix_htmul Q ?_).symm
    intro x y
    have hfixj : ∀ j, Q (x ⊗ₕ P j y) = x ⊗ₕ P j y := by
      intro j
      have hle := hub _ (Set.mem_range_self j)
      have hmul := ((hDproj _ (Set.mem_range_self j)).le_iff_mul_eq_right hQ).mp hle
      have := congrArg (fun T : HT H K →L[ℂ] HT H K => T (x ⊗ₕ y)) hmul
      simp only [clm_mul_apply, opTensor_apply] at this
      exact this
    have htend : Tendsto (fun j => x ⊗ₕ P j y) atTop (𝓝 (x ⊗ₕ y)) := by
      have hcont : Continuous fun w : K => x ⊗ₕ w :=
        (LinearMap.mkContinuous ((hilbTensor H K).map x) ‖x‖
          (fun w => le_of_eq (norm_htmul x w))).continuous
      exact (hcont.tendsto y).comp (tendsto_apply_of_isLUB_proj P hP hmono hlub y)
    exact (isClosed_fixed Q).mem_of_tendsto htend (Filter.Eventually.of_forall hfixj)
  rwa [hsup] at hlubD

end OpTensorNets

/-! ## Step 1: cutting

Once the compressions `(e ⊗ f)·(M ⊗̄ N)^□·(e ⊗ f)` are known to land in
`M^□ ⊗̄ N^□`, the commutation theorem follows: compress first in the `𝒦`
variable and then in the `ℋ` variable, each time by
`mem_of_compress_mem`.  That hypothesis — `RelCT` at each cut — is
supplied by `A/Proc/CornerTensor.lean`, which gets it from the corner
Hilbert space `eℋ` without proving `(M ⊗̄ N)_{e ⊗ f} = M_e ⊗̄ N_f`. -/

section Cutting

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **The cutting step.**  Let `{e_i} ⊆ B(ℋ)` and `{f_j} ⊆ B(𝒦)` be
increasing nets of projections with supremum `1`.  If every compression
`(e_i ⊗ f_j) y (e_i ⊗ f_j)` of an element `y` of `(𝒜 ⊗̄ ℬ)^□` lies in
`𝒜^□ ⊗̄ ℬ^□`, then `CT 𝒜 ℬ` holds. -/
theorem CT_of_compress {ι κ : Type*} [Nonempty ι] [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty κ] [Preorder κ] [IsDirected κ (· ≤ ·)]
    {SA : StarSubalgebra ℂ (H →L[ℂ] H)} {SB : StarSubalgebra ℂ (K →L[ℂ] K)}
    (e : ι → H →L[ℂ] H) (he : ∀ i, IsStarProjection (e i)) (hemono : Monotone e)
    (helub : IsLUB (Set.range e) 1)
    (f : κ → K →L[ℂ] K) (hf : ∀ j, IsStarProjection (f j)) (hfmono : Monotone f)
    (hflub : IsLUB (Set.range f) 1)
    (hcut : ∀ (i : ι) (j : κ), ∀ y ∈ vnComm (concreteTensor H K SA SB),
      opTensor (e i) (f j) * y * opTensor (e i) (f j)
        ∈ concreteTensor H K (vnComm SA) (vnComm SB)) :
    CT SA SB := by
  rw [CT_iff_le]
  intro y hy
  have hTclosed : @IsClosed _ (ultraweak (HT H K →L[ℂ] HT H K))
      ((concreteTensor H K (vnComm SA) (vnComm SB) : StarSubalgebra ℂ _) :
        Set (HT H K →L[ℂ] HT H K)) :=
    (vnsac _ (isVNSubalgebra_concreteTensor _ _)).2
  have hone : ∀ {L : Type u} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
      [CompleteSpace L], IsStarProjection (1 : L →L[ℂ] L) := IsStarProjection.one _
  have hqproj : ∀ i, IsStarProjection (opTensor (e i) (1 : K →L[ℂ] K)) :=
    fun i => isStarProjection_opTensor (he i) hone
  have hrproj : ∀ j, IsStarProjection (opTensor (1 : H →L[ℂ] H) (f j)) :=
    fun j => isStarProjection_opTensor hone (hf j)
  have hqmono : Monotone fun i => opTensor (e i) (1 : K →L[ℂ] K) :=
    fun i i' h => opTensor_le_opTensor_left (he i) (he i') hone (hemono h)
  have hrmono : Monotone fun j => opTensor (1 : H →L[ℂ] H) (f j) :=
    fun j j' h => opTensor_le_opTensor_right hone (hf j) (hf j') (hfmono h)
  have hqlub := isLUB_range_opTensor_left (K := K) e he hemono helub
  have hrlub := isLUB_range_opTensor_right (H := H) f hf hfmono hflub
  have hstep : ∀ i : ι,
      opTensor (e i) (1 : K →L[ℂ] K) * y * opTensor (e i) (1 : K →L[ℂ] K)
        ∈ (concreteTensor H K (vnComm SA) (vnComm SB) : Set (HT H K →L[ℂ] HT H K)) := by
    intro i
    refine mem_of_compress_mem (fun j => opTensor (1 : H →L[ℂ] H) (f j)) hrproj hrmono
      hrlub hTclosed ?_
    intro j
    have h1 : opTensor (1 : H →L[ℂ] H) (f j) * opTensor (e i) (1 : K →L[ℂ] K)
        = opTensor (e i) (f j) := by
      rw [← opTensor_mul, one_mul, mul_one]
    have h2 : opTensor (e i) (1 : K →L[ℂ] K) * opTensor (1 : H →L[ℂ] H) (f j)
        = opTensor (e i) (f j) := by
      rw [← opTensor_mul, mul_one, one_mul]
    have h3 : opTensor (1 : H →L[ℂ] H) (f j) *
          (opTensor (e i) (1 : K →L[ℂ] K) * y * opTensor (e i) (1 : K →L[ℂ] K)) *
          opTensor (1 : H →L[ℂ] H) (f j)
        = opTensor (e i) (f j) * y * opTensor (e i) (f j) := by
      calc opTensor (1 : H →L[ℂ] H) (f j) *
            (opTensor (e i) (1 : K →L[ℂ] K) * y * opTensor (e i) (1 : K →L[ℂ] K)) *
            opTensor (1 : H →L[ℂ] H) (f j)
          = (opTensor (1 : H →L[ℂ] H) (f j) * opTensor (e i) (1 : K →L[ℂ] K)) * y *
              (opTensor (e i) (1 : K →L[ℂ] K) * opTensor (1 : H →L[ℂ] H) (f j)) := by
            noncomm_ring
        _ = opTensor (e i) (f j) * y * opTensor (e i) (f j) := by rw [h1, h2]
    rw [h3]
    exact hcut i j y hy
  exact mem_of_compress_mem (fun i => opTensor (e i) (1 : K →L[ℂ] K)) hqproj hqmono
    hqlub hTclosed hstep

/-- The **commutation theorem relative to a cut** `p`: the relative
commutant of the reduced algebra `(𝒜 ⊗̄ ℬ)_p` inside the corner
`p B(ℋ ⊗ 𝒦) p` is contained in `𝒜^□ ⊗̄ ℬ^□`.

For `p = e ⊗ f` with `e ∈ 𝒜^□`, `f ∈ ℬ^□` this is *exactly* what the
identification `(𝒜 ⊗̄ ℬ)_{e ⊗ f} = 𝒜_e ⊗̄ ℬ_f` plus `CT(𝒜_e, ℬ_f)` would
deliver; `A/Proc/CornerTensor.lean` delivers it without that
identification, and `CT_of_relCT` consumes it. -/
def RelCT (SA : StarSubalgebra ℂ (H →L[ℂ] H)) (SB : StarSubalgebra ℂ (K →L[ℂ] K))
    (p : HT H K →L[ℂ] HT H K) : Prop :=
  ∀ z : HT H K →L[ℂ] HT H K, p * z * p = z →
    (∀ x ∈ concreteTensor H K SA SB, (x * p) * z = z * (x * p)) →
    z ∈ concreteTensor H K (vnComm SA) (vnComm SB)

/-- An elementary tensor of commutants lies in `(𝒜 ⊗̄ ℬ)^□`. -/
theorem opTensor_mem_vnComm_concreteTensor {SA : StarSubalgebra ℂ (H →L[ℂ] H)}
    {SB : StarSubalgebra ℂ (K →L[ℂ] K)} {a : H →L[ℂ] H} {b : K →L[ℂ] K}
    (ha : a ∈ vnComm SA) (hb : b ∈ vnComm SB) :
    opTensor a b ∈ vnComm (concreteTensor H K SA SB) :=
  concreteTensor_vnComm_le SA SB (opTensor_mem_concreteTensor ha hb)

/-- **The reduction, assembled.**  Given increasing nets of projections
`{e_i} ⊆ 𝒜^□`, `{f_j} ⊆ ℬ^□` with supremum `1`, the commutation theorem
for `(𝒜, ℬ)` follows from its relative form at each cut `e_i ⊗ f_j`.

The bridge is the reduction theorem `mem_vnComm_iff_comm_reduced`: the
compression `p y p` of an element of `(𝒜 ⊗̄ ℬ)^□` lies in the corner and
commutes with the reduced algebra, so `RelCT` applies to it; the cutting
principle `CT_of_compress` then removes the cuts. -/
theorem CT_of_relCT {ι κ : Type*} [Nonempty ι] [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty κ] [Preorder κ] [IsDirected κ (· ≤ ·)]
    {SA : StarSubalgebra ℂ (H →L[ℂ] H)} {SB : StarSubalgebra ℂ (K →L[ℂ] K)}
    (e : ι → H →L[ℂ] H) (he : ∀ i, IsStarProjection (e i)) (hemem : ∀ i, e i ∈ vnComm SA)
    (hemono : Monotone e) (helub : IsLUB (Set.range e) 1)
    (f : κ → K →L[ℂ] K) (hf : ∀ j, IsStarProjection (f j)) (hfmem : ∀ j, f j ∈ vnComm SB)
    (hfmono : Monotone f) (hflub : IsLUB (Set.range f) 1)
    (hrel : ∀ (i : ι) (j : κ), RelCT SA SB (opTensor (e i) (f j))) :
    CT SA SB := by
  refine CT_of_compress e he hemono helub f hf hfmono hflub ?_
  intro i j y hy
  have hpp : opTensor (e i) (f j) * opTensor (e i) (f j) = opTensor (e i) (f j) :=
    (isStarProjection_opTensor (he i) (hf j)).isIdempotentElem
  have hpmem : opTensor (e i) (f j) ∈ vnComm (concreteTensor H K SA SB) :=
    opTensor_mem_vnComm_concreteTensor (hemem i) (hfmem j)
  have hcorner : opTensor (e i) (f j) *
      (opTensor (e i) (f j) * y * opTensor (e i) (f j)) * opTensor (e i) (f j)
      = opTensor (e i) (f j) * y * opTensor (e i) (f j) := by
    calc opTensor (e i) (f j) *
          (opTensor (e i) (f j) * y * opTensor (e i) (f j)) * opTensor (e i) (f j)
        = opTensor (e i) (f j) * opTensor (e i) (f j) * y *
            (opTensor (e i) (f j) * opTensor (e i) (f j)) := by noncomm_ring
      _ = opTensor (e i) (f j) * y * opTensor (e i) (f j) := by rw [hpp]
  have hmemc : opTensor (e i) (f j) * y * opTensor (e i) (f j)
      ∈ vnComm (concreteTensor H K SA SB) := mem_vnComm_of_corner hpmem hy
  exact hrel i j _ hcorner
    ((mem_vnComm_iff_comm_reduced hpp hpmem hcorner).mpr hmemc)

end Cutting

/-! ## Finite sums of an orthogonal family increase to `1`

The nets that `CT_of_compress`/`CT_of_relCT` consume are the finite partial
sums `e_F = ∑_{i ∈ F} e_i` of the orthogonal family produced by the Zorn
step.  This is the (purely order-theoretic) statement that they increase to
`1`. -/

section PartialSums

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [VonNeumannAlgebra A]

/-- The finite partial sums of a pairwise orthogonal family of projections
with supremum `1` form an increasing net of projections with supremum `1`
*in the order of `A`*. -/
theorem isLUB_range_finsetSum {ι : Type*} (p : ι → A)
    (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i * p j = 0)
    (hsup : projSup (Set.range p) = 1) :
    (∀ F : Finset ι, IsStarProjection (∑ i ∈ F, p i)) ∧
      Monotone (fun F : Finset ι => ∑ i ∈ F, p i) ∧
      IsLUB (Set.range fun F : Finset ι => ∑ i ∈ F, p i) 1 := by
  classical
  have hproj : ∀ F : Finset ι, IsStarProjection (∑ i ∈ F, p i) := fun F =>
    isStarProjection_sum F p hp fun i _ j _ hij => horth i j hij
  have hmono : Monotone (fun F : Finset ι => ∑ i ∈ F, p i) := by
    intro F F' hFF'
    exact Finset.sum_le_sum_of_subset_of_nonneg hFF' fun i _ _ => (hp i).nonneg
  refine ⟨hproj, hmono, ?_⟩
  set D : Set A := Set.range (fun F : Finset ι => ∑ i ∈ F, p i) with hD
  have hDproj : ∀ q ∈ D, IsStarProjection q := by
    rintro _ ⟨F, rfl⟩; exact hproj F
  have hne : D.Nonempty := ⟨_, Set.mem_range_self (∅ : Finset ι)⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨F, rfl⟩ _ ⟨F', rfl⟩
    exact ⟨_, Set.mem_range_self (F ∪ F'),
      hmono Finset.subset_union_left, hmono Finset.subset_union_right⟩
  have hlubD : IsLUB D (projSup D) := isLUB_projSup_of_directed D hDproj hne hdir
  have hpproj : ∀ q ∈ Set.range p, IsStarProjection q := by
    rintro _ ⟨i, rfl⟩; exact hp i
  have hsupD : projSup D = 1 := by
    refine projSup_eq hDproj (IsStarProjection.one _)
      (fun q hq => (hDproj q hq).le_one) ?_
    intro Q hQ hub
    have hpQ : ∀ q ∈ Set.range p, q ≤ Q := by
      rintro _ ⟨i, rfl⟩
      have h := hub _ (Set.mem_range_self ({i} : Finset ι))
      rwa [Finset.sum_singleton] at h
    have := (projSup_spec hpproj).2.2 Q hQ hpQ
    rwa [hsup] at this
  rwa [hsupD] at hlubD

end PartialSums

end Theses.A.Proc
