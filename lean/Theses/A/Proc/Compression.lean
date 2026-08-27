/-
Thesis A, chapter "Assorted Structure in W*_cpsu" (proc.tex): **the
compression of a von Neumann algebra**, `(f 𝒯 f)^□ = 𝒯^□ f` for a projection
`f ∈ 𝒯` — the commutant taken in `B(fℋ)`.  This is the half of the reduction
theorem that `A/Proc/CornerTensor.lean` deliberately avoids
(`mem_vnComm_cornerAlg` is the other, elementary, half), and the last step the
reduction of the commutation theorem was missing.

## What is actually missing, and it is not what the name suggests

"The compression of a von Neumann algebra is a von Neumann algebra" is, read
literally, **already in the tree**: for a von Neumann subalgebra `𝒯 ∋ f` the
set `f 𝒯 f ≅ cmpr sub '' 𝒯` is the carrier of `cornerAlgVN`
(`coe_cornerAlgVN`), which is a *commutant* by construction and hence a von
Neumann subalgebra by 65III.  What is missing — and what needs the classical
extension argument — is the **identification of its commutant**:

    `(f 𝒯 f)^□ = 𝒯^□ f`,

equivalently, since `(𝒯^□ f)^□ = f 𝒯 f` is the easy half, that the
**reduction** `𝒯^□ f` of `𝒯^□` by a projection of its commutant is
bicommutant-closed (`vnComm_vnComm_cornerAlg`).

**The commutant trick of `CommutationAmplify.lean` does not apply, and the
reason is structural.**  There the set to be recognised as a von Neumann
algebra was a *preimage*, `{a | a ⊗ 1 ∈ 𝒲}`, which is cut out by the equations
`a` commutes with all slices of `𝒲^□`; being a commutant is then a
computation.  Here the set is an *image*, `cmpr sub '' 𝒯^□`, and "this image
is a commutant" **is** the theorem: any presentation of it as a commutant
already produces, for each `y` in that commutant, the element of `𝒯^□` above
`y`.  So there is nothing to sidestep, and the extension argument is the
content.

## The proof

For `y ∈ (f𝒯f)^□` the classical construction extends `y` to `ŷ` on the dense
subspace `𝒯 f ℋ` by `ŷ (x f ζ) := x ỹ f ζ`.  Well-definedness and boundedness
are one and the same estimate, and everything here is arranged around it.

* `cmap sub T w : 𝒯 ⊗ E →ₗ ℋ`, `x ⊗ v ↦ x (sub (w v))`, packages the finite
  sums `∑ᵢ xᵢ f ζᵢ` (`w = 1`) and their intended images `∑ᵢ xᵢ ỹ f ζᵢ`
  (`w = y`) as *linear maps out of an algebraic tensor product*.  This is what
  removes the well-definedness bookkeeping: a relation among the `∑ xᵢ f ζᵢ`
  is an element of the kernel of `cmap sub T 1`, and the estimate is a
  statement about all of `𝒯 ⊗ E` at once.
* `cmap_inner_cmap` — **the master identity**.  For `w` commuting with the
  compressed algebra `f𝒯f`,
  `⟪cmap w z₁, cmap w z₂⟫ = ⟪cmap 1 z₁, cmap (w^* w) z₂⟫`.
  Both sides are additive in each variable, so it is proved by two
  `TensorProduct.induction_on`s from the one-term case
  `⟪x₁(sub(w v₁)), x₂(sub(w v₂))⟫ = ⟪v₁, (x₁^*x₂)_f (w^*w) v₂⟫`; no double
  sums over finite index sets appear anywhere.
* `norm_cmap_le` — **the estimate** `‖cmap y z‖ ≤ ‖y‖ ‖cmap 1 z‖`.  With
  `t := (‖y‖² − y^*y)^{1/2}` (`CFC.sqrt`, which commutes with everything `y`
  commutes with by `Commute.cfcₙ_nnreal`), the master identity applied to `y`
  and to `t` and added gives
  `‖cmap y z‖² + ‖cmap t z‖² = ‖y‖² ‖cmap 1 z‖²`.
  The positive square root is the only analytic input, and it is where
  `y^*y ≤ ‖y‖²` enters.
* `yext` — the extension.  `LinearMap.extendOfNorm` extends along a linear map
  with dense range; the range of `cmap sub T 1` is *not* dense in `ℋ`, so the
  source is enlarged to `(𝒯 ⊗ E) × [𝒯fℋ]^⊥` and `ŷ` is defined to kill the
  second summand.  Pythagoras turns the estimate into the required bound, and
  no orthogonal projection or corestriction to a closed subspace is needed.
  `ŷ ∈ 𝒯^□` because `𝒯 f ℋ` and its orthogonal complement are `𝒯`-invariant,
  and `cmpr sub ŷ = y` by evaluating at `1 ⊗ v`.

## The consequence

`CT_of_CT_compression`: the commutation theorem transports across a cut
`e ∈ 𝒜`, `f ∈ ℬ` *inside* the algebras, provided `e ⊗ f` separates
`(𝒜 ⊗̄ ℬ)^□` — which is central carrier `1`, and is supplied in that form by
`sep_of_dense_carrier`.  `CornerTensor.lean`'s `relCT_of_CT` transports across
cuts in the *commutant*; this is the missing orientation, and it is the shape
`A/Proc/CommutationAmplify.lean`'s `CT_of_CT_cyclic` needs, since the corner
at `f = [𝒜^□ξ]` — where a cyclic *and separating* vector lives — is a cut
inside the algebra.  **No net of cuts is required**: with central carrier `1`,
`u ↦ u (e ⊗ f)` is injective on `(𝒜 ⊗̄ ℬ)^□`, so one cut suffices, and the
ultraweak cutting principle `CT_of_compress` is not used at all.

What is *not* here: the passage from "`𝒜` has a cyclic vector" to the data
this file consumes — that `e := [𝒜^□ξ]` lies in `𝒜`, that `𝒜 e ℋ` is total,
and that the compression `e𝒜e` has a cyclic and separating vector.  That is
the next brief, and with it `CT_of_CT_cyclic` composes to the reduction of the
commutation theorem to the cyclic-and-separating case.
-/
import Theses.A.Proc.CornerTensor

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
  TensorProduct ENNReal
open Filter Topology Theses Theses.A.VN

noncomputable section

namespace Theses.A.Proc

universe u

section Compression

variable {H E : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## The evaluation maps `𝒯 ⊗ E → ℋ` -/

/-- The bilinear building block of `cmap`: `x ↦ (v ↦ x (sub (w v)))`. -/
def cmapBil (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H)) (w : E →L[ℂ] E) :
    ↥T →ₗ[ℂ] E →ₗ[ℂ] H where
  toFun x := ((x : H →L[ℂ] H) ∘L sub ∘L w : E →L[ℂ] H).toLinearMap
  map_add' x x' := by ext v; simp
  map_smul' c x := by ext v; simp

/-- The evaluation map `𝒯 ⊗ E → ℋ`, `x ⊗ v ↦ x (sub (w v))`.  For `w = 1`
its range is the subspace `𝒯 sub(E) = 𝒯 f ℋ` on which the classical proof
defines the extension `ŷ`; for `w = y` its range is the set of candidate
values of `ŷ`. -/
def cmap (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H)) (w : E →L[ℂ] E) :
    (↥T ⊗[ℂ] E) →ₗ[ℂ] H :=
  TensorProduct.lift (cmapBil sub T w)

omit [CompleteSpace E] in
@[simp] theorem cmap_tmul (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    (w : E →L[ℂ] E) (x : ↥T) (v : E) :
    cmap sub T w (x ⊗ₜ[ℂ] v) = (x : H →L[ℂ] H) (sub (w v)) := rfl

omit [CompleteSpace E] in
theorem cmap_add_w (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    (w w' : E →L[ℂ] E) (z : ↥T ⊗[ℂ] E) :
    cmap sub T (w + w') z = cmap sub T w z + cmap sub T w' z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x v => simp
  | add z z' hz hz' => simp [hz, hz']; abel

omit [CompleteSpace E] in
theorem cmap_smul_w (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    (c : ℂ) (w : E →L[ℂ] E) (z : ↥T ⊗[ℂ] E) :
    cmap sub T (c • w) z = c • cmap sub T w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x v => simp
  | add z z' hz hz' => simp [hz, hz', smul_add]

omit [CompleteSpace E] in
theorem cmap_sub_w (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    (w w' : E →L[ℂ] E) (z : ↥T ⊗[ℂ] E) :
    cmap sub T (w - w') z = cmap sub T w z - cmap sub T w' z := by
  have := cmap_add_w sub T (w - w') w' z
  rw [sub_add_cancel] at this
  rw [this]; abel


/-! ## The master identity

Everything rests on one computation: for `w` commuting with the compressed
algebra `T_e = sub^* T sub`,

    `⟪cmap w z₁, cmap w z₂⟫ = ⟪cmap 1 z₁, cmap (w^* w) z₂⟫`,

i.e. the sesquilinear form `(z₁, z₂) ↦ ⟪cmap w z₁, cmap w z₂⟫` depends on
`w` only through `w^* w`, and *linearly* so.  Applied to `w = y` and to
`w = (‖y‖² − y^*y)^{1/2}` it gives well-definedness and boundedness of the
extension in one stroke. -/

/-- `⟪x₁ (sub a), x₂ (sub b)⟫ = ⟪a, (x₁^* x₂)_e b⟫`: an inner product of
vectors in the range of `sub` sees only the compression. -/
theorem inner_apply_sub (sub : E →L[ℂ] H) (x₁ x₂ : H →L[ℂ] H) (a b : E) :
    ⟪x₁ (sub a), x₂ (sub b)⟫ = ⟪a, cmpr sub (star x₁ * x₂) b⟫ := by
  rw [cmpr_apply, ContinuousLinearMap.adjoint_inner_right]
  show ⟪x₁ (sub a), x₂ (sub b)⟫ = ⟪sub a, star x₁ (x₂ (sub b))⟫
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

/-- `w : B(eℋ)` commutes with the compression `T_e` of `T`. -/
def CommCmpr (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    (w : E →L[ℂ] E) : Prop :=
  ∀ x ∈ T, Commute (cmpr sub x) w

namespace CommCmpr

variable {sub : E →L[ℂ] H} {T : StarSubalgebra ℂ (H →L[ℂ] H)} {w w' : E →L[ℂ] E}

theorem one : CommCmpr sub T (1 : E →L[ℂ] E) := fun _ _ => Commute.one_right _

theorem mul (hw : CommCmpr sub T w) (hw' : CommCmpr sub T w') :
    CommCmpr sub T (w * w') := fun x hx => ((hw x hx).mul_right (hw' x hx))

theorem star_mem (hw : CommCmpr sub T w) : CommCmpr sub T (star w) := by
  intro x hx
  have h := hw (star x) (StarMemClass.star_mem hx)
  have h2 := congrArg (fun t : E →L[ℂ] E => star t) h
  simp only [star_mul, cmpr_star, star_star] at h2
  exact h2.symm

theorem smul (hw : CommCmpr sub T w) (c : ℂ) : CommCmpr sub T (c • w) := by
  intro x hx
  have h := hw x hx
  show cmpr sub x * (c • w) = (c • w) * cmpr sub x
  rw [mul_smul_comm, smul_mul_assoc, h]

end CommCmpr

/-- **The master identity.** -/
theorem cmap_inner_cmap (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    {w : E →L[ℂ] E} (hw : CommCmpr sub T w) :
    ∀ z₁ z₂ : ↥T ⊗[ℂ] E,
      ⟪cmap sub T w z₁, cmap sub T w z₂⟫
        = ⟪cmap sub T 1 z₁, cmap sub T (star w * w) z₂⟫ := by
  intro z₁
  induction z₁ using TensorProduct.induction_on with
  | zero => intro z₂; simp
  | tmul x₁ v₁ =>
    intro z₂
    induction z₂ using TensorProduct.induction_on with
    | zero => simp
    | tmul x₂ v₂ =>
      have hmem : (star (x₁ : H →L[ℂ] H) * (x₂ : H →L[ℂ] H)) ∈ T :=
        mul_mem (star_mem x₁.2) x₂.2
      set c : E →L[ℂ] E := cmpr sub (star (x₁ : H →L[ℂ] H) * (x₂ : H →L[ℂ] H)) with hc
      have hcw : Commute c w := hw _ hmem
      have hcw2 : Commute c (star w * w) :=
        (CommCmpr.star_mem hw _ hmem).mul_right hcw
      have e1 : c (w v₂) = w (c v₂) := by
        have := congrArg (fun t : E →L[ℂ] E => t v₂) hcw
        simpa using this
      have e2 : c ((star w * w) v₂) = (star w * w) (c v₂) := by
        have := congrArg (fun t : E →L[ℂ] E => t v₂) hcw2
        simpa using this
      calc ⟪cmap sub T w (x₁ ⊗ₜ[ℂ] v₁), cmap sub T w (x₂ ⊗ₜ[ℂ] v₂)⟫
          = ⟪w v₁, c (w v₂)⟫ := by
            rw [cmap_tmul, cmap_tmul, inner_apply_sub]
        _ = ⟪w v₁, w (c v₂)⟫ := by rw [e1]
        _ = ⟪v₁, (star w * w) (c v₂)⟫ := by
            rw [show (star w * w) (c v₂) = star w (w (c v₂)) from rfl,
              ContinuousLinearMap.star_eq_adjoint,
              ContinuousLinearMap.adjoint_inner_right]
        _ = ⟪v₁, c ((star w * w) v₂)⟫ := by rw [e2]
        _ = ⟪cmap sub T 1 (x₁ ⊗ₜ[ℂ] v₁), cmap sub T (star w * w) (x₂ ⊗ₜ[ℂ] v₂)⟫ := by
            rw [cmap_tmul, cmap_tmul, inner_apply_sub]
            simp [hc]
    | add p q hp hq => simp only [map_add, inner_add_right, hp, hq]
  | add p q hp hq =>
    intro z₂
    simp only [map_add, inner_add_left, hp z₂, hq z₂]

/-! ## The estimate

`‖ŷ(∑ xᵢ f ζᵢ)‖ ≤ ‖y‖ ‖∑ xᵢ f ζᵢ‖`, in the form `‖cmap y z‖ ≤ ‖y‖ ‖cmap 1 z‖`.
Both the well-definedness and the boundedness of the classical extension are
contained in it. -/

omit [CompleteSpace E] in
theorem cmap_algebraMap_real (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    (r : ℝ) (z : ↥T ⊗[ℂ] E) :
    cmap sub T (algebraMap ℝ (E →L[ℂ] E) r) z = (r : ℂ) • cmap sub T 1 z := by
  have h : algebraMap ℝ (E →L[ℂ] E) r = (r : ℂ) • (1 : E →L[ℂ] E) := by
    rw [IsScalarTower.algebraMap_apply ℝ ℂ (E →L[ℂ] E), Algebra.algebraMap_eq_smul_one]
    norm_num
  rw [h, cmap_smul_w]

/-- **The estimate**, the entire content of the classical proof. -/
theorem norm_cmap_le (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    {y : E →L[ℂ] E} (hy : CommCmpr sub T y) (z : ↥T ⊗[ℂ] E) :
    ‖cmap sub T y z‖ ≤ ‖y‖ * ‖cmap sub T 1 z‖ := by
  have hxx : ∀ x : H, ⟪x, x⟫ = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  -- `b = ‖y‖² − y^*y ≥ 0`, and `t = b^{1/2}` again commutes with `T_e`.
  set b : E →L[ℂ] E := algebraMap ℝ (E →L[ℂ] E) (‖y‖ ^ 2) - star y * y with hbdef
  have hb : 0 ≤ b := sub_nonneg.mpr CStarAlgebra.star_mul_le_algebraMap_norm_sq
  set t : E →L[ℂ] E := CFC.sqrt b with htdef
  have htsa : star t = t := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)
  have ht2 : star t * t = b := by rw [htsa]; exact CFC.sqrt_mul_sqrt_self b hb
  have htc : CommCmpr sub T t := by
    intro x hx
    have h1 : Commute (cmpr sub x) (star y * y) :=
      (CommCmpr.star_mem hy x hx).mul_right (hy x hx)
    have h2 : Commute (cmpr sub x) b :=
      (Algebra.commute_algebraMap_right (‖y‖ ^ 2) (cmpr sub x)).sub_right h1
    exact (Commute.cfcₙ_nnreal h2.symm NNReal.sqrt).symm
  -- the two squared norms add up to `‖y‖² ‖cmap 1 z‖²`
  have hsum : ⟪cmap sub T y z, cmap sub T y z⟫ + ⟪cmap sub T t z, cmap sub T t z⟫
      = ((‖y‖ ^ 2 : ℝ) : ℂ) * ⟪cmap sub T 1 z, cmap sub T 1 z⟫ := by
    rw [cmap_inner_cmap sub T hy z z, cmap_inner_cmap sub T htc z z, ht2,
      ← inner_add_right, hbdef, cmap_sub_w, ← add_sub_assoc,
      add_comm (cmap sub T (star y * y) z), add_sub_cancel_right,
      cmap_algebraMap_real, inner_smul_right]
  rw [hxx, hxx, hxx] at hsum
  have hreal : ‖cmap sub T y z‖ ^ 2 + ‖cmap sub T t z‖ ^ 2
      = ‖y‖ ^ 2 * ‖cmap sub T 1 z‖ ^ 2 := by exact_mod_cast hsum
  have hle : ‖cmap sub T y z‖ ^ 2 ≤ (‖y‖ * ‖cmap sub T 1 z‖) ^ 2 := by
    nlinarith [sq_nonneg (‖cmap sub T t z‖)]
  calc ‖cmap sub T y z‖ = Real.sqrt (‖cmap sub T y z‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((‖y‖ * ‖cmap sub T 1 z‖) ^ 2) := Real.sqrt_le_sqrt hle
    _ = ‖y‖ * ‖cmap sub T 1 z‖ :=
        Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-! ## The extension `ŷ`

`ŷ` is defined on `𝒯 f ℋ ⊕ (𝒯 f ℋ)^⊥` — a dense subspace of `ℋ` — by
`ŷ(x f ζ) := x ỹ f ζ` and `ŷ = 0` on the orthogonal complement, and extended
by continuity (`LinearMap.extendOfNorm`).  Adding the orthogonal complement
to the *source* is what makes the range dense in all of `ℋ`, so no corestriction
to a closed subspace and no orthogonal projection is needed. -/

/-- Left multiplication by `x ∈ T` on `T ⊗ E`. -/
def ltens {T : StarSubalgebra ℂ (H →L[ℂ] H)} (x : ↥T) :
    (↥T ⊗[ℂ] E) →ₗ[ℂ] (↥T ⊗[ℂ] E) :=
  TensorProduct.map (LinearMap.mulLeft ℂ x) LinearMap.id

omit [CompleteSpace E] in
theorem cmap_ltens (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    (w : E →L[ℂ] E) (x : ↥T) (z : ↥T ⊗[ℂ] E) :
    cmap sub T w (ltens x z) = (x : H →L[ℂ] H) (cmap sub T w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x' v =>
    show cmap sub T w ((x * x') ⊗ₜ[ℂ] v) = _
    rw [cmap_tmul, cmap_tmul]
    simp
  | add p q hp hq => simp [map_add, hp, hq]

/-- The subspace `𝒯 f ℋ`. -/
def cmapRange (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Submodule ℂ H := LinearMap.range (cmap sub T 1)

/-- Its closure `[𝒯 f ℋ]`. -/
def cmapClosure (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Submodule ℂ H := (cmapRange sub T).topologicalClosure

instance instCompleteSpaceCmapClosure (sub : E →L[ℂ] H)
    (T : StarSubalgebra ℂ (H →L[ℂ] H)) : CompleteSpace ↥(cmapClosure sub T) :=
  (cmapRange sub T).isClosed_topologicalClosure.completeSpace_coe

/-- The source of the extension: `𝒯 ⊗ E` together with `[𝒯 f ℋ]^⊥`. -/
def extIn (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ((↥T ⊗[ℂ] E) × ↥((cmapClosure sub T)ᗮ)) →ₗ[ℂ] H :=
  (cmap sub T 1).comp (LinearMap.fst ℂ _ _) +
    ((cmapClosure sub T)ᗮ.subtype).comp (LinearMap.snd ℂ _ _)

/-- The values of the extension: `x f ζ ↦ x ỹ f ζ`, and `0` on the
orthogonal complement. -/
def extOut (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H)) (y : E →L[ℂ] E) :
    ((↥T ⊗[ℂ] E) × ↥((cmapClosure sub T)ᗮ)) →ₗ[ℂ] H :=
  (cmap sub T y).comp (LinearMap.fst ℂ _ _)

omit [CompleteSpace E] in
theorem extIn_apply (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    (p : (↥T ⊗[ℂ] E) × ↥((cmapClosure sub T)ᗮ)) :
    extIn sub T p = cmap sub T 1 p.1 + (p.2 : H) := rfl

omit [CompleteSpace E] in
theorem extOut_apply (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    (y : E →L[ℂ] E) (p : (↥T ⊗[ℂ] E) × ↥((cmapClosure sub T)ᗮ)) :
    extOut sub T y p = cmap sub T y p.1 := rfl

omit [CompleteSpace E] in
theorem cmapRange_le_cmapClosure (sub : E →L[ℂ] H)
    (T : StarSubalgebra ℂ (H →L[ℂ] H)) :
    cmapRange sub T ≤ cmapClosure sub T := Submodule.le_topologicalClosure _

omit [CompleteSpace E] in
theorem denseRange_extIn (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H)) :
    DenseRange (extIn sub T) := by
  have hsub : cmapClosure sub T ⊔ (cmapClosure sub T)ᗮ ≤
      (LinearMap.range (extIn sub T)).topologicalClosure := by
    refine sup_le ?_ ?_
    · refine le_trans (Submodule.topologicalClosure_mono ?_)
        (le_refl (LinearMap.range (extIn sub T)).topologicalClosure)
      rintro _ ⟨z, rfl⟩
      exact ⟨(z, 0), by simp [extIn_apply]⟩
    · refine le_trans ?_ (Submodule.le_topologicalClosure _)
      intro u hu
      exact ⟨(0, ⟨u, hu⟩), by simp [extIn_apply]⟩
  have htop : (LinearMap.range (extIn sub T)).topologicalClosure = ⊤ := by
    refine top_le_iff.mp ?_
    refine le_trans (le_of_eq ?_) hsub
    exact (Submodule.sup_orthogonal_of_hasOrthogonalProjection).symm
  have : Dense ((LinearMap.range (extIn sub T) : Submodule ℂ H) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact htop
  exact this

theorem norm_extOut_le (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    {y : E →L[ℂ] E} (hy : CommCmpr sub T y)
    (p : (↥T ⊗[ℂ] E) × ↥((cmapClosure sub T)ᗮ)) :
    ‖extOut sub T y p‖ ≤ ‖y‖ * ‖extIn sub T p‖ := by
  have horth : ⟪cmap sub T 1 p.1, (p.2 : H)⟫ = 0 := by
    refine Submodule.inner_right_of_mem_orthogonal
      (cmapRange_le_cmapClosure sub T ⟨p.1, rfl⟩) p.2.2
  have hpy : ‖extIn sub T p‖ ^ 2 = ‖cmap sub T 1 p.1‖ ^ 2 + ‖(p.2 : H)‖ ^ 2 := by
    rw [extIn_apply, sq, sq, sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hle : ‖cmap sub T 1 p.1‖ ≤ ‖extIn sub T p‖ := by
    nlinarith [norm_nonneg (cmap sub T 1 p.1), norm_nonneg (extIn sub T p),
      sq_nonneg ‖(p.2 : H)‖]
  calc ‖extOut sub T y p‖ = ‖cmap sub T y p.1‖ := rfl
    _ ≤ ‖y‖ * ‖cmap sub T 1 p.1‖ := norm_cmap_le sub T hy p.1
    _ ≤ ‖y‖ * ‖extIn sub T p‖ := by
        exact mul_le_mul_of_nonneg_left hle (norm_nonneg y)

/-- **The extension** `ŷ` of `y` to all of `ℋ`. -/
def yext (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H)) (y : E →L[ℂ] E) :
    H →L[ℂ] H :=
  LinearMap.extendOfNorm (extOut sub T y) (extIn sub T)

theorem yext_extIn (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    {y : E →L[ℂ] E} (hy : CommCmpr sub T y)
    (p : (↥T ⊗[ℂ] E) × ↥((cmapClosure sub T)ᗮ)) :
    yext sub T y (extIn sub T p) = extOut sub T y p :=
  LinearMap.extendOfNorm_eq (denseRange_extIn sub T)
    ⟨‖y‖, norm_extOut_le sub T hy⟩ p

/-- `ŷ (x f ζ) = x ỹ f ζ`. -/
theorem yext_cmap (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    {y : E →L[ℂ] E} (hy : CommCmpr sub T y) (z : ↥T ⊗[ℂ] E) :
    yext sub T y (cmap sub T 1 z) = cmap sub T y z := by
  have h := yext_extIn sub T hy (z, 0)
  rwa [show extIn sub T (z, 0) = cmap sub T 1 z by simp [extIn_apply],
    show extOut sub T y (z, 0) = cmap sub T y z from rfl] at h

/-- `ŷ` vanishes on `[𝒯 f ℋ]^⊥`. -/
theorem yext_orthogonal (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    {y : E →L[ℂ] E} (hy : CommCmpr sub T y) {u : H} (hu : u ∈ (cmapClosure sub T)ᗮ) :
    yext sub T y u = 0 := by
  have h := yext_extIn sub T hy (0, ⟨u, hu⟩)
  rwa [show extIn sub T (0, ⟨u, hu⟩) = u by simp [extIn_apply],
    show extOut sub T y (0, ⟨u, hu⟩) = 0 by simp [extOut_apply]] at h

/-! ### `ŷ` commutes with `𝒯` -/

omit [CompleteSpace E] in
theorem cmapRange_invariant (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    {x : H →L[ℂ] H} (hx : x ∈ T) {v : H} (hv : v ∈ cmapRange sub T) :
    x v ∈ cmapRange sub T := by
  obtain ⟨z, rfl⟩ := hv
  exact ⟨ltens (⟨x, hx⟩ : ↥T) z, cmap_ltens sub T 1 ⟨x, hx⟩ z⟩

omit [CompleteSpace E] in
theorem cmapClosure_invariant (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    {x : H →L[ℂ] H} (hx : x ∈ T) {v : H} (hv : v ∈ cmapClosure sub T) :
    x v ∈ cmapClosure sub T := by
  have hle : cmapClosure sub T ≤ Submodule.comap (x : H →ₗ[ℂ] H) (cmapClosure sub T) := by
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · intro v hv
      exact cmapRange_le_cmapClosure sub T (cmapRange_invariant sub T hx hv)
    · exact IsClosed.preimage x.continuous
        (cmapRange sub T).isClosed_topologicalClosure
  exact hle hv

omit [CompleteSpace E] in
theorem orthogonal_invariant (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    {x : H →L[ℂ] H} (hx : x ∈ T) {u : H} (hu : u ∈ (cmapClosure sub T)ᗮ) :
    x u ∈ (cmapClosure sub T)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  have hadj : ⟪v, x u⟫ = ⟪star x v, u⟫ := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  rw [hadj]
  exact (Submodule.mem_orthogonal _ _).mp hu _
    (cmapClosure_invariant sub T (StarMemClass.star_mem hx) hv)

/-- **`ŷ` lies in the commutant of `𝒯`.** -/
theorem yext_mem_vnComm (sub : E →L[ℂ] H) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    {y : E →L[ℂ] E} (hy : CommCmpr sub T y) :
    yext sub T y ∈ vnComm T := by
  refine mem_vnComm.mpr fun x hx => ?_
  refine ContinuousLinearMap.ext fun ζ => ?_
  show x (yext sub T y ζ) = yext sub T y (x ζ)
  obtain ⟨v, hv, u, hu, rfl⟩ := (cmapClosure sub T).exists_add_mem_mem_orthogonal ζ
  have hu0 : yext sub T y u = 0 := yext_orthogonal sub T hy hu
  have hxu0 : yext sub T y (x u) = 0 :=
    yext_orthogonal sub T hy (orthogonal_invariant sub T hx hu)
  have hgen : ∀ v ∈ cmapClosure sub T, x (yext sub T y v) = yext sub T y (x v) := by
    intro v hv
    have hmem : v ∈ closure ((cmapRange sub T : Submodule ℂ H) : Set H) := by
      rwa [← Submodule.topologicalClosure_coe]
    have hEq : Set.EqOn (fun ζ => x (yext sub T y ζ)) (fun ζ => yext sub T y (x ζ))
        ((cmapRange sub T : Submodule ℂ H) : Set H) := by
      rintro _ ⟨z, rfl⟩
      show x (yext sub T y (cmap sub T 1 z)) = yext sub T y (x (cmap sub T 1 z))
      rw [yext_cmap sub T hy, ← cmap_ltens sub T 1 (⟨x, hx⟩ : ↥T) z,
        yext_cmap sub T hy, cmap_ltens sub T y (⟨x, hx⟩ : ↥T) z]
    exact hEq.closure (x.continuous.comp (yext sub T y).continuous)
      ((yext sub T y).continuous.comp x.continuous) hmem
  calc x (yext sub T y (v + u)) = x (yext sub T y v) + x (yext sub T y u) := by
        rw [map_add, map_add]
    _ = yext sub T y (x v) := by rw [hu0, hgen v hv]; simp
    _ = yext sub T y (x v) + yext sub T y (x u) := by rw [hxu0]; simp
    _ = yext sub T y (x (v + u)) := by rw [map_add, map_add]

/-- **`ŷ` compresses back to `y`.** -/
theorem cmpr_yext {sub : E →L[ℂ] H} {e : H →L[ℂ] H} (h : IsCorner sub e)
    (T : StarSubalgebra ℂ (H →L[ℂ] H)) {y : E →L[ℂ] E} (hy : CommCmpr sub T y) :
    cmpr sub (yext sub T y) = y := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h1 : cmap sub T 1 ((1 : ↥T) ⊗ₜ[ℂ] v) = sub v := by
    rw [cmap_tmul]; simp
  have h2 : cmap sub T y ((1 : ↥T) ⊗ₜ[ℂ] v) = sub (y v) := by
    rw [cmap_tmul]; simp
  have h3 : yext sub T y (sub v) = sub (y v) := by
    rw [← h1, yext_cmap sub T hy, h2]
  rw [cmpr_apply, h3, h.apply_adjoint_apply]

/-! ## The pay-off

`(f 𝒯 f)^□ = 𝒯^□ f`: the commutant of the **compression** of `𝒯` by a
projection `f ∈ 𝒯`, computed in `B(fℋ)`, is the **reduction** of `𝒯^□`.
Equivalently — and this is how it is proved — the reduction `𝒯^□ f` of a von
Neumann algebra by a projection of its commutant is again a von Neumann
algebra, i.e. is bicommutant-closed.  `A/Proc/CornerTensor.lean`'s
`mem_vnComm_cornerAlg` is the other half: it identifies the commutant of the
*reduced* algebra, which is elementary. -/

/-- **The hard half of the reduction theorem.**  Every operator of `B(fℋ)`
commuting with the compression `f 𝒯 f` is itself the compression of an
element of `𝒯^□`.  No ultraweak continuity, no normality: the operator is
built by extending `y` along the dense subspace `𝒯 f ℋ`. -/
theorem exists_mem_vnComm_cmpr_eq {sub : E →L[ℂ] H} {e : H →L[ℂ] H}
    (h : IsCorner sub e) (T : StarSubalgebra ℂ (H →L[ℂ] H)) {y : E →L[ℂ] E}
    (hy : ∀ x ∈ T, cmpr sub x * y = y * cmpr sub x) :
    ∃ u ∈ vnComm T, cmpr sub u = y :=
  ⟨yext sub T y, yext_mem_vnComm sub T hy, cmpr_yext h T hy⟩

variable {sub : E →L[ℂ] H} {e : H →L[ℂ] H}

/-- **The reduction of a von Neumann algebra is bicommutant-closed.**  For a
von Neumann subalgebra `T ∋ e` the reduced algebra `T^□ e ⊆ B(eℋ)` equals its
own bicommutant. -/
theorem vnComm_vnComm_cornerAlg (h : IsCorner sub e)
    (T : StarSubalgebra ℂ (H →L[ℂ] H)) (hT : IsVNSubalgebra (H →L[ℂ] H) T)
    (heT : e ∈ T) :
    vnComm (vnComm (cornerAlg h (vnComm T) (le_vnComm_vnComm T heT)))
      = cornerAlg h (vnComm T) (le_vnComm_vnComm T heT) := by
  refine le_antisymm ?_ (le_vnComm_vnComm _)
  intro y hy
  have hcomm : ∀ x ∈ T, cmpr sub x * y = y * cmpr sub x := by
    intro x hx
    have hmem : cmpr sub x ∈ vnComm (cornerAlg h (vnComm T) (le_vnComm_vnComm T heT)) := by
      have : cext sub (cmpr sub x) ∈ T := by
        rw [cext_cmpr h]; exact mul_mem (mul_mem heT hx) heT
      exact (mem_vnComm_cornerAlg h (vnComm T) (le_vnComm_vnComm T heT) _).mpr
        (by rw [vnComm_vnComm T hT]; exact this)
    exact mem_vnComm.mp hy _ hmem
  obtain ⟨u, hu, hcu⟩ := exists_mem_vnComm_cmpr_eq h T hcomm
  exact ⟨u, hu, hcu⟩

/-- **The compression of a von Neumann algebra is a von Neumann algebra**, in
the form the reduction wants: `(f 𝒯 f)^□ = 𝒯^□ f`.  The left-hand side is the
commutant, computed in `B(fℋ)`, of the compressed algebra `cornerAlgVN`
(whose carrier is `cmpr sub '' T`, by `coe_cornerAlgVN`); the right-hand side
is the reduced algebra `cornerAlg` of `T^□` (carrier `cmpr sub '' T^□`). -/
theorem vnComm_cornerAlgVN (h : IsCorner sub e)
    (T : StarSubalgebra ℂ (H →L[ℂ] H)) (hT : IsVNSubalgebra (H →L[ℂ] H) T)
    (heT : e ∈ T) :
    vnComm (cornerAlgVN h T heT) = cornerAlg h (vnComm T) (le_vnComm_vnComm T heT) :=
  vnComm_vnComm_cornerAlg h T hT heT

/-- The reduction `T^□ e` of a von Neumann algebra by a projection `e` of its
commutant is a von Neumann subalgebra of `B(eℋ)`. -/
theorem isVNSubalgebra_cornerAlg (h : IsCorner sub e)
    (T : StarSubalgebra ℂ (H →L[ℂ] H)) (hT : IsVNSubalgebra (H →L[ℂ] H) T)
    (heT : e ∈ T) :
    IsVNSubalgebra (E →L[ℂ] E) (cornerAlg h (vnComm T) (le_vnComm_vnComm T heT)) :=
  vnComm_cornerAlgVN h T hT heT ▸ isVNSubalgebra_vnComm _

/-! ### Two small corner identities -/

theorem cmpr_e_mul (h : IsCorner sub e) (x : H →L[ℂ] H) :
    cmpr sub (e * x) = cmpr sub x := by
  have h1 : cmpr sub (star (e * x)) = cmpr sub (star x) := by
    rw [star_mul, h.star_eq, cmpr_mul_e h]
  have h2 := congrArg (fun t : E →L[ℂ] E => star t) h1
  simpa only [← cmpr_star, star_star] using h2

/-- If `z` commutes with the cut `e` and with `w`, the compressions of `z`
and `w` commute — the form of `cmpr_comm` needed when the cut lies in the
algebra and `z` in its commutant. -/
theorem cmpr_comm_of_comm (h : IsCorner sub e) {z w : H →L[ℂ] H}
    (hze : z * e = e * z) (hzw : z * w = w * z) :
    cmpr sub z * cmpr sub w = cmpr sub w * cmpr sub z := by
  have h1 : cmpr sub z * cmpr sub w = cmpr sub (z * w) := by
    rw [← cmpr_mul_mid h, hze, mul_assoc, cmpr_e_mul h]
  have h2 : cmpr sub w * cmpr sub z = cmpr sub (w * z) := by
    rw [← cmpr_mul_mid h, mul_assoc, ← hze, ← mul_assoc, cmpr_mul_e h]
  rw [h1, h2, hzw]

/-- `cornerAlg` does not depend on the membership proof, and is congruent in
its algebra argument. -/
theorem cornerAlg_congr (h : IsCorner sub e) {S S' : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hSS' : S = S') (he : e ∈ vnComm S) (he' : e ∈ vnComm S') :
    cornerAlg h S he = cornerAlg h S' he' := by
  subst hSS'; rfl

/-- **The reduction of a von Neumann algebra by a projection of its commutant
is a von Neumann algebra** — the form with the cut given in the commutant. -/
theorem isVNSubalgebra_cornerAlg' (h : IsCorner sub e)
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsVNSubalgebra (H →L[ℂ] H) S)
    (he : e ∈ vnComm S) :
    IsVNSubalgebra (E →L[ℂ] E) (cornerAlg h S he) := by
  have h1 := isVNSubalgebra_cornerAlg h (vnComm S) (isVNSubalgebra_vnComm S) he
  rwa [cornerAlg_congr h (vnComm_vnComm S hS) _ he] at h1

end Compression



/-! ## The consequence the reduction wants

**`CT` transports across a cut inside the algebra.**  If `e ∈ 𝒜` and `f ∈ ℬ`
are projections whose cut `e ⊗ f` *separates* `(𝒜 ⊗̄ ℬ)^□` — which is what
"central carrier `1`" buys — then the commutation theorem for the
**compressed** algebras `e𝒜e ⊆ B(eℋ)`, `fℬf ⊆ B(f𝒦)` implies it for `𝒜`
and `ℬ`.

This is the step `A/Proc/CornerTensor.lean` could not take: `relCT_of_CT`
transports across cuts `e ∈ 𝒜^□` — where "extension by zero" identifies the
commutant of the reduced algebra — while here the cut lies **in the algebra**,
and identifying `(e𝒜e)^□ = 𝒜^□e` is exactly `vnComm_cornerAlgVN` above.
Since the compressed algebras are where cyclic *and separating* vectors live
(`CommutationAmplify.lean`), this is the shape the last step of the reduction
consumes.  Note that no net of cuts is needed: one cut with central carrier
`1` suffices, because `u ↦ u(e ⊗ f)` is then injective on `(𝒜 ⊗̄ ℬ)^□`. -/

section Transport

variable {H K E F : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **`CT` transports across a cut with central carrier `1`.** -/
theorem CT_of_CT_compression {SA : StarSubalgebra ℂ (H →L[ℂ] H)}
    {SB : StarSubalgebra ℂ (K →L[ℂ] K)}
    (hA : IsVNSubalgebra (H →L[ℂ] H) SA) (hB : IsVNSubalgebra (K →L[ℂ] K) SB)
    {e : H →L[ℂ] H} {f : K →L[ℂ] K} {sube : E →L[ℂ] H} {subf : F →L[ℂ] K}
    (hse : IsCorner sube e) (hsf : IsCorner subf f)
    (heA : e ∈ SA) (hfB : f ∈ SB)
    (hsep : ∀ u ∈ vnComm (concreteTensor H K SA SB), u * opTensor e f = 0 → u = 0)
    (hCT : CT (cornerAlgVN hse SA heA) (cornerAlgVN hsf SB hfB)) :
    CT SA SB := by
  refine (CT_iff_le SA SB).mpr fun z hz => ?_
  have hP : IsCorner (opTensor sube subf) (opTensor e f) := hse.opTensor hsf
  set p : HT H K →L[ℂ] HT H K := opTensor e f with hpdef
  set P : HT E F →L[ℂ] HT H K := opTensor sube subf with hPdef
  have hpmem : p ∈ concreteTensor H K SA SB := opTensor_mem_concreteTensor heA hfB
  have hzp : z * p = p * z := (mem_vnComm.mp hz p hpmem).symm
  have hzs : star z ∈ vnComm (concreteTensor H K SA SB) := star_mem hz
  have hzsp : star z * p = p * star z := (mem_vnComm.mp hzs p hpmem).symm
  -- *Down*: the compression of `z` commutes with `𝒜_e ⊗̄ ℬ_f`.
  have hstep1 : cmpr P z ∈ vnComm (concreteTensor E F
      (cornerAlgVN hse SA heA) (cornerAlgVN hsf SB hfB)) := by
    have hstar : ∀ a ∈ ({cmpr P z, star (cmpr P z)} : Set (HT E F →L[ℂ] HT E F)),
        star a ∈ ({cmpr P z, star (cmpr P z)} : Set (HT E F →L[ℂ] HT E F)) := by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
      rcases ha with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (star_star _)
    obtain ⟨Y, hYvn, hYcoe⟩ := (commutant_basic_3'
      ({cmpr P z, star (cmpr P z)} : Set (HT E F →L[ℂ] HT E F)) hstar).1
    have hgen : ∀ a' ∈ cornerAlgVN hse SA heA, ∀ b' ∈ cornerAlgVN hsf SB hfB,
        opTensor a' b' ∈ Y := by
      intro a' ha' b' hb'
      rw [← SetLike.mem_coe, coe_cornerAlgVN hA] at ha'
      rw [← SetLike.mem_coe, coe_cornerAlgVN hB] at hb'
      obtain ⟨a, ha, rfl⟩ := ha'
      obtain ⟨b, hb, rfl⟩ := hb'
      have hmem : opTensor a b ∈ concreteTensor H K SA SB :=
        opTensor_mem_concreteTensor ha hb
      have hcp : opTensor (cmpr sube a) (cmpr subf b) = cmpr P (opTensor a b) := by
        rw [hPdef, cmpr_opTensor]
      have hYm : opTensor (cmpr sube a) (cmpr subf b)
          ∈ (Y : Set (HT E F →L[ℂ] HT E F)) := by
        rw [hYcoe, hcp]
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact cmpr_comm_of_comm hP hzp (mem_vnComm.mp hz _ hmem).symm
        · rw [← cmpr_star P z]
          exact cmpr_comm_of_comm hP hzsp (mem_vnComm.mp hzs _ hmem).symm
      exact hYm
    have hle := concreteTensor_le hYvn hgen
    refine mem_vnComm.mpr fun s hs => ?_
    have hsY : s ∈ (Y : Set (HT E F →L[ℂ] HT E F)) := hle hs
    rw [hYcoe] at hsY
    exact (hsY _ (Set.mem_insert _ _)).symm
  -- the commutation theorem for the compressed algebras, then
  -- `(e𝒜e)^□ = 𝒜^□e`
  rw [hCT, vnComm_cornerAlgVN hse SA hA heA, vnComm_cornerAlgVN hsf SB hB hfB]
    at hstep1
  -- *Up*: the compression of `𝒜^□ ⊗̄ ℬ^□` is a von Neumann algebra containing
  -- all the generators.
  have hCle : concreteTensor H K (vnComm SA) (vnComm SB)
      ≤ vnComm (concreteTensor H K SA SB) := concreteTensor_vnComm_le SA SB
  have hpC : p ∈ vnComm (concreteTensor H K (vnComm SA) (vnComm SB)) :=
    (le_vnComm_comm.mp hCle) hpmem
  have hle : concreteTensor E F
        (cornerAlg hse (vnComm SA) (le_vnComm_vnComm SA heA))
        (cornerAlg hsf (vnComm SB) (le_vnComm_vnComm SB hfB))
      ≤ cornerAlg hP (concreteTensor H K (vnComm SA) (vnComm SB)) hpC := by
    refine concreteTensor_le (isVNSubalgebra_cornerAlg' hP _
      (isVNSubalgebra_concreteTensor _ _) hpC) ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ⟨opTensor a b, opTensor_mem_concreteTensor ha hb, ?_⟩
    rw [hPdef, cmpr_opTensor]
  obtain ⟨c, hc, hcz⟩ := hle hstep1
  -- the cut separates, so `z = c`
  have h1 : cext P (cmpr P c) = cext P (cmpr P z) := by rw [hcz]
  rw [cext_cmpr hP, cext_cmpr hP] at h1
  have hcp : c * p = p * c := mem_vnComm.mp hpC c hc
  have h2 : c * p = z * p := by
    have hl : p * c * p = c * p := by
      rw [← hcp, mul_assoc, hP.mul_self]
    have hr : p * z * p = z * p := by
      rw [← hzp, mul_assoc, hP.mul_self]
    rw [← hl, ← hr, h1]
  have h3 : (z - c) * p = 0 := by rw [sub_mul, h2, sub_self]
  have h4 : z - c ∈ vnComm (concreteTensor H K SA SB) := sub_mem hz (hCle hc)
  have h5 : z - c = 0 := hsep _ h4 h3
  have h6 : z = c := by
    have := sub_eq_zero.mp h5
    exact this
  rw [h6]
  exact hc

/-! ### The separation hypothesis from central carrier `1`

`hsep` says that the cut `e ⊗ f` separates `(𝒜 ⊗̄ ℬ)^□`; that is exactly what
central carrier `1` gives, since the central carrier of a projection `e ∈ 𝒜`
is the projection onto `[𝒜 e ℋ]`.  Here the hypothesis is stated in the
density form `[𝒜 e ℋ] = ℋ` directly, which is what a consumer producing the
cut from a cyclic vector has in hand (`e = [𝒜^□ξ]` with `ξ` cyclic gives
`𝒜 e ℋ ⊇ 𝒜 ξ`, dense). -/

/-- The ket operator in the *second* variable, `y ↦ x ⊗ y`. -/
noncomputable def htKetR (x : H) : K →L[ℂ] HT H K :=
  LinearMap.mkContinuous ((hilbTensor H K).map x) ‖x‖
    (fun y => by
      show ‖htmul x y‖ ≤ ‖x‖ * ‖y‖
      rw [norm_htmul])

@[simp] theorem htKetR_apply (x : H) (y : K) : htKetR (K := K) x y = htmul x y := rfl

/-- **Central carrier `1` implies the separation hypothesis** of
`CT_of_CT_compression`: if `𝒜 e ℋ` is total in `ℋ` and `ℬ f 𝒦` is total in
`𝒦` then no nonzero element of `(𝒜 ⊗̄ ℬ)^□` is killed by `e ⊗ f`. -/
theorem sep_of_dense_carrier {SA : StarSubalgebra ℂ (H →L[ℂ] H)}
    {SB : StarSubalgebra ℂ (K →L[ℂ] K)} {e : H →L[ℂ] H} {f : K →L[ℂ] K}
    (hdA : Dense (Submodule.span ℂ {v : H | ∃ a ∈ SA, ∃ ξ : H, v = a (e ξ)} : Set H))
    (hdB : Dense (Submodule.span ℂ {w : K | ∃ b ∈ SB, ∃ η : K, w = b (f η)} : Set K))
    (u : HT H K →L[ℂ] HT H K) (hu : u ∈ vnComm (concreteTensor H K SA SB))
    (hup : u * opTensor e f = 0) : u = 0 := by
  -- on the generating vectors
  have key : ∀ a ∈ SA, ∀ b ∈ SB, ∀ (ξ : H) (η : K),
      u (htmul (a (e ξ)) (b (f η))) = 0 := by
    intro a ha b hb ξ η
    have h1 : htmul (a (e ξ)) (b (f η))
        = (opTensor a b) ((opTensor e f) (htmul ξ η)) := by
      rw [opTensor_apply, opTensor_apply]
    have h2 : u * opTensor a b = opTensor a b * u :=
      (mem_vnComm.mp hu _ (opTensor_mem_concreteTensor ha hb)).symm
    have h3 : u * opTensor a b * opTensor e f = 0 := by
      rw [h2, mul_assoc, hup, mul_zero]
    have h4 := congrArg (fun T : HT H K →L[ℂ] HT H K => T (htmul ξ η)) h3
    simpa [h1] using h4
  -- fill in the first variable
  have step2 : ∀ b ∈ SB, ∀ (η : K) (x : H), u (htmul x (b (f η))) = 0 := by
    intro b hb η
    have hz : u.comp (htKet (H := H) (b (f η))) = 0 := by
      refine ContinuousLinearMap.ext_on hdA ?_
      rintro v ⟨a, ha, ξ, rfl⟩
      simpa using key a ha b hb ξ η
    intro x
    have := congrArg (fun T : H →L[ℂ] HT H K => T x) hz
    simpa using this
  -- fill in the second variable
  refine ext_htmul fun x y => ?_
  have hz : u.comp (htKetR (K := K) x) = 0 := by
    refine ContinuousLinearMap.ext_on hdB ?_
    rintro w ⟨b, hb, η, rfl⟩
    simpa using step2 b hb η x
  have := congrArg (fun T : K →L[ℂ] HT H K => T y) hz
  simpa using this

/-- `CT_of_CT_compression` with the separation hypothesis replaced by the
central-carrier condition it comes from. -/
theorem CT_of_CT_compression_of_dense {SA : StarSubalgebra ℂ (H →L[ℂ] H)}
    {SB : StarSubalgebra ℂ (K →L[ℂ] K)}
    (hA : IsVNSubalgebra (H →L[ℂ] H) SA) (hB : IsVNSubalgebra (K →L[ℂ] K) SB)
    {e : H →L[ℂ] H} {f : K →L[ℂ] K} {sube : E →L[ℂ] H} {subf : F →L[ℂ] K}
    (hse : IsCorner sube e) (hsf : IsCorner subf f)
    (heA : e ∈ SA) (hfB : f ∈ SB)
    (hdA : Dense (Submodule.span ℂ {v : H | ∃ a ∈ SA, ∃ ξ : H, v = a (e ξ)} : Set H))
    (hdB : Dense (Submodule.span ℂ {w : K | ∃ b ∈ SB, ∃ η : K, w = b (f η)} : Set K))
    (hCT : CT (cornerAlgVN hse SA heA) (cornerAlgVN hsf SB hfB)) :
    CT SA SB :=
  CT_of_CT_compression hA hB hse hsf heA hfB
    (fun u hu hup => sep_of_dense_carrier hdA hdB u hu hup) hCT

end Transport

end Theses.A.Proc
