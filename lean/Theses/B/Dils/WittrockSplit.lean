/-
Thesis B companion: the note `wittrock-dil.tex`, Lemma 3 and Definition 4 to
Corollary 13 — the Wittrock correspondence, splitting off the commutant, and
the characterisation of Wittrock dilations through Paschke dilations
(Theorem 10).

Like `Wittrock.lean` this file has no thesis counterpart and carries no
DISP code; the item-by-item map from the note to the Lean names, and the
deviations from the note, are in the header of `Wittrock.lean`.  Nothing in
this file uses `sorry`.
-/
import Theses.B.Dils.Wittrock
import Theses.A.Proc.Duplicators

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra TensorProduct ENNReal
open Filter Topology Theses Theses.A.VN Theses.A.Proc

noncomputable section

namespace Theses.B.Dils

universe u v w

/-! ## Tools -/

theorem wncp_sub' {B C : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C] (f : NCPMap B C) (x y : B) :
    f (x - y) = f x - f y :=
  map_sub f.toCompletelyPositiveMap x y

theorem vtmul_add_right' {X E : Type u} [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
    [VonNeumannAlgebra X] [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
    [VonNeumannAlgebra E] (x : X) (a b : E) : x ⊗ᵥ (a + b) = x ⊗ᵥ a + x ⊗ᵥ b :=
  map_add ((vnTensor X E).map x) a b

theorem vtmul_sub_right' {X E : Type u} [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
    [VonNeumannAlgebra X] [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
    [VonNeumannAlgebra E] (x : X) (a b : E) : x ⊗ᵥ (a - b) = x ⊗ᵥ a - x ⊗ᵥ b :=
  map_sub ((vnTensor X E).map x) a b

section NMIUOfTensor

variable {X : Type u} {Y : Type v} {B : Type w}
  [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
  [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y] [VonNeumannAlgebra Y]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [VonNeumannAlgebra B]

/-- An ncp-map out of `𝒳 ⊗ 𝒴` that is unital and multiplicative on elementary
tensors is multiplicative: multiplication is separately ultraweakly
continuous (**45IV**, `mult_uws_cont`), and the elementary tensors span
an ultraweakly dense subspace (**108II**). -/
theorem ncp_tensor_mul (f : NCPMap (VNT X Y) B)
    (hmul : ∀ (x x' : X) (y y' : Y), f ((x * x') ⊗ᵥ (y * y')) = f (x ⊗ᵥ y) * f (x' ⊗ᵥ y'))
    (z z' : VNT X Y) : f (z * z') = f z * f z' := by
  let _ : TopologicalSpace B := ultraweak B
  have _ : T2Space B := vn_positive_basic_1.1
  have hf : @Continuous (VNT X Y) B (ultraweak _) (ultraweak B) ⇑f :=
    ((p_uwcont (ncpPositive f)).out 2 0).mp f.preservesDirSups'
  set fl := f.toCompletelyPositiveMap.toLinearMap
  have hγ := (vnTensor X Y).isTensorProduct
  have hel : ∀ (x x' : X) (y y' : Y), (x ⊗ᵥ y) * (x' ⊗ᵥ y') = (x * x') ⊗ᵥ (y * y') :=
    fun x x' y y' => (hγ.miu.2.1 x x' y y').symm
  -- first with an elementary tensor on the right
  have step : ∀ (x' : X) (y' : Y) (w : VNT X Y),
      f (w * (x' ⊗ᵥ y')) = f w * f (x' ⊗ᵥ y') := by
    intro x' y'
    have hc1 : @Continuous (VNT X Y) B (ultraweak _) (ultraweak B)
        fun w => f (w * (x' ⊗ᵥ y')) :=
      @Continuous.comp _ _ _ (ultraweak _) (ultraweak _) (ultraweak B) _ _ hf
        (mult_uws_cont _).2.1
    have hc2 : @Continuous (VNT X Y) B (ultraweak _) (ultraweak B)
        fun w => f w * f (x' ⊗ᵥ y') :=
      @Continuous.comp _ _ _ (ultraweak _) (ultraweak B) (ultraweak B) _ _
        (mult_uws_cont _).2.1 hf
    have key := tensor_linear_ext hγ (fl.comp (LinearMap.mulRight ℂ (x' ⊗ᵥ y')))
      ((LinearMap.mulRight ℂ (f (x' ⊗ᵥ y'))).comp fl) hc1 hc2
      (fun x y => by
        change f ((x ⊗ᵥ y) * (x' ⊗ᵥ y')) = f (x ⊗ᵥ y) * f (x' ⊗ᵥ y')
        rw [hel, hmul])
    intro w
    exact congrArg (fun k : VNT X Y →ₗ[ℂ] B => k w) key
  have hc1 : @Continuous (VNT X Y) B (ultraweak _) (ultraweak B) fun w => f (z * w) :=
    @Continuous.comp _ _ _ (ultraweak _) (ultraweak _) (ultraweak B) _ _ hf
      (mult_uws_cont _).1
  have hc2 : @Continuous (VNT X Y) B (ultraweak _) (ultraweak B) fun w => f z * f w :=
    @Continuous.comp _ _ _ (ultraweak _) (ultraweak B) (ultraweak B) _ _
      (mult_uws_cont _).1 hf
  have key := tensor_linear_ext hγ (fl.comp (LinearMap.mulLeft ℂ z))
    ((LinearMap.mulLeft ℂ (f z)).comp fl) hc1 hc2
    (fun x y => step x y z)
  exact congrArg (fun k : VNT X Y →ₗ[ℂ] B => k z') key

/-- A unital multiplicative ncp-map, as an nmiu-map (involutivity is that of
positive maps, **10IV**). -/
def nmiuOfNCP {A' : Type*} {B' : Type*} [CStarAlgebra A'] [PartialOrder A'] [StarOrderedRing A']
    [CStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
    (f : NCPMap A' B') (h1 : f 1 = 1) (hmul : ∀ a b, f (a * b) = f a * f b) :
    NMIUMap A' B' where
  toStarAlgHom :=
    { toFun := f
      map_one' := h1
      map_mul' := hmul
      map_zero' := map_zero f.toCompletelyPositiveMap
      map_add' := map_add f.toCompletelyPositiveMap
      commutes' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        change f.toCompletelyPositiveMap (r • 1) = r • 1
        rw [map_smul]
        exact congrArg (fun b => r • b) h1
      map_star' := fun z =>
        Theses.A.CStar.cstar_p_implies_i _
          (Theses.A.CStar.astara_pos_basic_2_cp _ (wit_ncp_cp f)) z }
  preservesDirSups' := f.preservesDirSups'

@[simp] theorem nmiuOfNCP_apply {A' : Type*} {B' : Type*} [CStarAlgebra A'] [PartialOrder A']
    [StarOrderedRing A'] [CStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
    (f : NCPMap A' B') (h1 : f 1 = 1) (hmul : ∀ a b, f (a * b) = f a * f b) (a : A') :
    nmiuOfNCP f h1 hmul a = f a := rfl

/-- An ncp-map out of `𝒳 ⊗ 𝒴` that is unital and multiplicative on
elementary tensors, as an nmiu-map. -/
def nmiuOfTensor (f : NCPMap (VNT X Y) B) (h1 : f 1 = 1)
    (hmul : ∀ (x x' : X) (y y' : Y), f ((x * x') ⊗ᵥ (y * y')) = f (x ⊗ᵥ y) * f (x' ⊗ᵥ y')) :
    NMIUMap (VNT X Y) B :=
  nmiuOfNCP f h1 (ncp_tensor_mul f hmul)

@[simp] theorem nmiuOfTensor_apply (f : NCPMap (VNT X Y) B) (h1 : f 1 = 1)
    (hmul : ∀ (x x' : X) (y y' : Y), f ((x * x') ⊗ᵥ (y * y')) = f (x ⊗ᵥ y) * f (x' ⊗ᵥ y'))
    (z : VNT X Y) : nmiuOfTensor f h1 hmul z = f z := rfl

end NMIUOfTensor

/-! ## The test algebra `ℂ²`

The note tests the universal property against `𝒳 ⊗ ℂ² ≅ 𝒳 ⊕ 𝒳`.  Test
objects must live in the universe of `ℰ`, so `ℂ²` is taken to be
`ℓ^∞({0,1}) = linf (ULift Bool)`; no identification with `𝒳 ⊕ 𝒳` is needed,
because the two coordinate slices `𝒳 ⊗ ℂ² → 𝒳` are built directly from the
evaluations and the right unitor. -/

section TestAlgebra

/-- `ℂ² = ℓ^∞({0,1})`, in universe `u`. -/
abbrev C2 : Type u := linf (ULift.{u} Bool)

/-- The first point of `{0,1}`. -/
def c2T : ULift.{u} Bool := ⟨true⟩

/-- The second point of `{0,1}`. -/
def c2F : ULift.{u} Bool := ⟨false⟩

theorem c2T_ne_c2F : c2T.{u} ≠ c2F.{u} := fun h => Bool.noConfusion (congrArg ULift.down h)

/-- The coordinate `v(b)` of `v ∈ ℂ²`. -/
abbrev c2ev (v : C2.{u}) (b : ULift.{u} Bool) : ℂ := (v : ∀ _ : ULift.{u} Bool, ℂ) b

/-- The minimal projection `δ_b` of `ℂ²`. -/
def c2ind (b : ULift.{u} Bool) : C2.{u} := lpKappa b 1

theorem c2ind_apply (b b' : ULift.{u} Bool) :
    c2ev (c2ind b) b' = if b' = b then 1 else 0 := by
  by_cases h : b' = b
  · subst h; simp only [ite_true]; exact lpKappa_apply_self _ _
  · simp only [h, ite_false]; exact lpKappa_apply_ne _ _ h

theorem c2ind_nonneg (b : ULift.{u} Bool) : 0 ≤ c2ind b := by
  rw [lp_infty_nonneg_iff]
  intro b'
  change 0 ≤ c2ev (c2ind b) b'
  rw [c2ind_apply]
  split_ifs <;> norm_num

theorem c2ind_le_one (b : ULift.{u} Bool) : c2ind b ≤ 1 := by
  rw [lp_infty_le_iff]
  intro b'
  change c2ev (c2ind b) b' ≤ c2ev 1 b'
  rw [c2ind_apply, show c2ev (1 : C2.{u}) b' = 1 from rfl]
  split_ifs <;> norm_num

/-- The evaluation `v ↦ v(b)` is ultraweakly continuous. -/
theorem continuous_c2ev (b : ULift.{u} Bool) :
    @Continuous C2.{u} ℂ (ultraweak _) _ fun v => c2ev v b :=
  continuous_ultraweak_npFunctional (lpNP (𝒜 := fun _ : ULift.{u} Bool => ℂ) b complexIdNP)

/-- A non-negative complex scalar times a positive element is positive. -/
theorem complex_smul_nonneg {E : Type*} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] {z : ℂ} (hz : 0 ≤ z) {a : E} (ha : 0 ≤ a) : 0 ≤ z • a := by
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 ≤ r ∧ (r : ℂ) = z :=
    ⟨z.re, Complex.nonneg_iff.mp hz |>.1, by
      apply Complex.ext <;> simp [(Complex.nonneg_iff.mp hz).2.symm]⟩
  exact Theses.A.CStar.ofReal_smul_nonneg ha hr

variable {E : Type u} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
  [VonNeumannAlgebra E]

/-- `v ↦ v(0)·a + v(1)·b : ℂ² → ℰ`, as a linear map. -/
def bitLin (a b : E) : C2.{u} →ₗ[ℂ] E where
  toFun v := c2ev v c2T • a + c2ev v c2F • b
  map_add' v w := by
    change (c2ev v c2T + c2ev w c2T) • a + (c2ev v c2F + c2ev w c2F) • b = _
    rw [add_smul, add_smul]; abel
  map_smul' c v := by
    change (c * c2ev v c2T) • a + (c * c2ev v c2F) • b = _
    rw [RingHom.id_apply, smul_add, mul_smul, mul_smul]

omit [VonNeumannAlgebra E] in
theorem bitLin_pos {a b : E} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Theses.A.CStar.IsPositiveMap (bitLin a b) := by
  intro v hv
  rw [lp_infty_nonneg_iff] at hv
  exact add_nonneg (complex_smul_nonneg (hv _) ha) (complex_smul_nonneg (hv _) hb)

/-- `v ↦ v(0)·a + v(1)·b : ℂ² → ℰ` is an ncp-map for positive `a`, `b`:
positive maps out of a commutative algebra are cp (**34IX**), and it is
normal because it is ultraweakly continuous (**44XV**). -/
def bitNCP {a b : E} (ha : 0 ≤ a) (hb : 0 ≤ b) : NCPMap C2.{u} E where
  toCompletelyPositiveMap :=
    { toLinearMap := bitLin a b
      map_cstarMatrix_nonneg' :=
        (Theses.A.CStar.cp_iff _).out 0 1 |>.mp
          (Theses.A.CStar.cp_commutative_dom _ (bitLin_pos ha hb)) }
  preservesDirSups' := by
    let f : C2.{u} →ₚ[ℂ] E :=
      { toLinearMap := bitLin a b
        monotone' := fun v w hvw => by
          have h := bitLin_pos ha hb (w - v) (sub_nonneg.mpr hvw)
          rwa [map_sub, sub_nonneg] at h }
    refine ((p_uwcont f).out 0 2).mp ?_
    refine continuous_ultraweak_of_forall _ fun ω => ?_
    have he : (fun v => (ω (f v) : ℂ)) = fun v => c2ev v c2T * ω a + c2ev v c2F * ω b := by
      funext v
      change ω.toPositiveLinearMap (c2ev v c2T • a + c2ev v c2F • b) = _
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      rfl
    rw [he]
    let _ : TopologicalSpace C2.{u} := ultraweak _
    exact ((continuous_c2ev c2T).mul continuous_const).add
      ((continuous_c2ev c2F).mul continuous_const)

theorem bitNCP_apply {a b : E} (ha : 0 ≤ a) (hb : 0 ≤ b) (v : C2.{u}) :
    bitNCP ha hb v = c2ev v c2T • a + c2ev v c2F • b := rfl

theorem bitNCP_ind {a b : E} (ha : 0 ≤ a) (hb : 0 ≤ b) : bitNCP ha hb (c2ind c2T) = a := by
  rw [bitNCP_apply, c2ind_apply, c2ind_apply]
  simp [c2T_ne_c2F.symm]

theorem bitNCP_one {a b : E} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    bitNCP ha hb 1 = a + b := by
  rw [bitNCP_apply, show c2ev (1 : C2.{u}) c2T = 1 from rfl,
    show c2ev (1 : C2.{u}) c2F = 1 from rfl, one_smul, one_smul]

end TestAlgebra

section Slices

variable (X : Type u) [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [VonNeumannAlgebra X]

/-- The slice `x ⊗ v ↦ v(b)·x : 𝒳 ⊗ ℂ² → 𝒳`: `id ⊗ ev_b` followed by the
right unitor (**119IVb**). -/
def c2Slice (b : ULift.{u} Bool) : NMIUMap (VNT X C2.{u}) X :=
  nmiuComp (rightUnitor X) (tmapM (nmiuId X) (linfEval (ULift.{u} Bool) b))

theorem c2Slice_apply (b : ULift.{u} Bool) (x : X) (v : C2.{u}) :
    c2Slice X b (x ⊗ᵥ v) = c2ev v b • x := by
  rw [c2Slice, nmiuComp_apply, tmapM_apply, rightUnitor_apply, nmiuId_apply, linfEval_apply]

variable {X} {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The ncp-map `x ⊗ v ↦ v(0)ψ₁(x) + v(1)ψ₂(x) : 𝒳 ⊗ ℂ² → 𝒜` of the note
(its `(x, y) ↦ ψ₁(x) + ψ₂(y)` on `𝒳 ⊕ 𝒳`). -/
def c2Pair (ψ₁ ψ₂ : NCPMap X A) : NCPMap (VNT X C2.{u}) A :=
  (exists_ncpAdd (ncpComp ψ₁ (nmiuNCP (c2Slice X c2T)))
    (ncpComp ψ₂ (nmiuNCP (c2Slice X c2F)))).choose

theorem c2Pair_apply (ψ₁ ψ₂ : NCPMap X A) (x : X) (v : C2.{u}) :
    c2Pair ψ₁ ψ₂ (x ⊗ᵥ v) = c2ev v c2T • ψ₁ x + c2ev v c2F • ψ₂ x := by
  rw [c2Pair, (exists_ncpAdd _ _).choose_spec, ncpComp_apply, ncpComp_apply,
    nmiuNCP_apply, nmiuNCP_apply, c2Slice_apply, c2Slice_apply, wncp_smul, wncp_smul]

end Slices

/-! ## Lemma 3: the Wittrock correspondence -/

section Correspondence

variable {X E A : Type u}
  [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
  [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E] [VonNeumannAlgebra E]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]

/-- The note's **Lemma 3** (the Wittrock correspondence, the analogue of
**157IV**): for a Wittrock dilation `h : 𝒳 ⊗ ℰ → 𝒜` of `φ`, the map
`e ↦ h(· ⊗ e)` is a bijection from the effects `[0,1]_ℰ` onto the set
`[0,φ]_ncp` of **157II** (`ncpInterval`): the maps `ψ` for which `ψ` and
`φ − ψ` are ncp.

The note's proof: `h(· ⊗ e)` and `h(· ⊗ (1 − e))` are ncp and sum to `φ`.
For `ψ ∈ [0,φ]_ncp`, a mediator for `x ⊗ v ↦ v(0)ψ(x) + v(1)(φ − ψ)(x)`
(`c2Pair`, on `𝒳 ⊗ ℂ²`) is unital by Remark 2, so it is
`v ↦ v(0)e + v(1)(1 − e)` (`bitNCP`) for an effect `e` with `h(· ⊗ e) = ψ`.
For injectivity, two effects `e₁`, `e₂` with `h(· ⊗ e₁) = h(· ⊗ e₂)` give two
mediators for that map (written here as `h ∘ (id ⊗ κ_{e₁})` with
`κ_e = bitNCP e (1 − e)`), so `e₁ = e₂` by uniqueness.  `φ` is a bare
function; it is ncp anyway, being `h(· ⊗ 1)`. -/
theorem wittrock_correspondence (φ : X → A) (h : NCPMap (VNT X E) A)
    (hW : IsWittrockDilationOf φ E h) :
    Set.BijOn (fun e x => h (x ⊗ᵥ e)) (effects E) (ncpInterval φ) := by
  have hκ1 : ∀ {e : E} (he : e ∈ effects E), bitNCP he.1 (sub_nonneg.mpr he.2) 1 = 1 :=
    fun he => by rw [bitNCP_one, add_sub_cancel]
  refine ⟨fun e he => ?_, fun e₁ he₁ e₂ he₂ h12 => ?_, fun ψ hψ => ?_⟩
  · -- `h(· ⊗ e)` and `h(· ⊗ (1 − e))` are ncp and sum to `φ`
    have hncp : ∀ b : E, 0 ≤ b → ∃ δ : NCPMap X A, ∀ x, δ x = h (x ⊗ᵥ b) := by
      intro b hb
      obtain ⟨f, hf⟩ := (tensor_simple_facts_5 (A := E) (B := X) b hb).1
      exact ⟨ncpComp h (ncpComp (nmiuNCP (braiding E X)) f), fun x => by
        rw [ncpComp_apply, ncpComp_apply, nmiuNCP_apply, hf, braiding_apply]⟩
    obtain ⟨δ₁, hδ₁⟩ := hncp e he.1
    obtain ⟨δ₂, hδ₂⟩ := hncp (1 - e) (sub_nonneg.mpr he.2)
    refine ⟨⟨δ₁, fun x => ?_⟩, ⟨δ₂, fun x => ?_⟩⟩
    · change h (x ⊗ᵥ e) = 0 + δ₁ x
      rw [zero_add, hδ₁]
    · change φ x = h (x ⊗ᵥ e) + δ₂ x
      rw [hδ₂, ← wncp_add, ← vtmul_add_right', add_sub_cancel, hW.1]
  · -- injective: `κ_{e₁}` and `κ_{e₂}` both mediate for `h' = h ∘ (id ⊗ κ_{e₁})`
    set h' := ncpComp h (tmap (ncpId X) (bitNCP he₁.1 (sub_nonneg.mpr he₁.2)))
    have hh' : ∀ x, h' (x ⊗ᵥ (1 : C2.{u})) = φ x := by
      intro x
      rw [ncpComp_apply, tmap_apply, ncpId_apply, hκ1 he₁, hW.1]
    have hmed : ∀ {e : E} (he : e ∈ effects E), (∀ x, h (x ⊗ᵥ e) = h (x ⊗ᵥ e₁)) →
        IsWittrockMediator h h' (bitNCP he.1 (sub_nonneg.mpr he.2)) := by
      intro e he hee
      refine (isWittrockMediator_iff_tmap _ _ _).mpr ⟨fun x => ?_, fun z => ?_⟩
      · rw [tmap_apply, ncpId_apply, hκ1 he]
      · have key : ncpComp h (tmap (ncpId X) (bitNCP he.1 (sub_nonneg.mpr he.2))) = h' := by
          refine ncp_ext_vnt _ _ fun x v => ?_
          rw [ncpComp_apply, ncpComp_apply, tmap_apply, tmap_apply, ncpId_apply,
            bitNCP_apply, bitNCP_apply, vtmul_add_right', vtmul_add_right',
            EqL.vtmul_smul_right, EqL.vtmul_smul_right, EqL.vtmul_smul_right,
            EqL.vtmul_smul_right, vtmul_sub_right', vtmul_sub_right', wncp_add, wncp_add,
            wncp_smul, wncp_smul, wncp_smul, wncp_smul, wncp_sub', wncp_sub', hee]
        rw [← key, ncpComp_apply]
    have hu := (hW.2 C2.{u} h' hh').unique (hmed he₁ fun _ => rfl)
      (hmed he₂ fun x => (congrFun h12 x).symm)
    have := congrArg (fun κ : NCPMap C2.{u} E => κ (c2ind c2T)) hu
    simpa only [bitNCP_ind] using this
  · -- surjective: test against `x ⊗ v ↦ v(0)ψ(x) + v(1)(φ − ψ)(x)`
    obtain ⟨⟨δ₁, hδ₁⟩, ⟨δ₂, hδ₂⟩⟩ := hψ
    have hψδ : ∀ x, ψ x = δ₁ x := fun x => by rw [hδ₁ x, zero_add]
    by_cases hXn : Nontrivial X
    swap
    · -- `𝒳 = {0}`: both sides vanish
      rw [not_nontrivial_iff_subsingleton] at hXn
      refine ⟨0, ⟨le_rfl, zero_le_one⟩, funext fun x => ?_⟩
      change h ((vnTensor X E).map x 0) = ψ x
      rw [map_zero, wncp_zero, hψδ, Subsingleton.elim x 0, wncp_zero]
    set h' := c2Pair δ₁ δ₂
    have hh' : ∀ x, h' (x ⊗ᵥ (1 : C2.{u})) = φ x := by
      intro x
      rw [c2Pair_apply, show c2ev (1 : C2.{u}) c2T = 1 from rfl,
        show c2ev (1 : C2.{u}) c2F = 1 from rfl, one_smul, one_smul, hδ₂, hψδ]
    obtain ⟨τ, hτ, -⟩ := hW.2 C2.{u} h' hh'
    obtain ⟨hτ1, hτh⟩ := (isWittrockMediator_iff_tmap _ _ _).mp hτ
    -- Remark 2: `τ` is unital
    have hτu : τ 1 = 1 := by
      refine one_vtmul_injective (X := X) ?_
      have := hτ1 1
      rwa [tmap_apply, ncpId_apply] at this
    refine ⟨τ (c2ind c2T), ⟨ncpMap_nonneg τ (c2ind_nonneg _), ?_⟩, funext fun x => ?_⟩
    · have := OrderHomClass.mono τ.toCompletelyPositiveMap (c2ind_le_one c2T)
      rwa [show τ.toCompletelyPositiveMap 1 = τ 1 from rfl, hτu] at this
    · have := hτh (x ⊗ᵥ c2ind c2T)
      rw [tmap_apply, ncpId_apply, c2Pair_apply, c2ind_apply, c2ind_apply] at this
      simp only [ite_true, c2T_ne_c2F.symm, ite_false, one_smul, zero_smul, add_zero] at this
      rw [hψδ]
      exact this

end Correspondence

section Misc

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [VonNeumannAlgebra A]

/-- A positive element below both a projection `p` and its complement is `0`
(the private lemma of the same name in `A/Proc/Measurement.lean`, whose
proof this repeats). -/
theorem eq_zero_of_le_proj_le_perp' {x p : A} (hx : 0 ≤ x) (hp : IsStarProjection p)
    (h1 : x ≤ p) (h2 : x ≤ 1 - p) : x = 0 := by
  have hc1 : (1 - p) * x * (1 - p) = 0 := by
    have hle : (1 - p) * x * (1 - p) ≤ (1 - p) * p * (1 - p) := by
      have := star_left_conjugate_le_conjugate h1 (1 - p)
      rwa [star_sub, star_one, hp.isSelfAdjoint.star_eq] at this
    have hzero : (1 - p) * p * (1 - p) = 0 := by
      have hpp : p * p = p := hp.isIdempotentElem
      noncomm_ring [hpp]
    rw [hzero] at hle
    have hge : (0 : A) ≤ (1 - p) * x * (1 - p) := by
      have := star_left_conjugate_nonneg hx (1 - p)
      rwa [star_sub, star_one, hp.isSelfAdjoint.star_eq] at this
    exact le_antisymm hle hge
  have hc2 : p * x * p = 0 := by
    have hle : p * x * p ≤ p * (1 - p) * p := by
      have := star_left_conjugate_le_conjugate h2 p
      rwa [hp.isSelfAdjoint.star_eq] at this
    have hzero : p * (1 - p) * p = 0 := by
      have hpp : p * p = p := hp.isIdempotentElem
      noncomm_ring [hpp]
    rw [hzero] at hle
    have hge : (0 : A) ≤ p * x * p := by
      have := star_left_conjugate_nonneg hx p
      rwa [hp.isSelfAdjoint.star_eq] at this
    exact le_antisymm hle hge
  have hce1 : ceil x ≤ p := by
    have := (ceil_le_perp_iff hx hp.one_sub).mpr hc1
    rwa [sub_sub_cancel] at this
  have hce2 : ceil x ≤ 1 - p := (ceil_le_perp_iff hx hp).mpr hc2
  have e1 : p * x = x := ((ceil_basic_1 x p hx hp).out 2 0).mp hce1
  have e2 : (1 - p) * x = x :=
    ((ceil_basic_1 x (1 - p) hx hp.one_sub).out 2 0).mp hce2
  have h3 : (1 - p) * x = x - p * x := by noncomm_ring
  rw [h3, e1, sub_self] at e2
  exact e2.symm

/-- The (non-unital) inclusion `c𝒜 ⊆ 𝒜` of the corner of a central
projection, as an ncp-map: a ∗-homomorphism is cp (**34IV**), and suprema
of the corner are suprema in `𝒜` (`CentralProj.saIncl_isLUB`). -/
def centralInclNCP (c : CentralProj A) : NCPMap c.sub A where
  toCompletelyPositiveMap :=
    { toLinearMap :=
        { toFun := fun y => (y : A)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_cstarMatrix_nonneg' :=
        (Theses.A.CStar.cp_iff _).out 0 1 |>.mp
          (Theses.A.CStar.cp_of_mi _ (fun _ _ => rfl) (fun _ => rfl)) }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have h := isLUB_val_of_isLUB (hne.image _) (c.saIncl_isLUB hne hdir hlub)
    rwa [← Set.image_comp] at h

@[simp] theorem centralInclNCP_apply (c : CentralProj A) (y : c.sub) :
    centralInclNCP c y = (y : A) := rfl

end Misc


/-! ## Tools on von Neumann subalgebras and tensor products -/

section SubTools

/-- The intersection of two von Neumann subalgebras is one. -/
theorem isVNSubalgebra_inf {P : Type*} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
    {R S : StarSubalgebra ℂ P} (hR : IsVNSubalgebra P R) (hS : IsVNSubalgebra P S) :
    IsVNSubalgebra P (R ⊓ S) := by
  refine ⟨?_, fun D s hD hne hdir hlub => ?_⟩
  · rw [StarSubalgebra.coe_inf]
    exact hR.isClosed.inter hS.isClosed
  · exact ⟨hR.dirSup_mem D s (fun d hd => (hD d hd).1) hne hdir hlub,
      hS.dirSup_mem D s (fun d hd => (hD d hd).2) hne hdir hlub⟩

/-- An ultraweakly continuous linear map out of `𝒳 ⊗ 𝒴` that sends every
elementary tensor into an ultraweakly closed subspace `S` sends everything
into `S` (**108II**). -/
theorem tensor_mem_of_forall {X Y Q : Type*}
    [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
    [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y] [VonNeumannAlgebra Y]
    [CStarAlgebra Q] [PartialOrder Q] [StarOrderedRing Q] [VonNeumannAlgebra Q]
    (F : VNT X Y →ₗ[ℂ] Q) (hF : @Continuous (VNT X Y) Q (ultraweak _) (ultraweak Q) F)
    (S : Submodule ℂ Q) (hS : @IsClosed Q (ultraweak Q) (S : Set Q))
    (h : ∀ x y, F (x ⊗ᵥ y) ∈ S) (z : VNT X Y) : F z ∈ S := by
  let _ : TopologicalSpace (VNT X Y) := ultraweak _
  let _ : TopologicalSpace Q := ultraweak Q
  have hT : IsClosed ((S.comap F : Submodule ℂ (VNT X Y)) : Set (VNT X Y)) := hS.preimage hF
  have hspan : Submodule.span ℂ {t : VNT X Y | ∃ a b, t = (vnTensor X Y).map a b}
      ≤ S.comap F :=
    Submodule.span_le.mpr fun t ⟨a, b, ht⟩ => ht ▸ h a b
  have hz : z ∈ closure (Submodule.span ℂ {t : VNT X Y | ∃ a b, t = (vnTensor X Y).map a b}
      : Set (VNT X Y)) := by
    rw [(vnTensor X Y).isTensorProduct.dense.closure_eq]; trivial
  exact hT.closure_subset_iff.mpr hspan hz

/-- A von Neumann subalgebra is ultraweakly closed (**75VIII**), as a
submodule. -/
theorem isClosed_ultraweak_vnsub {P : Type*} [CStarAlgebra P] [PartialOrder P]
    [StarOrderedRing P] [VonNeumannAlgebra P] (R : StarSubalgebra ℂ P)
    (hR : IsVNSubalgebra P R) :
    @IsClosed P (ultraweak P) ((Subalgebra.toSubmodule R.toSubalgebra : Submodule ℂ P) : Set P) :=
  (vnsac R hR).2

/-- The tensor product of two nmiu-isomorphisms is one. -/
theorem tmapM_bijective' {A₁ B₁ C₁ D₁ : Type*}
    [CStarAlgebra A₁] [PartialOrder A₁] [StarOrderedRing A₁] [VonNeumannAlgebra A₁]
    [CStarAlgebra B₁] [PartialOrder B₁] [StarOrderedRing B₁] [VonNeumannAlgebra B₁]
    [CStarAlgebra C₁] [PartialOrder C₁] [StarOrderedRing C₁] [VonNeumannAlgebra C₁]
    [CStarAlgebra D₁] [PartialOrder D₁] [StarOrderedRing D₁] [VonNeumannAlgebra D₁]
    (f : NMIUMap A₁ C₁) (hf : Function.Bijective f) (g : NMIUMap B₁ D₁)
    (hg : Function.Bijective g) : Function.Bijective (tmapM f g) := by
  set f' := nmiuSymm f hf
  set g' := nmiuSymm g hg
  have h1 : nmiuNCP (nmiuComp (tmapM f' g') (tmapM f g)) = nmiuNCP (nmiuId _) :=
    ncp_ext_vnt _ _ fun a b => by
      rw [nmiuNCP_apply, nmiuNCP_apply, nmiuComp_apply, tmapM_apply, tmapM_apply,
        nmiuSymm_apply_apply, nmiuSymm_apply_apply, nmiuId_apply]
  have h2 : nmiuNCP (nmiuComp (tmapM f g) (tmapM f' g')) = nmiuNCP (nmiuId _) :=
    ncp_ext_vnt _ _ fun a b => by
      rw [nmiuNCP_apply, nmiuNCP_apply, nmiuComp_apply, tmapM_apply, tmapM_apply,
        nmiuSymm_apply_apply', nmiuSymm_apply_apply', nmiuId_apply]
  refine ⟨fun z z' hzz => ?_, fun z => ⟨tmapM f' g' z, ?_⟩⟩
  · have e1 := congrArg (fun k : NCPMap _ _ => k z) h1
    have e2 := congrArg (fun k : NCPMap _ _ => k z') h1
    simp only [nmiuNCP_apply, nmiuComp_apply, nmiuId_apply] at e1 e2
    rw [← e1, ← e2, hzz]
  · have e := congrArg (fun k : NCPMap _ _ => k z) h2
    simpa only [nmiuNCP_apply, nmiuComp_apply, nmiuId_apply] using e

end SubTools

/-! ## Definition 4: splitting off the commutant -/

section Split

variable {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  [VonNeumannAlgebra P]

/-- A von Neumann subalgebra `ℛ` of `𝒫`, as a von Neumann algebra. -/
abbrev SubVN (R : StarSubalgebra ℂ P) (hR : IsVNSubalgebra P R) : Type u :=
  Theses.A.Proc.VNSub P R hR

/-- The commutant `ℛ^□` of `ℛ` in `𝒫`, as a von Neumann algebra. -/
abbrev CommVN (R : StarSubalgebra ℂ P) : Type u :=
  Theses.A.Proc.VNSub P (relComm R) (isVNSubalgebra_relComm R)

/-- The note's **Definition 4**: a von Neumann subalgebra `ℛ` of `𝒫`
**splits off its commutant in `𝒫`** if `a ⊗ t ↦ at` extends to an
nmiu-map `ℛ ⊗ ℛ^□ → 𝒫`, where `ℛ^□` is the commutant of `ℛ` in `𝒫`
(`relComm`). -/
def SplitsOffCommutant (R : StarSubalgebra ℂ P) (hR : IsVNSubalgebra P R) : Prop :=
  ∃ Ψ : NMIUMap (VNT (SubVN R hR) (CommVN R)) P,
    ∀ a t, Ψ (a ⊗ᵥ t) = a.val * t.val

end Split

/-! ## Lemma 9: reduction from `𝒳` to `ϱ(𝒳)` -/

section Reduction

variable {X : Type u} [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [VonNeumannAlgebra X]
  {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P] [VonNeumannAlgebra P]

/-- `ϱ(𝒳)`, the range of `ϱ`, a von Neumann subalgebra of `𝒫` (**69IVb**). -/
abbrev rangeSub (ρ : NMIUMap X P) : StarSubalgebra ℂ P := ρ.toStarAlgHom.range

/-- The note's `j : ϱ(𝒳) → 𝒳`: an ncp-map with `ϱ ∘ j = id`.  By **69IVa**
`ϱ` factors as the compression onto `c𝒳` (`c` central) followed by an
injective nmiu-map `H`; `j` is the inverse of the corestriction of `H`
followed by the inclusion `c𝒳 ⊆ 𝒳`. -/
theorem exists_range_section (ρ : NMIUMap X P) :
    ∃ j : NCPMap (SubVN (rangeSub ρ) (nmiu_image ρ)) X, ∀ a, ρ (j a) = a.val := by
  obtain ⟨c, G, H, -, -, hH, hGs, hHi, hfa⟩ :=
    nmiu_factors_maps ρ (nmiuP ρ) ρ.preservesDirSups' (fun _ => rfl)
  have hmem : ∀ y, H y ∈ rangeSub ρ := fun y => ⟨(y : X), (hH y).symm⟩
  have hbij : Function.Bijective (nmiuCorestrict H (rangeSub ρ) (nmiu_image ρ) hmem) := by
    refine nmiuCorestrict_bijective _ _ _ _ hHi ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨G x, (hfa x).symm⟩
  set j₀ := nmiuSymm _ hbij
  refine ⟨ncpComp (centralInclNCP c) (nmiuNCP j₀), fun a => ?_⟩
  rw [ncpComp_apply, nmiuNCP_apply, centralInclNCP_apply, ← hH]
  exact congrArg Theses.A.Proc.VNSub.val (nmiuSymm_apply_apply' _ hbij a)

/-- The note's **Lemma 9**: `ϱ(𝒳)` splits off its commutant in `𝒫` iff `x ⊗ t ↦ ϱ(x)t`
extends to an nmiu-map `𝒳 ⊗ ϱ(𝒳)^□ → 𝒫`. -/
theorem splitsOffCommutant_range_iff (ρ : NMIUMap X P) :
    SplitsOffCommutant (rangeSub ρ) (nmiu_image ρ) ↔
      ∃ Ψ : NMIUMap (VNT X (RangeComm ρ)) P, ∀ x t, Ψ (x ⊗ᵥ t) = ρ x * t.val := by
  constructor
  · rintro ⟨Ψ, hΨ⟩
    set ρ' := nmiuCorestrict ρ (rangeSub ρ) (nmiu_image ρ) fun x => ⟨x, rfl⟩
    refine ⟨nmiuComp Ψ (tmapM ρ' (nmiuId _)), fun x t => ?_⟩
    rw [nmiuComp_apply, tmapM_apply, hΨ, nmiuId_apply]
    rfl
  · rintro ⟨m, hm⟩
    obtain ⟨j, hj⟩ := exists_range_section ρ
    set f := ncpComp (nmiuNCP m) (tmap j (ncpId (RangeComm ρ)))
    have hf : ∀ a t, f (a ⊗ᵥ t) = a.val * t.val := by
      intro a t
      rw [ncpComp_apply, tmap_apply, nmiuNCP_apply, ncpId_apply, hm, hj]
    have hone : ∀ {Y Z : Type u} [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y]
        [VonNeumannAlgebra Y] [CStarAlgebra Z] [PartialOrder Z] [StarOrderedRing Z]
        [VonNeumannAlgebra Z], ((1 : Y) ⊗ᵥ (1 : Z)) = 1 :=
      fun {Y Z} _ _ _ _ _ _ _ _ => (vnTensor Y Z).isTensorProduct.miu.1
    have h1 : f 1 = 1 := by
      rw [← hone, hf]
      exact one_mul _
    have hmul : ∀ (a a' : SubVN (rangeSub ρ) (nmiu_image ρ)) (t t' : RangeComm ρ),
        f ((a * a') ⊗ᵥ (t * t')) = f (a ⊗ᵥ t) * f (a' ⊗ᵥ t') := by
      intro a a' t t'
      rw [hf, hf, hf]
      have hc : t.val * a'.val = a'.val * t.val :=
        ((mem_relComm.mp t.property) a'.val a'.property).symm
      change a.val * a'.val * (t.val * t'.val) = a.val * t.val * (a'.val * t'.val)
      rw [mul_assoc, ← mul_assoc a'.val, ← hc, mul_assoc, mul_assoc]
    exact ⟨nmiuOfTensor f h1 hmul, fun a t => hf a t⟩

end Reduction

/-! ## Theorem 10 -/

section Main

variable {X : Type u} [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [VonNeumannAlgebra X]
  {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P] [VonNeumannAlgebra P]
  {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]

/-- The zero map into the zero algebra, as an nmiu-map. -/
def nmiuToSubsingleton {A' B' : Type*} [CStarAlgebra A'] [PartialOrder A'] [StarOrderedRing A']
    [CStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B'] [Subsingleton B'] :
    NMIUMap A' B' where
  toStarAlgHom :=
    { toFun := fun _ => 0, map_one' := Subsingleton.elim _ _,
      map_mul' := fun _ _ => Subsingleton.elim _ _, map_zero' := rfl,
      map_add' := fun _ _ => Subsingleton.elim _ _,
      commutes' := fun _ => Subsingleton.elim _ _,
      map_star' := fun _ => Subsingleton.elim _ _ }
  preservesDirSups' := fun _ _ _ _ _ =>
    ⟨fun _ _ => le_of_eq (Subsingleton.elim _ _), fun _ _ => le_of_eq (Subsingleton.elim _ _)⟩

/-- A positive element of norm at most `r > 0` is `r` times an effect. -/
theorem inv_smul_mem_effects {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {x : B} (hx : 0 ≤ x) {r : ℝ} (hr : 0 < r) (hxr : ‖x‖ ≤ r) :
    ((r⁻¹ : ℝ) : ℂ) • x ∈ effects B := by
  refine ⟨Theses.A.CStar.ofReal_smul_nonneg hx (inv_nonneg.mpr hr.le), ?_⟩
  have hxle : x ≤ algebraMap ℂ B ((r : ℝ) : ℂ) := by
    refine ((IsSelfAdjoint.of_nonneg hx).le_algebraMap_norm_self).trans ?_
    rw [← Theses.A.CStar.algebraMap_real_eq]
    exact Theses.A.CStar.algebraMap_ofReal_mono hxr
  rw [← sub_nonneg]
  have hrw : (1 : B) - ((r⁻¹ : ℝ) : ℂ) • x
      = ((r⁻¹ : ℝ) : ℂ) • (algebraMap ℂ B ((r : ℝ) : ℂ) - x) := by
    rw [smul_sub, Algebra.algebraMap_eq_smul_one, smul_smul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
  rw [hrw]
  exact Theses.A.CStar.ofReal_smul_nonneg (sub_nonneg.mpr hxle) (inv_nonneg.mpr hr.le)

/-- The note's **Theorem 10**, `⇒`: if `φ` has a Wittrock dilation, then
`ϱ(𝒳)` splits off its commutant in `𝒫`.

The note's route is followed: with `σ(x ⊗ e) = ϱ(x) τ(e)`
(`exists_paschke_mediator`), `h_W(· ⊗ e) = φ_{τ(e)}`, so by Lemma 3
(`wittrock_correspondence`) and **157IV** the map `τ : ℰ → ϱ(𝒳)^□` is a
bijection of effects.  That `τ` maps projections to projections is shown
directly, not through extreme points: `τ(p) − τ(p)²` is `τ(g)` for an effect
`g` below both `p` and `p^⊥`.  **99II** (`gardner`) makes `τ`
multiplicative; it is then an nmiu-isomorphism, and `σ ∘ (id ⊗ τ⁻¹)` is the
nmiu-extension of `x ⊗ t ↦ ϱ(x)t` (Lemma 9). -/
theorem splitsOffCommutant_of_wittrock (φ : NCPMap X A) (ρ : NMIUMap X P) (hP : NCPMap P A)
    (hD : IsPaschkeDilationOf (⟨P, inferInstance, ρ, hP⟩ : PaschkeTriple X A) ⇑φ)
    {E : Type u} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E] [VonNeumannAlgebra E]
    (hW : NCPMap (VNT X E) A) (hWD : IsWittrockDilationOf ⇑φ E hW) :
    SplitsOffCommutant (rangeSub ρ) (nmiu_image ρ) := by
  classical
  rw [splitsOffCommutant_range_iff]
  by_cases hPn : Nontrivial P
  swap
  · rw [not_nontrivial_iff_subsingleton] at hPn
    exact ⟨nmiuToSubsingleton, fun _ _ => Subsingleton.elim _ _⟩
  have hρ1 : ρ 1 = 1 := map_one ρ.toStarAlgHom
  set D : PaschkeTriple X A := ⟨P, inferInstance, ρ, hP⟩ with hDdef
  obtain ⟨σ, τ, hσ1, hσh, hστ, hτ1⟩ := exists_paschke_mediator φ ρ hP hD hW hWD.1
  have hcomm : ∀ (t : RangeComm ρ) (x : X), ρ x * t.val = t.val * ρ x :=
    fun t x => mem_rangeComm.mp t.property x
  have hcommS : ∀ t : RangeComm ρ, t.val ∈ commutant D.P (Set.range ⇑D.ρ) := by
    rintro t _ ⟨x, rfl⟩
    exact hcomm t x
  -- `h_W(· ⊗ e) = φ_{τ(e)}`
  have hWτ : ∀ e x, hW (x ⊗ᵥ e) = hP ((τ e).val * ρ x) := by
    intro e x
    rw [← hσh, hστ, hcomm]
  have hτmono : ∀ {e e' : E}, e ≤ e' → τ e ≤ τ e' := fun h =>
    OrderHomClass.mono τ.toCompletelyPositiveMap h
  have hτ0 : ∀ {e : E}, 0 ≤ e → 0 ≤ τ e := fun h => ncpMap_nonneg τ h
  have hcorr := wittrock_correspondence (⇑φ) hW hWD
  -- (1) `e ↦ h_W(· ⊗ e)` is injective on effects (Lemma 3)
  have hinjW : ∀ e₁ e₂ : E, e₁ ∈ effects E → e₂ ∈ effects E →
      (∀ x, hW (x ⊗ᵥ e₁) = hW (x ⊗ᵥ e₂)) → e₁ = e₂ :=
    fun _ _ he₁ he₂ h12 => hcorr.injOn he₁ he₂ (funext h12)
  -- (2) every effect `t` of `ϱ(𝒳)^□` is `τ(e)` for an effect `e`: by Lemma 3,
  -- `φ_t ∈ [0,φ]_ncp` (**157IV**.1) is `h_W(· ⊗ e)` for an effect `e`
  have hsurj : ∀ t : RangeComm ρ, t ∈ effects (RangeComm ρ) →
      ∃ e : E, e ∈ effects E ∧ τ e = t := by
    intro t ht
    have ht0 : (0 : P) ≤ t.val := ht.1
    have ht1 : t.val ≤ 1 := ht.2
    obtain ⟨e, he, hWe⟩ :=
      hcorr.surjOn (paschke_correspondence_mem φ D hD t.val (hcommS t) ht0 ht1)
    have hWe : ∀ x, hW (x ⊗ᵥ e) = hP (t.val * ρ x) := fun x => congrFun hWe x
    refine ⟨e, he, Theses.A.Proc.VNSub.val_injective ?_⟩
    -- `φ_{τ(e)} = φ_t`, so `τ(e) = t` by **157IV**.2
    have hphi : phiT D (τ e).val = phiT D t.val := by
      funext x
      change hP ((τ e).val * ρ x) = hP (t.val * ρ x)
      rw [← hWτ, hWe]
    have hτe : (τ e) ∈ effects (RangeComm ρ) :=
      ⟨hτ0 he.1, by have := hτmono he.2; rwa [hτ1] at this⟩
    have hle := phiT_ncpLe D t.val t.val (fun a => (hcomm t a).symm)
      (fun a => (hcomm t a).symm) le_rfl
    refine le_antisymm ?_ ?_
    · refine (paschke_correspondence_embedding φ D hD t.val (τ e).val (hcommS t) ht0 ht1
        (hcommS _) hτe.1 hτe.2).mp ?_
      rwa [hphi]
    · refine (paschke_correspondence_embedding φ D hD (τ e).val t.val (hcommS _) hτe.1 hτe.2
        (hcommS t) ht0 ht1).mp ?_
      rwa [hphi]
  -- (3) `τ` is injective on positive elements
  have hinjP : ∀ e₁ e₂ : E, 0 ≤ e₁ → 0 ≤ e₂ → τ e₁ = τ e₂ → e₁ = e₂ := by
    intro e₁ e₂ h₁ h₂ h12
    set r : ℝ := ‖e₁‖ + ‖e₂‖ + 1
    have hr : 0 < r := by positivity
    have hs := inv_smul_mem_effects h₁ hr (by simp only [r]; linarith [norm_nonneg e₂])
    have ht := inv_smul_mem_effects h₂ hr (by simp only [r]; linarith [norm_nonneg e₁])
    have := hinjW _ _ hs ht fun x => by
      rw [hWτ, hWτ, wncp_smul, wncp_smul, h12]
    have h' := congrArg (fun y : E => ((r : ℝ) : ℂ) • y) this
    simp only [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one,
      one_smul] at h'
    exact h'
  -- (4) `τ` reflects the order on effects
  have hrefl : ∀ a b : E, a ∈ effects E → b ∈ effects E → τ a ≤ τ b → a ≤ b := by
    intro a b ha hb hab
    obtain ⟨c, hc, hτc⟩ := hsurj (τ b - τ a)
      ⟨sub_nonneg.mpr hab, (sub_le_self _ (hτ0 ha.1)).trans
        (by have := hτmono hb.2; rwa [hτ1] at this)⟩
    have := hinjP (a + c) b (add_nonneg ha.1 hc.1) hb.1 (by
      rw [wncp_add, hτc, add_sub_cancel])
    rw [← this]
    exact le_add_of_nonneg_right hc.1
  -- (5) `τ` maps projections to projections, hence is multiplicative (**99II**)
  have hproj : ∀ p : E, IsStarProjection p → IsStarProjection (τ p) := by
    intro p hp
    set u := τ p
    have hu0 : 0 ≤ u := hτ0 hp.nonneg
    have hu1 : u ≤ 1 := by have := hτmono hp.le_one; rwa [hτ1] at this
    have hd0 : 0 ≤ u - u * u := sub_nonneg.mpr (mul_self_le_self ⟨hu0, hu1⟩)
    have hsq : 0 ≤ u * u := by
      have := star_mul_self_nonneg u
      rwa [(IsSelfAdjoint.of_nonneg hu0).star_eq] at this
    have hd1 : u - u * u ≤ u := sub_le_self _ hsq
    have hd2 : u - u * u ≤ 1 - u := by
      have hns : (0 : RangeComm ρ) ≤ (1 - u) * (1 - u) := by
        have := star_mul_self_nonneg (1 - u)
        rwa [star_sub, star_one, (IsSelfAdjoint.of_nonneg hu0).star_eq] at this
      have hexp : (1 - u) * (1 - u) = (1 - u) - (u - u * u) := by noncomm_ring
      rw [hexp, sub_nonneg] at hns
      exact hns
    obtain ⟨g, hg, hτg⟩ := hsurj (u - u * u) ⟨hd0, hd1.trans hu1⟩
    have hgp : g ≤ p := hrefl g p hg ⟨hp.nonneg, hp.le_one⟩ (by rw [hτg]; exact hd1)
    have hgq : g ≤ 1 - p := hrefl g (1 - p) hg ⟨sub_nonneg.mpr hp.le_one, sub_le_self _ hp.nonneg⟩
      (by rw [hτg, wncp_sub', hτ1]; exact hd2)
    have hg0 : g = 0 := eq_zero_of_le_proj_le_perp' hg.1 hp hgp hgq
    rw [hg0, wncp_zero] at hτg
    exact ⟨(sub_eq_zero.mp hτg.symm).symm, IsSelfAdjoint.of_nonneg hu0⟩
  have hτmul : ∀ a b : E, τ (a * b) = τ a * τ b :=
    ((gardner τ hτ1).out 3 0).mp hproj
  set τN := nmiuOfNCP τ hτ1 hτmul
  -- (6) `τ` is bijective
  have hbij : Function.Bijective τN := by
    constructor
    · intro x y hxy
      have hz : τ (x - y) = 0 := by
        rw [wncp_sub']; exact sub_eq_zero.mpr hxy
      have hss : τ (star (x - y) * (x - y)) = τ 0 := by
        rw [hτmul, wncp_zero, hz, mul_zero]
      have := hinjP _ _ (star_mul_self_nonneg _) le_rfl hss
      exact sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp this)
    · intro t
      refine wit_nonneg_induction (fun t : RangeComm ρ => ∃ e, τN e = t) ?_ ?_ ?_ t
      · intro t ht
        rcases eq_or_lt_of_le (norm_nonneg t) with h0 | h0
        · refine ⟨0, ?_⟩
          rw [norm_eq_zero.mp h0.symm]
          exact map_zero τN.toStarAlgHom
        · obtain ⟨e, -, he⟩ := hsurj _ (inv_smul_mem_effects ht h0 le_rfl)
          refine ⟨((‖t‖ : ℝ) : ℂ) • e, ?_⟩
          change τ _ = t
          rw [wncp_smul, he, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ h0.ne',
            Complex.ofReal_one, one_smul]
      · rintro _ _ ⟨e, rfl⟩ ⟨e', rfl⟩
        exact ⟨e + e', map_add τN.toStarAlgHom e e'⟩
      · rintro c _ ⟨e, rfl⟩
        exact ⟨c • e, map_smul τN.toStarAlgHom c e⟩
  -- (7) `σ ∘ (id ⊗ τ⁻¹)` extends `x ⊗ t ↦ ϱ(x)t`
  set τinv := nmiuSymm τN hbij
  set m := ncpComp σ (tmap (ncpId X) (nmiuNCP τinv))
  have hm : ∀ x t, m (x ⊗ᵥ t) = ρ x * t.val := by
    intro x t
    rw [ncpComp_apply, tmap_apply, ncpId_apply, nmiuNCP_apply, hστ]
    exact congrArg (fun s : RangeComm ρ => ρ x * s.val) (nmiuSymm_apply_apply' τN hbij t)
  have hm1 : m 1 = 1 := by
    rw [← (vnTensor X (RangeComm ρ)).isTensorProduct.miu.1]
    change m ((1 : X) ⊗ᵥ (1 : RangeComm ρ)) = 1
    rw [hm, hρ1]
    exact one_mul _
  have hmmul : ∀ (x x' : X) (t t' : RangeComm ρ),
      m ((x * x') ⊗ᵥ (t * t')) = m (x ⊗ᵥ t) * m (x' ⊗ᵥ t') := by
    intro x x' t t'
    rw [hm, hm, hm, show ρ (x * x') = ρ x * ρ x' from map_mul ρ.toStarAlgHom x x']
    change ρ x * ρ x' * (t.val * t'.val) = ρ x * t.val * (ρ x' * t'.val)
    rw [mul_assoc, ← mul_assoc (ρ x'), hcomm, mul_assoc, mul_assoc]
  exact ⟨nmiuOfTensor m hm1 hmmul, hm⟩

/-- The note's **Theorem 10**, `⇐` with its last sentence: if `ϱ(𝒳)` splits
off its commutant in `𝒫`, then `x ⊗ t ↦ ϱ(x)t` extends to an nmiu-map
`Ψ : 𝒳 ⊗ ϱ(𝒳)^□ → 𝒫` (Lemma 9) and `h ∘ Ψ` is a Wittrock dilation of `φ`
(`isWittrockDilationOf_paschke_of_mul`, the note's first paragraph). -/
theorem isWittrockDilationOf_of_splitsOffCommutant (φ : NCPMap X A) (ρ : NMIUMap X P)
    (hP : NCPMap P A)
    (hD : IsPaschkeDilationOf (⟨P, inferInstance, ρ, hP⟩ : PaschkeTriple X A) ⇑φ)
    (hs : SplitsOffCommutant (rangeSub ρ) (nmiu_image ρ)) :
    ∃ Ψ : NMIUMap (VNT X (RangeComm ρ)) P, (∀ x t, Ψ (x ⊗ᵥ t) = ρ x * t.val) ∧
      IsWittrockDilationOf ⇑φ (RangeComm ρ) (ncpComp hP (nmiuNCP Ψ)) := by
  obtain ⟨Ψ, hΨ⟩ := (splitsOffCommutant_range_iff ρ).mp hs
  exact ⟨Ψ, hΨ, isWittrockDilationOf_paschke_of_mul φ ρ hP hD Ψ hΨ⟩

/-- The note's **Theorem 10**: for a Paschke dilation `(𝒫, ϱ, h)` of `φ`,
`φ` has a Wittrock dilation iff `ϱ(𝒳)` splits off its commutant in `𝒫`.
(The Wittrock dilation is sought in the universe of `𝒳`, which is also
that of `𝒫` and `𝒜`; see the file header of `Wittrock.lean`.) -/
theorem wittrock_iff_splitsOffCommutant (φ : NCPMap X A) (ρ : NMIUMap X P) (hP : NCPMap P A)
    (hD : IsPaschkeDilationOf (⟨P, inferInstance, ρ, hP⟩ : PaschkeTriple X A) ⇑φ) :
    (∃ (E : Type u) (_ : CStarAlgebra E) (_ : PartialOrder E) (_ : StarOrderedRing E)
      (_ : VonNeumannAlgebra E) (h : NCPMap (VNT X E) A), IsWittrockDilationOf ⇑φ E h) ↔
      SplitsOffCommutant (rangeSub ρ) (nmiu_image ρ) := by
  constructor
  · rintro ⟨E, _, _, _, _, h, hW⟩
    exact splitsOffCommutant_of_wittrock φ ρ hP hD h hW
  · intro hs
    obtain ⟨Ψ, -, hW⟩ := isWittrockDilationOf_of_splitsOffCommutant φ ρ hP hD hs
    exact ⟨_, inferInstance, inferInstance, inferInstance, inferInstance, _, hW⟩

end Main

/-! ## Lemma 6: type I factors -/

section TypeI

variable {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  [VonNeumannAlgebra P]

/-- The note's **Lemma 6**: if the von Neumann subalgebra `ℛ` of `𝒫` is a
type I factor — here: `ℛ ≅ 𝓑(ℋ)` for a Hilbert space `ℋ` — then
`a ⊗ t ↦ at` extends to an nmiu-isomorphism `ℛ ⊗ ℛ^□ ≅ 𝒫`.

This is `exists_bh_split` (whose proof is the note's, with the matrix-unit
step replaced by the amplification theorem) for `ϱ : 𝓑(ℋ) ≅ ℛ ⊆ 𝒫`,
transported along `𝓑(ℋ) ≅ ℛ` and the identification `ϱ(𝓑(ℋ))^□ = ℛ^□`. -/
theorem exists_typeI_factor_iso (R : StarSubalgebra ℂ P) (hR : IsVNSubalgebra P R)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : (H →L[ℂ] H) ≃⋆ₐ[ℂ] SubVN R hR) :
    ∃ Ψ : NMIUMap (VNT (SubVN R hR) (CommVN R)) P,
      Function.Bijective Ψ ∧ ∀ a t, Ψ (a ⊗ᵥ t) = a.val * t.val := by
  set ρ : NMIUMap (H →L[ℂ] H) P :=
    nmiuComp Theses.A.Proc.VNSub.valNMIU (nmiuOfBijective e.toStarAlgHom e.bijective)
  have hρ : ∀ x, ρ x = (e x).val := fun x => rfl
  have hrng : ∀ y, y ∈ rangeSub ρ ↔ y ∈ R := by
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, ?_⟩
      change ρ (e.symm ⟨y, hy⟩) = y
      rw [hρ, StarAlgEquiv.apply_symm_apply]
  have hcomm : ∀ y, y ∈ relComm (rangeSub ρ) ↔ y ∈ relComm R := by
    intro y
    simp only [mem_relComm, hrng]
  obtain ⟨Ψ₀, hΨ₀b, hΨ₀⟩ := exists_bh_split ρ
  set ι : NMIUMap (CommVN R) (RangeComm ρ) :=
    nmiuCorestrict Theses.A.Proc.VNSub.valNMIU (rangeComm ρ) (isVNSubalgebra_rangeComm ρ)
      (fun t => (hcomm _).mpr t.property)
  have hι : Function.Bijective ι :=
    nmiuCorestrict_bijective _ _ _ _ Theses.A.Proc.VNSub.valNMIU_injective
      (fun s hs => ⟨⟨s, (hcomm s).mp hs⟩, rfl⟩)
  set eInv := nmiuOfBijective e.symm.toStarAlgHom e.symm.bijective
  refine ⟨nmiuComp Ψ₀ (tmapM eInv ι),
    hΨ₀b.comp (tmapM_bijective' _ e.symm.bijective _ hι), fun a t => ?_⟩
  rw [nmiuComp_apply, tmapM_apply, hΨ₀, hρ]
  change (e (e.symm a)).val * t.val = a.val * t.val
  rw [StarAlgEquiv.apply_symm_apply]

/-- Lemma 6, last clause: a type I factor subalgebra splits off its
commutant. -/
theorem splitsOffCommutant_of_typeI_factor (R : StarSubalgebra ℂ P) (hR : IsVNSubalgebra P R)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : (H →L[ℂ] H) ≃⋆ₐ[ℂ] SubVN R hR) : SplitsOffCommutant R hR := by
  obtain ⟨Ψ, -, hΨ⟩ := exists_typeI_factor_iso R hR e
  exact ⟨Ψ, hΨ⟩

end TypeI

/-! ## Proposition 7, `⇒`: the centre -/

section Centre

variable {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  [VonNeumannAlgebra P]

/-- The centre `𝒵(ℛ) = ℛ ∩ ℛ^□` of a subalgebra `ℛ` of `𝒫`. -/
abbrev centreSub (R : StarSubalgebra ℂ P) : StarSubalgebra ℂ P := R ⊓ relComm R

theorem isVNSubalgebra_centreSub {R : StarSubalgebra ℂ P} (hR : IsVNSubalgebra P R) :
    IsVNSubalgebra P (centreSub R) :=
  isVNSubalgebra_inf hR (isVNSubalgebra_relComm R)

/-- The centre of `ℛ`, as a von Neumann algebra. -/
abbrev CentreVN (R : StarSubalgebra ℂ P) (hR : IsVNSubalgebra P R) : Type u :=
  SubVN (centreSub R) (isVNSubalgebra_centreSub hR)

/-- The note's **Proposition 7**, `⇒`, first half, up to **128XI**: if `ℛ`
splits off its commutant, the centre `𝒵` of `ℛ` is duplicable.  The
extension `μ` of `a ⊗ t ↦ at`, restricted along `𝒵 ⊗ 𝒵 → ℛ ⊗ ℛ^□`, sends
`a ⊗ b` to `ab ∈ 𝒵`; it lands in `𝒵` everywhere because `ℛ` and `ℛ^□`
are ultraweakly closed (**75VIII**) and the elementary tensors are
ultraweakly dense (**108II**). -/
theorem duplicable_centre_of_splitsOffCommutant {R : StarSubalgebra ℂ P}
    {hR : IsVNSubalgebra P R} (hs : SplitsOffCommutant R hR) :
    Duplicable (CentreVN R hR) := by
  obtain ⟨Ψ, hΨ⟩ := hs
  set ιR : NMIUMap (CentreVN R hR) (SubVN R hR) :=
    nmiuCorestrict Theses.A.Proc.VNSub.valNMIU R hR (fun z => z.property.1)
  set ιC : NMIUMap (CentreVN R hR) (CommVN R) :=
    nmiuCorestrict Theses.A.Proc.VNSub.valNMIU (relComm R) (isVNSubalgebra_relComm R)
      (fun z => z.property.2)
  set F := nmiuComp Ψ (tmapM ιR ιC)
  have hF : ∀ a b : CentreVN R hR, F (a ⊗ᵥ b) = a.val * b.val := by
    intro a b
    rw [nmiuComp_apply, tmapM_apply, hΨ]
    rfl
  have hin : ∀ (S : StarSubalgebra ℂ P), IsVNSubalgebra P S →
      (∀ a b : CentreVN R hR, a.val * b.val ∈ S) → ∀ w, F w ∈ S := by
    intro S hS hab w
    exact tensor_mem_of_forall (nmiuNCP F).toCompletelyPositiveMap.toLinearMap
      (nmiu_uwContinuous F) (Subalgebra.toSubmodule S.toSubalgebra)
      (isClosed_ultraweak_vnsub S hS) (fun a b => by
        change F (a ⊗ᵥ b) ∈ S
        rw [hF]; exact hab a b) w
  have hmem : ∀ w, F w ∈ centreSub R := fun w =>
    ⟨hin R hR (fun a b => mul_mem a.property.1 b.property.1) w,
      hin (relComm R) (isVNSubalgebra_relComm R)
        (fun a b => mul_mem a.property.2 b.property.2) w⟩
  set δ := nmiuCorestrict F (centreSub R) (isVNSubalgebra_centreSub hR) hmem
  have hδ : ∀ a b : CentreVN R hR, δ (a ⊗ᵥ b) = a * b := fun a b =>
    Theses.A.Proc.VNSub.val_injective (by rw [nmiuCorestrict_val, hF]; rfl)
  exact (duplicability_multiplication (A := CentreVN R hR)).1.mpr
    ⟨PositiveLinearMap.ofClass (nmiuNCP δ).toCompletelyPositiveMap,
      (nmiuNCP δ).preservesDirSups', hδ⟩

/-- The note's **Proposition 7**, `⇒`, first half: if `ℛ` splits off its
commutant in `𝒫`, its centre is nmiu-isomorphic to `ℓ^∞(I)` for some set
`I` (**128XI** and **127III**). -/
theorem centre_linf_of_splitsOffCommutant {R : StarSubalgebra ℂ P}
    {hR : IsVNSubalgebra P R} (hs : SplitsOffCommutant R hR) :
    ∃ (I : Type u) (f : NMIUMap (CentreVN R hR) (linf I)), Function.Bijective f :=
  duplicable.mp (duplicable_centre_of_splitsOffCommutant hs)

end Centre

/-! ## Corollary 13 -/

section Cor13

variable {X : Type u} [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [VonNeumannAlgebra X]
  {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P] [VonNeumannAlgebra P]
  {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]

/-- The note's **Corollary 13**, first claim: if `φ` has a Wittrock
dilation, then for any Paschke dilation `(𝒫, ϱ, h)` of `φ` the centre of
`ϱ(𝒳)` is nmiu-isomorphic to `ℓ^∞(I)` for some set `I` (Theorem 10 and
Proposition 7). -/
theorem centre_linf_of_wittrock (φ : NCPMap X A) (ρ : NMIUMap X P) (hP : NCPMap P A)
    (hD : IsPaschkeDilationOf (⟨P, inferInstance, ρ, hP⟩ : PaschkeTriple X A) ⇑φ)
    (hW : ∃ (E : Type u) (_ : CStarAlgebra E) (_ : PartialOrder E) (_ : StarOrderedRing E)
      (_ : VonNeumannAlgebra E) (h : NCPMap (VNT X E) A), IsWittrockDilationOf ⇑φ E h) :
    ∃ (I : Type u) (f : NMIUMap (CentreVN (rangeSub ρ) (nmiu_image ρ)) (linf I)),
      Function.Bijective f :=
  centre_linf_of_splitsOffCommutant ((wittrock_iff_splitsOffCommutant φ ρ hP hD).mp hW)

end Cor13

/-! ### Minimal projections: `ℓ^∞(I)` has them, atomless `L^∞` has none

Also the minimal central projections of Proposition 7 (`IsMinCentralProj`),
which state the hypothesis of Corollary 13, "in particular". -/

section MinProj

/-- An idempotent complex number is `0` or `1`. -/
theorem complex_idem {z : ℂ} (hz : z * z = z) : z = 0 ∨ z = 1 := by
  have h : z * (z - 1) = 0 := by rw [mul_sub, mul_one, hz, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- A **minimal projection** `p ≠ 0`: every projection below it (`rp = r`) is
`0` or `p`. -/
def IsMinProj {B : Type*} [Ring B] [StarRing B] (p : B) : Prop :=
  IsStarProjection p ∧ p ≠ 0 ∧ ∀ r : B, IsStarProjection r → r * p = r → r = 0 ∨ r = p

section MinCentral

variable {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  [VonNeumannAlgebra P]

/-- A **minimal central projection** of `ℛ`: a non-zero projection of the
centre of `ℛ` with no non-zero central projection strictly below it — that
is, a minimal projection of the centre (`isMinCentralProj_of_isMinProj`).
For `ℛ = ⊤` these are the minimal central projections of `𝒫` itself. -/
def IsMinCentralProj (R : StarSubalgebra ℂ P) (c : P) : Prop :=
  c ∈ centreSub R ∧ IsStarProjection c ∧ c ≠ 0 ∧
    ∀ r ∈ centreSub R, IsStarProjection r → r * c = r → r = 0 ∨ r = c

/-- A minimal projection of the centre, as an element of `𝒫`. -/
theorem isMinCentralProj_of_isMinProj {R : StarSubalgebra ℂ P} {hR : IsVNSubalgebra P R}
    {p : CentreVN R hR} (hp : IsMinProj p) : IsMinCentralProj R p.val := by
  obtain ⟨⟨hpi, hps⟩, hp0, hpmin⟩ := hp
  refine ⟨p.property, ⟨congrArg Theses.A.Proc.VNSub.val hpi.eq,
    congrArg Theses.A.Proc.VNSub.val hps⟩, fun h => hp0 (Theses.A.Proc.VNSub.val_injective h),
    fun r hr hri hrp => ?_⟩
  rcases hpmin ⟨r, hr⟩ ⟨Theses.A.Proc.VNSub.val_injective hri.isIdempotentElem.eq,
      Theses.A.Proc.VNSub.val_injective hri.isSelfAdjoint.star_eq⟩
      (Theses.A.Proc.VNSub.val_injective hrp) with h | h
  · exact Or.inl (congrArg Theses.A.Proc.VNSub.val h)
  · exact Or.inr (congrArg Theses.A.Proc.VNSub.val h)

end MinCentral

/-- `ℓ^∞(I)` has a minimal projection as soon as `I` is nonempty: `δ_i`. -/
theorem linf_isMinProj {I : Type u} (i : I) : IsMinProj (lpKappa i (1 : ℂ) : linf I) := by
  classical
  have hev : ∀ j, ((lpKappa i (1 : ℂ) : linf I) : ∀ _ : I, ℂ) j = if j = i then 1 else 0 := by
    intro j
    by_cases h : j = i
    · subst h; simp only [ite_true]; exact lpKappa_apply_self _ _
    · simp only [h, ite_false]; exact lpKappa_apply_ne _ _ h
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · refine lp.ext (funext fun j => ?_)
    rw [lp.infty_coeFn_mul, Pi.mul_apply, hev]
    split_ifs <;> simp
  · refine lp.ext (funext fun j => ?_)
    rw [lp.coeFn_star, Pi.star_apply, hev]
    split_ifs <;> simp
  · intro h
    have := congrArg (fun v : linf I => (v : ∀ _ : I, ℂ) i) h
    simp only [hev, ite_true] at this
    exact one_ne_zero (this.trans (by rfl))
  · intro r hr hri
    have hcoord : ∀ j, (r : ∀ _ : I, ℂ) j * (r : ∀ _ : I, ℂ) j = (r : ∀ _ : I, ℂ) j := by
      intro j
      have := congrArg (fun v : linf I => (v : ∀ _ : I, ℂ) j) hr.isIdempotentElem.eq
      simpa only [lp.infty_coeFn_mul, Pi.mul_apply] using this
    have hoff : ∀ j, j ≠ i → (r : ∀ _ : I, ℂ) j = 0 := by
      intro j hj
      have := congrArg (fun v : linf I => (v : ∀ _ : I, ℂ) j) hri
      simp only [lp.infty_coeFn_mul, Pi.mul_apply, hev, hj, ite_false, mul_zero] at this
      exact this.symm
    rcases complex_idem (hcoord i) with h0 | h1
    · left
      refine lp.ext (funext fun j => ?_)
      by_cases hj : j = i
      · subst hj; exact h0
      · exact hoff j hj
    · right
      refine lp.ext (funext fun j => ?_)
      rw [hev]
      by_cases hj : j = i
      · subst hj; simp only [ite_true]; exact h1
      · simp only [hj, ite_false]; exact hoff j hj

/-- Under an nmiu-isomorphism `𝒵 ≅ ℓ^∞(I)` the preimage of `δᵢ` is a
minimal projection. -/
theorem isMinProj_symm_linf {Z : Type u} [CStarAlgebra Z] [PartialOrder Z]
    [StarOrderedRing Z] [VonNeumannAlgebra Z] {I : Type u}
    (f : NMIUMap Z (linf I)) (hf : Function.Bijective f) (i : I) :
    IsMinProj (nmiuSymm f hf (lpKappa i (1 : ℂ))) := by
  set g := nmiuSymm f hf
  have hfg : ∀ v, f (g v) = v := nmiuSymm_apply_apply' f hf
  have hgf : ∀ z, g (f z) = z := nmiuSymm_apply_apply f hf
  obtain ⟨⟨hp1, hp2⟩, hp0, hpmin⟩ := linf_isMinProj (I := I) i
  set δ : linf I := lpKappa i (1 : ℂ)
  have hfm : ∀ a b : Z, f (a * b) = f a * f b := fun a b => map_mul f.toStarAlgHom a b
  have hfs : ∀ a : Z, f (star a) = star (f a) := fun a => map_star f.toStarAlgHom a
  have hproj : ∀ {z : Z}, IsStarProjection z ↔ IsStarProjection (f z) := by
    intro z
    constructor
    · intro hz
      exact ⟨by rw [IsIdempotentElem, ← hfm]; exact congrArg f hz.isIdempotentElem.eq,
        by rw [IsSelfAdjoint, ← hfs]; exact congrArg f hz.isSelfAdjoint.star_eq⟩
    · intro hz
      exact ⟨hf.1 (by rw [hfm]; exact hz.isIdempotentElem.eq),
        hf.1 (by rw [hfs]; exact hz.isSelfAdjoint.star_eq)⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hproj.mpr (by rw [hfg]; exact ⟨hp1, hp2⟩)
  · intro h
    apply hp0
    rw [← hfg δ, h]
    exact map_zero f.toStarAlgHom
  · intro r hr hrp
    have hfr : f r * δ = f r := by
      rw [← hfg δ, ← hfm]; exact congrArg f hrp
    rcases hpmin (f r) (hproj.mp hr) hfr with h | h
    · left
      exact hf.1 (h.trans (map_zero f.toStarAlgHom).symm)
    · right
      rw [← hgf r, h]

/-- A non-zero algebra nmiu-isomorphic to some `ℓ^∞(I)` has a minimal
projection. -/
theorem exists_isMinProj_of_linf {Z : Type u} [CStarAlgebra Z] [PartialOrder Z]
    [StarOrderedRing Z] [VonNeumannAlgebra Z] [Nontrivial Z] {I : Type u}
    (f : NMIUMap Z (linf I)) (hf : Function.Bijective f) : ∃ p : Z, IsMinProj p := by
  have hI : Nonempty I := by
    by_contra hI
    rw [not_nonempty_iff] at hI
    have h10 : f 1 = f 0 := Subsingleton.elim _ _
    exact one_ne_zero (hf.1 h10)
  obtain ⟨i⟩ := hI
  exact ⟨_, isMinProj_symm_linf f hf i⟩

variable {Ω : Type u} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)

omit [MeasurableSpace Ω] in
theorem bm_indicator' [MeasurableSpace Ω] {S : Set Ω} (hS : MeasurableSet S) :
    IsBoundedMeasurable Ω (S.indicator (1 : Ω → ℂ)) := by
  classical
  refine ⟨(measurable_const : Measurable (1 : Ω → ℂ)).indicator hS, 1, fun x => ?_⟩
  by_cases hx : x ∈ S <;> simp [hx]

theorem bm_sub' {f g : Ω → ℂ} (hf : IsBoundedMeasurable Ω f) (hg : IsBoundedMeasurable Ω g) :
    IsBoundedMeasurable Ω (f - g) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  exact ⟨hfm.sub hgm, C + D, fun x => (norm_sub_le _ _).trans (add_le_add (hC x) (hD x))⟩

theorem bm_mul' {f g : Ω → ℂ} (hf : IsBoundedMeasurable Ω f) (hg : IsBoundedMeasurable Ω g) :
    IsBoundedMeasurable Ω (f * g) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  refine ⟨hfm.mul hgm, C * D, fun x => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hC x) (hD x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))

/-- The example of Corollary 13, "in particular": `L^∞` of a measure space
without atoms has no minimal projection.  A projection is `q(1_S)`
for a measurable `S`, and minimality of `q(1_S)` makes `S` an atom. -/
theorem linfty_no_minProj (hc : ContinuousSpace μ) {X : Type*} [CStarAlgebra X]
    [PartialOrder X] [StarOrderedRing X] (q : (Ω → ℂ) → X) (hq : IsLinftyOf μ X q)
    (e₀ : X) (he₀ : IsMinProj e₀) : False := by
  classical
  obtain ⟨⟨hidem, hsa⟩, hne, hmin⟩ := he₀
  have hqsub : ∀ f g, IsBoundedMeasurable Ω f → IsBoundedMeasurable Ω g →
      q (f - g) = q f - q g := by
    intro f g hf hg
    have h := hq.add f ((-1 : ℂ) • g) hf ⟨(hg.1.const_smul _), by
      obtain ⟨C, hC⟩ := hg.2; exact ⟨C, fun x => by simpa using hC x⟩⟩
    rw [hq.smul (-1) g hg] at h
    simpa [sub_eq_add_neg] using h
  have hker : ∀ f g, IsBoundedMeasurable Ω f → IsBoundedMeasurable Ω g →
      (q f = q g ↔ f =ᵐ[μ] g) := by
    intro f g hf hg
    rw [← sub_eq_zero, ← hqsub f g hf hg, hq.kernel _ (bm_sub' hf hg)]
    constructor
    · intro h; filter_upwards [h] with x hx; exact sub_eq_zero.mp hx
    · intro h; filter_upwards [h] with x hx; simp [hx]
  have hind_mul : ∀ S T : Set Ω, S.indicator (1 : Ω → ℂ) * T.indicator 1 = (S ∩ T).indicator 1 := by
    intro S T; funext x; by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;>
      simp [hS, hT]
  -- `e₀ = q(1_S)` with `S = {f = 1}`
  obtain ⟨f, hf, hfq⟩ := hq.surj e₀
  have hff : f * f =ᵐ[μ] f := by
    rw [← hker _ _ (bm_mul' hf hf) hf, hq.mul f f hf hf, hfq]; exact hidem
  set S := f ⁻¹' {1}
  have hSm : MeasurableSet S := hf.1 (measurableSet_singleton 1)
  have hSf : S.indicator (1 : Ω → ℂ) =ᵐ[μ] f := by
    filter_upwards [hff] with x hx
    have hx' : f x * f x = f x := hx
    by_cases h1 : f x = 1
    · simp [S, h1]
    · have h0 : f x = 0 := by
        rcases complex_idem hx' with h | h
        · exact h
        · exact absurd h h1
      simp [S, h0]
  have he₀S : q (S.indicator 1) = e₀ := by
    rw [← hfq]; exact (hker _ _ (bm_indicator' hSm) hf).mpr hSf
  have hnull : ∀ T : Set Ω, MeasurableSet T → q (T.indicator 1) = 0 → μ T = 0 := by
    intro T hT h0
    have h := (hq.kernel _ (bm_indicator' hT)).mp h0
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h
    refine MeasureTheory.measure_mono_null (fun x hx => ?_) h
    simp [Set.indicator_apply, hx]
  refine hc S ⟨hSm, ?_, fun S' hS'S hS'm hS'pos => ?_⟩
  · refine pos_iff_ne_zero.mpr fun h0 => hne ?_
    rw [← he₀S]
    exact (hq.kernel _ (bm_indicator' hSm)).mpr
      ((Set.indicator_ae_eq_zero).mpr
        (MeasureTheory.measure_mono_null Set.inter_subset_left h0))
  · set e := q (S'.indicator 1)
    have he : IsStarProjection e := by
      refine ⟨?_, ?_⟩
      · change q _ * q _ = q _
        rw [← hq.mul _ _ (bm_indicator' hS'm) (bm_indicator' hS'm), hind_mul, Set.inter_self]
      · change star (q _) = q _
        rw [← hq.star_map _ (bm_indicator' hS'm)]
        congr 1; funext x; by_cases hx : x ∈ S' <;> simp [hx]
    have hee : e * e₀ = e := by
      change q _ * e₀ = q _
      rw [← he₀S, ← hq.mul _ _ (bm_indicator' hS'm) (bm_indicator' hSm), hind_mul,
        Set.inter_eq_left.mpr hS'S]
    rcases hmin e he hee with h | h
    · exact absurd (hnull S' hS'm h) (pos_iff_ne_zero.mp hS'pos)
    · have hae : S'.indicator (1 : Ω → ℂ) =ᵐ[μ] S.indicator 1 :=
        (hker _ _ (bm_indicator' hS'm) (bm_indicator' hSm)).mp (h.trans he₀S.symm)
      have hdiff : μ (S \ S') = 0 := by
        rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at hae
        refine MeasureTheory.measure_mono_null (fun x hx => ?_) hae
        simp [Set.indicator_apply, hx.1, hx.2]
      refine le_antisymm (MeasureTheory.measure_mono hS'S) ?_
      calc μ S ≤ μ (S' ∪ S \ S') := MeasureTheory.measure_mono (fun x hx => by
              by_cases h' : x ∈ S'
              · exact Or.inl h'
              · exact Or.inr ⟨hx, h'⟩)
        _ ≤ μ S' + μ (S \ S') := MeasureTheory.measure_union_le _ _
        _ = μ S' := by rw [hdiff, add_zero]

end MinProj

section Cor13Centre

variable {X : Type u} [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [VonNeumannAlgebra X]
  {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P] [VonNeumannAlgebra P]
  {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]

/-- The note's **Corollary 13**, "in particular", for a given Paschke
dilation: if the centre of `𝒳` has no minimal projections — that is, `𝒳`
has no minimal central projection (`IsMinCentralProj ⊤`) — then no
non-zero ncp-map `φ : 𝒳 → 𝒜` has a Wittrock dilation.

The note's argument: `ϱ(𝒳) ≅ c𝒳` for a central projection `c` of `𝒳`
(**69IVa**, `nmiu_factors_maps`), and the centre of `ϱ(𝒳)`, being
`≅ ℓ^∞(I)` with `I ≠ ∅` (the first claim), has a minimal projection
`p = ϱ(y₀)`, `y₀ ∈ c𝒳`.  Then `y₀` is a central projection of `𝒳`, and it is
minimal among them: a central projection below `y₀` lies in `c𝒳`, and its
image under `ϱ` is a central projection of `ϱ(𝒳)` below `p`. -/
theorem not_wittrock_of_centre_no_minProj_paschke (φ : NCPMap X A) (ρ : NMIUMap X P)
    (hP : NCPMap P A)
    (hD : IsPaschkeDilationOf (⟨P, inferInstance, ρ, hP⟩ : PaschkeTriple X A) ⇑φ)
    (hZ : ∀ c : X, ¬ IsMinCentralProj (⊤ : StarSubalgebra ℂ X) c) (hφ : ∃ x, φ x ≠ 0) :
    ¬ ∃ (E : Type u) (_ : CStarAlgebra E) (_ : PartialOrder E) (_ : StarOrderedRing E)
      (_ : VonNeumannAlgebra E) (h : NCPMap (VNT X E) A), IsWittrockDilationOf ⇑φ E h := by
  intro hW
  obtain ⟨I, f, hf⟩ := centre_linf_of_wittrock φ ρ hP hD hW
  have hPn : Nontrivial P := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    obtain ⟨x, hx⟩ := hφ
    apply hx
    rw [← hD.1 x, show ρ x = 0 from Subsingleton.elim _ _]
    exact wncp_zero hP
  have hZn : Nontrivial (CentreVN (rangeSub ρ) (nmiu_image ρ)) :=
    ⟨⟨1, 0, fun h => one_ne_zero (congrArg Theses.A.Proc.VNSub.val h)⟩⟩
  obtain ⟨p, ⟨hpi, hps⟩, hp0, hpmin⟩ := exists_isMinProj_of_linf f hf
  -- `ϱ = H ∘ G` with `G : 𝒳 → c𝒳` the compression and `H : c𝒳 → 𝒫` injective
  obtain ⟨c, G, H, -, -, hH, -, hHi, hfa⟩ :=
    nmiu_factors_maps ρ (nmiuP ρ) ρ.preservesDirSups' (fun _ => rfl)
  have hHm : ∀ a b, H (a * b) = H a * H b := fun a b => map_mul H.toStarAlgHom a b
  have hHs : ∀ a, H (star a) = star (H a) := fun a => map_star H.toStarAlgHom a
  have hH0 : H 0 = 0 := map_zero H.toStarAlgHom
  have hρm : ∀ a b, ρ (a * b) = ρ a * ρ b := fun a b => map_mul ρ.toStarAlgHom a b
  obtain ⟨x₀, hx₀⟩ := p.property.1
  set y₀ := G x₀
  have hy₀ : H y₀ = p.val := by rw [← hfa]; exact hx₀
  have hy₀i : y₀ * y₀ = y₀ := hHi (by
    rw [hHm, hy₀]; exact congrArg Theses.A.Proc.VNSub.val hpi.eq)
  have hy₀s : star y₀ = y₀ := hHi (by
    rw [hHs, hy₀]; exact congrArg Theses.A.Proc.VNSub.val hps)
  -- `y₀` is central in `𝒳`: `y₀ b` and `b y₀` lie in `c𝒳`, with images
  -- `p ϱ(b) = ϱ(b) p` under the injective `H`
  have hy₀c : ∀ b : X, b * (y₀ : X) = y₀ * b := by
    intro b
    have hcy : c.val * (y₀ : X) = y₀ := y₀.property
    have h₁ : c.val * (b * y₀) = b * y₀ := by rw [← mul_assoc, c.isCentral b, mul_assoc, hcy]
    have h₂ : c.val * (y₀ * b) = y₀ * b := by rw [← mul_assoc, hcy]
    have hpb : ρ b * p.val = p.val * ρ b := mem_relComm.mp p.property.2 _ ⟨b, rfl⟩
    have := hHi (a₁ := ⟨b * y₀, h₁⟩) (a₂ := ⟨y₀ * b, h₂⟩) (by
      rw [hH, hH]
      change ρ (b * y₀) = ρ (y₀ * b)
      rw [hρm, hρm, ← hH, hy₀, hpb])
    exact congrArg Subtype.val this
  refine hZ y₀ ⟨⟨trivial, mem_relComm.mpr fun b _ => hy₀c b⟩,
    ⟨congrArg Subtype.val hy₀i, congrArg Subtype.val hy₀s⟩, fun h => hp0 ?_,
    fun e he hep hee => ?_⟩
  · refine Theses.A.Proc.VNSub.val_injective ?_
    rw [← hy₀, show y₀ = 0 from Subtype.ext h, hH0]
    rfl
  · -- a central projection `e ≤ y₀` of `𝒳` lies in `c𝒳`
    have hec : ∀ b : X, b * e = e * b := fun b => mem_relComm.mp he.2 b trivial
    have hce : c.val * e = e := by
      calc c.val * e = c.val * (e * y₀) := by rw [hee]
        _ = e * (c.val * y₀) := by rw [← mul_assoc, c.isCentral e, mul_assoc]
        _ = e := by rw [show c.val * (y₀ : X) = y₀ from y₀.property, hee]
    set y : c.sub := ⟨e, hce⟩
    have hyi : y * y = y := Subtype.ext hep.isIdempotentElem.eq
    have hys : star y = y := Subtype.ext hep.isSelfAdjoint.star_eq
    have hyy : y * y₀ = y := Subtype.ext hee
    -- and `ϱ(e) = H(y)` is a central projection of `ϱ(𝒳)` below `p`
    have hmem : H y ∈ centreSub (rangeSub ρ) := by
      refine ⟨⟨e, (hH y).symm⟩, mem_relComm.mpr ?_⟩
      rintro _ ⟨x, rfl⟩
      change ρ x * H y = H y * ρ x
      rw [hH, ← hρm, ← hρm, hec]
    set r : CentreVN (rangeSub ρ) (nmiu_image ρ) := ⟨H y, hmem⟩
    have hr : IsStarProjection r :=
      ⟨Theses.A.Proc.VNSub.val_injective (by
          change H y * H y = H y; rw [← hHm, hyi]),
        Theses.A.Proc.VNSub.val_injective (by
          change star (H y) = H y; rw [← hHs, hys])⟩
    have hrp : r * p = r := Theses.A.Proc.VNSub.val_injective (by
      change H y * p.val = H y; rw [← hy₀, ← hHm, hyy])
    rcases hpmin r hr hrp with h | h
    · left
      have : H y = H 0 := by rw [hH0]; exact congrArg Theses.A.Proc.VNSub.val h
      exact congrArg Subtype.val (hHi this)
    · right
      have : H y = H y₀ := by rw [hy₀]; exact congrArg Theses.A.Proc.VNSub.val h
      exact congrArg Subtype.val (hHi this)

/-- The note's **Corollary 13**, "in particular": if the centre of `𝒳` has
no minimal projections (`𝒳` has no minimal central projection), then no
non-zero ncp-map `φ : 𝒳 → 𝒜` has a Wittrock dilation — for the Paschke
dilation of **154III**. -/
theorem not_wittrock_of_centre_no_minProj (φ : NCPMap X A)
    (hZ : ∀ c : X, ¬ IsMinCentralProj (⊤ : StarSubalgebra ℂ X) c) (hφ : ∃ x, φ x ≠ 0) :
    ¬ ∃ (E : Type u) (_ : CStarAlgebra E) (_ : PartialOrder E) (_ : StarOrderedRing E)
      (_ : VonNeumannAlgebra E) (h : NCPMap (VNT X E) A), IsWittrockDilationOf ⇑φ E h := by
  obtain ⟨M⟩ := existence_paschke φ
  let _ : VonNeumannAlgebra (Ba A M.X)ᵐᵒᵖ :=
    @vonNeumannAlgebra_mulOpposite (Ba A M.X) _ _ _ (ba_vonNeumannAlgebra M.selfDual)
  exact not_wittrock_of_centre_no_minProj_paschke φ M.ρ M.h (existence_paschke_5 φ M) hZ hφ

/-- The note's example for **Corollary 13**, "in particular", for a given
Paschke dilation: a non-zero ncp-map out of `L^∞` of a measure space without
atoms has no Wittrock dilation.  `L^∞(Ω)` is given, as in thesis A, by a
presentation `q : (Ω → ℂ) → 𝒳` (`IsLinftyOf`).  It is commutative, so its
centre is all of it, and it has no minimal projection
(`linfty_no_minProj`). -/
theorem not_wittrock_of_linfty_paschke (φ : NCPMap X A) (ρ : NMIUMap X P) (hP : NCPMap P A)
    (hD : IsPaschkeDilationOf (⟨P, inferInstance, ρ, hP⟩ : PaschkeTriple X A) ⇑φ)
    {Ω : Type u} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (hc : ContinuousSpace μ)
    (q : (Ω → ℂ) → X) (hq : IsLinftyOf μ X q) (hφ : ∃ x, φ x ≠ 0) :
    ¬ ∃ (E : Type u) (_ : CStarAlgebra E) (_ : PartialOrder E) (_ : StarOrderedRing E)
      (_ : VonNeumannAlgebra E) (h : NCPMap (VNT X E) A), IsWittrockDilationOf ⇑φ E h := by
  refine not_wittrock_of_centre_no_minProj_paschke φ ρ hP hD (fun e he => ?_) hφ
  obtain ⟨-, hep, he0, hemin⟩ := he
  -- `𝒳 = L^∞(Ω)` is commutative
  have hXc : ∀ a b : X, a * b = b * a := by
    intro a b
    obtain ⟨g₁, hg₁, rfl⟩ := hq.surj a
    obtain ⟨g₂, hg₂, rfl⟩ := hq.surj b
    rw [← hq.mul _ _ hg₁ hg₂, ← hq.mul _ _ hg₂ hg₁, mul_comm]
  exact linfty_no_minProj μ hc q hq e ⟨hep, he0, fun r hr hre =>
    hemin r ⟨trivial, mem_relComm.mpr fun a _ => hXc a r⟩ hr hre⟩

/-- The note's example for **Corollary 13**, "in particular": no non-zero
ncp-map `L^∞(Ω) → 𝒜` on a measure space without atoms has a Wittrock
dilation.  No σ-finiteness is needed once `L^∞(Ω)` is given as a von
Neumann algebra `𝒳` with a presentation `q`. -/
theorem not_wittrock_of_linfty (φ : NCPMap X A)
    {Ω : Type u} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (hc : ContinuousSpace μ)
    (q : (Ω → ℂ) → X) (hq : IsLinftyOf μ X q) (hφ : ∃ x, φ x ≠ 0) :
    ¬ ∃ (E : Type u) (_ : CStarAlgebra E) (_ : PartialOrder E) (_ : StarOrderedRing E)
      (_ : VonNeumannAlgebra E) (h : NCPMap (VNT X E) A), IsWittrockDilationOf ⇑φ E h := by
  obtain ⟨M⟩ := existence_paschke φ
  let _ : VonNeumannAlgebra (Ba A M.X)ᵐᵒᵖ :=
    @vonNeumannAlgebra_mulOpposite (Ba A M.X) _ _ _ (ba_vonNeumannAlgebra M.selfDual)
  exact not_wittrock_of_linfty_paschke φ M.ρ M.h (existence_paschke_5 φ M) μ hc q hq hφ

end Cor13Centre

/-! ## Ultraweak sums of ncp-maps

If the finite partial sums of a family of ncp-maps are bounded at `1`, the
family has an ultraweak sum, which is again ncp (**96III**).  This adds up
the blocks below, and the direct sums of `WittrockSum.lean`. -/

section UWSum

variable {T : Type u} [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T]
  [VonNeumannAlgebra T]
  {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]
  {ι : Type*}

/-- The finite partial sum `∑_{i∈F} gᵢ`, as a positive map. -/
def ncpPartSum (g : ι → NCPMap T A) (F : Finset ι) : T →ₚ[ℂ] A where
  toFun b := ∑ i ∈ F, g i b
  map_add' b b' := by simp only [wncp_add, Finset.sum_add_distrib]
  map_smul' c b := by simp only [wncp_smul, Finset.smul_sum, RingHom.id_apply]
  monotone' b b' hb := Finset.sum_le_sum fun i _ =>
    OrderHomClass.mono (g i).toCompletelyPositiveMap hb

omit [VonNeumannAlgebra T] [VonNeumannAlgebra A] in
theorem ncpPartSum_apply (g : ι → NCPMap T A) (F : Finset ι) (b : T) :
    ncpPartSum g F b = ∑ i ∈ F, g i b := rfl

omit [VonNeumannAlgebra T] [VonNeumannAlgebra A] in
theorem ncpPartSum_cp (g : ι → NCPMap T A) (F : Finset ι) :
    Theses.A.CStar.IsCompletelyPositiveMap (ncpPartSum g F).toLinearMap := by
  intro n a c
  have he : ∑ p, ∑ q, star (c p) * (ncpPartSum g F).toLinearMap (star (a p) * a q) * c q
      = ∑ i ∈ F, ∑ p, ∑ q, star (c p) *
          (g i).toCompletelyPositiveMap.toLinearMap (star (a p) * a q) * c q := by
    have h1 : ∀ x, (ncpPartSum g F).toLinearMap x = ∑ i ∈ F,
        (g i).toCompletelyPositiveMap.toLinearMap x := fun x => rfl
    simp only [h1, Finset.mul_sum, Finset.sum_mul]
    exact (Finset.sum_congr rfl fun p _ => Finset.sum_comm).trans Finset.sum_comm
  rw [he]
  exact Finset.sum_nonneg fun i _ => wit_ncp_cp (g i) n a c

theorem ncpPartSum_normal (g : ι → NCPMap T A) (F : Finset ι) :
    PreservesDirSups ⇑(ncpPartSum g F) := by
  refine ((p_uwcont (ncpPartSum g F)).out 0 2).mp ?_
  let _ : TopologicalSpace T := ultraweak _
  refine continuous_ultraweak_of_forall _ fun ω => ?_
  have h : (fun b => (ω (ncpPartSum g F b) : ℂ))
      = fun b => ∑ i ∈ F, (ω (g i b) : ℂ) := by
    funext b
    exact map_sum ω.toPositiveLinearMap _ F
  rw [h]
  refine continuous_finsetSum F fun i _ => ?_
  exact @Continuous.comp _ _ _ (ultraweak _) (ultraweak A) _ _ _
    (continuous_ultraweak_npFunctional ω) (wit_ncp_continuous (g i))

/-- The ultraweak sum of a family of ncp-maps whose partial sums are
bounded at `1`. -/
theorem exists_ncp_uwsum (g : ι → NCPMap T A) (b₀ : A)
    (hb : ∀ F : Finset ι, ∑ i ∈ F, g i 1 ≤ b₀) :
    ∃ L : NCPMap T A, ∀ z, UWTendsto (fun F : Finset ι => ∑ i ∈ F, g i z) atTop (L z) := by
  classical
  let _ : TopologicalSpace A := ultraweak A
  have : T2Space A := vn_positive_basic_1.1
  have : IsTopologicalAddGroup A := ultraweak_isTopologicalAddGroup
  have : ContinuousSMul ℂ A := ultraweak_continuousSMul_complex
  set S := ncpPartSum g with hSdef
  have hS1 : ∀ F, S F 1 ≤ b₀ := hb
  -- for positive `b` the partial sums increase and are bounded by `‖b‖ b₀`
  have hpos : ∀ b : T, 0 ≤ b →
      ∃ s, IsLUB (Set.range fun F => S F b) s ∧ UWTendsto (fun F => S F b) atTop s := by
    intro b hb0
    have hmono : Monotone fun F => S F b := by
      intro F G hFG
      change S F b ≤ S G b
      rw [hSdef, ncpPartSum_apply, ncpPartSum_apply, ← Finset.sum_sdiff hFG]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => ncpMap_nonneg (g i) hb0)
    have hbd : ∀ F, S F b ≤ ‖b‖ • b₀ := by
      intro F
      have h1 : S F b ≤ S F (algebraMap ℝ T ‖b‖) :=
        (S F).monotone' (IsSelfAdjoint.of_nonneg hb0).le_algebraMap_norm_self
      have h2 : S F (algebraMap ℝ T ‖b‖) = ‖b‖ • S F 1 := by
        rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, Complex.coe_smul]
      rw [h2] at h1
      refine h1.trans (sub_nonneg.mp ?_)
      rw [← smul_sub]
      exact smul_nonneg (norm_nonneg b) (sub_nonneg.mpr (hS1 F))
    have hnn : ∀ F, 0 ≤ S F b := fun F => by
      have := OrderHomClass.mono (S F) hb0
      rwa [map_zero] at this
    exact wit_uwTendsto_of_monotone _ hmono (fun F => IsSelfAdjoint.of_nonneg (hnn F)) hbd
  have hconv : ∀ b : T, ∃ s, UWTendsto (fun F => S F b) atTop s := by
    refine wit_nonneg_induction _ (fun b hb => (hpos b hb).imp fun s hs => hs.2) ?_ ?_
    · rintro b b' ⟨s, hs⟩ ⟨s', hs'⟩
      exact ⟨s + s', (hs.add hs').congr fun F => (map_add (S F) b b').symm⟩
    · rintro c b ⟨s, hs⟩
      exact ⟨c • s, (hs.const_smul c).congr fun F => (map_smul (S F) c b).symm⟩
  choose L hL using hconv
  have hLadd : ∀ b b', L (b + b') = L b + L b' := fun b b' =>
    uwTendsto_unique (hL (b + b'))
      ((hL b).add (hL b') |>.congr fun F => (map_add (S F) b b').symm)
  have hLsmul : ∀ (c : ℂ) b, L (c • b) = c • L b := fun c b =>
    uwTendsto_unique (hL (c • b))
      ((hL b).const_smul c |>.congr fun F => (map_smul (S F) c b).symm)
  set Ll : T →ₗ[ℂ] A := { toFun := L, map_add' := hLadd, map_smul' := hLsmul }
  have hLl : ∀ b, UWTendsto (fun F => S F b) atTop (Ll b) := hL
  have htail : ∀ F (b : T), 0 ≤ b → S F b ≤ L b := by
    intro F b hb0
    obtain ⟨s, hs, hlim⟩ := hpos b hb0
    rw [uwTendsto_unique (hL b) hlim]
    exact hs.1 ⟨F, rfl⟩
  have hunif : ∀ ω : NPFunctional A, ∀ ε > (0 : ℝ),
      ∀ᶠ F in atTop, ∀ p ∈ effects T, ‖ω (S F p) - ω (Ll p)‖ ≤ ε := by
    intro ω ε hε
    have h1 : Tendsto (fun F => ‖ω (Ll 1) - ω (S F 1)‖) atTop (𝓝 0) := by
      change Tendsto (fun F => ‖ω (L 1) - ω (S F 1)‖) atTop (𝓝 0)
      have := ((uwTendsto_iff _ _ _).mp (hL 1) ω)
      have h2 := (tendsto_const_nhds (x := ω (L 1))).sub this
      rw [sub_self] at h2
      simpa using h2.norm
    filter_upwards [(tendsto_order.1 h1).2 ε hε] with F hF p hp
    have hp0 : 0 ≤ Ll p - S F p := sub_nonneg.mpr (htail F p hp.1)
    have hp1 : Ll p - S F p ≤ Ll 1 - S F 1 := by
      have := htail F (1 - p) (sub_nonneg.mpr hp.2)
      change S F (1 - p) ≤ Ll (1 - p) at this
      rw [map_sub, map_sub] at this
      rw [← sub_nonneg] at this ⊢
      convert this using 1
      change Ll 1 - S F 1 - (Ll p - S F p) = Ll 1 - Ll p - (S F 1 - S F p)
      abel
    have hω0 := npFunctional_nonneg ω hp0
    have hω1 := npFunctional_mono ω hp1
    rw [npFunctional_sub] at hω0 hω1
    rw [npFunctional_sub] at hω1
    rw [← norm_neg, neg_sub]
    exact (wit_norm_le_of_le hω0 hω1).trans hF.le
  have hcp := ncp_uwlim_1 atTop S Ll hLl (fun F => ncpPartSum_cp g F)
  have hn := ncp_uwlim_2 atTop S Ll hLl (fun F => ncpPartSum_normal g F) hunif
  refine ⟨⟨⟨Ll, ?_⟩, hn⟩, hL⟩
  have h : ∀ (N : ℕ) (M : CStarMatrix (Fin N) (Fin N) T), 0 ≤ M → 0 ≤ M.map ⇑Ll :=
    (Theses.A.CStar.cp_iff Ll).out 0 1 |>.mp hcp
  exact h

end UWSum

/-! ## Direct sums of type I factors: the block argument

The note proves the "in particular" of Proposition 7 (and so Corollary 12)
by decomposing `ℛ ⊗ ℛ^□` along the minimal central projections.  Here the
same block argument is run on the domain side: for an nmiu-map
`ϱ : ⊕ᵢ 𝒳ᵢ → 𝒫`, maps `mᵢ : 𝒳ᵢ ⊗ ϱ(𝒳)^□ → 𝒫` with
`mᵢ(x ⊗ t) = ϱ(κᵢ x) t` add up (ultraweakly) to the extension
`m : 𝒳 ⊗ ϱ(𝒳)^□ → 𝒫` of Lemma 9 (`splitsOffCommutant_range_of_blocks`);
for `𝒳ᵢ = 𝓑(ℋᵢ)` the `mᵢ` come from Lemma 6 in the corner `qᵢ𝒫qᵢ`,
`qᵢ = ϱ(κᵢ(1))` (`exists_bh_piece`). -/

section Blocks

variable {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  [VonNeumannAlgebra P]

/-- `SplitsOffCommutant` only depends on the subalgebra. -/
theorem splitsOffCommutant_congr {R R' : StarSubalgebra ℂ P} (h : R = R')
    (hR : IsVNSubalgebra P R) (hR' : IsVNSubalgebra P R') :
    SplitsOffCommutant R hR ↔ SplitsOffCommutant R' hR' := by
  subst h; rfl

/-- The block lemma: if every block `κᵢ(𝒳ᵢ)` of `𝒳 = ⊕ᵢ 𝒳ᵢ` admits an
ncp-map `𝒳ᵢ ⊗ ϱ(𝒳)^□ → 𝒫`, `x ⊗ t ↦ ϱ(κᵢ x) t`, then `ϱ(𝒳)` splits off its
commutant: the ultraweak sum of the blocks is the nmiu-extension of Lemma 9. -/
theorem splitsOffCommutant_range_of_blocks {I : Type u} {Xs : I → Type u}
    [∀ i, CStarAlgebra (Xs i)] [∀ i, Nontrivial (Xs i)] [∀ i, PartialOrder (Xs i)]
    [∀ i, StarOrderedRing (Xs i)] [∀ i, VonNeumannAlgebra (Xs i)]
    (ρ : NMIUMap (lp Xs ∞) P) (ms : ∀ i, NCPMap (VNT (Xs i) (RangeComm ρ)) P)
    (hms : ∀ i x t, ms i (x ⊗ᵥ t) = ρ (lpKappa i x) * t.val) :
    SplitsOffCommutant (rangeSub ρ) (nmiu_image ρ) := by
  classical
  rw [splitsOffCommutant_range_iff]
  have hρm : ∀ a b, ρ (a * b) = ρ a * ρ b := fun a b => map_mul ρ.toStarAlgHom a b
  have hρ1 : ρ 1 = 1 := map_one ρ.toStarAlgHom
  have hcomm : ∀ (t : RangeComm ρ) (x : lp Xs ∞), ρ x * t.val = t.val * ρ x :=
    fun t x => mem_rangeComm.mp t.property x
  set g : I → NCPMap (VNT (lp Xs ∞) (RangeComm ρ)) P := fun i =>
    ncpComp (ms i) (tmap (nmiuNCP (lpProjNMIU i)) (ncpId (RangeComm ρ)))
  have hg : ∀ i x t, g i (x ⊗ᵥ t) = ρ (lpKappa i ((x : ∀ j, Xs j) i)) * t.val := by
    intro i x t
    simp only [g]
    rw [ncpComp_apply, tmap_apply, nmiuNCP_apply, ncpId_apply, lpProjNMIU_apply, hms]
  have hone : ((1 : lp Xs ∞) ⊗ᵥ (1 : RangeComm ρ)) = 1 :=
    (vnTensor (lp Xs ∞) (RangeComm ρ)).isTensorProduct.miu.1
  have hsumρ : ∀ (F : Finset I) (x : lp Xs ∞),
      ∑ i ∈ F, ρ (lpKappa (𝒜 := Xs) i ((x : ∀ j, Xs j) i))
        = ρ (∑ i ∈ F, lpKappa (𝒜 := Xs) i ((x : ∀ j, Xs j) i)) :=
    fun F x => (map_sum ρ.toStarAlgHom _ F).symm
  have hb : ∀ F : Finset I, ∑ i ∈ F, g i 1 ≤ 1 := by
    intro F
    rw [← hone]
    simp only [hg]
    change ∑ i ∈ F, ρ (lpKappa (𝒜 := Xs) i (((1 : lp Xs ∞) : ∀ j, Xs j) i)) * 1 ≤ 1
    simp only [mul_one]
    rw [hsumρ, ← hρ1]
    refine starAlgHom_mono' ρ.toStarAlgHom ?_
    rw [lp_infty_le_iff]
    intro k
    rw [lpKappa_sum_apply]
    split_ifs
    · exact le_rfl
    · rw [lp.infty_coeFn_one, Pi.one_apply]; exact zero_le_one
  obtain ⟨L, hL⟩ := exists_ncp_uwsum g 1 hb
  have hLel : ∀ x t, L (x ⊗ᵥ t) = ρ x * t.val := by
    intro x t
    let _ : TopologicalSpace P := ultraweak P
    let _ : TopologicalSpace (lp Xs ∞) := ultraweak _
    refine uwTendsto_unique (hL _) ?_
    have hc : @Continuous (lp Xs ∞) P (ultraweak _) (ultraweak P) fun z => ρ z * t.val :=
      @Continuous.comp _ _ _ (ultraweak _) (ultraweak P) (ultraweak P) _ _
        (mult_uws_cont _).2.1 (nmiu_uwContinuous ρ)
    refine ((hc.tendsto x).comp (uwTendsto_lpRestrict x)).congr fun F => ?_
    simp only [Function.comp_apply, hg]
    rw [← Finset.sum_mul, hsumρ]
  have hL1 : L 1 = 1 := by rw [← hone, hLel, hρ1]; exact one_mul _
  have hLmul : ∀ (x x' : lp Xs ∞) (t t' : RangeComm ρ),
      L ((x * x') ⊗ᵥ (t * t')) = L (x ⊗ᵥ t) * L (x' ⊗ᵥ t') := by
    intro x x' t t'
    rw [hLel, hLel, hLel, hρm]
    change ρ x * ρ x' * (t.val * t'.val) = ρ x * t.val * (ρ x' * t'.val)
    rw [mul_assoc, ← mul_assoc (ρ x'), hcomm, mul_assoc, mul_assoc]
  exact ⟨nmiuOfTensor L hL1 hLmul, hLel⟩

/-- A block `θ : 𝓑(ℋ) → ϱ(𝒳) ⊆ 𝒫` (a normal ∗-homomorphism, not
necessarily unital) gives an ncp-map `𝓑(ℋ) ⊗ ϱ(𝒳)^□ → 𝒫`,
`x ⊗ t ↦ θ(x)t`: in the corner `q𝒫q`, `q = θ(1)`, Lemma 6
(`exists_bh_split`) applies to the unital `θ : 𝓑(ℋ) → q𝒫q`, and
`t ↦ qtq` maps `ϱ(𝒳)^□` into the commutant of `θ(𝓑(ℋ))` in `q𝒫q`. -/
theorem exists_bh_piece {X : Type u} [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
    [VonNeumannAlgebra X] (ρ : NMIUMap X P)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (θ : NCPMap (H →L[ℂ] H) P) (hθm : ∀ a b, θ (a * b) = θ a * θ b)
    (hθs : ∀ a, θ (star a) = star (θ a)) (hθρ : ∀ a, θ a ∈ rangeSub ρ) :
    ∃ m : NCPMap (VNT (H →L[ℂ] H) (RangeComm ρ)) P, ∀ x t, m (x ⊗ᵥ t) = θ x * t.val := by
  set q := θ 1 with hqdef
  have hq : IsStarProjection q :=
    ⟨by rw [IsIdempotentElem, hqdef, ← hθm, one_mul],
      by rw [IsSelfAdjoint, hqdef, ← hθs, star_one]⟩
  have : Fact (IsStarProjection q) := ⟨hq⟩
  have hqx : ∀ x, q * θ x = θ x := fun x => by rw [hqdef, ← hθm, one_mul]
  have hxq : ∀ x, θ x * q = θ x := fun x => by rw [hqdef, ← hθm, mul_one]
  have hcommρ : ∀ (t : RangeComm ρ) (a : H →L[ℂ] H), θ a * t.val = t.val * θ a := by
    intro t a
    obtain ⟨y, hy⟩ := hθρ a
    rw [← hy]
    exact mem_rangeComm.mp t.property y
  -- `θ` as a unital nmiu-map into the corner `q𝒫q`
  have hmemq : ∀ x, q * θ x * q = θ x := fun x => by rw [hqx, hxq]
  let θ' : NMIUMap (H →L[ℂ] H) (Corner P q) :=
    { toStarAlgHom :=
        { toFun := fun x => ⟨θ x, hmemq x⟩
          map_one' := Corner.val_injective rfl
          map_mul' := fun a b => Corner.val_injective (hθm a b)
          map_zero' := Corner.val_injective (wncp_zero θ)
          map_add' := fun a b => Corner.val_injective (wncp_add θ a b)
          commutes' := fun r => Corner.val_injective (by
            rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
            change θ (r • 1) = r • q
            rw [wncp_smul])
          map_star' := fun a => Corner.val_injective (hθs a) }
      preservesDirSups' := by
        intro D s hne hdir hlub
        have hfn := θ.preservesDirSups' D s hne hdir hlub
        constructor
        · rintro _ ⟨d, hd, rfl⟩
          exact hfn.1 ⟨d, hd, rfl⟩
        · intro u hu
          exact hfn.2 (by rintro _ ⟨d, hd, rfl⟩; exact hu ⟨d, hd, rfl⟩) }
  have hθ' : ∀ x, (θ' x).val = θ x := fun x => rfl
  obtain ⟨Ψ, -, hΨ⟩ := exists_bh_split θ'
  -- `t ↦ qtq : ϱ(𝒳)^□ → θ'(𝓑(ℋ))^□`
  obtain ⟨fq, hfq⟩ := exists_adToCorner q q hq.isIdempotentElem.eq
  set base := ncpComp fq (nmiuNCP (Theses.A.Proc.VNSub.valNMIU (A := P) (S := rangeComm ρ)
    (hS := isVNSubalgebra_rangeComm ρ)))
  have hbase : ∀ t : RangeComm ρ, (base t).val = q * t.val * q := by
    intro t
    rw [ncpComp_apply, hfq, nmiuNCP_apply, Theses.A.Proc.VNSub.valNMIU_apply,
      hq.isSelfAdjoint.star_eq]
  have hqt : ∀ t : RangeComm ρ, q * t.val = t.val * q := fun t => hcommρ t 1
  have hmem : ∀ t, base t ∈ rangeComm θ' := by
    intro t
    rw [mem_rangeComm]
    intro x
    refine Corner.val_injective ?_
    change θ x * (base t).val = (base t).val * θ x
    have e1 : θ x * (q * t.val * q) = t.val * θ x := by
      rw [← mul_assoc, ← mul_assoc, hxq, hcommρ, mul_assoc, hxq]
    have e2 : q * t.val * q * θ x = t.val * θ x := by
      rw [mul_assoc, hqx, mul_assoc, ← hcommρ, ← mul_assoc, hqx, hcommρ]
    rw [hbase, e1, e2]
  set τ := ncpCorestrict base (rangeComm θ') (isVNSubalgebra_rangeComm θ') hmem
  refine ⟨ncpComp (cornerIncl q).toNCPMap (ncpComp (nmiuNCP Ψ) (tmap (ncpId _) τ)),
    fun x t => ?_⟩
  rw [ncpComp_apply, ncpComp_apply, tmap_apply, ncpId_apply, nmiuNCP_apply, cornerIncl_apply,
    hΨ]
  change θ x * (base t).val = θ x * t.val
  rw [hbase, ← mul_assoc, ← mul_assoc, hxq, hcommρ, mul_assoc, hxq]

/-- For an nmiu-map `ϱ : ⊕ᵢ 𝓑(ℋᵢ) → 𝒫` the image `ϱ(𝒳)` splits off its
commutant: the block lemma with the pieces of `exists_bh_piece`. -/
theorem splitsOffCommutant_range_lp_bh {I : Type u} {Hs : I → Type u}
    [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
    [∀ i, CompleteSpace (Hs i)] [∀ i, Nontrivial (Hs i →L[ℂ] Hs i)]
    (ρ : NMIUMap (lp (fun i => Hs i →L[ℂ] Hs i) ∞) P) :
    SplitsOffCommutant (rangeSub ρ) (nmiu_image ρ) := by
  have hpiece : ∀ i, ∃ m : NCPMap (VNT (Hs i →L[ℂ] Hs i) (RangeComm ρ)) P,
      ∀ x t, m (x ⊗ᵥ t) = ρ (lpKappa (𝒜 := fun i => Hs i →L[ℂ] Hs i) i x) * t.val := by
    intro i
    set θ := ncpComp (nmiuNCP ρ) (lpKappaNCP (𝒜 := fun i => Hs i →L[ℂ] Hs i) i)
    have hθ : ∀ a, θ a = ρ (lpKappa (𝒜 := fun i => Hs i →L[ℂ] Hs i) i a) := fun a => by
      rw [ncpComp_apply, nmiuNCP_apply, lpKappaNCP_apply]
    obtain ⟨m, hm⟩ := exists_bh_piece ρ θ
      (fun a b => by
        rw [hθ, hθ, hθ, ← lpKappa_mul]
        exact map_mul ρ.toStarAlgHom _ _)
      (fun a => by
        rw [hθ, hθ, ← lpKappa_star]
        exact map_star ρ.toStarAlgHom _)
      (fun a => ⟨_, (hθ a).symm⟩)
    exact ⟨m, fun x t => by rw [hm, hθ]⟩
  choose ms hms using hpiece
  exact splitsOffCommutant_range_of_blocks ρ ms hms

end Blocks

/-! ## Proposition 7 "in particular" and Corollary 12 -/

section AtomicTypeI

variable {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  [VonNeumannAlgebra P]

/-- For an nmiu-map `ϱ` out of a direct sum of type I factors (`AtomicTypeI`,
`𝒳 ≅ ⊕ⱼ 𝓑(𝒦ⱼ)`), the image `ϱ(𝒳)` splits off its commutant. -/
theorem splitsOffCommutant_range_of_atomicTypeI {X : Type u} [CStarAlgebra X]
    [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X] (hX : AtomicTypeI X)
    (ρ : NMIUMap X P) : SplitsOffCommutant (rangeSub ρ) (nmiu_image ρ) := by
  obtain ⟨rep⟩ := hX
  set e := rep.iso
  set ρ' := nmiuComp ρ (nmiuOfBijective e.symm.toStarAlgHom e.symm.bijective)
  have hr : rangeSub ρ' = rangeSub ρ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨e x, ?_⟩
      change ρ (e.symm (e x)) = ρ x
      rw [StarAlgEquiv.symm_apply_apply]
  exact (splitsOffCommutant_congr hr _ _).mp (splitsOffCommutant_range_lp_bh ρ')

/-- The note's **Proposition 7**, "in particular": a von Neumann subalgebra
of `𝒫` that is a direct sum of type I factors splits off its commutant.
Proved by the block argument on `ℛ ≅ ⊕ⱼ 𝓑(𝒦ⱼ)`
(`splitsOffCommutant_range_lp_bh`) rather than through the general `⇐` of
Proposition 7. -/
theorem splitsOffCommutant_of_atomicTypeI (R : StarSubalgebra ℂ P) (hR : IsVNSubalgebra P R)
    (hRI : AtomicTypeI (SubVN R hR)) : SplitsOffCommutant R hR := by
  have h := splitsOffCommutant_range_of_atomicTypeI hRI Theses.A.Proc.VNSub.valNMIU
  have hr : rangeSub (Theses.A.Proc.VNSub.valNMIU (A := P) (S := R) (hS := hR)) = R :=
    Theses.A.Proc.VNSub.valNMIU_range
  exact (splitsOffCommutant_congr hr _ _).mp h

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]

/-- The note's **Corollary 12**: every ncp-map `φ : 𝒳 → 𝒜` on a direct sum
`𝒳` of type I factors has a Wittrock dilation — Theorem 10 with the
splitting of `ϱ(𝒳)` from `splitsOffCommutant_range_of_atomicTypeI`, for the
Paschke dilation of **154III**.  (The note passes through
`ϱ(𝒳) ≅ c𝒳`; the block argument makes that unnecessary.) -/
theorem exists_wittrockDilation_of_atomicTypeI {X : Type u} [CStarAlgebra X]
    [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X] (hX : AtomicTypeI X)
    (φ : NCPMap X A) :
    ∃ (E : Type u) (_ : CStarAlgebra E) (_ : PartialOrder E) (_ : StarOrderedRing E)
      (_ : VonNeumannAlgebra E) (h : NCPMap (VNT X E) A), IsWittrockDilationOf ⇑φ E h := by
  obtain ⟨M⟩ := existence_paschke φ
  let _ : VonNeumannAlgebra (Ba A M.X)ᵐᵒᵖ :=
    @vonNeumannAlgebra_mulOpposite (Ba A M.X) _ _ _ (ba_vonNeumannAlgebra M.selfDual)
  exact (wittrock_iff_splitsOffCommutant φ M.ρ M.h (existence_paschke_5 φ M)).mpr
    (splitsOffCommutant_range_of_atomicTypeI hX M.ρ)

end AtomicTypeI

/-! ## Proposition 7 -/

section Prop7

variable {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  [VonNeumannAlgebra P]

/-- `cℛ` as a subalgebra of the corner `c𝒫c`, for a projection `c ∈ ℛ`:
the elements of the corner that lie in `ℛ` (which, for `c` central in `ℛ`,
are exactly the `ca`, `a ∈ ℛ`). -/
def cornerSub (R : StarSubalgebra ℂ P) (c : P) [Fact (IsStarProjection c)] (hcR : c ∈ R) :
    StarSubalgebra ℂ (Corner P c) where
  carrier := {x | x.val ∈ R}
  mul_mem' {x y} hx hy := by
    change x.val * y.val ∈ R
    exact mul_mem (show x.val ∈ R from hx) (show y.val ∈ R from hy)
  add_mem' {x y} hx hy := by
    change x.val + y.val ∈ R
    exact add_mem (show x.val ∈ R from hx) (show y.val ∈ R from hy)
  algebraMap_mem' r := by
    change (algebraMap ℂ (Corner P c) r).val ∈ R
    rw [Algebra.algebraMap_eq_smul_one]
    exact R.smul_mem hcR r
  star_mem' {x} hx := by
    change (star x).val ∈ R
    exact star_mem (show x.val ∈ R from hx)

omit [VonNeumannAlgebra P] in
theorem mem_cornerSub {R : StarSubalgebra ℂ P} {c : P} [Fact (IsStarProjection c)]
    {hcR : c ∈ R} {x : Corner P c} : x ∈ cornerSub R c hcR ↔ x.val ∈ R :=
  Iff.rfl

/-- `cℛ` is a von Neumann subalgebra of `c𝒫c`: suprema in the corner are
suprema in `𝒫`. -/
theorem isVNSubalgebra_cornerSub {R : StarSubalgebra ℂ P} (hR : IsVNSubalgebra P R) (c : P)
    [Fact (IsStarProjection c)] (hcR : c ∈ R) : IsVNSubalgebra (Corner P c) (cornerSub R c hcR) :=
  ⟨by exact hR.isClosed.preimage (Corner.isometry_val (e := c)).continuous,
    fun D s hD hne hdir hlub => by
    have h := Corner.isLUB_saMap_image hne hdir hlub
    refine mem_cornerSub.mpr
      (hR.dirSup_mem (Corner.saMap '' D) (Corner.saMap s) ?_ (hne.image _) ?_ h)
    · rintro _ ⟨d, hd, rfl⟩
      exact mem_cornerSub.mp (hD d hd)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
      obtain ⟨v, hv, hxv, hzv⟩ := hdir x hx z hz
      exact ⟨Corner.saMap v, ⟨v, hv, rfl⟩, hxv, hzv⟩⟩

variable {R : StarSubalgebra ℂ P} {hR : IsVNSubalgebra P R}

/-- The compression `a ↦ cac : ℛ → cℛ` for a central projection `c` of `ℛ`,
as an ncp-map (from `exists_adToCorner`). -/
theorem exists_compress_sub (c : P) [Fact (IsStarProjection c)] (hc : c ∈ centreSub R) :
    ∃ π : NCPMap (SubVN R hR) (SubVN (cornerSub R c hc.1) (isVNSubalgebra_cornerSub hR c hc.1)),
      ∀ a, (π a).val.val = c * a.val * c := by
  have hcp : IsStarProjection c := Fact.out
  obtain ⟨fq, hfq⟩ := exists_adToCorner c c hcp.isIdempotentElem.eq
  set base := ncpComp fq (nmiuNCP (Theses.A.Proc.VNSub.valNMIU (A := P) (S := R) (hS := hR)))
  have hbase : ∀ a : SubVN R hR, (base a).val = c * a.val * c := by
    intro a
    rw [ncpComp_apply, hfq, nmiuNCP_apply, Theses.A.Proc.VNSub.valNMIU_apply,
      hcp.isSelfAdjoint.star_eq]
  have hmem : ∀ a, base a ∈ cornerSub R c hc.1 := fun a => by
    rw [mem_cornerSub, hbase]
    exact mul_mem (mul_mem hc.1 a.property) hc.1
  exact ⟨ncpCorestrict base _ _ hmem, fun a => hbase a⟩

/-- The compression `t ↦ ctc : ℛ^□ → (cℛ)^□` (commutant in `c𝒫c`). -/
theorem exists_compress_comm (c : P) [Fact (IsStarProjection c)] (hc : c ∈ centreSub R) :
    ∃ π : NCPMap (CommVN R) (CommVN (cornerSub R c hc.1)),
      ∀ t, (π t).val.val = c * t.val * c := by
  have hcp : IsStarProjection c := Fact.out
  obtain ⟨fq, hfq⟩ := exists_adToCorner c c hcp.isIdempotentElem.eq
  set base := ncpComp fq (nmiuNCP (Theses.A.Proc.VNSub.valNMIU (A := P) (S := relComm R)
    (hS := isVNSubalgebra_relComm R)))
  have hbase : ∀ t : CommVN R, (base t).val = c * t.val * c := by
    intro t
    rw [ncpComp_apply, hfq, nmiuNCP_apply, Theses.A.Proc.VNSub.valNMIU_apply,
      hcp.isSelfAdjoint.star_eq]
  have hmem : ∀ t, base t ∈ relComm (cornerSub R c hc.1) := by
    intro t
    rw [mem_relComm]
    intro y hy
    refine Corner.val_injective ?_
    change y.val * (base t).val = (base t).val * y.val
    have hyR : y.val ∈ R := mem_cornerSub.mp hy
    have hty : y.val * t.val = t.val * y.val := mem_relComm.mp t.property _ hyR
    have hct : c * t.val = t.val * c := mem_relComm.mp t.property _ hc.1
    have hyc : y.val * c = y.val := Corner.mul_right y
    have hcy : c * y.val = y.val := Corner.mul_left y
    have e1 : y.val * (c * t.val * c) = t.val * y.val := by
      rw [← mul_assoc, ← mul_assoc, hyc, hty, mul_assoc, hyc]
    have e2 : c * t.val * c * y.val = t.val * y.val := by
      rw [mul_assoc, hcy, hct, mul_assoc, hcy]
    rw [hbase, e1, e2]
  exact ⟨ncpCorestrict base _ _ hmem, fun t => hbase t⟩

/-- The note's **Proposition 7**, `⇒`, second half: if `ℛ` splits off its
commutant in `𝒫`, so does `cℛ` in `c𝒫c` for every central projection `c`
of `ℛ` (the note states it for the minimal ones).  The extension `μ` is
restricted along the inclusions `cℛ ⊆ ℛ`, `(cℛ)^□ ⊆ ℛ^□`, and compressed
to `c𝒫c`. -/
theorem splitsOffCommutant_corner (hs : SplitsOffCommutant R hR) (c : P)
    [Fact (IsStarProjection c)] (hc : c ∈ centreSub R) :
    SplitsOffCommutant (cornerSub R c hc.1) (isVNSubalgebra_cornerSub hR c hc.1) := by
  obtain ⟨μ, hμ⟩ := hs
  have hcp : IsStarProjection c := Fact.out
  have hcR : c ∈ R := hc.1
  have hcC : c ∈ relComm R := hc.2
  have hcc : ∀ a ∈ R, c * a = a * c := fun a ha => (mem_relComm.mp hcC a ha).symm
  -- the inclusions `cℛ → ℛ`, `(cℛ)^□ → ℛ^□`
  set ι₁ : NCPMap (SubVN (cornerSub R c hc.1) (isVNSubalgebra_cornerSub hR c hc.1)) (SubVN R hR) :=
    ncpCorestrict (ncpComp (cornerIncl c).toNCPMap (nmiuNCP Theses.A.Proc.VNSub.valNMIU)) R hR
      (fun x => by
        rw [ncpComp_apply, nmiuNCP_apply, cornerIncl_apply]; exact mem_cornerSub.mp x.property)
  have hι₁ : ∀ x, (ι₁ x).val = x.val.val := fun x => by
    rw [ncpCorestrict_val, ncpComp_apply, nmiuNCP_apply, cornerIncl_apply]; rfl
  have hmem₂ : ∀ y : CommVN (cornerSub R c hc.1), y.val.val ∈ relComm R := by
    intro y
    rw [mem_relComm]
    intro a ha
    have hyc : y.val.val * c = y.val.val := Corner.mul_right y.val
    have hcy : c * y.val.val = y.val.val := Corner.mul_left y.val
    -- `cac ∈ cℛ` commutes with `y`
    have hmem : (⟨c * a * c, by
        rw [← mul_assoc, ← mul_assoc, hcp.isIdempotentElem.eq, mul_assoc,
          hcp.isIdempotentElem.eq]⟩ : Corner P c) ∈ cornerSub R c hc.1 :=
      mem_cornerSub.mpr (mul_mem (mul_mem hcR ha) hcR)
    have hcomm := congrArg Corner.val (mem_relComm.mp y.property _ hmem)
    change c * a * c * y.val.val = y.val.val * (c * a * c) at hcomm
    have e1 : c * a * c * y.val.val = a * y.val.val := by
      rw [mul_assoc, hcy, hcc a ha, mul_assoc, hcy]
    have e2 : y.val.val * (c * a * c) = y.val.val * a := by
      rw [← mul_assoc, ← mul_assoc, hyc, mul_assoc, ← hcc a ha, ← mul_assoc, hyc]
    rw [e1, e2] at hcomm
    exact hcomm
  set ι₂ : NCPMap (CommVN (cornerSub R c hc.1)) (CommVN R) :=
    ncpCorestrict (ncpComp (cornerIncl c).toNCPMap (nmiuNCP Theses.A.Proc.VNSub.valNMIU))
      (relComm R) (isVNSubalgebra_relComm R)
      (fun y => by rw [ncpComp_apply, nmiuNCP_apply, cornerIncl_apply]; exact hmem₂ y)
  have hι₂ : ∀ y, (ι₂ y).val = y.val.val := fun y => by
    rw [ncpCorestrict_val, ncpComp_apply, nmiuNCP_apply, cornerIncl_apply]; rfl
  obtain ⟨fq, hfq⟩ := exists_adToCorner c c hcp.isIdempotentElem.eq
  set G := ncpComp fq (ncpComp (nmiuNCP μ) (tmap ι₁ ι₂))
  have hG : ∀ x y, (G (x ⊗ᵥ y)).val = x.val.val * y.val.val := by
    intro x y
    rw [ncpComp_apply, hfq, ncpComp_apply, tmap_apply, nmiuNCP_apply, hμ, hι₁, hι₂,
      hcp.isSelfAdjoint.star_eq]
    have hxc : c * x.val.val = x.val.val := Corner.mul_left x.val
    have hyc : y.val.val * c = y.val.val := Corner.mul_right y.val
    rw [← mul_assoc, hxc, mul_assoc, hyc]
  have hG' : ∀ x y, G (x ⊗ᵥ y) = x.val * y.val := fun x y => Corner.val_injective (hG x y)
  have hone : ∀ {Y Z : Type u} [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y]
      [VonNeumannAlgebra Y] [CStarAlgebra Z] [PartialOrder Z] [StarOrderedRing Z]
      [VonNeumannAlgebra Z], ((1 : Y) ⊗ᵥ (1 : Z)) = 1 :=
    fun {Y Z} _ _ _ _ _ _ _ _ => (vnTensor Y Z).isTensorProduct.miu.1
  have hG1 : G 1 = 1 := by rw [← hone, hG']; exact one_mul _
  have hGmul : ∀ (x x' : SubVN (cornerSub R c hc.1) (isVNSubalgebra_cornerSub hR c hc.1))
      (y y' : CommVN (cornerSub R c hc.1)),
      G ((x * x') ⊗ᵥ (y * y')) = G (x ⊗ᵥ y) * G (x' ⊗ᵥ y') := by
    intro x x' y y'
    rw [hG', hG', hG']
    have hcm : y.val * x'.val = x'.val * y.val := (mem_relComm.mp y.property _ x'.property).symm
    change x.val * x'.val * (y.val * y'.val) = x.val * y.val * (x'.val * y'.val)
    rw [mul_assoc, ← mul_assoc x'.val, ← hcm, mul_assoc, mul_assoc]
  exact ⟨nmiuOfTensor G hG1 hGmul, hG'⟩

/-- The note's **Proposition 7**, `⇐`: if the centre of `ℛ` is
nmiu-isomorphic to `ℓ^∞(I)` and `cℛ` splits off its commutant in `c𝒫c` for
every minimal central projection `c`, then `ℛ` splits off its commutant.
The minimal central projections `cᵢ` (the images of the `δᵢ`) sum to `1`,
and the blocks `a ⊗ t ↦ cᵢat` — the extensions for `cᵢℛ ⊆ cᵢ𝒫cᵢ`
precomposed with the compressions — add up ultraweakly to the extension
for `ℛ` (the note's decomposition along `⊕_{i,j} cᵢℛ ⊗ cⱼℛ^□`, of which only
the diagonal blocks survive). -/
theorem splitsOffCommutant_of_centre_corners
    (hZ : ∃ (I : Type u) (f : NMIUMap (CentreVN R hR) (linf I)), Function.Bijective f)
    (hC : ∀ (c : P) [Fact (IsStarProjection c)] (hc : IsMinCentralProj R c),
      SplitsOffCommutant (cornerSub R c hc.1.1) (isVNSubalgebra_cornerSub hR c hc.1.1)) :
    SplitsOffCommutant R hR := by
  classical
  obtain ⟨I, f, hf⟩ := hZ
  set g := nmiuSymm f hf
  set c : I → P := fun i => (g (lpKappa i (1 : ℂ))).val
  have hmin : ∀ i, IsMinCentralProj R (c i) :=
    fun i => isMinCentralProj_of_isMinProj (isMinProj_symm_linf f hf i)
  have hcc : ∀ i, ∀ a ∈ R, c i * a = a * c i :=
    fun i a ha => (mem_relComm.mp (hmin i).1.2 a ha).symm
  have hct : ∀ i (t : CommVN R), c i * t.val = t.val * c i :=
    fun i t => mem_relComm.mp t.property _ (hmin i).1.1
  -- the blocks `a ⊗ t ↦ cᵢat`
  have hpiece : ∀ i, ∃ Ψ : NCPMap (VNT (SubVN R hR) (CommVN R)) P,
      ∀ a t, Ψ (a ⊗ᵥ t) = c i * (a.val * t.val) := by
    intro i
    have : Fact (IsStarProjection (c i)) := ⟨(hmin i).2.1⟩
    have hcp : IsStarProjection (c i) := (hmin i).2.1
    obtain ⟨μ, hμ⟩ := hC (c i) (hmin i)
    obtain ⟨π₁, hπ₁⟩ := exists_compress_sub (hR := hR) (c i) (hmin i).1
    obtain ⟨π₂, hπ₂⟩ := exists_compress_comm (R := R) (c i) (hmin i).1
    refine ⟨ncpComp (cornerIncl (c i)).toNCPMap (ncpComp (nmiuNCP μ) (tmap π₁ π₂)),
      fun a t => ?_⟩
    rw [ncpComp_apply, ncpComp_apply, tmap_apply, nmiuNCP_apply, cornerIncl_apply, hμ]
    change (π₁ a).val.val * (π₂ t).val.val = c i * (a.val * t.val)
    have e : c i * a.val * c i = c i * a.val := by
      rw [mul_assoc, ← hcc i _ a.property, ← mul_assoc, hcp.isIdempotentElem.eq]
    have e' : c i * t.val * c i = c i * t.val := by
      rw [mul_assoc, ← hct i t, ← mul_assoc, hcp.isIdempotentElem.eq]
    rw [hπ₁, hπ₂, e, e', mul_assoc, ← mul_assoc a.val, ← hcc i _ a.property, mul_assoc,
      ← mul_assoc, hcp.isIdempotentElem.eq]
  choose Ψs hΨs using hpiece
  -- `∑ᵢ cᵢ = 1` ultraweakly
  set h := nmiuComp (Theses.A.Proc.VNSub.valNMIU (A := P) (S := centreSub R)
    (hS := isVNSubalgebra_centreSub hR)) g
  have hc_h : ∀ i, c i = h (lpKappa i (1 : ℂ)) := fun i => rfl
  have hsum : ∀ F : Finset I, ∑ i ∈ F, c i = h (∑ i ∈ F, lpKappa i (1 : ℂ)) := fun F =>
    (map_sum h.toStarAlgHom (fun i => lpKappa (𝒜 := fun _ : I => ℂ) i (1 : ℂ)) F).symm
  have h1i : ∀ i, ((1 : linf I) : ∀ _ : I, ℂ) i = 1 := fun i => by
    rw [lp.infty_coeFn_one, Pi.one_apply]
  have hone : ((1 : SubVN R hR) ⊗ᵥ (1 : CommVN R)) = 1 :=
    (vnTensor (SubVN R hR) (CommVN R)).isTensorProduct.miu.1
  have hb : ∀ F : Finset I, ∑ i ∈ F, Ψs i 1 ≤ 1 := by
    intro F
    rw [← hone]
    simp only [hΨs]
    change ∑ i ∈ F, c i * (1 * 1) ≤ 1
    simp only [mul_one]
    rw [hsum, ← map_one h.toStarAlgHom]
    refine starAlgHom_mono' h.toStarAlgHom ?_
    have hF := lpKappa_sum_apply (1 : linf I) F
    simp only [h1i] at hF
    rw [lp_infty_le_iff]
    intro k
    rw [hF k]
    split_ifs
    · rw [h1i]
    · rw [h1i]; exact zero_le_one
  obtain ⟨L, hL⟩ := exists_ncp_uwsum Ψs 1 hb
  have hLel : ∀ a t, L (a ⊗ᵥ t) = a.val * t.val := by
    intro a t
    let _ : TopologicalSpace P := ultraweak P
    let _ : TopologicalSpace (linf I) := ultraweak _
    refine uwTendsto_unique (hL _) ?_
    have hc : @Continuous (linf I) P (ultraweak _) (ultraweak P)
        fun z => h z * (a.val * t.val) :=
      @Continuous.comp _ _ _ (ultraweak _) (ultraweak P) (ultraweak P) _ _
        (mult_uws_cont _).2.1 (nmiu_uwContinuous h)
    have hlim := (hc.tendsto 1).comp (uwTendsto_lpRestrict (1 : linf I))
    rw [show h 1 = 1 from map_one h.toStarAlgHom, one_mul] at hlim
    refine hlim.congr fun F => ?_
    simp only [Function.comp_apply, hΨs, h1i]
    rw [← Finset.sum_mul, hsum]
  have hL1 : L 1 = 1 := by rw [← hone, hLel]; exact one_mul _
  have hLmul : ∀ (a a' : SubVN R hR) (t t' : CommVN R),
      L ((a * a') ⊗ᵥ (t * t')) = L (a ⊗ᵥ t) * L (a' ⊗ᵥ t') := by
    intro a a' t t'
    rw [hLel, hLel, hLel]
    have hcm : t.val * a'.val = a'.val * t.val := (mem_relComm.mp t.property _ a'.property).symm
    change a.val * a'.val * (t.val * t'.val) = a.val * t.val * (a'.val * t'.val)
    rw [mul_assoc, ← mul_assoc a'.val, ← hcm, mul_assoc, mul_assoc]
  exact ⟨nmiuOfTensor L hL1 hLmul, hLel⟩

/-- The note's **Proposition 7**: `ℛ` splits off its commutant in `𝒫` iff its
centre is nmiu-isomorphic to some `ℓ^∞(I)` and `cℛ` splits off its
commutant in `c𝒫c` for every minimal central projection `c` of `ℛ`. -/
theorem splitsOffCommutant_iff_centre_corners :
    SplitsOffCommutant R hR ↔
      (∃ (I : Type u) (f : NMIUMap (CentreVN R hR) (linf I)), Function.Bijective f) ∧
        ∀ (c : P) [Fact (IsStarProjection c)] (hc : IsMinCentralProj R c),
          SplitsOffCommutant (cornerSub R c hc.1.1) (isVNSubalgebra_cornerSub hR c hc.1.1) :=
  ⟨fun hs => ⟨centre_linf_of_splitsOffCommutant hs,
      fun c _ hc => splitsOffCommutant_corner hs c hc.1⟩,
    fun ⟨hZ, hC⟩ => splitsOffCommutant_of_centre_corners hZ hC⟩

end Prop7

end Theses.B.Dils
