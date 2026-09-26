/-
FDS 2.2, "equivalently [GLR, Prop. 2.15]": the direction from the form
`WStarCategory` uses back to the print's primary definition `HomsHavePreduals`.

PLAN (written before the proof; feasibility decided first).

* Forward (predual form ⇒ `WStarCategory`) in general: NOT attempted.  Its one
  missing half, self-duality of `C(A,B)`, needs the preduals of the hom-sets
  to be tied to composition (`y ↦ x† ≫ y` weak-* continuous), which the print
  does not assume and which is the Sakai-type automatic-continuity theorem for
  the linking algebra `L`; without it the four preduals give a predual of `L`
  only for an equivalent (non C*) norm, so Mathlib's `WStarAlgebra` (an
  isometric predual) cannot be fed.  Neither the automatic continuity nor a
  Dixmier–Ng theorem exists in Mathlib or the tree; that is a research-size
  formalisation, well beyond 2,000 lines.  (`WStar.lean` keeps the forward
  direction under the common-embedding hypothesis.)
* Converse (`WStarCategory` ⇒ `HomsHavePreduals`), missing entirely so far,
  feasible (~500 lines), done here without the linking algebra:
  1. Kadison ⇒ predual.  For a (Kadison) von Neumann algebra `M` the evaluation
     `M → (M_*)*` is onto: the image of the unit ball is weak-* compact (the
     tree's **77III** `vn_ball_compact`: the ball is ultraweakly compact),
     convex, and a point outside it would be separated by an element of `M_*`
     (`Sakai.ks_separate`, WStar.lean), contradicting `‖ψ‖ ≤ 1`.  With
     **87VI** `norm_predual` it is isometric: `M ≅ (M_*)*`, so `M` is a
     Mathlib `WStarAlgebra` (the other half of DECISIONS §3.7).
  2. Self-dual ⇒ predual.  For a self-dual Hilbert `M`-module `X`, let
     `E ⊆ X*` be spanned by `e_{ω,g} = ω ∘ ⟨g, ·⟩` (`ω ∈ M_*`, `g ∈ X`).  The
     map `X → E*` is isometric (`‖x‖² = ‖⟨x,x⟩‖`, normed by `M_*`), and onto:
     for `φ ∈ E*` and each `g`, `ω ↦ φ(e_{ω,g})` lies in `(M_*)*`, hence is
     evaluation at some `τ₀ g ∈ M` (step 1); `g ↦ (τ₀ g)*` is a bounded module
     map (uniqueness in `M` because `M_*` separates points), so by
     self-duality `(τ₀ g)* = ⟨t, g⟩`, and `φ = ev_t` on the generators.
  3. Categories: `A ⟶ B` is self-dual over the von Neumann algebra `End B`
     in a `WStarCategory`, so every hom-set has a Banach predual.
-/
import Papers.FDS.WStar

open Filter Topology Set Metric CategoryTheory
open scoped ComplexOrder
open Theses Theses.A.VN Theses.B.Dils

noncomputable section

universe u v w

namespace Papers.FDS

namespace Linking

section Kadison

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [VonNeumannAlgebra M]

/-- The predual `M_*` of a von Neumann algebra (ultraweakly continuous
functionals, **87I**), as a normed space. -/
abbrev Pre (M : Type u) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [VonNeumannAlgebra M] : Submodule ℂ (M →L[ℂ] ℂ) := predualSub (A := M)

instance : CompleteSpace (Pre M) := (predual_complete (A := M)).completeSpace_coe

/-- The functionals of `M_*` separate the points of `M` (**87VI**). -/
theorem eq_of_forall_predual {a b : M} (h : ∀ f : Pre M, (f : M →L[ℂ] ℂ) a = (f : M →L[ℂ] ℂ) b) :
    a = b := by
  have hlub := norm_predual (a - b)
  have : ‖a - b‖ ≤ 0 := hlub.2 (by
    rintro r ⟨f, hf, -, rfl⟩
    have := h ⟨f, hf⟩
    simp only [map_sub] at *
    rw [this, sub_self, norm_zero])
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

/-- A norm bound through `M_*` (**87VI**). -/
theorem norm_le_of_forall_predual {a : M} {C : ℝ}
    (h : ∀ f : Pre M, ‖(f : M →L[ℂ] ℂ) a‖ ≤ C * ‖f‖) (hC : 0 ≤ C) : ‖a‖ ≤ C := by
  refine (norm_predual a).2 ?_
  rintro r ⟨f, hf, hf1, rfl⟩
  calc ‖f a‖ ≤ C * ‖(⟨f, hf⟩ : Pre M)‖ := h ⟨f, hf⟩
    _ ≤ C * 1 := by gcongr; exact hf1
    _ = C := mul_one C

/-- Right multiplication preserves normality: `y ↦ ω (y * b)` is in `M_*`. -/
def rmul (ω : Pre M) (b : M) : Pre M :=
  ⟨(ω : M →L[ℂ] ℂ).comp ((ContinuousLinearMap.mul ℂ M).flip b), by
    have hmul : @Continuous M M (ultraweak M) (ultraweak M) (fun y => y * b) := by
      refine continuous_ultraweak_of_npFunctional fun ν => ?_
      simpa only [one_mul] using continuous_ultraweak_conj ν 1 b
    show @Continuous M ℂ (ultraweak M) _ (fun y => (ω : M →L[ℂ] ℂ) (y * b))
    exact @Continuous.comp M M ℂ (ultraweak M) (ultraweak M) _ _ _
      (show @Continuous M ℂ (ultraweak M) _ ⇑(ω : M →L[ℂ] ℂ) from ω.2) hmul⟩

@[simp] theorem rmul_apply (ω : Pre M) (b y : M) :
    ((rmul ω b : Pre M) : M →L[ℂ] ℂ) y = (ω : M →L[ℂ] ℂ) (y * b) := rfl

/-- Evaluation `M → (M_*)*`. -/
def ev (a : M) : StrongDual ℂ (Pre M) :=
  (ContinuousLinearMap.apply ℂ ℂ a).comp (Pre M).subtypeL

@[simp] theorem ev_apply (a : M) (f : Pre M) : ev a f = (f : M →L[ℂ] ℂ) a := rfl

theorem norm_ev (a : M) : ‖ev a‖ = ‖a‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_
    rw [ev_apply, mul_comm]
    exact (f : M →L[ℂ] ℂ).le_opNorm a
  · refine norm_le_of_forall_predual (fun f => ?_) (norm_nonneg _)
    exact (ev a).le_opNorm f

/-- **Kadison ⇒ predual, the key step**: every functional of norm `≤ 1` on
`M_*` is evaluation at an element of the unit ball of `M`.  The image of the
ball is weak-* compact (**77III**) and convex; a point outside it would be
separated from it by an element of `M_*` (Krein–Šmulian, `Sakai.ks_separate`),
which the norm of that element forbids. -/
theorem exists_ev_eq_of_norm_le_one (ψ : StrongDual ℂ (Pre M)) (hψ : ‖ψ‖ ≤ 1) :
    ∃ a : M, ‖a‖ ≤ 1 ∧ ev a = ψ := by
  set K : Set (WeakDual ℂ (Pre M)) :=
    (fun a => StrongDual.toWeakDual (ev a)) '' closedBall (0 : M) 1 with hKdef
  have hcont : @Continuous M (WeakDual ℂ (Pre M)) (ultraweak M) _
      (fun a => StrongDual.toWeakDual (ev a)) := by
    let _ : TopologicalSpace M := ultraweak M
    exact WeakDual.continuous_of_continuous_eval fun f => f.2
  have hKc : IsCompact K := by
    let _ : TopologicalSpace M := ultraweak M
    exact vn_ball_compact.image hcont
  have hconv : ∀ w₁ ∈ K, ∀ w₂ ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (t : ℂ) • w₁ + ((1 - t : ℝ) : ℂ) • w₂ ∈ K := by
    rintro _ ⟨a₁, h₁, rfl⟩ _ ⟨a₂, h₂, rfl⟩ t ht0 ht1
    refine ⟨(t : ℂ) • a₁ + ((1 - t : ℝ) : ℂ) • a₂, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff] at h₁ h₂ ⊢
      calc ‖(t : ℂ) • a₁ + ((1 - t : ℝ) : ℂ) • a₂‖
          ≤ ‖(t : ℂ) • a₁‖ + ‖((1 - t : ℝ) : ℂ) • a₂‖ := norm_add_le _ _
        _ = t * ‖a₁‖ + (1 - t) * ‖a₂‖ := by
          rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg ht0, Real.norm_of_nonneg (by linarith)]
        _ ≤ t * 1 + (1 - t) * 1 := by gcongr
        _ = 1 := by ring
    · refine DFunLike.ext _ _ fun f => ?_
      simp [ev_apply]
      rfl
  have hK : ∀ r, IsClosed (K ∩ WeakDual.toStrongDual ⁻¹' closedBall 0 r) := fun r =>
    hKc.isClosed.inter (WeakDual.isClosed_closedBall 0 r)
  by_contra hne
  push Not at hne
  have hx₀ : StrongDual.toWeakDual ψ ∉ K := by
    rintro ⟨a, ha, hEq⟩
    exact hne a (mem_closedBall_zero_iff.mp ha) (StrongDual.toWeakDual.injective hEq)
  obtain ⟨e, he⟩ := Sakai.ks_separate hconv hK hx₀
  -- `he : ∀ w ∈ K, re ψ(e) + 1 ≤ re w(e)`
  have hsep : ∀ a : M, ‖a‖ ≤ 1 → (ψ e).re + 1 ≤ ((e : M →L[ℂ] ℂ) a).re := fun a ha =>
    he _ ⟨a, mem_closedBall_zero_iff.mpr ha, rfl⟩
  -- a point of the ball where `re e` is almost `-‖e‖`
  have hlt : ‖(e : M →L[ℂ] ℂ)‖ - 1 / 2 < ‖(e : M →L[ℂ] ℂ)‖ := by linarith
  obtain ⟨a, ha1, ha2⟩ := (e : M →L[ℂ] ℂ).exists_lt_apply_of_lt_opNorm hlt
  set z : ℂ := (e : M →L[ℂ] ℂ) a with hz
  set c : ℂ := -(starRingEnd ℂ z / (‖z‖ : ℂ)) with hc
  have hcn : ‖c‖ ≤ 1 := by
    rw [hc, norm_neg, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg
      (norm_nonneg _)]
    exact div_self_le_one _
  have hca : ‖c • a‖ ≤ 1 := by
    rw [norm_smul]
    calc ‖c‖ * ‖a‖ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  have hval : ((e : M →L[ℂ] ℂ) (c • a)).re = -‖z‖ := by
    rw [map_smul, smul_eq_mul, ← hz, hc]
    rcases eq_or_ne ‖z‖ 0 with h0 | h0
    · rw [h0]; simp
    · have : -(starRingEnd ℂ z / (‖z‖ : ℂ)) * z = -((‖z‖ : ℂ)) := by
        rw [neg_mul, div_mul_eq_mul_div, Complex.conj_mul', pow_two]
        field_simp
      rw [this]; simp
  have h1 := hsep _ hca
  rw [hval] at h1
  have h2 : -‖(e : M →L[ℂ] ℂ)‖ ≤ (ψ e).re := by
    have h3 : ‖ψ e‖ ≤ ‖e‖ := by
      calc ‖ψ e‖ ≤ ‖ψ‖ * ‖e‖ := ψ.le_opNorm e
        _ ≤ 1 * ‖e‖ := by gcongr
        _ = ‖e‖ := one_mul _
    have h4 : -‖ψ e‖ ≤ (ψ e).re := by
      have := Complex.abs_re_le_norm (ψ e)
      rw [abs_le] at this
      linarith [this.1]
    have h5 : ‖e‖ = ‖(e : M →L[ℂ] ℂ)‖ := rfl
    linarith
  linarith

/-- **Kadison ⇒ predual**: every functional on `M_*` is evaluation. -/
theorem exists_ev_eq (ψ : StrongDual ℂ (Pre M)) : ∃ a : M, ev a = ψ := by
  rcases eq_or_ne ψ 0 with h0 | h0
  · exact ⟨0, by rw [h0]; ext f; simp⟩
  have hn : 0 < ‖ψ‖ := norm_pos_iff.mpr h0
  obtain ⟨a, -, ha⟩ := exists_ev_eq_of_norm_le_one ((‖ψ‖⁻¹ : ℂ) • ψ) (by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hn.le,
      inv_mul_cancel₀ hn.ne'])
  refine ⟨(‖ψ‖ : ℂ) • a, ?_⟩
  ext f
  have := congrArg (fun φ : StrongDual ℂ (Pre M) => φ f) ha
  simp only [ev_apply] at this
  simp only [ev_apply, map_smul, smul_eq_mul, this]
  show (‖ψ‖ : ℂ) * ((‖ψ‖ : ℂ)⁻¹ * ψ f) = ψ f
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_mul]

/-- **Kadison ⇒ Sakai**: a (Kadison) von Neumann algebra is, isometrically,
the dual of its predual `M_*`. -/
def predualEquiv : StrongDual ℂ (Pre M) ≃ₗᵢ[ℂ] M :=
  let evL : M →ₗ[ℂ] StrongDual ℂ (Pre M) :=
    { toFun := ev
      map_add' := fun a b => by ext f; simp
      map_smul' := fun c a => by ext f; simp }
  have hinj : Function.Injective evL := by
    intro a b h
    have : ‖ev (a - b)‖ = 0 := by
      have h' : ev (a - b) = ev a - ev b := by ext f; simp
      rw [h', show ev a = ev b from h, sub_self, norm_zero]
    rw [norm_ev] at this
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  let e : M ≃ₗᵢ[ℂ] StrongDual ℂ (Pre M) :=
    { LinearEquiv.ofBijective evL ⟨hinj, fun ψ => exists_ev_eq ψ⟩ with
      norm_map' := norm_ev }
  e.symm

/-- **Kadison ⇒ Mathlib's `WStarAlgebra`** (the half of DECISIONS §3.7 that
`Sakai.vonNeumannAlgebra_of_wStarAlgebra` leaves open): a von Neumann algebra
in the theses' (Kadison) sense has a Banach predual in Mathlib's Sakai sense. -/
theorem wStarAlgebra_of_vonNeumannAlgebra : WStarAlgebra M where
  exists_predual := ⟨Pre M, inferInstance, inferInstance, inferInstance,
    ⟨{ toFun := fun x => star (predualEquiv x)
       invFun := fun m => predualEquiv.symm (star m)
       map_add' := fun x y => by simp [star_add]
       map_smul' := fun c x => by simp [star_smul]
       left_inv := fun x => by simp
       right_inv := fun m => by simp
       norm_map' := fun x => by simp }⟩⟩

end Kadison

section SelfDual

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [VonNeumannAlgebra M]
variable {X : Type w} [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul M X] [CStarModule M X]

/-- The functional `e_{ω,g} = ω ∘ ⟨g, ·⟩` on a Hilbert `M`-module. -/
def efun (ω : Pre M) (g : X) : X →L[ℂ] ℂ :=
  (ω : M →L[ℂ] ℂ).comp (CStarModule.innerSL (A := M) g)

@[simp] theorem efun_apply (ω : Pre M) (g f : X) :
    efun ω g f = (ω : M →L[ℂ] ℂ) (inner M g f) := rfl

theorem norm_efun_le (ω : Pre M) (g : X) : ‖efun ω g‖ ≤ ‖ω‖ * ‖g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
  rw [efun_apply]
  calc ‖(ω : M →L[ℂ] ℂ) (inner M g f)‖ ≤ ‖(ω : M →L[ℂ] ℂ)‖ * ‖(inner M g f : M)‖ :=
        (ω : M →L[ℂ] ℂ).le_opNorm _
    _ ≤ ‖(ω : M →L[ℂ] ℂ)‖ * (‖g‖ * ‖f‖) := by
        gcongr; exact CStarModule.norm_inner_le X
    _ = ‖ω‖ * ‖g‖ * ‖f‖ := by rw [mul_assoc]; rfl

variable (M X) in
/-- The candidate predual: the span of the `e_{ω,g}` in `X*`. -/
def Ep : Submodule ℂ (X →L[ℂ] ℂ) :=
  Submodule.span ℂ (range fun p : Pre M × X => efun p.1 p.2)

theorem efun_mem (ω : Pre M) (g : X) : efun ω g ∈ Ep M X :=
  Submodule.subset_span ⟨(ω, g), rfl⟩

/-- Evaluation `X → (Ep)*`. -/
def evX (x : X) : StrongDual ℂ (Ep M X) :=
  (ContinuousLinearMap.apply ℂ ℂ x).comp (Ep M X).subtypeL

@[simp] theorem evX_apply (x : X) (e : Ep M X) : evX x e = (e : X →L[ℂ] ℂ) x := rfl

theorem norm_evX (x : X) : ‖evX (M := M) x‖ = ‖x‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun e => ?_
    rw [evX_apply, mul_comm]
    exact (e : X →L[ℂ] ℂ).le_opNorm x
  · rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hsq : ‖x‖ ^ 2 ≤ ‖evX (M := M) x‖ * ‖x‖ := by
      rw [CStarModule.norm_sq_eq M]
      refine norm_le_of_forall_predual (fun ω => ?_) (by positivity)
      calc ‖(ω : M →L[ℂ] ℂ) (inner M x x)‖ = ‖evX (M := M) x ⟨efun ω x, efun_mem ω x⟩‖ := rfl
        _ ≤ ‖evX (M := M) x‖ * ‖efun ω x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖evX (M := M) x‖ * (‖ω‖ * ‖x‖) := by gcongr; exact norm_efun_le ω x
        _ = ‖evX (M := M) x‖ * ‖x‖ * ‖ω‖ := by ring
    nlinarith

/-- **A self-dual Hilbert module over a von Neumann algebra has a Banach
predual**: the evaluation `X → (Ep)*` is onto. -/
theorem exists_evX_eq (hX : SelfDual M X) (φ : StrongDual ℂ (Ep M X)) :
    ∃ t : X, evX t = φ := by
  -- for each `g`, the functional `ω ↦ φ(e_{ω,g})` on `M_*`
  let ψ : X → StrongDual ℂ (Pre M) := fun g =>
    LinearMap.mkContinuous
      { toFun := fun ω => φ ⟨efun ω g, efun_mem ω g⟩
        map_add' := fun ω₁ ω₂ => by
          rw [← map_add]; congr 1
        map_smul' := fun c ω => by
          rw [RingHom.id_apply, ← map_smul]; congr 1 }
      (‖φ‖ * ‖g‖) fun ω => by
        calc ‖φ ⟨efun ω g, efun_mem ω g⟩‖ ≤ ‖φ‖ * ‖(⟨efun ω g, efun_mem ω g⟩ : Ep M X)‖ :=
              φ.le_opNorm _
          _ ≤ ‖φ‖ * (‖ω‖ * ‖g‖) := by gcongr; exact norm_efun_le ω g
          _ = ‖φ‖ * ‖g‖ * ‖ω‖ := by ring
  have hψ : ∀ g ω, ψ g ω = φ ⟨efun ω g, efun_mem ω g⟩ := fun _ _ => rfl
  choose τ₀ hτ₀ using fun g => exists_ev_eq (ψ g)
  have hτ : ∀ g (ω : Pre M), (ω : M →L[ℂ] ℂ) (τ₀ g) = φ ⟨efun ω g, efun_mem ω g⟩ :=
    fun g ω => by rw [← hψ, ← hτ₀ g, ev_apply]
  have hadd : ∀ g₁ g₂, τ₀ (g₁ + g₂) = τ₀ g₁ + τ₀ g₂ := fun g₁ g₂ =>
    eq_of_forall_predual fun ω => by
      rw [map_add, hτ, hτ, hτ, ← map_add]; congr 1; ext f
      simp [CStarModule.inner_add_left]
  have hsmul : ∀ (c : ℂ) g, τ₀ (c • g) = starRingEnd ℂ c • τ₀ g := fun c g =>
    eq_of_forall_predual fun ω => by
      rw [map_smul, hτ, hτ, smul_eq_mul, ← smul_eq_mul, ← map_smul]; congr 1; ext f
      simp [CStarModule.inner_smul_left_complex]
  have hmod : ∀ (b : M) g, τ₀ (b • g) = τ₀ g * star b := fun b g =>
    eq_of_forall_predual fun ω => by
      rw [hτ, ← rmul_apply, hτ]; congr 1; ext f
      simp [CStarModule.inner_op_smul_left]
  have hbdd : ∀ g, ‖τ₀ g‖ ≤ ‖φ‖ * ‖g‖ := fun g =>
    norm_le_of_forall_predual (fun ω => by
      rw [hτ]
      calc ‖φ ⟨efun ω g, efun_mem ω g⟩‖ ≤ ‖φ‖ * ‖(⟨efun ω g, efun_mem ω g⟩ : Ep M X)‖ :=
            φ.le_opNorm _
        _ ≤ ‖φ‖ * (‖ω‖ * ‖g‖) := by gcongr; exact norm_efun_le ω g
        _ = ‖φ‖ * ‖g‖ * ‖ω‖ := by ring) (by positivity)
  let τ : X →ₗ[ℂ] M :=
    { toFun := fun g => star (τ₀ g)
      map_add' := fun g₁ g₂ => by rw [hadd, star_add]
      map_smul' := fun c g => by rw [hsmul, star_smul]; simp }
  obtain ⟨t, ht⟩ := hX τ (fun b g => by
      show star (τ₀ (b • g)) = b * star (τ₀ g)
      rw [hmod, star_mul, star_star])
    ⟨‖φ‖, fun g => by
      show ‖star (τ₀ g)‖ ≤ ‖φ‖ * ‖g‖
      rw [norm_star]; exact hbdd g⟩
  have hτt : ∀ g, τ₀ g = inner M g t := fun g => by
    have := ht g
    change star (τ₀ g) = inner M t g at this
    rw [← star_star (τ₀ g), this, CStarModule.star_inner]
  refine ⟨t, ?_⟩
  ext ⟨e, he⟩
  rw [evX_apply]
  induction he using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨⟨ω, g⟩, rfl⟩ := hv
      show efun ω g t = φ ⟨efun ω g, _⟩
      rw [← hτ, hτt, efun_apply]
  | zero =>
      show (0 : X →L[ℂ] ℂ) t = φ 0
      simp
  | add v₁ v₂ h₁ h₂ ih₁ ih₂ =>
      have : (⟨v₁ + v₂, add_mem h₁ h₂⟩ : Ep M X) = ⟨v₁, h₁⟩ + ⟨v₂, h₂⟩ := rfl
      rw [this, map_add, ← ih₁, ← ih₂]
      rfl
  | smul c v h ih =>
      have : (⟨c • v, Submodule.smul_mem _ c h⟩ : Ep M X) = c • ⟨v, h⟩ := rfl
      rw [this, map_smul, ← ih]
      rfl

/-- **A self-dual Hilbert module over a (Kadison) von Neumann algebra is a
dual Banach space**: `X ≅ (Ep)*` isometrically, `Ep` spanned by the
functionals `ω ∘ ⟨g, ·⟩`. -/
def selfDualPredualEquiv (hX : SelfDual M X) : StrongDual ℂ (Ep M X) ≃ₗᵢ[ℂ] X :=
  let evL : X →ₗ[ℂ] StrongDual ℂ (Ep M X) :=
    { toFun := evX
      map_add' := fun a b => by ext f; simp
      map_smul' := fun c a => by ext f; simp }
  have hinj : Function.Injective evL := by
    intro a b h
    have : ‖evX (M := M) (a - b)‖ = 0 := by
      have h' : evX (M := M) (a - b) = evX a - evX b := by ext f; simp
      rw [h', show evX (M := M) a = evX b from h, sub_self, norm_zero]
    rw [norm_evX] at this
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  let e : X ≃ₗᵢ[ℂ] StrongDual ℂ (Ep M X) :=
    { LinearEquiv.ofBijective evL ⟨hinj, fun φ => exists_evX_eq hX φ⟩ with
      norm_map' := norm_evX }
  e.symm

end SelfDual

end Linking

/-! ### FDS 2.2: the converse half of "equivalently [GLR, Prop. 2.15]" -/

section Category

open StarCategory

variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear ℂ C] [StarCategory C]
  [NormedStarCategory C] [CStarCategory C]

/-- **FDS 2.2** (direct_sums.tex:255, Definition), part 3, the converse half of
"equivalently [GLR, Prop. 2.15]": a W*-category in the form `WStarCategory`
(every `End A` a von Neumann algebra, every `A ⟶ B` self dual) is a
W*-category in the print's primary sense — every hom-set has a Banach predual.
The predual of `A ⟶ B` is spanned by the functionals `f ↦ ω(g† ≫ f)`, `ω`
normal on `End B` (`Linking.selfDualPredualEquiv`). -/
theorem homsHavePreduals_of_wStarCategory [WStarCategory C] : HomsHavePreduals C :=
  fun A B => ⟨_, _, _, ⟨Linking.selfDualPredualEquiv (M := End B) (X := A ⟶ B)
    (WStarCategory.selfDual A B)⟩⟩

/-- **FDS 2.2**, "equivalently [GLR, Prop. 2.15]", both directions for
C*-categories in which any two objects embed isometrically in a common object
(e.g. those with orthogonal binary direct sums): the print's predual definition
and `WStarCategory` agree. -/
theorem wStarCategory_iff_homsHavePreduals_of_linking
    (h : ∀ A B : C, ∃ (S : C) (ιA : A ⟶ S) (ιB : B ⟶ S), IsIsometry ιA ∧ IsIsometry ιB) :
    WStarCategory C ↔ HomsHavePreduals C :=
  ⟨fun _ => homsHavePreduals_of_wStarCategory,
    fun hP => WStarCategory.of_homsHavePreduals_of_linking hP h⟩

end Category

end Papers.FDS
