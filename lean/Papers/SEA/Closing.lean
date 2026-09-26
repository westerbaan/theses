/-
Papers/SEA/Closing.lean

Cleanup pass (2026-09-26): SEA rows graded `weaker` that are closed by new
declarations, without touching the committed statements.

* **SEA 16** (`ex:canonical-sea`), the normal clause as printed: for a
  *bounded-directed complete* (monotone complete) C*-algebra `A`, `[0,1]_A` is
  a normal SEA with `a ∘ b = √a b √a` (`bdcNormalSEA`).  `vnNormalSEA`
  (Basic.lean) covered von Neumann algebras only, through the theses' 44VIII
  `ad_normal`, whose proof uses normal functionals.  Here, for a monotone
  complete C*-algebra: conjugation by an *invertible* element is an order
  automorphism of the self-adjoint part, so it preserves least upper bounds
  (`conj_isLUB_of_isUnit`); conjugation by a positive `c` is the limit of
  conjugations by the invertible `c + ε` (`conj_isLUB_of_nonneg`), and the
  error is `O(ε)` in norm; commutation with a supremum goes through the
  unitary `a + i√(1-a²)` as in `commute_dirSup` (`commute_of_isLUB`).
* **SEA 31** (`ex:CX`): `[0,1]_R` for a partially ordered unital ring in the
  standard (Mathlib `IsOrderedRing`) sense, which includes `0 ≤ 1`
  (`intervalEffectMonoid'`); the ring conditions of the print's parenthesis
  plus `0 ≤ 1` are exactly `IsOrderedRing` (`isOrderedRing_iff_sea31`), and
  `0 ≤ 1` cannot be dropped: `ℤ` ordered by equality satisfies the
  parenthesis but `[0,1]` is empty (`sea31_zero_le_one_needed`).
-/
import Papers.SEA.Basic

namespace Papers.SEA

open Theses.B.Eff Filter Topology

universe u

/-! ## SEA 16: monotone complete C*-algebras -/

section BDC

open scoped ComplexStarModule

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem star_units_inv_mul (u : Aˣ) : star ((↑u⁻¹ : A)) * star (u : A) = 1 := by
  rw [← star_mul, Units.mul_inv, star_one]

omit [PartialOrder A] [StarOrderedRing A] in
theorem star_mul_star_units_inv (u : Aˣ) : star (u : A) * star ((↑u⁻¹ : A)) = 1 := by
  rw [← star_mul, Units.inv_mul, star_one]

/-- An upper bound of a non-empty set of self-adjoint elements is
self-adjoint. -/
theorem isSelfAdjoint_of_ub {D : Set A} (hD : ∀ d ∈ D, IsSelfAdjoint d) (hne : D.Nonempty)
    {y : A} (hy : y ∈ upperBounds D) : IsSelfAdjoint y := by
  obtain ⟨d, hd⟩ := hne
  have h1 : IsSelfAdjoint (y - d) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr (hy hd))
  have := h1.add (hD d hd)
  rwa [sub_add_cancel] at this

/-- Conjugation by an invertible element preserves least upper bounds of
self-adjoint elements (it is an order automorphism of the self-adjoint
part). -/
theorem conj_isLUB_of_isUnit {c : A} (hc : IsUnit c) {D : Set (selfAdjoint A)} (hne : D.Nonempty)
    {s : selfAdjoint A} (hs : IsLUB D s) :
    IsLUB ((fun d : selfAdjoint A => star c * (d : A) * c) '' D) (star c * (s : A) * c) := by
  refine ⟨?_, fun y hy => ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact star_left_conjugate_le_conjugate (show (d : A) ≤ s from hs.1 hd) c
  obtain ⟨u, rfl⟩ := hc
  set v : A := ↑u⁻¹ with hv
  have hysa : IsSelfAdjoint y := by
    refine isSelfAdjoint_of_ub ?_ (hne.image _) hy
    rintro _ ⟨d, _, rfl⟩
    exact IsSelfAdjoint.conjugate' d.2 _
  have hw : IsSelfAdjoint (star v * y * v) := IsSelfAdjoint.conjugate' hysa v
  have hub : (⟨star v * y * v, hw⟩ : selfAdjoint A) ∈ upperBounds D := by
    intro d hd
    have h1 : star (u : A) * (d : A) * u ≤ y := hy ⟨d, hd, rfl⟩
    have h2 := star_left_conjugate_le_conjugate h1 v
    have e : star v * (star (u : A) * (d : A) * u) * v = d := by
      calc star v * (star (u : A) * (d : A) * u) * v
          = (star v * star (u : A)) * (d : A) * ((u : A) * v) := by noncomm_ring
        _ = d := by rw [hv, star_units_inv_mul, Units.mul_inv, one_mul, mul_one]
    rw [e] at h2
    exact h2
  have h3 : (s : A) ≤ star v * y * v := hs.2 hub
  have h4 := star_left_conjugate_le_conjugate h3 (u : A)
  have e : star (u : A) * (star v * y * v) * u = y := by
    calc star (u : A) * (star v * y * v) * u
        = (star (u : A) * star v) * y * (v * (u : A)) := by noncomm_ring
      _ = y := by rw [hv, star_mul_star_units_inv, Units.inv_mul, one_mul, mul_one]
  rw [e] at h4
  exact h4

/-- `algebraMap ℝ A` is monotone. -/
theorem algebraMap_mono' {r t : ℝ} (h : r ≤ t) : algebraMap ℝ A r ≤ algebraMap ℝ A t := by
  have h0 : (0 : A) ≤ algebraMap ℝ A (t - r) := by
    rw [Algebra.algebraMap_eq_smul_one]
    have := rsmul_nonneg' (zero_le_one' A) (sub_nonneg.mpr h)
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact this
  rw [map_sub] at h0
  exact sub_nonneg.mp h0

/-- If `x ≤ y + ε K` for all `0 < ε ≤ 1`, then `x ≤ y` (the positive cone
of a C*-algebra is closed). -/
theorem le_of_forall_le_add_algebraMap {x y : A} {K : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → x ≤ y + algebraMap ℝ A (ε * K)) : x ≤ y := by
  have hc : Continuous fun ε : ℝ => y + algebraMap ℝ A (ε * K) :=
    continuous_const.add ((continuous_algebraMap ℝ A).comp (continuous_id.mul continuous_const))
  have ht : Tendsto (fun ε : ℝ => y + algebraMap ℝ A (ε * K)) (𝓝[>] 0) (𝓝 y) := by
    have := hc.tendsto 0
    simp only [zero_mul, map_zero, add_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact h ε hε.1 hε.2

/-- Conjugation by a positive element preserves least upper bounds of
uniformly norm-bounded sets of self-adjoint elements, in any C*-algebra:
`c + ε` is invertible and conjugation by it differs from conjugation by `c`
by `O(ε)` in norm. -/
theorem conj_isLUB_of_nonneg {c : A} (hc : 0 ≤ c) {D : Set (selfAdjoint A)} (hne : D.Nonempty)
    {M : ℝ} (hD : ∀ d ∈ D, ‖(d : A)‖ ≤ M) {s : selfAdjoint A} (hs : IsLUB D s)
    (hsM : ‖(s : A)‖ ≤ M) :
    IsLUB ((fun d : selfAdjoint A => c * (d : A) * c) '' D) (c * (s : A) * c) := by
  have hcsa : IsSelfAdjoint c := IsSelfAdjoint.of_nonneg hc
  refine ⟨?_, fun y hy => ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact hcsa.conjugate_le_conjugate (show (d : A) ≤ s from hs.1 hd)
  obtain ⟨d0, hd0⟩ := hne
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hD d0 hd0)
  set K : ℝ := M * (2 * ‖c‖ + 1) with hK
  -- the perturbation `(c + ε) x (c + ε) - c x c`, of norm `≤ ε K`
  have pert : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ x : A, IsSelfAdjoint x → ‖x‖ ≤ M →
      IsSelfAdjoint ((c + algebraMap ℝ A ε) * x * (c + algebraMap ℝ A ε) - c * x * c) ∧
      ‖(c + algebraMap ℝ A ε) * x * (c + algebraMap ℝ A ε) - c * x * c‖ ≤ ε * K := by
    intro ε hε0 hε1 x hx hxM
    have hr : IsSelfAdjoint (algebraMap ℝ A ε) := by
      exact (IsSelfAdjoint.all ε).algebraMap A
    have hcr : IsSelfAdjoint (c + algebraMap ℝ A ε) := hcsa.add hr
    refine ⟨?_, ?_⟩
    · have h1 := IsSelfAdjoint.conjugate' hx (c + algebraMap ℝ A ε)
      have h2 := IsSelfAdjoint.conjugate' hx c
      rw [hcr.star_eq] at h1
      rw [hcsa.star_eq] at h2
      exact h1.sub h2
    · have e : (c + algebraMap ℝ A ε) * x * (c + algebraMap ℝ A ε) - c * x * c =
          ε • (x * c + c * x) + (ε * ε) • x := by
        rw [Algebra.algebraMap_eq_smul_one]
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add,
          smul_smul]
        abel
      rw [e]
      have hn1 : ‖ε • (x * c + c * x)‖ ≤ ε * (2 * M * ‖c‖) := by
        rw [norm_smul, Real.norm_of_nonneg hε0]
        refine mul_le_mul_of_nonneg_left ?_ hε0
        calc ‖x * c + c * x‖ ≤ ‖x * c‖ + ‖c * x‖ := norm_add_le _ _
          _ ≤ ‖x‖ * ‖c‖ + ‖c‖ * ‖x‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
          _ ≤ M * ‖c‖ + ‖c‖ * M := add_le_add
              (mul_le_mul_of_nonneg_right hxM (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hxM (norm_nonneg _))
          _ = 2 * M * ‖c‖ := by ring
      have hn2 : ‖(ε * ε) • x‖ ≤ ε * M := by
        rw [norm_smul, Real.norm_of_nonneg (mul_nonneg hε0 hε0)]
        calc ε * ε * ‖x‖ ≤ ε * 1 * M :=
              mul_le_mul (mul_le_mul_of_nonneg_left hε1 hε0) hxM (norm_nonneg _) (by positivity)
          _ = ε * M := by ring
      calc ‖ε • (x * c + c * x) + (ε * ε) • x‖ ≤ ‖ε • (x * c + c * x)‖ + ‖(ε * ε) • x‖ :=
            norm_add_le _ _
        _ ≤ ε * (2 * M * ‖c‖) + ε * M := add_le_add hn1 hn2
        _ = ε * K := by rw [hK]; ring
  have hysa : IsSelfAdjoint y := by
    refine isSelfAdjoint_of_ub ?_ (Set.Nonempty.image _ ⟨d0, hd0⟩) hy
    rintro _ ⟨d, _, rfl⟩
    have := IsSelfAdjoint.conjugate' d.2 c
    rwa [hcsa.star_eq] at this
  refine le_of_forall_le_add_algebraMap (K := 2 * K) fun ε hε0 hε1 => ?_
  set cε : A := c + algebraMap ℝ A ε with hcε
  have hr : IsSelfAdjoint (algebraMap ℝ A ε) := by
    exact (IsSelfAdjoint.all ε).algebraMap A
  have hcεsa : IsSelfAdjoint cε := hcsa.add hr
  have hunit : IsUnit cε := by
    refine CStarAlgebra.isUnit_of_le (algebraMap ℝ A ε) ?_ (isStrictlyPositive_algebraMap hε0)
    rw [hcε]
    exact le_add_of_nonneg_left hc
  -- `cε d cε ≤ y + ε K` for `d ∈ D`, so `cε s cε ≤ y + ε K`
  have hub : y + algebraMap ℝ A (ε * K) ∈
      upperBounds ((fun d : selfAdjoint A => star cε * (d : A) * cε) '' D) := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨hzsa, hz⟩ := pert ε hε0.le hε1 d d.2 (hD d hd)
    have h1 : c * (d : A) * c ≤ y := hy ⟨d, hd, rfl⟩
    have h2 := hzsa.le_algebraMap_norm_self
    have h3 : algebraMap ℝ A ‖cε * (d : A) * cε - c * (d : A) * c‖ ≤ algebraMap ℝ A (ε * K) :=
      algebraMap_mono' hz
    show star cε * (d : A) * cε ≤ y + algebraMap ℝ A (ε * K)
    rw [hcεsa.star_eq]
    calc cε * (d : A) * cε = c * (d : A) * c + (cε * (d : A) * cε - c * (d : A) * c) := by abel
      _ ≤ y + algebraMap ℝ A (ε * K) := add_le_add h1 (h2.trans h3)
  have h4 : star cε * (s : A) * cε ≤ y + algebraMap ℝ A (ε * K) :=
    (conj_isLUB_of_isUnit hunit ⟨d0, hd0⟩ hs).2 hub
  rw [hcεsa.star_eq] at h4
  obtain ⟨hzsa, hz⟩ := pert ε hε0.le hε1 s s.2 hsM
  have h5 := hzsa.neg_algebraMap_norm_le_self
  have h6 : algebraMap ℝ A ‖cε * (s : A) * cε - c * (s : A) * c‖ ≤ algebraMap ℝ A (ε * K) :=
    algebraMap_mono' hz
  have e2 : algebraMap ℝ A (ε * (2 * K)) = algebraMap ℝ A (ε * K) + algebraMap ℝ A (ε * K) := by
    rw [← map_add]; ring_nf
  rw [e2]
  have h7 : -(cε * (s : A) * cε - c * (s : A) * c) ≤ algebraMap ℝ A (ε * K) :=
    neg_le.mp (le_trans (neg_le_neg h6) h5)
  calc c * (s : A) * c = cε * (s : A) * cε + -(cε * (s : A) * cε - c * (s : A) * c) := by abel
    _ ≤ (y + algebraMap ℝ A (ε * K)) + algebraMap ℝ A (ε * K) := add_le_add h4 h7
    _ = y + (algebraMap ℝ A (ε * K) + algebraMap ℝ A (ε * K)) := by abel

/-- An element of `[0,1]_A` commuting with every element of a non-empty set
`D` of self-adjoint elements commutes with a least upper bound `t` of `D`, in
any C*-algebra: `u = a + i√(1-a²)` is a unitary commuting with `D`, and
conjugation by the invertible `u` preserves least upper bounds
(`conj_isLUB_of_isUnit`), so `u* t u = t`.  (As `commute_dirSup`, with the
theses' 44VIII replaced by `conj_isLUB_of_isUnit`.) -/
theorem commute_of_isLUB {a : A} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {D : Set (selfAdjoint A)}
    (hne : D.Nonempty) {t : selfAdjoint A} (ht : IsLUB D t)
    (hc : ∀ d ∈ D, Commute a (d : A)) : Commute a (t : A) := by
  have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha0
  have ha2 : a ^ 2 ≤ 1 := by
    have e : sqrtConj a a = a * a := sqrtConj_eq_mul_of_commute ha0 (Commute.refl a)
    rw [sq, ← e]; exact sqrtConj_le_one ha0 ha1 ha1
  have hsq : 0 ≤ 1 - a ^ 2 := sub_nonneg.mpr ha2
  set b : A := CFC.sqrt (1 - a ^ 2) with hbdef
  have hbnn : 0 ≤ b := CFC.sqrt_nonneg _
  have hbsa : IsSelfAdjoint b := .of_nonneg hbnn
  have hbb : b * b = 1 - a ^ 2 := CFC.sqrt_mul_sqrt_self _ hsq
  have hcommb : ∀ x : A, Commute a x → Commute b x := by
    intro x hx
    rw [hbdef, CFC.sqrt_eq_cfc]
    exact Commute.cfc_nnreal ((Commute.one_left x).sub_left (hx.pow_left 2)) NNReal.sqrt
  have hcomm : Commute b a := hcommb a (Commute.refl a)
  set u : A := a + Complex.I • b with hu
  have hRe : (ℜ u : A) = a := by
    rw [hu, map_add, realPart_I_smul, hbsa.imaginaryPart]
    simp [hsa.coe_realPart]
  have hIm : (ℑ u : A) = b := by
    rw [hu, map_add, imaginaryPart_I_smul, hsa.imaginaryPart]
    simp [hbsa.coe_realPart]
  have hn : IsStarNormal u :=
    isStarNormal_iff_commute_realPart_imaginaryPart.mpr (by rw [hRe, hIm]; exact hcomm.symm)
  have huu : u ∈ unitary A := by
    rw [(Theses.A.CStar.unitary_basic_4 u).2 hn, hRe, hIm, sq b, hbb]
    abel
  have hsu : star u * u = 1 := Unitary.star_mul_self_of_mem huu
  have hus : u * star u = 1 := Unitary.mul_star_self_of_mem huu
  have hunit : IsUnit u := ⟨⟨u, star u, hus, hsu⟩, rfl⟩
  have hud : ∀ d ∈ D, Commute u (d : A) := fun d hd =>
    (hc d hd).add_left ((hcommb _ (hc d hd)).smul_left Complex.I)
  have himg : ((fun d : selfAdjoint A => star u * (d : A) * u) '' D) = ((↑) '' D : Set A) := by
    ext x; constructor
    · rintro ⟨d, hd, rfl⟩
      refine ⟨d, hd, ?_⟩
      show (d : A) = star u * d * u
      rw [mul_assoc, ← (hud d hd).eq, ← mul_assoc, hsu, one_mul]
    · rintro ⟨d, hd, rfl⟩
      refine ⟨d, hd, ?_⟩
      show star u * (d : A) * u = d
      rw [mul_assoc, ← (hud d hd).eq, ← mul_assoc, hsu, one_mul]
  have hL1 := conj_isLUB_of_isUnit hunit hne ht
  rw [himg] at hL1
  have hL2 := isLUB_coe_of_isLUB hne ht
  have hconj : star u * (t : A) * u = t := hL1.unique hL2
  have htu : Commute (t : A) u := by
    show (t : A) * u = u * t
    calc (t : A) * u = (u * star u) * t * u := by rw [hus, one_mul]
      _ = u * (star u * t * u) := by noncomm_ring
      _ = u * t := by rw [hconj]
  have htsa : IsSelfAdjoint (t : A) := t.2
  have htus : Commute (t : A) (star u) := by
    have := htu.star_star
    rwa [htsa.star_eq] at this
  have : Commute (t : A) (ℜ u : A) := by
    rw [realPart_apply_coe]
    exact ((htu.add_right htus).smul_right _)
  rw [hRe] at this
  exact this.symm

/-- `A` is **bounded-directed complete** (monotone complete, SEA 13's reading):
every non-empty bounded directed set of self-adjoint elements has a least
upper bound. -/
def BoundedDirectedComplete (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    Prop :=
  ∀ D : Set (selfAdjoint A), D.Nonempty → DirectedOn (· ≤ ·) D → BddAbove D → ∃ s, IsLUB D s

/-- **SEA 16** (`ex:canonical-sea`, second.tex:475, Example), second claim as
printed: if the C*-algebra `A` is bounded-directed complete (for instance a
von Neumann algebra), then `[0,1]_A` is a *normal* SEA with the same
sequential product `a ∘ b = √a b √a` (`cstarSEA`).  No proof printed; ours:
directed completeness is SEA 13 (`sea13_dc_of_bdc`); the product half of S6 is
`conj_isLUB_of_nonneg` for `c = √a` (conjugation by `√a + ε` is an order
automorphism, error `O(ε)`); the commutation half is `commute_of_isLUB`. -/
@[instance_reducible] noncomputable def bdcNormalSEA (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (hbdc : BoundedDirectedComplete A) :
    @NormalSEA (Set.Icc (0 : A) 1) (cstarEA A) := by
  letI := cstarEA A
  letI := cstarSEA A
  have hle_iff : ∀ x y : Set.Icc (0 : A) 1, x ≼ y ↔ (x : A) ≤ y :=
    interval_le_iff 1 zero_le_one
  -- the supremum of a directed `S ⊆ [0,1]_A` is the least upper bound of `saImage S`
  have supEq : ∀ {S : Set (Set.Icc (0 : A) 1)} (hS : EDirected S) {x : Set.Icc (0 : A) 1}
      {s : selfAdjoint A}, IsLUB (saImage S) s → EIsSup S x → (x : A) = s := by
    intro S hS x s hs hx
    obtain ⟨hmem, hsup⟩ := isSup_of_isLUB hS.1 hs
    exact congrArg Subtype.val (hx.unique hsup)
  have hnorm : ∀ z : Set.Icc (0 : A) 1, ‖(z : A)‖ ≤ ‖(1 : A)‖ := fun z =>
    CStarAlgebra.norm_le_norm_of_nonneg_of_le z.2.1 z.2.2
  exact
  { cstarSEA A with
    directedComplete := sea13_dc_of_bdc hbdc
    seq_sup := by
      intro a S x hS hx
      obtain ⟨hne, hdir, hbdd⟩ := saImage_directed hS
      obtain ⟨s, hs⟩ := hbdc _ hne hdir hbdd
      have hxs := supEq hS hs hx
      have hL := conj_isLUB_of_nonneg (CFC.sqrt_nonneg (a : A)) hne (M := ‖(1 : A)‖)
        (by rintro _ ⟨z, _, rfl⟩; exact hnorm z) hs (by rw [← hxs]; exact hnorm x)
      rw [← hxs] at hL
      refine ⟨?_, fun y hy => (hle_iff _ _).mpr (hL.2 ?_)⟩
      · rintro _ ⟨s, hs, rfl⟩
        refine (hle_iff _ _).mpr (hL.1 ⟨⟨s.1, IsSelfAdjoint.of_nonneg s.2.1⟩, ⟨s, hs, rfl⟩, ?_⟩)
        rfl
      · rintro _ ⟨d, ⟨s, hs, rfl⟩, rfl⟩
        have := (hle_iff _ _).mp (hy _ ⟨s, hs, rfl⟩)
        exact this
    comm_sup := by
      intro a S x hS hx hcomm
      obtain ⟨hne, hdir, hbdd⟩ := saImage_directed hS
      obtain ⟨s, hs⟩ := hbdc _ hne hdir hbdd
      have hc : ∀ d ∈ saImage S, Commute (a : A) (d : A) := by
        rintro _ ⟨s, hs, rfl⟩
        exact commute_of_sqrtConj_eq a.2.1 s.2.1 (congrArg Subtype.val (hcomm s hs))
      have := commute_of_isLUB a.2.1 a.2.2 hne hs hc
      rw [← supEq hS hs hx] at this
      exact Subtype.ext (sqrtConj_comm_of_commute a.2.1 x.2.1 this) }

/-- A von Neumann algebra is bounded-directed complete (vn.tex 42I), so
`bdcNormalSEA` recovers `vnNormalSEA`'s case. -/
theorem vonNeumann_boundedDirectedComplete [Theses.VonNeumannAlgebra A] :
    BoundedDirectedComplete A := fun D hne hdir hbdd =>
  Theses.VonNeumannAlgebra.isLUB_of_bddAbove_directed D hne hdir hbdd

end BDC


/-! ## SEA 31: `[0,1]_R` of an ordered unital ring -/

section Interval31

/-- For a ring with a partial order whose positive cone is closed under `+`,
the print's parenthesis ("the sum and product of positive elements are again
positive") together with `0 ≤ 1` is exactly Mathlib's `IsOrderedRing`. -/
theorem isOrderedRing_iff_sea31 (R : Type u) [Ring R] [PartialOrder R] [IsOrderedAddMonoid R] :
    IsOrderedRing R ↔ (0 : R) ≤ 1 ∧ ∀ a b : R, 0 ≤ a → 0 ≤ b → 0 ≤ a * b := by
  constructor
  · intro _
    exact ⟨zero_le_one, fun a b ha hb => mul_nonneg ha hb⟩
  · rintro ⟨h01, hmul⟩
    have : ZeroLEOneClass R := ⟨h01⟩
    exact IsOrderedRing.of_mul_nonneg hmul

/-- **SEA 31** (`ex:CX`, second.tex:852, Example), first sentence, with
"(partially) ordered unital ring" in the standard sense (Mathlib's
`IsOrderedRing`: positives closed under `+` and `·`, and `0 ≤ 1`): the unit
interval `[0,1]_R` is an effect monoid under the ring product.  (That `0 ≤ 1`
cannot be dropped from the print's parenthetical reading is
`sea31_zero_le_one_needed`.) -/
@[instance_reducible] noncomputable def intervalEffectMonoid' (R : Type u) [Ring R] [PartialOrder R]
    [IsOrderedRing R] : EffectMonoid (Set.Icc (0 : R) 1) :=
  intervalEffectMonoid zero_le_one fun _ _ ha hb => mul_nonneg ha hb

/-- `ℤ` ordered by equality: a partially ordered ring in which sums and
products of positive elements are positive, but `0 ≰ 1`. -/
def TrivOrdInt : Type := ℤ

instance : Ring TrivOrdInt := inferInstanceAs (Ring ℤ)

instance : PartialOrder TrivOrdInt where
  le a b := a = b
  le_refl _ := rfl
  le_trans _ _ _ h1 h2 := Eq.trans h1 h2
  le_antisymm _ _ h _ := h

instance : IsOrderedAddMonoid TrivOrdInt where
  add_le_add_left a b h c := by
    change a = b at h
    change a + c = b + c
    rw [h]

/-- **SEA 31**: the hypothesis `0 ≤ 1` of `intervalEffectMonoid` cannot be
dropped when "ordered unital ring" is read as only the print's parenthesis:
in `ℤ` ordered by equality positives are closed under `+` and `·`, yet
`0 ≰ 1`, `[0,1]` is empty, and so carries no effect algebra (which has a
`0`).  Not filed in ERRATA: the standard definition includes `0 ≤ 1`. -/
theorem sea31_zero_le_one_needed :
    (∀ a b : TrivOrdInt, 0 ≤ a → 0 ≤ b → 0 ≤ a * b) ∧ ¬ (0 : TrivOrdInt) ≤ 1 ∧
      IsEmpty (Set.Icc (0 : TrivOrdInt) 1) ∧ IsEmpty (EffectAlgebra (Set.Icc (0 : TrivOrdInt) 1)) := by
  have h01 : ¬ (0 : TrivOrdInt) ≤ 1 := by
    intro h
    change (0 : ℤ) = 1 at h
    exact absurd h (by decide)
  have hE : IsEmpty (Set.Icc (0 : TrivOrdInt) 1) :=
    ⟨fun x => h01 (le_trans x.2.1 x.2.2)⟩
  refine ⟨fun a b ha hb => ?_, h01, hE, ⟨fun e => ?_⟩⟩
  · change (0 : ℤ) = a at ha
    change (0 : ℤ) = b at hb
    change (0 : ℤ) = a * b
    rw [← ha, ← hb]; rfl
  · let _ := e
    exact isEmptyElim (0 : Set.Icc (0 : TrivOrdInt) 1)

end Interval31

end Papers.SEA
