/-
Papers/REC/JBWSummandA.lean

**`JBWExceptionalSummand`, part (A)** (Hanche-Olsen–Størmer 7.2.7's normal half), after
`docs/research/hos727-summand.md` (reviewed; part (A) stands).

Plan (2026-09-26).
* `normalKernel V` (`J_n`): the `x` killed by every *normal* Jordan homomorphism of `V`
  into a von Neumann algebra (Kadison, `Theses.VonNeumannAlgebra`) in `V`'s universe.
  It is a submodule, a Jordan ideal (`y * x`), hereditary (`0 ≤ x ≤ a ∈ J_n`; Jordan
  homomorphisms are positive, `jordanHom_nonneg`) and closed under directed suprema
  (normality: the image of the set is `{0}`).  No norm-closedness is needed.
* Range projections: `r(a) = ⋁ₙ min((n+1)t⁺,1)(a)` with `min((n+1)t⁺,1)(a) ≤ (n+1)a`, so
  `r(a) ∈ J_n` for `0 ≤ a ∈ J_n` (hereditary + directed sups).
* `c := ⋁ F`, `F` = idempotents of `J_n`.  `F` is directed without the review's
  `r(a), r(b) ≤ r(a+b)`: `p ∨ q = r(p+q)` (`sup2_spec`) and `p + q ∈ J_n`.  So `c ∈ J_n`,
  `c` idempotent (`isLUB_idem`).  `σ_e F ⊆ F` (Jordan ideal, `σ_e` multiplicative), so
  `σ_e c = c` for every Peirce reflection and `c` is central (`central_of_Ph`).
* `J_n = cV`: `⊇` by the ideal property; `⊆` (the review's argument): `y = x - cx ∈ J_n`,
  `cy = 0`; `z = y² ∈ J_n`, `p = r(z) ∈ F` so `p ≤ c`, `cp = p`, hence
  `cz = c(zp) = z(cp) = z`, while `cz = y(cy) = 0`; `‖y‖² = ‖z‖ = 0`.
* The product `Φ = (φₓ)ₓ : V → ⊕ₓ 𝔄ₓ = lp 𝔄 ∞` over witnesses `x ∉ J_n` (index
  `{x : V // x ∉ J_n}`, all in universe `v`; each `𝔄ₓ` non-trivial as `φₓ x ≠ 0`, which
  Mathlib's unital `lp` instance needs).  Uniform bound `‖φ v‖ ≤ 3‖v‖` from positivity
  and `‖φ 1‖ ≤ 1` (`φ 1` a projection) — contractivity itself is not needed.
  Normality coordinatewise (`lp_infty_le_iff`), `ker Φ = J_n`.
* `(1-c)V` is JW (`CentralIdem.Corner` of `1 - c`, a JBW-algebra): `Φ` restricted.
* The crux (B) as the named Prop `SpecialKernelNormal` (`J_n ⊆ J`: every Jordan hom into a
  C*-algebra kills `J_n`); `jbwExceptionalSummand_of_specialKernel`; and
  `specialKernelNormal_of_HOS` (REC 52 ⇒ it), so the new Prop is no stronger than REC 52.
-/
import Papers.REC.JBWProj

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace Papers.REC.JBWSummandA

open Theses Theses.B.Eff Theses.A.VN Papers.REC Papers.REC.JBCalc Papers.REC.JBPeirce Papers.REC.JBWProj
open Papers.SEA.JBW
open scoped ENNReal

universe v

noncomputable section

/-! ## 1. The normal kernel `J_n` -/

section Kernel

variable (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]

/-- The **normal kernel** `J_n`: the elements killed by every normal Jordan homomorphism of
`V` into a von Neumann algebra (Kadison's definition) of `V`'s universe. -/
def normalKernel : Submodule ℝ V where
  carrier := {x | ∀ (𝔄 : Type v) [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]
    [Theses.VonNeumannAlgebra 𝔄] (φ : V →ₗ[ℝ] 𝔄), IsJordanHomInto V 𝔄 φ → IsNormalMap φ →
      φ x = 0}
  add_mem' := by
    intro a b ha hb 𝔄 _ _ _ _ φ hJ hN
    rw [map_add, ha 𝔄 φ hJ hN, hb 𝔄 φ hJ hN, add_zero]
  zero_mem' := by
    intro 𝔄 _ _ _ _ φ _ _
    exact map_zero φ
  smul_mem' := by
    intro r a ha 𝔄 _ _ _ _ φ hJ hN
    rw [map_smul, ha 𝔄 φ hJ hN, smul_zero]

variable {V}

theorem mem_normalKernel {x : V} : x ∈ normalKernel V ↔
    ∀ (𝔄 : Type v) [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]
      [Theses.VonNeumannAlgebra 𝔄] (φ : V →ₗ[ℝ] 𝔄), IsJordanHomInto V 𝔄 φ → IsNormalMap φ →
        φ x = 0 := Iff.rfl

/-- `J_n` is a Jordan ideal. -/
theorem nk_mul (y : V) {x : V} (hx : x ∈ normalKernel V) : y * x ∈ normalKernel V := by
  intro 𝔄 _ _ _ _ φ hJ hN
  rw [hJ.2, hx 𝔄 φ hJ hN, mul_zero, zero_mul, add_zero, smul_zero]

/-- `J_n` is closed under non-empty directed suprema. -/
theorem nk_lub {S : Set V} (hS : S ⊆ normalKernel V) (hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) {s : V} (hs : IsLUB S s) : s ∈ normalKernel V := by
  intro 𝔄 _ _ _ _ φ hJ hN
  have h := hN S s hne hdir hs
  have himg : (φ : V → 𝔄) '' S = {0} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hne
      exact ⟨x, hx, hS hx 𝔄 φ hJ hN⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hS hx 𝔄 φ hJ hN
  rw [himg] at h
  exact h.unique isLUB_singleton

variable [hJB : JBAlgebra V]

theorem nk_Ph (e : V) {x : V} (hx : x ∈ normalKernel V) : Ph e x ∈ normalKernel V := by
  rw [Ph_apply]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (nk_mul e hx))
    (Submodule.smul_mem _ _ (nk_mul e (nk_mul e hx)))

theorem nk_refl (e : V) {x : V} (hx : x ∈ normalKernel V) : peirceRefl e x ∈ normalKernel V := by
  rw [peirceRefl_apply]
  exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (nk_Ph e hx))

/-- `J_n` is hereditary: Jordan homomorphisms into C*-algebras are positive. -/
theorem nk_hered {x a : V} (h0 : 0 ≤ x) (hxa : x ≤ a) (ha : a ∈ normalKernel V) :
    x ∈ normalKernel V := by
  intro 𝔄 _ _ _ _ φ hJ hN
  have h1 : 0 ≤ φ x := jordanHom_nonneg hJ h0
  have h2 : 0 ≤ φ (a - x) := jordanHom_nonneg hJ (sub_nonneg.2 hxa)
  rw [map_sub, ha 𝔄 φ hJ hN, zero_sub, neg_nonneg] at h2
  exact le_antisymm h2 h1

end Kernel

/-! ## 2. `J_n = cV` for a central idempotent `c` -/

section Summand

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

/-- Range projections of positive elements of `J_n` lie in `J_n`. -/
theorem rproj_mem {a : V} (ha0 : 0 ≤ a) (ha : a ∈ normalKernel V) :
    sproj (posF a) ∈ normalKernel V := by
  have hg : ∀ t, 0 ≤ posF a t := fun t => le_max_right _ _
  refine nk_lub ?_ (Set.range_nonempty _) (directedOn_range.2 (sseq_mono hg).directed_le)
    (sproj_isLUB hg)
  rintro _ ⟨n, rfl⟩
  refine nk_hered (sseq_nonneg hg n) ?_ (Submodule.smul_mem _ ((n : ℝ) + 1) ha)
  have e : ((n : ℝ) + 1) • a = jbCfc a (((n : ℝ) + 1) • posF a) := by
    rw [jbCfc_smul, jbCfc_posF ha0]
  rw [e, sseq, jbCfc_le_iff]
  intro t
  simp only [sfun_apply, ContinuousMap.smul_apply, smul_eq_mul]
  exact min_le_left _ _

/-- **(A), first half**: `J_n = cV` for a central idempotent `c` (which lies in `J_n`). -/
theorem normalKernel_eq_corner :
    ∃ c : V, c * c = c ∧ (∀ x y : V, c * (x * y) = x * (c * y)) ∧ c ∈ normalKernel V ∧
      ∀ x : V, x ∈ normalKernel V ↔ c * x = x := by
  set F := {e : V | e * e = e ∧ e ∈ normalKernel V} with hFdef
  have h0 : (0 : V) ∈ F := ⟨jb_zero_mul 0, Submodule.zero_mem _⟩
  have hF01 : F ⊆ Set.Icc 0 (ouUnit V) := fun e he => ⟨idem_nonneg he.1, idem_le_one he.1⟩
  have hdir : DirectedOn (· ≤ ·) F := by
    rintro e1 ⟨he1, hk1⟩ e2 ⟨he2, hk2⟩
    obtain ⟨hr, h1, h2, -⟩ := sup2_spec he1 he2
    exact ⟨sup2 e1 e2, ⟨hr, rproj_mem (add_nonneg (idem_nonneg he1) (idem_nonneg he2))
      (Submodule.add_mem _ hk1 hk2)⟩, h1, h2⟩
  obtain ⟨c, hc, hc01⟩ := exists_isLUB_unit hF01 ⟨0, h0⟩ hdir
  have hcc : c * c = c := isLUB_idem (fun e he => he.1) ⟨0, h0⟩ hdir hc hc01.2
  have hcN : c ∈ normalKernel V := nk_lub (fun e he => he.2) ⟨0, h0⟩ hdir hc
  have hfix : ∀ e : V, e * e = e → peirceRefl e c = c := by
    intro e he
    have himg : peirceRefl e '' F ⊆ F := by
      rintro _ ⟨f, ⟨hf, hfN⟩, rfl⟩
      exact ⟨by rw [← peirceRefl_mul he, hf], nk_refl e hfN⟩
    have h1 : peirceRefl e c ≤ c := (refl_isLUB he hc).2 fun x hx => hc.1 (himg hx)
    have h2 := refl_mono he h1
    rw [peirceRefl_peirceRefl he] at h2
    exact le_antisymm h1 h2
  have hPh : ∀ e : V, e * e = e → Ph e c = 0 := by
    intro e he
    have := hfix e he
    rw [peirceRefl_apply, sub_eq_self] at this
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  have hcen := central_of_Ph hPh
  refine ⟨c, hcc, hcen, hcN, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have hcx : c * (c * x) = c * x := by
      have := hcen x c
      rwa [hcc, JBAlgebra.mul_comm x c] at this
    set y := x - c * x with hy
    have hyN : y ∈ normalKernel V := Submodule.sub_mem _ hx (nk_mul c hx)
    have hcy : c * y = 0 := by rw [hy, jb_mul_sub, hcx, sub_self]
    set z := y * y with hz
    have hzN : z ∈ normalKernel V := nk_mul y hyN
    have hz0 : 0 ≤ z := jb_sq_nonneg y
    obtain ⟨hp, hpz, -⟩ := rproj_spec hz0
    have hpN := rproj_mem hz0 hzN
    generalize sproj (posF z) = p at hp hpz hpN
    have hcp : c * p = p := (idem_le_iff hp hcc).1 (hc.1 ⟨hp, hpN⟩)
    have hcz0 : c * z = 0 := by rw [hz, hcen y y, hcy, jb_mul_zero]
    have hczz : c * z = z := by
      calc c * z = c * (z * p) := by rw [JBAlgebra.mul_comm z p, hpz]
        _ = z * (c * p) := hcen z p
        _ = z := by rw [hcp, JBAlgebra.mul_comm, hpz]
    have hz00 : z = 0 := hczz.symm.trans hcz0
    have hn : ousNorm V y ^ 2 = 0 := by
      rw [← jb_norm_mul_self, ← hz, hz00, ousNorm_zero']
    have hy0 : y = 0 := IsOUS.norm_eq_zero _ (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hn)
    exact (sub_eq_zero.1 hy0).symm
  · rw [← hx, JBAlgebra.mul_comm]
    exact nk_mul x hcN

end Summand

/-! ## 3. Jordan homomorphisms are bounded; the product map -/

section Bound

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJB : JBAlgebra V]

/-- **Jordan homomorphisms into C*-algebras are bounded**, uniformly: `‖φ v‖ ≤ 3‖v‖`
(`φ` is positive, and `φ 1` is a projection, so `‖φ 1‖ ≤ 1`; the non-unital case). -/
theorem jordanHom_norm_le {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]
    {φ : V →ₗ[ℝ] 𝔄} (hφ : IsJordanHomInto V 𝔄 φ) (v : V) : ‖φ v‖ ≤ 3 * ousNorm V v := by
  have hpp : φ (ouUnit V) * φ (ouUnit V) = φ (ouUnit V) := by
    have h := hφ.2 (ouUnit V) (ouUnit V)
    rw [JBAlgebra.mul_one, ← two_smul ℝ (φ (ouUnit V) * φ (ouUnit V)), _root_.smul_smul,
      show (2⁻¹ * 2 : ℝ) = 1 by norm_num, one_smul] at h
    exact h.symm
  set p := φ (ouUnit V) with hp
  have hpn : ‖p‖ ≤ 1 := by
    have h := CStarRing.norm_star_mul_self (x := p)
    rw [(hφ.1 (ouUnit V)).star_eq, hpp] at h
    nlinarith [norm_nonneg p]
  set n := ousNorm V v with hn
  obtain ⟨hl, hu⟩ := ousNorm_bounds_le v
  have hn0 : 0 ≤ n := ousNorm_nonneg_rc v
  have a1 : 0 ≤ φ v + n • p := by
    have := jordanHom_nonneg hφ (show 0 ≤ v + n • ouUnit V by
      rw [← sub_neg_eq_add]; exact sub_nonneg.2 hl)
    rwa [map_add, map_smul] at this
  have a2 : φ v + n • p ≤ (2 * n) • p := by
    have := jordanHom_nonneg hφ (show 0 ≤ (2 * n) • ouUnit V - (v + n • ouUnit V) by
      rw [sub_nonneg, two_mul, add_smul]; exact add_le_add hu le_rfl)
    rwa [map_sub, map_add, map_smul, map_smul, sub_nonneg] at this
  have a3 := CStarAlgebra.norm_le_norm_of_nonneg_of_le a1 a2
  rw [norm_smul, Real.norm_of_nonneg (by positivity)] at a3
  have a4 : ‖n • p‖ ≤ n := by
    rw [norm_smul, Real.norm_of_nonneg hn0]; nlinarith [norm_nonneg p]
  calc ‖φ v‖ = ‖(φ v + n • p) - n • p‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖φ v + n • p‖ + ‖n • p‖ := norm_sub_le _ _
    _ ≤ 3 * n := by nlinarith [norm_nonneg p]

end Bound

section Prod

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJB : JBAlgebra V]
variable {ι : Type v} {𝔄 : ι → Type v} [∀ i, CStarAlgebra (𝔄 i)] [∀ i, Nontrivial (𝔄 i)]
  [∀ i, PartialOrder (𝔄 i)] [∀ i, StarOrderedRing (𝔄 i)]
  (φ : ∀ i, V →ₗ[ℝ] 𝔄 i) (hφ : ∀ i, IsJordanHomInto V (𝔄 i) (φ i))

/-- The **product** `Φ = (φᵢ)ᵢ : V → ⊕ᵢ 𝔄ᵢ = lp 𝔄 ∞` of a family of Jordan homomorphisms. -/
def prodMap : V →ₗ[ℝ] lp 𝔄 ∞ where
  toFun v := ⟨fun i => φ i v, memℓp_infty ⟨3 * ousNorm V v, by
    rintro _ ⟨i, rfl⟩; exact jordanHom_norm_le (hφ i) v⟩⟩
  map_add' a b := by
    apply lp.ext; funext i
    rw [lp.coeFn_add]
    exact map_add (φ i) a b
  map_smul' r a := by
    apply lp.ext; funext i
    exact map_smul (φ i) r a

theorem prodMap_apply (v : V) (i : ι) : (prodMap φ hφ v : ∀ i, 𝔄 i) i = φ i v := rfl

theorem prodMap_jordan : IsJordanHomInto V (lp 𝔄 ∞) (prodMap φ hφ) := by
  refine ⟨fun a => ?_, fun a b => ?_⟩
  · apply lp.ext; funext i
    rw [lp.coeFn_star]
    exact (hφ i).1 a
  · apply lp.ext; funext i
    show φ i (a * b) = _
    rw [(hφ i).2]
    rfl

theorem prodMap_normal (hN : ∀ i, IsNormalMap (φ i)) : IsNormalMap (prodMap φ hφ) := by
  intro S s hne hdir hs
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [lp_infty_le_iff]
    intro i
    exact ((hN i) S s hne hdir hs).1 ⟨x, hx, rfl⟩
  · rw [lp_infty_le_iff]
    intro i
    refine ((hN i) S s hne hdir hs).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (lp_infty_le_iff _ _).1 (hu ⟨x, hx, rfl⟩) i

end Prod

/-! ## 4. A normal Jordan homomorphism with kernel exactly `J_n`; `(1-c)V` is JW -/

section JW

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJB : JBAlgebra V]

/-- **(A), second half**: one normal Jordan homomorphism `Φ` of `V` into a von Neumann
algebra (the product over witnesses `x ∉ J_n`) has kernel exactly `J_n`. -/
theorem exists_normal_hom_ker :
    ∃ (𝔅 : Type v) (_ : CStarAlgebra 𝔅) (_ : PartialOrder 𝔅) (_ : StarOrderedRing 𝔅)
      (_ : Theses.VonNeumannAlgebra 𝔅) (Φ : V →ₗ[ℝ] 𝔅),
      IsJordanHomInto V 𝔅 Φ ∧ IsNormalMap Φ ∧ ∀ x, Φ x = 0 ↔ x ∈ normalKernel V := by
  have hwit : ∀ x : {x : V // x ∉ normalKernel V}, ∃ (𝔄 : Type v) (_ : CStarAlgebra 𝔄)
      (_ : PartialOrder 𝔄) (_ : StarOrderedRing 𝔄) (_ : Theses.VonNeumannAlgebra 𝔄)
      (φ : V →ₗ[ℝ] 𝔄), IsJordanHomInto V 𝔄 φ ∧ IsNormalMap φ ∧ φ x.1 ≠ 0 := by
    intro x
    by_contra h
    apply x.2
    intro 𝔄 _ _ _ _ φ hJ hN
    by_contra h'
    exact h ⟨𝔄, ‹_›, ‹_›, ‹_›, ‹_›, φ, hJ, hN, h'⟩
  choose 𝔄 i1 i2 i3 i4 φ hJ hN hne using hwit
  have : ∀ x, Nontrivial (𝔄 x) := fun x => ⟨⟨_, _, hne x⟩⟩
  refine ⟨lp 𝔄 ∞, inferInstance, inferInstance, inferInstance, vonNeumannAlgebra_lp_infty,
    prodMap φ hJ, prodMap_jordan φ hJ, prodMap_normal φ hJ hN, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra hx
    have := congrArg (fun w : lp 𝔄 ∞ => (w : ∀ i, 𝔄 i) ⟨x, hx⟩) h
    simp only [lp.coeFn_zero, Pi.zero_apply] at this
    exact hne ⟨x, hx⟩ this
  · apply lp.ext; funext i
    rw [lp.coeFn_zero]
    exact h (𝔄 i) (φ i) (hJ i) (hN i)

end JW

section JWCorner

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

/-- **(A)**: `J_n = cV` for a central idempotent `c`, and the complementary summand
`(1-c)V` (a JBW-algebra, `CentralIdem.Corner`) is a JW-algebra (REC 50 as rendered in
`IsJWAlgebra`: an injective normal Jordan homomorphism into a von Neumann algebra). -/
theorem normalKernel_summand_isJW :
    ∃ e : Papers.SEA.JBW.CentralIdem V, (∀ x, x ∈ normalKernel V ↔ e.c * x = x) ∧
      IsJWAlgebra e.compl.Corner := by
  obtain ⟨c, hcc, hcen, -, hker⟩ := normalKernel_eq_corner (V := V)
  obtain ⟨𝔅, i1, i2, i3, i4, Φ, hΦJ, hΦN, hΦker⟩ := exists_normal_hom_ker (V := V)
  set e : Papers.SEA.JBW.CentralIdem V := ⟨c, hcc, hcen⟩
  refine ⟨e, hker, 𝔅, i1, i2, i3, i4, Φ ∘ₗ e.compl.sub.subtype,
    ⟨fun a => hΦJ.1 a.1, fun a b => hΦJ.2 a.1 b.1⟩, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
    have h1 : w.1 ∈ normalKernel V := (hΦker _).1 hw
    rw [hker] at h1
    have h2 := e.compl.cx w
    rw [CentralIdem.compl_mul, h1, sub_self] at h2
    exact Subtype.ext h2.symm
  · intro S s hne hdir hs
    have hv := CentralIdem.isLUB_val e.compl hne hs
    have hdir' : DirectedOn (· ≤ ·) (Subtype.val '' S) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨d, hd, had, hbd⟩ := hdir a ha b hb
      exact ⟨d.1, ⟨d, hd, rfl⟩, had, hbd⟩
    have := hΦN _ _ (hne.image _) hdir' hv
    rwa [Set.image_image] at this

end JWCorner

/-! ## 5. The crux (B) as a named Prop; `JBWExceptionalSummand` from it -/

/-- **The remaining input (B)** of `JBWExceptionalSummand` (H-O–S 7.2.7's "`cM` is purely
exceptional"): in a JBW-algebra, whatever every *normal* Jordan homomorphism into a von
Neumann algebra kills (`J_n = cV`, part (A)), every Jordan homomorphism into a C*-algebra
kills.  Equivalently: the special kernel is `J_n`. -/
def SpecialKernelNormal : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V],
    JBWAlgebra V → ∀ x : V, x ∈ normalKernel V →
      ∀ (𝔅 : Type v) [CStarAlgebra 𝔅] (ψ : V →ₗ[ℝ] 𝔅), IsJordanHomInto V 𝔅 ψ → ψ x = 0

/-- **`JBWExceptionalSummand` from (A) and the single named input (B)**: with `c` from
`normalKernel_eq_corner`, `c = 0` makes the product map `Φ` injective (JW), and `c ≠ 0`
gives the summand, killed by every Jordan homomorphism by (B). -/
theorem jbwExceptionalSummand_of_specialKernel (h : SpecialKernelNormal.{v}) :
    JBWExceptionalSummand.{v} := by
  intro V _ _ _ _ _ hV
  obtain ⟨c, hcc, hcen, -, hker⟩ := normalKernel_eq_corner (V := V)
  by_cases hc0 : c = 0
  · left
    obtain ⟨𝔅, i1, i2, i3, i4, Φ, hΦJ, hΦN, hΦker⟩ := exists_normal_hom_ker (V := V)
    refine ⟨𝔅, i1, i2, i3, i4, Φ, hΦJ, fun x y hxy => ?_, hΦN⟩
    have h1 : x - y ∈ normalKernel V := (hΦker _).1 (by rw [map_sub, hxy, sub_self])
    rw [hker, hc0, jb_zero_mul] at h1
    exact sub_eq_zero.1 h1.symm
  · exact Or.inr ⟨c, hc0, hcc, hcen, fun 𝔅 _ ψ hψ x hx => h V hV x ((hker x).2 hx) 𝔅 ψ hψ⟩

/-- REC 52 (`HancheOlsenStormerDecomposition`) implies (B): the new named input is no
stronger than the one it replaces. -/
theorem specialKernelNormal_of_HOS (h : HancheOlsenStormerDecomposition.{v}) :
    SpecialKernelNormal.{v} := by
  intro V _ _ _ _ _ hV x hx 𝔅 _ ψ hψ
  obtain ⟨c, -, -, ⟨𝔄, i1, i2, i3, i4, φ, hφJ, hφN, hker⟩, hvan⟩ := h V hV
  exact hvan 𝔅 ψ hψ x ((hker x).1 (hx 𝔄 φ hφJ hφN))

end

end Papers.REC.JBWSummandA

#print axioms Papers.REC.JBWSummandA.normalKernel_eq_corner
#print axioms Papers.REC.JBWSummandA.exists_normal_hom_ker
#print axioms Papers.REC.JBWSummandA.normalKernel_summand_isJW
#print axioms Papers.REC.JBWSummandA.jbwExceptionalSummand_of_specialKernel
#print axioms Papers.REC.JBWSummandA.specialKernelNormal_of_HOS
