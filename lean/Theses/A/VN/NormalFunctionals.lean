/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 2: Von Neumann Algebras — vn.tex, lines
6231–7332.

  §Normal Functionals
    Ultraweak Boundedness  (parsecs 860–870: positivity criterion, extreme
                            points of the unit ball, polar decomposition of
                            functionals, the predual, uniform boundedness)
    Ultraweak Permanence   (parsecs 880–900: relative suprema of
                            projections, the double commutant theorem,
                            representation of normal functionals as sums of
                            vector functionals, extension of normal
                            functionals, centre separating collections)

Statements only; every proof is `sorry`.  See `Theses/A/VN/Basic.lean` for
the topologies, and `Theses/A/VN/Projections.lean` for `ceil`, `carrier`,
`cceil`, `commutant` and `projSup`.
-/
import Theses.A.VN.Division
import Theses.A.CStar.Matrices

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra ENNReal
open Filter Topology Theses Theses.A.CStar

universe u

namespace Theses.A.VN

variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-! ## Parsec 860: ultraweak boundedness

**85I** (vn.tex:6233) and **86I** (vn.tex:6259): overview — nothing to
formalize. -/

/-- `(y + ziz)*(y + zi) = y² + z²` for self-adjoint `y` and real `z`; the
computation behind the trick in the proof of **86II** (vn.tex:6310). -/
private theorem pfc_aux (y : A) (hy : IsSelfAdjoint y) (z : ℝ) :
    star (y + ((z * Complex.I)) • (1 : A)) * (y + ((z * Complex.I)) • (1 : A))
      = y * y + ((z ^ 2 : ℝ) : ℂ) • (1 : A) := by
  simp [hy.star_eq, smul_smul, mul_add, add_mul]
  ring_nf
  simp [Complex.I_sq]

/-- The normalized case (`f(1) = 1`, `‖f‖ ≤ 1`) of the hard direction of
**86II** (vn.tex:6300–6318): a unital contraction is positive on `[0,1]`. -/
private theorem pfc_key (g : A →L[ℂ] ℂ) (hg1 : g 1 = 1) (hgn : ‖g‖ ≤ 1)
    (b : A) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ g b := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact absurd (hg1 ▸ congrArg g (Subsingleton.elim (1 : A) 0) ▸ g.map_zero)
      (by norm_num)
  have hbsa : IsSelfAdjoint b := .of_nonneg hb0
  set r : ℝ := (g b).re with hr
  set t : ℝ := (g b).im with ht
  set y : A := b - (r : ℂ) • (1 : A) with hy
  have hysa : IsSelfAdjoint y := by
    simp [hy, IsSelfAdjoint, star_sub, hbsa.star_eq]
  -- the author's trick: the family `bₙ := (b - ℜ f(b)) + n i ℑ f(b)`
  have hkey : ∀ n : ℕ, ((2 * n + 1 : ℝ)) * t ^ 2 ≤ ‖y‖ ^ 2 := by
    intro n
    set z : ℝ := n * t with hz
    set bn : A := y + ((z * Complex.I)) • (1 : A) with hbn
    have hgbn : g bn = ((n + 1 : ℝ) * t : ℝ) * Complex.I := by
      simp only [hbn, hy, map_add, map_sub, map_smul, hg1, smul_eq_mul, mul_one]
      refine Complex.ext ?_ ?_ <;> simp [hr, ht, hz] <;> ring
    have hnorm2 : ‖bn‖ ^ 2 ≤ ‖y‖ ^ 2 + z ^ 2 := by
      have h1 : ‖bn‖ ^ 2 = ‖star bn * bn‖ := by
        rw [CStarRing.norm_star_mul_self]; ring
      rw [h1, pfc_aux y hysa z]
      calc ‖y * y + ((z ^ 2 : ℝ) : ℂ) • (1 : A)‖
          ≤ ‖y * y‖ + ‖((z ^ 2 : ℝ) : ℂ) • (1 : A)‖ := norm_add_le _ _
        _ ≤ ‖y‖ ^ 2 + z ^ 2 := by
            gcongr
            · rw [sq]; exact norm_mul_le _ _
            · simp [norm_smul]
    have hle : ‖g bn‖ ≤ ‖bn‖ := by
      calc ‖g bn‖ ≤ ‖g‖ * ‖bn‖ := g.le_opNorm bn
        _ ≤ 1 * ‖bn‖ := by gcongr
        _ = ‖bn‖ := one_mul _
    have hgn2 : ‖g bn‖ = ((n : ℝ) + 1) * |t| := by
      rw [hgbn, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    have hz2 : z ^ 2 = (n : ℝ) ^ 2 * t ^ 2 := by rw [hz]; ring
    have hle' : ((n : ℝ) + 1) * |t| ≤ ‖bn‖ := hgn2 ▸ hle
    have hsq : (((n : ℝ) + 1) * |t|) ^ 2 ≤ ‖bn‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hle' 2
    rw [mul_pow, sq_abs] at hsq
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have ht0 : t = 0 := by
    by_contra htne
    have ht2 : 0 < t ^ 2 := by positivity
    obtain ⟨n, hn⟩ := exists_nat_gt (‖y‖ ^ 2 / t ^ 2)
    have hk := hkey n
    rw [div_lt_iff₀ ht2] at hn
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hgbr : g b = (r : ℂ) := by
    refine Complex.ext ?_ ?_ <;> simp [hr, ← ht, ht0]
  -- `‖1 - g(b)‖ = ‖g(1 - b)‖ ≤ 1` forces `ℜ g(b) ≥ 0`
  have h1b : (0 : A) ≤ 1 - b := sub_nonneg.mpr hb1
  have h1b1 : ‖(1 : A) - b‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ h1b).mpr (sub_le_self 1 hb0)
  have hbound : ‖(1 : ℂ) - (r : ℂ)‖ ≤ 1 := by
    have hop := g.le_opNorm ((1 : A) - b)
    rw [map_sub, hg1, hgbr] at hop
    calc ‖(1 : ℂ) - (r : ℂ)‖ ≤ ‖g‖ * ‖(1 : A) - b‖ := hop
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  have hr0 : 0 ≤ r := by
    rw [show (1 : ℂ) - (r : ℂ) = ((1 - r : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs] at hbound
    cases abs_le.mp hbound with
    | intro h1 _ => linarith
  rw [hgbr]
  simpa [Complex.le_def] using hr0

/-- **86II** (`positive-functional-criterion`, vn.tex:6265, Lemma): a
(bounded) linear functional `f` on a C*-algebra is positive iff
`‖f‖ ≤ f(1)`. -/
theorem positive_functional_criterion (f : A →L[ℂ] ℂ) :
    (∀ a : A, 0 ≤ a → 0 ≤ f a) ↔ ((f 1).im = 0 ∧ ‖f‖ ≤ (f 1).re) := by
  constructor
  · -- `f` positive ⟹ `‖f‖ ≤ f(1)`; by `cp-commutative` + `cp-russo-dye`
    intro hpos
    have h1 : (0 : ℂ) ≤ f 1 := hpos 1 zero_le_one
    refine ⟨((Complex.le_def.mp h1).2).symm, ?_⟩
    have hre : (0 : ℝ) ≤ (f 1).re := (Complex.le_def.mp h1).1
    have hnf : ‖f 1‖ = (f 1).re := (Complex.re_eq_norm.mpr h1).symm
    refine ContinuousLinearMap.opNorm_le_bound _ hre fun a => ?_
    calc ‖f a‖ ≤ ‖f 1‖ * ‖a‖ :=
          cp_russo_dye f.toLinearMap (cp_commutative_cod _ hpos) a
      _ = (f 1).re * ‖a‖ := by rw [hnf]
  · -- `‖f‖ ≤ f(1)` ⟹ `f` positive; normalize and apply `pfc_key`
    rintro ⟨him, hnorm⟩ a ha
    set c : ℝ := (f 1).re with hc
    have hc0 : (0 : ℝ) ≤ c := le_trans (norm_nonneg f) hnorm
    rcases eq_or_lt_of_le hc0 with hce | hcp
    · have hz : ‖f‖ = 0 := le_antisymm (hce ▸ hnorm) (norm_nonneg f)
      simp [norm_eq_zero.mp hz]
    · have hf1 : f 1 = (c : ℂ) := Complex.ext (by simp [hc]) (by simp [him])
      set g : A →L[ℂ] ℂ := (c⁻¹ : ℂ) • f with hg
      have hg1 : g 1 = 1 := by
        rw [hg]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hf1]
        field_simp
      have hgn : ‖g‖ ≤ 1 := by
        rw [hg, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hc0, inv_mul_le_one₀ hcp]
        exact hnorm
      have hfg : ∀ x : A, f x = (c : ℂ) * g x := by
        intro x
        rw [hg]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
        field_simp
      rcases eq_or_ne a 0 with rfl | hane
      · simp
      have hna : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr hane
      set b : A := ((‖a‖⁻¹ : ℝ) : ℂ) • a with hb
      have hb0 : 0 ≤ b := cstar_positive_1 a ha _ (by positivity)
      have hbn : ‖b‖ = 1 := by
        rw [hb, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖a‖⁻¹)]
        field_simp
      have hb1 : b ≤ 1 :=
        (CStarAlgebra.norm_le_one_iff_of_nonneg b hb0).mp hbn.le
      have hgb : 0 ≤ g b := pfc_key g hg1 hgn b hb0 hb1
      have hga : g a = (‖a‖ : ℂ) * g b := by
        rw [hb, map_smul, smul_eq_mul, ← mul_assoc,
          show ((‖a‖ : ℂ)) * (((‖a‖⁻¹ : ℝ)) : ℂ) = 1 by
            push_cast; field_simp, one_mul]
      rw [hfg a, hga]
      have hcc : (0 : ℂ) ≤ (c : ℂ) := by simpa [Complex.le_def] using hc0
      have hnn : (0 : ℂ) ≤ (‖a‖ : ℂ) := by
        simp [Complex.le_def, hna.le]
      exact mul_nonneg hcc (mul_nonneg hnn hgb)

/-- `‖u f(u*u)‖² = ‖f(u*u) u*u f(u*u)‖`, the C*-identity computation used in
the proof of **86VI**. -/
private theorem vbep_norm (u : A) (h : ℝ → ℝ) (hc : Continuous h) :
    ‖u * cfc h (star u * u)‖ * ‖u * cfc h (star u * u)‖
      = ‖cfc (fun t => h t * t * h t) (star u * u)‖ := by
  have hp0 : (0 : A) ≤ star u * u := star_mul_self_nonneg u
  have hpsa : IsSelfAdjoint (star u * u) := .of_nonneg hp0
  have hbsa : IsSelfAdjoint (cfc h (star u * u)) := cfc_predicate h _
  rw [← CStarRing.norm_star_mul_self]
  congr 1
  rw [star_mul, hbsa.star_eq, mul_assoc, ← mul_assoc (star u), ← mul_assoc,
    cfc_mul (fun t : ℝ => h t * t) h (star u * u)
      (by fun_prop) hc.continuousOn,
    cfc_mul h (fun t : ℝ => t) (star u * u) hc.continuousOn (by fun_prop),
    cfc_id' (R := ℝ) (a := star u * u) hpsa]

/-- **86VI** (`vn-ball-extreme-point`, vn.tex:6320, Lemma): an extreme
point `u` of the unit ball of a C*-algebra is a partial isometry (i.e.
`u*u` is a projection) with `(uu*)^⊥ A (u*u)^⊥ = {0}`.  (**86VII**,
Remark: the converse also holds but is not needed — not converted.) -/
theorem vn_ball_extreme_point (u : A)
    (hu : u ∈ Set.extremePoints ℝ (Metric.closedBall (0 : A) 1)) :
    IsStarProjection (star u * u) ∧
      ∀ a : A, (1 - u * star u) * a * (1 - star u * u) = 0 := by
  have hu1 : ‖u‖ ≤ 1 := by simpa using hu.1
  have hext : ∀ v w : A, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 → v + w = u + u → v = u := by
    intro v w hv hw hvw
    refine hu.2 (mem_closedBall_zero_iff.mpr hv) (mem_closedBall_zero_iff.mpr hw)
      ⟨2⁻¹, 2⁻¹, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [← smul_add, hvw, ← two_smul ℝ u, smul_smul]
    norm_num
  set p : A := star u * u with hp
  have hp0 : (0 : A) ≤ p := star_mul_self_nonneg u
  have hpsa : IsSelfAdjoint p := .of_nonneg hp0
  have hpn : ‖p‖ ≤ 1 := by
    rw [hp, CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg u]
  have hspec01 : ∀ t ∈ spectrum ℝ p, 0 ≤ t ∧ t ≤ 1 := by
    intro t htp
    have h0 := spectrum_nonneg_of_nonneg hp0 htp
    refine ⟨h0, ?_⟩
    rcases subsingleton_or_nontrivial A with hA | hA
    · exact absurd htp (by simp)
    · have hn := spectrum.norm_le_norm_of_mem htp
      rw [Real.norm_eq_abs, abs_of_nonneg h0] at hn
      linarith
  -- Part 1: `u*u` is a projection
  have hpp : p * p = p := by
    by_contra hne
    rcases subsingleton_or_nontrivial A with hA | hA
    · exact hne (Subsingleton.elim _ _)
    have hex : ∃ l ∈ spectrum ℝ p, l ≠ 0 ∧ l ≠ 1 := by
      by_contra hall
      push_neg at hall
      refine hne ?_
      have hsq : (spectrum ℝ p).EqOn (fun t : ℝ => t * t) (fun t : ℝ => t) := by
        intro x hx
        rcases eq_or_ne x 0 with h | h
        · simp [h]
        · simp only [hall x hx h]; norm_num
      calc p * p = cfc (fun t : ℝ => t * t) p := by
            rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) p (by fun_prop) (by fun_prop),
              cfc_id' (R := ℝ) (a := p) hpsa]
        _ = cfc (fun t : ℝ => t) p := cfc_congr hsq
        _ = p := cfc_id' (R := ℝ) (a := p) hpsa
    obtain ⟨l, hl, hl0, hl1⟩ := hex
    have hlnn : 0 ≤ l := (hspec01 l hl).1
    have hlpos : 0 < l := hlnn.lt_of_ne (Ne.symm hl0)
    have hllt : l < 1 := (hspec01 l hl).2.lt_of_ne hl1
    set m : ℝ := (1 + l) / 2 with hm
    have hm1 : m < 1 := by rw [hm]; linarith
    have hm0 : 0 < m := by rw [hm]; linarith
    set rr : ℝ := min (l / 2) ((1 - l) / 2) with hrr
    have hrpos : 0 < rr := lt_min (by linarith) (by linarith)
    set ε : ℝ := (1 - m) / 2 with he
    have hepos : 0 < ε := by rw [he]; linarith
    have heps1 : ε < 1 := by rw [he]; linarith
    set g : ℝ → ℝ := fun t => ε * max 0 (1 - |t - l| / rr) with hg
    have hgc : Continuous g := by fun_prop
    have hg0 : ∀ t, 0 ≤ g t := fun t => mul_nonneg hepos.le (le_max_left _ _)
    have hgle : ∀ t, g t ≤ ε := by
      intro t
      have h1 : max 0 (1 - |t - l| / rr) ≤ 1 :=
        max_le (by norm_num)
          (by have : 0 ≤ |t - l| / rr := by positivity
              linarith)
      nlinarith [hepos.le]
    have hgl : g l = ε := by simp [hg]
    have hgsupp : ∀ t, g t ≠ 0 → |t - l| < rr := by
      intro t ht
      by_contra hcon
      push_neg at hcon
      refine ht ?_
      have h1 : 1 - |t - l| / rr ≤ 0 := by
        have : 1 ≤ |t - l| / rr := (one_le_div hrpos).mpr hcon
        linarith
      simp [hg, max_eq_left h1]
    have hkey : ∀ t, 0 ≤ t → t ≤ 1 → t * ((1 + g t) * (1 + g t)) ≤ 1 := by
      intro t ht0 ht1
      rcases eq_or_ne (g t) 0 with h | h
      · rw [h]; simpa using ht1
      · have hlt := abs_lt.mp (hgsupp t h)
        have htm : t ≤ m := by
          have h2 : rr ≤ (1 - l) / 2 := min_le_right _ _
          rw [hm]; linarith [hlt.2]
        have hge := hgle t
        have hg0t := hg0 t
        have h1 : (1 + g t) * (1 + g t) ≤ (1 + ε) * (1 + ε) := by nlinarith
        have h2 : t * ((1 + g t) * (1 + g t)) ≤ m * ((1 + ε) * (1 + ε)) := by
          nlinarith [hepos.le]
        have h3 : m * ((1 + ε) * (1 + ε)) ≤ 1 := by
          rw [he]; nlinarith [sq_nonneg (m - 1)]
        linarith
    set a : A := cfc g p with ha
    -- `‖u(1 ± a)‖ ≤ 1`
    have hplus : cfc (fun t : ℝ => 1 + g t) p = 1 + a := by
      rw [cfc_const_add (1 : ℝ) g p hgc.continuousOn hpsa, map_one, ha]
    have hminus : cfc (fun t : ℝ => 1 - g t) p = 1 - a := by
      rw [cfc_sub (fun _ : ℝ => (1 : ℝ)) g p continuousOn_const hgc.continuousOn,
        cfc_const_one ℝ (a := p) hpsa, ha]
    have hn1 : ‖u * (1 + a)‖ ≤ 1 := by
      have hh := vbep_norm u (fun t : ℝ => 1 + g t) (by fun_prop)
      rw [← hp, hplus] at hh
      have hb : ‖cfc (fun t : ℝ => (1 + g t) * t * (1 + g t)) p‖ ≤ 1 := by
        refine norm_cfc_le zero_le_one fun t htp => ?_
        obtain ⟨ht0, ht1⟩ := hspec01 t htp
        have hgt := hg0 t
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc (1 + g t) * t * (1 + g t) = t * ((1 + g t) * (1 + g t)) := by ring
          _ ≤ 1 := hkey t ht0 ht1
      nlinarith [norm_nonneg (u * (1 + a))]
    have hn2 : ‖u * (1 - a)‖ ≤ 1 := by
      have hh := vbep_norm u (fun t : ℝ => 1 - g t) (by fun_prop)
      rw [← hp, hminus] at hh
      have hb : ‖cfc (fun t : ℝ => (1 - g t) * t * (1 - g t)) p‖ ≤ 1 := by
        refine norm_cfc_le zero_le_one fun t htp => ?_
        obtain ⟨ht0, ht1⟩ := hspec01 t htp
        have hgt := hg0 t
        have hgt' := hgle t
        have h1g : 0 ≤ 1 - g t := by linarith
        have h1g' : 1 - g t ≤ 1 := by linarith
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_one₀ (mul_le_one₀ h1g' ht0 ht1) h1g h1g'
      nlinarith [norm_nonneg (u * (1 - a))]
    have hua : u * a = 0 := by
      have hE := hext (u * (1 + a)) (u * (1 - a)) hn1 hn2 (by noncomm_ring)
      have h2 : u + u * a = u := by
        rw [mul_add, mul_one] at hE; exact hE
      simpa using h2
    have hpa : p * a = 0 := by rw [hp, mul_assoc, hua, mul_zero]
    have hcfcpa : cfc (fun t : ℝ => t * g t) p = 0 := by
      rw [cfc_mul (fun t : ℝ => t) g p (by fun_prop) hgc.continuousOn,
        cfc_id' (R := ℝ) (a := p) hpsa, ha] at *
      exact hpa
    have hmem : l * g l ∈ spectrum ℝ (0 : A) := by
      rw [← hcfcpa, cfc_map_spectrum (fun t : ℝ => t * g t) p hpsa (by fun_prop)]
      exact Set.mem_image_of_mem _ hl
    rw [spectrum.zero_eq] at hmem
    simp only [Set.mem_singleton_iff, hgl] at hmem
    nlinarith
  refine ⟨⟨hpp, hpsa⟩, ?_⟩
  -- Part 2: `(uu*)^⊥ A (u*u)^⊥ = 0`
  intro x
  have hup : u * p = u := by
    have h0 : star (u - u * p) * (u - u * p) = 0 := by
      have e1 : star (u - u * p) = star u - p * star u := by
        rw [star_sub, star_mul, hpsa.star_eq]
      rw [e1]
      calc (star u - p * star u) * (u - u * p)
          = star u * u - (star u * u) * p - p * (star u * u)
              + p * (star u * u) * p := by noncomm_ring
        _ = p - p * p - p * p + p * p * p := by rw [← hp]
        _ = 0 := by simp [hpp]
    have h1 : ‖u - u * p‖ * ‖u - u * p‖ = 0 := by
      rw [← CStarRing.norm_star_mul_self, h0, norm_zero]
    exact (sub_eq_zero.mp (norm_eq_zero.mp (mul_self_eq_zero.mp h1))).symm
  have hpu : p * star u = star u := by
    have h := congrArg star hup
    rwa [star_mul, hpsa.star_eq] at h
  set e : A := u * star u with he
  have hue : star u * (1 - e) = 0 := by
    rw [he, mul_sub, mul_one, ← mul_assoc, ← hp, hpu, sub_self]
  set q : A := 1 - p with hq
  have hqsa : IsSelfAdjoint q := by
    rw [hq]; simp [IsSelfAdjoint, star_sub, hpsa.star_eq]
  have hqq : q * q = q := by
    rw [hq]
    calc (1 - p) * (1 - p) = 1 - p - p + p * p := by noncomm_ring
      _ = 1 - p := by rw [hpp]; abel
  by_cases hb : (1 - e) * x * q = 0
  · exact hb
  exfalso
  set b : A := (1 - e) * x * q with hbdef
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hbq : b * q = b := by rw [hbdef, mul_assoc ((1 - e) * x) q q, hqq]
  have hub : star u * b = 0 := by
    rw [hbdef, ← mul_assoc, ← mul_assoc, hue, zero_mul, zero_mul]
  set c : A := ((‖b‖⁻¹ : ℝ) : ℂ) • b with hc
  have hcn : ‖c‖ = 1 := by
    rw [hc, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖b‖⁻¹)]
    field_simp
  have hcq : c * q = c := by rw [hc, smul_mul_assoc, hbq]
  have hucz : star u * c = 0 := by rw [hc, mul_smul_comm, hub, smul_zero]
  have hcu : star c * u = 0 := by
    have h := congrArg star hucz
    rwa [star_mul, star_star, star_zero] at h
  have h1 : star c * c ≤ 1 := by
    have hnn : (0 : A) ≤ star c * c := star_mul_self_nonneg c
    refine (CStarAlgebra.norm_le_one_iff_of_nonneg _ hnn).mp ?_
    rw [CStarRing.norm_star_mul_self, hcn]; norm_num
  have h2 : star q * (star c * c) * q = star c * c := by
    rw [hqsa.star_eq]
    calc q * (star c * c) * q = star (c * q) * (c * q) := by
          rw [star_mul, hqsa.star_eq]; noncomm_ring
      _ = star c * c := by rw [hcq]
  have hcc : star c * c ≤ q := by
    rw [← h2]
    calc star q * (star c * c) * q ≤ star q * 1 * q :=
          star_left_conjugate_le_conjugate h1 q
      _ = q := by rw [mul_one, hqsa.star_eq, hqq]
  have hsum : ∀ s : A, star u * s = 0 → star s * u = 0 →
      star (u + s) * (u + s) = p + star s * s := by
    intro s hs1 hs2
    rw [star_add]
    calc (star u + star s) * (u + s)
        = star u * u + star u * s + (star s * u + star s * s) := by noncomm_ring
      _ = p + star s * s := by rw [hs1, hs2, ← hp]; abel
  have hnormle : ∀ s : A, star u * s = 0 → star s * u = 0 → star s * s ≤ q →
      ‖u + s‖ ≤ 1 := by
    intro s hs1 hs2 hs3
    have hnn : (0 : A) ≤ star (u + s) * (u + s) := star_mul_self_nonneg _
    have hle : star (u + s) * (u + s) ≤ 1 := by
      rw [hsum s hs1 hs2]
      have h4 : p + star s * s ≤ p + q := add_le_add_right hs3 p
      rw [hq] at h4
      calc p + star s * s ≤ p + (1 - p) := h4
        _ = 1 := by abel
    have h := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hnn).mpr hle
    rw [CStarRing.norm_star_mul_self] at h
    nlinarith [norm_nonneg (u + s)]
  have hA : ‖u + c‖ ≤ 1 := hnormle c hucz hcu hcc
  have hB : ‖u + (-c)‖ ≤ 1 := by
    refine hnormle (-c) (by rw [mul_neg, hucz, neg_zero]) ?_ ?_
    · rw [star_neg, neg_mul, hcu, neg_zero]
    · rw [star_neg, neg_mul, mul_neg, neg_neg]; exact hcc
  have hfin := hext (u + c) (u + (-c)) hA hB (by abel)
  have hc0 : c = 0 := by simpa using hfin
  rw [hc0] at hcn
  simp at hcn


omit [PartialOrder A] [StarOrderedRing A] in
/-- norm of a star projection is ≤ 1. -/
private theorem norm_starProjection_le_one {e : A} (he : IsStarProjection e) :
    ‖e‖ ≤ 1 := by
  have h : ‖e‖ * ‖e‖ = ‖e‖ := by
    rw [← CStarRing.norm_star_mul_self, he.isSelfAdjoint.star_eq,
      he.isIdempotentElem.eq]
  nlinarith [norm_nonneg e]

section VNA

variable [VonNeumannAlgebra A]

/-- **86IX** (`polar-decomposition-of-functional`, vn.tex:6373, Theorem
(Polar decomposition of functionals)): every linear functional `f` on a von
Neumann algebra that is ultraweakly continuous on the unit ball is of the
form `f = f(uu*(·)) = f((·)u*u)` for a partial isometry `u` such that
`f(u(·))` and `f((·)u)` are positive. -/
theorem polar_decomposition_of_functional (f : A →ₗ[ℂ] ℂ)
    (hf : @ContinuousOn A ℂ (ultraweak A) _ ⇑f (Metric.closedBall 0 1)) :
    ∃ u : A, IsPartialIsometry A u ∧
      (∀ a : A, f a = f (u * star u * a)) ∧
      (∀ a : A, f a = f (a * (star u * u))) ∧
      (∀ a : A, 0 ≤ a → 0 ≤ f (u * a)) ∧
      (∀ a : A, 0 ≤ a → 0 ≤ f (a * u)) :=
  sorry

/-- **86XII** (`uwcont-on-ball`, vn.tex:6435, Corollary): a functional on a
von Neumann algebra that is ultraweakly continuous on the unit ball is
ultraweakly continuous. -/
theorem uwcont_on_ball (f : A →ₗ[ℂ] ℂ)
    (hf : @ContinuousOn A ℂ (ultraweak A) _ ⇑f (Metric.closedBall 0 1)) :
    @Continuous A ℂ (ultraweak A) _ ⇑f :=
  sorry

/-- **86XIV** (`functional-norm`, vn.tex:6460, Lemma): for a normal
(= ultraweakly continuous) functional `f` and a partial isometry `u` with
`f(u(·))` positive and `f = f(uu*(·))`: `‖f‖ = f(u)`. -/
theorem functional_norm (f : A →L[ℂ] ℂ)
    (hf : @Continuous A ℂ (ultraweak A) _ ⇑f) (u : A)
    (hu : IsPartialIsometry A u) (hpos : ∀ a : A, 0 ≤ a → 0 ≤ f (u * a))
    (heq : ∀ a : A, f a = f (u * star u * a)) :
    f u = (‖f‖ : ℂ) := by
  have hpr : IsStarProjection (star u * u) := by
    rw [hu.1, suppProj]
    exact (ceil_spec (star_mul_self_nonneg u)).1
  have hun : ‖u‖ ≤ 1 := by
    have h1 : ‖u‖ * ‖u‖ ≤ 1 := by
      rw [← CStarRing.norm_star_mul_self]
      exact norm_starProjection_le_one hpr
    nlinarith [norm_nonneg u]
  set g : A →L[ℂ] ℂ := f.comp (ContinuousLinearMap.mul ℂ A u) with hg
  have hg1 : g 1 = f u := by simp [hg]
  have hgpos : ∀ a : A, 0 ≤ a → 0 ≤ g a := by
    intro a ha; simpa [hg] using hpos a ha
  obtain ⟨him, hle⟩ := (positive_functional_criterion g).mp hgpos
  rw [hg1] at him hle
  have hfg : ‖f‖ ≤ ‖g‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun a => ?_
    have hfa : f a = g (star u * a) := by
      rw [hg]; simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.mul_apply', ← mul_assoc]
      exact heq a
    calc ‖f a‖ = ‖g (star u * a)‖ := by rw [hfa]
      _ ≤ ‖g‖ * ‖star u * a‖ := g.le_opNorm _
      _ ≤ ‖g‖ * (‖star u‖ * ‖a‖) := by gcongr; exact norm_mul_le _ _
      _ ≤ ‖g‖ * (1 * ‖a‖) := by gcongr; simpa using hun
      _ = ‖g‖ * ‖a‖ := by ring
  have hrev : (f u).re ≤ ‖f‖ := by
    calc (f u).re ≤ ‖f u‖ := Complex.re_le_norm _
      _ ≤ ‖f‖ * ‖u‖ := f.le_opNorm u
      _ ≤ ‖f‖ * 1 := by gcongr
      _ = ‖f‖ := mul_one _
  have hres : (f u).re = ‖f‖ := le_antisymm hrev (le_trans hfg hle)
  exact Complex.ext (by simpa using hres) (by simpa using him)

/-! ## Parsec 870: the predual -/

variable (A) in
/-- **87I** (vn.tex:6480, Definition): the **predual** `A_*` of a von
Neumann algebra: the (normed vector) space of ultraweakly continuous
functionals on `A`, rendered as a subset of the continuous dual.
(**87II**, Remark: Sakai's theorem `(A_*)* ≅ A` is neither needed nor
converted.) -/
def predual : Set (A →L[ℂ] ℂ) :=
  {f : A →L[ℂ] ℂ | @Continuous A ℂ (ultraweak A) _ ⇑f}

/-- **87III** (`predual-complete`, vn.tex:6509, Proposition): the predual
of a von Neumann algebra is complete with respect to the operator norm. -/
theorem predual_complete : IsComplete (predual A) :=
  sorry

/-! **87V** (vn.tex:6548): motivation for the next lemma — nothing to
formalize. -/

/-- **87VI** (`norm-predual`, vn.tex:6563, Lemma):
`‖a‖ = sup {|f(a)| : f ∈ (A_*)₁}` for every element `a` of a von Neumann
algebra. -/
theorem norm_predual (a : A) :
    IsLUB {r : ℝ | ∃ f ∈ predual A, ‖f‖ ≤ 1 ∧ r = ‖f a‖} ‖a‖ :=
  sorry

/-- **87VIII** (`ultraweakly-bounded-implies-bounded`, vn.tex:6584,
Theorem): a net `(b_α)_α` in a von Neumann algebra is norm bounded provided
it is **ultraweakly bounded**, i.e. `sup_α |ω(b_α)| < ∞` for every
np-functional `ω`. -/
theorem ultraweakly_bounded_implies_bounded {ι : Type*} (x : ι → A)
    (h : ∀ ω : NPFunctional A, BddAbove (Set.range fun i => ‖ω (x i)‖)) :
    BddAbove (Set.range fun i => ‖x i‖) :=
  sorry

/-! ## Parsec 880: ultraweak permanence and the double commutant theorem

**88I** (vn.tex:6622): overview — nothing to formalize. -/

variable (A) in
/-- **88II** (`commutant-ceil`, vn.tex:6669, Proposition), definition part:
the projection `⌈e⌉_{S^□} = ⋃_{a∈S} ⌈a* e a⌉`. -/
noncomputable def commutantCeil (S : Set A) (e : A) : A :=
  projSup {x : A | ∃ a ∈ S, x = ceil (star a * e * a)}

/-- **88II** (`commutant-ceil`, vn.tex:6669, Proposition): for a subset `S`
of a von Neumann algebra closed under multiplication and involution and
containing `1`, and a projection `e`: `⌈e⌉_{S^□} = ⋃_{a∈S} ⌈a* e a⌉` is
the least projection in `S^□` above `e`. -/
theorem commutant_ceil (S : Set A) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hstar : ∀ a ∈ S, star a ∈ S) (hone : (1 : A) ∈ S) (e : A)
    (he : IsStarProjection e) :
    IsLeast {p : A | IsStarProjection p ∧ p ∈ commutant A S ∧ e ≤ p}
      (commutantCeil A S e) :=
  sorry

end VNA

section BH

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- **88IV** (`carrier-vector-state`, vn.tex:6714, Exercise): for a vector
`x` of a Hilbert space `H` and a unital ∗-subalgebra `S` of `B(H)`, the
least projection in `S^□` above `⌈|x⟩⟨x|⌉` equals
`⋃_{a∈S} ⌈|ax⟩⟨ax|⌉` and is the projection onto `closure (S x)` (a
projection identified by its fixed points).  (Item 2, identifying it with
the carrier of the vector functional restricted to `S^□`, needs the
relative carrier and is subsumed by the `IsLeast` formulation.) -/
theorem carrier_vector_state (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) :
    commutantCeil (H →L[ℂ] H) S (ceil (ketbra x x)) =
        projSup {p : H →L[ℂ] H | ∃ T ∈ S, p = ketbra (T x) (T x)} ∧
      {y : H | commutantCeil (H →L[ℂ] H) S (ceil (ketbra x x)) y = y} =
        closure {y : H | ∃ T ∈ S, y = T x} :=
  sorry

/-- **88IV** (`carrier-vector-state`, vn.tex:6714, Exercise), conclusion:
`closure (S^□□ x) = closure (S x)`. -/
theorem carrier_vector_state' (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) :
    closure {y : H | ∃ T ∈ commutant (H →L[ℂ] H)
        (commutant (H →L[ℂ] H) S), y = T x} =
      closure {y : H | ∃ T ∈ S, y = T x} := by
  -- the cyclic subspace `S x` and its closure `M`
  set L : S →ₗ[ℂ] H :=
    { toFun := fun T => (T : H →L[ℂ] H) x
      map_add' := fun T T' => rfl
      map_smul' := fun c T => rfl } with hL
  set Vsub : Submodule ℂ H := LinearMap.range L with hV
  have hVset : (Vsub : Set H) = {y : H | ∃ T ∈ S, y = T x} := by
    ext y
    constructor
    · rintro ⟨T, rfl⟩; exact ⟨(T : H →L[ℂ] H), T.2, rfl⟩
    · rintro ⟨T, hT, rfl⟩; exact ⟨⟨T, hT⟩, rfl⟩
  set M : Submodule ℂ H := Vsub.topologicalClosure with hM
  have hMclosed : IsClosed (M : Set H) := Vsub.isClosed_topologicalClosure
  have : CompleteSpace M := hMclosed.completeSpace_coe
  have hMset : (M : Set H) = closure {y : H | ∃ T ∈ S, y = T x} := by
    rw [hM, Submodule.topologicalClosure_coe, hVset]
  have hxM : x ∈ M := by
    refine Vsub.le_topologicalClosure ?_
    exact ⟨1, by simp [hL]⟩
  -- `M` is invariant under `S`
  have hinv : ∀ T ∈ S, ∀ z ∈ M, T z ∈ M := by
    intro T hT z hz
    have hcl : IsClosed {w : H | T w ∈ M} := hMclosed.preimage T.continuous
    have hsub : (Vsub : Set H) ⊆ {w : H | T w ∈ M} := by
      rintro _ ⟨T', rfl⟩
      refine Vsub.le_topologicalClosure ⟨⟨T * (T' : H →L[ℂ] H), mul_mem hT T'.2⟩, rfl⟩
    have : (M : Set H) ⊆ {w : H | T w ∈ M} := by
      rw [hM, Submodule.topologicalClosure_coe]
      exact closure_minimal hsub hcl
    exact this hz
  -- `Mᗮ` is invariant under `S`
  have hinvo : ∀ T ∈ S, ∀ z ∈ Mᗮ, T z ∈ Mᗮ := by
    intro T hT z hz
    rw [Submodule.mem_orthogonal]
    intro m hm
    have hadj : ContinuousLinearMap.adjoint T ∈ S := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact star_mem_iff.mpr hT
    have h1 : (inner ℂ ((ContinuousLinearMap.adjoint T) m) z : ℂ) = inner ℂ m (T z) :=
      ContinuousLinearMap.adjoint_inner_left T z m
    rw [← h1]
    exact (Submodule.mem_orthogonal M z).mp hz _ (hinv _ hadj m hm)
  -- the projection onto `M` lies in `S□`
  have hPcomm : M.starProjection ∈ commutant (H →L[ℂ] H) S := by
    intro T hT
    ext z
    have hz1 : M.starProjection z ∈ M := M.starProjection_apply_mem z
    have hz2 : z - M.starProjection z ∈ Mᗮ := Submodule.sub_starProjection_mem_orthogonal z
    have e1 : T z = T (M.starProjection z) + T (z - M.starProjection z) := by
      rw [← map_add]; congr 1; abel
    simp only [ContinuousLinearMap.mul_apply]
    rw [e1, map_add,
      (Submodule.starProjection_eq_self_iff).mpr (hinv T hT _ hz1),
      (Submodule.starProjection_apply_eq_zero_iff M).mpr (hinvo T hT _ hz2), add_zero]
  -- conclusion
  apply le_antisymm
  · refine closure_minimal ?_ hMclosed |>.trans (le_of_eq hMset)
    rintro _ ⟨R, hR, rfl⟩
    have hcomm := hR _ hPcomm
    have : R x = M.starProjection (R x) := by
      conv_lhs => rw [← (Submodule.starProjection_eq_self_iff).mpr hxM]
      exact congrArg (fun (T : H →L[ℂ] H) => T x) hcomm.symm
    rw [this]
    exact M.starProjection_apply_mem _
  · refine closure_mono ?_
    rintro _ ⟨T, hT, rfl⟩
    exact ⟨T, fun m hm => (hm T hT).symm, rfl⟩

/-- **88V** (`proto-double-commutant`, vn.tex:6737): for a unital
∗-subalgebra `S` of `B(H)`, the double commutant `S^□□` is contained in
the ultrastrong closure of `S`.  (The enumerated items are steps of the
proof, not converted separately.) -/
theorem proto_double_commutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) S) ⊆
      @closure _ (ultrastrong (H →L[ℂ] H)) (S : Set (H →L[ℂ] H)) :=
  sorry

/-- **88VI** (`double-commutant`, vn.tex:6781, Double Commutant Theorem):
for a unital ∗-subalgebra `S` of `B(H)` the following coincide: the double
commutant `S^□□`, the ultrastrong closure of `S`, the ultraweak closure of
`S`, and the least von Neumann subalgebra `W*(S)` containing `S`. -/
theorem double_commutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) S) =
        @closure _ (ultrastrong (H →L[ℂ] H)) (S : Set (H →L[ℂ] H)) ∧
      commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) S) =
        @closure _ (ultraweak (H →L[ℂ] H)) (S : Set (H →L[ℂ] H)) ∧
      commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) S) =
        (wstar (H →L[ℂ] H) (S : Set (H →L[ℂ] H)) :
          StarSubalgebra ℂ (H →L[ℂ] H)) :=
  sorry

/-- **88VIII** (`centre-commutant`, vn.tex:6824, Exercise): for a von
Neumann subalgebra `R` of `B(H)`: `Z(R) = Z(R^□)`, i.e. the central
elements of `R` coincide with those of its commutant. -/
theorem centre_commutant (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hR : IsVNSubalgebra (H →L[ℂ] H) R) :
    (R : Set (H →L[ℂ] H)) ∩ commutant (H →L[ℂ] H) R =
      commutant (H →L[ℂ] H) R ∩
        commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) R) :=
  sorry

/-- **88IX** (`commutant-cceil`, vn.tex:6831): for an np-map
`f : B(H) → B` and a von Neumann subalgebra `R` of `B(H)`, the central
carrier of `f` relative to `R` coincides with the central carrier of `f`
relative to `R^□`: some projection is least among the central projections
`p` of `R` with `f(p^⊥) = 0` and least among those of `R^□`. -/
theorem commutant_cceil [VonNeumannAlgebra B]
    (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hR : IsVNSubalgebra (H →L[ℂ] H) R) (f : (H →L[ℂ] H) →ₚ[ℂ] B)
    (hf : PreservesDirSups ⇑f) :
    ∃ c : H →L[ℂ] H,
      IsLeast {p : H →L[ℂ] H | p ∈ R ∧ IsStarProjection p ∧
        (∀ b ∈ R, p * b = b * p) ∧ f (1 - p) = 0} c ∧
      IsLeast {p : H →L[ℂ] H | p ∈ commutant (H →L[ℂ] H) R ∧
        IsStarProjection p ∧
        (∀ b ∈ commutant (H →L[ℂ] H) R, p * b = b * p) ∧
        f (1 - p) = 0} c :=
  sorry

/-! ## Parsec 890: normal functionals as sums of vector functionals -/

variable [VonNeumannAlgebra A]

/-- **89I** (`gns-mapping-property`, vn.tex:6839, Lemma): if an
np-functional `ω` on a von Neumann algebra is represented by nmiu-maps
`ρ : A → B(H)` and `π : A → B(K)` with vectors `x ∈ H`, `y ∈ K` — i.e.
`⟨x,ρ(·)x⟩ = ω = ⟨y,π(·)y⟩` — then there is a bounded `U : K → H` with
`UU*` the projection onto `closure (ρ(A)x)`, `U*U` the projection onto
`closure (π(A)y)`, and `Uπ(a) = ρ(a)U` for all `a`. -/
theorem gns_mapping_property (ω : NPFunctional A)
    (ρ : NMIUMap A (H →L[ℂ] H)) (π : NMIUMap A (K →L[ℂ] K)) (x : H) (y : K)
    (hx : ∀ a : A, ω a = ⟪x, ρ a x⟫) (hy : ∀ a : A, ω a = ⟪y, π a y⟫) :
    ∃ U : K →L[ℂ] H,
      {z : H | (U ∘L ContinuousLinearMap.adjoint U) z = z} =
          closure {z : H | ∃ a : A, z = ρ a x} ∧
      {z : K | (ContinuousLinearMap.adjoint U ∘L U) z = z} =
          closure {z : K | ∃ a : A, z = π a y} ∧
      ∀ a : A, U ∘L π a = ρ a ∘L U := by
  classical
  -- the ∗-algebra structure of `ρ` and `π`, through their `StarAlgHom`s
  have hρ_add : ∀ a b : A, ρ (a + b) = ρ a + ρ b := fun a b => map_add ρ.toStarAlgHom a b
  have hρ_smul : ∀ (c : ℂ) (a : A), ρ (c • a) = c • ρ a := fun c a =>
    map_smul ρ.toStarAlgHom c a
  have hρ_mul : ∀ a b : A, ρ (a * b) = ρ a * ρ b := fun a b => map_mul ρ.toStarAlgHom a b
  have hρ_star : ∀ a : A, ρ (star a) = star (ρ a) := fun a => map_star ρ.toStarAlgHom a
  have hπ_add : ∀ a b : A, π (a + b) = π a + π b := fun a b => map_add π.toStarAlgHom a b
  have hπ_smul : ∀ (c : ℂ) (a : A), π (c • a) = c • π a := fun c a =>
    map_smul π.toStarAlgHom c a
  have hπ_mul : ∀ a b : A, π (a * b) = π a * π b := fun a b => map_mul π.toStarAlgHom a b
  have hπ_star : ∀ a : A, π (star a) = star (π a) := fun a => map_star π.toStarAlgHom a
  -- `ρ` and `π` send `star` to the adjoint
  have hρadj : ∀ a : A, ContinuousLinearMap.adjoint (ρ a) = ρ (star a) := by
    intro a
    rw [← ContinuousLinearMap.star_eq_adjoint, hρ_star]
  have hπadj : ∀ a : A, ContinuousLinearMap.adjoint (π a) = π (star a) := by
    intro a
    rw [← ContinuousLinearMap.star_eq_adjoint, hπ_star]
  -- both representations realise the same norms
  have hρsq : ∀ a : A, ‖ρ a x‖ ^ 2 = RCLike.re (ω (star a * a)) := by
    intro a
    rw [hx (star a * a), hρ_mul, ← hρadj a]
    have h : (⟪x, (ContinuousLinearMap.adjoint (ρ a) * ρ a) x⟫ : ℂ) = ⟪ρ a x, ρ a x⟫ := by
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right]
    rw [h]
    exact (inner_self_eq_norm_sq _).symm
  have hπsq : ∀ a : A, ‖π a y‖ ^ 2 = RCLike.re (ω (star a * a)) := by
    intro a
    rw [hy (star a * a), hπ_mul, ← hπadj a]
    have h : (⟪y, (ContinuousLinearMap.adjoint (π a) * π a) y⟫ : ℂ) = ⟪π a y, π a y⟫ := by
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right]
    rw [h]
    exact (inner_self_eq_norm_sq _).symm
  have hnorm : ∀ a : A, ‖ρ a x‖ = ‖π a y‖ := by
    intro a
    have h : ‖ρ a x‖ ^ 2 = ‖π a y‖ ^ 2 := (hρsq a).trans (hπsq a).symm
    exact le_antisymm (le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) h.le)
      (le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) h.ge)
  -- the two cyclic subspaces
  set Lρ : A →ₗ[ℂ] H :=
    { toFun := fun a => ρ a x
      map_add' := fun a b => by rw [hρ_add]; rfl
      map_smul' := fun c a => by rw [hρ_smul]; rfl } with hLρ
  set Lπ : A →ₗ[ℂ] K :=
    { toFun := fun a => π a y
      map_add' := fun a b => by rw [hπ_add]; rfl
      map_smul' := fun c a => by rw [hπ_smul]; rfl } with hLπ
  set Msub : Submodule ℂ H := LinearMap.range Lρ with hMsub
  set Nsub : Submodule ℂ K := LinearMap.range Lπ with hNsub
  set M : Submodule ℂ H := Msub.topologicalClosure with hM
  set N : Submodule ℂ K := Nsub.topologicalClosure with hN
  have : CompleteSpace M := Msub.isClosed_topologicalClosure.completeSpace_coe
  have : CompleteSpace N := Nsub.isClosed_topologicalClosure.completeSpace_coe
  have hmemM : ∀ a : A, ρ a x ∈ M := fun a => Msub.le_topologicalClosure ⟨a, rfl⟩
  have hmemN : ∀ a : A, π a y ∈ N := fun a => Nsub.le_topologicalClosure ⟨a, rfl⟩
  set e₂ : A →ₗ[ℂ] M :=
    { toFun := fun a => ⟨ρ a x, hmemM a⟩
      map_add' := fun a b => by
        ext
        change (ρ (a + b)) x = (ρ a) x + (ρ b) x
        rw [hρ_add]; rfl
      map_smul' := fun c a => by
        ext
        change (ρ (c • a)) x = c • (ρ a) x
        rw [hρ_smul]; rfl } with he₂
  set e₁ : A →ₗ[ℂ] N :=
    { toFun := fun a => ⟨π a y, hmemN a⟩
      map_add' := fun a b => by
        ext
        change (π (a + b)) y = (π a) y + (π b) y
        rw [hπ_add]; rfl
      map_smul' := fun c a => by
        ext
        change (π (c • a)) y = c • (π a) y
        rw [hπ_smul]; rfl } with he₁
  have hdense₂ : DenseRange (e₂ : A → M) := by
    rw [DenseRange, Subtype.dense_iff]
    intro w hw
    have hw' : w ∈ closure (Msub : Set H) := by
      rwa [← Submodule.topologicalClosure_coe]
    refine closure_mono ?_ hw'
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨ρ a x, hmemM a⟩, ⟨a, rfl⟩, rfl⟩
  have hdense₁ : DenseRange (e₁ : A → N) := by
    rw [DenseRange, Subtype.dense_iff]
    intro w hw
    have hw' : w ∈ closure (Nsub : Set K) := by
      rwa [← Submodule.topologicalClosure_coe]
    refine closure_mono ?_ hw'
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨π a y, hmemN a⟩, ⟨a, rfl⟩, rfl⟩
  -- the unitary between the cyclic subspaces
  set Φ : N ≃ₗᵢ[ℂ] M :=
    (LinearEquiv.refl ℂ A).extendOfIsometry e₁ e₂ hdense₁ hdense₂ (fun a => hnorm a)
    with hΦ
  have hΦval : ∀ a : A, Φ (e₁ a) = e₂ a := fun a =>
    LinearEquiv.extendOfIsometry_eq _ _ _ hdense₁ hdense₂ (fun a => hnorm a) a
  set Ψ : N →L[ℂ] M := Φ.toLinearIsometry.toContinuousLinearMap with hΨ
  set Ψ' : M →L[ℂ] N := Φ.symm.toLinearIsometry.toContinuousLinearMap with hΨ'
  set U : K →L[ℂ] H := M.subtypeL ∘L (Ψ ∘L N.orthogonalProjectionOnto) with hU
  set W : H →L[ℂ] K := N.subtypeL ∘L (Ψ' ∘L M.orthogonalProjectionOnto) with hW
  have hUapp : ∀ z : K, U z = ((Φ (N.orthogonalProjectionOnto z) : M) : H) := fun z => rfl
  have hWapp : ∀ w : H, W w = ((Φ.symm (M.orthogonalProjectionOnto w) : N) : K) := fun w => rfl
  -- `U` maps the cyclic vectors correctly
  have hUval : ∀ a : A, U (π a y) = ρ a x := by
    intro a
    rw [hUapp]
    have h : N.orthogonalProjectionOnto (π a y) = e₁ a :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨π a y, hmemN a⟩ : N)
    rw [h, hΦval a]
    rfl
  -- inner-product bookkeeping for the projections
  have hNinner : ∀ u z : K, u ∈ N → (⟪u, z⟫ : ℂ) = ⟪u, N.starProjection z⟫ := by
    intro u z hu
    have h := Submodule.starProjection_inner_eq_zero (K := N) z u hu
    rw [inner_sub_left, sub_eq_zero] at h
    have h2 := congrArg (starRingEnd ℂ) h
    rwa [inner_conj_symm, inner_conj_symm] at h2
  have hMinner : ∀ u w : H, u ∈ M → (⟪u, w⟫ : ℂ) = ⟪u, M.starProjection w⟫ := by
    intro u w hu
    have h := Submodule.starProjection_inner_eq_zero (K := M) w u hu
    rw [inner_sub_left, sub_eq_zero] at h
    have h2 := congrArg (starRingEnd ℂ) h
    rwa [inner_conj_symm, inner_conj_symm] at h2
  -- `W` is the adjoint of `U`
  have hadjU : ContinuousLinearMap.adjoint U = W := by
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro w z
    rw [hWapp, hUapp]
    have h1 : (⟪((Φ.symm (M.orthogonalProjectionOnto w) : N) : K), z⟫ : ℂ) =
        ⟪((Φ.symm (M.orthogonalProjectionOnto w) : N) : K),
          ((N.orthogonalProjectionOnto z : N) : K)⟫ :=
      hNinner _ z (Φ.symm (M.orthogonalProjectionOnto w)).2
    have h2 : (⟪(Φ.symm (M.orthogonalProjectionOnto w) : N),
        (N.orthogonalProjectionOnto z : N)⟫ : ℂ) =
        ⟪(M.orthogonalProjectionOnto w : M), Φ (N.orthogonalProjectionOnto z)⟫ := by
      rw [← Φ.inner_map_map (Φ.symm (M.orthogonalProjectionOnto w))
        (N.orthogonalProjectionOnto z), Φ.apply_symm_apply]
    have h3 : (⟪w, ((Φ (N.orthogonalProjectionOnto z) : M) : H)⟫ : ℂ) =
        ⟪((M.orthogonalProjectionOnto w : M) : H),
          ((Φ (N.orthogonalProjectionOnto z) : M) : H)⟫ := by
      have := hMinner ((Φ (N.orthogonalProjectionOnto z) : M) : H) w
        (Φ (N.orthogonalProjectionOnto z)).2
      have h4 := congrArg (starRingEnd ℂ) this
      rwa [inner_conj_symm, inner_conj_symm] at h4
    rw [h1, h3]
    exact h2
  -- the two range projections
  have hUW : U ∘L W = M.starProjection := by
    ext w
    show ((Φ (N.orthogonalProjectionOnto
      ((Φ.symm (M.orthogonalProjectionOnto w) : N) : K)) : M) : H) = M.starProjection w
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (Φ.symm (M.orthogonalProjectionOnto w)), Φ.apply_symm_apply]
    rfl
  have hWU : W ∘L U = N.starProjection := by
    ext z
    show ((Φ.symm (M.orthogonalProjectionOnto
      ((Φ (N.orthogonalProjectionOnto z) : M) : H)) : N) : K) = N.starProjection z
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (Φ (N.orthogonalProjectionOnto z)), Φ.symm_apply_apply]
    rfl
  -- invariance of the cyclic subspaces
  have hNinv : ∀ (a : A) (z : K), z ∈ N → π a z ∈ N := by
    intro a z hz
    have hsub : (Nsub : Set K) ⊆ (π a) ⁻¹' (N : Set K) := by
      rintro _ ⟨b, rfl⟩
      have h : π a (π b y) = π (a * b) y := by rw [hπ_mul]; rfl
      change π a (Lπ b) ∈ (N : Set K)
      change π a (π b y) ∈ N
      rw [h]
      exact hmemN _
    have hclosed : IsClosed ((π a) ⁻¹' (N : Set K)) :=
      Nsub.isClosed_topologicalClosure.preimage (π a).continuous
    have := closure_minimal hsub hclosed
    rw [← Submodule.topologicalClosure_coe] at this
    exact this hz
  -- the intertwining relation
  have hinter : ∀ (a : A) (z : K), U (π a z) = ρ a (U z) := by
    intro a
    have hOnN : ∀ z ∈ N, U (π a z) = ρ a (U z) := by
      have hsub : (Nsub : Set K) ⊆ {z : K | U (π a z) = ρ a (U z)} := by
        rintro _ ⟨b, rfl⟩
        change U (π a (π b y)) = ρ a (U (π b y))
        have h : π a (π b y) = π (a * b) y := by rw [hπ_mul]; rfl
        rw [h, hUval (a * b), hUval b, hρ_mul]
        rfl
      have hclosed : IsClosed {z : K | U (π a z) = ρ a (U z)} :=
        isClosed_eq (by fun_prop) (by fun_prop)
      have hcl := closure_minimal hsub hclosed
      rw [← Submodule.topologicalClosure_coe] at hcl
      exact hcl
    have hOnPerp : ∀ z ∈ Nᗮ, U (π a z) = ρ a (U z) := by
      intro z hz
      have hz' : π a z ∈ Nᗮ := by
        rw [Submodule.mem_orthogonal]
        intro u hu
        have h : (⟪u, π a z⟫ : ℂ) = ⟪π (star a) u, z⟫ := by
          rw [← hπadj a, ContinuousLinearMap.adjoint_inner_left]
        rw [h]
        exact hz _ (hNinv (star a) u hu)
      have hUzero : ∀ v : K, v ∈ Nᗮ → U v = 0 := by
        intro v hv
        rw [hUapp, Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hv]
        simp
      rw [hUzero _ hz', hUzero _ hz, map_zero]
    intro z
    set u : K := N.starProjection z with hu
    have huN : u ∈ N := N.starProjection_apply_mem z
    have hvperp : z - u ∈ Nᗮ := Submodule.sub_starProjection_mem_orthogonal z
    have hsplit : π a z = π a u + π a (z - u) := by
      rw [← map_add]
      congr 1
      abel
    have hsplitU : U z = U u + U (z - u) := by
      rw [← map_add]
      congr 1
      abel
    rw [hsplit, map_add, hOnN u huN, hOnPerp _ hvperp, ← map_add, ← hsplitU]
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hadjU, hUW]
    ext w
    simp only [Set.mem_setOf_eq, Submodule.starProjection_eq_self_iff, hM]
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    constructor
    · intro h
      refine closure_mono ?_ h
      rintro _ ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · intro h
      refine closure_mono ?_ h
      rintro _ ⟨a, rfl⟩
      exact ⟨a, rfl⟩
  · rw [hadjU, hWU]
    ext z
    simp only [Set.mem_setOf_eq, Submodule.starProjection_eq_self_iff, hN]
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    constructor
    · intro h
      refine closure_mono ?_ h
      rintro _ ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · intro h
      refine closure_mono ?_ h
      rintro _ ⟨a, rfl⟩
      exact ⟨a, rfl⟩
  · intro a
    ext z
    exact hinter a z

section SumOfPartialIsometries

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Finite Parseval identity for a pairwise orthogonal family. -/
private theorem norm_sq_finset_sum_orthogonal {ι : Type*} (v : ι → F)
    (horth : Pairwise fun i j => (⟪v i, v j⟫ : ℂ) = 0) (s : Finset ι) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  have key : (⟪∑ i ∈ s, v i, ∑ i ∈ s, v i⟫ : ℂ) = ∑ i ∈ s, (⟪v i, v i⟫ : ℂ) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [inner_sum]
    exact Finset.sum_eq_single i (fun j _ hji => horth (Ne.symm hji))
      fun h => absurd hi h
  calc ‖∑ i ∈ s, v i‖ ^ 2
      = RCLike.re (⟪∑ i ∈ s, v i, ∑ i ∈ s, v i⟫ : ℂ) := (inner_self_eq_norm_sq _).symm
    _ = RCLike.re (∑ i ∈ s, (⟪v i, v i⟫ : ℂ)) := by rw [key]
    _ = ∑ i ∈ s, RCLike.re (⟪v i, v i⟫ : ℂ) := map_sum _ _ _
    _ = ∑ i ∈ s, ‖v i‖ ^ 2 := Finset.sum_congr rfl fun i _ => inner_self_eq_norm_sq _

/-- A pairwise orthogonal family with summable squared norms is summable. -/
private theorem summable_of_pairwise_orthogonal {ι : Type*} (v : ι → F)
    (horth : Pairwise fun i j => (⟪v i, v j⟫ : ℂ) = 0)
    (hsq : Summable fun i => ‖v i‖ ^ 2) : Summable v := by
  classical
  rw [summable_iff_vanishing_norm]
  intro ε hε
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hsq (ε ^ 2) (by positivity)
  refine ⟨s, fun t ht => ?_⟩
  have h1 : ‖∑ i ∈ t, ‖v i‖ ^ 2‖ < ε ^ 2 := hs t ht
  have h2 : ‖∑ i ∈ t, v i‖ ^ 2 = ∑ i ∈ t, ‖v i‖ ^ 2 :=
    norm_sq_finset_sum_orthogonal v horth t
  have h3 : ∑ i ∈ t, ‖v i‖ ^ 2 ≤ ‖∑ i ∈ t, ‖v i‖ ^ 2‖ := le_abs_self _
  have h4 : ‖∑ i ∈ t, v i‖ ^ 2 < ε ^ 2 := by rw [h2]; exact lt_of_le_of_lt h3 h1
  exact lt_of_pow_lt_pow_left₀ 2 hε.le h4

/-- The key construction behind **89III**: a family of partial isometries
with pairwise orthogonal initial projections whose "cross terms" vanish can
be summed pointwise into a single contraction. -/
private theorem exists_sum_of_partial_isometries {ι : Type*} (U : ι → (E →L[ℂ] F))
    (hproj : ∀ i, IsStarProjection (ContinuousLinearMap.adjoint (U i) ∘L U i))
    (horthL : Pairwise fun i j =>
      (ContinuousLinearMap.adjoint (U i) ∘L U i) ∘L
        (ContinuousLinearMap.adjoint (U j) ∘L U j) = 0)
    (hcross : Pairwise fun i j => ContinuousLinearMap.adjoint (U i) ∘L U j = 0) :
    ∃ V : E →L[ℂ] F, ∀ x : E, HasSum (fun i => U i x) (V x) := by
  classical
  set p : ι → (E →L[ℂ] E) := fun i => ContinuousLinearMap.adjoint (U i) ∘L U i with hpdef
  -- the vectors `U i x` are pairwise orthogonal
  have horthv : ∀ x : E, Pairwise fun i j => (⟪U i x, U j x⟫ : ℂ) = 0 := by
    intro x i j hij
    have h : (⟪U i x, U j x⟫ : ℂ) =
        ⟪x, (ContinuousLinearMap.adjoint (U i) ∘L U j) x⟫ := by
      rw [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right (U i) x (U j x)]
    rw [h, hcross hij]
    simp
  -- `‖U i x‖²` sums to at most `‖x‖²`
  have hnormp : ∀ (i : ι) (x : E), ‖U i x‖ ^ 2 = RCLike.re (⟪x, p i x⟫ : ℂ) := by
    intro i x
    rw [hpdef]
    simp only [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.adjoint_inner_right (U i) x (U i x)]
    exact (inner_self_eq_norm_sq _).symm
  have hbound : ∀ (x : E) (s : Finset ι), ∑ i ∈ s, ‖U i x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    intro x s
    have hP : IsStarProjection (∑ i ∈ s, p i) :=
      isStarProjection_sum s p hproj fun i _ j _ hij => horthL hij
    have hPx : (∑ i ∈ s, p i) ((∑ i ∈ s, p i) x) = (∑ i ∈ s, p i) x := by
      have := hP.isIdempotentElem
      calc (∑ i ∈ s, p i) ((∑ i ∈ s, p i) x)
          = ((∑ i ∈ s, p i) * (∑ i ∈ s, p i)) x := rfl
        _ = (∑ i ∈ s, p i) x := by rw [this]
    have hre : RCLike.re (⟪x, (∑ i ∈ s, p i) x⟫ : ℂ) = ‖(∑ i ∈ s, p i) x‖ ^ 2 := by
      have hadj : ContinuousLinearMap.adjoint (∑ i ∈ s, p i) = ∑ i ∈ s, p i :=
        hP.isSelfAdjoint
      have : (⟪x, (∑ i ∈ s, p i) x⟫ : ℂ) = ⟪(∑ i ∈ s, p i) x, (∑ i ∈ s, p i) x⟫ := by
        conv_lhs => rw [← hPx]
        rw [← hadj]
        rw [ContinuousLinearMap.adjoint_inner_right]
        rw [hadj]
      rw [this]
      exact inner_self_eq_norm_sq _
    have hle : ‖(∑ i ∈ s, p i) x‖ ≤ ‖x‖ := by
      rcases eq_or_ne ((∑ i ∈ s, p i) x) 0 with h0 | h0
      · simp [h0]
      · have hcs : RCLike.re (⟪x, (∑ i ∈ s, p i) x⟫ : ℂ) ≤ ‖x‖ * ‖(∑ i ∈ s, p i) x‖ :=
          le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
        rw [hre] at hcs
        have hpos : 0 < ‖(∑ i ∈ s, p i) x‖ := norm_pos_iff.mpr h0
        nlinarith
    have hsum : ∑ i ∈ s, ‖U i x‖ ^ 2 = RCLike.re (⟪x, (∑ i ∈ s, p i) x⟫ : ℂ) := by
      rw [ContinuousLinearMap.sum_apply, inner_sum, map_sum]
      exact Finset.sum_congr rfl fun i _ => hnormp i x
    rw [hsum, hre]
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hsummable : ∀ x : E, Summable fun i => U i x := by
    intro x
    exact summable_of_pairwise_orthogonal _ (horthv x)
      (summable_of_sum_le (fun i => sq_nonneg _) (hbound x))
  -- assemble the pointwise sums into a bounded operator
  have hadd : ∀ x y : E, ∑' i, U i (x + y) = (∑' i, U i x) + ∑' i, U i y := by
    intro x y
    refine HasSum.tsum_eq ?_
    simpa only [map_add] using ((hsummable x).hasSum.add (hsummable y).hasSum)
  have hsmul : ∀ (c : ℂ) (x : E), ∑' i, U i (c • x) = c • ∑' i, U i x := by
    intro c x
    refine HasSum.tsum_eq ?_
    simpa only [map_smul] using ((hsummable x).hasSum.const_smul c)
  set L : E →ₗ[ℂ] F :=
    { toFun := fun x => ∑' i, U i x
      map_add' := hadd
      map_smul' := fun c x => hsmul c x } with hLdef
  have hLnorm : ∀ x : E, ‖L x‖ ≤ 1 * ‖x‖ := by
    intro x
    rw [one_mul]
    have hpart : ∀ s : Finset ι, ‖∑ i ∈ s, U i x‖ ≤ ‖x‖ := by
      intro s
      have h1 : ‖∑ i ∈ s, U i x‖ ^ 2 = ∑ i ∈ s, ‖U i x‖ ^ 2 :=
        norm_sq_finset_sum_orthogonal _ (horthv x) s
      have h2 : ‖∑ i ∈ s, U i x‖ ^ 2 ≤ ‖x‖ ^ 2 := by rw [h1]; exact hbound x s
      exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) h2
    have htend : Filter.Tendsto (fun s : Finset ι => ∑ i ∈ s, U i x)
        (SummationFilter.unconditional ι).filter (𝓝 (∑' i, U i x)) :=
      (hsummable x).hasSum
    exact le_of_tendsto htend.norm (Filter.Eventually.of_forall fun s => hpart s)
  refine ⟨L.mkContinuous 1 hLnorm, fun x => ?_⟩
  simpa only [LinearMap.mkContinuous_apply, hLdef, LinearMap.coe_mk, AddHom.coe_mk]
    using (hsummable x).hasSum

end SumOfPartialIsometries

/-- **89III** (`summing-partial-isometries`, vn.tex:6901, Exercise): given
bounded operators `Uᵢ : H → K` such that the `Uᵢ*Uᵢ` are pairwise
orthogonal projections and the `UᵢUᵢ*` are pairwise orthogonal
projections, there is a bounded `V : H → K` with
`⟪y, Vx⟫ = ∑ᵢ ⟪y, Uᵢx⟫`, `V*V = ∑ᵢ Uᵢ*Uᵢ` and `VV* = ∑ᵢ UᵢUᵢ*` (the
last two sums taken pointwise). -/
theorem summing_partial_isometries {ι : Type*} (U : ι → (H →L[ℂ] K))
    (hproj : ∀ i, IsStarProjection (ContinuousLinearMap.adjoint (U i) ∘L U i))
    (horthL : Pairwise fun i j =>
      (ContinuousLinearMap.adjoint (U i) ∘L U i) ∘L
        (ContinuousLinearMap.adjoint (U j) ∘L U j) = 0)
    (horthR : Pairwise fun i j =>
      (U i ∘L ContinuousLinearMap.adjoint (U i)) ∘L
        (U j ∘L ContinuousLinearMap.adjoint (U j)) = 0) :
    ∃ V : H →L[ℂ] K,
      (∀ (x : H) (y : K), HasSum (fun i => ⟪y, U i x⟫) ⟪y, V x⟫) ∧
      (∀ x : H, HasSum (fun i => (ContinuousLinearMap.adjoint (U i) ∘L U i) x)
        ((ContinuousLinearMap.adjoint V ∘L V) x)) ∧
      (∀ y : K, HasSum (fun i => (U i ∘L ContinuousLinearMap.adjoint (U i)) y)
        ((V ∘L ContinuousLinearMap.adjoint V) y)) := by
  classical
  set p : ι → (H →L[ℂ] H) := fun i => ContinuousLinearMap.adjoint (U i) ∘L U i with hpdef
  set q : ι → (K →L[ℂ] K) := fun i => U i ∘L ContinuousLinearMap.adjoint (U i) with hqdef
  -- a partial isometry absorbs its initial projection
  have hUp : ∀ i, U i ∘L p i = U i := by
    intro i
    ext x
    have hidem : ∀ z : H, p i (p i z) = p i z := by
      intro z
      rw [← ContinuousLinearMap.mul_apply, (hproj i).isIdempotentElem]
    have hpy : p i (x - p i x) = 0 := by rw [map_sub, hidem, sub_self]
    have h1 : ‖U i (x - p i x)‖ ^ 2 = RCLike.re (⟪x - p i x, p i (x - p i x)⟫ : ℂ) := by
      have hinner : (⟪x - p i x, p i (x - p i x)⟫ : ℂ) =
          ⟪U i (x - p i x), U i (x - p i x)⟫ :=
        ContinuousLinearMap.adjoint_inner_right (U i) (x - p i x) (U i (x - p i x))
      rw [hinner]
      exact (inner_self_eq_norm_sq _).symm
    rw [hpy, inner_zero_right, map_zero] at h1
    have h2 : U i (x - p i x) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      exact norm_eq_zero.mp this
    rw [map_sub, sub_eq_zero] at h2
    exact h2.symm
  have hqU : ∀ i, q i ∘L U i = U i := by
    intro i
    rw [hqdef, ContinuousLinearMap.comp_assoc]
    exact hUp i
  have hpadj : ∀ i, p i ∘L ContinuousLinearMap.adjoint (U i) =
      ContinuousLinearMap.adjoint (U i) := by
    intro i
    have h := congrArg ContinuousLinearMap.adjoint (hUp i)
    rwa [ContinuousLinearMap.adjoint_comp, hpdef, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint] at h
  -- the final projections
  have hq : ∀ i, IsStarProjection (q i) := by
    intro i
    refine ⟨?_, ?_⟩
    · change q i * q i = q i
      ext y
      change U i (ContinuousLinearMap.adjoint (U i)
          (U i (ContinuousLinearMap.adjoint (U i) y))) =
        U i (ContinuousLinearMap.adjoint (U i) y)
      exact congrArg (fun T : H →L[ℂ] K => T (ContinuousLinearMap.adjoint (U i) y)) (hUp i)
    · change star (q i) = q i
      rw [ContinuousLinearMap.star_eq_adjoint]
      change ContinuousLinearMap.adjoint (U i ∘L ContinuousLinearMap.adjoint (U i)) =
        U i ∘L ContinuousLinearMap.adjoint (U i)
      rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  have hqadj : ∀ i, ContinuousLinearMap.adjoint (q i) = q i := fun i => by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (hq i).isSelfAdjoint
  have hUqadj : ∀ i, ContinuousLinearMap.adjoint (U i) ∘L q i =
      ContinuousLinearMap.adjoint (U i) := by
    intro i
    have h := congrArg ContinuousLinearMap.adjoint (hqU i)
    rwa [ContinuousLinearMap.adjoint_comp, hqadj] at h
  -- the cross terms vanish
  have hcross : Pairwise fun i j => ContinuousLinearMap.adjoint (U i) ∘L U j = 0 := by
    intro i j hij
    calc ContinuousLinearMap.adjoint (U i) ∘L U j
        = ContinuousLinearMap.adjoint (U i) ∘L (q j ∘L U j) := by rw [hqU j]
      _ = (ContinuousLinearMap.adjoint (U i) ∘L q j) ∘L U j := rfl
      _ = ((ContinuousLinearMap.adjoint (U i) ∘L q i) ∘L q j) ∘L U j := by rw [hUqadj i]
      _ = (ContinuousLinearMap.adjoint (U i) ∘L (q i ∘L q j)) ∘L U j := rfl
      _ = 0 := by rw [horthR hij]; simp
  have hcross' : Pairwise fun i j => U i ∘L ContinuousLinearMap.adjoint (U j) = 0 := by
    intro i j hij
    calc U i ∘L ContinuousLinearMap.adjoint (U j)
        = U i ∘L (p j ∘L ContinuousLinearMap.adjoint (U j)) := by rw [hpadj j]
      _ = (U i ∘L p j) ∘L ContinuousLinearMap.adjoint (U j) := rfl
      _ = ((U i ∘L p i) ∘L p j) ∘L ContinuousLinearMap.adjoint (U j) := by rw [hUp i]
      _ = (U i ∘L (p i ∘L p j)) ∘L ContinuousLinearMap.adjoint (U j) := rfl
      _ = 0 := by rw [horthL hij]; simp
  -- the two sums
  obtain ⟨V, hVsum⟩ := exists_sum_of_partial_isometries U hproj horthL hcross
  obtain ⟨W, hWsum⟩ := exists_sum_of_partial_isometries
    (fun i => ContinuousLinearMap.adjoint (U i))
    (by simpa only [ContinuousLinearMap.adjoint_adjoint] using hq)
    (by simpa only [ContinuousLinearMap.adjoint_adjoint] using horthR)
    (by simpa only [ContinuousLinearMap.adjoint_adjoint] using hcross')
  -- `W` is the adjoint of `V`
  have hWV : W = ContinuousLinearMap.adjoint V := by
    ext y
    refine ext_inner_left ℂ fun x => ?_
    have h1 : HasSum (fun i => (⟪x, ContinuousLinearMap.adjoint (U i) y⟫ : ℂ)) ⟪x, W y⟫ :=
      (innerSL ℂ x).hasSum (hWsum y)
    have h2 : HasSum (fun i => (⟪y, U i x⟫ : ℂ)) ⟪y, V x⟫ :=
      (innerSL ℂ y).hasSum (hVsum x)
    have h3 : HasSum (fun i => (⟪U i x, y⟫ : ℂ)) ⟪V x, y⟫ := by
      simpa only [RCLike.star_def, inner_conj_symm] using h2.star
    have h4 : HasSum (fun i => (⟪x, ContinuousLinearMap.adjoint (U i) y⟫ : ℂ)) ⟪V x, y⟫ := by
      simpa only [ContinuousLinearMap.adjoint_inner_right] using h3
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact h1.unique h4
  -- the three conclusions
  refine ⟨V, fun x y => (innerSL ℂ y).hasSum (hVsum x), fun x => ?_, fun y => ?_⟩
  · have hval : ∀ i, ContinuousLinearMap.adjoint (U i) (V x) =
        ContinuousLinearMap.adjoint (U i) (U i x) := by
      intro i
      have hA : HasSum (fun j => ContinuousLinearMap.adjoint (U i) (U j x))
          (ContinuousLinearMap.adjoint (U i) (V x)) :=
        (ContinuousLinearMap.adjoint (U i)).hasSum (hVsum x)
      have hB : HasSum (fun j => ContinuousLinearMap.adjoint (U i) (U j x))
          (ContinuousLinearMap.adjoint (U i) (U i x)) := by
        refine hasSum_single i fun j hj => ?_
        have := hcross (Ne.symm hj)
        exact congrArg (fun T : H →L[ℂ] H => T x) this
      exact hA.unique hB
    have := hWsum (V x)
    rw [hWV] at this
    simpa only [ContinuousLinearMap.comp_apply, hval] using this
  · have hval : ∀ i, U i (W y) = U i (ContinuousLinearMap.adjoint (U i) y) := by
      intro i
      have hA : HasSum (fun j => U i (ContinuousLinearMap.adjoint (U j) y)) (U i (W y)) :=
        (U i).hasSum (hWsum y)
      have hB : HasSum (fun j => U i (ContinuousLinearMap.adjoint (U j) y))
          (U i (ContinuousLinearMap.adjoint (U i) y)) := by
        refine hasSum_single i fun j hj => ?_
        have := hcross' (Ne.symm hj)
        exact congrArg (fun T : K →L[ℂ] K => T y) this
      exact hA.unique hB
    have hs := hVsum (W y)
    simp only [hval] at hs
    rw [hWV] at hs
    simpa only [ContinuousLinearMap.comp_apply] using hs

/-- **89V** (`sigma-weak-lemma-2`, vn.tex:6952, Lemma): let `Ω` be a
collection of np-functionals on a von Neumann algebra `A` with pairwise
orthogonal central carriers, and let `ρ : A → B(H)`, `π : A → B(K)` be
nmiu-maps such that each `ω ∈ Ω` is given by vectors `x_ω ∈ H` and
`y_ω ∈ K`.  Then there is a bounded `U : K → H` intertwining `π` and `ρ`
such that `U*U` is a projection in `π(A)^□` whose least
`Z(π(A)^□)`-majorant is `π(∑_ω ⌈⌈ω⌉⌉)`, and symmetrically for `UU*`. -/
theorem sigma_weak_lemma_2 (Ω : Set (NPFunctional A))
    (horth : ∀ ω ∈ Ω, ∀ ω' ∈ Ω, ω ≠ ω' →
      cceil (npCarrier ω) * cceil (npCarrier ω') = 0)
    (ρ : NMIUMap A (H →L[ℂ] H)) (π : NMIUMap A (K →L[ℂ] K))
    (x : Ω → H) (y : Ω → K)
    (hx : ∀ ω : Ω, ∀ a : A, (ω : NPFunctional A) a = ⟪x ω, ρ a (x ω)⟫)
    (hy : ∀ ω : Ω, ∀ a : A, (ω : NPFunctional A) a = ⟪y ω, π a (y ω)⟫) :
    ∃ U : K →L[ℂ] H,
      (∀ a : A, U ∘L π a = ρ a ∘L U) ∧
      IsStarProjection (ContinuousLinearMap.adjoint U ∘L U) ∧
      ContinuousLinearMap.adjoint U ∘L U ∈
        commutant (K →L[ℂ] K) (Set.range fun a : A => (π a : K →L[ℂ] K)) ∧
      IsLeast {p : K →L[ℂ] K |
          p ∈ commutant (K →L[ℂ] K)
            (Set.range fun a : A => (π a : K →L[ℂ] K)) ∧
          IsStarProjection p ∧
          (∀ b ∈ commutant (K →L[ℂ] K)
            (Set.range fun a : A => (π a : K →L[ℂ] K)), p * b = b * p) ∧
          ContinuousLinearMap.adjoint U ∘L U ≤ p}
        (π (projSup {c : A | ∃ ω ∈ Ω, c = cceil (npCarrier ω)})) :=
  sorry

/-- **89VII** (`sigma-weak-lemma`, vn.tex:7052, Corollary): let `A` be
(represented as) a von Neumann algebra of operators on `H` via an injective
nmiu-map `ρ` with von Neumann subalgebra range, and let
`π : A → B(K)` be a representation in which *every* np-functional of `A`
is a vector functional (a universal representation, cf. 48V).  Then there
is a bounded `U : K → H` such that `U*U` is a projection in `π(A)^□` whose
least `Z(π(A)^□)`-majorant is `1`, and `Uπ(a) = ρ(a)U` for all `a`. -/
theorem sigma_weak_lemma (ρ : NMIUMap A (H →L[ℂ] H))
    (hρ : Function.Injective ⇑ρ)
    (hR : IsVNSubalgebra (H →L[ℂ] H) ρ.toStarAlgHom.range)
    (π : NMIUMap A (K →L[ℂ] K))
    (huniv : ∀ ω : NPFunctional A, ∃ y : K, ∀ a : A, ω a = ⟪y, π a y⟫) :
    ∃ U : K →L[ℂ] H,
      (∀ a : A, U ∘L π a = ρ a ∘L U) ∧
      IsStarProjection (ContinuousLinearMap.adjoint U ∘L U) ∧
      ContinuousLinearMap.adjoint U ∘L U ∈
        commutant (K →L[ℂ] K) (Set.range fun a : A => (π a : K →L[ℂ] K)) ∧
      IsLeast {p : K →L[ℂ] K |
          p ∈ commutant (K →L[ℂ] K)
            (Set.range fun a : A => (π a : K →L[ℂ] K)) ∧
          IsStarProjection p ∧
          (∀ b ∈ commutant (K →L[ℂ] K)
            (Set.range fun a : A => (π a : K →L[ℂ] K)), p * b = b * p) ∧
          ContinuousLinearMap.adjoint U ∘L U ≤ p}
        1 :=
  sorry

/-- **89IX** (`normal-functional`, vn.tex:7089, Theorem): every
np-functional `ω` on a von Neumann subalgebra `A` of `B(H)` (given by an
injective nmiu-map `ρ : A → B(H)` with von Neumann subalgebra range) is of
the form `ω = ∑ₙ ⟨xₙ,(·)xₙ⟩` for some `x₁, x₂, … ∈ H` with
`∑ₙ ‖xₙ‖² < ∞`. -/
theorem normal_functional (ρ : NMIUMap A (H →L[ℂ] H))
    (hρ : Function.Injective ⇑ρ)
    (hR : IsVNSubalgebra (H →L[ℂ] H) ρ.toStarAlgHom.range)
    (ω : NPFunctional A) :
    ∃ x : ℕ → H, (Summable fun n => ‖x n‖ ^ 2) ∧
      ∀ a : A, HasSum (fun n => ⟪x n, ρ a (x n)⟫) (ω a) :=
  sorry

end BH

section Permanence

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B]

/-- **89XI** (`functional-permanence`, vn.tex:7155, Corollary), part 1: for
a von Neumann subalgebra `A` of `B` (an injective nmiu-map `ρ : A → B`
with von Neumann subalgebra range), every np-functional `ω` on `A` extends
to an np-functional `ξ` on `B`: `ξ ∘ ρ = ω`. -/
theorem functional_permanence_1 (ρ : NMIUMap A B)
    (hρ : Function.Injective ⇑ρ)
    (hR : IsVNSubalgebra B ρ.toStarAlgHom.range) (ω : NPFunctional A) :
    ∃ ξ : NPFunctional B, ∀ a : A, ξ (ρ a) = ω a :=
  sorry

/-- **89XI** (`functional-permanence`, vn.tex:7155, Corollary), part 2
(**ultraweak permanence**): the ultraweak topology of a von Neumann
subalgebra `A` of `B` is the restriction of the ultraweak topology of
`B`. -/
theorem functional_permanence_2 (ρ : NMIUMap A B)
    (hρ : Function.Injective ⇑ρ)
    (hR : IsVNSubalgebra B ρ.toStarAlgHom.range) :
    ultraweak A = TopologicalSpace.induced ⇑ρ (ultraweak B) :=
  sorry

/-- **89XI** (`functional-permanence`, vn.tex:7155, Corollary), part 3
(**ultrastrong permanence**): likewise for the ultrastrong topologies. -/
theorem functional_permanence_3 (ρ : NMIUMap A B)
    (hρ : Function.Injective ⇑ρ)
    (hR : IsVNSubalgebra B ρ.toStarAlgHom.range) :
    ultrastrong A = TopologicalSpace.induced ⇑ρ (ultrastrong B) :=
  sorry

/-- **89XII** (`functional-extension`, vn.tex:7175, Exercise): every
np-functional `ω` on `A` extends along any injective nmiu-map
`ρ : A → B`: there is an np-functional `ω'` on `B` with `ω' ∘ ρ = ω`.
(The thesis writes `ρ ∘ ω' = ω`, an obvious slip.) -/
theorem functional_extension (ρ : NMIUMap A B)
    (hρ : Function.Injective ⇑ρ) (ω : NPFunctional A) :
    ∃ ω' : NPFunctional B, ∀ a : A, ω' (ρ a) = ω a :=
  sorry

/-! ## Parsec 900: centre separating collections

**90I** (vn.tex:7191): introduction — nothing to formalize. -/

/-- **90II** (`vn-center-separating-fundamental`, vn.tex:7206,
Proposition), part 1: for a centre separating collection `Ω` of
np-functionals and an ultrastrongly dense subset `S` of a von Neumann
algebra, the collection `Ω' = {ω(s*(·)s) : ω ∈ Ω, s ∈ S}` is order
separating. -/
theorem vn_center_separating_fundamental_1 (Ω : Set (NPFunctional A))
    (hΩ : CentreSeparating A Ω) (S : Set A)
    (hS : @Dense A (ultrastrong A) S) (a b : A) (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b)
    (h : ∀ ω ∈ Ω, ∀ s ∈ S, ω (star s * a * s) ≤ ω (star s * b * s)) :
    a ≤ b :=
  sorry

/-- **90II** (`vn-center-separating-fundamental`, vn.tex:7206,
Proposition), part 2: the finite sums `Ω''` of members of `Ω'` are
operator-norm dense in the positive part of the predual: every
np-functional `f` is an operator-norm limit of sums
`∑ₖ ωₖ(sₖ*(·)sₖ)` with `ωₖ ∈ Ω`, `sₖ ∈ S`. -/
theorem vn_center_separating_fundamental_2 (Ω : Set (NPFunctional A))
    (hΩ : CentreSeparating A Ω) (S : Set A)
    (hS : @Dense A (ultrastrong A) S) (f : NPFunctional A) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ (n : ℕ) (ω : Fin n → NPFunctional A) (s : Fin n → A),
      (∀ k, ω k ∈ Ω ∧ s k ∈ S) ∧
      ∀ a : A, ‖f a - ∑ k, (ω k) (star (s k) * a * s k)‖ ≤ ε * ‖a‖ :=
  sorry

/-! **91I** (vn.tex:7311): closing remarks of the chapter — nothing to
formalize. -/

end Permanence

end Theses.A.VN
