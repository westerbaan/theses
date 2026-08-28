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

See `Theses/A/VN/Basic.lean` for the topologies, and
`Theses/A/VN/Projections.lean` for `ceil`, `carrier`, `cceil`, `commutant`
and `projSup`.
-/
import Theses.A.VN.Division
import Theses.A.CStar.Matrices

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra ENNReal
open Filter Topology Theses Theses.A.CStar

universe u

namespace Theses.A.VN

variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-! ## Von Neumann subalgebras as bundled algebras

`VNSub A S hS` (a von Neumann subalgebra `S ⊆ A` bundled as a von Neumann
algebra in its own right) was **moved upstream to `A/VN/Division.lean`** in
session 79, where **84bV** `ha_equalisers` needs it; it is unchanged, and
still lives in the `Theses.A.VN` namespace, so every use below and
downstream is unaffected. -/



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

/-- **86II** (`positive-functional-criterion`, vn.tex:6293, Lemma): a
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

/-- **86VI** (`vn-ball-extreme-point`, vn.tex:6348, Lemma): an extreme
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

/-! ### Tools for **86IX**: the ultraweak topology is a locally convex TVS

The Krein–Milman theorem needs `A` with the ultraweak topology to be a
Hausdorff locally convex topological vector space over `ℝ`.  Hausdorffness is
**44XI**.1; the other three properties follow formally, the ultraweak topology
being an infimum of topologies induced by linear maps into `ℂ`. -/

omit [StarOrderedRing A] in
/-- The ultraweak topology makes `A` a topological additive group: it is the
infimum of the topologies induced by the (additive) np-functionals. -/
theorem ultraweak_isTopologicalAddGroup : @IsTopologicalAddGroup A (ultraweak A) _ := by
  rw [ultraweak]
  refine topologicalAddGroup_iInf fun ω => ?_
  exact topologicalAddGroup_induced ω.toPositiveLinearMap.toLinearMap

omit [StarOrderedRing A] in
/-- Scalar multiplication is ultraweakly continuous. -/
theorem ultraweak_continuousSMul : @ContinuousSMul ℝ A _ _ (ultraweak A) := by
  rw [ultraweak]
  refine continuousSMul_iInf fun ω => ?_
  exact continuousSMul_induced
    (LinearMap.restrictScalars ℝ ω.toPositiveLinearMap.toLinearMap)

omit [StarOrderedRing A] in
/-- The ultraweak topology is locally convex: `ℂ` is, and local convexity is
preserved by induced topologies and by infima. -/
theorem ultraweak_locallyConvexSpace : @LocallyConvexSpace ℝ A _ _ _ _ (ultraweak A) := by
  rw [ultraweak]
  refine LocallyConvexSpace.iInf fun ω => ?_
  exact LocallyConvexSpace.induced
    (LinearMap.restrictScalars ℝ ω.toPositiveLinearMap.toLinearMap)

/-- Krein–Milman step of **86IX**. -/
theorem exists_extremePoint_max (f : A →ₗ[ℂ] ℂ)
    (hf : @ContinuousOn A ℂ (ultraweak A) _ ⇑f (Metric.closedBall 0 1)) :
    ∃ (M : ℝ) (u : A), 0 ≤ M ∧
      u ∈ Set.extremePoints ℝ (Metric.closedBall (0 : A) 1) ∧
      f u = (M : ℂ) ∧ ∀ z ∈ Metric.closedBall (0 : A) 1, ‖f z‖ ≤ M := by
  letI : TopologicalSpace A := ultraweak A
  haveI : T2Space A := vn_positive_basic_1.1
  haveI : IsTopologicalAddGroup A := ultraweak_isTopologicalAddGroup
  haveI : ContinuousSMul ℝ A := ultraweak_continuousSMul
  haveI : LocallyConvexSpace ℝ A := ultraweak_locallyConvexSpace
  have h0 : (0 : A) ∈ Metric.closedBall (0 : A) 1 := Metric.mem_closedBall_self zero_le_one
  have hballc : IsCompact (Metric.closedBall (0 : A) 1) := vn_ball_compact
  have hballcl : IsClosed (Metric.closedBall (0 : A) 1) :=
    ultraclosed _ (convex_closedBall (0 : A) 1) vn_positive_basic_3
  obtain ⟨a₀, ha₀, hmax⟩ := hballc.exists_isMaxOn ⟨0, h0⟩
    (Complex.continuous_re.comp_continuousOn hf)
  set M : ℝ := (f a₀).re with hMdef
  have hM0 : 0 ≤ M := by simpa using hmax h0
  have hMle : ∀ z ∈ Metric.closedBall (0 : A) 1, ‖f z‖ ≤ M := by
    intro z hz
    rcases eq_or_ne (f z) 0 with h | h
    · rw [h, norm_zero]; exact hM0
    · set l : ℂ := (‖f z‖ : ℂ) / f z with hl
      have hlnorm : ‖l‖ = 1 := by
        rw [hl, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _)]
        field_simp
      have hlz : l • z ∈ Metric.closedBall (0 : A) 1 := by
        rw [mem_closedBall_zero_iff, norm_smul, hlnorm, one_mul]
        exact mem_closedBall_zero_iff.mp hz
      have hval : f (l • z) = (‖f z‖ : ℂ) := by
        rw [map_smul, smul_eq_mul, hl]
        field_simp
      have hle := hmax hlz
      simp only [Set.mem_setOf_eq, Function.comp_apply, hval, Complex.ofReal_re] at hle
      exact hle
  have hkey : ∀ x ∈ Metric.closedBall (0 : A) 1, (f x).re = M → f x = (M : ℂ) := by
    intro x hx hre
    have h1 : ‖f x‖ ≤ M := hMle x hx
    have h2 : (f x).re = ‖f x‖ := le_antisymm (Complex.re_le_norm _) (by rw [hre]; exact h1)
    have h3 : (0 : ℂ) ≤ f x := Complex.re_eq_norm.mp h2
    exact Complex.ext (by simpa using hre) (by simpa using ((Complex.le_def.mp h3).2).symm)
  have hfa₀ : f a₀ = (M : ℂ) := hkey a₀ ha₀ rfl
  set F : Set A := Metric.closedBall (0 : A) 1 ∩ ⇑f ⁻¹' {(M : ℂ)} with hFdef
  have hFcl : IsClosed F := hf.preimage_isClosed_of_isClosed hballcl isClosed_singleton
  have hFcomp : IsCompact F := hballc.of_isClosed_subset hFcl Set.inter_subset_left
  obtain ⟨u, hu⟩ := hFcomp.extremePoints_nonempty ⟨a₀, ha₀, hfa₀⟩
  refine ⟨M, u, hM0, ⟨hu.1.1, ?_⟩, hu.1.2, hMle⟩
  intro x₁ hx₁ x₂ hx₂ hseg
  obtain ⟨t₁, t₂, ht₁, ht₂, hts, hcomb⟩ := hseg
  have hfu : f u = (M : ℂ) := hu.1.2
  have hre1 : (f x₁).re ≤ M := (Complex.re_le_norm _).trans (hMle x₁ hx₁)
  have hre2 : (f x₂).re ≤ M := (Complex.re_le_norm _).trans (hMle x₂ hx₂)
  have hcx : f u = (t₁ : ℂ) * f x₁ + (t₂ : ℂ) * f x₂ := by
    rw [← hcomb, map_add, ← Complex.coe_smul, ← Complex.coe_smul, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul]
  have hsum : t₁ * (f x₁).re + t₂ * (f x₂).re = M := by
    have := congrArg Complex.re hcx
    simpa [hfu] using this.symm
  have he1 : (f x₁).re = M := by nlinarith
  have he2 : (f x₂).re = M := by nlinarith
  exact hu.2 ⟨hx₁, hkey x₁ hx₁ he1⟩ ⟨hx₂, hkey x₂ hx₂ he2⟩ ⟨t₁, t₂, ht₁, ht₂, hts, hcomb⟩

/-- Cauchy–Schwarz consequence: a positive functional killing a projection
kills every product with it. -/
theorem posFunctional_mul_eq_zero (g : A →L[ℂ] ℂ)
    (hg : ∀ a : A, 0 ≤ a → 0 ≤ g a) (q : A) (hq : IsStarProjection q)
    (hq0 : g q = 0) :
    (∀ b : A, g (q * b) = 0) ∧ (∀ b : A, g (b * q) = 0) := by
  have hω : IsPositiveMap (g : A →ₗ[ℂ] ℂ) := hg
  have hqs : star q = q := hq.isSelfAdjoint.star_eq
  have hqq : star q * q = q := by rw [hqs]; exact hq.isIdempotentElem.eq
  have hzero : ∀ z : A, ((‖g z‖ : ℂ)) ^ 2 ≤ 0 → g z = 0 := by
    intro z hz
    have hle : ((‖g z‖ ^ 2 : ℝ) : ℂ) ≤ 0 := by push_cast; exact hz
    have h2 : (‖g z‖ : ℝ) ^ 2 ≤ 0 := by
      exact_mod_cast Complex.real_le_real.mp (by simpa using hle)
    have : ‖g z‖ = 0 := by nlinarith [norm_nonneg (g z)]
    exact norm_eq_zero.mp this
  constructor
  · intro b
    have hcs := omega_norm_basic_1 (g : A →ₗ[ℂ] ℂ) hω q b
    simp only [ContinuousLinearMap.coe_coe] at hcs
    rw [hqs, hq.isIdempotentElem.eq, hq0, zero_mul] at hcs
    exact hzero _ hcs
  · intro b
    have hcs := omega_norm_basic_1 (g : A →ₗ[ℂ] ℂ) hω (star b) q
    simp only [ContinuousLinearMap.coe_coe] at hcs
    rw [star_star, hqq, hq0, mul_zero] at hcs
    exact hzero _ hcs

private theorem np_real_smul (ω : NPFunctional A) (r : ℝ) (a : A) :
    (ω (r • a) : ℂ) = (r : ℂ) * ω a := by
  rw [← Complex.coe_smul]
  exact (map_smul ω.toPositiveLinearMap _ _).trans (smul_eq_mul _ _)

/-- **44XV**, (2) ⇒ (3), for functionals: a positive linear functional that
is ultraweakly continuous on the effects is normal.  This is the general
`Theses.A.VN.preservesDirSups_of_continuousOn_effects` (`A/VN/Basic.lean`)
with target `B = ℂ`, which is a von Neumann algebra whose ultraweak topology
is its usual one (`ultraweak_complex`). -/
theorem preservesDirSups_of_continuousOn_effects_functional (g : A →ₚ[ℂ] ℂ)
    (h : @ContinuousOn A ℂ (ultraweak A) _ ⇑g (effects A)) :
    PreservesDirSups ⇑g :=
  preservesDirSups_of_continuousOn_effects g (by rwa [ultraweak_complex])


/-- **86IX** (`polar-decomposition-of-functional`, vn.tex:6401, Theorem
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
      (∀ a : A, 0 ≤ a → 0 ≤ f (a * u)) := by
  obtain ⟨M, u, hM0, huext, hfu, hMle⟩ := exists_extremePoint_max f hf
  have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.mp huext.1
  have hbound : ∀ z : A, ‖f z‖ ≤ M * ‖z‖ := by
    intro z
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · have hzn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
      have hmem : ((‖z‖⁻¹ : ℝ) : ℂ) • z ∈ Metric.closedBall (0 : A) 1 := by
        rw [mem_closedBall_zero_iff, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hzn), inv_mul_cancel₀ (ne_of_gt hzn)]
      have h := hMle _ hmem
      rw [map_smul, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hzn)] at h
      simpa [mul_comm] using (inv_mul_le_iff₀ hzn).mp h
  set fc : A →L[ℂ] ℂ := f.mkContinuous M hbound with hfcdef
  have hfcapp : ∀ z : A, fc z = f z := fun _ => rfl
  obtain ⟨hproj, hann⟩ := vn_ball_extreme_point u huext
  have hpi : IsPartialIsometry A u :=
    ((partial_isometry_equivalents u).out 1 0).mp hproj
  have huu : u * star u * u = u := ((partial_isometry_equivalents u).out 1 2).mp hproj
  have hproje : IsStarProjection (u * star u) :=
    ((partial_isometry_equivalents u).out 1 3).mp hproj
  -- `g = f(u ·)` and `g' = f((·)u)` are positive
  set g : A →L[ℂ] ℂ := fc.comp (ContinuousLinearMap.mul ℂ A u) with hgdef
  have hgapp : ∀ a : A, g a = f (u * a) := fun _ => rfl
  set g' : A →L[ℂ] ℂ := fc.comp ((ContinuousLinearMap.mul ℂ A).flip u) with hg'def
  have hg'app : ∀ a : A, g' a = f (a * u) := fun _ => rfl
  have hgnorm : ‖g‖ ≤ M := by
    refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun a => ?_
    rw [hgapp]
    calc ‖f (u * a)‖ ≤ M * ‖u * a‖ := hbound _
      _ ≤ M * (‖u‖ * ‖a‖) := by gcongr; exact norm_mul_le _ _
      _ ≤ M * (1 * ‖a‖) := by gcongr
      _ = M * ‖a‖ := by ring
  have hg'norm : ‖g'‖ ≤ M := by
    refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun a => ?_
    rw [hg'app]
    calc ‖f (a * u)‖ ≤ M * ‖a * u‖ := hbound _
      _ ≤ M * (‖a‖ * ‖u‖) := by gcongr; exact norm_mul_le _ _
      _ ≤ M * (‖a‖ * 1) := by gcongr
      _ = M * ‖a‖ := by ring
  have hgpos : ∀ a : A, 0 ≤ a → 0 ≤ g a := by
    refine (positive_functional_criterion g).mpr ?_
    have h1 : g 1 = (M : ℂ) := by rw [hgapp, mul_one, hfu]
    rw [h1]
    exact ⟨Complex.ofReal_im M, by simpa using hgnorm⟩
  have hg'pos : ∀ a : A, 0 ≤ a → 0 ≤ g' a := by
    refine (positive_functional_criterion g').mpr ?_
    have h1 : g' 1 = (M : ℂ) := by rw [hg'app, one_mul, hfu]
    rw [h1]
    exact ⟨Complex.ofReal_im M, by simpa using hg'norm⟩
  -- `g` kills `(u*u)^⊥`
  have hcompl : IsStarProjection (1 - star u * u) := hproj.one_sub
  have hg0 : g (1 - star u * u) = 0 := by
    rw [hgapp, mul_sub, mul_one, ← mul_assoc, huu, sub_self, map_zero]
  have hgz := posFunctional_mul_eq_zero g hgpos _ hcompl hg0
  have hcomple : IsStarProjection (1 - u * star u) := hproje.one_sub
  have hg'0 : g' (1 - u * star u) = 0 := by
    rw [hg'app, sub_mul, one_mul, huu, sub_self, map_zero]
  have hg'z := posFunctional_mul_eq_zero g' hg'pos _ hcomple hg'0
  -- `f(u b (u*u)) = f(u b)`
  have hR : ∀ b : A, f (u * b * (star u * u)) = f (u * b) := by
    intro b
    have h := hgz.2 b
    rw [hgapp, show u * (b * (1 - star u * u)) = u * b - u * b * (star u * u) by
      noncomm_ring, map_sub, sub_eq_zero] at h
    exact h.symm
  -- `f((1-uu*) b u) = 0`, i.e. `f(b u) = f(uu* b u)`
  have hL : ∀ b : A, f (u * star u * b * u) = f (b * u) := by
    intro b
    have h := hg'z.1 b
    rw [hg'app, show (1 - u * star u) * b * u = b * u - u * star u * b * u by
      noncomm_ring, map_sub, sub_eq_zero] at h
    exact h.symm
  have hexpand : ∀ a : A, f a - f (u * star u * a) - f (a * (star u * u))
      + f (u * star u * a * (star u * u)) = 0 := by
    intro a
    have h0 : f ((1 - u * star u) * a * (1 - star u * u)) = 0 := by
      rw [hann a, map_zero]
    rw [show (1 - u * star u) * a * (1 - star u * u)
        = a - u * star u * a - a * (star u * u) + u * star u * a * (star u * u) by
      noncomm_ring, map_add, map_sub, map_sub] at h0
    exact h0
  have hA : ∀ a : A, f (u * star u * a * (star u * u)) = f (u * star u * a) := by
    intro a
    have h := hR (star u * a)
    rw [show u * (star u * a) * (star u * u) = u * star u * a * (star u * u) by
      noncomm_ring, show u * (star u * a) = u * star u * a by noncomm_ring] at h
    exact h
  have hB : ∀ a : A, f (u * star u * a * (star u * u)) = f (a * (star u * u)) := by
    intro a
    have h := hL (a * star u)
    rw [show u * star u * (a * star u) * u = u * star u * a * (star u * u) by
      noncomm_ring, show a * star u * u = a * (star u * u) by noncomm_ring] at h
    exact h
  refine ⟨u, hpi, fun a => ?_, fun a => ?_, fun a ha => by rw [← hgapp]; exact hgpos a ha,
    fun a ha => by rw [← hg'app]; exact hg'pos a ha⟩
  · have h := hexpand a
    rw [hB a] at h
    linear_combination h
  · have h := hexpand a
    rw [hA a] at h
    linear_combination h

/-- **86XII** (`uwcont-on-ball`, vn.tex:6463, Corollary): a functional on a
von Neumann algebra that is ultraweakly continuous on the unit ball is
ultraweakly continuous. -/
theorem uwcont_on_ball (f : A →ₗ[ℂ] ℂ)
    (hf : @ContinuousOn A ℂ (ultraweak A) _ ⇑f (Metric.closedBall 0 1)) :
    @Continuous A ℂ (ultraweak A) _ ⇑f := by
  obtain ⟨u, hpi, h1, h2, hpos, hpos'⟩ := polar_decomposition_of_functional f hf
  have hproj : IsStarProjection (star u * u) :=
    ((partial_isometry_equivalents u).out 0 1).mp hpi
  have hu1 : ‖u‖ ≤ 1 := by
    have h : ‖u‖ * ‖u‖ ≤ 1 := by
      rw [← CStarRing.norm_star_mul_self]
      exact norm_starProjection_le_one hproj
    nlinarith [norm_nonneg u]
  let g : A →ₚ[ℂ] ℂ :=
    { toFun := fun a => f (u * a)
      map_add' := fun x y => by simp only [mul_add, map_add]
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, mul_smul_comm, map_smul, smul_eq_mul]
      monotone' := fun a b hab => by
        have h0 : (0 : ℂ) ≤ f (u * (b - a)) := hpos _ (sub_nonneg.mpr hab)
        rw [mul_sub, map_sub, sub_nonneg] at h0
        exact h0 }
  have hgapp : ∀ a : A, (g a : ℂ) = f (u * a) := fun _ => rfl
  have hcont : @ContinuousOn A ℂ (ultraweak A) _ ⇑g (effects A) := by
    letI : TopologicalSpace A := ultraweak A
    have hmul : Continuous (fun a : A => u * a) := (mult_uws_cont u).1
    have hmaps : Set.MapsTo (fun a : A => u * a) (effects A) (Metric.closedBall 0 1) := by
      intro a ha
      rw [mem_closedBall_zero_iff]
      calc ‖u * a‖ ≤ ‖u‖ * ‖a‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := by
            gcongr
            exact (CStarAlgebra.norm_le_one_iff_of_nonneg a ha.1).mpr ha.2
        _ = 1 := by norm_num
    exact hf.comp hmul.continuousOn hmaps
  have hnormal : PreservesDirSups ⇑g :=
    preservesDirSups_of_continuousOn_effects_functional g hcont
  have hgc : @Continuous A ℂ (ultraweak A) _ ⇑g :=
    continuous_ultraweak_npFunctional ⟨g, hnormal⟩
  have hfg : ∀ a : A, (g (star u * a) : ℂ) = f a := by
    intro a
    rw [hgapp, ← mul_assoc, ← h1 a]
  have hfinal : @Continuous A ℂ (ultraweak A) _ (fun a : A => (g (star u * a) : ℂ)) := by
    letI : TopologicalSpace A := ultraweak A
    exact hgc.comp ((mult_uws_cont (star u)).1)
  letI : TopologicalSpace A := ultraweak A
  exact hfinal.congr hfg

/-- **86XIV** (`functional-norm`, vn.tex:6488, Lemma): for a normal
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
/-- **87I** (vn.tex:6508, Definition): the **predual** `A_*` of a von
Neumann algebra: the (normed vector) space of ultraweakly continuous
functionals on `A`, rendered as a subset of the continuous dual.
(**87II**, Remark: Sakai's theorem `(A_*)* ≅ A` is neither needed nor
converted.) -/
def predual : Set (A →L[ℂ] ℂ) :=
  {f : A →L[ℂ] ℂ | @Continuous A ℂ (ultraweak A) _ ⇑f}

/-- **87III** (`predual-complete`, vn.tex:6537, Proposition): the predual
of a von Neumann algebra is complete with respect to the operator norm. -/
theorem predual_complete : IsComplete (predual A) := by
  intro F hF hFle
  haveI : F.NeBot := hF.1
  obtain ⟨x, hx⟩ := CompleteSpace.complete hF
  refine ⟨x, ?_, hx⟩
  have hmemF : predual A ∈ F := le_principal_iff.mp hFle
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ g : A →L[ℂ] ℂ,
      (@Continuous A ℂ (ultraweak A) _ ⇑g) ∧ ‖x - g‖ ≤ ε := by
    intro ε hε
    have h1 : Metric.closedBall x ε ∈ F := hx (Metric.closedBall_mem_nhds x hε)
    obtain ⟨g, hg1, hg2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 hmemF)
    refine ⟨g, hg2, ?_⟩
    rw [← dist_eq_norm, dist_comm]
    exact Metric.mem_closedBall.mp hg1
  choose G hGcont hGnorm using fun n : ℕ => happrox (1 / (n + 1)) (by positivity)
  have hcontOn : @ContinuousOn A ℂ (ultraweak A) _ ⇑x (Metric.closedBall 0 1) := by
    letI : TopologicalSpace A := ultraweak A
    have huc : TendstoUniformlyOn (fun n : ℕ => ⇑(G n)) ⇑x atTop
        (Metric.closedBall (0 : A) 1) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      refine Eventually.mono (eventually_ge_atTop N) fun n hn a ha => ?_
      have h1 : ‖x a - G n a‖ ≤ 1 / (n + 1) := by
        have h2 := (x - G n).le_opNorm a
        have h3 : ‖a‖ ≤ 1 := mem_closedBall_zero_iff.mp ha
        have h4 : ((x - G n) a) = x a - G n a := rfl
        rw [h4] at h2
        calc ‖x a - G n a‖ ≤ ‖x - G n‖ * ‖a‖ := h2
          _ ≤ (1 / (n + 1)) * 1 :=
              mul_le_mul (hGnorm n) h3 (norm_nonneg a) (by positivity)
          _ = 1 / (n + 1) := by ring
      have h5 : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      rw [dist_eq_norm]
      linarith
    exact huc.continuousOn
      ((Eventually.of_forall fun n => (hGcont n).continuousOn).frequently)
  show @Continuous A ℂ (ultraweak A) _ ⇑x
  exact uwcont_on_ball (x : A →ₗ[ℂ] ℂ) hcontOn

/-! **87V** (vn.tex:6548): motivation for the next lemma — nothing to
formalize. -/

/-- **87VI** (`norm-predual`, vn.tex:6591, Lemma):
`‖a‖ = sup {|f(a)| : f ∈ (A_*)₁}` for every element `a` of a von Neumann
algebra. -/
theorem norm_predual (a : A) :
    IsLUB {r : ℝ | ∃ f ∈ predual A, ‖f‖ ≤ 1 ∧ r = ‖f a‖} ‖a‖ := by
  constructor
  · rintro r ⟨f, -, hf1, rfl⟩
    calc ‖f a‖ ≤ ‖f‖ * ‖a‖ := f.le_opNorm a
      _ ≤ 1 * ‖a‖ := by gcongr
      _ = ‖a‖ := one_mul _
  intro b hb
  have hb0 : (0 : ℝ) ≤ b := by
    refine hb ⟨0, ?_, by simp, by simp⟩
    show @Continuous A ℂ (ultraweak A) _ ⇑(0 : A →L[ℂ] ℂ)
    letI : TopologicalSpace A := ultraweak A
    exact continuous_const
  obtain ⟨hpi, hstaru, -⟩ := polar_decomposition_1 a
  obtain ⟨-, hus, -⟩ := polar_decomposition a
  obtain ⟨hspos, hssa, hss, -, -, hse⟩ := sqrt_star_self_spec a
  set u : A := polar a with hudef
  set s : A := CFC.sqrt (star a * a) with hsdef
  have hprojuu : IsStarProjection (star u * u) :=
    ((partial_isometry_equivalents u).out 0 1).mp hpi
  have hu1 : ‖u‖ ≤ 1 := by
    have h : ‖u‖ * ‖u‖ ≤ 1 := by
      rw [← CStarRing.norm_star_mul_self]
      exact norm_starProjection_le_one hprojuu
    nlinarith [norm_nonneg u]
  have hsu : star u * a = s := by
    have hsp : suppProj a * s = s := by
      have h := congrArg star hse
      rwa [star_mul, hssa, (((ceill_basic_1 a).1.1).isSelfAdjoint).star_eq] at h
    rw [hus, ← mul_assoc, hstaru, hsp]
  have hone_nonneg : ∀ ω : NPFunctional A, (0 : ℂ) ≤ ω 1 := fun ω =>
    npFunctional_nonneg ω (zero_le_one (α := A))
  -- Cauchy–Schwarz estimate: `|ω([a]* z)| ≤ ω(1)‖z‖`
  have hkey : ∀ (ω : NPFunctional A) (z : A),
      ‖(ω (star u * z) : ℂ)‖ ≤ (ω 1).re * ‖z‖ := by
    intro ω z
    have h1 : ‖(ω (star u * z) : ℂ)‖ ≤ omegaNorm A ω u * omegaNorm A ω z :=
      norm_apply_star_mul_le ω u z
    have hnn : (0 : ℝ) ≤ (ω 1).re := (Complex.le_def.mp (hone_nonneg ω)).1
    have h2 : omegaNorm A ω u ≤ Real.sqrt (ω 1).re := by
      have h := omegaNorm_mul_le ω u 1
      rw [mul_one, omegaNorm_one] at h
      refine h.trans ?_
      nlinarith [Real.sqrt_nonneg (ω 1).re]
    have h3 : omegaNorm A ω z ≤ ‖z‖ * Real.sqrt (ω 1).re := by
      have h := omegaNorm_mul_le ω z 1
      rwa [mul_one, omegaNorm_one] at h
    calc ‖(ω (star u * z) : ℂ)‖ ≤ omegaNorm A ω u * omegaNorm A ω z := h1
      _ ≤ Real.sqrt (ω 1).re * (‖z‖ * Real.sqrt (ω 1).re) :=
          mul_le_mul h2 h3 (omegaNorm_nonneg ω z) (Real.sqrt_nonneg _)
      _ = (Real.sqrt (ω 1).re * Real.sqrt (ω 1).re) * ‖z‖ := by ring
      _ = (ω 1).re * ‖z‖ := by rw [Real.mul_self_sqrt hnn]
  -- every np-functional satisfies `ω(√(a*a)) ≤ ω(b·1)`
  have hmain : ∀ ω : NPFunctional A, (ω s : ℂ) ≤ ω ((b : ℝ) • (1 : A)) := by
    intro ω
    have hnn : (0 : ℝ) ≤ (ω 1).re := (Complex.le_def.mp (hone_nonneg ω)).1
    have him1 : (ω 1 : ℂ).im = 0 := ((Complex.le_def.mp (hone_nonneg ω)).2).symm
    have hsnn : (0 : ℂ) ≤ ω s := npFunctional_nonneg ω hspos
    have hsre : ‖(ω s : ℂ)‖ = (ω s).re := (Complex.re_eq_norm.mpr hsnn).symm
    have hbound : ‖(ω s : ℂ)‖ ≤ b * (ω 1).re := by
      rcases eq_or_lt_of_le hnn with hr0 | hrpos
      · have h0 := hkey ω a
        rw [hsu] at h0
        rw [← hr0] at h0 ⊢
        simpa using h0
      · set L : A →ₗ[ℂ] ℂ := (((((ω 1).re)⁻¹ : ℝ) : ℂ) •
          (ω.toPositiveLinearMap.toLinearMap.comp (LinearMap.mulLeft ℂ (star u))))
          with hLdef
        have hLapp : ∀ z : A, L z = ((((ω 1).re)⁻¹ : ℝ) : ℂ) * ω (star u * z) :=
          fun _ => rfl
        have hLb : ∀ z : A, ‖L z‖ ≤ 1 * ‖z‖ := by
          intro z
          rw [hLapp, norm_mul, one_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hrpos)]
          have h := hkey ω z
          rw [inv_mul_le_iff₀ hrpos]
          exact h
        set fc : A →L[ℂ] ℂ := L.mkContinuous 1 hLb with hfcdef
        have hfcnorm : ‖fc‖ ≤ 1 := L.mkContinuous_norm_le zero_le_one hLb
        have hfcpred : fc ∈ predual A := by
          show @Continuous A ℂ (ultraweak A) _ ⇑fc
          letI : TopologicalSpace A := ultraweak A
          exact ((continuous_ultraweak_npFunctional ω).comp
            ((mult_uws_cont (star u)).1)).const_mul _
        have hle := hb (show ‖fc a‖ ∈ _ from ⟨fc, hfcpred, hfcnorm, rfl⟩)
        have hfca : ‖fc a‖ = ((ω 1).re)⁻¹ * ‖(ω s : ℂ)‖ := by
          show ‖L a‖ = _
          rw [hLapp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hrpos), hsu]
        rw [hfca, inv_mul_le_iff₀ hrpos] at hle
        simpa [mul_comm] using hle
    have him : (ω s : ℂ).im = 0 := ((Complex.le_def.mp hsnn).2).symm
    rw [np_real_smul ω b 1]
    refine Complex.le_def.mpr ⟨?_, ?_⟩
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        him1, mul_zero, sub_zero]
      rw [← hsre]
      exact hbound
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        him1, mul_zero, add_zero, him]
  have hbsa : IsSelfAdjoint ((b : ℝ) • (1 : A)) :=
    (IsSelfAdjoint.all (b : ℝ)).smul (IsSelfAdjoint.one A)
  have hsle : s ≤ (b : ℝ) • (1 : A) :=
    np_orderSeparating s _ (IsSelfAdjoint.of_nonneg hspos) hbsa hmain
  have hnorms : ‖s‖ ≤ b := by
    rcases eq_or_lt_of_le hb0 with hb0' | hbpos
    · have hz : s = 0 := by
        refine le_antisymm ?_ hspos
        rw [← hb0'] at hsle
        simpa using hsle
      rw [hz, norm_zero, ← hb0']
    · have h1 : (b⁻¹ : ℝ) • s ≤ 1 := by
        have h := smul_le_smul_of_nonneg_left hsle (inv_nonneg.mpr hb0)
        rwa [smul_smul, inv_mul_cancel₀ hbpos.ne', one_smul] at h
      have h2 : (0 : A) ≤ (b⁻¹ : ℝ) • s := smul_nonneg (inv_nonneg.mpr hb0) hspos
      have h3 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ h2).mpr h1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbpos),
        inv_mul_le_iff₀ hbpos] at h3
      simpa [mul_comm] using h3
  have hnorm_eq : ‖a‖ = ‖s‖ := by
    have h1 : ‖a‖ * ‖a‖ = ‖s‖ * ‖s‖ := by
      rw [← CStarRing.norm_star_mul_self, ← hss, ← CStarRing.norm_star_mul_self, hssa]
    nlinarith [norm_nonneg a, norm_nonneg s]
  rw [hnorm_eq]
  exact hnorms

/-- The predual `A_*` as a **submodule** of `A →L[ℂ] ℂ` — the shape the
principle of uniform boundedness needs in **87VIII**.  (Ultraweakly
continuous functionals are closed under sums and scalars, so `predual A` is
one.) -/
def predualSub : Submodule ℂ (A →L[ℂ] ℂ) where
  carrier := predual A
  add_mem' := by
    intro f g hf hg
    letI : TopologicalSpace A := ultraweak A
    exact (hf.add hg : Continuous fun a : A => f a + g a)
  zero_mem' := by
    letI : TopologicalSpace A := ultraweak A
    exact (continuous_const : Continuous fun _ : A => (0 : ℂ))
  smul_mem' := by
    intro c f hf
    letI : TopologicalSpace A := ultraweak A
    exact (continuous_const.mul hf : Continuous fun a : A => c * f a)

/-- **87VIII** (`ultraweakly-bounded-implies-bounded`, vn.tex:6612,
Theorem): a net `(b_α)_α` in a von Neumann algebra is norm bounded provided
it is **ultraweakly bounded**, i.e. `sup_α |ω(b_α)| < ∞` for every
np-functional `ω`.

This is 870.90's proof.  `f ↦ f(b_α)` is a bounded functional on the
predual with `‖(·)(b_α)‖ = ‖b_α‖` (**87VI** `norm_predual`); the predual is
complete (**87III** `predual_complete`), so the principle of uniform
boundedness applies as soon as `sup_α |f(b_α)| < ∞` for each `f ∈ 𝒜_*`, and
that is ultraweak boundedness itself once `f = ∑_{k<4} i^k ω_k` is split
into np-functionals by **72XI** `luws`.

*(Until 2026-08-21 this ran instead through a faithful normal
representation and two applications of Banach–Steinhaus on `H`, on the
stated ground that 87III and 87VI were "both still `sorry`".  They are
proved, above, in this file.)* -/
theorem ultraweakly_bounded_implies_bounded {ι : Type*} (x : ι → A)
    (h : ∀ ω : NPFunctional A, BddAbove (Set.range fun i => ‖ω (x i)‖)) :
    BddAbove (Set.range fun i => ‖x i‖) := by
  haveI : CompleteSpace (predualSub (A := A)) :=
    (predual_complete (A := A)).completeSpace_coe
  -- `Φ i : 𝒜_* → ℂ`, `f ↦ f(bᵢ)`
  set Φ : ι → (predualSub (A := A) →L[ℂ] ℂ) := fun i =>
    LinearMap.mkContinuous
      { toFun := fun f => (f : A →L[ℂ] ℂ) (x i)
        map_add' := fun f g => rfl
        map_smul' := fun c f => rfl } ‖x i‖
      (fun f => by
        have h1 : ‖(f : A →L[ℂ] ℂ) (x i)‖ ≤ ‖(f : A →L[ℂ] ℂ)‖ * ‖x i‖ :=
          (f : A →L[ℂ] ℂ).le_opNorm (x i)
        calc ‖(f : A →L[ℂ] ℂ) (x i)‖ ≤ ‖(f : A →L[ℂ] ℂ)‖ * ‖x i‖ := h1
          _ = ‖x i‖ * ‖f‖ := by rw [mul_comm]; rfl) with hΦ
  have hΦapp : ∀ (i : ι) (f : predualSub (A := A)),
      Φ i f = (f : A →L[ℂ] ℂ) (x i) := fun _ _ => rfl
  -- pointwise boundedness on `𝒜_*`, by **72XI**: `f = f₀ + i f₁ - f₂ - i f₃`
  have hpt : ∀ f : predualSub (A := A), ∃ C : ℝ, ∀ i, ‖Φ i f‖ ≤ C := by
    intro f
    have hcont : @Continuous A ℂ (ultraweak A) _ ⇑((f : A →L[ℂ] ℂ) : A →ₗ[ℂ] ℂ) := f.2
    obtain ⟨g, hg⟩ := ((luws ((f : A →L[ℂ] ℂ) : A →ₗ[ℂ] ℂ)).out 1 2).mp hcont
    choose C hC using fun k : Fin 4 => (h (g k)).exists_ge 0
    refine ⟨C 0 + C 1 + C 2 + C 3, fun i => ?_⟩
    have hbd : ∀ k : Fin 4, ‖(g k (x i) : ℂ)‖ ≤ C k := fun k =>
      (hC k).2 _ ⟨i, rfl⟩
    have hval : (Φ i f : ℂ)
        = g 0 (x i) + Complex.I * g 1 (x i) - g 2 (x i) - Complex.I * g 3 (x i) := by
      rw [hΦapp]; exact hg (x i)
    rw [hval]
    calc ‖g 0 (x i) + Complex.I * g 1 (x i) - g 2 (x i) - Complex.I * g 3 (x i)‖
        ≤ ‖g 0 (x i) + Complex.I * g 1 (x i) - g 2 (x i)‖
            + ‖Complex.I * (g 3 (x i) : ℂ)‖ := norm_sub_le _ _
      _ ≤ (‖g 0 (x i) + Complex.I * g 1 (x i)‖ + ‖(g 2 (x i) : ℂ)‖)
            + ‖Complex.I * (g 3 (x i) : ℂ)‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ((‖(g 0 (x i) : ℂ)‖ + ‖Complex.I * (g 1 (x i) : ℂ)‖)
            + ‖(g 2 (x i) : ℂ)‖) + ‖Complex.I * (g 3 (x i) : ℂ)‖ := by
          gcongr; exact norm_add_le _ _
      _ = ‖(g 0 (x i) : ℂ)‖ + ‖(g 1 (x i) : ℂ)‖ + ‖(g 2 (x i) : ℂ)‖
            + ‖(g 3 (x i) : ℂ)‖ := by
          simp only [norm_mul, Complex.norm_I, one_mul]
      _ ≤ C 0 + C 1 + C 2 + C 3 := by
          have h0 := hbd 0; have h1 := hbd 1; have h2 := hbd 2; have h3 := hbd 3
          linarith
  -- the principle of uniform boundedness (**11II**), on the complete `𝒜_*`
  obtain ⟨C, hC⟩ := banach_steinhaus (g := Φ) hpt
  refine ⟨C, ?_⟩
  rintro _ ⟨i, rfl⟩
  -- `‖bᵢ‖ = sup {|f(bᵢ)| : f ∈ (𝒜_*)₁} ≤ ‖Φ i‖ ≤ C` by **87VI**
  refine le_trans ((norm_predual (x i)).2 ?_) (hC i)
  rintro r ⟨f, hf, hf1, rfl⟩
  have hmem : f ∈ predualSub (A := A) := hf
  calc ‖f (x i)‖ = ‖Φ i ⟨f, hmem⟩‖ := rfl
    _ ≤ ‖Φ i‖ * ‖(⟨f, hmem⟩ : predualSub (A := A))‖ := (Φ i).le_opNorm _
    _ ≤ ‖Φ i‖ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        show ‖f‖ ≤ 1
        exact hf1
    _ = ‖Φ i‖ := mul_one _

/-! ## Parsec 880: ultraweak permanence and the double commutant theorem

**88I** (vn.tex:6622): overview — nothing to formalize. -/

variable (A) in
/-- **88II** (`commutant-ceil`, vn.tex:6697, Proposition), definition part:
the projection `⌈e⌉_{S^□} = ⋃_{a∈S} ⌈a* e a⌉`. -/
noncomputable def commutantCeil (S : Set A) (e : A) : A :=
  projSup {x : A | ∃ a ∈ S, x = ceil (star a * e * a)}

/-- **88II** (`commutant-ceil`, vn.tex:6697, Proposition): for a subset `S`
of a von Neumann algebra closed under multiplication and involution and
containing `1`, and a projection `e`: `⌈e⌉_{S^□} = ⋃_{a∈S} ⌈a* e a⌉` is
the least projection in `S^□` above `e`. -/
theorem commutant_ceil (S : Set A) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hstar : ∀ a ∈ S, star a ∈ S) (hone : (1 : A) ∈ S) (e : A)
    (he : IsStarProjection e) :
    IsLeast {p : A | IsStarProjection p ∧ p ∈ commutant A S ∧ e ≤ p}
      (commutantCeil A S e) := by
  -- The author's argument, in the form used for **68I** (`isLeast_centralAbove`):
  -- `⌈pb⌋ = ⌈b* p b⌉ = ⋃_{a∈S} ⌈b* ⌈a* e a⌉ b⌉ = ⋃_{a∈S} ⌈(ab)* e (ab)⌉ ≤ p`
  -- (by **60IX**.2 and **60VII**.1, using that `S` is closed under
  -- multiplication), whence `pbp = pb`; `bp = pbp` follows by applying this to
  -- `b*` and taking adjoints.  Minimality: `e ≤ q ∈ S□` gives
  -- `(a* e a)q = a* e (qa) = a* (eq) a = a* e a`, so `⌈a* e a⌉ ≤ q`.
  classical
  rw [commutantCeil]
  -- two elementary facts about projections, spelled out here
  have hprojmul : ∀ {x y : A}, IsStarProjection x → IsStarProjection y → x ≤ y →
      x * y = x := fun hx hy h =>
    ((projection_below_effect _ _ ⟨hy.nonneg, hy.le_one⟩ hx).out 0 7).mp h
  have hsupp : ∀ {x q : A}, IsStarProjection q → suppProj x ≤ q → x * q = x := by
    intro x q hq h
    obtain ⟨h1, h2⟩ := (ceill_basic_1 x).1
    calc x * q = x * suppProj x * q := by rw [h2]
      _ = x * (suppProj x * q) := by noncomm_ring
      _ = x * suppProj x := by rw [hprojmul h1 hq h]
      _ = x := h2
  set T : Set A := {x : A | ∃ a ∈ S, x = ceil (star a * e * a)} with hTdef
  have hTnn : ∀ a : A, (0 : A) ≤ star a * e * a := fun a =>
    star_left_conjugate_nonneg he.nonneg a
  have hTproj : ∀ x ∈ T, IsStarProjection x := by
    rintro _ ⟨a, -, rfl⟩
    exact (ceil_spec (hTnn a)).1
  obtain ⟨hpproj, hpub, hpleast⟩ := projSup_spec hTproj
  set p : A := projSup T with hpdef
  have hkey : ∀ b ∈ S, p * b * p = p * b := by
    intro b hb
    have e1 : star (p * b) * (p * b) = star b * p * b := by
      rw [star_mul, hpproj.isSelfAdjoint.star_eq]
      calc star b * p * (p * b) = star b * (p * p) * b := by noncomm_ring
        _ = star b * p * b := by rw [hpproj.isIdempotentElem.eq]
    have himgproj : ∀ x ∈ ((fun q => ceil (star b * q * b)) '' T),
        IsStarProjection x := by
      rintro _ ⟨q, hq, rfl⟩
      exact (ceil_spec (star_left_conjugate_nonneg (hTproj q hq).nonneg b)).1
    have himgT : ∀ x ∈ ((fun q => ceil (star b * q * b)) '' T), x ∈ T := by
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨a * b, hmul a ha b hb, ?_⟩
      show ceil (star b * ceil (star a * e * a) * b)
        = ceil (star (a * b) * e * (a * b))
      rw [← ceil_fundamental_1 b (star a * e * a) (hTnn a), star_mul]
      congr 1
      noncomm_ring
    have h3 : suppProj (p * b) ≤ p := by
      rw [suppProj, e1]
      refine le_of_eq_of_le (?_ : ceil (star b * p * b) = _)
        ((projSup_spec himgproj).2.2 p hpproj fun x hx => hpub x (himgT x hx))
      exact ceil_conj_projSup b T hTproj
    exact hsupp hpproj h3
  have hcomm : p ∈ commutant A S := by
    intro b hb
    have h4 : p * b * p = b * p := by
      have h := congrArg star (hkey (star b) (hstar b hb))
      simp only [star_mul, star_star, hpproj.isSelfAdjoint.star_eq] at h
      rw [← mul_assoc] at h
      exact h
    exact h4.symm.trans (hkey b hb)
  refine ⟨⟨hpproj, hcomm, hpub e ⟨1, hone, by
    rw [star_one, one_mul, mul_one, ceil_of_isStarProjection he]⟩⟩, ?_⟩
  rintro q ⟨hq, hqc, heq⟩
  refine hpleast q hq ?_
  rintro _ ⟨a, ha, rfl⟩
  refine (ceil_le_iff (hTnn a) hq).mpr ?_
  have heq' : e * q = e := hprojmul he hq heq
  calc star a * e * a * q = star a * e * (a * q) := by noncomm_ring
    _ = star a * e * (q * a) := by rw [hqc a ha]
    _ = star a * (e * q) * a := by noncomm_ring
    _ = star a * e * a := by rw [heq']

end VNA

section BH

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-! ### The rank-one projection `|x⟩⟨x|` and the cyclic subspace `closure (S x)`

Infrastructure for **88IV** (`carrier-vector-state`). -/

omit [CompleteSpace H] in
/-- `|x⟩⟨x| = ‖x‖² · P_{ℂx}`: the rank-one operator is a positive multiple
of the orthogonal projection onto the line it spans. -/
theorem ketbra_self_eq_smul_starProjection (x : H) :
    ketbra x x = ((‖x‖ ^ 2 : ℝ) : ℂ) • (Submodule.starProjection (ℂ ∙ x)) := by
  ext w
  rw [smul_apply]
  exact (Submodule.smul_starProjection_singleton ℂ w).symm

/-- `|x⟩⟨x| ≥ 0`. -/
theorem ketbra_self_nonneg (x : H) : (0 : H →L[ℂ] H) ≤ ketbra x x := by
  rw [ketbra_self_eq_smul_starProjection]
  exact ofReal_smul_nonneg isStarProjection_starProjection.nonneg (by positivity)

/-- `a* |x⟩⟨x| a = |a*x⟩⟨a*x|`. -/
theorem ketbra_conj_self (a : H →L[ℂ] H) (x : H) :
    star a * ketbra x x * a = ketbra (star a x) (star a x) := by
  ext w
  simp only [ContinuousLinearMap.mul_apply, ketbra, ContinuousLinearMap.smulRight_apply,
    map_smul, ContinuousLinearMap.star_eq_adjoint]
  congr 1
  exact (ContinuousLinearMap.adjoint_inner_left a w x).symm

/-- The orthogonal projection onto the cyclic subspace `closure (S x)` of a
∗-subalgebra `S ⊆ B(H)`: it lies in `S^□`, fixes `x`, and its fixed points
are exactly `closure (S x)`.  (This is the geometric half of **88IV**, and
the construction the thesis's item 4 refers to.) -/
theorem exists_cyclic_projection (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) :
    ∃ q : H →L[ℂ] H, IsStarProjection q ∧ q ∈ commutant (H →L[ℂ] H) S ∧
      q x = x ∧ {y : H | q y = y} = closure {y : H | ∃ T ∈ S, y = T x} := by
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
  -- and so is `Mᗮ`, because `S` is ∗-closed
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
  refine ⟨M.starProjection, isStarProjection_starProjection, hPcomm,
    (Submodule.starProjection_eq_self_iff).mpr hxM, ?_⟩
  rw [← hMset]
  ext y
  exact Submodule.starProjection_eq_self_iff

/-- **88IV** (`carrier-vector-state`, vn.tex:6742, Exercise): for a vector
`x` of a Hilbert space `H` and a unital ∗-subalgebra `S` of `B(H)`, the
least projection in `S^□` above `⌈|x⟩⟨x|⌉` equals
`⋃_{a∈S} ⌈|ax⟩⟨ax|⌉` and is the projection onto `closure (S x)` (a
projection identified by its fixed points).  (Item 2, identifying it with
the carrier of the vector functional restricted to `S^□`, needs the
relative carrier and is subsumed by the `IsLeast` formulation.) -/
theorem carrier_vector_state (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) :
    commutantCeil (H →L[ℂ] H) S (ceil (ketbra x x)) =
        projSup {p : H →L[ℂ] H | ∃ T ∈ S, p = ceil (ketbra (T x) (T x))} ∧
      {y : H | commutantCeil (H →L[ℂ] H) S (ceil (ketbra x x)) y = y} =
        closure {y : H | ∃ T ∈ S, y = T x} := by
  have hkb := ketbra_self_nonneg x
  -- (1) `⌈|x⟩⟨x|⌉_{S□} = ⋃_{a∈S} ⌈a* ⌈|x⟩⟨x|⌉ a⌉` is **88II**; the index set is
  -- reindexed by `a ↦ a*` using `⌈a* ⌈b⌉ a⌉ = ⌈a* b a⌉` (**60VII**.1) and
  -- `a* |x⟩⟨x| a = |a*x⟩⟨a*x|`.
  have hset : {y : H →L[ℂ] H | ∃ a ∈ (S : Set (H →L[ℂ] H)),
        y = ceil (star a * ceil (ketbra x x) * a)}
      = {p : H →L[ℂ] H | ∃ T ∈ S, p = ceil (ketbra (T x) (T x))} := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨star a, star_mem ha,
        by rw [← ceil_fundamental_1 a _ hkb, ketbra_conj_self]⟩
    · rintro ⟨T, hT, rfl⟩
      refine ⟨star T, star_mem hT, ?_⟩
      rw [← ceil_fundamental_1 (star T) _ hkb, ketbra_conj_self, star_star]
  have h1 : commutantCeil (H →L[ℂ] H) S (ceil (ketbra x x)) =
      projSup {p : H →L[ℂ] H | ∃ T ∈ S, p = ceil (ketbra (T x) (T x))} := by
    rw [commutantCeil, hset]
  refine ⟨h1, ?_⟩
  -- (2) the fixed points of that projection are `closure (S x)`: the projection
  -- `q` onto `closure (S x)` is a competitor, and `p` fixes `x` hence all of `S x`.
  obtain ⟨q, hqproj, hqcomm, hqx, hqfix⟩ := exists_cyclic_projection S x
  obtain ⟨⟨hpproj, hpcomm, hple⟩, hpmin⟩ :=
    commutant_ceil (A := H →L[ℂ] H) (S : Set (H →L[ℂ] H))
      (fun a ha b hb => mul_mem ha hb) (fun a ha => star_mem ha) (one_mem S)
      _ (ceil_spec hkb).1
  set p : H →L[ℂ] H := commutantCeil (H →L[ℂ] H) S (ceil (ketbra x x)) with hp
  have hpx : p x = x := by
    have h2 : p * ketbra x x = ketbra x x := ((ceil_basic_1 _ p hkb hpproj).out 2 0).mp hple
    have h3 := congrArg (fun T : H →L[ℂ] H => T x) h2
    simp only [ContinuousLinearMap.mul_apply, ketbra, ContinuousLinearMap.smulRight_apply,
      map_smul] at h3
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hne : (inner ℂ x x : ℂ) ≠ 0 := by
        simpa [inner_self_eq_zero] using hx
      exact smul_right_injective H hne h3
  have hkbq : ketbra x x * q = ketbra x x := by
    ext w
    simp only [ContinuousLinearMap.mul_apply, ketbra, ContinuousLinearMap.smulRight_apply]
    congr 1
    calc (inner ℂ x (q w) : ℂ) = inner ℂ ((ContinuousLinearMap.adjoint q) x) w :=
          (ContinuousLinearMap.adjoint_inner_left q w x).symm
      _ = inner ℂ x w := by
          rw [← ContinuousLinearMap.star_eq_adjoint, hqproj.isSelfAdjoint.star_eq, hqx]
  have hpq : p ≤ q := hpmin ⟨hqproj, hqcomm, (ceil_le_iff hkb hqproj).mpr hkbq⟩
  have hqp : q * p = p := by
    have h4 : p * q = p :=
      ((projection_below_effect q p ⟨hqproj.nonneg, hqproj.le_one⟩ hpproj).out 0 7).mp hpq
    have h5 := congrArg star h4
    rwa [star_mul, hqproj.isSelfAdjoint.star_eq, hpproj.isSelfAdjoint.star_eq] at h5
  apply Set.Subset.antisymm
  · intro y hy
    rw [← hqfix]
    show q y = y
    calc q y = q (p y) := by rw [(show p y = y from hy)]
      _ = (q * p) y := rfl
      _ = y := by rw [hqp]; exact hy
  · refine closure_minimal ?_ (isClosed_eq p.continuous continuous_id)
    rintro _ ⟨T, hT, rfl⟩
    show p (T x) = T x
    calc p (T x) = (p * T) x := rfl
      _ = (T * p) x := by rw [hpcomm T hT]
      _ = T x := by show T (p x) = T x; rw [hpx]

/-- **88IV** (`carrier-vector-state`, vn.tex:6742, Exercise), **item 2**:
the same projection is `⌈⟨x,(·)x⟩|S^□⌉`, the carrier of the vector
functional given by `x` *restricted to* `S^□`.

`S^□` is not built as a type here, so the relative carrier is rendered by
its defining property — the least projection `p` **of `S^□`** with
`⟨x,(1−p)x⟩ = 0` — exactly as **88IX** `commutant_cceil` renders the
relative *central* carrier.  That is `carrier_spec` read inside the von
Neumann algebra `S^□`.

Together with `carrier_vector_state` (items 1, 3 and 4) this is the
Exercise's "the following coincide": all four are
`commutantCeil (H →L[ℂ] H) S ⌈|x⟩⟨x|⌉`. -/
theorem carrier_vector_state_2 (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) :
    IsLeast {p : H →L[ℂ] H | p ∈ commutant (H →L[ℂ] H) (S : Set (H →L[ℂ] H)) ∧
        IsStarProjection p ∧ (⟪x, ((1 : H →L[ℂ] H) - p) x⟫ : ℂ) = 0}
      (commutantCeil (H →L[ℂ] H) S (ceil (ketbra x x))) := by
  have hkb := ketbra_self_nonneg x
  obtain ⟨⟨hpproj, hpcomm, hple⟩, hpmin⟩ :=
    commutant_ceil (A := H →L[ℂ] H) (S : Set (H →L[ℂ] H))
      (fun a ha b hb => mul_mem ha hb) (fun a ha => star_mem ha) (one_mem S)
      _ (ceil_spec hkb).1
  set p : H →L[ℂ] H := commutantCeil (H →L[ℂ] H) S (ceil (ketbra x x)) with hp
  -- for a projection `q`, `⟨x,(1−q)x⟩ = ‖(1−q)x‖²`, so the equation says `qx = x`
  have hfix : ∀ q : H →L[ℂ] H, IsStarProjection q →
      ((⟪x, ((1 : H →L[ℂ] H) - q) x⟫ : ℂ) = 0 ↔ q x = x) := by
    intro q hq
    have hr : IsStarProjection ((1 : H →L[ℂ] H) - q) := hq.one_sub
    have hrsa : ContinuousLinearMap.adjoint ((1 : H →L[ℂ] H) - q)
        = (1 : H →L[ℂ] H) - q := by
      rw [← ContinuousLinearMap.star_eq_adjoint]; exact hr.isSelfAdjoint.star_eq
    have key : (⟪x, ((1 : H →L[ℂ] H) - q) x⟫ : ℂ)
        = ⟪((1 : H →L[ℂ] H) - q) x, ((1 : H →L[ℂ] H) - q) x⟫ := by
      have h := ContinuousLinearMap.adjoint_inner_right ((1 : H →L[ℂ] H) - q) x
        (((1 : H →L[ℂ] H) - q) x)
      rw [hrsa] at h
      rw [← h]
      congr 1
      exact (congrArg (fun T : H →L[ℂ] H => T x) hr.isIdempotentElem.eq).symm
    rw [key, inner_self_eq_zero]
    constructor
    · intro h0
      have h1 : x - q x = 0 := h0
      exact (sub_eq_zero.mp h1).symm
    · intro h0
      show x - q x = 0
      rw [h0, sub_self]
  have hpx : p x = x := by
    have h2 : p * ketbra x x = ketbra x x := ((ceil_basic_1 _ p hkb hpproj).out 2 0).mp hple
    have h3 := congrArg (fun T : H →L[ℂ] H => T x) h2
    simp only [ContinuousLinearMap.mul_apply, ketbra, ContinuousLinearMap.smulRight_apply,
      map_smul] at h3
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hne : (inner ℂ x x : ℂ) ≠ 0 := by
        simpa [inner_self_eq_zero] using hx
      exact smul_right_injective H hne h3
  refine ⟨⟨hpcomm, hpproj, (hfix p hpproj).mpr hpx⟩, ?_⟩
  rintro q ⟨hqmem, hqproj, hq0⟩
  have hqx : q x = x := (hfix q hqproj).mp hq0
  refine hpmin ⟨hqproj, hqmem, (ceil_le_iff hkb hqproj).mpr ?_⟩
  ext w
  simp only [ContinuousLinearMap.mul_apply, ketbra, ContinuousLinearMap.smulRight_apply]
  congr 1
  calc (inner ℂ x (q w) : ℂ) = inner ℂ ((ContinuousLinearMap.adjoint q) x) w :=
        (ContinuousLinearMap.adjoint_inner_left q w x).symm
    _ = inner ℂ x w := by
        rw [← ContinuousLinearMap.star_eq_adjoint, hqproj.isSelfAdjoint.star_eq, hqx]

/-- **88IV** (`carrier-vector-state`, vn.tex:6742, Exercise), conclusion:
`closure (S^□□ x) = closure (S x)`. -/
theorem carrier_vector_state' (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) :
    closure {y : H | ∃ T ∈ commutant (H →L[ℂ] H)
        (commutant (H →L[ℂ] H) S), y = T x} =
      closure {y : H | ∃ T ∈ S, y = T x} := by
  -- the projection onto the cyclic subspace `closure (S x)` lies in `S□`, so every
  -- `R ∈ S□□` commutes with it and therefore maps `x` back into `closure (S x)`.
  obtain ⟨q, hqproj, hqcomm, hqx, hqfix⟩ := exists_cyclic_projection S x
  apply le_antisymm
  · rw [← hqfix]
    refine closure_minimal ?_ (isClosed_eq q.continuous continuous_id)
    rintro _ ⟨R, hR, rfl⟩
    show q (R x) = R x
    have hcomm := hR _ hqcomm
    calc q (R x) = (q * R) x := rfl
      _ = (R * q) x := by rw [hcomm]
      _ = R x := by show R (q x) = R x; rw [hqx]
  · refine closure_mono ?_
    rintro _ ⟨T, hT, rfl⟩
    exact ⟨T, fun m hm => (hm T hT).symm, rfl⟩

/-! ### The `ℕ`-fold amplification `ρ' : B(H) → B(⊕ₙ H)`

Infrastructure for **88V** (`proto-double-commutant`): the Hilbert space
`⊕ₙ H = lp (fun _ : ℕ => H) 2`, the nmiu-map `ρ'(t)y = (t yₙ)ₙ`, and the two
facts the thesis's hint (vn.tex:6752) asks for — `Pₙ a Pₘ* ∈ S□` for
`a ∈ ρ'(S)□`, and `ρ'(t) ∈ ρ'(S)□□` for `t ∈ S□□`. -/

omit [CompleteSpace H] in
/-- `(t yₙ)ₙ` is again square-summable: `‖t yₙ‖ ≤ ‖t‖‖yₙ‖`. -/
theorem amp_memLp (t : H →L[ℂ] H) (y : lp (fun _ : ℕ => H) 2) :
    Memℓp (fun n : ℕ => t (y n)) 2 := by
  refine memℓp_gen (Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (((lp.memℓp y).summable (by norm_num)).mul_left (‖t‖ ^ (2 : ℝ≥0∞).toReal)))
  calc ‖t ((y : ∀ _ : ℕ, H) n)‖ ^ (2 : ℝ≥0∞).toReal
      ≤ (‖t‖ * ‖(y : ∀ _ : ℕ, H) n‖) ^ (2 : ℝ≥0∞).toReal :=
        Real.rpow_le_rpow (norm_nonneg _) (t.le_opNorm _) (by norm_num)
    _ = ‖t‖ ^ (2 : ℝ≥0∞).toReal * ‖(y : ∀ _ : ℕ, H) n‖ ^ (2 : ℝ≥0∞).toReal :=
        Real.mul_rpow (norm_nonneg _) (norm_nonneg _)

/-- The amplification `ρ'(t)y = (t yₙ)ₙ`, as a linear map. -/
noncomputable def ampLM (t : H →L[ℂ] H) :
    lp (fun _ : ℕ => H) 2 →ₗ[ℂ] lp (fun _ : ℕ => H) 2 where
  toFun y := ⟨fun n => t (y n), amp_memLp t y⟩
  map_add' y z := by ext n; simp only [lp.coeFn_add, Pi.add_apply]; exact map_add t _ _
  map_smul' c y := by
    ext n
    simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    exact map_smul t _ _

omit [CompleteSpace H] in
/-- The components of `ρ'(t)y`. -/
@[simp] theorem ampLM_apply (t : H →L[ℂ] H) (y : lp (fun _ : ℕ => H) 2) (n : ℕ) :
    ((ampLM t y : lp (fun _ : ℕ => H) 2) : ∀ _ : ℕ, H) n = t (y n) := rfl

omit [CompleteSpace H] in
/-- `ρ'` is bounded, with `‖ρ'(t)‖ ≤ ‖t‖`. -/
theorem ampLM_norm_le (t : H →L[ℂ] H) (y : lp (fun _ : ℕ => H) 2) :
    ‖ampLM t y‖ ≤ ‖t‖ * ‖y‖ := by
  have hp : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hsy : Summable fun n : ℕ => ‖(y : ∀ _ : ℕ, H) n‖ ^ (2 : ℝ≥0∞).toReal :=
    (lp.memℓp y).summable hp
  have hsz : Summable fun n : ℕ =>
      ‖((ampLM t y : lp (fun _ : ℕ => H) 2) : ∀ _ : ℕ, H) n‖ ^ (2 : ℝ≥0∞).toReal :=
    (lp.memℓp _).summable hp
  have hle : ∀ n : ℕ, ‖((ampLM t y : lp (fun _ : ℕ => H) 2) : ∀ _ : ℕ, H) n‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ‖t‖ ^ (2 : ℝ≥0∞).toReal * ‖(y : ∀ _ : ℕ, H) n‖ ^ (2 : ℝ≥0∞).toReal := by
    intro n
    rw [ampLM_apply]
    calc ‖t ((y : ∀ _ : ℕ, H) n)‖ ^ (2 : ℝ≥0∞).toReal
        ≤ (‖t‖ * ‖(y : ∀ _ : ℕ, H) n‖) ^ (2 : ℝ≥0∞).toReal :=
          Real.rpow_le_rpow (norm_nonneg _) (t.le_opNorm _) hp.le
      _ = _ := Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
  have h1 : ‖ampLM t y‖ ^ (2 : ℝ≥0∞).toReal ≤ (‖t‖ * ‖y‖) ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum hp, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
      lp.norm_rpow_eq_tsum hp y, ← tsum_mul_left]
    exact hsz.tsum_le_tsum hle (hsy.mul_left _)
  have hcast : (2 : ℝ≥0∞).toReal = ((2:ℕ):ℝ) := by norm_num
  rw [hcast, Real.rpow_natCast, Real.rpow_natCast] at h1
  nlinarith [norm_nonneg (ampLM t y), mul_nonneg (norm_nonneg t) (norm_nonneg y)]

/-- The amplification `ρ'(t)y = (t yₙ)ₙ` of `t ∈ B(H)` to `B(⊕ₙ H)`. -/
noncomputable def amp (t : H →L[ℂ] H) :
    lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => H) 2 :=
  (ampLM t).mkContinuous ‖t‖ (ampLM_norm_le t)

/-- The components of `ρ'(t)y`. -/
@[simp] theorem amp_apply (t : H →L[ℂ] H) (y : lp (fun _ : ℕ => H) 2) (n : ℕ) :
    ((amp t y : lp (fun _ : ℕ => H) 2) : ∀ _ : ℕ, H) n = t (y n) := rfl

omit [CompleteSpace H] in
/-- Two operators on `⊕ₙ H` agree as soon as they agree componentwise. -/
theorem lp_clm_ext {f g : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => H) 2}
    (h : ∀ (y : lp (fun _ : ℕ => H) 2) (n : ℕ),
      ((f y : lp (fun _ : ℕ => H) 2) : ∀ _ : ℕ, H) n
        = ((g y : lp (fun _ : ℕ => H) 2) : ∀ _ : ℕ, H) n) : f = g :=
  ContinuousLinearMap.ext fun y => Subtype.ext (funext (h y))

/-- `ρ'` commutes with the involution: `ρ'(t*) = ρ'(t)*`. -/
theorem amp_star (t : H →L[ℂ] H) : amp (star t) = star (amp t) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun y z => ?_
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [amp_apply, amp_apply]
  exact ContinuousLinearMap.adjoint_inner_left t ((z : ∀ _ : ℕ, H) n)
    ((y : ∀ _ : ℕ, H) n)

/-- The amplification as a ∗-homomorphism `B(H) → B(⊕ₙ H)`. -/
noncomputable def ampHom :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => H) 2) where
  toFun := amp
  map_one' := by refine lp_clm_ext fun y n => ?_; rw [amp_apply]; rfl
  map_mul' t s := by refine lp_clm_ext fun y n => ?_; rw [amp_apply]; rfl
  map_zero' := by refine lp_clm_ext fun y n => ?_; rw [amp_apply]; simp
  map_add' t s := by
    refine lp_clm_ext fun y n => ?_
    rw [amp_apply]
    change t (y n) + s (y n) = _
    rfl
  commutes' r := by
    refine lp_clm_ext fun y n => ?_
    rw [amp_apply]
    change r • (y : ∀ _ : ℕ, H) n = _
    rfl
  map_star' t := amp_star t

/-- `ampHom` is `amp`. -/
@[simp] theorem ampHom_apply (t : H →L[ℂ] H) : (ampHom (H := H)) t = amp t := rfl


/-- `ρ'(b) Pₘ* = Pₘ* b`: the amplification respects the `m`-th coordinate
embedding. -/
theorem amp_single (b : H →L[ℂ] H) (m : ℕ) (u : H) :
    amp b (lp.single 2 m u) = lp.single 2 m (b u) := by
  refine Subtype.ext (funext fun j => ?_)
  rw [amp_apply, lp.single_apply, lp.single_apply]
  rcases eq_or_ne j m with rfl | hj
  · simp
  · simp [Pi.single_eq_of_ne hj]

/-- `Pₙ a Pₘ*`, the `(n,m)`-corner of an operator on `⊕ₙ H`. -/
noncomputable def ampCorner
    (a : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => H) 2) (n m : ℕ) :
    H →L[ℂ] H :=
  (lp.evalCLM ℂ (fun _ : ℕ => H) 2 n) ∘L a ∘L
    (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 m)

omit [CompleteSpace H] in
/-- `(Pₙ a Pₘ*)u` is the `n`-th component of `a (Pₘ* u)`. -/
theorem ampCorner_apply (a : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => H) 2)
    (n m : ℕ) (u : H) :
    ampCorner a n m u
      = ((a (lp.single 2 m u) : lp (fun _ : ℕ => H) 2) : ∀ _ : ℕ, H) n := rfl

/-- The thesis's hint for **88V**: `Pₙ a Pₘ* ∈ S□` whenever `a ∈ ρ'(S)□`. -/
theorem ampCorner_mem_commutant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (a : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => H) 2)
    (ha : a ∈ commutant (lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => H) 2)
      ((S.map (ampHom (H := H)) : StarSubalgebra ℂ _) : Set _))
    (n m : ℕ) :
    ampCorner a n m ∈ commutant (H →L[ℂ] H) (S : Set (H →L[ℂ] H)) := by
  intro s hs
  refine ContinuousLinearMap.ext fun u => ?_
  change s (ampCorner a n m u) = ampCorner a n m (s u)
  have h2 := congrArg (fun T : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => H) 2 =>
    T (lp.single 2 m u)) (ha (amp s) ⟨s, hs, rfl⟩)
  simp only [mul_apply_eq_comp] at h2
  rw [ampCorner_apply, ampCorner_apply, ← amp_apply s, h2, amp_single]

/-- The second half of the thesis's hint: `ρ'(t) ∈ ρ'(S)□□` for
`t ∈ S□□`. -/
theorem amp_mem_double_commutant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (t : H →L[ℂ] H)
    (ht : t ∈ commutant (H →L[ℂ] H)
      (commutant (H →L[ℂ] H) (S : Set (H →L[ℂ] H)))) :
    amp t ∈ commutant (lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => H) 2)
      (commutant (lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => H) 2)
        ((S.map (ampHom (H := H)) : StarSubalgebra ℂ _) : Set _)) := by
  intro a ha
  refine ContinuousLinearMap.ext fun y => ?_
  change a (amp t y) = amp t (a y)
  refine Subtype.ext (funext fun n => ?_)
  rw [amp_apply]
  set Φ : lp (fun _ : ℕ => H) 2 →L[ℂ] H :=
    (lp.evalCLM ℂ (fun _ : ℕ => H) 2 n) ∘L a with hΦ
  have hy : HasSum (fun m : ℕ => lp.single 2 m ((y : ∀ _ : ℕ, H) m)) y :=
    lp.hasSum_single ENNReal.ofNat_ne_top y
  have hty : HasSum
      (fun m : ℕ => lp.single 2 m (t ((y : ∀ _ : ℕ, H) m))) (amp t y) := by
    have h := lp.hasSum_single (E := fun _ : ℕ => H) ENNReal.ofNat_ne_top (amp t y)
    simpa using h
  have h1 : HasSum (fun m : ℕ => ampCorner a n m ((y : ∀ _ : ℕ, H) m)) (Φ y) :=
    Φ.hasSum hy
  have h2 : HasSum (fun m : ℕ => t (ampCorner a n m ((y : ∀ _ : ℕ, H) m)))
      (t (Φ y)) := t.hasSum h1
  have h3 : HasSum (fun m : ℕ => ampCorner a n m (t ((y : ∀ _ : ℕ, H) m)))
      (Φ (amp t y)) := Φ.hasSum hty
  have hterm : ∀ m : ℕ, t (ampCorner a n m ((y : ∀ _ : ℕ, H) m))
      = ampCorner a n m (t ((y : ∀ _ : ℕ, H) m)) := by
    intro m
    have h := ht (ampCorner a n m) (ampCorner_mem_commutant S a ha n m)
    exact (congrArg (fun T : H →L[ℂ] H => T ((y : ∀ _ : ℕ, H) m)) h).symm
  have h3' : HasSum (fun m : ℕ => t (ampCorner a n m ((y : ∀ _ : ℕ, H) m)))
      (Φ (amp t y)) := by simpa only [hterm] using h3
  exact (h2.unique h3').symm

/-- The commutant of a ∗-subalgebra is closed under the involution (the
star-closedness that **65III** `commutant_basic_3'` asks for). -/
theorem star_mem_commutant_of_starSubalgebra (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {a : H →L[ℂ] H} (ha : a ∈ commutant (H →L[ℂ] H) (S : Set (H →L[ℂ] H))) :
    star a ∈ commutant (H →L[ℂ] H) (S : Set (H →L[ℂ] H)) := by
  intro m hm
  have h := ha (star m) (star_mem hm)
  have h2 := congrArg star h
  rw [star_mul, star_mul, star_star] at h2
  exact h2.symm

/-- `W*(R) = R` for a von Neumann subalgebra `R`. -/
theorem wstar_eq_of_isVNSubalgebra (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hR : IsVNSubalgebra (H →L[ℂ] H) R) :
    wstar (H →L[ℂ] H) (R : Set (H →L[ℂ] H)) = R :=
  le_antisymm (sInf_le ⟨hR, subset_rfl⟩)
    (fun _ ha => (isVNSubalgebra_wstar (R : Set (H →L[ℂ] H))).2 ha)

/-- **88V** (`proto-double-commutant`, vn.tex:6765), **item 1**, second
half: `ρ'(t) = ∑ₙ Pₙ* t Pₙ`, where `Pₙ : ⊕ₙ H → H` is the `n`-th projection
and `Pₙ*` the corresponding coordinate embedding.  The series converges
strongly — pointwise on `⊕ₙ H` — which is the only sense it can have (in
norm it does not converge, already for `t = 1`). -/
theorem amp_eq_sum_corners (t : H →L[ℂ] H) (y : lp (fun _ : ℕ => H) 2) :
    HasSum (fun n : ℕ =>
        (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 n ∘L t ∘L
          lp.evalCLM ℂ (fun _ : ℕ => H) 2 n) y)
      (amp t y) := by
  have h0 := lp.hasSum_single (E := fun _ : ℕ => H) ENNReal.ofNat_ne_top (amp t y)
  have heq : ∀ n : ℕ,
      (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 n ∘L t ∘L
        lp.evalCLM ℂ (fun _ : ℕ => H) 2 n) y
        = lp.single 2 n (((amp t y : lp (fun _ : ℕ => H) 2) : ∀ _ : ℕ, H) n) := by
    intro n; rw [amp_apply]; rfl
  simpa only [heq] using h0

/-- **88V** (`proto-double-commutant`, vn.tex:6765), **item 1**, first
half: an np-map `ω : B(H) → ℂ` is `ω(t) = ⟨x', ρ'(t)x'⟩` for the vector
`x' ≡ (x₁, x₂, …)` of `H' = ⊕ₙ H` assembled from the sequence that **39IX**
(`bh_np`) supplies, `ω = ∑ₙ ⟨xₙ, (·)xₙ⟩`.  (Square-summability of the `xₙ`
is what puts `x'` in `H'`.) -/
theorem proto_double_commutant_1 (ω : NPFunctional (H →L[ℂ] H)) :
    ∃ x' : lp (fun _ : ℕ => H) 2,
      ∀ t : H →L[ℂ] H, (ω t : ℂ) = ⟪x', amp t x'⟫ := by
  obtain ⟨x, hx, hxsum⟩ := bh_np ω
  have hsum : Summable fun n : ℕ => ‖x n‖ ^ 2 := by
    have h := ((Complex.hasSum_iff _ _).mp hxsum).1
    simpa only [Complex.ofReal_re] using h.summable
  have hmem : Memℓp x 2 := by
    refine memℓp_gen ?_
    have hcast : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
    simpa [hcast, Real.rpow_natCast] using hsum
  refine ⟨⟨x, hmem⟩, fun t => ?_⟩
  rw [lp.inner_eq_tsum]
  have heq : ∀ n : ℕ,
      (⟪((⟨x, hmem⟩ : lp (fun _ : ℕ => H) 2) : ∀ _ : ℕ, H) n,
        ((amp t ⟨x, hmem⟩ : lp (fun _ : ℕ => H) 2) : ∀ _ : ℕ, H) n⟫ : ℂ)
      = ⟪x n, t (x n)⟫ := by
    intro n; rw [amp_apply]
  simp only [heq]
  exact ((hx t).tsum_eq).symm

/-- **88V** (`proto-double-commutant`, vn.tex:6765), **item 3**: for a
unital ∗-subalgebra `S` of `B(H)`, the double commutant `S^□□` is contained
in the ultrastrong closure of `S`.  (Item 1 is `proto_double_commutant_1`
and `amp_eq_sum_corners` above; item 2's two halves are
`ampCorner_mem_commutant` and `amp_mem_double_commutant`, and its "conclude
that" is the `hin` step of this proof.) -/
theorem proto_double_commutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) S) ⊆
      @closure _ (ultrastrong (H →L[ℂ] H)) (S : Set (H →L[ℂ] H)) := by
  intro t ht
  rw [mem_usClosure_iff]
  intro ω ε hε
  obtain ⟨x, hx, hxsum⟩ := bh_np ω
  have hsum : Summable fun n : ℕ => ‖x n‖ ^ 2 := by
    have h := ((Complex.hasSum_iff _ _).mp hxsum).1
    simpa only [Complex.ofReal_re] using h.summable
  have hmem : Memℓp x 2 := by
    refine memℓp_gen ?_
    have hcast : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
    simpa [hcast, Real.rpow_natCast] using hsum
  set x' : lp (fun _ : ℕ => H) 2 := ⟨x, hmem⟩ with hx'
  have hnorm : ∀ u : H →L[ℂ] H, ‖amp u x'‖ = omegaNorm (H →L[ℂ] H) ω u := by
    intro u
    have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
    have hcast : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
    have h1 : ‖amp u x'‖ ^ (2 : ℕ) = ∑' n : ℕ, ‖u (x n)‖ ^ (2 : ℕ) := by
      have := lp.norm_rpow_eq_tsum hp (amp u x')
      rw [hcast] at this
      simpa [Real.rpow_natCast] using this
    have h2 := (hasSum_normSq_of_np hx u).tsum_eq
    rw [h2] at h1
    have := congrArg Real.sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (omegaNorm_nonneg ω u)] at this
  have hin : amp t x' ∈ closure {y : lp (fun _ : ℕ => H) 2 |
      ∃ R ∈ (S.map (ampHom (H := H)) : StarSubalgebra ℂ _), y = R x'} := by
    rw [← carrier_vector_state' (S.map (ampHom (H := H))) x']
    exact subset_closure ⟨amp t, amp_mem_double_commutant S t ht, rfl⟩
  obtain ⟨w, ⟨R, hR, rfl⟩, hd⟩ := Metric.mem_closure_iff.mp hin ε hε
  obtain ⟨s, hs, rfl⟩ := hR
  refine ⟨s, hs, ?_⟩
  have hmapsub : amp (t - s) = amp t - amp s := by
    simpa only [ampHom_apply] using map_sub (ampHom (H := H)) t s
  rw [dist_eq_norm] at hd
  have hd2 : ‖amp (t - s) x'‖ < ε := by rw [hmapsub]; simpa using hd
  rw [hnorm] at hd2
  rwa [show s - t = -(t - s) by abel, omegaNorm_neg]

/-- **88VI** (`double-commutant`, vn.tex:6809, Double Commutant Theorem):
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
          StarSubalgebra ℂ (H →L[ℂ] H)) := by
  have hAB := proto_double_commutant S
  have hBC := usClosure_subset_uwClosure (A := H →L[ℂ] H) (S : Set (H →L[ℂ] H))
  obtain ⟨T, hTvn, hTcoe⟩ :=
    (commutant_basic_3' (commutant (H →L[ℂ] H) (S : Set (H →L[ℂ] H)))
      (fun _ ha => star_mem_commutant_of_starSubalgebra S ha)).1
  have hST : (S : Set (H →L[ℂ] H)) ⊆ (T : Set (H →L[ℂ] H)) := by
    rw [hTcoe]
    exact (commutant_basic_1 (S : Set (H →L[ℂ] H)) (S : Set (H →L[ℂ] H))).2.2.1
  have hCD : @closure _ (ultraweak (H →L[ℂ] H)) (S : Set (H →L[ℂ] H)) ⊆
      (wstar (H →L[ℂ] H) (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) :=
    @closure_minimal _ (ultraweak (H →L[ℂ] H)) _ _
      (isVNSubalgebra_wstar (S : Set (H →L[ℂ] H))).2
      (vnsac _ (isVNSubalgebra_wstar (S : Set (H →L[ℂ] H))).1).2
  have hDA : (wstar (H →L[ℂ] H) (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) ⊆
      commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) (S : Set (H →L[ℂ] H))) := by
    intro a ha
    rw [SetLike.mem_coe, wstar, StarSubalgebra.mem_sInf] at ha
    have : a ∈ T := ha T ⟨hTvn, hST⟩
    rw [← hTcoe]
    exact this
  exact ⟨subset_antisymm hAB fun z hz => hDA (hCD (hBC hz)),
    subset_antisymm (hAB.trans hBC) fun z hz => hDA (hCD hz),
    subset_antisymm ((hAB.trans hBC).trans hCD) hDA⟩

/-- **88VIII** (`centre-commutant`, vn.tex:6852, Exercise): for a von
Neumann subalgebra `R` of `B(H)`: `Z(R) = Z(R^□)`, i.e. the central
elements of `R` coincide with those of its commutant. -/
theorem centre_commutant (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hR : IsVNSubalgebra (H →L[ℂ] H) R) :
    (R : Set (H →L[ℂ] H)) ∩ commutant (H →L[ℂ] H) R =
      commutant (H →L[ℂ] H) R ∩
        commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) R) := by
  have h := (double_commutant R).2.2
  rw [wstar_eq_of_isVNSubalgebra R hR] at h
  rw [h, Set.inter_comm]

/-- Auxiliary: the product of two *commuting* projections is a projection. -/
private theorem isStarProjection_mul_of_comm {M : Type*} [CStarAlgebra M]
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : p * q = q * p) : IsStarProjection (p * q) := by
  constructor
  · show p * q * (p * q) = p * q
    calc p * q * (p * q) = p * (q * p) * q := by noncomm_ring
      _ = p * (p * q) * q := by rw [h]
      _ = (p * p) * (q * q) := by noncomm_ring
      _ = p * q := by rw [hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]
  · show star (p * q) = p * q
    rw [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, ← h]

/-- **88IX** (`commutant-cceil`, vn.tex:6859): for an np-map
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
        f (1 - p) = 0} c := by
  classical
  have hfnn : ∀ a : H →L[ℂ] H, 0 ≤ a → (0 : B) ≤ f a := by
    intro a ha
    have h : (f (0 : H →L[ℂ] H) : B) ≤ f a := f.monotone ha
    rwa [map_zero f] at h
  -- `T` is the commutant of `R`, as a von Neumann subalgebra
  obtain ⟨T, hT, hTset⟩ :=
    (commutant_basic_3' (R : Set (H →L[ℂ] H)) (fun s hs => star_mem hs)).1
  -- the set of projections of `Z(R)` killed by `f`
  set E : Set (H →L[ℂ] H) :=
    {p : H →L[ℂ] H | p ∈ R ∧ p ∈ commutant (H →L[ℂ] H) (R : Set (H →L[ℂ] H)) ∧
      IsStarProjection p ∧ f p = 0} with hEdef
  have hEproj : ∀ p ∈ E, IsStarProjection p := fun _ hp => hp.2.2.1
  have hEne : E.Nonempty := by
    refine ⟨0, zero_mem _, ?_, IsStarProjection.zero _, map_zero f⟩
    intro b _
    rw [mul_zero, zero_mul]
  have hEdir : DirectedOn (· ≤ ·) E := by
    rintro p ⟨hpR, hpC, hpproj, hpf⟩ q ⟨hqR, hqC, hqproj, hqf⟩
    have hpq : p * q = q * p := (hpC q hqR).symm
    have hp' : IsStarProjection (1 - p) := hpproj.one_sub
    have hq' : IsStarProjection (1 - q) := hqproj.one_sub
    have hpq' : (1 - p) * (1 - q) = (1 - q) * (1 - p) := by
      have h1 : (1 - p) * ((1 : H →L[ℂ] H) - q) = 1 - p - q + p * q := by noncomm_ring
      have h2 : (1 - q) * ((1 : H →L[ℂ] H) - p) = 1 - q - p + q * p := by noncomm_ring
      rw [h1, h2, hpq]; abel
    set s : H →L[ℂ] H := (1 - p) * (1 - q) with hsdef
    have hsproj : IsStarProjection s := isStarProjection_mul_of_comm hp' hq' hpq'
    set r : H →L[ℂ] H := 1 - s with hrdef
    have hrproj : IsStarProjection r := hsproj.one_sub
    have hreq : r = p + q - p * q := by
      rw [hrdef, hsdef]; noncomm_ring
    have hpr : p ≤ r := by
      have hd : r - p = (1 - p) * q := by rw [hreq]; noncomm_ring
      have hdproj : IsStarProjection ((1 - p) * q) := by
        refine isStarProjection_mul_of_comm hp' hqproj ?_
        have h1 : (1 - p) * q = q - p * q := by noncomm_ring
        have h2 : q * ((1 : H →L[ℂ] H) - p) = q - q * p := by noncomm_ring
        rw [h1, h2, hpq]
      have : (0 : H →L[ℂ] H) ≤ r - p := hd ▸ hdproj.nonneg
      exact sub_nonneg.mp this
    have hqr : q ≤ r := by
      have hd : r - q = p * (1 - q) := by rw [hreq]; noncomm_ring
      have hdproj : IsStarProjection (p * (1 - q)) := by
        refine isStarProjection_mul_of_comm hpproj hq' ?_
        have h1 : p * ((1 : H →L[ℂ] H) - q) = p - p * q := by noncomm_ring
        have h2 : (1 - q) * p = p - q * p := by noncomm_ring
        rw [h1, h2, hpq]
      have : (0 : H →L[ℂ] H) ≤ r - q := hd ▸ hdproj.nonneg
      exact sub_nonneg.mp this
    refine ⟨r, ⟨?_, ?_, hrproj, ?_⟩, hpr, hqr⟩
    · rw [hreq]; exact sub_mem (add_mem hpR hqR) (mul_mem hpR hqR)
    · intro b hb
      have h1 : b * p = p * b := hpC b hb
      have h2 : b * q = q * b := hqC b hb
      rw [hreq]
      calc b * (p + q - p * q) = b * p + b * q - (b * p) * q := by noncomm_ring
        _ = p * b + q * b - (p * b) * q := by rw [h1, h2]
        _ = p * b + q * b - p * (b * q) := by noncomm_ring
        _ = p * b + q * b - p * (q * b) := by rw [h2]
        _ = (p + q - p * q) * b := by noncomm_ring
    · have hle : r ≤ p + q := by
        have hpqnn : (0 : H →L[ℂ] H) ≤ p * q :=
          (isStarProjection_mul_of_comm hpproj hqproj hpq).nonneg
        rw [hreq]
        have h := sub_le_sub_left hpqnn (p + q)
        rwa [sub_zero] at h
      have h1 : (f r : B) ≤ f (p + q) := f.monotone hle
      rw [map_add f, hpf, hqf, add_zero] at h1
      exact le_antisymm h1 (hfnn r hrproj.nonneg)
  -- the supremum of `E`
  obtain ⟨heproj, heub, -⟩ := projSup_spec hEproj
  set e : H →L[ℂ] H := projSup E with hedef
  have hlub : IsLUB E e := isLUB_projSup_of_directed E hEproj hEne hEdir
  have hmemS : ∀ S : StarSubalgebra ℂ (H →L[ℂ] H), IsVNSubalgebra (H →L[ℂ] H) S →
      (∀ p ∈ E, p ∈ S) → e ∈ S := by
    intro S hS hsub
    refine hS.dirSup_mem {d : selfAdjoint (H →L[ℂ] H) | (d : H →L[ℂ] H) ∈ E}
      ⟨e, heproj.isSelfAdjoint⟩ (fun d hd => hsub _ hd) ?_ ?_ ?_
    · obtain ⟨p, hp⟩ := hEne
      exact ⟨⟨p, (hEproj p hp).isSelfAdjoint⟩, hp⟩
    · intro x hx y hy
      obtain ⟨z, hz, hxz, hyz⟩ := hEdir _ hx _ hy
      exact ⟨⟨z, (hEproj z hz).isSelfAdjoint⟩, hz, hxz, hyz⟩
    · constructor
      · intro d hd
        exact Subtype.coe_le_coe.mp (hlub.1 hd)
      · intro u hu
        refine Subtype.coe_le_coe.mp (hlub.2 fun x hx => ?_)
        exact Subtype.coe_le_coe.mpr
          (hu (show (⟨x, (hEproj x hx).isSelfAdjoint⟩ : selfAdjoint _) ∈ _ from hx))
  have heR : e ∈ R := hmemS R hR fun p hp => hp.1
  have heC : e ∈ commutant (H →L[ℂ] H) (R : Set (H →L[ℂ] H)) := by
    have hmem : e ∈ T := hmemS T hT fun p hp => by
      rw [← SetLike.mem_coe, hTset]; exact hp.2.1
    rw [← SetLike.mem_coe, hTset] at hmem
    exact hmem
  have hfe : (f e : B) = 0 := by
    have himg : ∀ x ∈ ((fun p => ceil (f p)) '' E), IsStarProjection x := by
      rintro _ ⟨p, hp, rfl⟩
      show IsStarProjection (ceil (f p))
      rw [hp.2.2.2, ceil_zero]
      exact IsStarProjection.zero B
    have hzero : projSup ((fun p => ceil (f p)) '' E) = 0 := by
      refine projSup_eq himg (IsStarProjection.zero B) ?_ fun q hq _ => hq.nonneg
      rintro _ ⟨p, hp, rfl⟩
      show ceil (f p) ≤ 0
      rw [hp.2.2.2, ceil_zero]
    have h := ncp_union_2 f hf E hEproj
    rw [hzero] at h
    exact (ceil_basic_3 _ (hfnn e heproj.nonneg)).mpr h
  -- `1 - e` is the least element of the first set
  have hS1 : IsLeast {p : H →L[ℂ] H | p ∈ R ∧ IsStarProjection p ∧
      (∀ b ∈ R, p * b = b * p) ∧ f (1 - p) = 0} (1 - e) := by
    constructor
    · refine ⟨sub_mem (one_mem R) heR, heproj.one_sub, ?_, ?_⟩
      · intro b hb
        have h := heC b hb
        calc (1 - e) * b = b - e * b := by noncomm_ring
          _ = b - b * e := by rw [h]
          _ = b * (1 - e) := by noncomm_ring
      · rw [sub_sub_cancel]; exact hfe
    · rintro p ⟨hpR, hpproj, hpc, hpf⟩
      have hmem : 1 - p ∈ E := by
        refine ⟨sub_mem (one_mem R) hpR, ?_, hpproj.one_sub, hpf⟩
        intro b hb
        have h := hpc b hb
        calc b * (1 - p) = b - b * p := by noncomm_ring
          _ = b - p * b := by rw [h]
          _ = (1 - p) * b := by noncomm_ring
      exact sub_le_comm.mp (heub _ hmem)
  refine ⟨1 - e, hS1, ?_⟩
  -- the second set is the same set, by **88VIII**
  have hc1 : ∀ p : H →L[ℂ] H, (∀ b ∈ (R : Set (H →L[ℂ] H)), p * b = b * p) ↔
      p ∈ commutant (H →L[ℂ] H) (R : Set (H →L[ℂ] H)) :=
    fun p => ⟨fun h b hb => (h b hb).symm, fun h b hb => (h b hb).symm⟩
  have hc2 : ∀ p : H →L[ℂ] H,
      (∀ b ∈ commutant (H →L[ℂ] H) (R : Set (H →L[ℂ] H)), p * b = b * p) ↔
      p ∈ commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) (R : Set (H →L[ℂ] H))) :=
    fun p => ⟨fun h b hb => (h b hb).symm, fun h b hb => (h b hb).symm⟩
  have hcc := centre_commutant R hR
  have hsetEq : {p : H →L[ℂ] H | p ∈ commutant (H →L[ℂ] H) (R : Set (H →L[ℂ] H)) ∧
        IsStarProjection p ∧
        (∀ b ∈ commutant (H →L[ℂ] H) (R : Set (H →L[ℂ] H)), p * b = b * p) ∧
        f (1 - p) = 0}
      = {p : H →L[ℂ] H | p ∈ R ∧ IsStarProjection p ∧
        (∀ b ∈ R, p * b = b * p) ∧ f (1 - p) = 0} := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have hmem : p ∈ commutant (H →L[ℂ] H) (R : Set (H →L[ℂ] H)) ∩
          commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) (R : Set (H →L[ℂ] H))) :=
        ⟨h1, (hc2 p).mp h3⟩
      rw [← hcc] at hmem
      exact ⟨hmem.1, h2, (hc1 p).mpr hmem.2, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      have hmem : p ∈ (R : Set (H →L[ℂ] H)) ∩
          commutant (H →L[ℂ] H) (R : Set (H →L[ℂ] H)) := ⟨h1, (hc1 p).mp h3⟩
      rw [hcc] at hmem
      exact ⟨hmem.1, h2, (hc2 p).mpr hmem.2, h4⟩
  rw [hsetEq]
  exact hS1

/-! ## Parsec 890: normal functionals as sums of vector functionals -/

variable [VonNeumannAlgebra A]

/-- **89I** (`gns-mapping-property`, vn.tex:6867, Lemma): if an
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
      IsStarProjection (U ∘L ContinuousLinearMap.adjoint U) ∧
      IsStarProjection (ContinuousLinearMap.adjoint U ∘L U) ∧
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
  refine ⟨U, ?_, ?_, by rw [hadjU, hUW]; exact isStarProjection_starProjection,
    by rw [hadjU, hWU]; exact isStarProjection_starProjection, ?_⟩
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

/-- **89III** (`summing-partial-isometries`, vn.tex:6929, Exercise): given
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

/-! ### Vector states, central carriers and the image of an nmiu-map

Infrastructure for **89V** (`sigma-weak-lemma-2`). -/

section Helpers
variable {L : Type u} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem isStarProjection_le_of_fix_subset {e f : L →L[ℂ] L}
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (h : {z : L | e z = z} ⊆ {z : L | f z = z}) : e ≤ f := by
  refine ((projection_below_effect f e ⟨hf.nonneg, hf.le_one⟩ he).out 0 6).mpr ?_
  ext z
  show f (e z) = e z
  refine h ?_
  show e (e z) = e z
  rw [← ContinuousLinearMap.mul_apply, he.isIdempotentElem]

theorem nmiu_isStarProjection (σ : NMIUMap A (L →L[ℂ] L)) {q : A}
    (hq : IsStarProjection q) : IsStarProjection (σ q) := by
  constructor
  · show σ q * σ q = σ q
    have h : σ (q * q) = σ q * σ q := map_mul σ.toStarAlgHom _ _
    rw [← h, hq.isIdempotentElem.eq]
  · show star (σ q) = σ q
    have h : σ (star q) = star (σ q) := map_star σ.toStarAlgHom _
    rw [← h, hq.isSelfAdjoint.star_eq]

theorem nmiu_vector_fix (σ : NMIUMap A (L →L[ℂ] L)) (v : L) {q : A}
    (hq : IsStarProjection q) (h0 : (⟪v, σ ((1 : A) - q) v⟫ : ℂ) = 0) : σ q v = v := by
  have hone : σ (1 : A) = 1 := map_one σ.toStarAlgHom
  have hsub : σ ((1 : A) - q) = 1 - σ q := by
    have h : σ ((1 : A) - q) = σ (1 : A) - σ q := map_sub σ.toStarAlgHom _ _
    rw [h, hone]
  have hP : IsStarProjection (σ ((1 : A) - q)) := nmiu_isStarProjection σ hq.one_sub
  have hnorm : (⟪v, σ ((1 : A) - q) v⟫ : ℂ) = ⟪σ ((1 : A) - q) v, σ ((1 : A) - q) v⟫ := by
    conv_lhs => rw [← hP.isIdempotentElem.eq]
    rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint, hP.isSelfAdjoint.star_eq]
  rw [hnorm, inner_self_eq_zero, hsub] at h0
  have h1 : v - σ q v = 0 := by simpa using h0
  exact (sub_eq_zero.mp h1).symm

theorem nmiu_orbit_subset_fix (σ : NMIUMap A (L →L[ℂ] L)) (v : L) {q : A}
    (hqc : IsCentral A q) (hv : σ q v = v) :
    closure {z : L | ∃ a : A, z = σ a v} ⊆ {z : L | σ q z = z} := by
  refine closure_minimal ?_ (isClosed_eq (σ q).continuous continuous_id)
  rintro _ ⟨a, rfl⟩
  show σ q (σ a v) = σ a v
  have h1 : σ (q * a) = σ q * σ a := map_mul σ.toStarAlgHom _ _
  have h2 : σ (a * q) = σ a * σ q := map_mul σ.toStarAlgHom _ _
  calc σ q (σ a v) = (σ q * σ a) v := rfl
    _ = σ (q * a) v := by rw [h1]
    _ = σ (a * q) v := by rw [hqc a]
    _ = (σ a * σ q) v := by rw [h2]
    _ = σ a (σ q v) := rfl
    _ = σ a v := by rw [hv]

theorem nmiu_central_preimage (π : NMIUMap A (L →L[ℂ] L)) {p : L →L[ℂ] L}
    (hp : IsStarProjection p) (w : A) (hw : π w = p)
    (hcomm : ∀ a : A, p * π a = π a * p) :
    ∃ z : A, IsStarProjection z ∧ IsCentral A z ∧ π z = p := by
  set g : A →ₚ[ℂ] (L →L[ℂ] L) := nmiuP π with hg
  have hgp : PreservesDirSups ⇑g := π.preservesDirSups'
  have heq : ∀ a, (g a : L →L[ℂ] L) = π a := fun a => rfl
  set c : A := carrier g hgp with hc
  have hcproj : IsStarProjection c := (carrier_spec g hgp).1
  have hccen : IsCentral A c := (carrier_miu π g hgp heq).1
  refine ⟨c * w, ?_, ?_, ?_⟩
  · constructor
    · show c * w * (c * w) = c * w
      have hstep : c * (w * w) = c * w := by
        refine ((nmiu_factors π g hgp heq (w * w) w).2).mp ?_
        have h : π (w * w) = π w * π w := map_mul π.toStarAlgHom _ _
        rw [h, hw, hp.isIdempotentElem.eq]
      calc c * w * (c * w) = c * (w * c) * w := by noncomm_ring
        _ = c * (c * w) * w := by rw [hccen w]
        _ = c * (c * (w * w)) := by noncomm_ring
        _ = c * (c * w) := by rw [hstep]
        _ = c * w := by rw [← mul_assoc, hcproj.isIdempotentElem.eq]
    · show star (c * w) = c * w
      have hstep : c * star w = c * w := by
        refine ((nmiu_factors π g hgp heq (star w) w).2).mp ?_
        have h : π (star w) = star (π w) := map_star π.toStarAlgHom _
        rw [h, hw, hp.isSelfAdjoint.star_eq]
      rw [star_mul, hcproj.isSelfAdjoint.star_eq, ← hccen (star w), hstep]
  · intro b
    have hstep : c * (w * b) = c * (b * w) := by
      refine ((nmiu_factors π g hgp heq (w * b) (b * w)).2).mp ?_
      have h1 : π (w * b) = π w * π b := map_mul π.toStarAlgHom _ _
      have h2 : π (b * w) = π b * π w := map_mul π.toStarAlgHom _ _
      rw [h1, h2, hw, hcomm b]
    calc c * w * b = c * (w * b) := by noncomm_ring
      _ = c * (b * w) := hstep
      _ = c * b * w := by noncomm_ring
      _ = b * c * w := by rw [hccen b]
      _ = b * (c * w) := by noncomm_ring
  · have h := (nmiu_factors π g hgp heq w w).1
    rw [← h, hw]

end Helpers

/-- **89V** (`sigma-weak-lemma-2`, vn.tex:6980, Lemma): let `Ω` be a
collection of np-functionals on a von Neumann algebra `A` with pairwise
orthogonal central carriers, and let `ρ : A → B(H)`, `π : A → B(K)` be
nmiu-maps such that each `ω ∈ Ω` is given by vectors `x_ω ∈ H` and
`y_ω ∈ K`.  Then there is a bounded `U : K → H` intertwining `π` and `ρ`
such that

> `U*U` is a projection in `π(𝒜)^□` with
> `⌈⌈U*U⌉⌉_{π(𝒜)^□} = π(∑_ω ⌈⌈ω⌉⌉)`, **and** `UU*` is a projection in
> `ϱ(𝒜)^□` with `⌈⌈UU*⌉⌉_{ϱ(𝒜)^□} = ϱ(∑_ω ⌈⌈ω⌉⌉)`.

Both halves are stated: the Lemma's conclusion is symmetric, and it is the
`UU*` half that gives the hypothesis vectors `x_ω ∈ H` a conclusion of their
own.  The relative *central* carrier `⌈⌈·⌉⌉_{R}` is rendered, as everywhere
in this file (cf. **88IX** `commutant_cceil`), by its defining `IsLeast`
property inside the ambient `B(H)`: least among the projections of `R` that
are central in `R` and dominate the given one.

Proof: 890.60's.  **89I** `gns_mapping_property` for each `ω` gives partial
isometries `U_ω` with `U_ω*U_ω = ⌈τ'_ω⌉` and `U_ωU_ω* = ⌈σ'_ω⌉`; both
families are pairwise orthogonal because `⌈σ'_ω⌉ ≤ ⌈⌈σ'_ω⌉⌉ = ⌈⌈σ_ω⌉⌉ =
ϱ(⌈⌈ω⌉⌉)` (**88IX**) and the `⌈⌈ω⌉⌉` are; **89III**
`summing_partial_isometries` sums them, and **83V** `cceil-sum` identifies
the two central carriers. -/
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
        (π (projSup {c : A | ∃ ω ∈ Ω, c = cceil (npCarrier ω)})) ∧
      IsStarProjection (U ∘L ContinuousLinearMap.adjoint U) ∧
      U ∘L ContinuousLinearMap.adjoint U ∈
        commutant (H →L[ℂ] H) (Set.range fun a : A => (ρ a : H →L[ℂ] H)) ∧
      IsLeast {p : H →L[ℂ] H |
          p ∈ commutant (H →L[ℂ] H)
            (Set.range fun a : A => (ρ a : H →L[ℂ] H)) ∧
          IsStarProjection p ∧
          (∀ b ∈ commutant (H →L[ℂ] H)
            (Set.range fun a : A => (ρ a : H →L[ℂ] H)), p * b = b * p) ∧
          U ∘L ContinuousLinearMap.adjoint U ≤ p}
        (ρ (projSup {c : A | ∃ ω ∈ Ω, c = cceil (npCarrier ω)})) := by
  classical
  set c : Ω → A := fun ω => cceil (npCarrier (ω : NPFunctional A)) with hcdef
  have hcproj : ∀ ω : Ω, IsStarProjection (c ω) := fun ω => (cceil_isLeast _).1.1
  have hccen : ∀ ω : Ω, IsCentral A (c ω) := fun ω => (cceil_isLeast _).1.2.1
  have hcorth : Pairwise fun ω ω' : Ω => c ω * c ω' = 0 := fun ω ω' h =>
    horth ω.1 ω.2 ω'.1 ω'.2 fun hh => h (Subtype.ext hh)
  -- each `ω` kills `(c ω)^⊥`
  have hkill : ∀ ω : Ω, ((ω : NPFunctional A) ((1 : A) - c ω)) = 0 := by
    intro ω
    have hcar : IsStarProjection (npCarrier (ω : NPFunctional A)) := (carrier_spec _ _).1
    have h0 : ((ω : NPFunctional A) ((1 : A) - npCarrier (ω : NPFunctional A))) = 0 :=
      (carrier_spec _ _).2.1
    have hle : npCarrier (ω : NPFunctional A) ≤ c ω := (cceil_fundamental _ hcar).1.1.2.2
    set f : A →ₚ[ℂ] ℂ := (ω : NPFunctional A).toPositiveLinearMap with hf
    have hfeq : ∀ a : A, (f a : ℂ) = (ω : NPFunctional A) a := fun _ => rfl
    have h1 : (f ((1 : A) - c ω) : ℂ) ≤ f ((1 : A) - npCarrier (ω : NPFunctional A)) :=
      f.monotone (sub_le_sub_left hle 1)
    have h2 : (0 : ℂ) ≤ f ((1 : A) - c ω) := by
      have h3 : (f (0 : A) : ℂ) ≤ f ((1 : A) - c ω) :=
        f.monotone (by simpa using (hcproj ω).le_one)
      rwa [map_zero] at h3
    simp only [hfeq] at h1 h2
    rw [h0] at h1
    exact le_antisymm h1 h2
  have hfixx : ∀ ω : Ω, ρ (c ω) (x ω) = x ω := fun ω =>
    nmiu_vector_fix ρ (x ω) (hcproj ω) (by rw [← hx ω, hkill ω])
  have hfixy : ∀ ω : Ω, π (c ω) (y ω) = y ω := fun ω =>
    nmiu_vector_fix π (y ω) (hcproj ω) (by rw [← hy ω, hkill ω])
  -- the partial isometries of **89I**
  choose U hUfixH hUfixK hUprojH hUprojK hUint using
    fun ω : Ω => gns_mapping_property (ω : NPFunctional A) ρ π (x ω) (y ω) (hx ω) (hy ω)
  set p : Ω → (K →L[ℂ] K) := fun ω => ContinuousLinearMap.adjoint (U ω) ∘L U ω with hpdef
  set q : Ω → (H →L[ℂ] H) := fun ω => U ω ∘L ContinuousLinearMap.adjoint (U ω) with hqdef
  -- the range projections sit under the images of the central carriers
  have hple : ∀ ω : Ω, p ω ≤ π (c ω) := fun ω =>
    isStarProjection_le_of_fix_subset (hUprojK ω) (nmiu_isStarProjection π (hcproj ω))
      (by rw [hUfixK ω]; exact nmiu_orbit_subset_fix π (y ω) (hccen ω) (hfixy ω))
  have hqle : ∀ ω : Ω, q ω ≤ ρ (c ω) := fun ω =>
    isStarProjection_le_of_fix_subset (hUprojH ω) (nmiu_isStarProjection ρ (hcproj ω))
      (by rw [hUfixH ω]; exact nmiu_orbit_subset_fix ρ (x ω) (hccen ω) (hfixx ω))
  -- hence pairwise orthogonal
  have horthgen : ∀ {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
      {e f g h : M}, IsStarProjection e →
      IsStarProjection f → IsStarProjection g → IsStarProjection h →
      e ≤ g → f ≤ h → g * h = 0 → e * f = 0 := by
    intro M _ _ _ e f g h he hf hg hh heg hfh hgh
    have h1 : e * g = e := ((projection_below_effect g e ⟨hg.nonneg, hg.le_one⟩ he).out 0 7).mp heg
    have h2 : h * f = f := ((projection_below_effect h f ⟨hh.nonneg, hh.le_one⟩ hf).out 0 6).mp hfh
    calc e * f = (e * g) * (h * f) := by rw [h1, h2]
      _ = e * (g * h) * f := by noncomm_ring
      _ = 0 := by rw [hgh]; noncomm_ring
  have hπorth : ∀ ω ω' : Ω, ω ≠ ω' → π (c ω) * π (c ω') = 0 := by
    intro ω ω' hne
    have h : π (c ω * c ω') = π (c ω) * π (c ω') := map_mul π.toStarAlgHom _ _
    have hz : π (0 : A) = 0 := map_zero π.toStarAlgHom
    rw [← h, hcorth hne, hz]
  have hρorth : ∀ ω ω' : Ω, ω ≠ ω' → ρ (c ω) * ρ (c ω') = 0 := by
    intro ω ω' hne
    have h : ρ (c ω * c ω') = ρ (c ω) * ρ (c ω') := map_mul ρ.toStarAlgHom _ _
    have hz : ρ (0 : A) = 0 := map_zero ρ.toStarAlgHom
    rw [← h, hcorth hne, hz]
  have horthK : Pairwise fun ω ω' : Ω => p ω ∘L p ω' = 0 := fun ω ω' hne =>
    horthgen (hUprojK ω) (hUprojK ω') (nmiu_isStarProjection π (hcproj ω))
      (nmiu_isStarProjection π (hcproj ω')) (hple ω) (hple ω') (hπorth ω ω' hne)
  have horthH : Pairwise fun ω ω' : Ω => q ω ∘L q ω' = 0 := fun ω ω' hne =>
    horthgen (hUprojH ω) (hUprojH ω') (nmiu_isStarProjection ρ (hcproj ω))
      (nmiu_isStarProjection ρ (hcproj ω')) (hqle ω) (hqle ω') (hρorth ω ω' hne)
  -- **89III**: sum them
  obtain ⟨V, hVinner, hVsumK, hVsumH⟩ :=
    summing_partial_isometries U hUprojK horthK horthH
  set P : K →L[ℂ] K := ContinuousLinearMap.adjoint V ∘L V with hPdef
  set Q : H →L[ℂ] H := V ∘L ContinuousLinearMap.adjoint V with hQdef
  -- `V` intertwines `π` and `ρ`
  have hρadj : ∀ a : A, ContinuousLinearMap.adjoint (ρ a) = ρ (star a) := by
    intro a
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (map_star ρ.toStarAlgHom a).symm
  have hπadj : ∀ a : A, ContinuousLinearMap.adjoint (π a) = π (star a) := by
    intro a
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (map_star π.toStarAlgHom a).symm
  have hVint : ∀ a : A, V ∘L π a = ρ a ∘L V := by
    intro a
    ext z
    show V (π a z) = ρ a (V z)
    refine ext_inner_left ℂ ?_
    intro w
    have h2 : HasSum (fun ω : Ω => (⟪ρ (star a) w, U ω z⟫ : ℂ)) ⟪ρ (star a) w, V z⟫ :=
      hVinner z (ρ (star a) w)
    have heq : ∀ ω : Ω, (⟪w, U ω (π a z)⟫ : ℂ) = ⟪ρ (star a) w, U ω z⟫ := by
      intro ω
      have h3 : U ω (π a z) = ρ a (U ω z) :=
        congrArg (fun T : K →L[ℂ] H => T z) (hUint ω a)
      rw [h3, ← hρadj a]
      exact (ContinuousLinearMap.adjoint_inner_left (ρ a) (U ω z) w).symm
    have h1 : HasSum (fun ω : Ω => (⟪ρ (star a) w, U ω z⟫ : ℂ)) ⟪w, V (π a z)⟫ := by
      simpa only [heq] using hVinner (π a z) w
    rw [h1.unique h2, ← hρadj a]
    exact ContinuousLinearMap.adjoint_inner_left (ρ a) (V z) w
  -- `P = V*V` is a projection: the `p ω` are orthogonal and sum to it
  have hpP : ∀ (ν : Ω) (z : K), p ν (P z) = p ν z := by
    intro ν z
    have h1 : HasSum (fun ω : Ω => p ν (p ω z)) (p ν (P z)) :=
      (hVsumK z).map (p ν) (ContinuousLinearMap.continuous _)
    have h2 : HasSum (fun ω : Ω => p ν (p ω z)) (p ν (p ν z)) := by
      refine hasSum_single ν ?_
      intro ω hω
      have h3 : p ν ∘L p ω = 0 := horthK (Ne.symm hω)
      exact congrArg (fun T : K →L[ℂ] K => T z) h3
    have h4 : p ν (p ν z) = p ν z := by
      have := (hUprojK ν).isIdempotentElem.eq
      exact congrArg (fun T : K →L[ℂ] K => T z) this
    rw [← h4]
    exact h1.unique h2
  have hPproj : IsStarProjection P := by
    constructor
    · show P * P = P
      ext z
      show P (P z) = P z
      have h1 : HasSum (fun ω : Ω => p ω (P z)) (P (P z)) := hVsumK (P z)
      have h2 : HasSum (fun ω : Ω => p ω (P z)) (P z) := by
        simpa only [hpP] using hVsumK z
      exact h1.unique h2
    · show star P = P
      rw [hPdef, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint]
  have hpleP : ∀ ν : Ω, p ν ≤ P := by
    intro ν
    refine ((projection_below_effect P (p ν) ⟨hPproj.nonneg, hPproj.le_one⟩
      (hUprojK ν)).out 0 7).mpr ?_
    ext z
    show p ν (P z) = p ν z
    exact hpP ν z
  -- `P` commutes with `π(A)`
  have hadjint : ∀ a : A, π a ∘L ContinuousLinearMap.adjoint V
      = ContinuousLinearMap.adjoint V ∘L ρ a := by
    intro a
    have h := congrArg ContinuousLinearMap.adjoint (hVint (star a))
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, hπadj, hρadj,
      star_star] at h
    exact h
  have hPcomm : ∀ a : A, P * π a = π a * P := by
    intro a
    calc P * π a = ContinuousLinearMap.adjoint V ∘L (V ∘L π a) := rfl
      _ = ContinuousLinearMap.adjoint V ∘L (ρ a ∘L V) := by rw [hVint a]
      _ = (ContinuousLinearMap.adjoint V ∘L ρ a) ∘L V := rfl
      _ = (π a ∘L ContinuousLinearMap.adjoint V) ∘L V := by rw [hadjint a]
      _ = π a * P := rfl
  -- the central projection `e = ∑_ω ⌈⌈ω⌉⌉`
  set E : Set A := {c' : A | ∃ ω ∈ Ω, c' = cceil (npCarrier ω)} with hEdef
  have hEeq : E = Set.range c := by
    ext z
    constructor
    · rintro ⟨ω, hω, rfl⟩; exact ⟨⟨ω, hω⟩, rfl⟩
    · rintro ⟨w, rfl⟩; exact ⟨w.1, w.2, rfl⟩
  have hEproj : ∀ z ∈ E, IsStarProjection z := by
    rw [hEeq]; rintro _ ⟨w, rfl⟩; exact hcproj w
  have hEcen : ∀ z ∈ E, IsCentral A z := by
    rw [hEeq]; rintro _ ⟨w, rfl⟩; exact hccen w
  obtain ⟨heproj, heub, heleast⟩ := projSup_spec hEproj
  have hecen : IsCentral A (projSup E) := projSup_isCentral hEproj hEcen
  set e : A := projSup E with hedef
  have hπmono : ∀ {a b : A}, a ≤ b → (π a : K →L[ℂ] K) ≤ π b := fun h => (nmiuP π).monotone h
  have hπeproj : IsStarProjection (π e) := nmiu_isStarProjection π heproj
  have hπecomm : ∀ a : A, (π e : K →L[ℂ] K) * π a = π a * π e := by
    intro a
    have h1 : π (e * a) = (π e : K →L[ℂ] K) * π a := map_mul π.toStarAlgHom _ _
    have h2 : π (a * e) = (π a : K →L[ℂ] K) * π e := map_mul π.toStarAlgHom _ _
    rw [← h1, ← h2, hecen a]
  have hπemem : (π e : K →L[ℂ] K) ∈
      commutant (K →L[ℂ] K) (Set.range fun a : A => (π a : K →L[ℂ] K)) := by
    rintro _ ⟨a, rfl⟩
    exact (hπecomm a).symm
  -- the centre of `π(A)` is the centre of `π(A)□` (**88VIII**), via **69IVb**
  have hRset : (π.toStarAlgHom.range : Set (K →L[ℂ] K))
      = Set.range fun a : A => (π a : K →L[ℂ] K) := by
    ext b
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩
  have hcc := centre_commutant π.toStarAlgHom.range (nmiu_image π)
  rw [hRset] at hcc
  have hπecentre : ∀ b ∈ commutant (K →L[ℂ] K)
      (Set.range fun a : A => (π a : K →L[ℂ] K)), (π e : K →L[ℂ] K) * b = b * π e := by
    have hmem : (π e : K →L[ℂ] K) ∈ (Set.range fun a : A => (π a : K →L[ℂ] K)) ∩
        commutant (K →L[ℂ] K) (Set.range fun a : A => (π a : K →L[ℂ] K)) := ⟨⟨e, rfl⟩, hπemem⟩
    rw [hcc] at hmem
    intro b hb
    exact (hmem.2 b hb).symm
  have hce : ∀ ω : Ω, c ω ≤ e := fun ω => heub (c ω) (by rw [hEeq]; exact ⟨ω, rfl⟩)
  have hpπe : ∀ ω : Ω, (π e : K →L[ℂ] K) * p ω = p ω := fun ω =>
    ((projection_below_effect (π e) (p ω) ⟨hπeproj.nonneg, hπeproj.le_one⟩
      (hUprojK ω)).out 0 6).mp (le_trans (hple ω) (hπmono (hce ω)))
  have hPle : P ≤ π e := by
    refine ((projection_below_effect (π e) P ⟨hπeproj.nonneg, hπeproj.le_one⟩
      hPproj).out 0 6).mpr ?_
    ext z
    show (π e : K →L[ℂ] K) (P z) = P z
    have h1 : HasSum (fun ω : Ω => (π e : K →L[ℂ] K) (p ω z)) ((π e : K →L[ℂ] K) (P z)) :=
      (hVsumK z).map (π e : K →L[ℂ] K) (ContinuousLinearMap.continuous _)
    have h2 : HasSum (fun ω : Ω => (π e : K →L[ℂ] K) (p ω z)) (P z) := by
      have hstep : ∀ ω : Ω, (π e : K →L[ℂ] K) (p ω z) = p ω z := fun ω =>
        congrArg (fun T : K →L[ℂ] K => T z) (hpπe ω)
      simpa only [hstep] using hVsumK z
    exact h1.unique h2
  -- the fixed vectors
  have hyfix : ∀ ω : Ω, p ω (y ω) = y ω := by
    intro ω
    have hmem : y ω ∈ {z : K | p ω z = z} := by
      rw [hUfixK ω]
      refine subset_closure ⟨1, ?_⟩
      have h : π (1 : A) = 1 := map_one π.toStarAlgHom
      rw [h]; rfl
    exact hmem
  /- ### The `UU*` half, on `H`: the same argument with `ρ` for `π`, `x` for
  `y`, `q ω = U_ω U_ω*` for `p ω = U_ω* U_ω`, and `Q = VV*` for `P = V*V`. -/
  have hqQ : ∀ (ν : Ω) (z : H), q ν (Q z) = q ν z := by
    intro ν z
    have h1 : HasSum (fun ω : Ω => q ν (q ω z)) (q ν (Q z)) :=
      (hVsumH z).map (q ν) (ContinuousLinearMap.continuous _)
    have h2 : HasSum (fun ω : Ω => q ν (q ω z)) (q ν (q ν z)) := by
      refine hasSum_single ν ?_
      intro ω hω
      have h3 : q ν ∘L q ω = 0 := horthH (Ne.symm hω)
      exact congrArg (fun T : H →L[ℂ] H => T z) h3
    have h4 : q ν (q ν z) = q ν z := by
      have := (hUprojH ν).isIdempotentElem.eq
      exact congrArg (fun T : H →L[ℂ] H => T z) this
    rw [← h4]
    exact h1.unique h2
  have hQproj : IsStarProjection Q := by
    constructor
    · show Q * Q = Q
      ext z
      show Q (Q z) = Q z
      have h1 : HasSum (fun ω : Ω => q ω (Q z)) (Q (Q z)) := hVsumH (Q z)
      have h2 : HasSum (fun ω : Ω => q ω (Q z)) (Q z) := by
        simpa only [hqQ] using hVsumH z
      exact h1.unique h2
    · show star Q = Q
      rw [hQdef, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint]
  have hqleQ : ∀ ν : Ω, q ν ≤ Q := by
    intro ν
    refine ((projection_below_effect Q (q ν) ⟨hQproj.nonneg, hQproj.le_one⟩
      (hUprojH ν)).out 0 7).mpr ?_
    ext z
    show q ν (Q z) = q ν z
    exact hqQ ν z
  have hQcomm : ∀ a : A, Q * ρ a = ρ a * Q := by
    intro a
    calc Q * ρ a = V ∘L (ContinuousLinearMap.adjoint V ∘L ρ a) := rfl
      _ = V ∘L (π a ∘L ContinuousLinearMap.adjoint V) := by rw [hadjint a]
      _ = (V ∘L π a) ∘L ContinuousLinearMap.adjoint V := rfl
      _ = (ρ a ∘L V) ∘L ContinuousLinearMap.adjoint V := by rw [hVint a]
      _ = ρ a * Q := rfl
  have hρmono : ∀ {a b : A}, a ≤ b → (ρ a : H →L[ℂ] H) ≤ ρ b := fun h => (nmiuP ρ).monotone h
  have hρeproj : IsStarProjection (ρ e) := nmiu_isStarProjection ρ heproj
  have hρecomm : ∀ a : A, (ρ e : H →L[ℂ] H) * ρ a = ρ a * ρ e := by
    intro a
    have h1 : ρ (e * a) = (ρ e : H →L[ℂ] H) * ρ a := map_mul ρ.toStarAlgHom _ _
    have h2 : ρ (a * e) = (ρ a : H →L[ℂ] H) * ρ e := map_mul ρ.toStarAlgHom _ _
    rw [← h1, ← h2, hecen a]
  have hρemem : (ρ e : H →L[ℂ] H) ∈
      commutant (H →L[ℂ] H) (Set.range fun a : A => (ρ a : H →L[ℂ] H)) := by
    rintro _ ⟨a, rfl⟩
    exact (hρecomm a).symm
  have hρRset : (ρ.toStarAlgHom.range : Set (H →L[ℂ] H))
      = Set.range fun a : A => (ρ a : H →L[ℂ] H) := by
    ext b
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩
  have hρcc := centre_commutant ρ.toStarAlgHom.range (nmiu_image ρ)
  rw [hρRset] at hρcc
  have hρecentre : ∀ b ∈ commutant (H →L[ℂ] H)
      (Set.range fun a : A => (ρ a : H →L[ℂ] H)), (ρ e : H →L[ℂ] H) * b = b * ρ e := by
    have hmem : (ρ e : H →L[ℂ] H) ∈ (Set.range fun a : A => (ρ a : H →L[ℂ] H)) ∩
        commutant (H →L[ℂ] H) (Set.range fun a : A => (ρ a : H →L[ℂ] H)) := ⟨⟨e, rfl⟩, hρemem⟩
    rw [hρcc] at hmem
    intro b hb
    exact (hmem.2 b hb).symm
  have hqρe : ∀ ω : Ω, (ρ e : H →L[ℂ] H) * q ω = q ω := fun ω =>
    ((projection_below_effect (ρ e) (q ω) ⟨hρeproj.nonneg, hρeproj.le_one⟩
      (hUprojH ω)).out 0 6).mp (le_trans (hqle ω) (hρmono (hce ω)))
  have hQle : Q ≤ ρ e := by
    refine ((projection_below_effect (ρ e) Q ⟨hρeproj.nonneg, hρeproj.le_one⟩
      hQproj).out 0 6).mpr ?_
    ext z
    show (ρ e : H →L[ℂ] H) (Q z) = Q z
    have h1 : HasSum (fun ω : Ω => (ρ e : H →L[ℂ] H) (q ω z)) ((ρ e : H →L[ℂ] H) (Q z)) :=
      (hVsumH z).map (ρ e : H →L[ℂ] H) (ContinuousLinearMap.continuous _)
    have h2 : HasSum (fun ω : Ω => (ρ e : H →L[ℂ] H) (q ω z)) (Q z) := by
      have hstep : ∀ ω : Ω, (ρ e : H →L[ℂ] H) (q ω z) = q ω z := fun ω =>
        congrArg (fun T : H →L[ℂ] H => T z) (hqρe ω)
      simpa only [hstep] using hVsumH z
    exact h1.unique h2
  have hxfixq : ∀ ω : Ω, q ω (x ω) = x ω := by
    intro ω
    have hmem : x ω ∈ {z : H | q ω z = z} := by
      rw [hUfixH ω]
      refine subset_closure ⟨1, ?_⟩
      have h : ρ (1 : A) = 1 := map_one ρ.toStarAlgHom
      rw [h]; rfl
    exact hmem
  refine ⟨V, hVint, hPproj, ?_, ⟨⟨hπemem, hπeproj, hπecentre, hPle⟩, ?_⟩,
    hQproj, ?_, ⟨⟨hρemem, hρeproj, hρecentre, hQle⟩, ?_⟩⟩
  · rintro _ ⟨a, rfl⟩
    exact (hPcomm a).symm
  · -- the `U*U` half, uniqueness
    rintro pp ⟨hpmem, hppproj, hpcentre, hpge⟩
    -- `pp` lies in `π(A)`, hence is `π` of a central projection
    have hmem2 : pp ∈ commutant (K →L[ℂ] K) (Set.range fun a : A => (π a : K →L[ℂ] K)) ∩
        commutant (K →L[ℂ] K)
          (commutant (K →L[ℂ] K) (Set.range fun a : A => (π a : K →L[ℂ] K))) :=
      ⟨hpmem, fun b hb => (hpcentre b hb).symm⟩
    rw [← hcc] at hmem2
    obtain ⟨w, hw⟩ := hmem2.1
    have hppcomm : ∀ a : A, pp * π a = π a * pp := fun a => (hpmem _ ⟨a, rfl⟩).symm
    obtain ⟨z, hzproj, hzcen, hzπ⟩ := nmiu_central_preimage π hppproj w hw hppcomm
    -- `pp` fixes every `y ω`, so `ω((1-z)) = 0`
    have hppfix : ∀ ω : Ω, pp (y ω) = y ω := by
      intro ω
      have hle2 : p ω ≤ pp := le_trans (hpleP ω) hpge
      have hmul : pp * p ω = p ω :=
        ((projection_below_effect pp (p ω) ⟨hppproj.nonneg, hppproj.le_one⟩
          (hUprojK ω)).out 0 6).mp hle2
      have h := congrArg (fun T : K →L[ℂ] K => T (y ω)) hmul
      simp only [ContinuousLinearMap.mul_apply] at h
      rw [hyfix ω] at h
      exact h
    have hzkill : ∀ ω : Ω, ((ω : NPFunctional A) ((1 : A) - z)) = 0 := by
      intro ω
      have hone : π (1 : A) = 1 := map_one π.toStarAlgHom
      have hsub : π ((1 : A) - z) = 1 - pp := by
        have h : π ((1 : A) - z) = π (1 : A) - π z := map_sub π.toStarAlgHom _ _
        rw [h, hone, hzπ]
      rw [hy ω ((1 : A) - z), hsub]
      show (⟪y ω, ((1 : K →L[ℂ] K) - pp) (y ω)⟫ : ℂ) = 0
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hppfix ω,
        sub_self, inner_zero_right]
    have hcz : ∀ ω : Ω, c ω ≤ z := by
      intro ω
      have hcar : IsStarProjection (npCarrier (ω : NPFunctional A)) := (carrier_spec _ _).1
      have hnp : npCarrier (ω : NPFunctional A) ≤ z :=
        (carrier_spec _ _).2.2 z hzproj (hzkill ω)
      exact (cceil_fundamental _ hcar).1.2 ⟨hzproj, hzcen, hnp⟩
    have hez : e ≤ z := heleast z hzproj (by rw [hEeq]; rintro _ ⟨w', rfl⟩; exact hcz w')
    calc (π e : K →L[ℂ] K) ≤ π z := hπmono hez
      _ = pp := hzπ
  · rintro _ ⟨a, rfl⟩
    exact (hQcomm a).symm
  · -- the `UU*` half, uniqueness: the mirror of the `U*U` argument above
    rintro pp ⟨hpmem, hppproj, hpcentre, hpge⟩
    have hmem2 : pp ∈ commutant (H →L[ℂ] H) (Set.range fun a : A => (ρ a : H →L[ℂ] H)) ∩
        commutant (H →L[ℂ] H)
          (commutant (H →L[ℂ] H) (Set.range fun a : A => (ρ a : H →L[ℂ] H))) :=
      ⟨hpmem, fun b hb => (hpcentre b hb).symm⟩
    rw [← hρcc] at hmem2
    obtain ⟨w, hw⟩ := hmem2.1
    have hppcomm : ∀ a : A, pp * ρ a = ρ a * pp := fun a => (hpmem _ ⟨a, rfl⟩).symm
    obtain ⟨z, hzproj, hzcen, hzρ⟩ := nmiu_central_preimage ρ hppproj w hw hppcomm
    have hppfix : ∀ ω : Ω, pp (x ω) = x ω := by
      intro ω
      have hle2 : q ω ≤ pp := le_trans (hqleQ ω) hpge
      have hmul : pp * q ω = q ω :=
        ((projection_below_effect pp (q ω) ⟨hppproj.nonneg, hppproj.le_one⟩
          (hUprojH ω)).out 0 6).mp hle2
      have h := congrArg (fun T : H →L[ℂ] H => T (x ω)) hmul
      simp only [ContinuousLinearMap.mul_apply] at h
      rw [hxfixq ω] at h
      exact h
    have hzkill : ∀ ω : Ω, ((ω : NPFunctional A) ((1 : A) - z)) = 0 := by
      intro ω
      have hone : ρ (1 : A) = 1 := map_one ρ.toStarAlgHom
      have hsub : ρ ((1 : A) - z) = 1 - pp := by
        have h : ρ ((1 : A) - z) = ρ (1 : A) - ρ z := map_sub ρ.toStarAlgHom _ _
        rw [h, hone, hzρ]
      rw [hx ω ((1 : A) - z), hsub]
      show (⟪x ω, ((1 : H →L[ℂ] H) - pp) (x ω)⟫ : ℂ) = 0
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hppfix ω,
        sub_self, inner_zero_right]
    have hcz : ∀ ω : Ω, c ω ≤ z := by
      intro ω
      have hcar : IsStarProjection (npCarrier (ω : NPFunctional A)) := (carrier_spec _ _).1
      have hnp : npCarrier (ω : NPFunctional A) ≤ z :=
        (carrier_spec _ _).2.2 z hzproj (hzkill ω)
      exact (cceil_fundamental _ hcar).1.2 ⟨hzproj, hzcen, hnp⟩
    have hez : e ≤ z := heleast z hzproj (by rw [hEeq]; rintro _ ⟨w', rfl⟩; exact hcz w')
    calc (ρ e : H →L[ℂ] H) ≤ ρ z := hρmono hez
      _ = pp := hzρ


/-- **89VII** (`sigma-weak-lemma`, vn.tex:7080, Corollary): let `A` be
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
        1 := by
  classical
  -- the vector functional of `v ∈ H`, as an np-functional on `A`
  set vf : H → NPFunctional A :=
    fun v => compNP (nmiuP ρ) ρ.preservesDirSups' (vectorNP v) with hvf
  have hvfapp : ∀ (v : H) (a : A), vf v a = ⟪v, ρ a v⟫ := fun v a => rfl
  -- a maximal family of vector functionals with pairwise orthogonal central carriers
  set T : Set (Set (NPFunctional A)) :=
    {Ω | (∀ ω ∈ Ω, ∃ v : H, ω = vf v) ∧ (∀ ω ∈ Ω, cceil (npCarrier ω) ≠ 0) ∧
      ∀ ω ∈ Ω, ∀ ω' ∈ Ω, ω ≠ ω' → cceil (npCarrier ω) * cceil (npCarrier ω') = 0} with hT
  obtain ⟨Ω, hΩmax⟩ : ∃ Ω, Maximal (· ∈ T) Ω := by
    refine zorn_subset T fun cc hcc hchain =>
      ⟨⋃₀ cc, ⟨?_, ?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro ω ⟨s, hs, hωs⟩; exact (hcc hs).1 ω hωs
    · rintro ω ⟨s, hs, hωs⟩; exact (hcc hs).2.1 ω hωs
    · rintro ω ⟨s, hs, hωs⟩ ω' ⟨s', hs', hω's'⟩ hne
      rcases hchain.total hs hs' with hsub | hsub
      · exact (hcc hs').2.2 ω (hsub hωs) ω' hω's' hne
      · exact (hcc hs).2.2 ω hωs ω' (hsub hω's') hne
  obtain ⟨hΩrep, hΩne, hΩorth⟩ := hΩmax.1
  -- the central carriers sum to `1`
  set E : Set A := {c : A | ∃ ω ∈ Ω, c = cceil (npCarrier ω)} with hE
  have hEproj : ∀ z ∈ E, IsStarProjection z := by
    rintro _ ⟨ω, hω, rfl⟩; exact (cceil_isLeast _).1.1
  have hEcen : ∀ z ∈ E, IsCentral A z := by
    rintro _ ⟨ω, hω, rfl⟩; exact (cceil_isLeast _).1.2.1
  obtain ⟨heproj, heub, heleast⟩ := projSup_spec hEproj
  have hecen : IsCentral A (projSup E) := projSup_isCentral hEproj hEcen
  set e : A := projSup E with hedef
  have hone : e = 1 := by
    by_contra hne1
    -- `1 - e ≠ 0`, so `ρ(1-e) ≠ 0`, so some vector is fixed by it
    have hf : (1 : A) - e ≠ 0 := fun h => hne1 (by
      have : (1 : A) = e := by rw [← sub_eq_zero]; exact h
      exact this.symm)
    have hρf : (ρ ((1 : A) - e) : H →L[ℂ] H) ≠ 0 := by
      intro h
      refine hf (hρ ?_)
      have hz : ρ (0 : A) = 0 := map_zero ρ.toStarAlgHom
      rw [h, hz]
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ : H, ρ ((1 : A) - e) v₀ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hρf (by ext v; simpa using hcon v)
    set v : H := ρ ((1 : A) - e) v₀ with hv
    set ω' : NPFunctional A := vf v with hω'
    have hmul : ∀ a b : A, ρ (a * b) = (ρ a : H →L[ℂ] H) * ρ b := fun a b =>
      map_mul ρ.toStarAlgHom a b
    -- `ω'` kills `e`
    have hωe : ω' e = 0 := by
      have hρe : (ρ e : H →L[ℂ] H) v = 0 := by
        have h1 : (ρ e : H →L[ℂ] H) * ρ ((1 : A) - e) = ρ (e * ((1 : A) - e)) := (hmul _ _).symm
        have h2 : e * ((1 : A) - e) = 0 := by
          rw [mul_sub, mul_one, heproj.isIdempotentElem.eq, sub_self]
        have hz : ρ (0 : A) = 0 := map_zero ρ.toStarAlgHom
        have h3 : (ρ e : H →L[ℂ] H) * ρ ((1 : A) - e) = 0 := by rw [h1, h2, hz]
        have := congrArg (fun T : H →L[ℂ] H => T v₀) h3
        simpa [hv] using this
      rw [hω', hvfapp, hρe, inner_zero_right]
    have hcarle : npCarrier ω' ≤ (1 : A) - e := by
      refine (carrier_spec _ _).2.2 _ heproj.one_sub ?_
      have hrw : (1 : A) - ((1 : A) - e) = e := by abel
      rw [hrw]
      exact hωe
    have hecen' : IsCentral A ((1 : A) - e) := fun b => by
      rw [sub_mul, mul_sub, one_mul, mul_one, hecen b]
    have hcceille : cceil (npCarrier ω') ≤ (1 : A) - e :=
      (cceil_fundamental _ (carrier_spec _ _).1).1.2
        ⟨heproj.one_sub, hecen', hcarle⟩
    -- `ω'` is non-degenerate
    have hω'ne : cceil (npCarrier ω') ≠ 0 := by
      intro h
      have hcar0 : npCarrier ω' = 0 := le_antisymm (h ▸ (cceil_fundamental _
        (carrier_spec _ _).1).1.1.2.2) (carrier_spec _ _).1.nonneg
      have h0 : ω' ((1 : A) - npCarrier ω') = 0 := (carrier_spec _ _).2.1
      rw [hcar0, sub_zero] at h0
      have hone' : ρ (1 : A) = 1 := map_one ρ.toStarAlgHom
      rw [hω', hvfapp, hone'] at h0
      have : (⟪v, v⟫ : ℂ) = 0 := by simpa using h0
      exact hv₀ (inner_self_eq_zero.mp this)
    -- adding `ω'` contradicts maximality
    have horthnew : ∀ ω ∈ Ω, cceil (npCarrier ω) * cceil (npCarrier ω') = 0 ∧
        cceil (npCarrier ω') * cceil (npCarrier ω) = 0 := by
      intro ω hω
      have h1 : cceil (npCarrier ω) ≤ e := heub _ ⟨ω, hω, rfl⟩
      have hp1 : IsStarProjection (cceil (npCarrier ω)) := (cceil_isLeast _).1.1
      have hp2 : IsStarProjection (cceil (npCarrier ω')) := (cceil_isLeast _).1.1
      have e1 : cceil (npCarrier ω) * e = cceil (npCarrier ω) :=
        ((projection_below_effect e _ ⟨heproj.nonneg, heproj.le_one⟩ hp1).out 0 7).mp h1
      have e2 : ((1 : A) - e) * cceil (npCarrier ω') = cceil (npCarrier ω') :=
        ((projection_below_effect ((1 : A) - e) _
          ⟨heproj.one_sub.nonneg, heproj.one_sub.le_one⟩ hp2).out 0 6).mp hcceille
      have e3 : cceil (npCarrier ω') * ((1 : A) - e) = cceil (npCarrier ω') :=
        ((projection_below_effect ((1 : A) - e) _
          ⟨heproj.one_sub.nonneg, heproj.one_sub.le_one⟩ hp2).out 0 7).mp hcceille
      have e4 : e * cceil (npCarrier ω) = cceil (npCarrier ω) :=
        ((projection_below_effect e _ ⟨heproj.nonneg, heproj.le_one⟩ hp1).out 0 6).mp h1
      constructor
      · calc cceil (npCarrier ω) * cceil (npCarrier ω')
            = (cceil (npCarrier ω) * e) * (((1 : A) - e) * cceil (npCarrier ω')) := by
              rw [e1, e2]
          _ = cceil (npCarrier ω) * (e * ((1 : A) - e)) * cceil (npCarrier ω') := by
              noncomm_ring
          _ = 0 := by
              rw [mul_sub, mul_one, heproj.isIdempotentElem.eq, sub_self]; noncomm_ring
      · calc cceil (npCarrier ω') * cceil (npCarrier ω)
            = (cceil (npCarrier ω') * ((1 : A) - e)) * (e * cceil (npCarrier ω)) := by
              rw [e3, e4]
          _ = cceil (npCarrier ω') * (((1 : A) - e) * e) * cceil (npCarrier ω) := by
              noncomm_ring
          _ = 0 := by
              rw [sub_mul, one_mul, heproj.isIdempotentElem.eq, sub_self]; noncomm_ring
    have hmem : insert ω' Ω ∈ T := by
      refine ⟨?_, ?_, ?_⟩
      · rintro ω (rfl | hω)
        · exact ⟨v, rfl⟩
        · exact hΩrep ω hω
      · rintro ω (rfl | hω)
        · exact hω'ne
        · exact hΩne ω hω
      · rintro ω (rfl | hω) ω'' (rfl | hω'') hne
        · exact absurd rfl hne
        · exact (horthnew ω'' hω'').2
        · exact (horthnew ω hω).1
        · exact hΩorth ω hω ω'' hω'' hne
    have hsub : Ω ⊆ insert ω' Ω := Set.subset_insert _ _
    have hback := hΩmax.2 hmem hsub
    have hω'Ω : ω' ∈ Ω := hback (Set.mem_insert _ _)
    have h1 : cceil (npCarrier ω') ≤ e := heub _ ⟨ω', hω'Ω, rfl⟩
    have hp2 : IsStarProjection (cceil (npCarrier ω')) := (cceil_isLeast _).1.1
    have e1 : cceil (npCarrier ω') * e = cceil (npCarrier ω') :=
      ((projection_below_effect e _ ⟨heproj.nonneg, heproj.le_one⟩ hp2).out 0 7).mp h1
    have e3 : cceil (npCarrier ω') * ((1 : A) - e) = cceil (npCarrier ω') :=
      ((projection_below_effect ((1 : A) - e) _
        ⟨heproj.one_sub.nonneg, heproj.one_sub.le_one⟩ hp2).out 0 7).mp hcceille
    refine hω'ne ?_
    calc cceil (npCarrier ω') = cceil (npCarrier ω') * ((1 : A) - e) := e3.symm
      _ = cceil (npCarrier ω') - cceil (npCarrier ω') * e := by noncomm_ring
      _ = 0 := by rw [e1, sub_self]
  -- realise the family in both representations
  choose xv hxv using fun ω : Ω => hΩrep ω.1 ω.2
  choose yv hyv using fun ω : Ω => huniv (ω : NPFunctional A)
  obtain ⟨U, hUint, hUproj, hUmem, hUleast, -, -, -⟩ :=
    sigma_weak_lemma_2 Ω (fun ω hω ω' hω' h => hΩorth ω hω ω' hω' h) ρ π xv yv
      (fun ω a => by rw [hxv ω]; exact hvfapp _ _) hyv
  refine ⟨U, hUint, hUproj, hUmem, ?_⟩
  have hEeq : {c : A | ∃ ω ∈ Ω, c = cceil (npCarrier ω)} = E := rfl
  have hπone : (π (projSup {c : A | ∃ ω ∈ Ω, c = cceil (npCarrier ω)}) : K →L[ℂ] K) = 1 := by
    rw [hEeq, ← hedef, hone]
    exact map_one π.toStarAlgHom
  rwa [hπone] at hUleast


/-- Pairwise orthogonal projections of `B(K)` whose supremum is `1` resolve
every vector: `∑ᵢ pᵢ y = y`. -/
theorem hasSum_projSup_apply {ι : Type*} (p : ι → (K →L[ℂ] K))
    (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise fun i j => p i * p j = 0)
    (hsup : projSup (Set.range p) = 1) (y : K) :
    HasSum (fun i => p i y) y := by
  have hus := sum_of_orthogonal_projections p hp horth
  rw [hsup] at hus
  have h := (usTendsto_iff (fun F : Finset ι => ∑ i ∈ F, p i) atTop 1).mp hus (vectorNP y)
  simp only [omegaNorm_vectorNP] at h
  rw [HasSum, tendsto_iff_norm_sub_tendsto_zero]
  refine h.congr fun F => ?_
  congr 1
  simp

/-- The computation at the end of **89IX** (`normal-functional`,
vn.tex:7089): given the partial isometries `(vᵢ)` of the commutant supplied
by the relative form of `cceil-sum`, the vectors `Uvᵢy` represent `ω`. -/
theorem normal_functional_assembly {ι : Type*} (ρ : NMIUMap A (H →L[ℂ] H))
    (π : NMIUMap A (K →L[ℂ] K)) (U : K →L[ℂ] H)
    (hU : ∀ a : A, U ∘L π a = ρ a ∘L U)
    (hQ : IsStarProjection (ContinuousLinearMap.adjoint U ∘L U))
    (v : ι → (K →L[ℂ] K))
    (hvpi : ∀ i, IsPartialIsometry (K →L[ℂ] K) (v i))
    (hvcomm : ∀ (i) (a : A), v i * π a = π a * v i)
    (horth : Pairwise fun i j => (star (v i) * v i) * (star (v j) * v j) = 0)
    (hsup : projSup (Set.range fun i => star (v i) * v i) = 1)
    (hvle : ∀ i, v i * star (v i) ≤ ContinuousLinearMap.adjoint U ∘L U)
    (ω : NPFunctional A) (y : K) (hy : ∀ a : A, ω a = ⟪y, π a y⟫) :
    ∀ a : A, HasSum (fun i => ⟪U (v i y), ρ a (U (v i y))⟫) (ω a) := by
  set Q : K →L[ℂ] K := ContinuousLinearMap.adjoint U ∘L U with hQdef
  -- `Q vᵢ = vᵢ`, because `vᵢvᵢ* ≤ Q`
  have hQv : ∀ i, Q * v i = v i := by
    intro i
    have hvv : IsStarProjection (v i * star (v i)) :=
      ((partial_isometry_equivalents (v i)).out 0 3).mp (hvpi i)
    have h1 : Q * (v i * star (v i)) = v i * star (v i) :=
      ((projection_below_effect Q (v i * star (v i)) ⟨hQ.nonneg, hQ.le_one⟩
        hvv).out 0 6).mp (hvle i)
    have h2 : v i * star (v i) * v i = v i :=
      ((partial_isometry_equivalents (v i)).out 0 2).mp (hvpi i)
    calc Q * v i = Q * (v i * star (v i) * v i) := by rw [h2]
      _ = (Q * (v i * star (v i))) * v i := by noncomm_ring
      _ = v i := by rw [h1, h2]
  set p : ι → (K →L[ℂ] K) := fun i => star (v i) * v i with hpdef
  have hpproj : ∀ i, IsStarProjection (p i) :=
    fun i => ((partial_isometry_equivalents (v i)).out 0 1).mp (hvpi i)
  -- the key term-by-term identity
  have hterm : ∀ (a : A) (i), (⟪U (v i y), ρ a (U (v i y))⟫ : ℂ) = ⟪p i y, π a y⟫ := by
    intro a i
    have e1 : (ρ a : H →L[ℂ] H) (U (v i y)) = U (π a (v i y)) := by
      have := congrArg (fun T : K →L[ℂ] H => T (v i y)) (hU a)
      simpa using this.symm
    have e2 : ContinuousLinearMap.adjoint U (U (v i y)) = v i y := by
      have := congrArg (fun T : K →L[ℂ] K => T y) (hQv i)
      simpa [hQdef] using this
    have e3 : (π a : K →L[ℂ] K) (v i y) = v i ((π a : K →L[ℂ] K) y) := by
      have := congrArg (fun T : K →L[ℂ] K => T y) (hvcomm i a)
      simpa using this.symm
    calc (⟪U (v i y), ρ a (U (v i y))⟫ : ℂ)
        = ⟪U (v i y), U (π a (v i y))⟫ := by rw [e1]
      _ = ⟪ContinuousLinearMap.adjoint U (U (v i y)), π a (v i y)⟫ := by
            rw [ContinuousLinearMap.adjoint_inner_left]
      _ = ⟪v i y, π a (v i y)⟫ := by rw [e2]
      _ = ⟪v i y, v i ((π a : K →L[ℂ] K) y)⟫ := by rw [e3]
      _ = ⟪y, star (v i) (v i ((π a : K →L[ℂ] K) y))⟫ := by
            rw [ContinuousLinearMap.star_eq_adjoint,
              ContinuousLinearMap.adjoint_inner_right]
      _ = ⟪y, p i ((π a : K →L[ℂ] K) y)⟫ := rfl
      _ = ⟪p i y, π a y⟫ := by
            have hself : ContinuousLinearMap.adjoint (p i) = p i := by
              rw [← ContinuousLinearMap.star_eq_adjoint]
              exact (hpproj i).isSelfAdjoint.star_eq
            conv_rhs => rw [← hself]
            rw [ContinuousLinearMap.adjoint_inner_left]
  intro a
  have hres : HasSum (fun i => p i y) y := hasSum_projSup_apply p hpproj horth hsup y
  have h2 : HasSum (fun i => (⟪(π a : K →L[ℂ] K) y, p i y⟫ : ℂ))
      ⟪(π a : K →L[ℂ] K) y, y⟫ := hres.mapL (innerSL ℂ ((π a : K →L[ℂ] K) y))
  have h3 := h2.map (starRingEnd ℂ) Complex.continuous_conj
  simp only [Function.comp_def, inner_conj_symm] at h3
  rw [← hy a] at h3
  exact h3.congr_fun fun i => hterm a i

/-- Zero-padded re-indexing of a square-summable family by `ℕ`. -/
theorem exists_nat_reindex {ι : Type*} (x : ι → H)
    (hs : Summable fun i => ‖x i‖ ^ 2) :
    ∃ (x' : ℕ → H) (φ : Function.support x → ℕ), Function.Injective φ ∧
      (∀ i : Function.support x, x' (φ i) = x i) ∧
      (∀ n, n ∉ Set.range φ → x' n = 0) := by
  classical
  have hsupp : (Function.support fun i => ‖x i‖ ^ 2) = Function.support x := by
    ext i; simp [Function.mem_support]
  have hcount : (Function.support x).Countable := by
    rw [← hsupp]; exact hs.countable_support
  obtain ⟨φ, hφ⟩ := Set.countable_iff_exists_injective.mp hcount
  refine ⟨Function.extend φ (fun i : Function.support x => x i) (fun _ => 0), φ, hφ,
    fun i => hφ.extend_apply _ _ i, fun n hn => ?_⟩
  exact Function.extend_apply' (f := φ) (fun i : Function.support x => x i) (fun _ => 0) n
    (fun h => hn ⟨h.choose, h.choose_spec⟩)

/-- The converse of **89IX**, for an arbitrary index type: a square-summable
family `(xᵢ)ᵢ` of vectors defines an np-functional `T ↦ ∑ᵢ ⟪xᵢ, T xᵢ⟫` on
`B(H)`.

For `ι = ℕ` this is **38IV**.2 `bh_functional_lemma_2`
(`A/CStar/TowardsVN.lean`), already proved; all that is added here is the
re-indexing, since a square-summable family has countable support.  Stated
in `A/VN` because both **89XI** and **111VII**'s condition `tensor-2` need
it, the latter for the family `(n,m) ↦ xₙ ⊗ yₘ` indexed by `ℕ × ℕ`. -/
theorem exists_sumVectorNP {ι : Type*} (x : ι → H)
    (hx : Summable fun i => ‖x i‖ ^ 2) :
    ∃ ω : NPFunctional (H →L[ℂ] H),
      ∀ T : H →L[ℂ] H, HasSum (fun i => ⟪x i, T (x i)⟫) (ω T) := by
  classical
  obtain ⟨x', φ, hφ, hval, hzero⟩ := exists_nat_reindex x hx
  have hx' : Summable fun n => ‖x' n‖ ^ 2 := by
    refine (hφ.summable_iff ?_).mp ?_
    · intro n hn; rw [hzero n hn]; simp
    · exact (hx.subtype _).congr fun i => by
        show ‖x (i : ι)‖ ^ 2 = ‖x' (φ i)‖ ^ 2
        rw [hval i]
  obtain ⟨ν, hν⟩ := bh_functional_lemma_2 x' hx'
  refine ⟨ν, fun T => ?_⟩
  have h1 : HasSum (fun n => ⟪x' n, T (x' n)⟫) (ν T) := by
    rw [hν T]; exact (bh_functional_lemma_1 x' hx' T).hasSum
  have hz : ∀ n ∉ Set.range φ, (⟪x' n, T (x' n)⟫ : ℂ) = 0 := by
    intro n hn; rw [hzero n hn]; simp
  have h2 : HasSum (fun i : Function.support x => ⟪x i, T (x i)⟫) (ν T) := by
    refine ((hφ.hasSum_iff hz).mpr h1).congr_fun fun i => ?_
    rw [Function.comp_apply, hval i]
  have hsub : (Function.support fun i => (⟪x i, T (x i)⟫ : ℂ)) ⊆ Function.support x := by
    intro i hi
    by_contra hc
    simp only [Function.mem_support, not_not] at hc
    exact hi (by simp [hc])
  exact (hasSum_subtype_iff_of_support_subset hsub).mp h2

/-- A family of vectors indexed by an arbitrary type representing an
np-functional can be re-indexed by `ℕ`. -/
theorem exists_nat_index {ι : Type*} (ρ : NMIUMap A (H →L[ℂ] H)) (ω : NPFunctional A)
    (x : ι → H) (hx : ∀ a : A, HasSum (fun i => ⟪x i, ρ a (x i)⟫) (ω a)) :
    ∃ x' : ℕ → H, (Summable fun n => ‖x' n‖ ^ 2) ∧
      ∀ a : A, HasSum (fun n => ⟪x' n, ρ a (x' n)⟫) (ω a) := by
  classical
  -- square-summability is the case `a = 1`
  have hone : ∀ i, (⟪x i, ρ (1 : A) (x i)⟫ : ℂ) = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    have h1 : ρ (1 : A) = 1 := map_one ρ.toStarAlgHom
    rw [h1]
    simp [inner_self_eq_norm_sq_to_K]
  have hsumℂ : HasSum (fun i => ((‖x i‖ ^ 2 : ℝ) : ℂ)) (ω 1) := by
    refine (hx 1).congr_fun fun i => (hone i).symm
  have hsum : Summable fun i => ‖x i‖ ^ 2 := by
    have := hsumℂ.mapL Complex.reCLM
    simpa [← Complex.ofReal_pow] using this.summable
  obtain ⟨x', φ, hφ, hval, hzero⟩ := exists_nat_reindex x hsum
  -- transport a `HasSum` along the re-indexing
  have key : ∀ (g : H → ℂ) (c : ℂ), g 0 = 0 →
      HasSum (fun i => g (x i)) c → HasSum (fun n => g (x' n)) c := by
    intro g c hg0 hgs
    have hsub : Function.support (fun i => g (x i)) ⊆ Function.support x := by
      intro i hi
      by_contra hc
      simp only [Function.mem_support, not_not] at hc
      exact hi (by simp [Function.mem_support, hc, hg0])
    have h1 : HasSum (fun i : Function.support x => g (x i)) c :=
      (hasSum_subtype_iff_of_support_subset hsub).mpr hgs
    refine (hφ.hasSum_iff ?_).mp ?_
    · intro n hn; rw [hzero n hn, hg0]
    · exact h1.congr_fun fun i => by rw [Function.comp_apply, hval i]
  refine ⟨x', ?_, fun a => ?_⟩
  · have : HasSum (fun n => ((‖x' n‖ ^ 2 : ℝ) : ℂ)) (ω 1) := by
      refine key (fun z => ((‖z‖ ^ 2 : ℝ) : ℂ)) (ω 1) (by simp) ?_
      exact hsumℂ
    have := this.mapL Complex.reCLM
    simpa [← Complex.ofReal_pow] using this.summable
  · refine key (fun z => ⟪z, ρ a z⟫) (ω a) (by simp) (hx a)

/-- **89IX** (`normal-functional`, vn.tex:7117, Theorem): every
np-functional `ω` on a von Neumann subalgebra `A` of `B(H)` (given by an
injective nmiu-map `ρ : A → B(H)` with von Neumann subalgebra range) is of
the form `ω = ∑ₙ ⟨xₙ,(·)xₙ⟩` for some `x₁, x₂, … ∈ H` with
`∑ₙ ‖xₙ‖² < ∞`. -/
theorem normal_functional (ρ : NMIUMap A (H →L[ℂ] H))
    (hρ : Function.Injective ⇑ρ)
    (hR : IsVNSubalgebra (H →L[ℂ] H) ρ.toStarAlgHom.range)
    (ω : NPFunctional A) :
    ∃ x : ℕ → H, (Summable fun n => ‖x n‖ ^ 2) ∧
      ∀ a : A, HasSum (fun n => ⟪x n, ρ a (x n)⟫) (ω a) := by
  classical
  -- the universal representation `π` of 89VII
  obtain ⟨K₀, _, _, _, π₀, -, hπn, huniv⟩ := exists_faithful_normal_rep_vectors A
  set π : NMIUMap A (K₀ →L[ℂ] K₀) := ⟨π₀, hπn⟩ with hπdef
  obtain ⟨U, hU, hQproj, hQmem, hQleast⟩ := sigma_weak_lemma ρ hρ hR π huniv
  set C : Set (K₀ →L[ℂ] K₀) :=
    commutant (K₀ →L[ℂ] K₀) (Set.range fun a : A => (π a : K₀ →L[ℂ] K₀)) with hC
  set Q : K₀ →L[ℂ] K₀ := ContinuousLinearMap.adjoint U ∘L U with hQdef
  -- `π(A)□` as a von Neumann subalgebra
  obtain ⟨T, hT, hTcar⟩ :=
    (commutant_basic_3' (Set.range fun a : A => (π a : K₀ →L[ℂ] K₀)) (by
      rintro _ ⟨a, rfl⟩
      exact ⟨star a, by
        show (π (star a) : K₀ →L[ℂ] K₀) = star (π a)
        exact map_star π.toStarAlgHom a⟩)).1
  have hmemT : ∀ p : K₀ →L[ℂ] K₀, p ∈ T ↔ p ∈ C := by
    intro p; rw [← SetLike.mem_coe, hTcar]
  -- the relative `cceil-sum`
  obtain ⟨ι, v, hvT, hvproj, hvorth, hvsup, hvle⟩ :=
    cceil_sum_relative T hT Q ((hmemT Q).mpr hQmem) hQproj
      (by
        constructor
        · exact ⟨(hmemT 1).mpr hQleast.1.1, hQleast.1.2.1,
            fun b hb => hQleast.1.2.2.1 b ((hmemT b).mp hb), hQleast.1.2.2.2⟩
        · rintro p ⟨hp1, hp2, hp3, hp4⟩
          exact hQleast.2 ⟨(hmemT p).mp hp1, hp2,
            fun b hb => hp3 b ((hmemT b).mpr hb), hp4⟩)
  -- the vector representing `ω` in the universal representation
  obtain ⟨y, hy⟩ := huniv ω
  have hvpi : ∀ i, IsPartialIsometry (K₀ →L[ℂ] K₀) (v i) :=
    fun i => ((partial_isometry_equivalents (v i)).out 1 0).mp (hvproj i)
  have hvcomm : ∀ (i) (a : A), v i * π a = π a * v i := by
    intro i a
    exact ((hmemT (v i)).mp (hvT i) (π a) ⟨a, rfl⟩).symm
  exact exists_nat_index ρ ω (fun i => U (v i y))
    (normal_functional_assembly ρ π U hU hQproj v hvpi hvcomm hvorth hvsup hvle ω y hy)

end BH

section Permanence

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B]

/-- **89XI** (`functional-permanence`, vn.tex:7183, Corollary), part 1: for
a von Neumann subalgebra `A` of `B` (an injective nmiu-map `ρ : A → B`
with von Neumann subalgebra range), every np-functional `ω` on `A` extends
to an np-functional `ξ` on `B`: `ξ ∘ ρ = ω`. -/
theorem functional_permanence_1 (ρ : NMIUMap A B)
    (hρ : Function.Injective ⇑ρ)
    (hR : IsVNSubalgebra B ρ.toStarAlgHom.range) (ω : NPFunctional A) :
    ∃ ξ : NPFunctional B, ∀ a : A, ξ (ρ a) = ω a := by
  classical
  -- Represent `B` faithfully and normally on a Hilbert space (**48VIII**
  -- `ngns`).  Then `A` sits inside `B(ℓ²(ι))` through `σ = f ∘ ρ`, which is
  -- again injective and normal, so its range is a von Neumann subalgebra
  -- (**48VI**.1) and **89IX** applies: `ω = ∑ₙ ⟨xₙ, σ(·)xₙ⟩`.  The *same*
  -- square-summable family defines an np-functional `ν` on all of
  -- `B(ℓ²(ι))` — that is **38IV**.2 `bh_functional_lemma_2`, the converse of
  -- 39IX — and `ξ = ν ∘ f` is the required extension.
  -- (The hypothesis `hR` is not needed: `ρ` injective already forces it, by
  -- 48VI.1.  It is kept because the thesis states the corollary for a von
  -- Neumann subalgebra.)
  obtain ⟨ι, f, hfinj, -⟩ := ngns B
  have hσn : PreservesDirSups ⇑(f.toStarAlgHom.comp ρ.toStarAlgHom) :=
    preservesDirSups_pmap_comp (starAlgHomP ρ.toStarAlgHom) ρ.preservesDirSups'
      (starAlgHomP f.toStarAlgHom) f.preservesDirSups'
  set σ : NMIUMap A (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :=
    ⟨f.toStarAlgHom.comp ρ.toStarAlgHom, hσn⟩ with hσ
  have hσinj : Function.Injective ⇑σ := hfinj.comp hρ
  have hσR : IsVNSubalgebra _ σ.toStarAlgHom.range :=
    isVNSubalgebra_range σ.toStarAlgHom hσinj hσn
  obtain ⟨x, hx, hsum⟩ := normal_functional σ hσinj hσR ω
  obtain ⟨ν, hν⟩ := bh_functional_lemma_2 x hx
  have hfP : PreservesDirSups ⇑(nmiuP f) := f.preservesDirSups'
  refine ⟨compNP (nmiuP f) hfP ν, fun a => ?_⟩
  show ν (f (ρ a)) = ω a
  rw [hν]
  exact (hsum a).tsum_eq

/-- **89XI** (`functional-permanence`, vn.tex:7183, Corollary), part 2
(**ultraweak permanence**): the ultraweak topology of a von Neumann
subalgebra `A` of `B` is the restriction of the ultraweak topology of
`B`. -/
theorem functional_permanence_2 (ρ : NMIUMap A B)
    (hρ : Function.Injective ⇑ρ)
    (hR : IsVNSubalgebra B ρ.toStarAlgHom.range) :
    ultraweak A = TopologicalSpace.induced ⇑ρ (ultraweak B) := by
  classical
  -- Both topologies are initial topologies for a family of functionals: the
  -- ultraweak topology of `A` for *all* np-functionals of `A`, the induced
  -- one for the family `ξ ∘ ρ`, `ξ` an np-functional of `B`.  Each `ξ ∘ ρ`
  -- is an np-functional of `A` (`compNP`), and by part 1 every np-functional
  -- of `A` is of that form; so the two families generate the same topology.
  have hρP : PreservesDirSups ⇑(nmiuP ρ) := ρ.preservesDirSups'
  have hind : TopologicalSpace.induced ⇑ρ (ultraweak B)
      = ⨅ ξ : NPFunctional B,
          TopologicalSpace.induced (fun a : A => (ξ (ρ a) : ℂ)) inferInstance := by
    rw [ultraweak, induced_iInf]
    exact iInf_congr fun ξ => induced_compose
  rw [hind, ultraweak]
  refine le_antisymm (le_iInf fun ξ => ?_) (le_iInf fun ω => ?_)
  · exact iInf_le_of_le (compNP (nmiuP ρ) hρP ξ) le_rfl
  · obtain ⟨ξ, hξ⟩ := functional_permanence_1 ρ hρ hR ω
    refine iInf_le_of_le ξ ?_
    have heq : (fun a : A => (ξ (ρ a) : ℂ)) = fun a : A => (ω a : ℂ) := funext hξ
    rw [heq]

/-- **89XI** (`functional-permanence`, vn.tex:7183, Corollary), part 3
(**ultrastrong permanence**): likewise for the ultrastrong topologies. -/
theorem functional_permanence_3 (ρ : NMIUMap A B)
    (hρ : Function.Injective ⇑ρ)
    (hR : IsVNSubalgebra B ρ.toStarAlgHom.range) :
    ultrastrong A = TopologicalSpace.induced ⇑ρ (ultrastrong B) := by
  classical
  -- The two topologies have the *same* generating balls: `‖ρ a - ρ b‖_ξ
  -- = ‖a - b‖_{ξ∘ρ}`, so a ball of `A` is the `ρ`-preimage of a ball of `B`
  -- (part 1 provides the `ξ` with `ξ∘ρ = ω`), and conversely the preimage of
  -- a ball around an arbitrary `c ∈ B` is ultrastrongly open in `A` because
  -- `a ↦ ‖ρ a - c‖_ξ` is `‖·‖_{ξ∘ρ}`-Lipschitz.
  have hρP : PreservesDirSups ⇑(nmiuP ρ) := ρ.preservesDirSups'
  have hnorm : ∀ (ξ : NPFunctional B) (a : A),
      omegaNorm A (compNP (nmiuP ρ) hρP ξ) a = omegaNorm B ξ (ρ a) :=
    fun ξ a => omegaNorm_comp_starAlgHom ρ.toStarAlgHom _ ξ (fun _ => rfl) a
  have hsub : ∀ a b : A, (ρ (a - b) : B) = ρ a - ρ b := fun a b =>
    map_sub ρ.toStarAlgHom a b
  have hopen : ∀ (ξ : NPFunctional B) (c : B) (ε : ℝ),
      @IsOpen A (ultrastrong A) {a : A | omegaNorm B ξ (ρ a - c) < ε} := by
    intro ξ c ε
    rw [@isOpen_iff_mem_nhds A (ultrastrong A)]
    intro a ha
    have ha' : omegaNorm B ξ (ρ a - c) < ε := ha
    set δ : ℝ := ε - omegaNorm B ξ (ρ a - c) with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    refine mem_of_superset
      (ultrastrong_ball_mem_nhds (compNP (nmiuP ρ) hρP ξ) a hδ0) ?_
    intro z hz
    have hz' : omegaNorm A (compNP (nmiuP ρ) hρP ξ) (z - a) < δ := hz
    rw [hnorm ξ (z - a), hsub] at hz'
    have htri : omegaNorm B ξ (ρ z - c) ≤ omegaNorm B ξ (ρ z - ρ a)
        + omegaNorm B ξ (ρ a - c) := by
      have h := omegaNorm_add_le ξ (ρ z - ρ a) (ρ a - c)
      simpa using h
    show omegaNorm B ξ (ρ z - c) < ε
    rw [hδ] at hz'
    linarith
  refine le_antisymm ?_ ?_
  · unfold ultrastrong
    rw [induced_generateFrom_eq]
    refine le_generateFrom ?_
    rintro _ ⟨U, ⟨ξ, c, ε, hε, rfl⟩, rfl⟩
    exact hopen ξ c ε
  · unfold ultrastrong
    rw [induced_generateFrom_eq]
    refine TopologicalSpace.generateFrom_anti ?_
    rintro U ⟨ω, b, ε, hε, rfl⟩
    obtain ⟨ξ, hξ⟩ := functional_permanence_1 ρ hρ hR ω
    refine ⟨{y : B | omegaNorm B ξ (y - ρ b) < ε}, ⟨ξ, ρ b, ε, hε, rfl⟩, ?_⟩
    ext a
    have hcomp : omegaNorm A ω (a - b) = omegaNorm B ξ (ρ a - ρ b) := by
      rw [← hsub]
      exact omegaNorm_comp_starAlgHom ρ.toStarAlgHom ω ξ (fun a => (hξ a).symm) (a - b)
    show omegaNorm B ξ (ρ a - ρ b) < ε ↔ omegaNorm A ω (a - b) < ε
    rw [hcomp]

/-- **89XII** (`functional-extension`, vn.tex:7203, Exercise): every
np-functional `ω` on `A` extends along any injective nmiu-map
`ρ : A → B`: there is an np-functional `ω'` on `B` with `ω' ∘ ρ = ω`.
(The thesis writes `ρ ∘ ω' = ω`, an obvious slip.) -/
theorem functional_extension (ρ : NMIUMap A B)
    (hρ : Function.Injective ⇑ρ) (ω : NPFunctional A) :
    ∃ ω' : NPFunctional B, ∀ a : A, ω' (ρ a) = ω a :=
  -- the thesis's hint: `injective-nmiu-iso-on-image` (**48VI**.1) supplies
  -- the missing hypothesis of 89XI.1.
  functional_permanence_1 ρ hρ (injective_nmiu_iso_on_image_1 ρ hρ) ω

/-! ## Parsec 900: centre separating collections

**90I** (vn.tex:7191): introduction — nothing to formalize. -/

/-- `x ↦ ω(x* k x)` is ultrastrongly continuous: it is `‖·‖_ω`-locally
Lipschitz by **72III**.1c. -/
theorem continuous_ultrastrong_conjFunctional (ω : NPFunctional A) (k : A) :
    @Continuous A ℂ (ultrastrong A) _ (fun x : A => ω (star x * k * x)) := by
  let _ : TopologicalSpace A := ultrastrong A
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set C : ℝ := (2 * omegaNorm A ω x₀ + 1) * ‖k‖ + 1 with hC
  have hC0 : 0 < C := by
    have := omegaNorm_nonneg ω x₀
    have := norm_nonneg k
    positivity
  set δ : ℝ := min 1 (ε / (2 * C)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  filter_upwards [ultrastrong_ball_mem_nhds ω x₀ hδ0] with x hx
  have hx' : omegaNorm A ω (x - x₀) < δ := hx
  have hxb : omegaNorm A ω x ≤ omegaNorm A ω x₀ + δ := by
    have h := omegaNorm_add_le ω (x - x₀) x₀
    rw [sub_add_cancel] at h
    linarith
  have hlip := bstaromega_lipschitz ω x x₀ k
  have hkey : ‖ω (star x * k * x) - ω (star x₀ * k * x₀)‖
      ≤ omegaNorm A ω (x - x₀) * (omegaNorm A ω x + omegaNorm A ω x₀) * ‖k‖ := hlip
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hmul : omegaNorm A ω (x - x₀) * (omegaNorm A ω x + omegaNorm A ω x₀) * ‖k‖
      ≤ δ * C := by
    have h1 : omegaNorm A ω x + omegaNorm A ω x₀ ≤ 2 * omegaNorm A ω x₀ + 1 := by
      linarith
    have h2 : (0 : ℝ) ≤ omegaNorm A ω x + omegaNorm A ω x₀ :=
      add_nonneg (omegaNorm_nonneg _ _) (omegaNorm_nonneg _ _)
    have h3 : omegaNorm A ω (x - x₀) * (omegaNorm A ω x + omegaNorm A ω x₀)
        ≤ δ * (2 * omegaNorm A ω x₀ + 1) :=
      mul_le_mul hx'.le h1 h2 hδ0.le
    have h4 : (0 : ℝ) ≤ ‖k‖ := norm_nonneg k
    nlinarith [omegaNorm_nonneg ω x₀, mul_nonneg hδ0.le h4]
  have hδC : δ * C < ε := by
    have hle : δ ≤ ε / (2 * C) := min_le_right _ _
    have : δ * C ≤ (ε / (2 * C)) * C := by nlinarith
    have heq : (ε / (2 * C)) * C = ε / 2 := by field_simp
    rw [heq] at this
    linarith
  rw [dist_eq_norm]
  calc ‖ω (star x * k * x) - ω (star x₀ * k * x₀)‖ ≤ _ := hkey
    _ ≤ δ * C := hmul
    _ < ε := hδC

/-- **90II** (`vn-center-separating-fundamental`, vn.tex:7234,
Proposition), part 1: for a centre separating collection `Ω` of
np-functionals (cstar.tex **21II**.4, `CentreSeparatingConj`) and an
ultrastrongly dense subset `S` of a von Neumann algebra `𝒜`, the collection
`Ω' = {ω(s*(·)s) : ω ∈ Ω, s ∈ S}` is **order separating** — that is,
`A/CStar/Positive`'s `OrderSeparating` (cstar.tex **21II**.1): an *arbitrary*
element `a` of `𝒜` is positive iff `ω(s* a s) ≥ 0` for all `ω ∈ Ω`, `s ∈ S`.

The proof is 900.30's: `Ξ = {ω(c*(·)c) : ω ∈ Ω, c ∈ 𝒜}` is order separating
by **30X** (`nonneg_of_conjNP_of_centreSeparating`, fed the C*-notion
**21II**.4 that 30X wants, which is our hypothesis verbatim), and `Ω' ⊆ Ξ`
is norm dense by **72III**.1c — rendered here as ultrastrong *continuity* of
`x ↦ ω(x* a x)`, which is that same estimate. -/
theorem vn_center_separating_fundamental_1' (Ω : Set (NPFunctional A))
    (hΩ : CentreSeparatingConj A Ω) (S : Set A)
    (hS : @Dense A (ultrastrong A) S) :
    OrderSeparating (fun p : Ω × S =>
      ((p.1 : NPFunctional A).toPositiveLinearMap.toLinearMap :
        A →ₗ[ℂ] ℂ).comp (conjMap A (p.2 : A))) := by
  have happ : ∀ (p : Ω × S) (x : A),
      ((((p.1 : NPFunctional A).toPositiveLinearMap.toLinearMap : A →ₗ[ℂ] ℂ).comp
        (conjMap A (p.2 : A))) x : ℂ) = (p.1 : NPFunctional A) (star (p.2 : A) * x * (p.2 : A)) := by
    intro p x
    show (p.1 : NPFunctional A) (star (p.2 : A) * (x * (p.2 : A))) = _
    rw [mul_assoc]
  intro a
  refine ⟨fun ha p => ?_, fun H => ?_⟩
  · rw [happ]
    exact npFunctional_nonneg _ (star_left_conjugate_nonneg ha _)
  · refine nonneg_of_conjNP_of_centreSeparating Ω hΩ fun ω hω c => ?_
    set T : Set A := {x : A | (0 : ℂ) ≤ ω (star x * a * x)} with hT
    have hTclosed : @IsClosed A (ultrastrong A) T := by
      have hcont := continuous_ultrastrong_conjFunctional ω a
      have hcl : IsClosed {z : ℂ | (0 : ℂ) ≤ z} := isClosed_le continuous_const continuous_id
      exact @IsClosed.preimage A ℂ (ultrastrong A) _ _ hcont _ hcl
    have hST : S ⊆ T := by
      intro s hs
      have h1 := H (⟨⟨ω, hω⟩, ⟨s, hs⟩⟩ : Ω × S)
      rw [happ] at h1
      exact h1
    have hsub : @closure A (ultrastrong A) S ⊆ T :=
      (@IsClosed.closure_subset_iff A (ultrastrong A) S T hTclosed).mpr hST
    have huniv : @closure A (ultrastrong A) S = Set.univ :=
      @Dense.closure_eq A (ultrastrong A) S hS
    exact hsub (by rw [huniv]; trivial)

/-- **90II**.1 in the two-element comparison form, which is how
`A/Proc/Tensor` (7256, `char_bounded`) uses it: `a ≤ b` follows from
`ω(s* a s) ≤ ω(s* b s)` for all `ω ∈ Ω`, `s ∈ S`.  A corollary of
`vn_center_separating_fundamental_1'` above, applied to `b - a`.

The two self-adjointness hypotheses are **not needed** — the primed
statement, which is the Proposition's, quantifies over arbitrary elements —
and are kept only because the call site above passes them positionally. -/
theorem vn_center_separating_fundamental_1 (Ω : Set (NPFunctional A))
    (hΩ : CentreSeparatingConj A Ω) (S : Set A)
    (hS : @Dense A (ultrastrong A) S) (a b : A) (_ha : IsSelfAdjoint a)
    (_hb : IsSelfAdjoint b)
    (h : ∀ ω ∈ Ω, ∀ s ∈ S, ω (star s * a * s) ≤ ω (star s * b * s)) :
    a ≤ b := by
  rw [← sub_nonneg]
  refine (vn_center_separating_fundamental_1' Ω hΩ S hS (b - a)).mpr fun p => ?_
  show (0 : ℂ) ≤ (p.1 : NPFunctional A) (star (p.2 : A) * ((b - a) * (p.2 : A)))
  rw [← mul_assoc,
    show star (p.2 : A) * (b - a) * (p.2 : A)
      = star (p.2 : A) * b * (p.2 : A) - star (p.2 : A) * a * (p.2 : A) by noncomm_ring,
    npFunctional_sub, sub_nonneg]
  exact h _ p.1.2 _ p.2.2

/-! ### The direct-sum GNS representation `ϱ_Ω` over a *set* of functionals

**90II**.2 runs through `ϱ_Ω : 𝒜 → 𝔅(ℋ_Ω)`, `ℋ_Ω = ⊕_{ω∈Ω} ℋ_ω`, for the
given collection `Ω`.  `A/VN/Basic.lean`'s `GNSSum` section now builds this
for an arbitrary family `F : ι → NPFunctional A` (`gnsHilbFam`, `gnsRepFam`),
so the definitions below are its instance at `F = Subtype.val`; the
`gnsHilb`/`gnsRep` of **48VIII** are its instance at `F = id`.

`gnsRepOn_injective` — `ϱ_Ω` is injective when `Ω` is centre separating — is
the step 900.40 opens with, and the thesis takes it from **30X**
(`proto-gelfand-naimark`, (2) ⇒ (1)).  The tree's 30X, `proto_gelfand_naimark_2`,
is stated *existentially* in the Hilbert space and so cannot speak about this
particular `ϱ_Ω`; **69IX** (`vn_center_separating`) can, since its fourth
entry is literally `Function.Injective ϱ_Ω`, and its equivalence with entry 1
*is* 30X's in the von Neumann setting.  That is the one line below.  (Until
2026-08-21 30X's own argument — `ϱ_Ω(a) = 0` gives
`ω(b* a* a b) = ‖ϱ_Ω(a) η_ω(b)‖² = 0` for all `ω ∈ Ω` and `b`, hence
`a* a = 0` — was re-run here by hand, because 69IX had no fourth entry.) -/

section GNSSumOn

variable (A) in
/-- `ℋ_Ω = ⊕_{ω∈Ω} ℋ_ω`: `A/VN/Basic.lean`'s `gnsHilbFam` at the family
`Subtype.val : Ω → NPFunctional A`. -/
abbrev gnsHilbOn (Ω : Set (NPFunctional A)) : Type u :=
  gnsHilbFam (Subtype.val : Ω → NPFunctional A)

variable {Ω : Set (NPFunctional A)}

private theorem rpow_two_toReal' (x : ℝ) : x ^ (2 : ℝ≥0∞).toReal = x ^ 2 := by
  rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

variable (Ω) in
/-- The direct-sum GNS representation `ϱ_Ω : A → B(⊕_{ω∈Ω} ℋ_ω)` over a
*set* `Ω` of np-functionals (**48V** at `Subtype.val`). -/
noncomputable def gnsRepOn : A →⋆ₐ[ℂ] (gnsHilbOn A Ω →L[ℂ] gnsHilbOn A Ω) :=
  gnsRepFam (Subtype.val : Ω → NPFunctional A)

@[simp] theorem gnsRepOn_apply_coe (a : A) (y : gnsHilbOn A Ω) (ω : Ω) :
    ((gnsRepOn Ω a y : gnsHilbOn A Ω) : ∀ ω : Ω, _) ω
      = (ω : NPFunctional A).toPositiveLinearMap.gnsStarAlgHom a
        ((y : ∀ ω : Ω, _) ω) := rfl

open scoped Classical in
/-- The "elementary" vectors `η_ω(b)` of `⊕_{ω∈Ω} ℋ_ω`. -/
def gnsElemVecsOn (Ω : Set (NPFunctional A)) : Set (gnsHilbOn A Ω) :=
  gnsElemVecsFam (Subtype.val : Ω → NPFunctional A)

theorem gnsRepOn_normal : PreservesDirSups ⇑(gnsRepOn (A := A) Ω) :=
  gnsRepFam_normal _


/-- `ϱ_Ω` is injective exactly when `Ω` is centre separating (cstar.tex
**21II**.4).  This is **69IX** (`vn_center_separating`), entry 1 ⟹ entry 4;
see the section note above for why 30X itself cannot be cited here. -/
theorem gnsRepOn_injective (hΩ : CentreSeparatingConj A Ω) :
    Function.Injective (gnsRepOn (A := A) Ω) :=
  ((vn_center_separating Ω).out 0 3).mp hΩ

/-- `⟪u,Tu⟫ - ⟪w,Tw⟫ = ⟪u-w,Tu⟫ + ⟪w,T(u-w)⟫`, whence the bound. -/
private theorem inner_conj_diff_le {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (T : K →L[ℂ] K) (u w : K) {M : ℝ} (hM : 0 ≤ M)
    (hTM : ∀ z, ‖T z‖ ≤ M * ‖z‖) :
    ‖(⟪u, T u⟫ : ℂ) - ⟪w, T w⟫‖ ≤ M * (‖u‖ + ‖w‖) * ‖u - w‖ := by
  have hsplit : (⟪u, T u⟫ : ℂ) - ⟪w, T w⟫ = ⟪u - w, T u⟫ + ⟪w, T (u - w)⟫ := by
    simp only [inner_sub_left, map_sub, inner_sub_right]
    ring
  rw [hsplit]
  have b1 : ‖(⟪u - w, T u⟫ : ℂ)‖ ≤ ‖u - w‖ * (M * ‖u‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hTM u) (norm_nonneg _))
  have b2 : ‖(⟪w, T (u - w)⟫ : ℂ)‖ ≤ ‖w‖ * (M * ‖u - w‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hTM _) (norm_nonneg _))
  calc ‖(⟪u - w, T u⟫ : ℂ) + ⟪w, T (u - w)⟫‖
      ≤ ‖(⟪u - w, T u⟫ : ℂ)‖ + ‖(⟪w, T (u - w)⟫ : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖u - w‖ * (M * ‖u‖) + ‖w‖ * (M * ‖u - w‖) := add_le_add b1 b2
    _ = M * (‖u‖ + ‖w‖) * ‖u - w‖ := by ring

/-- Every vector functional `⟪v, ϱ_ω(·)v⟫` of a GNS space is, to any
prescribed operator-norm accuracy, of the form `ω(s*(·)s)` with `s` in a
prescribed ultrastrongly dense set: `v` is a norm limit of the `η_ω(b)`
(**48III**), and `b ↦ b*ω` is `‖·‖_ω`-to-norm Lipschitz (**72III**.1c). -/
private theorem gnsVec_approx_functional (ω : NPFunctional A) {S : Set A}
    (hS : @Dense A (ultrastrong A) S) (v : ω.toPositiveLinearMap.GNS) {η : ℝ}
    (hη : 0 < η) :
    ∃ s ∈ S, ∀ a : A,
      ‖(⟪v, ω.toPositiveLinearMap.gnsStarAlgHom a v⟫ : ℂ)
        - ω (star s * a * s)‖ ≤ η * ‖a‖ := by
  -- Step 1: replace `v` by an `η_ω(b)`.
  set δ : ℝ := min 1 (η / (2 * (2 * ‖v‖ + 1))) with hδdef
  have hpos : (0:ℝ) < 2 * (2 * ‖v‖ + 1) := by positivity
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  obtain ⟨b, hb⟩ := (gnsVec_denseRange ω).exists_dist_lt v hδ0
  have hbv : ‖v - gnsVec ω b‖ < δ := by rwa [dist_eq_norm] at hb
  have hbnorm : ‖gnsVec ω b‖ ≤ ‖v‖ + δ := by
    have h1 : ‖gnsVec ω b‖ - ‖v‖ ≤ ‖gnsVec ω b - v‖ := norm_sub_norm_le _ _
    have h2 : ‖gnsVec ω b - v‖ = ‖v - gnsVec ω b‖ := norm_sub_rev _ _
    have h3 := hbv.le
    linarith
  have hstep1 : ∀ a : A,
      ‖(⟪v, ω.toPositiveLinearMap.gnsStarAlgHom a v⟫ : ℂ) - ω (star b * a * b)‖
        ≤ η / 2 * ‖a‖ := by
    intro a
    have hT : ∀ z, ‖ω.toPositiveLinearMap.gnsStarAlgHom a z‖ ≤ ‖a‖ * ‖z‖ :=
      starAlgHom_apply_norm_le _ a
    have hval : (⟪gnsVec ω b,
        ω.toPositiveLinearMap.gnsStarAlgHom a (gnsVec ω b)⟫ : ℂ)
          = ω (star b * a * b) := by
      rw [gnsRep_gnsVec, gnsVec_inner, mul_assoc]
    have hd := inner_conj_diff_le (ω.toPositiveLinearMap.gnsStarAlgHom a) v
      (gnsVec ω b) (norm_nonneg a) hT
    rw [hval] at hd
    refine hd.trans ?_
    have h1 : ‖v‖ + ‖gnsVec ω b‖ ≤ 2 * ‖v‖ + 1 := by linarith
    have h2 : ‖a‖ * (‖v‖ + ‖gnsVec ω b‖) * ‖v - gnsVec ω b‖
        ≤ ‖a‖ * (2 * ‖v‖ + 1) * δ := by
      have hn : (0:ℝ) ≤ ‖a‖ := norm_nonneg a
      have hd1 : (0:ℝ) ≤ ‖v - gnsVec ω b‖ := norm_nonneg _
      have hmul := mul_le_mul_of_nonneg_left h1 hn
      have hA : (0:ℝ) ≤ ‖a‖ * (2 * ‖v‖ + 1) := by positivity
      calc ‖a‖ * (‖v‖ + ‖gnsVec ω b‖) * ‖v - gnsVec ω b‖
          ≤ ‖a‖ * (2 * ‖v‖ + 1) * ‖v - gnsVec ω b‖ :=
            mul_le_mul_of_nonneg_right hmul hd1
        _ ≤ ‖a‖ * (2 * ‖v‖ + 1) * δ := mul_le_mul_of_nonneg_left hbv.le hA
    refine h2.trans ?_
    have hδle : δ ≤ η / (2 * (2 * ‖v‖ + 1)) := min_le_right _ _
    have hkey : (2 * ‖v‖ + 1) * δ ≤ η / 2 := by
      have h3 : (2 * ‖v‖ + 1) * δ ≤ (2 * ‖v‖ + 1) * (η / (2 * (2 * ‖v‖ + 1))) := by
        have : (0:ℝ) ≤ 2 * ‖v‖ + 1 := by positivity
        exact mul_le_mul_of_nonneg_left hδle this
      have h4 : (2 * ‖v‖ + 1) * (η / (2 * (2 * ‖v‖ + 1))) = η / 2 := by
        field_simp
      linarith
    have hn : (0:ℝ) ≤ ‖a‖ := norm_nonneg a
    nlinarith
  -- Step 2: replace `b` by an `s ∈ S`, using **72III**.1c.
  set γ : ℝ := min 1 (η / (2 * (2 * omegaNorm A ω b + 1))) with hγdef
  have hγpos : (0:ℝ) < 2 * (2 * omegaNorm A ω b + 1) := by
    have := omegaNorm_nonneg ω b; positivity
  have hγ0 : 0 < γ := lt_min one_pos (by positivity)
  have hγ1 : γ ≤ 1 := min_le_left _ _
  have hmemcl : b ∈ @closure A (ultrastrong A) S := hS b
  obtain ⟨s, hsball, hsS⟩ :=
    (@mem_closure_iff_nhds A (ultrastrong A) _ _).mp hmemcl _
      (ultrastrong_ball_mem_nhds ω b hγ0)
  have hsb : omegaNorm A ω (s - b) < γ := hsball
  refine ⟨s, hsS, fun a => ?_⟩
  have hstep2 : ‖(ω (star b * a * b) : ℂ) - ω (star s * a * s)‖ ≤ η / 2 * ‖a‖ := by
    have hlip := bstaromega_lipschitz ω b s a
    have he1 : bStarOmega A b ω a = ω (star b * a * b) := rfl
    have he2 : bStarOmega A s ω a = ω (star s * a * s) := rfl
    rw [he1, he2] at hlip
    refine hlip.trans ?_
    have hbs : omegaNorm A ω (b - s) < γ := by
      rw [show b - s = -(s - b) by rw [neg_sub], omegaNorm_neg]; exact hsb
    have hsn : omegaNorm A ω s ≤ omegaNorm A ω b + γ := by
      have hadd : omegaNorm A ω (b + (s - b)) ≤ omegaNorm A ω b + omegaNorm A ω (s - b) :=
        omegaNorm_add_le ω b (s - b)
      rw [add_sub_cancel] at hadd
      linarith
    have hn : (0:ℝ) ≤ ‖a‖ := norm_nonneg a
    have hnn := omegaNorm_nonneg ω b
    have hkey : omegaNorm A ω (b - s) * (omegaNorm A ω b + omegaNorm A ω s)
        ≤ γ * (2 * omegaNorm A ω b + 1) := by
      have h1 : omegaNorm A ω b + omegaNorm A ω s ≤ 2 * omegaNorm A ω b + 1 := by
        linarith
      have h2 : (0:ℝ) ≤ omegaNorm A ω b + omegaNorm A ω s := by
        have := omegaNorm_nonneg ω s; linarith
      nlinarith [omegaNorm_nonneg ω (b - s)]
    have hγle : γ ≤ η / (2 * (2 * omegaNorm A ω b + 1)) := min_le_right _ _
    have h4 : γ * (2 * omegaNorm A ω b + 1) ≤ η / 2 := by
      have h5 : γ * (2 * omegaNorm A ω b + 1)
          ≤ (η / (2 * (2 * omegaNorm A ω b + 1))) * (2 * omegaNorm A ω b + 1) :=
        mul_le_mul_of_nonneg_right hγle (by linarith)
      have h6 : (η / (2 * (2 * omegaNorm A ω b + 1))) * (2 * omegaNorm A ω b + 1)
          = η / 2 := by field_simp
      linarith
    nlinarith
  calc ‖(⟪v, ω.toPositiveLinearMap.gnsStarAlgHom a v⟫ : ℂ) - ω (star s * a * s)‖
      ≤ ‖(⟪v, ω.toPositiveLinearMap.gnsStarAlgHom a v⟫ : ℂ) - ω (star b * a * b)‖
        + ‖(ω (star b * a * b) : ℂ) - ω (star s * a * s)‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub
          (⟪v, ω.toPositiveLinearMap.gnsStarAlgHom a v⟫ : ℂ) (ω (star b * a * b))
          (ω (star s * a * s))
    _ ≤ η / 2 * ‖a‖ + η / 2 * ‖a‖ := add_le_add (hstep1 a) hstep2
    _ = η * ‖a‖ := by ring

/-- **90II** (`vn-center-separating-fundamental`, vn.tex:7234,
Proposition), part 2: the finite sums `Ω''` of members of `Ω'` are
operator-norm dense in the positive part of the predual: every
np-functional `f` is an operator-norm limit of sums
`∑ₖ ωₖ(sₖ*(·)sₖ)` with `ωₖ ∈ Ω`, `sₖ ∈ S`. -/
theorem vn_center_separating_fundamental_2 (Ω : Set (NPFunctional A))
    (hΩ : CentreSeparatingConj A Ω) (S : Set A)
    (hS : @Dense A (ultrastrong A) S) (f : NPFunctional A) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ (n : ℕ) (ω : Fin n → NPFunctional A) (s : Fin n → A),
      (∀ k, ω k ∈ Ω ∧ s k ∈ S) ∧
      ∀ a : A, ‖f a - ∑ k, (ω k) (star (s k) * a * s k)‖ ≤ ε * ‖a‖ := by
  classical
  -- `ϱ_Ω` is an injective normal representation with von Neumann range.
  set ρ : NMIUMap A (gnsHilbOn A Ω →L[ℂ] gnsHilbOn A Ω) :=
    ⟨gnsRepOn Ω, gnsRepOn_normal⟩ with hρdef
  have hinj : Function.Injective ⇑ρ := gnsRepOn_injective hΩ
  have hR : IsVNSubalgebra _ ρ.toStarAlgHom.range :=
    isVNSubalgebra_range ρ.toStarAlgHom hinj gnsRepOn_normal
  -- **89IX**: `f = ∑ₙ ⟪xₙ, ϱ_Ω(·)xₙ⟫`.
  obtain ⟨x, hx2, hxs⟩ := normal_functional ρ hinj hR f
  -- the double family of components, and its square-summability
  set w : ℕ × Ω → ℝ := fun p => ‖(x p.1 : ∀ ω : Ω, _) p.2‖ ^ 2 with hwdef
  have hfiber : ∀ n : ℕ, HasSum (fun ω : Ω => w (n, ω)) (‖x n‖ ^ 2) := by
    intro n
    simpa only [hwdef, rpow_two_toReal'] using lp.hasSum_norm (by norm_num) (x n)
  have hw0 : ∀ p, 0 ≤ w p := fun p => by positivity
  have hw : Summable w := by
    refine (summable_prod_of_nonneg hw0).mpr ⟨fun n => (hfiber n).summable, ?_⟩
    refine hx2.congr fun n => ((hfiber n).tsum_eq).symm
  -- a finite set carrying all but `ε/2` of the mass
  obtain ⟨F, hFball⟩ :=
    (hw.hasSum.eventually (Metric.ball_mem_nhds _ (half_pos hε))).exists
  have htail : ∑' p : ↥((F : Set (ℕ × ↥Ω))ᶜ), w p ≤ ε / 2 := by
    have hsplit := hw.sum_add_tsum_compl (s := F)
    have hd : |∑ p ∈ F, w p - ∑' p, w p| < ε / 2 := by
      simpa [Real.dist_eq] using hFball
    have h0 : 0 ≤ ∑' p : ↥((F : Set (ℕ × ↥Ω))ᶜ), w p :=
      tsum_nonneg fun p => hw0 p
    have hd2 := (abs_lt.mp hd).1
    linarith
  -- one `s ∈ S` per index, uniformly in `a` (approximation lemma)
  set η : ℝ := ε / (2 * (F.card + 1)) with hηdef
  have hη : 0 < η := by
    have : (0:ℝ) < 2 * (F.card + 1) := by positivity
    exact div_pos hε this
  have hchoice : ∀ p : ℕ × Ω, ∃ s ∈ S, ∀ a : A,
      ‖(⟪(x p.1 : ∀ ω : Ω, _) p.2,
          (p.2 : NPFunctional A).toPositiveLinearMap.gnsStarAlgHom a
            ((x p.1 : ∀ ω : Ω, _) p.2)⟫ : ℂ)
        - (p.2 : NPFunctional A) (star s * a * s)‖ ≤ η * ‖a‖ :=
    fun p => gnsVec_approx_functional (p.2 : NPFunctional A) hS _ hη
  choose sel hselS hsel using hchoice
  -- package the finite index set as `Fin F.card`
  refine ⟨F.card, fun k => ((F.equivFin.symm k : ℕ × Ω).2 : NPFunctional A),
    fun k => sel (F.equivFin.symm k : ℕ × Ω), fun k => ⟨(F.equivFin.symm k : ℕ × Ω).2.2,
      hselS _⟩, fun a => ?_⟩
  -- the `a`-dependent scalar family
  set g : ℕ × Ω → ℂ := fun p =>
    (⟪(x p.1 : ∀ ω : Ω, _) p.2,
      (p.2 : NPFunctional A).toPositiveLinearMap.gnsStarAlgHom a
        ((x p.1 : ∀ ω : Ω, _) p.2)⟫ : ℂ) with hgdef
  have hgb : ∀ p, ‖g p‖ ≤ ‖a‖ * w p := by
    intro p
    show ‖g p‖ ≤ ‖a‖ * ‖(x p.1 : ∀ ω : Ω, _) p.2‖ ^ 2
    have h1 : ‖g p‖ ≤ ‖(x p.1 : ∀ ω : Ω, _) p.2‖ *
        ‖(p.2 : NPFunctional A).toPositiveLinearMap.gnsStarAlgHom a
          ((x p.1 : ∀ ω : Ω, _) p.2)‖ := norm_inner_le_norm _ _
    have h2 := starAlgHom_apply_norm_le
      ((p.2 : NPFunctional A).toPositiveLinearMap.gnsStarAlgHom) a
      ((x p.1 : ∀ ω : Ω, _) p.2)
    calc ‖g p‖ ≤ ‖(x p.1 : ∀ ω : Ω, _) p.2‖ * _ := h1
      _ ≤ ‖(x p.1 : ∀ ω : Ω, _) p.2‖ * (‖a‖ * ‖(x p.1 : ∀ ω : Ω, _) p.2‖) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ‖a‖ * ‖(x p.1 : ∀ ω : Ω, _) p.2‖ ^ 2 := by ring
  have hgsummable : Summable g :=
    Summable.of_norm_bounded (hw.mul_left ‖a‖) hgb
  have hgfiber : ∀ n : ℕ, HasSum (fun ω : Ω => g (n, ω)) (⟪x n, ρ a (x n)⟫) := by
    intro n
    have h := lp.hasSum_inner (𝕜 := ℂ)
      (G := fun ω : Ω => (ω : NPFunctional A).toPositiveLinearMap.GNS) (x n) (ρ a (x n))
    refine h.congr_fun fun ω => ?_
    rfl
  have hgtot : HasSum g (f a) := by
    have h1 := hgsummable.hasSum
    have h2 := h1.prod_fiberwise hgfiber
    have h3 := hxs a
    rw [← h2.unique h3]
    exact h1
  -- the tail estimate
  have hcompl : ∑' p : ↥((F : Set (ℕ × ↥Ω))ᶜ), g p = f a - ∑ p ∈ F, g p := by
    have heq := hgsummable.sum_add_tsum_compl (s := F)
    rw [hgtot.tsum_eq] at heq
    exact eq_sub_of_add_eq' heq
  have htailbound : ‖f a - ∑ p ∈ F, g p‖ ≤ ε / 2 * ‖a‖ := by
    have h1 : ‖f a - ∑ p ∈ F, g p‖ ≤ ∑' p : ↥((F : Set (ℕ × ↥Ω))ᶜ), ‖g p‖ := by
      rw [← hcompl]
      exact norm_tsum_le_tsum_norm ((hgsummable.subtype _).norm)
    have h2 : ∑' p : ↥((F : Set (ℕ × ↥Ω))ᶜ), ‖g p‖
        ≤ ∑' p : ↥((F : Set (ℕ × ↥Ω))ᶜ), ‖a‖ * w p := by
      refine Summable.tsum_le_tsum (fun p => hgb p) ((hgsummable.subtype _).norm)
        ((hw.mul_left ‖a‖).subtype _)
    have h3 : ∑' p : ↥((F : Set (ℕ × ↥Ω))ᶜ), ‖a‖ * w p
        = ‖a‖ * ∑' p : ↥((F : Set (ℕ × ↥Ω))ᶜ), w p := tsum_mul_left
    have h4 : ‖a‖ * ∑' p : ↥((F : Set (ℕ × ↥Ω))ᶜ), w p ≤ ‖a‖ * (ε / 2) :=
      mul_le_mul_of_nonneg_left htail (norm_nonneg a)
    calc ‖f a - ∑ p ∈ F, g p‖ ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := h3
      _ ≤ ‖a‖ * (ε / 2) := h4
      _ = ε / 2 * ‖a‖ := by ring
  -- the per-index estimate
  have hsum_eq : ∑ k : Fin F.card,
      ((F.equivFin.symm k : ℕ × Ω).2 : NPFunctional A)
        (star (sel (F.equivFin.symm k : ℕ × Ω)) * a * sel (F.equivFin.symm k : ℕ × Ω))
      = ∑ p ∈ F, ((p.2 : NPFunctional A) (star (sel p) * a * sel p) : ℂ) := by
    rw [← Finset.sum_coe_sort F
      (fun p : ℕ × Ω => ((p.2 : NPFunctional A) (star (sel p) * a * sel p) : ℂ))]
    exact Fintype.sum_equiv F.equivFin.symm _ _ fun k => rfl
  rw [hsum_eq]
  have hper : ‖(∑ p ∈ F, g p) - ∑ p ∈ F, ((p.2 : NPFunctional A)
      (star (sel p) * a * sel p) : ℂ)‖ ≤ ε / 2 * ‖a‖ := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hbd : ∀ p ∈ F, ‖g p - ((p.2 : NPFunctional A)
        (star (sel p) * a * sel p) : ℂ)‖ ≤ η * ‖a‖ := fun p _ => hsel p a
    refine (Finset.sum_le_sum hbd).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hηeq : 2 * (η * (F.card : ℝ)) + 2 * η = ε := by
      rw [hηdef]; field_simp
    have hηc : (F.card : ℝ) * η ≤ ε / 2 := by
      have := hη.le
      nlinarith
    have hn : (0:ℝ) ≤ ‖a‖ := norm_nonneg a
    have hcard : (F.card : ℝ) * (η * ‖a‖) ≤ ε / 2 * ‖a‖ := by nlinarith
    linarith [hcard]
  calc ‖f a - ∑ p ∈ F, ((p.2 : NPFunctional A) (star (sel p) * a * sel p) : ℂ)‖
      ≤ ‖f a - ∑ p ∈ F, g p‖
        + ‖(∑ p ∈ F, g p) - ∑ p ∈ F, ((p.2 : NPFunctional A)
            (star (sel p) * a * sel p) : ℂ)‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub (f a) (∑ p ∈ F, g p)
          (∑ p ∈ F, ((p.2 : NPFunctional A) (star (sel p) * a * sel p) : ℂ))
    _ ≤ ε / 2 * ‖a‖ + ε / 2 * ‖a‖ := add_le_add htailbound hper
    _ = ε * ‖a‖ := by ring

end GNSSumOn

/-! **91I** (vn.tex:7311): closing remarks of the chapter — nothing to
formalize. -/

end Permanence

/-! ## The scalars in universe `u`

Several universal properties in thesis A and thesis B (proc.tex 98II,
dils.tex 169II/169VIII) quantify their test algebra over `Type u`, the
universe this development's von Neumann algebras live in, while `ℂ` sits in
`Type 0`.  The cheapest test maps available are the ones *out of the
scalars*: the ncp-maps `ℂ → A` are exactly `z ↦ z·a` for `0 ≤ a ∈ A`, so the
uniqueness half of such a universal property becomes an injectivity
statement about elements of `A`.  The scalars therefore have to be lifted.
Mathlib carries the ring, norm, algebra and completeness of `ULift ℂ` but
neither its ∗-structure nor its order; those are supplied here.

This block is a copy of the one in `Theses/B/Dils/Pure.lean` (session 45),
lifted here so that `A/Proc` — a sibling of `B/Dils` over `A/VN`, hence
unable to import it — can use it too; the copy in `B/Dils` should be dropped
in favour of this one. -/

section Scalars

/-- `ℂ`, lifted into the universe `u` of this chapter's algebras. -/
abbrev CU : Type u := ULift.{u} ℂ

namespace CU

theorem down_injective : Function.Injective (ULift.down : CU.{u} → ℂ) :=
  fun a b h => by cases a; cases b; exact congrArg ULift.up h

instance : StarRing CU.{u} where
  star x := ⟨star x.down⟩
  star_involutive x := down_injective (star_star x.down)
  star_mul x y := down_injective (star_mul x.down y.down)
  star_add x y := down_injective (star_add x.down y.down)

@[simp] theorem down_star (x : CU.{u}) : (star x).down = star x.down := rfl
@[simp] theorem down_one : (1 : CU.{u}).down = 1 := rfl
@[simp] theorem down_mul (x y : CU.{u}) : (x * y).down = x.down * y.down := rfl
@[simp] theorem down_smul (r : ℂ) (x : CU.{u}) : (r • x).down = r * x.down := rfl

instance : StarModule ℂ CU.{u} where
  star_smul r x := down_injective (star_smul r x.down)

instance : CStarRing CU.{u} where
  norm_mul_self_le x := CStarRing.norm_mul_self_le (x := x.down)

noncomputable instance : CStarAlgebra CU.{u} where

instance : PartialOrder CU.{u} := PartialOrder.lift ULift.down down_injective

theorem le_def {x y : CU.{u}} : x ≤ y ↔ x.down ≤ y.down := Iff.rfl

instance : StarOrderedRing CU.{u} := by
  refine StarOrderedRing.of_nonneg_iff' (fun {x y} hxy z => ?_) (fun x => ?_)
  · exact le_def.mpr (add_le_add (le_refl z.down) (le_def.mp hxy))
  · constructor
    · intro hx
      obtain ⟨s, hs⟩ :=
        CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (le_def.mp hx)
      exact ⟨⟨s⟩, down_injective hs⟩
    · rintro ⟨s, rfl⟩
      exact le_def.mpr (star_mul_self_nonneg s.down)

theorem isSelfAdjoint_down {x : CU.{u}} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint x.down :=
  congrArg ULift.down hx

end CU

/-- The linear map `ℂᵤ → A`, `z ↦ z·a`. -/
private noncomputable def smulLin (a : A) : CU.{u} →ₗ[ℂ] A where
  toFun z := z.down • a
  map_add' x y := by simp [add_smul]
  map_smul' r x := by simp [mul_smul]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem smulLin_apply (a : A) (z : CU.{u}) : smulLin a z = z.down • a := rfl

/-- Complete positivity of `z ↦ z·a`: `∑ᵢⱼ bᵢ* (cᵢ*cⱼ · a) bⱼ = v* a v` for
`v = ∑ᵢ cᵢbᵢ`. -/
private theorem smulLin_cp {a : A} (ha : 0 ≤ a) :
    IsCompletelyPositiveMap (smulLin (A := A) a) := by
  intro n c b
  have h : ∀ i j : Fin n,
      star (b i) * smulLin a (star (c i) * c j) * b j
        = star ((c i).down • b i) * a * ((c j).down • b j) := by
    intro i j
    simp only [smulLin_apply, CU.down_mul, CU.down_star, star_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]
  simp_rw [h]
  have hsum : ∑ i, ∑ j, star ((c i).down • b i) * a * ((c j).down • b j)
      = star (∑ i, (c i).down • b i) * a * (∑ j, (c j).down • b j) := by
    rw [star_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [hsum]
  exact star_left_conjugate_nonneg ha _

/-- Transfer of a supremum in `sa(ℂᵤ)` to `ℝ`. -/
private theorem isLUB_re {D : Set (selfAdjoint CU.{u})} {s : selfAdjoint CU.{u}}
    (hlub : IsLUB D s) :
    IsLUB ((fun d : selfAdjoint CU.{u} => ((d : CU.{u}).down).re) '' D)
      (((s : CU.{u}).down).re) := by
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact (Complex.le_def.mp (CU.le_def.mp (Subtype.coe_le_coe.mpr (hlub.1 hd)))).1
  · intro r hr
    have hsa : IsSelfAdjoint (⟨((r : ℝ) : ℂ)⟩ : CU.{u}) :=
      CU.down_injective
        ((Complex.im_eq_zero_iff_isSelfAdjoint _).mp (Complex.ofReal_im _))
    have hub : (⟨⟨((r : ℝ) : ℂ)⟩, hsa⟩ : selfAdjoint CU.{u}) ∈ upperBounds D := by
      intro d hd
      refine Subtype.coe_le_coe.mp
        (CU.le_def.mpr (Complex.le_def.mpr ⟨hr ⟨d, hd, rfl⟩, ?_⟩))
      rw [Complex.ofReal_im, Complex.im_eq_zero_iff_isSelfAdjoint]
      exact CU.isSelfAdjoint_down d.2
    exact (Complex.le_def.mp (CU.le_def.mp (Subtype.coe_le_coe.mpr (hlub.2 hub)))).1

/-- Normality of `z ↦ z·a`: the positive cone of `A` is closed, and a
supremum in `ℝ` lies in the closure of its set. -/
private theorem smulLin_normal {a : A} (ha : 0 ≤ a) :
    PreservesDirSups ⇑(smulLin (A := A) a) := by
  intro D s hne _ hlub
  have hre := isLUB_re hlub
  have hmono : ∀ t r : ℝ, t ≤ r → ((t : ℂ)) • a ≤ ((r : ℂ)) • a := by
    intro t r htr
    have h : (0 : A) ≤ ((r - t : ℝ) : ℂ) • a := cstar_positive_1 a ha _ (by linarith)
    have he : ((r - t : ℝ) : ℂ) • a = (r : ℂ) • a - (t : ℂ) • a := by
      push_cast; rw [sub_smul]
    rw [he] at h
    exact sub_nonneg.mp h
  have hcoe : ∀ d : selfAdjoint CU.{u},
      (((((d : CU.{u}).down).re : ℝ)) : ℂ) = (d : CU.{u}).down := by
    intro d
    have him : ((d : CU.{u}).down).im = 0 :=
      (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr (CU.isSelfAdjoint_down d.2)
    apply Complex.ext <;> simp [him]
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    show (d : CU.{u}).down • a ≤ (s : CU.{u}).down • a
    rw [← hcoe d, ← hcoe s]
    exact hmono _ _ (hre.1 ⟨d, hd, rfl⟩)
  · intro u hu
    show (s : CU.{u}).down • a ≤ u
    have hclosed : IsClosed {t : ℝ | ((t : ℂ)) • a ≤ u} :=
      isClosed_Iic.preimage (by fun_prop)
    have hsub : (fun d : selfAdjoint CU.{u} => ((d : CU.{u}).down).re) '' D
        ⊆ {t : ℝ | ((t : ℂ)) • a ≤ u} := by
      rintro _ ⟨d, hd, rfl⟩
      show ((((d : CU.{u}).down).re : ℝ) : ℂ) • a ≤ u
      rw [hcoe d]
      exact hu ⟨d, hd, rfl⟩
    have hmem := hre.mem_closure (hne.image _)
    have hfin := hclosed.closure_subset_iff.mpr hsub hmem
    rw [← hcoe s]
    exact hfin

/-- Every positive element `a` of a C*-algebra `A` is the value at `1` of an
ncp-map `ℂᵤ → A`, namely `z ↦ z·a`.  (Conversely every ncp-map `ℂᵤ → A` is
of this form, by linearity; that direction is not needed here.) -/
noncomputable def ncpOfNonneg {a : A} (ha : 0 ≤ a) : NCPMap CU.{u} A where
  toCompletelyPositiveMap :=
    { toLinearMap := smulLin a
      map_cstarMatrix_nonneg' :=
        (cp_iff (smulLin (A := A) a)).out 0 1 |>.mp (smulLin_cp ha) }
  preservesDirSups' := smulLin_normal ha

@[simp] theorem ncpOfNonneg_apply {a : A} (ha : 0 ≤ a) (z : CU.{u}) :
    ncpOfNonneg ha z = z.down • a := rfl

end Scalars

end Theses.A.VN
