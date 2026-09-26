import Papers.EJA.Appendix2
import Papers.REC.JBCoord

/-!
# EJA 54 unconditionally: a factor EJA is finite-dimensional or a spin factor

`HOSClassification` (Appendix2.lean) is the only input of EJA 54 (`appendixjnw`): **an EJA
(EJA 1: complete real inner product space, possibly infinite-dimensional, with an associative
Jordan product) that is a factor is finite-dimensional or Jordan-isomorphic to the spin factor
of an infinite-dimensional Hilbert space.**  That is all EJA 54 needs of the classification;
the Jordan–von Neumann–Wigner list of the finite-dimensional factors is NOT needed and is not
proved here.  This file proves `HOSClassification` outright (`hosClassification`) and hence
EJA 54 with no hypothesis (`appendixjnw_uncond`).

Plan (estimate → actual lines; all done, no `sorry`, axioms: propext, choice, Quot.sound):
A. Hurwitz, infinite-dimensional form [~300 → 400]: a unital bilinear product on a closed subspace
   `K` of a real inner product space with `‖xy‖ = ‖x‖‖y‖` forces `dim K < ∞`
   (`hurwitz_finiteDimensional`).  The linearised composition identities give conjugation,
   `x̄(xy) = N(x) y` and the doubling formulas `a(bj) = (ba)j`, `(aj)b = (ab̄)j`,
   `(aj)(bj) = −N(j) b̄a` for `j ⊥ B`, `B` a subalgebra; then `B ⊕ Bj` is a subalgebra,
   `B` is associative when such a `j ≠ 0` exists, and commutative when `B ⊕ Bj` is associative.
   Four orthogonal doublings of `ℝe` inside an infinite-dimensional `K` contradict
   `ij = −ji ≠ 0`.
B. Primitive idempotents [~80 → 100]: for `q` atomic, `V₁(q) = ℝq` (spectral theorem in the corner).
C. Off-diagonal Peirce spaces [~200 → 240] of a frame of atomic idempotents (EJA 52): `x ∈ V_ab`
   has `x² = λ(e_a + e_b)` (power associativity); Peirce specialisation (`peirce_spec`) gives
   `4 y(yx) = λ x`; so `‖2xy‖ = ‖x‖‖y‖/‖e_b+e_c‖` on `V_ab × V_bc → V_ac`, and
   `u ⋆ v = 8 (y₀u)(x₀v)` is a unital composition product on `V_ac`: `V_ab, V_bc ≠ 0` ⟹
   `dim V_ac < ∞` and `V_ac ≠ 0`.
D. Factor argument [~150 → 190]: `E` infinite-dimensional ⟹ (joint Peirce decomposition, JBPeirce)
   some `V_ij` is infinite-dimensional ⟹ `V_ik = V_jk = 0` for every other `k` (by C) ⟹
   `V½(e_i + e_j) = 0` ⟹ `e_i + e_j` central ⟹ `= 1`.
E. Rank two [~150 → 210]: `1 = e + f` atomic, then on `K = 1^⊥`, `k² = (‖k‖²/‖1‖²) 1`, so
   `a ↦ (‖1‖⁻¹(a − t 1), t)` is an isomorphism onto `SpinFactor K`.
-/

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace Papers.EJA.Classification

open scoped InnerProductSpace

universe u

/-! ## A. Hurwitz: unital composition algebras are finite-dimensional -/

section Hurwitz

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]

/-- A unital composition product on the subspace `K`: `μ` is bilinear on the ambient space,
`K` is closed under it, `e ∈ K` is a two-sided unit on `K` of norm one, and
`‖μ x y‖ = ‖x‖ ‖y‖` on `K`. -/
structure IsComp (μ : D →ₗ[ℝ] D →ₗ[ℝ] D) (K : Submodule ℝ D) (e : D) : Prop where
  mem : ∀ x ∈ K, ∀ y ∈ K, μ x y ∈ K
  e_mem : e ∈ K
  left : ∀ x ∈ K, μ e x = x
  right : ∀ x ∈ K, μ x e = x
  norm : ∀ x ∈ K, ∀ y ∈ K, ‖μ x y‖ = ‖x‖ * ‖y‖
  e_norm : ‖e‖ = 1

variable {μ : D →ₗ[ℝ] D →ₗ[ℝ] D} {K : Submodule ℝ D} {e : D}

theorem polar_of_quad (f : D →ₗ[ℝ] D) (c : ℝ) (hf : ∀ y ∈ K, ⟪f y, f y⟫_ℝ = c * ⟪y, y⟫_ℝ)
    {y z : D} (hy : y ∈ K) (hz : z ∈ K) : ⟪f y, f z⟫_ℝ = c * ⟪y, z⟫_ℝ := by
  have h := hf (y + z) (K.add_mem hy hz)
  have h1 := hf y hy
  have h2 := hf z hz
  simp only [map_add, inner_add_left, inner_add_right] at h
  rw [real_inner_comm (f y) (f z), real_inner_comm y z] at h
  linarith

theorem eq_of_inner_K {u v : D} (hu : u ∈ K) (hv : v ∈ K)
    (h : ∀ z ∈ K, ⟪u, z⟫_ℝ = ⟪v, z⟫_ℝ) : u = v := by
  have := h (u - v) (K.sub_mem hu hv)
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ), inner_sub_left, this, sub_self]

namespace IsComp

variable (h : IsComp μ K e)
include h

theorem inner_self_mul {x y : D} (hx : x ∈ K) (hy : y ∈ K) :
    ⟪μ x y, μ x y⟫_ℝ = ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ := by
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    h.norm x hx y hy]; ring

theorem c1l {x y z : D} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    ⟪μ x y, μ x z⟫_ℝ = ⟪x, x⟫_ℝ * ⟪y, z⟫_ℝ :=
  polar_of_quad (μ x) _ (fun _ hy' => h.inner_self_mul hx hy') hy hz

theorem c1r {x y z : D} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    ⟪μ y x, μ z x⟫_ℝ = ⟪y, z⟫_ℝ * ⟪x, x⟫_ℝ := by
  have := polar_of_quad (μ.flip x) (⟪x, x⟫_ℝ)
    (fun y hy => by rw [LinearMap.flip_apply, h.inner_self_mul hy hx]; ring) hy hz
  rw [LinearMap.flip_apply, LinearMap.flip_apply] at this
  rw [this]; ring

theorem c2l {x w y z : D} (hx : x ∈ K) (hw : w ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    ⟪μ x y, μ w z⟫_ℝ + ⟪μ w y, μ x z⟫_ℝ = 2 * ⟪x, w⟫_ℝ * ⟪y, z⟫_ℝ := by
  have h0 := h.c1l (K.add_mem hx hw) hy hz
  have h1 := h.c1l hx hy hz
  have h2 := h.c1l hw hy hz
  simp only [map_add, LinearMap.add_apply, inner_add_left, inner_add_right] at h0
  have hc := real_inner_comm x w
  linear_combination h0 - h1 - h2 + ⟪y, z⟫_ℝ * hc

theorem c2r {x w y z : D} (hx : x ∈ K) (hw : w ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    ⟪μ y x, μ z w⟫_ℝ + ⟪μ y w, μ z x⟫_ℝ = 2 * ⟪x, w⟫_ℝ * ⟪y, z⟫_ℝ := by
  have h0 := h.c1r (K.add_mem hx hw) hy hz
  have h1 := h.c1r hx hy hz
  have h2 := h.c1r hw hy hz
  simp only [map_add, inner_add_left, inner_add_right] at h0
  have hc := real_inner_comm x w
  linear_combination h0 - h1 - h2 + ⟪y, z⟫_ℝ * hc

theorem e_inner : ⟪e, e⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, h.e_norm]; norm_num

omit h in
/-- Conjugation `x̄ = 2⟨x, e⟩ e − x`. -/
def cj (e x : D) : D := (2 * ⟪x, e⟫_ℝ) • e - x

theorem cj_mem {x : D} (hx : x ∈ K) : cj e x ∈ K :=
  K.sub_mem (K.smul_mem _ h.e_mem) hx

theorem cj_inner_e (x : D) : ⟪cj e x, e⟫_ℝ = ⟪x, e⟫_ℝ := by
  rw [cj, inner_sub_left, real_inner_smul_left, h.e_inner]; ring

theorem cj_cj (x : D) : cj e (cj e x) = x := by
  rw [cj, h.cj_inner_e, cj]; abel

theorem inner_cj (x z : D) : ⟪cj e x, z⟫_ℝ = ⟪x, cj e z⟫_ℝ := by
  simp only [cj, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm e z]; ring

theorem mul_cj_left (x z : D) : μ (cj e x) z = (2 * ⟪x, e⟫_ℝ) • μ e z - μ x z := by
  simp only [cj, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]

theorem mul_cj_right (x z : D) : μ z (cj e x) = (2 * ⟪x, e⟫_ℝ) • μ z e - μ z x := by
  simp only [cj, map_sub, map_smul]

/-- `⟨xy, z⟩ = ⟨y, x̄z⟩`. -/
theorem c3l {x y z : D} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    ⟪μ x y, z⟫_ℝ = ⟪y, μ (cj e x) z⟫_ℝ := by
  have h0 := h.c2l hx h.e_mem hy hz
  rw [h.left z hz, h.left y hy] at h0
  rw [h.mul_cj_left, h.left z hz, inner_sub_right, real_inner_smul_right]
  linarith

/-- `⟨yx, z⟩ = ⟨y, z x̄⟩`. -/
theorem c3r {x y z : D} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    ⟪μ y x, z⟫_ℝ = ⟪y, μ z (cj e x)⟫_ℝ := by
  have h0 := h.c2r hx h.e_mem hy hz
  rw [h.right z hz, h.right y hy] at h0
  rw [h.mul_cj_right, h.right z hz, inner_sub_right, real_inner_smul_right]
  linarith

theorem c3l' {x y z : D} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    ⟪μ (cj e x) y, z⟫_ℝ = ⟪y, μ x z⟫_ℝ := by
  rw [h.c3l (h.cj_mem hx) hy hz, h.cj_cj]

theorem c3r' {x y z : D} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    ⟪μ y (cj e x), z⟫_ℝ = ⟪y, μ z x⟫_ℝ := by
  rw [h.c3r (h.cj_mem hx) hy hz, h.cj_cj]

/-- Linearised `x̄(xy) = N(x) y`. -/
theorem c4l {x w y : D} (hx : x ∈ K) (hw : w ∈ K) (hy : y ∈ K) :
    μ (cj e x) (μ w y) + μ (cj e w) (μ x y) = (2 * ⟪x, w⟫_ℝ) • y := by
  refine eq_of_inner_K (K.add_mem (h.mem _ (h.cj_mem hx) _ (h.mem _ hw _ hy))
    (h.mem _ (h.cj_mem hw) _ (h.mem _ hx _ hy))) (K.smul_mem _ hy) fun z hz => ?_
  rw [inner_add_left, h.c3l' hx (h.mem _ hw _ hy) hz, h.c3l' hw (h.mem _ hx _ hy) hz,
    real_inner_smul_left, add_comm]
  exact h.c2l hx hw hy hz

/-- Linearised `(yx)x̄ = N(x) y`. -/
theorem c4r {x w y : D} (hx : x ∈ K) (hw : w ∈ K) (hy : y ∈ K) :
    μ (μ y w) (cj e x) + μ (μ y x) (cj e w) = (2 * ⟪x, w⟫_ℝ) • y := by
  refine eq_of_inner_K (K.add_mem (h.mem _ (h.mem _ hy _ hw) _ (h.cj_mem hx))
    (h.mem _ (h.mem _ hy _ hx) _ (h.cj_mem hw))) (K.smul_mem _ hy) fun z hz => ?_
  rw [inner_add_left, h.c3r' hx (h.mem _ hy _ hw) hz, h.c3r' hw (h.mem _ hy _ hx) hz,
    real_inner_smul_left, add_comm]
  exact h.c2r hx hw hy hz

/-- Conjugation is an anti-automorphism. -/
theorem cj_mul {x y : D} (hx : x ∈ K) (hy : y ∈ K) : cj e (μ x y) = μ (cj e y) (cj e x) := by
  refine eq_of_inner_K (h.cj_mem (h.mem _ hx _ hy))
    (h.mem _ (h.cj_mem hy) _ (h.cj_mem hx)) fun z hz => ?_
  rw [h.inner_cj, h.c3l hx hy (h.cj_mem hz), h.c3l' hy (h.cj_mem hx) hz,
    ← h.c3r hz hy (h.cj_mem hx)]
  exact real_inner_comm _ _

theorem cj_of_orth {j : D} (hj : ⟪j, e⟫_ℝ = 0) : cj e j = -j := by
  rw [cj, hj]; simp

/-! ### Doubling -/

variable {B : Submodule ℝ D} (hBK : B ≤ K) (heB : e ∈ B) (hBm : ∀ a ∈ B, ∀ b ∈ B, μ a b ∈ B)
  {j : D} (hjK : j ∈ K) (hj : ∀ b ∈ B, ⟪b, j⟫_ℝ = 0)
include hBK heB hBm hjK hj

theorem cj_mem_B {a : D} (ha : a ∈ B) : cj e a ∈ B := B.sub_mem (B.smul_mem _ heB) ha

theorem cj_j : cj e j = -j := h.cj_of_orth (by rw [real_inner_comm]; exact hj e heB)

/-- `a j = j ā`. -/
theorem dbl_a {a : D} (ha : a ∈ B) : μ a j = μ j (cj e a) := by
  have hcaK := hBK (h.cj_mem_B hBK heB hBm hjK hj ha)
  have h0 := h.c4l hcaK hjK h.e_mem
  rw [h.cj_cj, h.right j hjK, h.right _ hcaK, h.cj_j hBK heB hBm hjK hj,
    hj _ (h.cj_mem_B hBK heB hBm hjK hj ha)] at h0
  simp only [map_neg, LinearMap.neg_apply, mul_zero, zero_smul] at h0
  exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h0)

/-- `a (b j) = (b a) j`. -/
theorem dbl_f1 {a b : D} (ha : a ∈ B) (hb : b ∈ B) : μ a (μ b j) = μ (μ b a) j := by
  have hca := h.cj_mem_B hBK heB hBm hjK hj ha
  have hcb := h.cj_mem_B hBK heB hBm hjK hj hb
  have h0 := h.c4l (hBK hca) hjK (hBK hcb)
  rw [h.cj_cj, h.cj_j hBK heB hBm hjK hj, hj _ hca, ← h.cj_mul (hBK hb) (hBK ha)] at h0
  simp only [map_neg, LinearMap.neg_apply, mul_zero, zero_smul] at h0
  rw [← h.dbl_a hBK heB hBm hjK hj (hBm _ hb _ ha), ← h.dbl_a hBK heB hBm hjK hj hb] at h0
  exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h0)

/-- `(a j) b = (a b̄) j`. -/
theorem dbl_f2 {a b : D} (ha : a ∈ B) (hb : b ∈ B) : μ (μ a j) b = μ (μ a (cj e b)) j := by
  have hcb := h.cj_mem_B hBK heB hBm hjK hj hb
  have h0 := h.c4r (hBK hcb) hjK (hBK ha)
  rw [h.cj_cj, h.cj_j hBK heB hBm hjK hj, hj _ hcb] at h0
  simp only [map_neg, mul_zero, zero_smul] at h0
  exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h0)

/-- `⟨b j, a⟩ = 0`. -/
theorem dbl_orth {a b : D} (ha : a ∈ B) (hb : b ∈ B) : ⟪μ b j, a⟫_ℝ = 0 := by
  rw [h.c3l (hBK hb) hjK (hBK ha), real_inner_comm]
  exact hj _ (hBm _ (h.cj_mem_B hBK heB hBm hjK hj hb) _ ha)

/-- `j (j y) = −N(j) y`. -/
theorem jj {y : D} (hy : y ∈ K) : μ j (μ j y) = -(⟪j, j⟫_ℝ • y) := by
  have h0 := h.c4l hjK hjK hy
  rw [h.cj_j hBK heB hBm hjK hj] at h0
  simp only [map_neg, LinearMap.neg_apply] at h0
  linear_combination (norm := module) (-(1 / 2 : ℝ)) • h0

/-- `(a j)(b j) = −N(j) b̄ a`. -/
theorem dbl_f3 {a b : D} (ha : a ∈ B) (hb : b ∈ B) :
    μ (μ a j) (μ b j) = -(⟪j, j⟫_ℝ • μ (cj e b) a) := by
  have hcb := h.cj_mem_B hBK heB hBm hjK hj hb
  have hajK : μ a j ∈ K := h.mem _ (hBK ha) _ hjK
  have e1 : cj e (μ a j) = -(μ a j) := h.cj_of_orth (h.dbl_orth hBK heB hBm hjK hj heB ha)
  have e2 : ⟪cj e (μ a j), j⟫_ℝ = -(⟪a, e⟫_ℝ * ⟪j, j⟫_ℝ) := by
    have := h.c1r hjK (hBK ha) h.e_mem
    rw [h.left j hjK] at this
    rw [e1, inner_neg_left, this]
  have e3 : μ (cj e (μ a j)) (cj e b) = -(μ (μ a b) j) := by
    rw [e1, map_neg, LinearMap.neg_apply, h.dbl_f2 hBK heB hBm hjK hj ha hcb, h.cj_cj]
  have e4 : μ j (μ (μ a b) j) =
      -(⟪j, j⟫_ℝ • ((2 * ⟪a, e⟫_ℝ) • cj e b - μ (cj e b) a)) := by
    have hab := hBm _ ha _ hb
    rw [h.dbl_a hBK heB hBm hjK hj hab,
      h.jj hBK heB hBm hjK hj (h.cj_mem (hBK hab)), h.cj_mul (hBK ha) (hBK hb),
      h.mul_cj_right, h.right _ (hBK hcb)]
  have h0 := h.c4l (h.cj_mem hajK) hjK (hBK hcb)
  rw [h.cj_cj, ← h.dbl_a hBK heB hBm hjK hj hb, h.cj_j hBK heB hBm hjK hj, e2, e3] at h0
  simp only [map_neg, LinearMap.neg_apply, neg_neg] at h0
  rw [e4] at h0
  linear_combination (norm := module) h0

/-- If there is a non-zero `j ⊥ B`, then `B` is associative. -/
theorem dbl_assoc (hj0 : j ≠ 0) {a c d : D} (ha : a ∈ B) (hc : c ∈ B) (hd : d ∈ B) :
    μ d (μ a c) = μ (μ d a) c := by
  have hN : ⟪j, j⟫_ℝ ≠ 0 := inner_self_ne_zero.mpr hj0
  have key : ∀ b ∈ B, ⟪b, μ (μ d a) c - μ d (μ a c)⟫_ℝ = 0 := by
    intro b hb
    have hcc := h.cj_mem_B hBK heB hBm hjK hj hc
    have h0 := h.c2l (hBK ha) (h.mem _ (hBK hb) _ hjK) (hBK hc) (h.mem _ (hBK hd) _ hjK)
    rw [h.dbl_f3 hBK heB hBm hjK hj hb hd, h.dbl_f2 hBK heB hBm hjK hj hb hc,
      h.dbl_f1 hBK heB hBm hjK hj ha hd, ← real_inner_comm a (μ b j),
      h.dbl_orth hBK heB hBm hjK hj ha hb,
      h.c1r hjK (hBK (hBm _ hb _ hcc)) (hBK (hBm _ hd _ ha)),
      h.c3r' (hBK hc) (hBK hb) (hBK (hBm _ hd _ ha)), inner_neg_right, real_inner_smul_right,
      ← real_inner_comm (μ a c), h.c3l' (hBK hd) (hBK hb) (hBK (hBm _ ha _ hc))] at h0
    rw [inner_sub_right]
    have : ⟪j, j⟫_ℝ * (⟪b, μ (μ d a) c⟫_ℝ - ⟪b, μ d (μ a c)⟫_ℝ) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hN
    · exact h1
  have hm : μ (μ d a) c - μ d (μ a c) ∈ B :=
    B.sub_mem (hBm _ (hBm _ hd _ ha) _ hc) (hBm _ hd _ (hBm _ ha _ hc))
  have := key _ hm
  rw [inner_self_eq_zero, sub_eq_zero] at this
  exact this.symm

end IsComp

/-- The Cayley–Dickson double `B ⊕ B j`. -/
def dbl (μ : D →ₗ[ℝ] D →ₗ[ℝ] D) (B : Submodule ℝ D) (j : D) : Submodule ℝ D :=
  B ⊔ B.map (μ.flip j)

theorem mem_dbl {B : Submodule ℝ D} {j x : D} :
    x ∈ dbl μ B j ↔ ∃ a ∈ B, ∃ b ∈ B, x = a + μ b j := by
  simp only [dbl, Submodule.mem_sup, Submodule.mem_map, LinearMap.flip_apply]
  constructor
  · rintro ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩

namespace IsComp

variable (h : IsComp μ K e)
include h

variable {B : Submodule ℝ D} (hBK : B ≤ K) (heB : e ∈ B) (hBm : ∀ a ∈ B, ∀ b ∈ B, μ a b ∈ B)
  {j : D} (hjK : j ∈ K) (hj : ∀ b ∈ B, ⟪b, j⟫_ℝ = 0)
include hBK heB hBm hjK hj

theorem dbl_le : dbl μ B j ≤ K := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_dbl.mp hx
  exact K.add_mem (hBK ha) (h.mem _ (hBK hb) _ hjK)

theorem le_dbl : B ≤ dbl μ B j := le_sup_left

theorem j_mem_dbl : j ∈ dbl μ B j :=
  mem_dbl.mpr ⟨0, B.zero_mem, e, heB, by rw [h.left j hjK, zero_add]⟩

theorem dbl_mul_mem : ∀ x ∈ dbl μ B j, ∀ y ∈ dbl μ B j, μ x y ∈ dbl μ B j := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_dbl.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := mem_dbl.mp hy
  have hcc := h.cj_mem_B hBK heB hBm hjK hj hc
  have hcd := h.cj_mem_B hBK heB hBm hjK hj hd
  refine mem_dbl.mpr ⟨μ a c - ⟪j, j⟫_ℝ • μ (cj e d) b,
    B.sub_mem (hBm _ ha _ hc) (B.smul_mem _ (hBm _ hcd _ hb)),
    μ d a + μ b (cj e c), B.add_mem (hBm _ hd _ ha) (hBm _ hb _ hcc), ?_⟩
  simp only [map_add, LinearMap.add_apply]
  rw [h.dbl_f1 hBK heB hBm hjK hj ha hd, h.dbl_f2 hBK heB hBm hjK hj hb hc,
    h.dbl_f3 hBK heB hBm hjK hj hb hd]
  abel

/-- If `B ⊕ Bj` is associative, `B` is commutative. -/
theorem dbl_comm (hass : ∀ x ∈ dbl μ B j, ∀ y ∈ dbl μ B j, ∀ z ∈ dbl μ B j,
      μ (μ x y) z = μ x (μ y z)) (hj0 : j ≠ 0) {a b : D} (ha : a ∈ B) (hb : b ∈ B) :
    μ a b = μ b a := by
  have h1 := hass a (h.le_dbl hBK heB hBm hjK hj ha) b (h.le_dbl hBK heB hBm hjK hj hb) j
    (h.j_mem_dbl hBK heB hBm hjK hj)
  rw [h.dbl_f1 hBK heB hBm hjK hj ha hb, ← sub_eq_zero, ← LinearMap.sub_apply, ← map_sub] at h1
  have h2 := h.norm _ (K.sub_mem (h.mem _ (hBK ha) _ (hBK hb)) (h.mem _ (hBK hb) _ (hBK ha))) _ hjK
  rw [h1, norm_zero] at h2
  rcases mul_eq_zero.mp h2.symm with h3 | h3
  · exact sub_eq_zero.mp (norm_eq_zero.mp h3)
  · exact absurd (norm_eq_zero.mp h3) hj0

end IsComp

theorem exists_orth {B : Submodule ℝ D} [FiniteDimensional ℝ B] (hBK : B ≤ K)
    (hK : ¬ FiniteDimensional ℝ K) : ∃ j ∈ K, j ≠ 0 ∧ ∀ b ∈ B, ⟪b, j⟫_ℝ = 0 := by
  have hlt : B < K := lt_of_le_of_ne hBK (by rintro rfl; exact hK inferInstance)
  obtain ⟨v, hvK, hvB⟩ := SetLike.exists_of_lt hlt
  refine ⟨v - B.starProjection v, K.sub_mem hvK (hBK (B.starProjection_apply_mem v)), ?_,
    fun b hb => (Submodule.mem_orthogonal _ _).mp (B.sub_starProjection_mem_orthogonal v) b hb⟩
  intro h0
  rw [sub_eq_zero] at h0
  exact hvB (h0 ▸ B.starProjection_apply_mem v)

/-- **Hurwitz, infinite-dimensional form**: a unital composition product on `K` forces
`K` to be finite-dimensional (of dimension at most 8, though only finiteness is used). -/
theorem IsComp.finiteDimensional (h : IsComp μ K e) : FiniteDimensional ℝ K := by
  by_contra hK
  let B0 : Submodule ℝ D := ℝ ∙ e
  have hB0K : B0 ≤ K := (Submodule.span_singleton_le_iff_mem _ _).mpr h.e_mem
  have heB0 : e ∈ B0 := Submodule.mem_span_singleton_self e
  have hB0m : ∀ a ∈ B0, ∀ b ∈ B0, μ a b ∈ B0 := by
    intro a ha b hb
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_smul, map_smul, LinearMap.smul_apply, h.left e h.e_mem]
    exact B0.smul_mem _ (B0.smul_mem _ heB0)
  obtain ⟨j1, hj1K, hj10, hj1⟩ := exists_orth hB0K hK
  let B1 := dbl μ B0 j1
  have hB1K : B1 ≤ K := h.dbl_le hB0K heB0 hB0m hj1K hj1
  have heB1 : e ∈ B1 := h.le_dbl hB0K heB0 hB0m hj1K hj1 heB0
  have hB1m := h.dbl_mul_mem hB0K heB0 hB0m hj1K hj1
  have : FiniteDimensional ℝ B1 := by
    show FiniteDimensional ℝ ↥(B0 ⊔ B0.map (μ.flip j1)); infer_instance
  obtain ⟨j2, hj2K, hj20, hj2⟩ := exists_orth hB1K hK
  let B2 := dbl μ B1 j2
  have hB2K : B2 ≤ K := h.dbl_le hB1K heB1 hB1m hj2K hj2
  have heB2 : e ∈ B2 := h.le_dbl hB1K heB1 hB1m hj2K hj2 heB1
  have hB2m := h.dbl_mul_mem hB1K heB1 hB1m hj2K hj2
  have : FiniteDimensional ℝ B2 := by
    show FiniteDimensional ℝ ↥(B1 ⊔ B1.map (μ.flip j2)); infer_instance
  obtain ⟨j3, hj3K, hj30, hj3⟩ := exists_orth hB2K hK
  let B3 := dbl μ B2 j3
  have hB3K : B3 ≤ K := h.dbl_le hB2K heB2 hB2m hj3K hj3
  have heB3 : e ∈ B3 := h.le_dbl hB2K heB2 hB2m hj3K hj3 heB2
  have hB3m := h.dbl_mul_mem hB2K heB2 hB2m hj3K hj3
  have : FiniteDimensional ℝ B3 := by
    show FiniteDimensional ℝ ↥(B2 ⊔ B2.map (μ.flip j3)); infer_instance
  obtain ⟨j4, hj4K, hj40, hj4⟩ := exists_orth hB3K hK
  have hass3 : ∀ x ∈ B3, ∀ y ∈ B3, ∀ z ∈ B3, μ (μ x y) z = μ x (μ y z) :=
    fun x hx y hy z hz => (h.dbl_assoc hB3K heB3 hB3m hj4K hj4 hj40 hy hz hx).symm
  have hj1B2 : j1 ∈ B2 := h.le_dbl hB1K heB1 hB1m hj2K hj2 (h.j_mem_dbl hB0K heB0 hB0m hj1K hj1)
  have hj2B2 : j2 ∈ B2 := h.j_mem_dbl hB1K heB1 hB1m hj2K hj2
  have hc := h.dbl_comm hB2K heB2 hB2m hj3K hj3 hass3 hj30 hj1B2 hj2B2
  have ha := h.dbl_a hB1K heB1 hB1m hj2K hj2 (h.j_mem_dbl hB0K heB0 hB0m hj1K hj1)
  rw [h.cj_of_orth (by rw [real_inner_comm]; exact hj1 e heB0), map_neg, ← hc] at ha
  have h0 : μ j1 j2 = 0 := by
    have : (2 : ℝ) • μ j1 j2 = 0 := by rw [two_smul]; nth_rw 1 [ha]; exact neg_add_cancel _
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  have := h.norm _ hj1K _ hj2K
  rw [h0, norm_zero] at this
  rcases mul_eq_zero.mp this.symm with h3 | h3
  · exact hj10 (norm_eq_zero.mp h3)
  · exact hj20 (norm_eq_zero.mp h3)

/-- Hurwitz with a norm constant and an unnormalised unit. -/
theorem finiteDimensional_of_comp {w : D} (κ : ℝ) (hκ : 0 < κ)
    (hm : ∀ x ∈ K, ∀ y ∈ K, μ x y ∈ K) (hw : w ∈ K) (hw0 : w ≠ 0)
    (hl : ∀ x ∈ K, μ w x = x) (hr : ∀ x ∈ K, μ x w = x)
    (hn : ∀ x ∈ K, ∀ y ∈ K, ‖μ x y‖ = κ * ‖x‖ * ‖y‖) : FiniteDimensional ℝ K := by
  have hwn : κ * ‖w‖ = 1 := by
    have := hn w hw w hw
    rw [hl w hw] at this
    have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    field_simp at this
    linarith
  refine IsComp.finiteDimensional (μ := κ⁻¹ • μ) (e := κ • w) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    rw [LinearMap.smul_apply, LinearMap.smul_apply]; exact K.smul_mem _ (hm x hx y hy)
  · exact K.smul_mem _ hw
  · intro x hx
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hl x hx,
      smul_smul, inv_mul_cancel₀ hκ.ne', one_smul]
  · intro x hx
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hr x hx,
      smul_smul, inv_mul_cancel₀ hκ.ne', one_smul]
  · intro x hx y hy
    rw [LinearMap.smul_apply, LinearMap.smul_apply, norm_smul, hn x hx y hy, Real.norm_eq_abs,
      abs_inv, abs_of_pos hκ]
    field_simp
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hκ, hwn]

end Hurwitz

/-! ## B. The Jordan side: primitive idempotents -/

section Jordan

open Papers.REC.JBPeirce Papers.REC.JBCoord

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Mul E] [One E] [PaperEJA E]

instance (priority := 100) paperEJA_isJordanMul : IsJordanMul E :=
  ⟨pj_mul_comm, pj_add_mul, pj_smul_mul, pj_jordan⟩

/-- The Peirce `1`-space `{x | q x = x}` of an idempotent `q`, an EJA with unit `q`. -/
def QC (q : E) (_hq : q * q = q) : Type u := ↥(cornerSubm q)

section QC

variable {q : E} {hq : q * q = q}

noncomputable instance : NormedAddCommGroup (QC q hq) :=
  inferInstanceAs (NormedAddCommGroup ↥(cornerSubm q))

noncomputable instance : InnerProductSpace ℝ (QC q hq) :=
  inferInstanceAs (InnerProductSpace ℝ ↥(cornerSubm q))

instance : CompleteSpace (QC q hq) := (cornerSubm_closed q).completeSpace_coe

def QC.val (x : QC q hq) : E := (x : ↥(cornerSubm q)).1

theorem QC.mem (x : QC q hq) : q * x.val = x.val := mem_cornerSubm.mp (x : ↥(cornerSubm q)).2

theorem QC.ext {x y : QC q hq} (h : x.val = y.val) : x = y := Subtype.ext h

def QC.mk (x : E) (hx : q * x = x) : QC q hq := (⟨x, mem_cornerSubm.mpr hx⟩ : ↥(cornerSubm q))

theorem qc_mul_mem (hq : q * q = q) {x y : E} (hx : q * x = x) (hy : q * y = y) :
    q * (x * y) = x * y := by
  have := peirce_one_mul_one hq (x := x) (y := y) (by rw [mem_peirce, one_smul]; exact hx)
    (by rw [mem_peirce, one_smul]; exact hy)
  rwa [mem_peirce, one_smul] at this

noncomputable instance : Mul (QC q hq) :=
  ⟨fun x y => QC.mk (x.val * y.val) (qc_mul_mem hq x.mem y.mem)⟩

instance : One (QC q hq) := ⟨QC.mk q hq⟩

@[simp] theorem QC.mul_val (x y : QC q hq) : (x * y).val = x.val * y.val := rfl
@[simp] theorem QC.one_val : (1 : QC q hq).val = q := rfl
@[simp] theorem QC.add_val (x y : QC q hq) : (x + y).val = x.val + y.val := rfl
@[simp] theorem QC.smul_val (r : ℝ) (x : QC q hq) : (r • x).val = r • x.val := rfl
@[simp] theorem QC.mk_val (x : E) (hx : q * x = x) : (QC.mk x hx : QC q hq).val = x := rfl

instance : PaperEJA (QC q hq) where
  mul_comm _ _ := QC.ext (PaperEJA.mul_comm _ _)
  mul_add _ _ _ := QC.ext (PaperEJA.mul_add _ _ _)
  smul_mul _ _ _ := QC.ext (PaperEJA.smul_mul _ _ _)
  one_mul x := QC.ext x.mem
  jordan _ _ := QC.ext (PaperEJA.jordan _ _)
  inner_mul x y z := PaperEJA.inner_mul x.val y.val z.val

end QC

attribute [local instance] PaperEJA.order

/-- **An atomic idempotent is primitive**: `V₁(q) = ℝ q` (the spectral theorem, EJA 46, in
the EJA `V₁(q)`, whose idempotents lie below `q`). -/
theorem atomic_prim {q : E} (hat : IsAtomicP q) {x : E} (hx : q * x = x) :
    ∃ t : ℝ, x = t • q := by
  classical
  have hq := hat.1
  obtain ⟨T, hT, -, -, c, hc⟩ := spectral_family (QC.mk x hx : QC q hq)
  have hone : ∀ p ∈ T, p = 1 := by
    intro p hp
    have hpp : p.val * p.val = p.val := congrArg QC.val (hT.idem p hp)
    have hqp : q * p.val = p.val := p.mem
    have hpq : p.val * q = p.val := by rw [pj_mul_comm]; exact hqp
    have hle : p.val ≤ q := by
      rw [pe_le_iff]; refine idem_isSq ?_
      rw [pj_sub_mul, pj_mul_sub, pj_mul_sub, hq, hqp, hpq, hpp]; abel
    by_contra hne
    have h1 : p.val ≠ q := fun h => hne (QC.ext h)
    exact hT.ne_zero p hp (QC.ext (hat.2 p.val hpp hle h1))
  refine ⟨∑ p ∈ T, c p, ?_⟩
  have hs : ∑ p ∈ T, c p • p = ∑ p ∈ T, c p • (1 : QC q hq) :=
    Finset.sum_congr rfl fun p hp => by rw [hone p hp]
  rw [hs, ← Finset.sum_smul] at hc
  exact congrArg QC.val hc

/-! ## C. Off-diagonal Peirce spaces -/

/-- For orthogonal primitive idempotents `f, g` and `x ∈ V½(f) ∩ V½(g)`: `x² = λ (f + g)`
(the two coefficients agree by power associativity, `x² x² = x (x x²)`). -/
theorem sq_off {f g : E} (hf : f * f = f) (hg : g * g = g) (hfg : f * g = 0) (hf0 : f ≠ 0)
    (hg0 : g ≠ 0) (pf : ∀ x, f * x = x → ∃ t : ℝ, x = t • f)
    (pg : ∀ x, g * x = x → ∃ t : ℝ, x = t • g)
    {x : E} (hxf : x ∈ peirce f (1 / 2)) (hxg : x ∈ peirce g (1 / 2)) :
    ∃ l : ℝ, x * x = l • (f + g) := by
  have hgf : g * f = 0 := by rw [pj_mul_comm]; exact hfg
  have hs := add_idem_of_orth hf hg hfg
  have hx1 := mem_peirce_one_add hxf hxg
  have hxx : (f + g) * (x * x) = x * x := by
    have := peirce_one_mul_one hs hx1 hx1; rwa [mem_peirce, one_smul] at this
  have hd := peirce_decomp f (x * x)
  rw [peirce_half_mul_half hf hxf hxf, add_zero] at hd
  obtain ⟨a, ha⟩ := pf (P1 f (x * x)) (by
    have := P1_mem hf (x * x); rwa [mem_peirce, one_smul] at this)
  have h0 := P0_mem hf (x * x)
  rw [mem_peirce, zero_smul] at h0
  have hr : P0 f (x * x) = x * x - a • f := by rw [← ha]; exact eq_sub_of_add_eq' hd
  obtain ⟨b, hb⟩ := pg (P0 f (x * x)) (by
    have e1 : (f + g) * P0 f (x * x) = P0 f (x * x) := by
      rw [hr, pj_mul_sub, hxx, pj_mul_smul, pj_add_mul, hf, hgf, add_zero]
    rwa [pj_add_mul, h0, zero_add] at e1)
  have hsq : x * x = a • f + b • g := by rw [← hd, ← ha, ← hb]
  have hxf' : x * f = (1 / 2 : ℝ) • x := by rw [pj_mul_comm]; exact hxf
  have hxg' : x * g = (1 / 2 : ℝ) • x := by rw [pj_mul_comm]; exact hxg
  have h3 : x * (x * x) = ((a + b) / 2) • x := by
    rw [hsq, pj_mul_add, pj_mul_smul, pj_mul_smul, hxf', hxg']; module
  have h4 : x * (x * (x * x)) = ((a + b) / 2) • (a • f + b • g) := by
    rw [h3, pj_mul_smul, hsq]
  have h5 : (x * x) * (x * x) = (a * a) • f + (b * b) • g := by
    rw [hsq]
    simp only [pj_add_mul, pj_mul_add, pj_smul_mul, pj_mul_smul, hf, hg, hfg, hgf, smul_zero,
      add_zero, zero_add, smul_smul]
  have hJ := pj_jordan x x
  rw [h5, h4] at hJ
  have key : ∀ u v : ℝ, u • f + v • g = 0 → u = 0 ∧ v = 0 := by
    intro u v huv
    have h1 : f * (u • f + v • g) = f * 0 := by rw [huv]
    have h2 : g * (u • f + v • g) = g * 0 := by rw [huv]
    simp only [pj_mul_add, pj_mul_smul, hf, hg, hfg, hgf, smul_zero, add_zero, zero_add,
      pj_mul_zero] at h1 h2
    exact ⟨(smul_eq_zero.mp h1).resolve_right hf0, (smul_eq_zero.mp h2).resolve_right hg0⟩
  obtain ⟨k1, k2⟩ := key (a * a - (a + b) / 2 * a) (b * b - (a + b) / 2 * b)
    (by linear_combination (norm := module) hJ)
  have hab : a = b := by nlinarith [sq_nonneg (a - b)]
  exact ⟨a, by rw [hsq, hab, smul_add]⟩

/-- Peirce specialisation at a square: `y ∈ V₁(c)`, `y² = λ c`, `x ∈ V½(c)` ⟹
`y (y x) = (λ/4) x`. -/
theorem spec_quarter {c y x : E} (hc : c * c = c) (hy : y ∈ peirce c 1) {l : ℝ}
    (hyy : y * y = l • c) (hx : x ∈ peirce c (1 / 2)) : y * (y * x) = (l / 4) • x := by
  have h := peirce_spec hc hy hy hx
  rw [hyy, pj_smul_mul, mem_peirce.mp hx] at h
  linear_combination (norm := module) (-(1 / 2 : ℝ)) • h

section Frame

variable {ι : Type*} [DecidableEq ι] {e : ι → E}

/-- The off-diagonal joint Peirce space `V_ab = V½(e_a) ∩ V½(e_b)`. -/
noncomputable def Voff (e : ι → E) (a b : ι) : Submodule ℝ E := peirce (e a) (1 / 2) ⊓ peirce (e b) (1 / 2)

omit [DecidableEq ι] in
theorem Voff_comm (a b : ι) : Voff e a b = Voff e b a := inf_comm _ _

variable (he : ∀ i, e i * e i = e i) (horth : ∀ i j, i ≠ j → e i * e j = 0)
  (hne : ∀ i, e i ≠ 0) (hprim : ∀ i x, e i * x = x → ∃ t : ℝ, x = t • e i)
include he horth hne hprim

theorem pair_ne_zero {a b : ι} (hab : a ≠ b) : e a + e b ≠ 0 := by
  intro h0
  have : e a * (e a + e b) = e a * 0 := by rw [h0]
  simp only [pj_mul_add, he a, horth a b hab, add_zero, pj_mul_zero] at this
  exact hne a this

theorem sqV {a b : ι} (hab : a ≠ b) {x : E} (hx : x ∈ Voff e a b) :
    ∃ l : ℝ, x * x = l • (e a + e b) ∧ ‖x‖ ^ 2 = l * ‖e a + e b‖ ^ 2 := by
  obtain ⟨l, hl⟩ := sq_off (he a) (he b) (horth a b hab) (hne a) (hne b) (hprim a) (hprim b)
    hx.1 hx.2
  refine ⟨l, hl, ?_⟩
  have hc : (e a + e b) * x = x := by
    have := mem_peirce_one_add hx.1 hx.2; rwa [mem_peirce, one_smul] at this
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  have := PaperEJA.inner_mul x x (e a + e b)
  rw [pj_mul_comm x (e a + e b), hc, hl, real_inner_smul_left] at this
  exact this.symm

/-- `‖x y‖² = (λ/4) ‖x‖²` for `x ∈ V_ab`, `y ∈ V_bc`, `y² = λ (e_b + e_c)`. -/
theorem normsq_mul {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) {x y : E}
    (hx : x ∈ Voff e a b) (hy : y ∈ Voff e b c) {l : ℝ} (hyy : y * y = l • (e b + e c)) :
    ‖x * y‖ ^ 2 = l / 4 * ‖x‖ ^ 2 := by
  have hs := add_idem_of_orth (he b) (he c) (horth b c hbc)
  have hy1 := mem_peirce_one_add hy.1 hy.2
  have hxc : e c * x = 0 := frame_half_sub_zero he horth hab (Ne.symm hac) hbc.symm hx.1 hx.2
  have hxh : x ∈ peirce (e b + e c) (1 / 2) := by
    rw [mem_peirce, pj_add_mul, mem_peirce.mp hx.2, hxc, add_zero]
  have hq := spec_quarter hs hy1 hyy hxh
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, pj_mul_comm x y,
    PaperEJA.inner_mul, hq, real_inner_smul_right]

/-- Normalising a non-zero off-diagonal element: `x₀² = e_a + e_b`. -/
theorem normalize {a b : ι} (hab : a ≠ b) {x : E} (hx : x ∈ Voff e a b) (hx0 : x ≠ 0) :
    ∃ x₀ ∈ Voff e a b, x₀ * x₀ = e a + e b := by
  obtain ⟨l, hl, hn⟩ := sqV he horth hne hprim hab hx
  have hc : 0 < ‖e a + e b‖ ^ 2 := by
    have := norm_pos_iff.mpr (pair_ne_zero he horth hne hprim hab); positivity
  have hxp : 0 < ‖x‖ ^ 2 := by have := norm_pos_iff.mpr hx0; positivity
  have hlp : 0 < l := by
    by_contra h; push Not at h; nlinarith
  refine ⟨(Real.sqrt l)⁻¹ • x, (Voff e a b).smul_mem _ hx, ?_⟩
  rw [pj_smul_mul, pj_mul_smul, smul_smul, hl, smul_smul, ← mul_inv, Real.mul_self_sqrt hlp.le,
    inv_mul_cancel₀ hlp.ne', one_smul]

/-- **The composition product**: for distinct `a, b, c`, normalised `x₀ ∈ V_ab`,
`y₀ ∈ V_bc`, the product `u ⋆ v = 8 (y₀ u)(x₀ v)` on `V_ac` is unital with unit `2 x₀ y₀`
and `‖u ⋆ v‖ = ‖u‖ ‖v‖ / ‖e_b + e_c‖`; so `V_ac` is finite-dimensional (Hurwitz). -/
theorem off_comp {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) {x₀ y₀ : E}
    (hx₀ : x₀ ∈ Voff e a b) (hy₀ : y₀ ∈ Voff e b c) (hxx : x₀ * x₀ = e a + e b)
    (hyy : y₀ * y₀ = e b + e c) :
    FiniteDimensional ℝ (Voff e a c) ∧ (2 : ℝ) • (x₀ * y₀) ∈ Voff e a c ∧
      (2 : ℝ) • (x₀ * y₀) ≠ 0 := by
  have hba := hab.symm
  have hcb := hbc.symm
  have hca := hac.symm
  -- the membership rules
  have m1 : ∀ u ∈ Voff e a c, y₀ * u ∈ Voff e a b := fun u hu => by
    have := frame_mul_off_off he horth hbc hca hba hy₀.1 hy₀.2 hu.2 hu.1
    exact ⟨this.2, this.1⟩
  have m2 : ∀ v ∈ Voff e a c, x₀ * v ∈ Voff e b c := fun v hv =>
    frame_mul_off_off he horth hba hac hbc hx₀.2 hx₀.1 hv.1 hv.2
  have m3 : ∀ X ∈ Voff e a b, ∀ Y ∈ Voff e b c, X * Y ∈ Voff e a c := fun X hX Y hY =>
    frame_mul_off_off he horth hab hbc hac hX.1 hX.2 hY.1 hY.2
  -- the Peirce specialisation facts
  have hsB := add_idem_of_orth (he b) (he c) (horth b c hbc)
  have hsA := add_idem_of_orth (he a) (he b) (horth a b hab)
  have hy1 := mem_peirce_one_add hy₀.1 hy₀.2
  have hx1 := mem_peirce_one_add hx₀.1 hx₀.2
  have hB : ∀ u ∈ Voff e a c, u ∈ peirce (e b + e c) (1 / 2) := fun u hu => by
    rw [mem_peirce, pj_add_mul, mem_peirce.mp hu.2,
      frame_half_sub_zero he horth hac hba hbc hu.1 hu.2, zero_add]
  have hA : ∀ v ∈ Voff e a c, v ∈ peirce (e a + e b) (1 / 2) := fun v hv => by
    rw [mem_peirce, pj_add_mul, mem_peirce.mp hv.1,
      frame_half_sub_zero he horth hac hba hbc hv.1 hv.2, add_zero]
  have hxB : x₀ ∈ peirce (e b + e c) (1 / 2) := by
    rw [mem_peirce, pj_add_mul, mem_peirce.mp hx₀.2,
      frame_half_sub_zero he horth hab hca hcb hx₀.1 hx₀.2, add_zero]
  have hyA : y₀ ∈ peirce (e a + e b) (1 / 2) := by
    rw [mem_peirce, pj_add_mul, mem_peirce.mp hy₀.1,
      frame_half_sub_zero he horth hbc hab hac hy₀.1 hy₀.2, zero_add]
  have hyy' : y₀ * y₀ = (1 : ℝ) • (e b + e c) := by rw [one_smul, hyy]
  have hxx' : x₀ * x₀ = (1 : ℝ) • (e a + e b) := by rw [one_smul, hxx]
  have q1 : y₀ * (y₀ * x₀) = (1 / 4 : ℝ) • x₀ := by
    rw [spec_quarter hsB hy1 hyy' hxB]
  have q2 : ∀ u ∈ Voff e a c, y₀ * (y₀ * u) = (1 / 4 : ℝ) • u := fun u hu => by
    rw [spec_quarter hsB hy1 hyy' (hB u hu)]
  have q3 : ∀ v ∈ Voff e a c, x₀ * (x₀ * v) = (1 / 4 : ℝ) • v := fun v hv => by
    rw [spec_quarter hsA hx1 hxx' (hA v hv)]
  have q4 : x₀ * (x₀ * y₀) = (1 / 4 : ℝ) • y₀ := by
    rw [spec_quarter hsA hx1 hxx' hyA]
  -- the norms
  have nB : ‖e b + e c‖ ^ 2 ≠ 0 := by
    have := norm_pos_iff.mpr (pair_ne_zero he horth hne hprim hbc); positivity
  have n1 : ∀ u ∈ Voff e a c, ‖y₀ * u‖ ^ 2 = 1 / 4 * ‖u‖ ^ 2 := fun u hu => by
    rw [pj_mul_comm]
    have := normsq_mul he horth hne hprim hac hcb hab hu (show y₀ ∈ Voff e c b by rw [Voff_comm]; exact hy₀)
      (l := 1) (by rw [one_smul, hyy, add_comm])
    rw [this]
  have n2 : ∀ v ∈ Voff e a c, ‖x₀ * v‖ ^ 2 = 1 / 4 * ‖v‖ ^ 2 := fun v hv => by
    rw [pj_mul_comm]
    have := normsq_mul he horth hne hprim hca hab hcb (show v ∈ Voff e c a by rw [Voff_comm]; exact hv) hx₀ (l := 1)
      (by rw [one_smul, hxx])
    rw [this]
  let μ : E →ₗ[ℝ] E →ₗ[ℝ] E := LinearMap.mk₂ ℝ (fun u v => (8 : ℝ) • ((y₀ * u) * (x₀ * v)))
    (fun u u' v => by simp only [pj_mul_add, pj_add_mul]; module)
    (fun r u v => by simp only [pj_mul_smul, pj_smul_mul]; module)
    (fun u v v' => by simp only [pj_mul_add]; module)
    (fun r u v => by simp only [pj_mul_smul]; module)
  have hμ : ∀ u v, μ u v = (8 : ℝ) • ((y₀ * u) * (x₀ * v)) := fun _ _ => rfl
  have hw : (2 : ℝ) • (x₀ * y₀) ∈ Voff e a c := (Voff e a c).smul_mem _ (m3 _ hx₀ _ hy₀)
  have hwn : ‖(2 : ℝ) • (x₀ * y₀)‖ ^ 2 = ‖x₀‖ ^ 2 := by
    rw [norm_smul, mul_pow, normsq_mul he horth hne hprim hab hbc hac hx₀ hy₀ hyy',
      Real.norm_eq_abs, abs_two]
    ring
  have hx₀0 : x₀ ≠ 0 := by
    intro h0; rw [h0, pj_mul_zero] at hxx
    exact pair_ne_zero he horth hne hprim hab hxx.symm
  have hw0 : (2 : ℝ) • (x₀ * y₀) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwn
    have := norm_pos_iff.mpr hx₀0; nlinarith
  refine ⟨finiteDimensional_of_comp (μ := μ) (‖e b + e c‖⁻¹)
    (inv_pos.mpr (norm_pos_iff.mpr (pair_ne_zero he horth hne hprim hbc)))
    (fun u hu v hv => by rw [hμ]; exact (Voff e a c).smul_mem _ (m3 _ (m1 u hu) _ (m2 v hv)))
    hw hw0 ?_ ?_ ?_, hw, hw0⟩
  · intro v hv
    rw [hμ, pj_mul_smul, pj_mul_comm x₀ y₀, q1, pj_smul_mul, pj_smul_mul, q3 v hv]
    module
  · intro u hu
    rw [hμ, pj_mul_smul, q4, pj_mul_smul, pj_mul_smul, pj_mul_comm (y₀ * u) y₀, q2 u hu]
    module
  · intro u hu v hv
    obtain ⟨l, hl, hln⟩ := sqV he horth hne hprim hbc (m2 v hv)
    have h1 := normsq_mul he horth hne hprim hab hbc hac (m1 u hu) (m2 v hv) hl
    have h2 : ‖μ u v‖ ^ 2 = (‖e b + e c‖⁻¹ * ‖u‖ * ‖v‖) ^ 2 := by
      rw [hμ, norm_smul, mul_pow, h1, n1 u hu]
      rw [n2 v hv] at hln
      have hl' : l = 1 / 4 * ‖v‖ ^ 2 / ‖e b + e c‖ ^ 2 := by
        rw [eq_div_iff nB]; linarith
      rw [hl', Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
      field_simp; ring
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h2


/-- `V_ab, V_bc ≠ 0` (distinct `a, b, c`) ⟹ `V_ac` is finite-dimensional and non-zero. -/
theorem off_nonzero {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hx : ∃ x ∈ Voff e a b, x ≠ 0) (hy : ∃ y ∈ Voff e b c, y ≠ 0) :
    FiniteDimensional ℝ (Voff e a c) ∧ ∃ z ∈ Voff e a c, z ≠ 0 := by
  obtain ⟨x, hx, hx0⟩ := hx
  obtain ⟨y, hy, hy0⟩ := hy
  obtain ⟨x₀, hx₀, hxx⟩ := normalize he horth hne hprim hab hx hx0
  obtain ⟨y₀, hy₀, hyy⟩ := normalize he horth hne hprim hbc hy hy0
  obtain ⟨h1, h2, h3⟩ := off_comp he horth hne hprim hab hbc hac hx₀ hy₀ hxx hyy
  exact ⟨h1, _, h2, h3⟩

/-- If every off-diagonal Peirce space of a frame is finite-dimensional, so is `E` (the joint
Peirce decomposition, with `V_ii = ℝ e_i`). -/
theorem finiteDimensional_of_off [Fintype ι] (hsum : ∑ i, e i = 1)
    (hoff : ∀ i j, i ≠ j → FiniteDimensional ℝ (Voff e i j)) : FiniteDimensional ℝ E := by
  classical
  let W : ι × ι → Submodule ℝ E := fun p => if p.1 = p.2 then ⊥ else Voff e p.1 p.2
  have hW : ∀ p, FiniteDimensional ℝ (W p) := by
    intro p
    by_cases h : p.1 = p.2
    · exact Submodule.finiteDimensional_of_le (show W p ≤ ⊥ from (if_pos h).le)
    · have := hoff _ _ h
      exact Submodule.finiteDimensional_of_le (show W p ≤ Voff e p.1 p.2 from (if_neg h).le)
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range e) ⊔ ⨆ p, W p
  have hS : FiniteDimensional ℝ S := by
    have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range e)) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range e)
    infer_instance
  have htop : S = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    rw [frame_decomp he horth pj_one_mul hsum x]
    refine S.add_mem (S.sum_mem fun i _ => ?_)
      (S.smul_mem _ (S.sum_mem fun i _ => S.sum_mem fun j hj => ?_))
    · obtain ⟨t, ht⟩ := hprim i (P1 (e i) x) (by
        have := P1_mem (he i) x; rwa [mem_peirce, one_smul] at this)
      rw [ht]
      exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
      refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem (i, j) ?_)
      dsimp only [W]
      rw [if_neg hij]
      exact frame_offdiag_mem he horth i j x
  exact (LinearEquiv.ofTop S htop).finiteDimensional

/-- If `V_ik = V_jk = 0` for every `k ∉ {i, j}`, then `V½(e_i + e_j) = 0`. -/
theorem half_zero_pair [Fintype ι] (hsum : ∑ i, e i = 1) {i j : ι} (hij : i ≠ j)
    (hV : ∀ k, k ≠ i → k ≠ j → Voff e i k = ⊥ ∧ Voff e j k = ⊥)
    {z : E} (hz : z ∈ peirce (e i + e j) (1 / 2)) : z = 0 := by
  have hz' : (e i + e j) * z = (1 / 2 : ℝ) • z := hz
  have half_ne : ∀ w : E, (e i + e j) * w = (1 / 2 : ℝ) • w → ∀ c : ℝ, c ≠ 1 / 2 →
      (e i + e j) * w = c • w → w = 0 := by
    intro w h1 c hc h2
    have : (c - 1 / 2) • w = 0 := by rw [sub_smul, ← h2, ← h1, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc)
  have h1 : ∀ k, P1 (e k) z = 0 := by
    intro k
    have hwk : P1 (e k) z ∈ peirce (e k) 1 := P1_mem (he k) z
    have hpw : (e i + e j) * P1 (e k) z = (1 / 2 : ℝ) • P1 (e k) z := by
      rw [pj_add_mul, frame_L_P1 he horth k i z, frame_L_P1 he horth k j z, ← map_add,
        ← pj_add_mul, hz', map_smul]
    have hev : ∀ m, e m * P1 (e k) z = if m = k then P1 (e k) z else 0 := by
      intro m
      split_ifs with hm
      · subst hm; rwa [mem_peirce, one_smul] at hwk
      · exact frame_one_sub_zero he horth (Ne.symm hm) hwk
    by_cases hik : i = k
    · have hjk : j ≠ k := fun h => hij (hik.trans h.symm)
      refine half_ne _ hpw 1 (by norm_num) ?_
      rw [pj_add_mul, hev i, hev j, if_pos hik, if_neg hjk, add_zero, one_smul]
    · by_cases hjk : j = k
      · refine half_ne _ hpw 1 (by norm_num) ?_
        rw [pj_add_mul, hev i, hev j, if_neg hik, if_pos hjk, zero_add, one_smul]
      · refine half_ne _ hpw 0 (by norm_num) ?_
        rw [pj_add_mul, hev i, hev j, if_neg hik, if_neg hjk, add_zero, zero_smul]
  have h2 : ∀ k l, k ≠ l → Ph (e k) (Ph (e l) z) = 0 := by
    intro k l hkl
    have hw := frame_offdiag_mem he horth k l z
    have hpw : (e i + e j) * Ph (e k) (Ph (e l) z) = (1 / 2 : ℝ) • Ph (e k) (Ph (e l) z) := by
      rw [pj_add_mul, frame_L_Ph he horth k i, frame_L_Ph he horth l i, frame_L_Ph he horth k j,
        frame_L_Ph he horth l j, ← map_add, ← map_add, ← pj_add_mul, hz', map_smul, map_smul]
    have hev : ∀ m, e m * Ph (e k) (Ph (e l) z) =
        if m = k ∨ m = l then (1 / 2 : ℝ) • Ph (e k) (Ph (e l) z) else 0 := by
      intro m
      split_ifs with hm
      · rcases hm with rfl | rfl
        · exact hw.1
        · exact hw.2
      · push Not at hm
        exact frame_half_sub_zero he horth hkl hm.1 hm.2 hw.1 hw.2
    have hmem : Ph (e k) (Ph (e l) z) ∈ Voff e k l := hw
    have bot : ∀ a b, Voff e a b = ⊥ → Ph (e k) (Ph (e l) z) ∈ Voff e a b →
        Ph (e k) (Ph (e l) z) = 0 := fun a b h hm => by
      rw [h] at hm; exact (Submodule.mem_bot ℝ).mp hm
    by_cases hi : i = k ∨ i = l
    · by_cases hj : j = k ∨ j = l
      · refine half_ne _ hpw 1 (by norm_num) ?_
        rw [pj_add_mul, hev i, hev j, if_pos hi, if_pos hj, ← add_smul]; norm_num
      · push Not at hj
        rcases hi with rfl | rfl
        · exact bot i l (hV l (Ne.symm hkl) (Ne.symm hj.2)).1 hmem
        · exact bot i k (hV k hkl (Ne.symm hj.1)).1 (by rw [Voff_comm]; exact hmem)
    · by_cases hj : j = k ∨ j = l
      · push Not at hi
        rcases hj with rfl | rfl
        · exact bot j l (hV l (Ne.symm hi.2) (Ne.symm hkl)).2 hmem
        · exact bot j k (hV k (Ne.symm hi.1) hkl).2 (by rw [Voff_comm]; exact hmem)
      · refine half_ne _ hpw 0 (by norm_num) ?_
        rw [pj_add_mul, hev i, hev j, if_neg hi, if_neg hj, add_zero, zero_smul]
  rw [frame_decomp he horth pj_one_mul hsum z, Finset.sum_eq_zero (fun k _ => h1 k),
    Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero fun l hl =>
      h2 k l (Ne.symm (Finset.ne_of_mem_erase hl)))]
  simp

omit hne hprim in
/-- An idempotent with `V½(p) = 0` is central. -/
theorem central_of_half_zero {p : E} (hp : p * p = p)
    (h : ∀ z, z ∈ peirce p (1 / 2) → z = 0) : IsCentral p := by
  intro x y
  have hx := peirce_decomp p x
  have hy := peirce_decomp p y
  rw [h _ (Ph_mem hp x), add_zero] at hx
  rw [h _ (Ph_mem hp y), add_zero] at hy
  obtain ⟨x1, x0, hx1, hx0, rfl⟩ : ∃ x1 x0, x1 ∈ peirce p 1 ∧ x0 ∈ peirce p 0 ∧ x = x1 + x0 :=
    ⟨_, _, P1_mem hp x, P0_mem hp x, hx.symm⟩
  obtain ⟨y1, y0, hy1, hy0, rfl⟩ : ∃ y1 y0, y1 ∈ peirce p 1 ∧ y0 ∈ peirce p 0 ∧ y = y1 + y0 :=
    ⟨_, _, P1_mem hp y, P0_mem hp y, hy.symm⟩
  have a1 : x1 * y0 = 0 := peirce_one_mul_zero hp hx1 hy0
  have a2 : x0 * y1 = 0 := by rw [pj_mul_comm]; exact peirce_one_mul_zero hp hy1 hx0
  have a3 : p * (x1 * y1) = x1 * y1 := by
    have := peirce_one_mul_one hp hx1 hy1; rwa [mem_peirce, one_smul] at this
  have a4 : p * (x0 * y0) = 0 := by
    have := peirce_zero_mul_zero hp hx0 hy0; rwa [mem_peirce, zero_smul] at this
  have a5 : p * x1 = x1 := by rwa [mem_peirce, one_smul] at hx1
  have a6 : p * x0 = 0 := by rwa [mem_peirce, zero_smul] at hx0
  simp only [pj_add_mul, pj_mul_add, a1, a2, a3, a4, a5, a6, add_zero, zero_add]

/-- **The factor argument**: in an infinite-dimensional factor, a frame of atomic idempotents
has two members `e_i, e_j` with `e_i + e_j = 1` and `V_ij` infinite-dimensional. -/
theorem frame_case [Fintype ι] (hsum : ∑ i, e i = 1) (hfac : IsFactor E)
    (hinf : ¬ FiniteDimensional ℝ E) :
    ∃ i j, i ≠ j ∧ e i + e j = 1 ∧ ¬ FiniteDimensional ℝ (Voff e i j) := by
  obtain ⟨i, j, hij, hV⟩ : ∃ i j, i ≠ j ∧ ¬ FiniteDimensional ℝ (Voff e i j) := by
    by_contra hcon
    push Not at hcon
    exact hinf (finiteDimensional_of_off he horth hne hprim hsum hcon)
  have nz : ∀ a b, ¬ FiniteDimensional ℝ (Voff e a b) → ∃ x ∈ Voff e a b, x ≠ 0 := by
    intro a b h
    by_contra hc
    push Not at hc
    apply h
    rw [(Submodule.eq_bot_iff _).mpr hc]
    infer_instance
  have kill : ∀ a b, a ≠ b → ¬ FiniteDimensional ℝ (Voff e a b) →
      ∀ k, k ≠ a → k ≠ b → Voff e a k = ⊥ := by
    intro a b hab hinf' k hka hkb
    refine (Submodule.eq_bot_iff _).mpr fun z hz => ?_
    by_contra hz0
    obtain ⟨x, hx, hx0⟩ := nz a b hinf'
    obtain ⟨-, w, hw, hw0⟩ := off_nonzero he horth hne hprim hab.symm hka.symm hkb.symm
      ⟨x, by rw [Voff_comm]; exact hx, hx0⟩ ⟨z, hz, hz0⟩
    exact hinf' (off_nonzero he horth hne hprim hka.symm hkb hab ⟨z, hz, hz0⟩
      ⟨w, by rw [Voff_comm]; exact hw, hw0⟩).1
  have hV' : ∀ k, k ≠ i → k ≠ j → Voff e i k = ⊥ ∧ Voff e j k = ⊥ := fun k hki hkj =>
    ⟨kill i j hij hV k hki hkj, kill j i hij.symm (by rwa [Voff_comm]) k hkj hki⟩
  have hp := add_idem_of_orth (he i) (he j) (horth i j hij)
  obtain ⟨t, ht⟩ := hfac _ (central_of_half_zero he horth hp
    fun z hz => half_zero_pair he horth hne hprim hsum hij hV' hz)
  have hp0 := pair_ne_zero he horth hne hprim hij
  have h10 : (1 : E) ≠ 0 := by
    intro h; rw [h, smul_zero] at ht; exact hp0 ht
  have ht1 : t = 1 := by
    rw [ht, pj_smul_mul, pj_mul_smul, pj_one_mul, smul_smul] at hp
    have : (t * t - t) • (1 : E) = 0 := by rw [sub_smul, hp, sub_self]
    have htt := (smul_eq_zero.mp this).resolve_right h10
    have ht0 : t ≠ 0 := by rintro rfl; rw [zero_smul] at ht; exact hp0 ht
    have : t * (t - 1) = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ht0)
  exact ⟨i, j, hij, by rw [ht, ht1, one_smul], hV⟩

end Frame

/-! ## E. Rank two: the spin factor -/

/-- **An EJA whose `1^⊥` squares into `ℝ 1` is a spin factor**:
`a ↦ (‖1‖⁻¹ (a − t 1), t)`, `t = ⟨a, 1⟩/⟨1, 1⟩`, is an isomorphism onto `SpinFactor (1^⊥)`. -/
theorem spin_iso (h1 : (1 : E) ≠ 0)
    (hK : ∀ k ∈ (ℝ ∙ (1 : E))ᗮ, ∃ s : ℝ, k * k = s • (1 : E)) :
    Nonempty (EJAIso E (SpinFactor ↥(ℝ ∙ (1 : E))ᗮ)) := by
  set K := (ℝ ∙ (1 : E))ᗮ with hKdef
  set N : ℝ := ⟪(1 : E), 1⟫_ℝ with hN
  have hNpos : 0 < N := real_inner_self_pos.mpr h1
  have kk : ∀ k ∈ K, k * k = (⟪k, k⟫_ℝ / N) • (1 : E) := by
    intro k hk
    obtain ⟨s, hs⟩ := hK k hk
    have := PaperEJA.inner_mul k k 1
    rw [pj_mul_one, hs, real_inner_smul_left] at this
    rw [hs, ← this, mul_div_assoc, div_self hNpos.ne', mul_one]
  have kk' : ∀ k ∈ K, ∀ k' ∈ K, k * k' = (⟪k, k'⟫_ℝ / N) • (1 : E) := by
    intro k hk k' hk'
    have h0 := kk (k + k') (K.add_mem hk hk')
    have ha := kk k hk
    have hb := kk k' hk'
    simp only [pj_add_mul, pj_mul_add, inner_add_left, inner_add_right] at h0
    rw [pj_mul_comm k' k, real_inner_comm k k'] at h0
    linear_combination (norm := module) (1 / 2 : ℝ) • (h0 - ha - hb)
  have hK1 : ∀ k ∈ K, ⟪k, (1 : E)⟫_ℝ = 0 := fun k hk =>
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp hk
  let t : E → ℝ := fun a => ⟪a, 1⟫_ℝ / N
  let π : E → E := fun a => a - t a • (1 : E)
  have hπ : ∀ a, π a ∈ K := fun a => by
    refine Submodule.mem_orthogonal_singleton_iff_inner_left.mpr ?_
    simp only [π, t, inner_sub_left, real_inner_smul_left]
    rw [← hN, div_mul_cancel₀ _ hNpos.ne', sub_self]
  have hdec : ∀ a, a = t a • (1 : E) + π a := fun a => by simp only [π]; abel
  have ht_uniq : ∀ (r : ℝ) (k : E), k ∈ K → t (r • (1 : E) + k) = r := fun r k hk => by
    simp only [t, inner_add_left, real_inner_smul_left, hK1 k hk, add_zero]
    rw [← hN, mul_div_assoc, div_self hNpos.ne', mul_one]
  have hπ_uniq : ∀ (r : ℝ) (k : E), k ∈ K → π (r • (1 : E) + k) = k := fun r k hk => by
    simp only [π]; rw [ht_uniq r k hk]; abel
  set c : ℝ := (Real.sqrt N)⁻¹ with hc
  have hsq : Real.sqrt N * c = 1 := by rw [hc, mul_inv_cancel₀ (Real.sqrt_pos.mpr hNpos).ne']
  have hc2 : c * c = N⁻¹ := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt hNpos.le]
  let φ : E → SpinFactor K := fun a => WithLp.toLp 2 (⟨c • π a, K.smul_mem _ (hπ a)⟩, t a)
  let ψ : SpinFactor K → E := fun x => x.snd • (1 : E) + Real.sqrt N • (x.fst : E)
  have φfst : ∀ a, ((φ a).fst : E) = c • π a := fun _ => rfl
  have φsnd : ∀ a, (φ a).snd = t a := fun _ => rfl
  have hφ_of : ∀ (r : ℝ) (k : E) (hk : k ∈ K), φ (r • (1 : E) + k) =
      WithLp.toLp 2 (⟨c • k, K.smul_mem _ hk⟩, r) := fun r k hk => by
    apply spin_ext
    · exact Subtype.ext (by
        show c • π (r • (1 : E) + k) = c • k
        rw [hπ_uniq r k hk])
    · exact ht_uniq r k hk
  have hadd : ∀ a b, t (a + b) = t a + t b ∧ π (a + b) = π a + π b := fun a b => by
    have e1 : a + b = (t a + t b) • (1 : E) + (π a + π b) := by
      conv_lhs => rw [hdec a, hdec b]
      module
    rw [e1, ht_uniq _ _ (K.add_mem (hπ a) (hπ b)), hπ_uniq _ _ (K.add_mem (hπ a) (hπ b))]
    exact ⟨rfl, rfl⟩
  refine ⟨⟨⟨⟨⟨φ, ?_⟩, ?_⟩, ψ, ?_, ?_⟩, ?_, ?_⟩⟩
  · intro a b
    apply spin_ext
    · exact Subtype.ext (by
        show c • π (a + b) = c • π a + c • π b
        rw [(hadd a b).2, smul_add])
    · exact (hadd a b).1
  · intro r a
    have e1 : r • a = (r * t a) • (1 : E) + r • π a := by
      conv_lhs => rw [hdec a]
      module
    rw [RingHom.id_apply]
    apply spin_ext
    · exact Subtype.ext (by
        show c • π (r • a) = r • (c • π a)
        rw [e1, hπ_uniq _ _ (K.smul_mem _ (hπ a)), smul_comm])
    · show t (r • a) = r • t a
      rw [e1, ht_uniq _ _ (K.smul_mem _ (hπ a)), smul_eq_mul]
  · intro a
    show (φ a).snd • (1 : E) + Real.sqrt N • ((φ a).fst : E) = a
    rw [φsnd, φfst, smul_smul, hsq, one_smul]
    exact (hdec a).symm
  · intro x
    show φ (x.snd • (1 : E) + Real.sqrt N • (x.fst : E)) = x
    rw [hφ_of _ _ (K.smul_mem _ x.fst.2)]
    apply spin_ext
    · exact Subtype.ext (by
        show c • Real.sqrt N • (x.fst : E) = (x.fst : E)
        rw [smul_smul, mul_comm, hsq, one_smul])
    · rfl
  · intro a b
    show φ (a * b) = φ a * φ b
    have e1 : a * b = (t a * t b + ⟪π a, π b⟫_ℝ / N) • (1 : E) + (t a • π b + t b • π a) := by
      conv_lhs => rw [hdec a, hdec b]
      simp only [pj_add_mul, pj_mul_add, pj_smul_mul, pj_mul_smul, pj_one_mul, pj_mul_one,
        kk' _ (hπ a) _ (hπ b)]
      module
    rw [e1, hφ_of _ _ (K.add_mem (K.smul_mem _ (hπ b)) (K.smul_mem _ (hπ a)))]
    apply spin_ext
    · rw [spin_mul_fst]
      exact Subtype.ext (by
        show c • (t a • π b + t b • π a) = (φ b).snd • (c • π a) + (φ a).snd • (c • π b)
        rw [φsnd, φsnd]
        module)
    · rw [spin_mul_snd, φsnd, φsnd]
      show t a * t b + ⟪π a, π b⟫_ℝ / N = ⟪(φ a).fst, (φ b).fst⟫_ℝ + t a * t b
      rw [Submodule.coe_inner, φfst, φfst, real_inner_smul_left, real_inner_smul_right,
        ← mul_assoc, hc2]
      ring
  · show φ 1 = 1
    have : (1 : E) = (1 : ℝ) • (1 : E) + 0 := by rw [one_smul, add_zero]
    rw [this, hφ_of _ _ K.zero_mem]
    apply spin_ext
    · exact Subtype.ext (by show c • (0 : E) = 0; exact smul_zero c)
    · rfl

/-- **Rank two**: `1 = f + g` with `f, g` atomic and `V½(f) ≠ 0`; then every `k ⊥ 1` has
`k² ∈ ℝ 1`. -/
theorem rank_two {f g : E} (hf : f * f = f) (hg : g * g = g) (hfg : f * g = 0) (hf0 : f ≠ 0)
    (hg0 : g ≠ 0) (h1 : f + g = 1) (pf : ∀ x, f * x = x → ∃ t : ℝ, x = t • f)
    (pg : ∀ x, g * x = x → ∃ t : ℝ, x = t • g) {x₀ : E} (hx₀ : x₀ ∈ peirce f (1 / 2))
    (hx₀0 : x₀ ≠ 0) : ∀ k ∈ (ℝ ∙ (1 : E))ᗮ, ∃ s : ℝ, k * k = s • (1 : E) := by
  have hgf : g * f = 0 := by rw [pj_mul_comm]; exact hfg
  have gx : ∀ x, g * x = x - f * x := fun x => by
    rw [eq_sub_iff_add_eq, ← pj_add_mul, add_comm, h1, pj_one_mul]
  have half_g : ∀ x ∈ peirce f (1 / 2), x ∈ peirce g (1 / 2) := fun x hx => by
    rw [mem_peirce, gx, mem_peirce.mp hx]; module
  have sqx : ∀ x ∈ peirce f (1 / 2), ∃ l : ℝ, x * x = l • (f + g) := fun x hx =>
    sq_off hf hg hfg hf0 hg0 pf pg hx (half_g x hx)
  have ifg : ⟪f, g⟫_ℝ = 0 := idem_inner_orth hf hfg
  have ihalf : ∀ p : E, p * p = p → ∀ x ∈ peirce p (1 / 2), ⟪x, p⟫_ℝ = 0 := by
    intro p hp x hx
    have := PaperEJA.inner_mul p x p
    rw [mem_peirce.mp hx, hp, real_inner_smul_left] at this
    linarith
  -- `‖f‖ = ‖g‖`
  have hfgn : ⟪f, f⟫_ℝ = ⟪g, g⟫_ℝ := by
    obtain ⟨l, hl⟩ := sqx x₀ hx₀
    have hxf : x₀ * f = (1 / 2 : ℝ) • x₀ := by rw [pj_mul_comm]; exact hx₀
    have hxg : x₀ * g = (1 / 2 : ℝ) • x₀ := by rw [pj_mul_comm]; exact half_g x₀ hx₀
    have e1 := PaperEJA.inner_mul x₀ x₀ f
    have e2 := PaperEJA.inner_mul x₀ x₀ g
    rw [hl, hxf, real_inner_smul_left, real_inner_smul_right, inner_add_left,
      real_inner_comm f g, ifg] at e1
    rw [hl, hxg, real_inner_smul_left, real_inner_smul_right, inner_add_left, ifg] at e2
    have hx2 : 0 < ⟪x₀, x₀⟫_ℝ := real_inner_self_pos.mpr hx₀0
    have hl0 : l ≠ 0 := by rintro rfl; rw [zero_mul] at e1; linarith
    have : l * (⟪f, f⟫_ℝ - ⟪g, g⟫_ℝ) = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hl0)
  intro k hk
  have hk1 : ⟪k, (1 : E)⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.mp hk
  have hd := peirce_decomp f k
  obtain ⟨a, ha⟩ := pf (P1 f k) (by have := P1_mem hf k; rwa [mem_peirce, one_smul] at this)
  have h0 := P0_mem hf k
  rw [mem_peirce, zero_smul] at h0
  obtain ⟨b, hb⟩ := pg (P0 f k) (by rw [gx, h0, sub_zero])
  set x := Ph f k with hxdef
  have hxm : x ∈ peirce f (1 / 2) := Ph_mem hf k
  obtain ⟨l, hl⟩ := sqx x hxm
  have hab : b = -a := by
    rw [← hd, ha, hb, ← h1] at hk1
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, ihalf f hf x hxm,
      ihalf g hg x (half_g x hxm), ifg, real_inner_comm f g] at hk1
    have hfpos : 0 < ⟪f, f⟫_ℝ := real_inner_self_pos.mpr hf0
    rw [← hfgn] at hk1
    have : (a + b) * ⟪f, f⟫_ℝ = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_right hfpos.ne'
    linarith
  have hfx : f * x = (1 / 2 : ℝ) • x := hxm
  have hgx : g * x = (1 / 2 : ℝ) • x := half_g x hxm
  have hxf : x * f = (1 / 2 : ℝ) • x := by rw [pj_mul_comm]; exact hfx
  have hxg : x * g = (1 / 2 : ℝ) • x := by rw [pj_mul_comm]; exact hgx
  refine ⟨a * a + l, ?_⟩
  rw [← hd, ha, hb, hab, ← h1]
  simp only [pj_add_mul, pj_mul_add, pj_smul_mul, pj_mul_smul, hf, hg, hfg, hgf, hfx, hgx, hxf,
    hxg, hl, smul_zero, add_zero, zero_add]
  module

/-! ## The classification of factors, and EJA 54 unconditionally -/

/-- **`HOSClassification` holds**: an EJA that is a factor is finite-dimensional or
Jordan-isomorphic to the spin factor of an infinite-dimensional Hilbert space. -/
theorem hosClassification : HOSClassification.{u} := by
  intro F _ _ _ _ _ _ hfac
  by_cases hfin : FiniteDimensional ℝ F
  · exact Or.inl hfin
  right
  classical
  obtain ⟨T, hT, hat, hsum⟩ := atomicsum (pj_mul_one (1 : F))
  let e : {q // q ∈ T} → F := Subtype.val
  have he : ∀ i, e i * e i = e i := fun i => hT.idem i.1 i.2
  have horth : ∀ i j, i ≠ j → e i * e j = 0 := fun i j h =>
    hT.orth i.1 i.2 j.1 j.2 (fun h' => h (Subtype.ext h'))
  have hne : ∀ i, e i ≠ 0 := fun i => hT.ne_zero i.1 i.2
  have hprim : ∀ i x, e i * x = x → ∃ t : ℝ, x = t • e i := fun i x hx =>
    atomic_prim (hat i.1 i.2) hx
  have hsum' : ∑ i, e i = 1 := by rw [← hsum]; exact Finset.sum_coe_sort T (fun q => q)
  obtain ⟨i, j, hij, h1, hV⟩ := frame_case he horth hne hprim hsum' hfac hfin
  obtain ⟨x₀, hx₀, hx₀0⟩ : ∃ x ∈ Voff e i j, x ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hV
    rw [(Submodule.eq_bot_iff _).mpr hc]
    infer_instance
  have hK := rank_two (he i) (he j) (horth i j hij) (hne i) (hne j) h1 (hprim i) (hprim j)
    hx₀.1 hx₀0
  have h1ne : (1 : F) ≠ 0 := fun h => hne i (by rw [← pj_one_mul (e i), h, pj_zero_mul])
  obtain ⟨φ⟩ := spin_iso h1ne hK
  refine ⟨⟨↥(ℝ ∙ (1 : F))ᗮ⟩, fun hKfin => hfin ?_, ⟨φ⟩⟩
  have : FiniteDimensional ℝ ↥(ℝ ∙ (1 : F))ᗮ := hKfin
  exact LinearEquiv.finiteDimensional
    (φ.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (↥(ℝ ∙ (1 : F))ᗮ × ℝ))).symm

/-- **EJA 54** (`appendixjnw`, main.tex:1292, Corollary), **unconditionally**: every EJA is
isomorphic to `E_fin ⊕ E_inf`, with `E_fin` a finite-dimensional EJA and `E_inf` a finite
direct sum of spin factors of infinite-dimensional Hilbert spaces.  `appendixjnw` with its
hypothesis `HOSClassification` discharged by `hosClassification`. -/
theorem appendixjnw_uncond :
    ∃ Ef : EJABundle.{u}, FiniteDimensional ℝ Ef.carrier ∧
      ∃ (ι : Type u) (_ : Fintype ι) (H : ι → HilbBundle.{u}),
        (∀ i, ¬ FiniteDimensional ℝ (H i).carrier) ∧
        Nonempty (EJAIso E (EJASum Ef.carrier (EJAPi fun i => SpinFactor (H i).carrier))) :=
  appendixjnw hosClassification

end Jordan

end Papers.EJA.Classification
