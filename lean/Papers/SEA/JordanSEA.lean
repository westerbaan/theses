/-
Papers/SEA/JordanSEA.lean

**SEA 16** (`ex:canonical-sea`, second.tex:475), the Jordan sentence: "any
JB-algebra is a convex SEA, while any JBW-algebra is a convex normal SEA"
(product `a ∘ b = U_{√a} b`, cited from van de Wetering 2019).

Plan and scope (2026-09-26).
* The hard axioms are S4/S5: they need van de Wetering's theorem that
  `U_{√a} b = U_{√b} a` iff `a`, `b` operator-commute, and that the elements
  commuting with `c` form a subalgebra closed under `U_{√·}`; S6 needs `U_{√a}`
  to preserve directed suprema and the commutant of `a` to be closed under them.
* General JB/JBW: `Papers.REC.Algebras` has only the *definitions*
  (`JBAlgebra`, `JBWAlgebra`); there is no functional calculus (square roots),
  no Macdonald/Shirshov–Cohn, no Peirce theory for them.  Supplying that is far
  beyond ~2,500 lines, so the general case is left open.
* Done here, in full: the **finite-dimensional** case — a Euclidean Jordan
  algebra in the tree's sense (`EuclideanJordanAlgebra`; every
  finite-dimensional JB-algebra is one, and it is a JBW-algebra), using the
  spectral theorem, Peirce rules, trace form and frames of `Theses.B.Eff` and
  `Papers.EJA`.  `[0,1]_V` with `a ∘ b = U_{√a} b` is a convex normal SEA
  (`ejaNormalSEA`, `sea16_eja`).
* The commutation theorem, finite-dimensional and Jordan-native (no reduction
  to C*-algebras): with `b = ∑ λ_l e_l` spectral,
  `⟨b a, a⟩ − ⟨U_{√b} a, a⟩ = ∑_{l ≠ k} 4 (√λ_l − √λ_k)² ‖e_l (e_k a)‖²`
  (`sub_U_expand`, `ejaB_orth_idem`), while `U_{√a} b = U_{√b} a` makes the
  left side `⟨b, a²⟩ − ⟨b, a²⟩ = 0`.  So commuting forces `e_l (e_k a) = 0`
  (`inD_of_comm`); the set `D_e` of such `a` is a unital subalgebra closed under
  spectral idempotents and square roots (`inD_mul`, `inD_spectral`,
  `inD_sqrt`); and `a ∈ D_e` gives a common refining frame (`comp_of_inD`), on
  which everything is diagonal (`frame_seq`, `frame_assoc`).  Conversely a common
  frame gives commutation.  Hence `seq_comm_iff`: `a ∘ b = b ∘ a` iff `a`, `b`
  are combinations of one frame.
* Normality: a bounded directed set has a supremum that is its weak limit for
  the trace form (the argument of EJA 51, `dirSup_weak`, Riesz by
  `eja_exists_riesz`); `U_{√a}` is trace-self-adjoint, and `D_e` is weakly
  closed.
-/
import Papers.SEA.Basic
import Papers.EJA.Pure

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace Papers.SEA.Jordan

open Theses.B.Eff Theses.B.Eff.EuclideanJordanAlgebra Papers.EJA Filter Topology Polynomial

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- `U_{√b} b = b²` (as `Papers.EJA.ejaU_sqrt_self`, which lives in a heavier file). -/
theorem ejaU_sqrt_self_eja {b : V} (hb : 0 ≤ b) : ejaU (ejaSqrt b) b = b * b := by
  obtain ⟨_, hss⟩ := ejaSqrt_spec hb
  have h : ejaU (ejaSqrt b) b = ejaU (ejaSqrt b) (ejaU (ejaSqrt b) 1) := by
    rw [ejaU_apply_one, hss]
  rw [h, ← ejaU_mul_self, hss, ejaU_apply_one]

/-! ## Orthogonal idempotents and the Peirce rules -/

/-- For orthogonal idempotents `q, r`: `q (r a) = ½ r P½(q) a`. -/
theorem orth_idem_half {q r : V} (hq : q * q = q) (hqr : q * r = 0) (a : V) :
    q * (r * a) = (2 : ℝ)⁻¹ • (r * ejaPhalf q a) := by
  have hs := eja_peirce_sum q a
  have h1 : ejaPone q a * r = 0 := eja_peirce_one_mul_zero hq (eja_mul_pone q hq a) hqr
  have h2 : q * (r * ejaPhalf q a) = (2 : ℝ)⁻¹ • (r * ejaPhalf q a) :=
    eja_peirce_zero_mul_half hq hqr (eja_mul_phalf q hq a)
  have h3 : q * (r * ejaPone (1 - q) a) = 0 := eja_peirce_zero_mul_zero hq hqr (eja_mul_pzero hq a)
  conv_lhs => rw [← hs]
  rw [eja_mul_add, eja_mul_add, eja_mul_add, eja_mul_add, eja_mul_comm r (ejaPone q a), h1, h2,
    h3, eja_mul_zero, zero_add, add_zero]

/-- For orthogonal idempotents `q, r`, `q (r a)` is in the Peirce `½`-space of `q`. -/
theorem orth_idem_sq {q r : V} (hq : q * q = q) (hqr : q * r = 0) (a : V) :
    q * (q * (r * a)) = (2 : ℝ)⁻¹ • (q * (r * a)) := by
  rw [orth_idem_half hq hqr a, eja_mul_smul,
    eja_peirce_zero_mul_half hq hqr (eja_mul_phalf q hq a)]

/-- For orthogonal idempotents `q, r` and `y = q (r a)`: `⟨y, a⟩ = 4 ⟨y, y⟩`. -/
theorem ejaB_orth_idem {q r : V} (hq : q * q = q) (hr : r * r = r) (hqr : q * r = 0) (a : V) :
    ejaB (q * (r * a)) a = 4 * ejaB (q * (r * a)) (q * (r * a)) := by
  have hrq : r * q = 0 := by rw [eja_mul_comm]; exact hqr
  have hyq : q * (q * (r * a)) = (2 : ℝ)⁻¹ • (q * (r * a)) := orth_idem_sq hq hqr a
  have hyr' : q * (r * a) = r * (q * a) := eja_commute_of_peirce_zero hq hqr a
  have hyr : r * (q * (r * a)) = (2 : ℝ)⁻¹ • (q * (r * a)) := by
    rw [hyr']; exact orth_idem_sq hr hrq a
  have e1 : ejaB (q * (r * a)) a = 2 * ejaB (q * (r * a)) (q * a) := by
    have h : q * (r * a) = (2 : ℝ) • (q * (q * (r * a))) := by
      rw [hyq, smul_smul]; norm_num
    conv_lhs => rw [h]
    rw [ejaB_smul_left, ejaB_assoc]
  have e2 : ejaB (q * (r * a)) (q * a) = 2 * ejaB (q * (r * a)) (q * (r * a)) := by
    have h : q * (r * a) = (2 : ℝ) • (r * (q * (r * a))) := by
      rw [hyr, smul_smul]; norm_num
    conv_lhs => rw [h]
    rw [ejaB_smul_left, ejaB_assoc, ← hyr']
  rw [e1, e2]; ring

/-! ## Spectral frames and the diagonal subalgebra `D_e` -/

/-- A finite family of pairwise orthogonal idempotents summing to `1`, indexed
by a `Finset ℝ` (the shape `eja_spectral` produces). -/
structure SpecFrame (s : Finset ℝ) (e : ℝ → V) : Prop where
  idem : ∀ l ∈ s, e l * e l = e l
  orth : ∀ l ∈ s, ∀ k ∈ s, l ≠ k → e l * e k = 0
  sum_one : ∑ l ∈ s, e l = 1

/-- `D_e`: the elements with no off-diagonal Peirce part for the frame `e`
(equivalently, operator-commuting with every `e l`). -/
def InD (s : Finset ℝ) (e : ℝ → V) (y : V) : Prop :=
  ∀ l ∈ s, ∀ k ∈ s, l ≠ k → e l * (e k * y) = 0

namespace SpecFrame

variable {s : Finset ℝ} {e : ℝ → V} (F : SpecFrame s e)
include F

theorem sum_mul (y : V) : ∑ l ∈ s, e l * y = y := by
  rw [← eja_sum_mul, F.sum_one, eja_one_mul]

theorem mul_eq_sum (l : ℝ) (y : V) : e l * y = ∑ k ∈ s, e l * (e k * y) := by
  rw [← eja_mul_sum, F.sum_mul]

/-- An element of the Peirce `1`-space of `e k` is killed by `e l`, `l ≠ k`. -/
theorem zero_of_one {l k : ℝ} (hl : l ∈ s) (hk : k ∈ s) (hlk : l ≠ k) {w : V}
    (hw : e k * w = w) : e l * w = 0 := by
  have := eja_peirce_one_mul_zero (F.idem k hk) hw (F.orth k hk l hl (Ne.symm hlk))
  rw [eja_mul_comm]; exact this

theorem inD_fix {y : V} (hy : InD s e y) {l : ℝ} (hl : l ∈ s) : e l * (e l * y) = e l * y := by
  conv_rhs => rw [F.mul_eq_sum l y]
  rw [Finset.sum_eq_single_of_mem l hl]
  intro k hk hkl; exact hy l hl k hk (Ne.symm hkl)

omit F in
/-- `D_e` as a subspace. -/
def dSub' (s : Finset ℝ) (e : ℝ → V) : Submodule ℝ V where
  carrier := {y | InD s e y}
  add_mem' := by
    intro y z hy hz l hl k hk h
    rw [eja_mul_add, eja_mul_add, hy l hl k hk h, hz l hl k hk h, add_zero]
  zero_mem' := by
    intro l _ k _ _
    rw [eja_mul_zero, eja_mul_zero]
  smul_mem' := by
    intro r y hy l hl k hk h
    rw [eja_mul_smul, eja_mul_smul, hy l hl k hk h, smul_zero]


theorem inD_one : InD s e (1 : V) := by
  intro l hl k hk h
  rw [eja_mul_one, F.orth l hl k hk h]

/-- `D_e` is closed under products, and `y ↦ e l * y` is multiplicative on it. -/
theorem inD_mul {y z : V} (hy : InD s e y) (hz : InD s e z) :
    InD s e (y * z) ∧ ∀ l ∈ s, e l * (y * z) = (e l * y) * (e l * z) := by
  have hdec : y * z = ∑ k ∈ s, (e k * y) * (e k * z) := by
    conv_lhs => rw [← F.sum_mul y, ← F.sum_mul z]
    rw [eja_sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [eja_mul_sum, Finset.sum_eq_single_of_mem k hk]
    intro k' hk' hne
    exact eja_peirce_one_mul_zero (F.idem k hk) (F.inD_fix hy hk)
      (F.zero_of_one hk hk' (Ne.symm hne) (F.inD_fix hz hk'))
  have hw : ∀ k ∈ s, e k * ((e k * y) * (e k * z)) = (e k * y) * (e k * z) := fun k hk =>
    eja_peirce_one_mul_one (F.idem k hk) (F.inD_fix hy hk) (F.inD_fix hz hk)
  have hcomp : ∀ l ∈ s, e l * (y * z) = (e l * y) * (e l * z) := by
    intro l hl
    rw [hdec, eja_mul_sum, Finset.sum_eq_single_of_mem l hl, hw l hl]
    intro k hk hkl
    exact F.zero_of_one hl hk (Ne.symm hkl) (hw k hk)
  refine ⟨fun l hl k hk h => ?_, hcomp⟩
  rw [hcomp k hk]
  exact F.zero_of_one hl hk h (hw k hk)

theorem inD_pow {y : V} (hy : InD s e y) (n : ℕ) : InD s e (ejaPow y n) := by
  induction n with
  | zero => exact F.inD_one
  | succ n ih => exact (F.inD_mul hy ih).1

theorem inD_ejaEv {y : V} (hy : InD s e y) (P : ℝ[X]) : InD s e (ejaEv y P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add]; exact (SpecFrame.dSub' s e).add_mem hP hQ
  | monomial n a => rw [ejaEv_monomial]; exact (SpecFrame.dSub' s e).smul_mem a (F.inD_pow hy n)

/-- The spectral idempotents of an element of `D_e` are in `D_e` (they are
polynomials in it). -/
theorem inD_spectral {y : V} (hy : InD s e y) {t : Finset ℝ} {f : ℝ → V} (G : SpecFrame t f)
    (hdec : y = ∑ m ∈ t, m • f m) {m : ℝ} (hm : m ∈ t) : InD s e (f m) := by
  have h := ejaEv_ortho G.idem G.orth G.sum_one (fun l => l) (Lagrange.basis t id m)
  rw [← hdec, Finset.sum_eq_single_of_mem m hm] at h
  · have h1 : (Lagrange.basis t id m).eval m = 1 :=
      Lagrange.eval_basis_self (v := id) (Set.injOn_id _) hm
    rw [h1, one_smul] at h
    rw [← h]; exact F.inD_ejaEv hy _
  · intro k hk hkm
    have h0 : (Lagrange.basis t id m).eval k = 0 :=
      Lagrange.eval_basis_of_ne (v := id) (Ne.symm hkm) hk
    rw [h0, zero_smul]

end SpecFrame

/-- The data of `eja_spectral` as a `SpecFrame`. -/
theorem spectral_frame (x : V) : ∃ (s : Finset ℝ) (e : ℝ → V), SpecFrame s e ∧
    (∀ l ∈ s, e l ≠ 0) ∧ x = ∑ l ∈ s, l • e l := by
  obtain ⟨s, e, hidem, horth, hne0, hsum, hdec⟩ := eja_spectral x
  exact ⟨s, e, ⟨hidem, horth, hsum⟩, hne0, hdec⟩

/-- Spectral values of a positive element are non-negative. -/
theorem spectral_nonneg {x : V} (hx : 0 ≤ x) {s : Finset ℝ} {e : ℝ → V} (F : SpecFrame s e)
    (hne0 : ∀ l ∈ s, e l ≠ 0) (hdec : x = ∑ l ∈ s, l • e l) : ∀ l ∈ s, 0 ≤ l := by
  refine (eja_ortho_isSumSq_iff F.idem F.orth hne0 (fun r => r)).mp ?_
  rw [← hdec]; exact (eja_nonneg_iff x).mp hx

/-- `√x = ∑ √λ_l e_l` for a spectral decomposition of `x ≥ 0`. -/
theorem sqrt_spectral {x : V} (hx : 0 ≤ x) {s : Finset ℝ} {e : ℝ → V} (F : SpecFrame s e)
    (hne0 : ∀ l ∈ s, e l ≠ 0) (hdec : x = ∑ l ∈ s, l • e l) :
    ejaSqrt x = ∑ l ∈ s, Real.sqrt l • e l := by
  have hl := spectral_nonneg hx F hne0 hdec
  refine ejaSqrt_unique ?_ ?_
  · rw [eja_nonneg_iff, eja_ortho_isSumSq_iff F.idem F.orth hne0 (fun l => Real.sqrt l)]
    exact fun l _ => Real.sqrt_nonneg l
  · rw [eja_ortho_mul F.idem F.orth, hdec]
    exact Finset.sum_congr rfl fun l hl' => by rw [Real.mul_self_sqrt (hl l hl')]

theorem SpecFrame.inD_sqrt {s : Finset ℝ} {e : ℝ → V} (F : SpecFrame s e) {y : V} (hy0 : 0 ≤ y)
    (hy : InD s e y) : InD s e (ejaSqrt y) := by
  obtain ⟨t, f, G, hne0, hdec⟩ := spectral_frame y
  rw [sqrt_spectral hy0 G hne0 hdec]
  refine (SpecFrame.dSub' s e).sum_mem fun m hm => (SpecFrame.dSub' s e).smul_mem _ ?_
  exact F.inD_spectral hy G hdec hm

theorem SpecFrame.inD_U {s : Finset ℝ} {e : ℝ → V} (F : SpecFrame s e) {a b : V} (ha0 : 0 ≤ a)
    (ha : InD s e a) (hb : InD s e b) : InD s e (ejaU (ejaSqrt a) b) := by
  have hs := F.inD_sqrt ha0 ha
  rw [ejaU_apply]
  refine (SpecFrame.dSub' s e).sub_mem ((SpecFrame.dSub' s e).smul_mem _ ?_) ?_
  · exact (F.inD_mul hs (F.inD_mul hs hb).1).1
  · exact (F.inD_mul (F.inD_mul hs hs).1 hb).1

/-! ## Frames: the diagonal calculus -/

/-- `a` and `b` are **compatible**: combinations of one frame. -/
def Comp (a b : V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (g : ι → V), IsOrthFrame g ∧
    (∃ c : ι → ℝ, a = ∑ i, c i • g i) ∧ ∃ d : ι → ℝ, b = ∑ i, d i • g i

section FrameCalc

variable {ι : Type} [Fintype ι] {g : ι → V}

theorem frame_coeff_nonneg' (hg : IsOrthFrame g) {c : ι → ℝ} (h : 0 ≤ ∑ i, c i • g i) (i : ι)
    (hi : g i ≠ 0) : 0 ≤ c i := by
  have h1 := eja_isSumSq_ejaB_idem_nonneg ((eja_nonneg_iff _).mp h) (g i) (hg.idem i)
  have h2 : ejaB (∑ j, c j • g j) (g i) = ejaB (c i • g i) (g i) := by
    show ejaTrL (_ * _) = ejaTrL (_ * _)
    rw [frame_mul_elt hg, eja_smul_mul, hg.idem]
  rw [h2, ejaB_smul_left] at h1
  exact nonneg_of_mul_nonneg_left h1 (ejaB_self_pos hi)

/-- A positive frame combination has a representation with non-negative
coefficients. -/
theorem frame_pos_rep (hg : IsOrthFrame g) {c : ι → ℝ} (h : 0 ≤ ∑ i, c i • g i) :
    ∑ i, c i • g i = ∑ i, max (c i) 0 • g i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : g i = 0
  · rw [hi, smul_zero, smul_zero]
  · rw [max_eq_left (frame_coeff_nonneg' hg h i hi)]

theorem frame_sqrt (hg : IsOrthFrame g) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    ejaSqrt (∑ i, c i • g i) = ∑ i, Real.sqrt (c i) • g i := by
  refine ejaSqrt_unique (frame_nonneg hg fun i => Real.sqrt_nonneg _) ?_
  rw [frame_mul hg]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.mul_self_sqrt (hc i)]

theorem frame_U (hg : IsOrthFrame g) (c d : ι → ℝ) :
    ejaU (∑ i, c i • g i) (∑ i, d i • g i) = ∑ i, (c i * c i * d i) • g i := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, frame_U_elt hg, smul_smul, mul_comm (d i)]

theorem frame_seq (hg : IsOrthFrame g) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (d : ι → ℝ) :
    ejaU (ejaSqrt (∑ i, c i • g i)) (∑ i, d i • g i) = ∑ i, (c i * d i) • g i := by
  rw [frame_sqrt hg hc, frame_U hg]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.mul_self_sqrt (hc i)]

theorem frame_assoc (hg : IsOrthFrame g) {c d : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i)
    (x : V) :
    ejaU (ejaSqrt (ejaU (ejaSqrt (∑ i, c i • g i)) (∑ i, d i • g i))) x =
      ejaU (ejaSqrt (∑ i, c i • g i)) (ejaU (ejaSqrt (∑ i, d i • g i)) x) := by
  rw [frame_seq hg hc, frame_sqrt hg (fun i => mul_nonneg (hc i) (hd i)), frame_sqrt hg hc,
    frame_sqrt hg hd, frame_U_comp hg]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by rw [Real.sqrt_mul (hc i)]

end FrameCalc

/-- Compatible positive elements have a common frame with non-negative
coefficients. -/
theorem Comp.pos {a b : V} (h : Comp a b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → V), IsOrthFrame g ∧ ∃ c d : ι → ℝ,
      (∀ i, 0 ≤ c i) ∧ (∀ i, 0 ≤ d i) ∧ a = ∑ i, c i • g i ∧ b = ∑ i, d i • g i := by
  obtain ⟨ι, _, g, hg, ⟨c, rfl⟩, ⟨d, rfl⟩⟩ := h
  exact ⟨ι, inferInstance, g, hg, fun i => max (c i) 0, fun i => max (d i) 0,
    fun i => le_max_right _ _, fun i => le_max_right _ _, frame_pos_rep hg ha, frame_pos_rep hg hb⟩

/-- Compatible positive elements commute sequentially. -/
theorem Comp.comm {a b : V} (h : Comp a b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ejaU (ejaSqrt a) b = ejaU (ejaSqrt b) a := by
  obtain ⟨ι, _, g, hg, c, d, hc, hd, rfl, rfl⟩ := h.pos ha hb
  rw [frame_seq hg hc, frame_seq hg hd]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

theorem Comp.assoc {a b : V} (h : Comp a b) (ha : 0 ≤ a) (hb : 0 ≤ b) (x : V) :
    ejaU (ejaSqrt (ejaU (ejaSqrt a) b)) x = ejaU (ejaSqrt a) (ejaU (ejaSqrt b) x) := by
  obtain ⟨ι, _, g, hg, c, d, hc, hd, rfl, rfl⟩ := h.pos ha hb
  exact frame_assoc hg hc hd x

/-- **The refinement**: an element of `D_e` is compatible with every
combination of the frame `e`. -/
theorem SpecFrame.comp_of_inD {s : Finset ℝ} {e : ℝ → V} (F : SpecFrame s e) (β : ℝ → ℝ)
    {y : V} (hy : InD s e y) : Comp (∑ l ∈ s, β l • e l) y := by
  obtain ⟨t, f, G, _, hdec⟩ := spectral_frame y
  have hf : ∀ m ∈ t, InD s e (f m) := fun m hm => F.inD_spectral hy G hdec hm
  have hfix : ∀ l ∈ s, ∀ m ∈ t, e l * (e l * f m) = e l * f m := fun l hl m hm =>
    F.inD_fix (hf m hm) hl
  let ι : Type := ↥(s ×ˢ t)
  let g : ι → V := fun x => e x.1.1 * f x.1.2
  have hmem : ∀ x : ι, x.1.1 ∈ s ∧ x.1.2 ∈ t := fun x => Finset.mem_product.mp x.2
  have hS : ∀ Φ : ℝ × ℝ → V, ∑ x : ι, Φ x.1 = ∑ l ∈ s, ∑ m ∈ t, Φ (l, m) := fun Φ => by
    rw [Finset.sum_coe_sort (s ×ˢ t) Φ, Finset.sum_product]
  have hg : IsOrthFrame g := by
    refine ⟨fun x => ?_, fun x x' hxx' => ?_, ?_⟩
    · obtain ⟨hl, hm⟩ := hmem x
      show (e x.1.1 * f x.1.2) * (e x.1.1 * f x.1.2) = e x.1.1 * f x.1.2
      rw [← ((F.inD_mul (hf _ hm) (hf _ hm)).2 _ hl), G.idem _ hm]
    · obtain ⟨hl, hm⟩ := hmem x
      obtain ⟨hl', hm'⟩ := hmem x'
      show (e x.1.1 * f x.1.2) * (e x'.1.1 * f x'.1.2) = 0
      by_cases hll : x.1.1 = x'.1.1
      · have hmm : x.1.2 ≠ x'.1.2 := by
          intro h; exact hxx' (Subtype.ext (Prod.ext hll h))
        rw [← hll, ← ((F.inD_mul (hf _ hm) (hf _ hm')).2 _ hl), G.orth _ hm _ hm' hmm,
          eja_mul_zero]
      · exact eja_peirce_one_mul_zero (F.idem _ hl) (hfix _ hl _ hm)
          (F.zero_of_one hl hl' hll (hfix _ hl' _ hm'))
    · rw [hS (fun p => e p.1 * f p.2)]
      simp only
      rw [← F.sum_one]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← eja_mul_sum, G.sum_one, eja_mul_one]
  refine ⟨ι, inferInstance, g, hg, ⟨fun x => β x.1.1, ?_⟩, ⟨fun x => x.1.2, ?_⟩⟩
  · rw [hS (fun p => β p.1 • (e p.1 * f p.2))]
    refine Finset.sum_congr rfl fun l _ => ?_
    dsimp only
    rw [← Finset.smul_sum, ← eja_mul_sum, G.sum_one, eja_mul_one]
  · rw [hS (fun p => p.2 • (e p.1 * f p.2)), Finset.sum_comm]
    conv_lhs => rw [hdec]
    refine Finset.sum_congr rfl fun m _ => ?_
    dsimp only
    rw [← Finset.smul_sum, F.sum_mul]

/-! ## The commutation theorem -/

/-- The expansion `b a − U_{√b} a = ∑_{l,k} (√λ_l − √λ_k)² e_l (e_k a)`. -/
theorem sub_U_expand {c : V} (hc : 0 ≤ c) {s : Finset ℝ} {e : ℝ → V} (F : SpecFrame s e)
    (hne0 : ∀ l ∈ s, e l ≠ 0) (hdec : c = ∑ l ∈ s, l • e l) (y : V) :
    c * y - ejaU (ejaSqrt c) y =
      ∑ l ∈ s, ∑ k ∈ s, ((Real.sqrt l - Real.sqrt k) ^ 2) • (e l * (e k * y)) := by
  have hl := spectral_nonneg hc F hne0 hdec
  have hsq := sqrt_spectral hc F hne0 hdec
  have hss : ejaSqrt c * ejaSqrt c = c := (ejaSqrt_spec hc).2
  have hX : ejaSqrt c * (ejaSqrt c * y) =
      ∑ l ∈ s, ∑ k ∈ s, (Real.sqrt l * Real.sqrt k) • (e l * (e k * y)) := by
    rw [hsq]
    simp only [eja_sum_mul, eja_mul_sum, eja_smul_mul, eja_mul_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]
  have hc1 : c * y = ∑ l ∈ s, ∑ k ∈ s, l • (e l * (e k * y)) := by
    conv_lhs => rw [hdec]
    rw [eja_sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [eja_smul_mul, F.mul_eq_sum l y, Finset.smul_sum]
  have hc2 : c * y = ∑ l ∈ s, ∑ k ∈ s, k • (e l * (e k * y)) := by
    rw [Finset.sum_comm]
    conv_lhs => rw [hdec]
    rw [eja_sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.smul_sum, F.sum_mul, eja_smul_mul]
  have key : ∀ l ∈ s, ∀ k ∈ s, ((Real.sqrt l - Real.sqrt k) ^ 2) • (e l * (e k * y)) =
      l • (e l * (e k * y)) + k • (e l * (e k * y)) -
        (2 : ℝ) • ((Real.sqrt l * Real.sqrt k) • (e l * (e k * y))) := by
    intro l hl' k hk'
    rw [smul_smul, ← add_smul, ← sub_smul]
    congr 1
    have h1 := Real.sq_sqrt (hl l hl')
    have h2 := Real.sq_sqrt (hl k hk')
    nlinarith [h1, h2]
  have h2X : ∑ l ∈ s, ∑ k ∈ s, (2 : ℝ) • ((Real.sqrt l * Real.sqrt k) • (e l * (e k * y))) =
      (2 : ℝ) • (ejaSqrt c * (ejaSqrt c * y)) := by
    rw [hX, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [Finset.smul_sum]
  rw [Finset.sum_congr rfl fun l hl' => Finset.sum_congr rfl fun k hk' => key l hl' k hk']
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h2X, ← hc1, ← hc2, ejaU_apply, hss]
  module

/-- **Sequential commutation forces the diagonal form**: if
`U_{√c} y = U_{√y} c` for positive `c, y` and `c = ∑ λ_l e_l` is spectral,
then `y ∈ D_e`. -/
theorem inD_of_comm {c y : V} (hc : 0 ≤ c) (hy : 0 ≤ y) {s : Finset ℝ} {e : ℝ → V}
    (F : SpecFrame s e) (hne0 : ∀ l ∈ s, e l ≠ 0) (hdec : c = ∑ l ∈ s, l • e l)
    (h : ejaU (ejaSqrt c) y = ejaU (ejaSqrt y) c) : InD s e y := by
  have hl := spectral_nonneg hc F hne0 hdec
  have hΦ : ejaB (c * y - ejaU (ejaSqrt c) y) y = 0 := by
    rw [ejaB_sub_left, h, ← ejaB_U_self_adj, ejaU_sqrt_self_eja hy, eja_mul_comm c y,
      ejaB_assoc]
    ring
  rw [sub_U_expand hc F hne0 hdec, ejaB_sum_left] at hΦ
  simp only [ejaB_sum_left, ejaB_smul_left] at hΦ
  have hterm : ∀ l ∈ s, ∀ k ∈ s, 0 ≤ (Real.sqrt l - Real.sqrt k) ^ 2 * ejaB (e l * (e k * y)) y
      := by
    intro l hl' k hk'
    by_cases hlk : l = k
    · rw [hlk, sub_self]; simp
    · rw [ejaB_orth_idem (F.idem l hl') (F.idem k hk') (F.orth l hl' k hk' hlk)]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (ejaB_self_nonneg _))
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun l hl' =>
    Finset.sum_nonneg fun k hk' => hterm l hl' k hk').mp hΦ
  intro l hl' k hk' hlk
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun k hk' => hterm l hl' k hk').mp (h1 l hl') k hk'
  rw [ejaB_orth_idem (F.idem l hl') (F.idem k hk') (F.orth l hl' k hk' hlk)] at h2
  have hne : (Real.sqrt l - Real.sqrt k) ^ 2 ≠ 0 := by
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => hlk ?_)
    exact (Real.sqrt_inj (hl l hl') (hl k hk')).mp h
  have h3 : ejaB (e l * (e k * y)) (e l * (e k * y)) = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hne
    · linarith
  exact eja_eq_zero_of_ejaB_self h3

/-- The converse: `D_e` commutes with `c = ∑ λ_l e_l`. -/
theorem comm_of_inD {c y : V} (hc : 0 ≤ c) (hy : 0 ≤ y) {s : Finset ℝ} {e : ℝ → V}
    (F : SpecFrame s e) (hdec : c = ∑ l ∈ s, l • e l) (hyD : InD s e y) :
    ejaU (ejaSqrt c) y = ejaU (ejaSqrt y) c := by
  have h := F.comp_of_inD (fun l => l) hyD
  rw [← hdec] at h
  exact h.comm hc hy

/-- **The commutation theorem** (finite-dimensional case of van de Wetering's):
for positive `a, b`, `U_{√a} b = U_{√b} a` iff `a` and `b` are combinations of
one frame of orthogonal idempotents. -/
theorem seq_comm_iff {a b : V} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ejaU (ejaSqrt a) b = ejaU (ejaSqrt b) a ↔ Comp a b := by
  refine ⟨fun h => ?_, fun h => h.comm ha hb⟩
  obtain ⟨s, e, F, hne0, hdec⟩ := spectral_frame a
  have hD := inD_of_comm ha hb F hne0 hdec h
  have := F.comp_of_inD (fun l => l) hD
  rwa [← hdec] at this

/-! ## The axioms S3–S5 on `[0,1]_V` -/

/-- `a` and `b` commute sequentially: `U_{√a} b = U_{√b} a`. -/
def Cm (a b : V) : Prop := ejaU (ejaSqrt a) b = ejaU (ejaSqrt b) a

theorem ejaB_zero_left' (b : V) : ejaB (0 : V) b = 0 := by simp [ejaB, eja_zero_mul]

/-- S3 on `[0,1]_V`. -/
theorem seq_zero_comm_V {a b : V} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ejaU (ejaSqrt a) b = 0) :
    ejaU (ejaSqrt b) a = 0 := by
  have hba : ejaB b a = 0 := by
    have h1 : ejaB (ejaU (ejaSqrt a) b) 1 = ejaB b (ejaU (ejaSqrt a) 1) :=
      (ejaB_U_self_adj _ _ _).symm
    rw [h, ejaB_zero_left', ejaU_apply_one, (ejaSqrt_spec ha).2] at h1
    exact h1.symm
  have h2 : ejaB (1 : V) (ejaU (ejaSqrt b) a) = 0 := by
    rw [ejaB_U_self_adj, ejaU_apply_one, (ejaSqrt_spec hb).2, hba]
  have h3 := eja_idem_mul_nonneg_eq_zero (eja_one_mul (1 : V)) (eja_U_nonneg' _ ha) h2
  rwa [eja_one_mul] at h3

/-- S4, first half: `a | b` implies `a | 1 − b`. -/
theorem comm_orth_V {a b : V} (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (h : Cm a b) :
    Cm a (1 - b) := by
  obtain ⟨s, e, F, hne0, hdec⟩ := spectral_frame a
  have hD := inD_of_comm ha hb0 F hne0 hdec h
  exact comm_of_inD ha (eja_sub_nonneg.mpr hb1) F hdec
    ((SpecFrame.dSub' s e).sub_mem F.inD_one hD)

/-- S4, second half: `a | b` implies `a ∘ (b ∘ x) = (a ∘ b) ∘ x`. -/
theorem comm_assoc_V {a b : V} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Cm a b) (x : V) :
    ejaU (ejaSqrt (ejaU (ejaSqrt a) b)) x = ejaU (ejaSqrt a) (ejaU (ejaSqrt b) x) :=
  ((seq_comm_iff ha hb).mp h).assoc ha hb x

/-- S5: `c | a` and `c | b` imply `c | a ∘ b` and `c | a + b` (no summability
needed for either). -/
theorem comm_compat_V {a b c : V} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hca : Cm c a)
    (hcb : Cm c b) : Cm c (ejaU (ejaSqrt a) b) ∧ Cm c (a + b) := by
  obtain ⟨s, e, F, hne0, hdec⟩ := spectral_frame c
  have hA := inD_of_comm hc ha F hne0 hdec hca
  have hB := inD_of_comm hc hb F hne0 hdec hcb
  have hab : (0 : V) ≤ a + b := by
    rw [eja_nonneg_iff] at ha hb ⊢; exact IsSumSq.add ha hb
  exact ⟨comm_of_inD hc (eja_U_nonneg' _ hb) F hdec (F.inD_U ha hA hB),
    comm_of_inD hc hab F hdec ((SpecFrame.dSub' s e).add_mem hA hB)⟩

/-! ## Bounded directed sets: suprema are weak limits (the argument of EJA 51) -/

theorem ejaB_nonneg_nonneg {x y : V} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ ejaB x y :=
  (EJAForm.trace (V := V)).nonneg_nonneg hx hy

theorem nonneg_of_ejaB {x : V} (h : ∀ b : V, 0 ≤ b → 0 ≤ ejaB x b) : 0 ≤ x :=
  ((EJAForm.trace (V := V)).selfDual x).mpr h

/-- A non-empty bounded directed set `D` has a least upper bound `a`, and
`⟨d, b⟩ → ⟨a, b⟩` along `D`; recorded as the two consequences used below. -/
theorem dirSup_weak (D : Set V) (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (c : V)
    (hc : ∀ d ∈ D, d ≤ c) :
    ∃ a : V, IsLUB D a ∧ (∀ b r, (∀ d ∈ D, ejaB d b = r) → ejaB a b = r) ∧
      (∀ b, 0 ≤ b → ∀ r, (∀ d ∈ D, ejaB d b ≤ r) → ejaB a b ≤ r) := by
  have : Nonempty D := hne.to_subtype
  have : IsDirectedOrder D := ⟨fun i j => by
    obtain ⟨k, hk, hik, hjk⟩ := hdir i i.2 j j.2
    exact ⟨⟨k, hk⟩, hik, hjk⟩⟩
  let f : V → D → ℝ := fun b i => ejaB (i : V) b
  have hmono : ∀ b, 0 ≤ b → Monotone (f b) := by
    intro b hb i j hij
    have h := ejaB_nonneg_nonneg (eja_sub_nonneg.mpr (show (i : V) ≤ j from hij)) hb
    rw [ejaB_sub_left] at h
    show ejaB (i : V) b ≤ ejaB (j : V) b
    linarith
  have hub : ∀ b, 0 ≤ b → ∀ i : D, f b i ≤ ejaB c b := by
    intro b hb i
    have h := ejaB_nonneg_nonneg (eja_sub_nonneg.mpr (hc i i.2)) hb
    rw [ejaB_sub_left] at h
    show ejaB (i : V) b ≤ ejaB c b
    linarith
  have hpos : ∀ b, 0 ≤ b → ∃ L, Tendsto (f b) atTop (𝓝 L) := fun b hb =>
    ⟨_, tendsto_atTop_ciSup (hmono b hb) ⟨ejaB c b, by rintro _ ⟨i, rfl⟩; exact hub b hb i⟩⟩
  have hconv : ∀ b, ∃ L, Tendsto (f b) atTop (𝓝 L) := by
    intro b
    obtain ⟨n, hn⟩ := eja_exists_isSumSq_nsmul_one_sub (-b)
    have h1 : (0 : V) ≤ (n : ℝ) • (1 : V) - -b := (eja_nonneg_iff _).mpr hn
    have h2 : (0 : V) ≤ (n : ℝ) • (1 : V) :=
      (eja_nonneg_iff _).mpr (eja_isSumSq_smul_one (Nat.cast_nonneg n))
    obtain ⟨L1, hL1⟩ := hpos _ h1
    obtain ⟨L2, hL2⟩ := hpos _ h2
    refine ⟨L1 - L2, ?_⟩
    have := hL1.sub hL2
    convert this using 1
    funext i
    simp only [f, ← ejaB_sub_right]
    congr 1; abel
  choose L hL using hconv
  have hadd : ∀ b b', L (b + b') = L b + L b' := by
    intro b b'
    refine tendsto_nhds_unique (hL (b + b')) ?_
    have := (hL b).add (hL b')
    convert this using 1
    funext i; simp only [f, ejaB_add_right]
  have hsmul : ∀ (r : ℝ) b, L (r • b) = r * L b := by
    intro r b
    refine tendsto_nhds_unique (hL (r • b)) ?_
    have := (hL b).const_mul r
    convert this using 1
    funext i; simp only [f, ejaB_smul_right]
  let φ : V →ₗ[ℝ] ℝ :=
    { toFun := L, map_add' := hadd, map_smul' := fun r b => by simp [hsmul, smul_eq_mul] }
  obtain ⟨w, hw⟩ := eja_exists_riesz φ
  have hwL : ∀ b, ejaB w b = L b := fun b => (hw b).symm
  refine ⟨w, ⟨fun i hi => ?_, fun u hu => ?_⟩, fun b r h => ?_, fun b hb r h => ?_⟩
  · refine eja_sub_nonneg.mp (nonneg_of_ejaB fun b hb => ?_)
    rw [ejaB_sub_left, hwL]
    have := (hmono b hb).ge_of_tendsto (hL b) ⟨i, hi⟩
    exact sub_nonneg.mpr this
  · refine eja_sub_nonneg.mp (nonneg_of_ejaB fun b hb => ?_)
    rw [ejaB_sub_left, hwL]
    have : L b ≤ ejaB u b := le_of_tendsto' (hL b) fun i => by
      have h := ejaB_nonneg_nonneg (eja_sub_nonneg.mpr (hu i.2)) hb
      rw [ejaB_sub_left] at h
      show ejaB (i : V) b ≤ ejaB u b
      linarith
    exact sub_nonneg.mpr this
  · rw [hwL]
    refine tendsto_nhds_unique (hL b) ?_
    have : f b = fun _ => r := funext fun i => h i i.2
    rw [this]; exact tendsto_const_nhds
  · rw [hwL]; exact le_of_tendsto' (hL b) fun i => h i i.2

/-- The same for a directed subset of `[0,1]_V`. -/
theorem exists_sup_Icc (S : Set (Set.Icc (0 : V) 1)) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, (a : V) ≤ c ∧ (b : V) ≤ c) :
    ∃ x : Set.Icc (0 : V) 1, (∀ s ∈ S, (s : V) ≤ x) ∧
      (∀ u : V, (∀ s ∈ S, (s : V) ≤ u) → (x : V) ≤ u) ∧
      (∀ b r, (∀ s ∈ S, ejaB (s : V) b = r) → ejaB (x : V) b = r) ∧
      (∀ b, 0 ≤ b → ∀ r, (∀ s ∈ S, ejaB (s : V) b ≤ r) → ejaB (x : V) b ≤ r) := by
  obtain ⟨a, hlub, hw1, hw2⟩ := dirSup_weak (Subtype.val '' S) (hne.image _)
    (by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨r, hr, h1, h2⟩ := hdir p hp q hq
      exact ⟨r, ⟨r, hr, rfl⟩, h1, h2⟩)
    1 (by rintro _ ⟨s, _, rfl⟩; exact s.2.2)
  obtain ⟨s0, hs0⟩ := hne
  have h0 : (0 : V) ≤ a := le_trans s0.2.1 (hlub.1 ⟨s0, hs0, rfl⟩)
  have h1 : a ≤ 1 := hlub.2 (by rintro _ ⟨s, _, rfl⟩; exact s.2.2)
  refine ⟨⟨a, h0, h1⟩, fun s hs => hlub.1 ⟨s, hs, rfl⟩,
    fun u hu => hlub.2 (by rintro _ ⟨s, hs, rfl⟩; exact hu s hs), fun b r h => ?_,
    fun b hb r h => ?_⟩
  · exact hw1 b r (by rintro _ ⟨s, hs, rfl⟩; exact h s hs)
  · exact hw2 b hb r (by rintro _ ⟨s, hs, rfl⟩; exact h s hs)

/-! ## `[0,1]_V` as a convex normal SEA -/

/-- The tree's order-unit-space structure of an EJA (local instance: it makes
`V` an ordered additive group, as `orderIntervalEffectAlgebra` needs). -/
noncomputable def ejaOUS : OrderUnitSpace V := toOrderUnitSpace V

attribute [local instance] ejaOUS

theorem eja_zero_le_one' : (0 : V) ≤ 1 := eja_idem_nonneg (eja_one_mul (1 : V))

theorem ejaSqrt_one' : ejaSqrt (1 : V) = 1 := ejaSqrt_unique eja_zero_le_one' (eja_one_mul 1)

variable (V) in
/-- `[0,1]_V` with the effect algebra structure of SEA 4 (`u = 1`). -/
@[instance_reducible] noncomputable def ejaEA : EffectAlgebra (Set.Icc (0 : V) 1) :=
  orderIntervalEffectAlgebra V 1 eja_zero_le_one'

/-- The Jordan sequential product `a ∘ b = U_{√a} b` on `[0,1]_V`. -/
noncomputable def jseq (a b : Set.Icc (0 : V) 1) : Set.Icc (0 : V) 1 :=
  ⟨ejaU (ejaSqrt (a : V)) b, eja_U_nonneg' _ b.2.1, le_trans (eja_U_mono _ b.2.2)
    (by rw [ejaU_apply_one, (ejaSqrt_spec a.2.1).2]; exact a.2.2)⟩

variable (V) in
/-- **SEA 16**, Jordan sentence, finite-dimensional case: `[0,1]_V` of a
Euclidean Jordan algebra is a SEA with `a ∘ b = U_{√a} b`. -/
@[instance_reducible] noncomputable def ejaSEA : @SEAlgebra (Set.Icc (0 : V) 1) (ejaEA V) := by
  letI := ejaEA V
  exact
  { seq := jseq
    seq_add := fun c {a b} h => by
      have hab : (a : V) + b ≤ 1 := h
      have hab0 : (0 : V) ≤ (a : V) + b := by
        have ha := a.2.1; have hb := b.2.1
        rw [eja_nonneg_iff] at ha hb ⊢; exact IsSumSq.add ha hb
      refine ⟨?_, Subtype.ext ?_⟩
      · show ejaU (ejaSqrt (c : V)) a + ejaU (ejaSqrt (c : V)) b ≤ 1
        rw [← map_add]; exact (jseq c ⟨_, hab0, hab⟩).2.2
      · show ejaU (ejaSqrt (c : V)) a + ejaU (ejaSqrt (c : V)) b =
          ejaU (ejaSqrt (c : V)) ((a : V) + b)
        rw [map_add]
    one_seq := fun a => Subtype.ext (by
      show ejaU (ejaSqrt (1 : V)) a = a
      rw [ejaSqrt_one', ejaU_one]; rfl)
    seq_zero_comm := fun a b h =>
      Subtype.ext (seq_zero_comm_V a.2.1 b.2.1 (congrArg Subtype.val h))
    seq_comm_orth := fun {a b} h =>
      Subtype.ext (comm_orth_V a.2.1 b.2.1 b.2.2 (congrArg Subtype.val h))
    seq_comm_assoc := fun {a b} h c =>
      Subtype.ext (comm_assoc_V a.2.1 b.2.1 (congrArg Subtype.val h) c)
    seq_comm_compat := fun {a b c} _ hca hcb =>
      ⟨Subtype.ext (comm_compat_V a.2.1 b.2.1 c.2.1 (congrArg Subtype.val hca)
          (congrArg Subtype.val hcb)).1,
        Subtype.ext (comm_compat_V a.2.1 b.2.1 c.2.1 (congrArg Subtype.val hca)
          (congrArg Subtype.val hcb)).2⟩
    seq_comm_seq := fun {a b c} hca hcb =>
      Subtype.ext (comm_compat_V a.2.1 b.2.1 c.2.1 (congrArg Subtype.val hca)
          (congrArg Subtype.val hcb)).1 }

/-- **SEA 16**: the product of `ejaSEA` is `a ∘ b = U_{√a} b`. -/
theorem sea16_eja_seq (a b : Set.Icc (0 : V) 1) :
    ((@SequentialEffectAlgebra.seq _ (ejaEA V) (ejaSEA V).toSequentialEffectAlgebra a b :
      Set.Icc (0 : V) 1) : V) = ejaU (ejaSqrt (a : V)) b := rfl

/-- **The commutation theorem in SEA terms**: `a ∘ b = b ∘ a` in `[0,1]_V` iff
`a` and `b` are combinations of one frame of orthogonal idempotents. -/
theorem sea16_eja_commutes_iff (a b : Set.Icc (0 : V) 1) :
    @Commutes _ (ejaEA V) (ejaSEA V) a b ↔ Comp (a : V) b := by
  rw [← seq_comm_iff a.2.1 b.2.1]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

variable (V) in
/-- **SEA 16**, Jordan sentence, finite-dimensional case: `[0,1]_V` is a
*normal* SEA with the same product. -/
@[instance_reducible] noncomputable def ejaNormalSEA :
    @NormalSEA (Set.Icc (0 : V) 1) (ejaEA V) := by
  letI := ejaEA V
  letI := ejaSEA V
  have hle_iff : ∀ x y : Set.Icc (0 : V) 1, x ≼ y ↔ (x : V) ≤ y :=
    interval_le_iff 1 eja_zero_le_one'
  have hdir : ∀ {S : Set (Set.Icc (0 : V) 1)}, EDirected S →
      ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, (a : V) ≤ c ∧ (b : V) ≤ c := by
    intro S hS a ha b hb
    obtain ⟨c, hc, h1, h2⟩ := hS.2 a ha b hb
    exact ⟨c, hc, (hle_iff _ _).mp h1, (hle_iff _ _).mp h2⟩
  have hsup : ∀ {S : Set (Set.Icc (0 : V) 1)} (hS : EDirected S) {x : Set.Icc (0 : V) 1},
      EIsSup S x → (∀ s ∈ S, (s : V) ≤ x) ∧
        (∀ b r, (∀ s ∈ S, ejaB (s : V) b = r) → ejaB (x : V) b = r) ∧
        (∀ b, 0 ≤ b → ∀ r, (∀ s ∈ S, ejaB (s : V) b ≤ r) → ejaB (x : V) b ≤ r) := by
    intro S hS x hx
    obtain ⟨x', h1, h2, h3, h4⟩ := exists_sup_Icc S hS.1 (hdir hS)
    have hx' : EIsSup S x' := ⟨fun s hs => (hle_iff _ _).mpr (h1 s hs),
      fun y hy => (hle_iff _ _).mpr (h2 y fun s hs => (hle_iff _ _).mp (hy s hs))⟩
    rw [hx.unique hx']
    exact ⟨h1, h3, h4⟩
  exact
  { ejaSEA V with
    directedComplete := fun S hS => by
      obtain ⟨x, h1, h2, _, _⟩ := exists_sup_Icc S hS.1 (hdir hS)
      exact ⟨x, fun s hs => (hle_iff _ _).mpr (h1 s hs),
        fun y hy => (hle_iff _ _).mpr (h2 y fun s hs => (hle_iff _ _).mp (hy s hs))⟩
    seq_sup := fun a {S x} hS hx => by
      obtain ⟨h1, _, h3⟩ := hsup hS hx
      refine ⟨?_, fun y hy => (hle_iff _ _).mpr ?_⟩
      · rintro _ ⟨s, hs, rfl⟩
        exact (hle_iff _ _).mpr (eja_U_mono _ (h1 s hs))
      · refine eja_sub_nonneg.mp (nonneg_of_ejaB fun b hb => ?_)
        rw [ejaB_sub_left]
        have : ejaB (ejaU (ejaSqrt (a : V)) x) b ≤ ejaB (y : V) b := by
          rw [← ejaB_U_self_adj]
          refine h3 _ (eja_U_nonneg' _ hb) _ fun s hs => ?_
          have hys : ejaU (ejaSqrt (a : V)) s ≤ y := (hle_iff _ _).mp (hy _ ⟨s, hs, rfl⟩)
          have h := ejaB_nonneg_nonneg (eja_sub_nonneg.mpr hys) hb
          rw [ejaB_sub_left, ← ejaB_U_self_adj] at h
          linarith
        show 0 ≤ ejaB (y : V) b - ejaB (ejaU (ejaSqrt (a : V)) x) b
        linarith
    comm_sup := fun a {S x} hS hx hcomm => by
      obtain ⟨_, h2, _⟩ := hsup hS hx
      obtain ⟨s, e, F, hne0, hdec⟩ := spectral_frame (a : V)
      have hD : ∀ p ∈ S, InD s e (p : V) := fun p hp =>
        inD_of_comm a.2.1 p.2.1 F hne0 hdec (congrArg Subtype.val (hcomm p hp))
      have hDx : InD s e (x : V) := by
        intro l hl k hk hlk
        have hz : ∀ b, ejaB (e l * (e k * (x : V))) b = 0 := by
          intro b
          rw [ejaB_assoc, ejaB_assoc]
          refine h2 _ 0 fun p hp => ?_
          rw [← ejaB_assoc, ← ejaB_assoc, hD p hp l hl k hk hlk, ejaB_zero_left']
        exact eja_eq_zero_of_ejaB_self (hz _)
      exact Subtype.ext (comm_of_inD a.2.1 x.2.1 F hdec hDx) }

/-- `λ • ·` is monotone on `V` for `λ ≥ 0`. -/
theorem eja_posSMulMono : PosSMulMono ℝ V := ⟨fun r hr x y hxy => by
  have h2 : (0 : V) ≤ r • (y - x) := (eja_nonneg_iff _).mpr
    (eja_isSumSq_smul hr ((eja_nonneg_iff _).mp (eja_sub_nonneg.mpr hxy)))
  rw [smul_sub] at h2; exact eja_sub_nonneg.mp h2⟩

/-- `· • x` is monotone on `ℝ` for `x ≥ 0`. -/
theorem eja_smulPosMono : SMulPosMono ℝ V := ⟨fun x hx r t hrt => by
  have h2 : (0 : V) ≤ (t - r) • x := (eja_nonneg_iff _).mpr
    (eja_isSumSq_smul (sub_nonneg.mpr hrt) ((eja_nonneg_iff _).mp hx))
  rw [sub_smul] at h2; exact eja_sub_nonneg.mp h2⟩

attribute [local instance] eja_posSMulMono eja_smulPosMono

variable (V) in
/-- **SEA 16** (`ex:canonical-sea`, second.tex:475, Example), the sentence
"any JB-algebra is a convex SEA, while any JBW-algebra is a convex normal SEA"
(product `a ∘ b = U_{√a} b`), for finite-dimensional algebras: for a
Euclidean Jordan algebra `V` (the tree's `EuclideanJordanAlgebra`, i.e. a
finite-dimensional JB(W)-algebra), `[0,1]_V` is a convex effect algebra
(SEA 8) and a normal SEA (`ejaNormalSEA`, whose SEA is `ejaSEA`) with
sequential product `a ∘ b = U_{√a} b = 2 √a(√a b) − a b`. -/
theorem sea16_eja :
    @IsConvex _ (ejaEA V) ∧
    (∀ a b : Set.Icc (0 : V) 1,
      ((@SequentialEffectAlgebra.seq _ (ejaEA V)
        (ejaNormalSEA V).toSEAlgebra.toSequentialEffectAlgebra a b : Set.Icc (0 : V) 1) : V) =
        ejaU (ejaSqrt (a : V)) b) :=
  ⟨sea9_interval_convex V 1 eja_zero_le_one', fun _ _ => rfl⟩

end Papers.SEA.Jordan
