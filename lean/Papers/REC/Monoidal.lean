import Papers.REC.Reconstruction
import Papers.EJA.Albert
import Papers.SEA.Discharge
import Theses.A.VN.Basic

/-!
# REC §6: reconstruction for monoidal effectuses (REC 122–136)

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707, `short.tex` §6 (lines 2264–2418).

The main theorem is **REC 136** (`rec136`): a monoidal sequential effectus (REC 122)
with irreducible scalars `≠ {0,1}` has a functor `F : C → JW_npcᵒᵖ` (`A ↦ V_A`,
`f ↦ Pred(f)`) with `Pred(A) ≅ [0,1]_{F(A)}`, faithful iff `C` is separated by
predicates.  Its core is **REC 135** (`rec135`): with scalars `[0,1]` every `V_A` is a
JW-algebra.

## Named hypotheses (external results, stated as `Prop`s)

* §5's three, carried from REC 102/103: `AlfsenShultzJordanFromDerivations` (REC 121),
  `AlfsenShultzResolventCriterion` (REC 120), `WeteringStateOrderLemma` (REC 119);
* `HancheOlsenStormerDecomposition` — REC 52 (H-O–S 7.2.7), JBW = JW ⊕ purely exceptional;
* `ShultzExceptionalStructure` — REC 55 (Shultz 1979), purely exceptional
  `≅ C(X, M₃(𝕆)_sa)`, with `M₃(𝕆)_sa` the Albert algebra of `Papers/EJA/Albert.lean`;
  REC 133 is then *proved*: the three exchangeable idempotents of `M₃(𝕆)_sa`
  (H-O–S 2.8.3) are computed (`AlbertFacts`);
* `AlfsenShultzFourExchangeable` — REC 132 (A–S *Geometry* 4.4);
* `HancheOlsenStormerUniversalEnvelope` — REC 129 (H-O–S 7.1.9), stated; REC 130 is
  proved for any universal envelope, and REC 135 does not need either.

van de Wetering's thesis Thm 4.6.17 (`asrt_a = Q_{√a}`), which the paper uses for
REC 123/128, is **not** needed: REC 123 follows from REC 100 axiom 5 and SEA square
roots, and REC 128 is proved (for two-block combinations, which is what REC 134 uses)
by evaluating `Q` only at sharp product elements.

## Structure of the file

* OUS/JB toolkit: triangle inequality, `‖ab‖ ≤ ‖a‖‖b‖`, the quadratic map `jQ`.
* REC 129–133: the Jordan-algebraic inputs, the Albert algebra computation.
* The bridge between the Jordan product of REC 121 and the sequential product:
  `y * y = y & y` (`jsq_gmap`, via the commuting spectral approximation
  `spec_comm_approx`), hence Jordan idempotents are sharp (`jidem_gmap`) and
  `Q_e = asrt_e` for sharp `e` (`jQ_idem`); density of sharp combinations
  (`linear_eq_zero_of_idem`).
* The tensor of predicates (`ptens`) and the bilinear map `⊗ : V_A × V_B → V_{A⊗B}`
  (`tensV`); REC 122–128, 134.
* Corners: for a central sharp `c`, `Pred(π_c) : V_A → V_{A_c}` is a surjective Jordan
  homomorphism (`corner_jordan`), transferring pure exceptionality.
* REC 135, REC 136.

## Deviations (recorded in `docs/audit/papers-rec.csv`)

* **REC 127 is false as printed** (`rec127_false_as_printed`): `a ↦ a ⊗ 1_B` is not
  injective for `B = 0`; proved injective when `B` has a state (`rec127`).  Normality is
  proved via `a ⊗ 1 = Pred(ρ)(a)` rather than the printed order-isomorphism argument.
* REC 125, 128 on product vectors (`T_a ⊗ id`, `Q_a ⊗ Q_b` are not defined as operators
  on `V_{A⊗B}` in general); REC 125 also as printed for sharp `a`; REC 128 for
  `a = αe + βe⊥`, `b = γf + δf⊥`.
* REC 135: the paper's `Pred(A_p) ≅ [0,1]_{V₂}` is only an order isomorphism; the
  Jordan structure is transferred by `corner_jordan` instead.
-/

open CategoryTheory
open Theses.B.Eff
open scoped unitInterval

namespace Papers.REC

universe u v w

/-! ## Order unit spaces: the norm (REC 41) -/

/-- Multiplication by a non-negative real is monotone in an order unit space. -/
instance ous_posSMulMono {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V]
    [OrderUnitSpace V] : PosSMulMono ℝ V :=
  ⟨fun _ hr _ _ h => ou_smul_le_smul hr h⟩

section OUSTools

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]

/-- If `c ≤ (x + δ)(y + δ)` for all `δ > 0` then `c ≤ x y` (`x, y ≥ 0`). -/
theorem le_mul_of_forall_pos {c x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ∀ δ : ℝ, 0 < δ → c ≤ (x + δ) * (y + δ)) : c ≤ x * y := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := min 1 (ε / (x + y + 1)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hε (by linarith))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ * (x + y + 1) ≤ ε := by
    have := min_le_right 1 (ε / (x + y + 1))
    rw [← hδ] at this
    calc δ * (x + y + 1) ≤ ε / (x + y + 1) * (x + y + 1) :=
          mul_le_mul_of_nonneg_right this (by linarith)
      _ = ε := div_mul_cancel₀ _ (by linarith)
  have := h δ hδ0
  nlinarith

/-- The triangle inequality for the order-unit norm. -/
theorem ousNorm_add_le (x y : V) : ousNorm V (x + y) ≤ ousNorm V x + ousNorm V y := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a1, a2⟩ := ousNorm_bounds (v := x) (ε := ousNorm V x + ε / 2) (by linarith)
  obtain ⟨b1, b2⟩ := ousNorm_bounds (v := y) (ε := ousNorm V y + ε / 2) (by linarith)
  have hx0 := ousNorm_nonneg_rc x
  have hy0 := ousNorm_nonneg_rc y
  have e : (ousNorm V x + ε / 2) • ouUnit V + (ousNorm V y + ε / 2) • ouUnit V =
      (ousNorm V x + ousNorm V y + ε) • ouUnit V := by rw [← add_smul]; ring_nf
  refine ousNorm_le_rc (by linarith) ?_ ?_
  · rw [← e, neg_add]; exact add_le_add a1 b1
  · rw [← e]; exact add_le_add a2 b2

/-- `‖r v‖ ≤ r ‖v‖` for `r ≥ 0`. -/
theorem ousNorm_smul_le_of_nonneg {r : ℝ} (hr : 0 ≤ r) (x : V) :
    ousNorm V (r • x) ≤ r * ousNorm V x := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hx0 := ousNorm_nonneg_rc x
  set m := ousNorm V x + ε / (r + 1) with hm
  have hm0 : 0 ≤ m := by positivity
  obtain ⟨a1, a2⟩ := ousNorm_bounds (v := x) (ε := m)
    (by rw [hm]; have : 0 < ε / (r + 1) := by positivity
        linarith)
  have hbound : r * m ≤ r * ousNorm V x + ε := by
    rw [hm, mul_add]
    have : r * (ε / (r + 1)) ≤ ε := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  refine le_trans (ousNorm_le_rc (mul_nonneg hr hm0) ?_ ?_) hbound
  · rw [← _root_.smul_smul, ← smul_neg]; exact smul_le_smul_of_nonneg_left a1 hr
  · rw [← _root_.smul_smul]; exact smul_le_smul_of_nonneg_left a2 hr

/-- `‖r v‖ ≤ |r| ‖v‖`. -/
theorem ousNorm_smul_le (r : ℝ) (x : V) : ousNorm V (r • x) ≤ |r| * ousNorm V x := by
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr]; exact ousNorm_smul_le_of_nonneg hr x
  · rw [abs_of_nonpos hr, ← ousNorm_neg (r • x), ← neg_smul]
    exact ousNorm_smul_le_of_nonneg (neg_nonneg.2 hr) x

theorem ousNorm_sub_comm (x y : V) : ousNorm V (x - y) = ousNorm V (y - x) := by
  rw [← ousNorm_neg, neg_sub]

theorem ousNorm_zero' : ousNorm V (0 : V) = 0 :=
  le_antisymm (ousNorm_le_rc le_rfl (by simp) (by simp)) (ousNorm_nonneg_rc _)

variable [IsOUS V]

/-- In an order unit space (REC 41, closed cone) `-‖v‖·1 ≤ v ≤ ‖v‖·1`. -/
theorem ousNorm_bounds_le (v : V) :
    -(ousNorm V v • ouUnit V) ≤ v ∧ v ≤ ousNorm V v • ouUnit V := by
  have key : ∀ w : V, (∀ ε : ℝ, 0 < ε → 0 ≤ w + ε • ouUnit V) → 0 ≤ w := by
    intro w hw
    refine IsOUS.cone_closed w fun ε hε => ⟨w + (ε / 2) • ouUnit V, hw _ (by positivity), ?_⟩
    rw [sub_add_cancel_left, ousNorm_neg]
    refine lt_of_le_of_lt (ousNorm_le_rc (by positivity) ?_ le_rfl) (by linarith)
    exact neg_le_self (smul_nonneg (by positivity) ou_unit_nonneg)
  constructor
  · rw [← sub_nonneg, sub_neg_eq_add]
    refine key _ fun ε hε => ?_
    obtain ⟨h1, -⟩ := ousNorm_bounds (v := v) (ε := ousNorm V v + ε) (by linarith)
    have : 0 ≤ v + (ousNorm V v + ε) • ouUnit V := by
      rw [← sub_neg_eq_add]; exact sub_nonneg.2 h1
    have e : v + (ousNorm V v + ε) • ouUnit V = v + ousNorm V v • ouUnit V + ε • ouUnit V := by
      rw [add_smul]; abel
    rwa [e] at this
  · rw [← sub_nonneg]
    refine key _ fun ε hε => ?_
    obtain ⟨-, h2⟩ := ousNorm_bounds (v := v) (ε := ousNorm V v + ε) (by linarith)
    have := sub_nonneg.2 h2
    rw [add_smul] at this
    have e : ousNorm V v • ouUnit V + ε • ouUnit V - v = ousNorm V v • ouUnit V - v + ε • ouUnit V := by
      abel
    rwa [e] at this

/-- A vector of arbitrarily small norm is zero. -/
theorem eq_zero_of_ousNorm_small {v : V} (h : ∀ ε : ℝ, 0 < ε → ousNorm V v ≤ ε) : v = 0 :=
  IsOUS.norm_eq_zero v (le_antisymm (le_of_forall_pos_le_add fun ε hε => by
    simpa using h ε hε) (ousNorm_nonneg_rc v))

end OUSTools

/-! ## JB-algebras (REC 44): products, squares, the quadratic map -/

section JQ

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V]

/-- The quadratic map `Q_a b = 2 a(ab) - a² b` of a Jordan algebra. -/
def jQ (a b : V) : V := (2 : ℝ) • (a * (a * b)) - (a * a) * b

/-- The triple product `Q_{a,c} b = a(cb) + c(ab) − (ac)b`, symmetric and bilinear in
`(a, c)`, with `Q_{a,a} = Q_a` (`jQ_eq_jQ2`).  (The paper's running text before REC 128
prints `Q_{a,b} c = (a*b)*c + (c*b)*a − (a*c)*b`, which has `b` and `c` exchanged: as
printed `Q_{a,a} = T_{a²} ≠ Q_a`.) -/
def jQ2 (a c b : V) : V := a * (c * b) + c * (a * b) - (a * c) * b

theorem jQ_eq_jQ2 (a b : V) : jQ a b = jQ2 a a b := by
  simp only [jQ, jQ2]; rw [two_smul]

end JQ


section JBTools

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

theorem jb_mul_add (a b c : V) : a * (b + c) = a * b + a * c := by
  rw [JBAlgebra.mul_comm, JBAlgebra.add_mul, JBAlgebra.mul_comm b, JBAlgebra.mul_comm c]

theorem jb_mul_smul (r : ℝ) (a b : V) : a * (r • b) = r • (a * b) := by
  rw [JBAlgebra.mul_comm, JBAlgebra.smul_mul, JBAlgebra.mul_comm]

theorem jb_zero_mul (a : V) : (0 : V) * a = 0 := by
  have := JBAlgebra.smul_mul (0 : ℝ) (0 : V) a
  simpa using this

theorem jb_mul_zero (a : V) : a * (0 : V) = 0 := by
  rw [JBAlgebra.mul_comm]; exact jb_zero_mul a

theorem jb_neg_mul (a b : V) : (-a) * b = -(a * b) := by
  have := JBAlgebra.smul_mul (-1 : ℝ) a b
  simpa using this

theorem jb_sub_mul (a b c : V) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg, JBAlgebra.add_mul, jb_neg_mul, ← sub_eq_add_neg]

theorem jb_mul_sub (a b c : V) : a * (b - c) = a * b - a * c := by
  rw [JBAlgebra.mul_comm, jb_sub_mul, JBAlgebra.mul_comm b, JBAlgebra.mul_comm c]

theorem jb_mul_neg (a b : V) : a * (-b) = -(a * b) := by
  rw [JBAlgebra.mul_comm, jb_neg_mul, JBAlgebra.mul_comm]

/-- The Jordan product as a bilinear map. -/
noncomputable def jbT (a : V) : V →ₗ[ℝ] V where
  toFun b := a * b
  map_add' := jb_mul_add a
  map_smul' r b := jb_mul_smul r a b

@[simp] theorem jbT_apply (a b : V) : jbT a b = a * b := rfl

/-- If `‖a‖ < r` and `‖b‖ < s` then `-rs·1 ≤ a b ≤ rs·1`. -/
theorem jb_sq_bounds {a : V} {r : ℝ} (hr : 0 < r) (ha : ousNorm V a < r) :
    0 ≤ a * a ∧ a * a ≤ (r * r) • ouUnit V := by
  obtain ⟨h1, h2⟩ := ousNorm_bounds ha
  have hx1 : -ouUnit V ≤ r⁻¹ • a := by
    have := smul_le_smul_of_nonneg_left h1 (inv_nonneg.2 hr.le)
    rwa [smul_neg, _root_.smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at this
  have hx2 : r⁻¹ • a ≤ ouUnit V := by
    have := smul_le_smul_of_nonneg_left h2 (inv_nonneg.2 hr.le)
    rwa [_root_.smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at this
  obtain ⟨s1, s2⟩ := JBAlgebra.sq_mem (r⁻¹ • a) hx1 hx2
  have e : a * a = (r * r) • ((r⁻¹ • a) * (r⁻¹ • a)) := by
    rw [JBAlgebra.smul_mul, jb_mul_smul, _root_.smul_smul, _root_.smul_smul]
    rw [show r * r * r⁻¹ * r⁻¹ = (1 : ℝ) by field_simp, one_smul]
  rw [e]
  exact ⟨smul_nonneg (by positivity) s1, smul_le_smul_of_nonneg_left s2 (by positivity)⟩

/-- Squares are positive. -/
theorem jb_sq_nonneg (a : V) : 0 ≤ a * a :=
  (jb_sq_bounds (r := ousNorm V a + 1) (by linarith [ousNorm_nonneg_rc a]) (by linarith)).1

/-- `‖a b‖ ≤ ‖a‖ ‖b‖`. -/
theorem jb_norm_mul_le (a b : V) : ousNorm V (a * b) ≤ ousNorm V a * ousNorm V b := by
  refine le_mul_of_forall_pos (ousNorm_nonneg_rc a) (ousNorm_nonneg_rc b) fun δ hδ => ?_
  set r := ousNorm V a + δ
  set s := ousNorm V b + δ
  have hr : 0 < r := by have := ousNorm_nonneg_rc a; positivity
  have hs : 0 < s := by have := ousNorm_nonneg_rc b; positivity
  set x := r⁻¹ • a
  set y := s⁻¹ • b
  have hxn : ousNorm V x < 1 := by
    have := ousNorm_smul_le r⁻¹ a
    rw [abs_of_pos (inv_pos.2 hr)] at this
    refine lt_of_le_of_lt this ?_
    rw [inv_mul_lt_iff₀ hr]; linarith
  have hyn : ousNorm V y < 1 := by
    have := ousNorm_smul_le s⁻¹ b
    rw [abs_of_pos (inv_pos.2 hs)] at this
    refine lt_of_le_of_lt this ?_
    rw [inv_mul_lt_iff₀ hs]; linarith
  have hp : ousNorm V (x + y) < 2 := lt_of_le_of_lt (ousNorm_add_le x y) (by linarith)
  have hm : ousNorm V (x - y) < 2 := by
    rw [sub_eq_add_neg]
    refine lt_of_le_of_lt (ousNorm_add_le x (-y)) ?_
    rw [ousNorm_neg]; linarith
  obtain ⟨p1, p2⟩ := jb_sq_bounds (by norm_num : (0 : ℝ) < 2) hp
  obtain ⟨m1, m2⟩ := jb_sq_bounds (by norm_num : (0 : ℝ) < 2) hm
  have e : x * y = (4⁻¹ : ℝ) • ((x + y) * (x + y) - (x - y) * (x - y)) := by
    rw [JBAlgebra.add_mul, jb_mul_add, jb_mul_add, jb_sub_mul, jb_mul_sub, jb_mul_sub,
      JBAlgebra.mul_comm y x]
    module
  have hxy : ousNorm V (x * y) ≤ 1 := by
    rw [e]
    refine ousNorm_le_rc zero_le_one ?_ ?_
    · have : -((2 * 2 : ℝ) • ouUnit V) ≤ (x + y) * (x + y) - (x - y) * (x - y) := by
        rw [neg_le_sub_iff_le_add]
        exact le_add_of_nonneg_of_le p1 m2
      have := smul_le_smul_of_nonneg_left this (show (0 : ℝ) ≤ 4⁻¹ by norm_num)
      rw [smul_neg, _root_.smul_smul] at this
      norm_num at this ⊢; exact this
    · have : (x + y) * (x + y) - (x - y) * (x - y) ≤ (2 * 2 : ℝ) • ouUnit V :=
        le_trans (sub_le_self _ m1) p2
      have := smul_le_smul_of_nonneg_left this (show (0 : ℝ) ≤ 4⁻¹ by norm_num)
      rw [_root_.smul_smul] at this
      norm_num at this ⊢; exact this
  have eab : a * b = (r * s) • (x * y) := by
    rw [JBAlgebra.smul_mul, jb_mul_smul, _root_.smul_smul, _root_.smul_smul]
    rw [show r * s * r⁻¹ * s⁻¹ = (1 : ℝ) by field_simp, one_smul]
  rw [eab]
  refine (ousNorm_smul_le _ _).trans ?_
  rw [abs_of_pos (mul_pos hr hs)]
  calc r * s * ousNorm V (x * y) ≤ r * s * 1 := mul_le_mul_of_nonneg_left hxy (by positivity)
    _ = r * s := mul_one _

end JBTools

/-! ## REC 129–133: the Jordan-algebraic inputs of §6 -/

section JordanInputs

/-- **REC 131** (short.tex:2373, Definition): `s` is a **symmetry** when `s² = 1`. -/
def IsSymmetry {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
    [Mul V] (s : V) : Prop :=
  s * s = ouUnit V

/-- **REC 131** (short.tex:2373, Definition): idempotents `p, q` are **exchangeable by a
symmetry** when `Q_s p = q` for some symmetry `s`. -/
def ExchangeableBySymmetry {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V]
    [OrderUnitSpace V] [Mul V] (p q : V) : Prop :=
  p * p = p ∧ q * q = q ∧ ∃ s : V, IsSymmetry s ∧ jQ s p = q

/-- The universal property of **REC 129**: `ψ : V → W` is a normal Jordan homomorphism
into a von Neumann algebra `W` through which every normal Jordan homomorphism `φ` of `V`
into (the self-adjoint part of) a von Neumann algebra factors uniquely as `φ̂ ∘ ψ` with
`φ̂` a normal `*`-homomorphism. -/
def IsUniversalEnvelope (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V]
    [OrderUnitSpace V] [Mul V] (W : Type v) [CStarAlgebra W] [PartialOrder W]
    [StarOrderedRing W] (ψ : V →ₗ[ℝ] W) : Prop :=
  Theses.VonNeumannAlgebra W ∧ IsJordanHomInto V W ψ ∧ IsNormalMap ψ ∧
    ∀ (𝔅 : Type v) [CStarAlgebra 𝔅] [PartialOrder 𝔅] [StarOrderedRing 𝔅]
      [Theses.VonNeumannAlgebra 𝔅] (φ : V →ₗ[ℝ] 𝔅), IsJordanHomInto V 𝔅 φ → IsNormalMap φ →
        ∃! φh : W →⋆ₐ[ℂ] 𝔅, IsNormalMap φh ∧ ∀ x, φh (ψ x) = φ x

/-- **REC 129** (short.tex:2362, Theorem; Hanche-Olsen–Størmer, *Jordan operator
algebras*, Thm 7.1.9), as a named hypothesis: every JBW-algebra `V` has a **universal
von Neumann algebra** `W*(V)` with a normal Jordan homomorphism `ψ : V → W*(V)_sa`
through which every normal Jordan homomorphism into a von Neumann algebra factors
uniquely through a normal `*`-homomorphism.  (The source also says `ψ(V)` generates
`W*(V)` and that `W*(V)` is unique up to isomorphism; both are omitted, which only
weakens the hypothesis.  Von Neumann algebras are thesis A's Kadison ones,
`Theses.VonNeumannAlgebra`, in the universe of `V`.) -/
def HancheOlsenStormerUniversalEnvelope : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V],
    JBWAlgebra V →
      ∃ (W : Type v) (_ : CStarAlgebra W) (_ : PartialOrder W) (_ : StarOrderedRing W)
        (ψ : V →ₗ[ℝ] W), IsUniversalEnvelope V W ψ

/-- **REC 130** (`cor:JW-injective`, short.tex:2366, Corollary): a JBW-algebra is a
JW-algebra iff `ψ : V → W*(V)` is injective.  Proved for any universal envelope in the
sense of REC 129 (so REC 129's existence claim is not needed), by the paper's argument:
an injective normal Jordan homomorphism `φ` into a von Neumann algebra factors as
`φ̂ ∘ ψ`, so `ψ` is injective; conversely `ψ` itself witnesses REC 50. -/
theorem rec130 (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
    [Mul V] (W : Type v) [CStarAlgebra W] [PartialOrder W] [StarOrderedRing W]
    (ψ : V →ₗ[ℝ] W) (hψ : IsUniversalEnvelope V W ψ) :
    IsJWAlgebra V ↔ Function.Injective ψ := by
  constructor
  · rintro ⟨𝔄, i1, i2, i3, i4, φ, hφJ, hφi, hφn⟩
    obtain ⟨φh, ⟨-, hφh⟩, -⟩ := hψ.2.2.2 𝔄 φ hφJ hφn
    intro x y hxy
    apply hφi
    rw [← hφh x, ← hφh y, hxy]
  · intro hinj
    exact ⟨W, inferInstance, inferInstance, inferInstance, hψ.1, ψ, hψ.2.1, hinj, hψ.2.2.1⟩

/-- **REC 132** (`lem:exchangeable-by-4-is-JW`, short.tex:2377, Lemma; Alfsen–Shultz,
*Geometry of state spaces of operator algebras*, Lemma 4.4), as a named hypothesis: a
JBW-algebra whose unit is the sum of `n ≥ 4` idempotents that are mutually exchangeable
by a symmetry is a JW-algebra (REC 50).  Stated for finitely many idempotents, which we
also ask to be non-zero and pairwise orthogonal (`p_i p_j = 0`; automatic for idempotents
summing to `1`); both only weaken the hypothesis. -/
def AlfsenShultzFourExchangeable : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V],
    JBWAlgebra V → ∀ (n : ℕ), 4 ≤ n → ∀ p : Fin n → V,
      (∀ i, p i * p i = p i ∧ p i ≠ 0) → (∀ i j, i ≠ j → p i * p j = 0) →
      ∑ i, p i = ouUnit V → (∀ i j, ∃ s : V, IsSymmetry s ∧ jQ s (p i) = p j) →
      IsJWAlgebra V

/-- **REC 52** (`thm:JBW-decomposition`, short.tex:925, Theorem; Hanche-Olsen–Størmer,
*Jordan operator algebras*, Thm 7.2.7), as a named hypothesis, in the form REC 135
uses it: a JBW-algebra `V` splits along a central idempotent `c` (`c² = c`, and `c`
operator-commutes with everything: `c(xy) = x(cy)`) into a JW-part `(1-c)V` and a
purely exceptional part `cV = {x ; c x = x}`.  "`(1-c)V` is JW" is rendered as a normal
Jordan homomorphism `φ` of `V` into a von Neumann algebra with kernel exactly `cV`
(compose the embedding of `(1-c)V` with the Jordan projection `x ↦ (1-c)x`); "`cV` is
purely exceptional" (REC 51) as: every Jordan homomorphism of `V` into a C*-algebra
vanishes on `cV` (its restriction to `cV` is a Jordan homomorphism of `cV`).  The
source's uniqueness of `c` is omitted. -/
def HancheOlsenStormerDecomposition : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V],
    JBWAlgebra V → ∃ c : V, c * c = c ∧ (∀ x y : V, c * (x * y) = x * (c * y)) ∧
      (∃ (𝔄 : Type v) (_ : CStarAlgebra 𝔄) (_ : PartialOrder 𝔄) (_ : StarOrderedRing 𝔄)
          (_ : Theses.VonNeumannAlgebra 𝔄) (φ : V →ₗ[ℝ] 𝔄),
          IsJordanHomInto V 𝔄 φ ∧ IsNormalMap φ ∧ ∀ x, φ x = 0 ↔ c * x = x) ∧
      ∀ (𝔅 : Type v) [CStarAlgebra 𝔅] (ψ : V →ₗ[ℝ] 𝔅), IsJordanHomInto V 𝔅 ψ →
        ∀ x, c * x = x → ψ x = 0

/-- **REC 55** (`thm:purely-exceptional-char`, short.tex:940, Theorem; Shultz 1979,
Hanche-Olsen–Størmer Thm 7.2.7), as a named hypothesis: a purely exceptional
JBW-algebra is Jordan-isomorphic to `C(X, M₃(𝕆)_sa)` for a hyperstonean `X` (REC 53),
with the pointwise Jordan product.  `M₃(𝕆)_sa` is the Albert algebra
`Papers.EJA.Albert.Alb` (constructed, with its Jordan identity proved, in
`Papers/EJA/Albert.lean`).  Only a linear bijection preserving the product is asked
(the source's isomorphism is also isometric and an order isomorphism). -/
def ShultzExceptionalStructure : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V],
    JBWAlgebra V → IsPurelyExceptional.{v, v} V →
      ∃ (X : Type v) (_ : TopologicalSpace X), IsHyperstonean X ∧
        ∃ Φ : V ≃ₗ[ℝ] C(X, Papers.EJA.Albert.Alb), ∀ (a b : V) (t : X),
          Φ (a * b) t = Φ a t * Φ b t

end JordanInputs

/-! ### The Albert algebra: three exchangeable idempotents (Hanche-Olsen–Størmer 2.8.3) -/

namespace AlbertFacts

open Papers.EJA Papers.EJA.Albert Matrix

/-- Integer matrices inside `M₃(𝕆)`. -/
noncomputable def octZ : ℤ →+* Oct := Int.castRingHom Oct

theorem albZ_herm (R : Matrix (Fin 3) (Fin 3) ℤ) (hR : Rᵀ = R) : (R.map octZ).IsHermitian := by
  show (R.map octZ)ᴴ = R.map octZ
  ext i j
  rw [conjTranspose_apply, map_apply, map_apply]
  rw [show octZ (R j i) = ((R j i : ℤ) : Oct) from rfl, star_intCast]
  rw [show R j i = R i j by rw [← transpose_apply R i j, hR]]
  rfl

/-- A symmetric integer matrix as an element of the Albert algebra. -/
noncomputable def albZ (R : Matrix (Fin 3) (Fin 3) ℤ) (hR : Rᵀ = R) : Alb :=
  (⟨R.map octZ, albZ_herm R hR⟩ : ↥(hermSub 3 Oct))

theorem albZ_mat (R : Matrix (Fin 3) (Fin 3) ℤ) (hR : Rᵀ = R) : (albZ R hR).mat = R.map octZ :=
  rfl

theorem symm_jordan {R R' : Matrix (Fin 3) (Fin 3) ℤ} (hR : Rᵀ = R) (hR' : R'ᵀ = R') :
    (R * R' + R' * R)ᵀ = R * R' + R' * R := by
  rw [transpose_add, transpose_mul, transpose_mul, hR, hR', add_comm]

theorem albZ_mul {R R' : Matrix (Fin 3) (Fin 3) ℤ} (hR : Rᵀ = R) (hR' : R'ᵀ = R') :
    albZ R hR * albZ R' hR' = (1 / 2 : ℝ) • albZ (R * R' + R' * R) (symm_jordan hR hR') :=
  HermMat.ext (by
    rw [HermMat.mat_mul, HermMat.mat_smul, albZ_mat, albZ_mat, albZ_mat,
      Matrix.map_add _ (map_add octZ), Matrix.map_mul, Matrix.map_mul])

theorem albZ_add {R R' : Matrix (Fin 3) (Fin 3) ℤ} (hR : Rᵀ = R) (hR' : R'ᵀ = R')
    (h : (R + R')ᵀ = R + R') : albZ (R + R') h = albZ R hR + albZ R' hR' :=
  HermMat.ext (by rw [HermMat.mat_add, albZ_mat, albZ_mat, albZ_mat, Matrix.map_add _ (map_add octZ)])

theorem albZ_zero : albZ 0 transpose_zero = 0 :=
  HermMat.ext (by rw [albZ_mat, HermMat.mat_zero]; exact Matrix.map_zero _ (map_zero _))

theorem albZ_congr {R R' : Matrix (Fin 3) (Fin 3) ℤ} (hR : Rᵀ = R) (hR' : R'ᵀ = R')
    (e : R = R') : albZ R hR = albZ R' hR' := by subst e; rfl

theorem albZ_one : albZ 1 (transpose_one) = 1 :=
  HermMat.ext (by rw [albZ_mat, HermMat.mat_one]; exact Matrix.map_one _ (map_zero _) (map_one _))

/-- The diagonal idempotents `E_ii`. -/
def dE (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun a b => if a = i ∧ b = i then 1 else 0

/-- The permutation matrix of the transposition `(i j)`. -/
def dS (i j : Fin 3) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun a b => if Equiv.swap i j a = b then 1 else 0

theorem dE_symm (i : Fin 3) : (dE i)ᵀ = dE i := by
  ext a b; simp only [dE, transpose_apply, of_apply]; by_cases h : a = i <;> by_cases h' : b = i <;>
    simp [h, h']

theorem dS_symm (i j : Fin 3) : (dS i j)ᵀ = dS i j := by
  ext a b; simp only [dS, transpose_apply, of_apply]
  have : (Equiv.swap i j b = a) ↔ (Equiv.swap i j a = b) := by
    constructor <;> (intro h; rw [← h, Equiv.swap_apply_self])
  simp only [this]

theorem dE_mul (i j : Fin 3) : dE i * dE j = if i = j then dE i else 0 := by
  revert i j; decide

theorem dS_sq (i j : Fin 3) : dS i j * dS i j = 1 := by
  revert i j; decide

theorem dS_conj (i j : Fin 3) : dS i j * dE i * dS i j = dE j := by
  revert i j; decide

theorem dE_sum : dE 0 + dE 1 + dE 2 = 1 := by decide

/-- The idempotents `E_ii` of `M₃(𝕆)_sa`. -/
noncomputable def aE (i : Fin 3) : Alb := albZ (dE i) (dE_symm i)

/-- The symmetries (transposition matrices). -/
noncomputable def aS (i j : Fin 3) : Alb := albZ (dS i j) (dS_symm i j)

theorem alb_one_mul (x : Alb) : 1 * x = x := by rw [mul_comm', mul_one']

theorem aE_mul (i j : Fin 3) : aE i * aE j = if i = j then aE i else 0 := by
  unfold aE
  rw [albZ_mul]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    have e : dE i * dE i + dE i * dE i = dE i + dE i := by rw [dE_mul, if_pos rfl]
    rw [albZ_congr _ (by rw [transpose_add, dE_symm]) e, albZ_add (dE_symm i) (dE_symm i)]
    module
  · rw [if_neg h]
    have e : dE i * dE j + dE j * dE i = 0 := by rw [dE_mul, dE_mul, if_neg h, if_neg (Ne.symm h),
      add_zero]
    rw [albZ_congr _ transpose_zero e, albZ_zero, smul_zero]

theorem aS_sq (i j : Fin 3) : aS i j * aS i j = 1 := by
  unfold aS
  rw [albZ_mul]
  have e : dS i j * dS i j + dS i j * dS i j = 1 + 1 := by rw [dS_sq]
  rw [albZ_congr _ (by rw [transpose_add, transpose_one]) e, albZ_add transpose_one transpose_one,
    albZ_one]
  module

theorem aS_exchange (i j : Fin 3) : jQ (aS i j) (aE i) = aE j := by
  unfold jQ
  rw [aS_sq, alb_one_mul]
  unfold aS aE
  rw [albZ_mul, mul_smul', albZ_mul]
  set S := dS i j
  set E := dE i
  have hS : Sᵀ = S := dS_symm i j
  have hE : Eᵀ = E := dE_symm i
  have hSES : (S * E * S)ᵀ = S * E * S := by rw [transpose_mul, transpose_mul, hS, hE, mul_assoc]
  have e : S * (S * E + E * S) + (S * E + E * S) * S = (E + E) + (S * E * S + S * E * S) := by
    rw [mul_add, add_mul, ← mul_assoc, dS_sq, one_mul, mul_assoc E, dS_sq, mul_one, mul_assoc S E S]
    abel
  rw [albZ_congr _ (by rw [transpose_add, transpose_add, transpose_add, hE, hSES]) e,
    albZ_add (by rw [transpose_add, hE]) (by rw [transpose_add, hSES]),
    albZ_add hE hE, albZ_add hSES hSES]
  have hc : albZ (S * E * S) hSES = albZ (dE j) (dE_symm j) := albZ_congr _ _ (dS_conj i j)
  rw [hc]
  module

theorem aE_sum : aE 0 + aE 1 + aE 2 = 1 := by
  unfold aE
  rw [← albZ_add (dE_symm 0) (dE_symm 1) (by rw [transpose_add, dE_symm, dE_symm]),
    ← albZ_add (by rw [transpose_add, dE_symm, dE_symm]) (dE_symm 2)
      (by rw [transpose_add, transpose_add, dE_symm, dE_symm, dE_symm])]
  rw [albZ_congr _ transpose_one dE_sum, albZ_one]

theorem aE_ne_zero (i : Fin 3) : aE i ≠ 0 := by
  intro h
  have := congrArg (fun x : Alb => (x.mat i i).fst.re) h
  simp only [aE, albZ_mat, map_apply, dE, of_apply, and_self, if_true, HermMat.mat_zero,
    Matrix.zero_apply] at this
  rw [show octZ 1 = (1 : Oct) from map_one _] at this
  exact one_ne_zero this

end AlbertFacts

/-- **REC 133** (`lem:symmetry-exceptional`, short.tex:2381, Lemma): the unit of a
non-zero purely exceptional JBW-algebra is the sum of 3 orthogonal non-zero idempotents
that are mutually exchangeable by a symmetry.  The paper's proof: `V ≅ C(X, M₃(𝕆)_sa)`
(REC 55, the named hypothesis `ShultzExceptionalStructure`); `M₃(𝕆)_sa` has three
exchangeable diagonal idempotents (Hanche-Olsen–Størmer 2.8.3 — here computed in the
Albert algebra of `Papers/EJA/Albert.lean`: the diagonal matrix units `E_ii`, exchanged
by the transposition matrices); take constant functions. -/
theorem rec133 (hSh : ShultzExceptionalStructure.{v}) (V : Type v) [AddCommGroup V]
    [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V] (hV : JBWAlgebra V)
    (hpe : IsPurelyExceptional.{v, v} V) (hne : ∃ x : V, x ≠ 0) :
    ∃ q : Fin 3 → V, (∀ i, q i * q i = q i ∧ q i ≠ 0) ∧ (∀ i j, i ≠ j → q i * q j = 0) ∧
      ∑ i, q i = ouUnit V ∧ ∀ i j, ∃ s : V, IsSymmetry s ∧ jQ s (q i) = q j := by
  open AlbertFacts Papers.EJA.Albert in
  obtain ⟨X, iX, -, Φ, hΦ⟩ := hSh V hV hpe
  obtain ⟨x₀, hx₀⟩ := hne
  have hX : Nonempty X := by
    by_contra hc
    apply hx₀
    apply Φ.injective
    ext t
    exact (hc ⟨t⟩).elim
  obtain ⟨t₀⟩ := hX
  let cst : Alb →ₗ[ℝ] C(X, Alb) :=
    { toFun := ContinuousMap.const X
      map_add' := fun a b => by ext; rfl
      map_smul' := fun r a => by ext; rfl }
  let κL : Alb →ₗ[ℝ] V := Φ.symm.toLinearMap ∘ₗ cst
  let κ : Alb → V := κL
  have hκmul : ∀ a b, κ a * κ b = κ (a * b) := by
    intro a b
    apply Φ.injective
    ext t
    rw [hΦ]
    simp [κ, κL, cst]
  have hκlin : ∀ (r s : ℝ) (a b : Alb), κ (r • a + s • b) = r • κ a + s • κ b := by
    intro r s a b
    simp only [κ, map_add, map_smul]
  have hκinj : ∀ a b, κ a = κ b → a = b := by
    intro a b h
    have := congrArg (fun y => Φ y t₀) h
    simpa [κ, κL, cst] using this
  have hunit : κ 1 = ouUnit V := by
    have h1 : ∀ t, Φ (ouUnit V) t = 1 := by
      intro t
      have := congrArg (fun y => Φ y t) (JBAlgebra.one_mul (A := V) (κ 1))
      rw [hΦ] at this
      simpa [κ, κL, cst, mul_one'] using this
    apply Φ.injective
    ext t
    simp [κ, κL, cst, h1 t]
  have hκQ : ∀ a b, jQ (κ a) (κ b) = κ (jQ a b) := by
    intro a b
    simp only [jQ]
    rw [hκmul, hκmul, hκmul, hκmul]
    have := hκlin 2 (-1) (a * (a * b)) (a * a * b)
    rw [neg_one_smul, neg_one_smul, ← sub_eq_add_neg, ← sub_eq_add_neg] at this
    exact this.symm
  refine ⟨fun i => κ (aE i), fun i => ⟨?_, ?_⟩, fun i j hij => ?_, ?_, fun i j => ?_⟩
  · rw [hκmul, aE_mul, if_pos rfl]
  · intro h
    have h' : κ (aE i) = 0 := h
    apply aE_ne_zero i
    apply hκinj
    rw [h']
    exact (map_zero κL).symm
  · rw [hκmul, aE_mul, if_neg hij]
    exact map_zero κL
  · rw [Fin.sum_univ_three, ← hunit, ← aE_sum]
    have h1 := hκlin 1 1 (aE 0) (aE 1)
    have h2 := hκlin 1 1 (aE 0 + aE 1) (aE 2)
    simp only [one_smul] at h1 h2
    rw [h2, h1]
  · refine ⟨κ (aS i j), ?_, ?_⟩
    · show κ (aS i j) * κ (aS i j) = ouUnit V
      rw [hκmul, aS_sq, hunit]
    · rw [hκQ, aS_exchange]

/-! ## The Jordan product on a sequential effect algebra's space

A normal SEA `E` with a convex structure, whose Gudder–Pulmannová space `V = GP.Vec E`
carries a JB-product with `e * w = ½ (w + e & w − e⊥ & w)` for idempotent `e` (this is
what REC 121 provides for `V_A`).  Everything below is used for `V_A` in §6. -/

section SeqJordan

open Papers.SEA
open scoped Papers.SEA

variable {E : Type u} [EffectAlgebra E] [NormalSEA E] [EffectModule I E]
  (hsm : ∀ (a b : E) (l : I), a ⊙ (l • b) = l • (a ⊙ b))

omit [EffectModule I E] in
theorem commutes_psi {B : Type u} [CompleteBooleanAlgebra B] {X : Type u} [TopologicalSpace X]
    (Ψ : B → Set.Icc (0 : C(X, ℝ)) 1 → E)
    (hmul : ∀ b b' f f', Ψ (b ⊓ b') (kmul f f') = Ψ b f ⊙ Ψ b' f') (b b' f f') :
    Commutes (Ψ b f) (Ψ b' f') := by
  show Ψ b f ⊙ Ψ b' f' = Ψ b' f' ⊙ Ψ b f
  rw [← hmul, ← hmul, inf_comm]
  congr 1
  exact kext fun t => by simp [mul_comm]

/-- **The spectral theorem, commuting form** (REC 58): every effect `y` is a norm limit of
combinations of idempotents that commute with `y` (the level-set idempotents of `y`'s
spectral representation). -/
theorem spec_comm_approx (y : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List (ℝ × E), (∀ p ∈ l, Papers.SEA.IsIdempotent p.2 ∧ Commutes p.2 y) ∧
      ousNorm (GP.Vec E) (GP.gmap y - (l.map fun p => p.1 • GP.gmap p.2).sum) < ε := by
  obtain ⟨B, _, X, _, _, _, hED, Ψ, hadd, hone, hmul, -, b, f, rfl⟩ := spectral_rep y
  set G : B → Set.Icc (0 : C(X, ℝ)) 1 → GP.Vec E := fun b f => GP.gmap (Ψ b f) with hG
  have hGadd := fun {b b' f f' k} hb hk => spec_G_add (E := E) Ψ hadd (b := b) (b' := b')
    (f := f) (f' := f') (k := k) hb hk
  have hG0 : G ⊥ kzero = 0 := by simp only [hG]; rw [spec_zero Ψ hadd, GP.gmap_zero]
  have hGnn : ∀ b f, 0 ≤ G b f := fun b f => GP.gmap_nonneg _
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnε : 1 / (n : ℝ) < ε := by
    rw [div_lt_iff₀ hnR]; rw [div_lt_iff₀ hε] at hn; linarith
  let S : ℕ → Set.Icc (0 : C(X, ℝ)) 1 := fun j =>
    kmk ((f : C(X, ℝ)) ⊓ ContinuousMap.const X ((j : ℝ) / n))
      (fun t => le_min (cIcc_nonneg f t) (by simp; positivity))
      (fun t => min_le_of_left_le (cIcc_le_one f t))
  have hS : ∀ j t, (S j : C(X, ℝ)) t = min ((f : C(X, ℝ)) t) ((j : ℝ) / n) := fun j t => by
    simp [S]
  have hSmono : ∀ j t, (S j : C(X, ℝ)) t ≤ (S (j + 1) : C(X, ℝ)) t := fun j t => by
    rw [hS, hS]; exact min_le_min_left _ (div_le_div_of_nonneg_right (by push_cast; linarith)
      hnR.le)
  let L : ℕ → Set.Icc (0 : C(X, ℝ)) 1 := fun j =>
    kmk ((S (j + 1) : C(X, ℝ)) - S j) (fun t => by simp only [ContinuousMap.sub_apply]; linarith [hSmono j t])
      (fun t => by
        simp only [ContinuousMap.sub_apply]
        have := cIcc_le_one (S (j + 1)) t; have := cIcc_nonneg (S j) t; linarith)
  have hL : ∀ j t, (L j : C(X, ℝ)) t = (S (j + 1) : C(X, ℝ)) t - (S j : C(X, ℝ)) t :=
    fun j t => rfl
  have hWc : ∀ j : ℕ, IsClopen (closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t}) := fun j =>
    ⟨isClosed_closure, hED.open_closure _ (isOpen_lt continuous_const (f : C(X, ℝ)).continuous)⟩
  have hWf : ∀ j : ℕ, ∀ t ∈ closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t},
      (j : ℝ) / n ≤ (f : C(X, ℝ)) t := fun j t ht =>
    closure_minimal (fun s hs => le_of_lt hs) (isClosed_le continuous_const
      (f : C(X, ℝ)).continuous) ht
  have hWn : ∀ j : ℕ, ∀ t ∉ closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t},
      (f : C(X, ℝ)) t ≤ (j : ℝ) / n := fun j t ht => by
    by_contra hc; push Not at hc; exact ht (subset_closure hc)
  let χ : ℕ → Set.Icc (0 : C(X, ℝ)) 1 := fun j => kind _ (hWc j)
  have hχ : ∀ j t, (χ j : C(X, ℝ)) t =
      (closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t}).indicator (fun _ => (1 : ℝ)) t :=
    fun j t => rfl
  have hn1 : (0 : ℝ) ≤ ((1 : ℕ) : ℝ) / n := by positivity
  have hn2 : ((1 : ℕ) : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact_mod_cast hnpos
  have hup : ∀ j, G ⊥ (L j) ≤ (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j) := by
    intro j
    rw [← spec_G_rat Ψ hadd (χ j) hnpos 1 hn1 hn2]
    refine spec_G_bot_mono Ψ hadd fun t => ?_
    simp only [kscale_val, ContinuousMap.smul_apply, smul_eq_mul, hχ, hL, hS]
    by_cases ht : t ∈ closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t}
    · rw [Set.indicator_of_mem ht, mul_one]
      have h1 := min_le_right ((f : C(X, ℝ)) t) (((j + 1 : ℕ) : ℝ) / n)
      have h2 := hWf j t ht
      rw [min_eq_right h2]; push_cast at h1 ⊢
      have : ((j : ℝ) + 1) / n = (j : ℝ) / n + 1 / n := by ring
      linarith
    · rw [Set.indicator_of_notMem ht, mul_zero]
      have h2 := hWn j t ht
      rw [min_eq_left h2, min_eq_left (h2.trans (div_le_div_of_nonneg_right (by push_cast; linarith)
        hnR.le))]; simp
  have hlow : ∀ j, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ (j + 1)) ≤ G ⊥ (L j) := by
    intro j
    rw [← spec_G_rat Ψ hadd (χ (j + 1)) hnpos 1 hn1 hn2]
    refine spec_G_bot_mono Ψ hadd fun t => ?_
    simp only [kscale_val, ContinuousMap.smul_apply, smul_eq_mul, hχ, hL, hS]
    by_cases ht : t ∈ closure {t | ((j + 1 : ℕ) : ℝ) / n < (f : C(X, ℝ)) t}
    · rw [Set.indicator_of_mem ht, mul_one]
      have h2 := hWf (j + 1) t ht
      rw [min_eq_right h2, min_eq_right ((div_le_div_of_nonneg_right (by push_cast; linarith)
        hnR.le).trans h2)]
      push_cast; ring_nf; rfl
    · rw [Set.indicator_of_notMem ht, mul_zero]
      linarith [hSmono j t, hS j t, hS (j + 1) t]
  have hsum : ∀ m, G ⊥ (S m) = ∑ j ∈ Finset.range m, G ⊥ (L j) := by
    intro m
    induction m with
    | zero =>
      rw [Finset.sum_range_zero]
      have : S 0 = kzero := kext fun t => by
        rw [hS]; simp [min_eq_right (cIcc_nonneg f t)]
      rw [this, hG0]
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      have := hGadd (b := ⊥) (b' := ⊥) (f := S m) (f' := L m) (k := S (m + 1)) (inf_idem _)
        (fun t => by rw [hL]; ring)
      rwa [sup_idem] at this
  have hSn : S n = f := kext fun t => by
    rw [hS, div_self hnR.ne']; exact min_eq_left (cIcc_le_one f t)
  have hGf : G ⊥ f = ∑ j ∈ Finset.range n, G ⊥ (L j) := by rw [← hSn]; exact hsum n
  set T : GP.Vec E := ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j) with hT
  have hfT : G ⊥ f ≤ T := by rw [hGf]; exact Finset.sum_le_sum fun j _ => hup j
  have hGone : G ⊥ kone ≤ GP.gunit := by
    have := hGadd (b := ⊤) (b' := ⊥) (f := kzero) (f' := kone) (k := kone) (inf_bot_eq _)
      (fun t => by simp)
    rw [sup_bot_eq] at this
    have hu : GP.gunit = G ⊤ kone := by simp only [hG]; rw [hone]; rfl
    rw [hu]; simp only [hG]; rw [this]; exact le_add_of_nonneg_left (GP.gmap_nonneg _)
  have hTf : T - (((1 : ℕ) : ℝ) / n) • GP.gunit ≤ G ⊥ f := by
    have h1 : ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ (j + 1)) ≤ G ⊥ f := by
      rw [hGf]; exact Finset.sum_le_sum fun j _ => hlow j
    have h2 : ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ (j + 1)) =
        T - (((1 : ℕ) : ℝ) / n) • G ⊥ (χ 0) + (((1 : ℕ) : ℝ) / n) • G ⊥ (χ n) := by
      rw [hT]
      have := Finset.sum_range_succ' (fun j => (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j)) n
      have h3 := Finset.sum_range_succ (fun j => (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j)) n
      rw [this] at h3
      rw [eq_sub_of_add_eq h3.symm]; abel
    have h4 : G ⊥ (χ 0) ≤ G ⊥ kone := spec_G_bot_mono Ψ hadd fun t => cIcc_le_one _ t
    calc T - (((1 : ℕ) : ℝ) / n) • GP.gunit ≤ T - (((1 : ℕ) : ℝ) / n) • G ⊥ (χ 0) :=
          sub_le_sub_left (smul_le_smul_of_nonneg_left (h4.trans hGone) hn1) _
      _ ≤ T - (((1 : ℕ) : ℝ) / n) • G ⊥ (χ 0) + (((1 : ℕ) : ℝ) / n) • G ⊥ (χ n) :=
          le_add_of_nonneg_right (smul_nonneg hn1 (hGnn _ _))
      _ = _ := h2.symm
      _ ≤ G ⊥ f := h1
  refine ⟨((1 : ℝ), Ψ b kzero) ::
      (List.range n).map (fun j => ((((1 : ℕ) : ℝ) / n), Ψ ⊥ (χ j))), ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
    rcases hp with rfl | ⟨j, -, rfl⟩
    · exact ⟨spec_idem (b := b) (f := kzero) Ψ hmul (kext fun t => by simp),
        commutes_psi Ψ hmul _ _ _ _⟩
    · exact ⟨spec_idem (b := ⊥) (f := χ j) Ψ hmul (kext fun t => by
        simp only [kmul_val, ContinuousMap.mul_apply, hχ]
        by_cases ht : t ∈ closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t} <;> simp [ht]),
        commutes_psi Ψ hmul _ _ _ _⟩
  · have hsumL : ((((1 : ℝ), Ψ b kzero) ::
        (List.range n).map (fun j => ((((1 : ℕ) : ℝ) / n), Ψ ⊥ (χ j)))).map
          fun p : ℝ × E => p.1 • GP.gmap p.2).sum = G b kzero + T := by
      rw [List.map_cons, List.sum_cons, List.map_map, list_range_map_sum, hT, one_smul]
      rfl
    have e1 : G b f = G b kzero + G ⊥ f := by
      have := hGadd (b := b) (b' := ⊥) (f := kzero) (f' := f) (k := f) (inf_bot_eq _)
        (fun t => by simp)
      rwa [sup_bot_eq] at this
    have hdiff : GP.gmap (Ψ b f) - (G b kzero + T) = G ⊥ f - T := by
      show G b f - _ = _
      rw [e1]; abel
    rw [hsumL, hdiff]
    refine lt_of_le_of_lt (ousNorm_le_rc (by positivity) ?_ ?_) hnε
    · have h := hTf
      rw [Nat.cast_one] at h
      rw [neg_le_sub_iff_le_add]
      exact sub_le_iff_le_add.1 h
    · exact (sub_nonpos.2 hfT).trans (smul_nonneg (by positivity) (GP.gmap_nonneg _))

theorem ulin_nonneg' (q : E) {x : GP.Vec E} (hx : 0 ≤ x) : 0 ≤ ULin hsm q x :=
  gpLift_nonneg _ (ULin_hadd q) (ULin_hsmul hsm q) (fun _ => GP.gmap_nonneg _) hx

theorem ulin_unit (q : E) : ULin hsm q GP.gunit = GP.gmap q := by
  show ULin hsm q (GP.gmap 1) = _
  rw [ULin_gmap, seq_one]

theorem ulin_idem {e : E} (he : Papers.SEA.IsIdempotent e) (x : GP.Vec E) :
    ULin hsm e (ULin hsm e x) = ULin hsm e x := by
  have := gp_linearMap_ext (f := ULin hsm e ∘ₗ ULin hsm e) (g := ULin hsm e) fun b => by
    simp only [LinearMap.comp_apply, ULin_gmap]
    rw [(commutes_refl e).assoc, he]
  exact congrArg (fun φ => φ x) this

theorem ulin_orth_zero {e : E} (he : Papers.SEA.IsIdempotent e) (x : GP.Vec E) :
    ULin hsm e (ULin hsm (orth e) x) = 0 := by
  have := gp_linearMap_ext (f := ULin hsm e ∘ₗ ULin hsm (orth e)) (g := 0) fun b => by
    simp only [LinearMap.comp_apply, ULin_gmap, LinearMap.zero_apply]
    rw [(commutes_orth_self e).assoc, he.seq_orth, zero_seq, GP.gmap_zero]
  exact congrArg (fun φ => φ x) this

theorem ulin_orth_zero' {e : E} (he : Papers.SEA.IsIdempotent e) (x : GP.Vec E) :
    ULin hsm (orth e) (ULin hsm e x) = 0 := by
  have h := ulin_orth_zero hsm he.compl x
  rwa [orth_orth] at h

theorem ulin_one (x : GP.Vec E) : ULin hsm 1 x = x := by
  have := gp_linearMap_ext (f := ULin hsm 1) (g := LinearMap.id) fun b => by
    simp only [ULin_gmap, LinearMap.id_apply, one_seq]
  exact congrArg (fun φ => φ x) this

/-- An idempotent `e` commuting with `y`: `e & y + e⊥ & y = y` in `V`. -/
theorem gmap_split_comm {e y : E} (h : Commutes e y) :
    GP.gmap (e ⊙ y) + GP.gmap (orth e ⊙ y) = GP.gmap y := by
  obtain ⟨h', e'⟩ := seq_split y e
  have h1 : e ⊙ y = y ⊙ e := h
  have h2 : orth e ⊙ y = y ⊙ orth e := h.orth_l
  have hp : Perp (e ⊙ y) (orth e ⊙ y) := by rw [h1, h2]; exact h'
  rw [← GP.gmap_ovee hp]
  congr 1
  exact (PCM.ovee_congr h1 h2 hp h').trans e'

variable [Mul (GP.Vec E)] [hJ : JBAlgebra (GP.Vec E)]
  (hform : ∀ q : E, Papers.SEA.IsIdempotent q → ∀ w : GP.Vec E,
    GP.gmap q * w = (2⁻¹ : ℝ) • (w + (ULin hsm q w - ULin hsm (orth q) w)))

include hform

/-- For an idempotent `e` commuting with `y`: `e * y = e & y`. -/
theorem jmul_comm_idem {e y : E} (he : Papers.SEA.IsIdempotent e) (h : Commutes e y) :
    GP.gmap e * GP.gmap y = GP.gmap (e ⊙ y) := by
  rw [hform e he, ULin_gmap, ULin_gmap, ← gmap_split_comm h]
  module

/-- `e * e = e` for an idempotent `e`. -/
theorem jmul_idem_self {e : E} (he : Papers.SEA.IsIdempotent e) : GP.gmap e * GP.gmap e = GP.gmap e := by
  rw [jmul_comm_idem hsm hform he (commutes_refl e), he]

include hJ in
/-- **Squares agree** (the bridge between the Jordan and the sequential product):
`y * y = y & y` for every effect `y`.  By the commuting spectral approximation: for a
combination `z` of idempotents commuting with `y`, `z * y = y & z`. -/
theorem jsq_gmap (y : E) : GP.gmap y * GP.gmap y = GP.gmap (y ⊙ y) := by
  have hne : ∀ ε : ℝ, 0 < ε → ousNorm (GP.Vec E) (GP.gmap y * GP.gmap y - GP.gmap (y ⊙ y)) ≤
      ε * (ousNorm (GP.Vec E) (GP.gmap y) + 1) := by
    intro ε hε
    obtain ⟨l, hl, hn⟩ := spec_comm_approx y hε
    set z := (l.map fun p => p.1 • GP.gmap p.2).sum with hz
    have hzy : z * GP.gmap y = ULin hsm y z := by
      rw [hz]
      clear hn hz
      induction l with
      | nil => simp [jb_zero_mul]
      | cons p l ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [JBAlgebra.add_mul, JBAlgebra.smul_mul, map_add, map_smul,
          jmul_comm_idem hsm hform (hl p (List.mem_cons_self)).1 (hl p (List.mem_cons_self)).2,
          ULin_gmap, (hl p (List.mem_cons_self)).2,
          ih fun q hq => hl q (List.mem_cons_of_mem _ hq)]
    have e : GP.gmap y * GP.gmap y - GP.gmap (y ⊙ y) =
        (GP.gmap y - z) * GP.gmap y + ULin hsm y (z - GP.gmap y) := by
      rw [jb_sub_mul, hzy, map_sub, ULin_gmap]; abel
    rw [e]
    refine (ousNorm_add_le _ _).trans ?_
    have h1 := jb_norm_mul_le (GP.gmap y - z) (GP.gmap y)
    have h2 : ousNorm (GP.Vec E) (ULin hsm y (z - GP.gmap y)) ≤
        ousNorm (GP.Vec E) (z - GP.gmap y) :=
      contraction_of_pos (fun v hv => ulin_nonneg' hsm y hv)
        (by rw [show ouUnit (GP.Vec E) = GP.gunit from rfl, ulin_unit]; exact GP.gmap_le_gunit y) _
    rw [ousNorm_sub_comm] at h2
    have h0 := ousNorm_nonneg_rc (GP.gmap y)
    have : ousNorm (GP.Vec E) (GP.gmap y - z) * ousNorm (GP.Vec E) (GP.gmap y) ≤
        ε * ousNorm (GP.Vec E) (GP.gmap y) := mul_le_mul_of_nonneg_right hn.le h0
    nlinarith
  refine sub_eq_zero.1 (eq_zero_of_ousNorm_small fun ε hε => ?_)
  have h0 := ousNorm_nonneg_rc (GP.gmap y)
  have := hne (ε / (ousNorm (GP.Vec E) (GP.gmap y) + 1)) (by positivity)
  rwa [div_mul_cancel₀ _ (by positivity)] at this

include hJ in
/-- A Jordan idempotent of `V` is (the image of) an idempotent of the SEA. -/
theorem jidem_gmap {v : GP.Vec E} (hv : v * v = v) : ∃ y : E, Papers.SEA.IsIdempotent y ∧ v = GP.gmap y := by
  have h0 : 0 ≤ v := hv ▸ jb_sq_nonneg v
  have h1 : v ≤ GP.gunit := by
    have e : (GP.gunit - v) * (GP.gunit - v) = GP.gunit - v := by
      rw [jb_sub_mul, jb_mul_sub, jb_mul_sub, hv]
      rw [show (GP.gunit : GP.Vec E) = ouUnit (GP.Vec E) from rfl, JBAlgebra.mul_one,
        JBAlgebra.one_mul, JBAlgebra.mul_one]
      abel
    have := jb_sq_nonneg (GP.gunit - v)
    rw [e] at this; exact sub_nonneg.1 this
  obtain ⟨y, rfl⟩ := GP.gmap_surjective_Icc ⟨h0, h1⟩
  refine ⟨y, GP.gmap_injective ?_, rfl⟩
  rw [← jsq_gmap hsm hform y, hv]

/-- `Q_e = e & –` for an idempotent `e`. -/
theorem jQ_idem {e : E} (he : Papers.SEA.IsIdempotent e) (w : GP.Vec E) :
    jQ (GP.gmap e) w = ULin hsm e w := by
  unfold jQ
  rw [jmul_idem_self hsm hform he, hform e he (GP.gmap e * w), hform e he w]
  simp only [map_add, map_sub, map_smul, ulin_idem hsm he, ulin_orth_zero hsm he,
    ulin_orth_zero' hsm he, ulin_idem hsm he.compl]
  module

end SeqJordan

/-! ## Density: linear maps vanishing on idempotents -/

section Density

open Papers.SEA
open scoped Papers.SEA

variable {E : Type u} [EffectAlgebra E] [NormalSEA E] [EffectModule I E]
  {W : Type w} [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W] [IsOUS W]

/-- A bounded linear map out of `V = GP.Vec E` that vanishes on the idempotents vanishes
(the idempotents span a norm-dense subspace, REC 58). -/
theorem linear_eq_zero_of_idem (h : GP.Vec E →ₗ[ℝ] W) (K : ℝ)
    (hK : ∀ x, ousNorm W (h x) ≤ K * ousNorm (GP.Vec E) x)
    (h0 : ∀ e : E, Papers.SEA.IsIdempotent e → h (GP.gmap e) = 0) (x : GP.Vec E) : h x = 0 := by
  refine eq_zero_of_ousNorm_small fun ε hε => ?_
  obtain ⟨l, hl, hn⟩ := spectral_dense x (ε := ε / (|K| + 1)) (by positivity)
  have hs : h (l.map fun p => p.1 • GP.gmap p.2).sum = 0 := by
    clear hn
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.sum_cons, map_add, map_smul, h0 p.2 (hl p List.mem_cons_self),
        smul_zero, zero_add]
      exact ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
  have e : h x = h (x - (l.map fun p => p.1 • GP.gmap p.2).sum) := by rw [map_sub, hs, sub_zero]
  rw [e]
  refine (hK _).trans ?_
  have h1 := ousNorm_nonneg_rc (x - (l.map fun p => p.1 • GP.gmap p.2).sum)
  calc K * ousNorm (GP.Vec E) (x - _) ≤ |K| * ousNorm (GP.Vec E) (x - _) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) h1
    _ ≤ |K| * (ε / (|K| + 1)) := mul_le_mul_of_nonneg_left hn.le (abs_nonneg K)
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith [abs_nonneg K]

end Density

/-! ## Monoidal effectuses: the tensor of predicates (REC 28, 29) -/

section UnitHelpers

open MonoidalCategory

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- The multiplication `X ⊗ X → X` of the tensor unit, transported along `𝟙_ = X`. -/
def muOf (X : D) (hX : 𝟙_ D = X) : X ⊗ X ⟶ X :=
  eqToHom (congrArg (fun Y => Y ⊗ X) hX.symm) ≫ (λ_ X).hom

instance muOf_isIso (X : D) (hX : 𝟙_ D = X) : IsIso (muOf X hX) := by
  unfold muOf; infer_instance

theorem muOf_right (X : D) (hX : 𝟙_ D = X) (s : X ⟶ X) :
    (𝟙 X ⊗ₘ s) ≫ muOf X hX = muOf X hX ≫ s := by
  subst hX
  simp only [muOf, eqToHom_refl, Category.id_comp, id_tensorHom]
  exact leftUnitor_naturality s

theorem muOf_left (X : D) (hX : 𝟙_ D = X) (s : X ⟶ X) :
    (s ⊗ₘ 𝟙 X) ≫ muOf X hX = muOf X hX ≫ s := by
  subst hX
  simp only [muOf, eqToHom_refl, Category.id_comp, tensorHom_id]
  rw [unitors_equal]
  exact rightUnitor_naturality s

theorem muOf_scalars (X : D) (hX : 𝟙_ D = X) (s t : X ⟶ X) :
    inv (muOf X hX) ≫ (s ⊗ₘ t) ≫ muOf X hX = s ≫ t := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc]
  rw [show s ▷ X ≫ X ◁ t ≫ muOf X hX = (s ⊗ₘ 𝟙 X) ≫ (𝟙 X ⊗ₘ t) ≫ muOf X hX by
    simp [id_tensorHom, tensorHom_id]]
  rw [muOf_right]
  rw [← Category.assoc (s ⊗ₘ 𝟙 X), muOf_left, Category.assoc, IsIso.inv_hom_id_assoc]

/-- `ρ_A ∘ (A ⊗ eqToHom)` matches `muOf` after tensoring a predicate. -/
theorem rho_muOf (X : D) (hX : 𝟙_ D = X) {A : D} (a : A ⟶ X) :
    (A ◁ eqToHom hX.symm) ≫ (ρ_ A).hom ≫ a = (a ⊗ₘ 𝟙 X) ≫ muOf X hX := by
  subst hX
  simp only [muOf, eqToHom_refl, Category.id_comp, MonoidalCategory.whiskerLeft_id,
    tensorHom_id]
  rw [unitors_equal]
  exact (rightUnitor_naturality a).symm

section Braided

variable [BraidedCategory D]

theorem muOf_braiding (X : D) (hX : 𝟙_ D = X) : (β_ X X).hom ≫ muOf X hX = muOf X hX := by
  subst hX
  simp only [muOf, eqToHom_refl, Category.id_comp]
  rw [braiding_leftUnitor, unitors_equal]

end Braided

end UnitHelpers

section MonoidalPred

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]

/-- `μ : I ⊗ I → I` (REC 28 identifies the tensor unit with the effect object). -/
noncomputable def muI : effObj C ⊗ effObj C ⟶ effObj C :=
  muOf (effObj C) (MonoidalEffectus.unit_eq (C := C))

/-- The tensor `p ⊗ q := μ ∘ (p ⊗ q) : A ⊗ B → I` of predicates (the paper's `p ⊗ q`,
with REC 28's identification of `I ⊗ I` with `I`). -/
instance muI_isIso : IsIso (muI (C := C)) := muOf_isIso _ _

noncomputable def ptens {A B : C} (p : Pred A) (q : Pred B) : Pred (A ⊗ B) := (p ⊗ₘ q) ≫ muI

theorem ptens_truth (A B : C) : ptens (truth A) (truth B) = truth (A ⊗ B) := by
  have := MonoidalEffectus.truth_tensor (C := C) A B
  rw [← this]; rfl

theorem tensor_comp_ptens {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') (p : Pred A') (q : Pred B') :
    (f ⊗ₘ g) ≫ ptens p q = ptens (f ≫ p) (g ≫ q) := by
  rw [ptens, ptens, ← Category.assoc, tensorHom_comp_tensorHom]

theorem ptens_comm {A B : C} (p : Pred A) (q : Pred B) :
    (β_ A B).hom ≫ ptens q p = ptens p q := by
  rw [ptens, ptens, ← Category.assoc, ← BraidedCategory.braiding_naturality, Category.assoc]
  congr 1
  exact muOf_braiding _ _

theorem ptens_ovee_left {A B : C} {p p' : Pred A} (h : Perp p p') (q : Pred B) :
    ∃ h' : Perp (ptens p q) (ptens p' q), ptens (ovee p p' h) q = ovee (ptens p q) (ptens p' q) h' := by
  obtain ⟨h1, e1⟩ := MonoidalEffectus.ovee_tensor h q
  obtain ⟨h2, e2⟩ := FinPAC.comp_ovee h1 muI
  exact ⟨h2, by rw [ptens, e1, e2]; rfl⟩

theorem ptens_ovee_right {A B : C} (p : Pred A) {q q' : Pred B} (h : Perp q q') :
    ∃ h' : Perp (ptens p q) (ptens p q'), ptens p (ovee q q' h) = ovee (ptens p q) (ptens p q') h' := by
  obtain ⟨h1, e1⟩ := ptens_ovee_left h p
  obtain ⟨h2, e2⟩ := FinPAC.ovee_comp h1 (β_ A B).hom
  refine ⟨by rw [← ptens_comm p q, ← ptens_comm p q']; exact h2, ?_⟩
  rw [← ptens_comm p (ovee q q' h), e1, e2]
  exact PCM.ovee_congr (ptens_comm p q) (ptens_comm p q') _ _

theorem ptens_zero_left {A B : C} (q : Pred B) : ptens (0 : Pred A) q = 0 := by
  rw [ptens, MonoidalEffectus.zero_tensor, FinPAC.zero_comp]

theorem ptens_zero_right {A B : C} (p : Pred A) : ptens p (0 : Pred B) = 0 := by
  rw [← ptens_comm, ptens_zero_left, FinPAC.comp_zero]

theorem ptens_scal_right {A B : C} (p : Pred A) (q : Pred B) (s : Scal C) :
    ptens p (q ≫ s) = ptens p q ≫ s := by
  rw [ptens, ptens, show q ≫ s = q ≫ s from rfl, ← Category.comp_id p, ← tensorHom_comp_tensorHom,
    Category.assoc, muI, muOf_right, Category.comp_id, Category.assoc]

theorem ptens_scal_left {A B : C} (p : Pred A) (q : Pred B) (s : Scal C) :
    ptens (p ≫ s) q = ptens p q ≫ s := by
  rw [← ptens_comm, ptens_scal_right, ← Category.assoc, ptens_comm]

/-- The product of two states: `Ω = (ω ⊗ ω') ∘ μ⁻¹ : I → A ⊗ B`, with
`(p ⊗ q) ∘ Ω = (p ∘ ω) · (q ∘ ω')`. -/
noncomputable def stateTensor {A B : C} (ω : effObj C ⟶ A) (ω' : effObj C ⟶ B) :
    effObj C ⟶ A ⊗ B :=
  inv muI ≫ (ω ⊗ₘ ω')

theorem stateTensor_ptens {A B : C} (ω : effObj C ⟶ A) (ω' : effObj C ⟶ B) (p : Pred A)
    (q : Pred B) : stateTensor ω ω' ≫ ptens p q = (ω ≫ p) ≫ (ω' ≫ q) := by
  rw [stateTensor, Category.assoc, tensor_comp_ptens, ptens]
  exact muOf_scalars _ _ _ _

theorem stateTensor_total {A B : C} (ω : Stat A) (ω' : Stat B) :
    IsTotal (stateTensor ω.1 ω'.1) := by
  show stateTensor ω.1 ω'.1 ≫ truth (A ⊗ B) = truth (effObj C)
  rw [← ptens_truth, stateTensor_ptens, ω.2, ω'.2, truth_effObj_eq_id, Category.id_comp]

end MonoidalPred

/-! ## REC 122: monoidal sequential effectuses -/

section Rec122

open MonoidalCategory

variable (C : Type u) [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]

/-- **REC 122** (short.tex:2270, Definition): a **monoidal sequential effectus** is a
sequential effectus (REC 100) that is monoidal (REC 28) such that the tensor product
of two pure maps is pure and, for pure `f` and `g`, `(f ⊗ g)† = f† ⊗ g†`.  (A mixin
over `SequentialEffectus` and `MonoidalEffectus`.) -/
class MonoidalSequentialEffectus : Prop where
  pure_tensor : ∀ {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}, IsPure f → IsPure g →
    IsPure (f ⊗ₘ g)
  dag_tensor : ∀ {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}, IsPure f → IsPure g →
    SequentialEffectus.dag (f ⊗ₘ g) = SequentialEffectus.dag f ⊗ₘ SequentialEffectus.dag g

end Rec122

section Rec123

open MonoidalCategory SequentialEffectus

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C] [MonoidalSequentialEffectus C]

/-- Square roots for the sequential product (SEA 37, discharged in `Papers.SEA.Discharge`). -/
theorem exists_seq_sqrt {A : C} (a : Pred A) : ∃ r : Pred A, asrtS r ≫ asrtS r = asrtS a := by
  obtain ⟨r, hr, -⟩ := Papers.SEA.sea37_sqrt_unconditional a
  refine ⟨r, ?_⟩
  rw [rec108]
  congr 1

/-- **REC 123** (`prop:JBW-tensor-preserves-assert`, short.tex:2288, Proposition):
`asrt_{a⊗b} = asrt_a ⊗ asrt_b`.  The paper's proof: `1 ∘ (asrt_a ⊗ asrt_b) = a ⊗ b`,
and `asrt_a ⊗ asrt_b = (asrt_√a ⊗ asrt_√b)† ∘ (asrt_√a ⊗ asrt_√b)` is `†`-positive
(REC 122; `√a` by SEA 37), so it is the unique assert map of `a ⊗ b` (REC 100,
axiom 5). -/
theorem rec123 {A B : C} (a : Pred A) (b : Pred B) :
    asrtS (ptens a b) = asrtS a ⊗ₘ asrtS b := by
  obtain ⟨r, hr⟩ := exists_seq_sqrt a
  obtain ⟨t, ht⟩ := exists_seq_sqrt b
  refine (asrtS_unique (MonoidalSequentialEffectus.pure_tensor (isPure_asrtS a) (isPure_asrtS b))
    ⟨A ⊗ B, asrtS r ⊗ₘ asrtS t, MonoidalSequentialEffectus.pure_tensor (isPure_asrtS r)
      (isPure_asrtS t), ?_⟩ ?_).symm
  · rw [MonoidalSequentialEffectus.dag_tensor (isPure_asrtS r) (isPure_asrtS t), dag_asrtS,
      dag_asrtS, tensorHom_comp_tensorHom, hr, ht]
  · rw [← ptens_truth, tensor_comp_ptens, asrtS_truth, asrtS_truth]

/-- **REC 123**, "in particular": `asrt_{a⊗1} = asrt_a ⊗ id` and `(a ⊗ b)² = a² ⊗ b²`. -/
theorem rec123_particular {A B : C} (a : Pred A) (b : Pred B) :
    asrtS (ptens a (truth B)) = asrtS a ⊗ₘ 𝟙 B ∧
      SEA.seq (ptens a b) (ptens a b) = ptens (SEA.seq a a) (SEA.seq b b) := by
  refine ⟨by rw [rec123]; congr 1; exact asrtS_one B, ?_⟩
  rw [seq_eq, seq_eq, seq_eq, rec123, tensor_comp_ptens]

/-- **REC 124** (`cor:tensor-idempotents`, short.tex:2299, Corollary): the tensor of sharp
predicates is sharp. -/
theorem rec124 {A B : C} {p : Pred A} {q : Pred B} (hp : IsSharp p) (hq : IsSharp q) :
    IsSharp (ptens p q) := by
  apply isSharp_of_isIdempotent
  show SEA.seq (ptens p q) (ptens p q) = ptens p q
  rw [(rec123_particular p q).2]
  have h1 : SEA.seq p p = p := isIdempotent_of_isSharp hp
  have h2 : SEA.seq q q = q := isIdempotent_of_isSharp hq
  rw [h1, h2]

end Rec123

/-! ## The bilinear map `⊗ : V_A × V_B → V_{A⊗B}` (§6, running text) -/

section VTensor

open MonoidalCategory SequentialEffectus

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  (σs : ScalarSplit C)

/-- The tensor of two elements of the convex parts. -/
noncomputable def cptTens {A B : C} (p : CPt σs A) (q : CPt σs B) : CPt σs (A ⊗ B) :=
  cptMk σs (ptens p.1 q.1) (by rw [← ptens_scal_left, p.2])

@[simp] theorem cptTens_val {A B : C} (p : CPt σs A) (q : CPt σs B) :
    (cptTens σs p q).1 = ptens p.1 q.1 := rfl

theorem vtensL_hadd {A B : C} (q : CPt σs B) {a b : CPt σs A} (h : Perp a b) :
    GP.gmap (cptTens σs (ovee a b h) q) = GP.gmap (cptTens σs a q) + GP.gmap (cptTens σs b q) := by
  obtain ⟨h', e⟩ := ptens_ovee_left (show Perp a.1 b.1 from h) q.1
  have hp : Perp (cptTens σs a q) (cptTens σs b q) := h'
  rw [← GP.gmap_ovee hp]; congr 1; exact Subtype.ext e

theorem vtensL_hsmul {A B : C} (q : CPt σs B) (l : I) (a : CPt σs A) :
    GP.gmap (cptTens σs (l • a) q) = (l : ℝ) • GP.gmap (cptTens σs a q) := by
  rw [← GP.gmap_smul]; congr 1; apply Subtype.ext
  show ptens (a.1 ≫ σs.c l) q.1 = ptens a.1 q.1 ≫ σs.c l
  exact ptens_scal_left _ _ _

/-- `a ↦ a ⊗ q` on `V_A`. -/
noncomputable def vtensL {A B : C} (q : CPt σs B) : VA σs A →ₗ[ℝ] VA σs (A ⊗ B) :=
  gpLift (fun a : CPt σs A => GP.gmap (cptTens σs a q)) (vtensL_hadd σs q) (vtensL_hsmul σs q)

theorem vtensL_gmap {A B : C} (q : CPt σs B) (a : CPt σs A) :
    vtensL σs q (GP.gmap a) = GP.gmap (cptTens σs a q) :=
  gpLift_gmap _ (vtensL_hadd σs q) (vtensL_hsmul σs q) a

theorem vtens_hadd {A B : C} {q q' : CPt σs B} (h : Perp q q') :
    (vtensL σs (A := A) (ovee q q' h)) = vtensL σs q + vtensL σs q' :=
  gp_linearMap_ext fun a => by
    rw [LinearMap.add_apply, vtensL_gmap, vtensL_gmap, vtensL_gmap]
    obtain ⟨h', e⟩ := ptens_ovee_right a.1 (show Perp q.1 q'.1 from h)
    have hp : Perp (cptTens σs a q) (cptTens σs a q') := h'
    rw [← GP.gmap_ovee hp]; congr 1; exact Subtype.ext e

theorem vtens_hsmul {A B : C} (l : I) (q : CPt σs B) :
    (vtensL σs (A := A) (l • q)) = (l : ℝ) • vtensL σs q :=
  gp_linearMap_ext fun a => by
    rw [LinearMap.smul_apply, vtensL_gmap, vtensL_gmap, ← GP.gmap_smul]
    congr 1; apply Subtype.ext
    show ptens a.1 (q.1 ≫ σs.c l) = ptens a.1 q.1 ≫ σs.c l
    exact ptens_scal_right _ _ _

/-- The bilinear map `⊗ : V_A × V_B → V_{A⊗B}` of §6 ("As a result we get a bilinear
positive unital map `V_A × V_B → V_{A⊗B}`"), curried. -/
noncomputable def vtens {A B : C} : VA σs B →ₗ[ℝ] (VA σs A →ₗ[ℝ] VA σs (A ⊗ B)) :=
  gpLift (fun q : CPt σs B => vtensL σs (A := A) q) (vtens_hadd σs) (vtens_hsmul σs)

/-- `a ⊗ b` in `V_{A⊗B}`. -/
noncomputable def tensV {A B : C} (a : VA σs A) (b : VA σs B) : VA σs (A ⊗ B) := vtens σs b a

theorem tensV_gmap {A B : C} (p : CPt σs A) (q : CPt σs B) :
    tensV σs (GP.gmap p) (GP.gmap q) = GP.gmap (cptTens σs p q) := by
  unfold tensV vtens
  rw [gpLift_gmap _ (vtens_hadd σs) (vtens_hsmul σs), vtensL_gmap]

theorem tensV_add_left {A B : C} (a a' : VA σs A) (b : VA σs B) :
    tensV σs (a + a') b = tensV σs a b + tensV σs a' b := map_add _ _ _

theorem tensV_add_right {A B : C} (a : VA σs A) (b b' : VA σs B) :
    tensV σs a (b + b') = tensV σs a b + tensV σs a b' := by
  unfold tensV; rw [map_add, LinearMap.add_apply]

theorem tensV_smul_left {A B : C} (r : ℝ) (a : VA σs A) (b : VA σs B) :
    tensV σs (r • a) b = r • tensV σs a b := map_smul _ _ _

theorem tensV_smul_right {A B : C} (r : ℝ) (a : VA σs A) (b : VA σs B) :
    tensV σs a (r • b) = r • tensV σs a b := by
  unfold tensV; rw [map_smul, LinearMap.smul_apply]

theorem tensV_sub_left {A B : C} (a a' : VA σs A) (b : VA σs B) :
    tensV σs (a - a') b = tensV σs a b - tensV σs a' b := map_sub _ _ _

theorem tensV_sub_right {A B : C} (a : VA σs A) (b b' : VA σs B) :
    tensV σs a (b - b') = tensV σs a b - tensV σs a b' := by
  unfold tensV; rw [map_sub, LinearMap.sub_apply]

theorem tensV_zero_left {A B : C} (b : VA σs B) : tensV σs (0 : VA σs A) b = 0 := map_zero _

theorem tensV_zero_right {A B : C} (a : VA σs A) : tensV σs a (0 : VA σs B) = 0 := by
  unfold tensV; rw [map_zero, LinearMap.zero_apply]

theorem gp_nonneg_repr {E : Type u} [EffectAlgebra E] [EffectModule I E] {x : GP.Vec E}
    (hx : 0 ≤ x) : ∃ (r : ℝ) (a : E), 0 ≤ r ∧ x = r • GP.gmap a := by
  obtain ⟨p, rfl⟩ := GP.Vec.exists_of_zero_le hx
  obtain ⟨r, a, rfl⟩ := GP.Cone.exists_mk p
  exact ⟨r, a, r.2, (gp_rsmul_gmap r a).symm⟩

theorem tensV_nonneg {A B : C} {a : VA σs A} {b : VA σs B} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ tensV σs a b := by
  obtain ⟨r, x, hr, rfl⟩ := gp_nonneg_repr ha
  obtain ⟨t, y, ht, rfl⟩ := gp_nonneg_repr hb
  rw [tensV_smul_left, tensV_smul_right, tensV_gmap]
  exact smul_nonneg hr (smul_nonneg ht (GP.gmap_nonneg _))

theorem cptTens_one {A B : C} : cptTens σs (1 : CPt σs A) (1 : CPt σs B) = 1 := by
  apply Subtype.ext
  show ptens (truth A ≫ orth σs.s) (truth B ≫ orth σs.s) = truth (A ⊗ B) ≫ orth σs.s
  rw [ptens_scal_left, ptens_scal_right, ptens_truth, Category.assoc,
    show orth σs.s ≫ orth σs.s = orth σs.s from orth_idem σs.hs]

/-- `1 ⊗ 1 = 1` (REC 28). -/
theorem tensV_unit {A B : C} :
    tensV σs (ouUnit (VA σs A)) (ouUnit (VA σs B)) = ouUnit (VA σs (A ⊗ B)) := by
  show tensV σs (GP.gmap 1) (GP.gmap 1) = GP.gmap 1
  rw [tensV_gmap, cptTens_one]

/-- `Pred(f ⊗ g)(a ⊗ b) = Pred(f)(a) ⊗ Pred(g)(b)`. -/
theorem stateLin_tensor {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') (a : VA σs A')
    (b : VA σs B') :
    stateLin σs (f ⊗ₘ g) (tensV σs a b) = tensV σs (stateLin σs f a) (stateLin σs g b) := by
  have key : (vtens σs (A := A') (B := B')).compr₂ (stateLin σs (f ⊗ₘ g)) =
      ((vtens σs (A := A) (B := B)).comp (stateLin σs g)).compl₂ (stateLin σs f) :=
    gp_linearMap_ext fun q => gp_linearMap_ext fun p => by
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply]
      rw [stateLin_gmap, stateLin_gmap]
      change stateLin σs (f ⊗ₘ g) (tensV σs (GP.gmap p) (GP.gmap q)) =
        tensV σs (GP.gmap _) (GP.gmap _)
      rw [tensV_gmap, tensV_gmap, stateLin_gmap]
      congr 1; apply Subtype.ext
      exact tensor_comp_ptens f g p.1 q.1
  exact LinearMap.congr_fun (LinearMap.congr_fun key b) a

/-- `‖a ⊗ b‖ ≤ ‖a‖ ‖b‖`: `⊗` is a positive bilinear map with `1 ⊗ 1 = 1`. -/
theorem tensV_norm_le {A B : C} (a : VA σs A) (b : VA σs B) :
    ousNorm (VA σs (A ⊗ B)) (tensV σs a b) ≤ ousNorm (VA σs A) a * ousNorm (VA σs B) b := by
  have := VA_isOUS σs A
  have := VA_isOUS σs B
  have half : ∀ w : VA σs (A ⊗ B), 0 ≤ (2 : ℝ) • w → 0 ≤ w := fun w h => by
    have := smul_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) h
    rwa [_root_.smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at this
  set x := ousNorm (VA σs A) a
  set y := ousNorm (VA σs B) b
  obtain ⟨a1, a2⟩ := ousNorm_bounds_le a
  obtain ⟨b1, b2⟩ := ousNorm_bounds_le b
  have pa : 0 ≤ x • ouUnit (VA σs A) + a := by
    have := sub_nonneg.2 a1; rwa [sub_neg_eq_add, add_comm] at this
  have ma : 0 ≤ x • ouUnit (VA σs A) - a := sub_nonneg.2 a2
  have pb : 0 ≤ y • ouUnit (VA σs B) + b := by
    have := sub_nonneg.2 b1; rwa [sub_neg_eq_add, add_comm] at this
  have mb : 0 ≤ y • ouUnit (VA σs B) - b := sub_nonneg.2 b2
  have e1 := tensV_nonneg σs pa mb
  have e2 := tensV_nonneg σs ma pb
  have e3 := tensV_nonneg σs pa pb
  have e4 := tensV_nonneg σs ma mb
  simp only [tensV_add_left, tensV_add_right, tensV_sub_left, tensV_sub_right, tensV_smul_left,
    tensV_smul_right, tensV_unit] at e1 e2 e3 e4
  have hx := ousNorm_nonneg_rc a
  have hy := ousNorm_nonneg_rc b
  refine ousNorm_le_rc (mul_nonneg hx hy) ?_ ?_
  · have h : 0 ≤ (2 : ℝ) • ((x * y) • ouUnit (VA σs (A ⊗ B)) + tensV σs a b) := by
      have := add_nonneg e3 e4
      convert this using 1; module
    have := half _ h
    calc -((x * y) • ouUnit (VA σs (A ⊗ B))) = -((x * y) • ouUnit (VA σs (A ⊗ B))) + 0 := by
          abel
      _ ≤ -((x * y) • ouUnit (VA σs (A ⊗ B))) +
          ((x * y) • ouUnit (VA σs (A ⊗ B)) + tensV σs a b) := add_le_add_right this _
      _ = tensV σs a b := by abel
  · have h : 0 ≤ (2 : ℝ) • ((x * y) • ouUnit (VA σs (A ⊗ B)) - tensV σs a b) := by
      have := add_nonneg e1 e2
      convert this using 1; module
    exact sub_nonneg.1 (half _ h)

end VTensor

/-! ## The Jordan product of `V_A` (REC 121) and the tensor: REC 125–127 -/

section JordanVA

open MonoidalCategory SequentialEffectus
open scoped Papers.SEA

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (σs : ScalarSplit C) (hAS : AlfsenShultzJordanFromDerivations.{v})
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

/-- The Jordan product `x * y` of `V_A` (REC 121's `jbMul`). -/
noncomputable def jm (A : C) (x y : VA σs A) : VA σs A :=
  @HMul.hMul _ _ _ (@instHMul _ (jbMul σs hAS hRC h119 A)) x y

/-- The quadratic map `Q_a` of `V_A`. -/
noncomputable def jQA (A : C) (a b : VA σs A) : VA σs A :=
  @jQ (VA σs A) _ _ (jbMul σs hAS hRC h119 A) a b

theorem jm_jb (A : C) : @JBAlgebra (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A) :=
  jbMul_spec σs hAS hRC h119 A

/-- `Uop p = Pred(asrt_p)` on `V_A`. -/
theorem Uop_eq_stateLin {A : C} (p : CPt σs A) : Uop σs p = stateLin σs (asrtS p.1) :=
  gp_linearMap_ext fun b => by
    rw [Uop_gmap, stateLin_gmap]; congr 1; apply Subtype.ext
    show SEA.seq p.1 b.1 = asrtS p.1 ≫ b.1
    exact seq_eq _ _

/-- REC 121's formula `e * w = ½ (w + e & w − e⊥ & w)` for idempotent `e`. -/
theorem jm_form (A : C) (q : CPt σs A) (hq : Papers.SEA.IsIdempotent q) (w : VA σs A) :
    jm σs hAS hRC h119 A (GP.gmap q) w =
      (2⁻¹ : ℝ) • (w + (ULin (cpt_hsm σs A) q w - ULin (cpt_hsm σs A) (orth q) w)) := by
  have := (rec121 σs hAS hRC h119 A).choose_spec.2 q
    (isSharp_of_isIdempotent ((cpt_idem_iff σs q).1 hq)) w
  exact this

theorem jm_add_left (A : C) (x x' y : VA σs A) :
    jm σs hAS hRC h119 A (x + x') y = jm σs hAS hRC h119 A x y + jm σs hAS hRC h119 A x' y :=
  (jm_jb σs hAS hRC h119 A).add_mul x x' y

theorem jm_smul_left (A : C) (r : ℝ) (x y : VA σs A) :
    jm σs hAS hRC h119 A (r • x) y = r • jm σs hAS hRC h119 A x y :=
  (jm_jb σs hAS hRC h119 A).smul_mul r x y

theorem jm_comm (A : C) (x y : VA σs A) :
    jm σs hAS hRC h119 A x y = jm σs hAS hRC h119 A y x :=
  (jm_jb σs hAS hRC h119 A).mul_comm x y

theorem jm_add_right (A : C) (x y y' : VA σs A) :
    jm σs hAS hRC h119 A x (y + y') = jm σs hAS hRC h119 A x y + jm σs hAS hRC h119 A x y' := by
  rw [jm_comm, jm_add_left, jm_comm, jm_comm σs hAS hRC h119 A y']

theorem jm_smul_right (A : C) (r : ℝ) (x y : VA σs A) :
    jm σs hAS hRC h119 A x (r • y) = r • jm σs hAS hRC h119 A x y := by
  rw [jm_comm, jm_smul_left, jm_comm]

theorem jm_sub_left (A : C) (x x' y : VA σs A) :
    jm σs hAS hRC h119 A (x - x') y = jm σs hAS hRC h119 A x y - jm σs hAS hRC h119 A x' y := by
  rw [sub_eq_add_neg, jm_add_left, ← neg_one_smul ℝ x', jm_smul_left]; simp [sub_eq_add_neg]

theorem jm_sub_right (A : C) (x y y' : VA σs A) :
    jm σs hAS hRC h119 A x (y - y') = jm σs hAS hRC h119 A x y - jm σs hAS hRC h119 A x y' := by
  rw [jm_comm, jm_sub_left, jm_comm, jm_comm σs hAS hRC h119 A y']

theorem jm_unit (A : C) (x : VA σs A) : jm σs hAS hRC h119 A (ouUnit (VA σs A)) x = x :=
  (jm_jb σs hAS hRC h119 A).one_mul x

theorem jm_norm_le (A : C) (x y : VA σs A) :
    ousNorm (VA σs A) (jm σs hAS hRC h119 A x y) ≤ ousNorm (VA σs A) x * ousNorm (VA σs A) y :=
  @jb_norm_mul_le _ _ _ _ _ (jbMul σs hAS hRC h119 A) (jm_jb σs hAS hRC h119 A) x y

/-- The Jordan product as a linear map in its second argument. -/
noncomputable def jmT (A : C) (x : VA σs A) : VA σs A →ₗ[ℝ] VA σs A where
  toFun := jm σs hAS hRC h119 A x
  map_add' := jm_add_right σs hAS hRC h119 A x
  map_smul' r y := jm_smul_right σs hAS hRC h119 A r x y

/-- The Jordan product as a linear map in its first argument. -/
noncomputable def jmL (A : C) (y : VA σs A) : VA σs A →ₗ[ℝ] VA σs A where
  toFun x := jm σs hAS hRC h119 A x y
  map_add' x x' := jm_add_left σs hAS hRC h119 A x x' y
  map_smul' r x := jm_smul_left σs hAS hRC h119 A r x y

theorem jm_sq_gmap (A : C) (y : CPt σs A) :
    jm σs hAS hRC h119 A (GP.gmap y) (GP.gmap y) = GP.gmap (y ⊙ y) :=
  @jsq_gmap (CPt σs A) _ _ _ (cpt_hsm σs A) (jbMul σs hAS hRC h119 A) (jm_jb σs hAS hRC h119 A)
    (jm_form σs hAS hRC h119 A) y

theorem jm_idem_gmap (A : C) {x : VA σs A} (hx : jm σs hAS hRC h119 A x x = x) :
    ∃ y : CPt σs A, Papers.SEA.IsIdempotent y ∧ x = GP.gmap y :=
  @jidem_gmap (CPt σs A) _ _ _ (cpt_hsm σs A) (jbMul σs hAS hRC h119 A) (jm_jb σs hAS hRC h119 A)
    (jm_form σs hAS hRC h119 A) x hx

theorem jQA_idem (A : C) {e : CPt σs A} (he : Papers.SEA.IsIdempotent e) (w : VA σs A) :
    jQA σs hAS hRC h119 A (GP.gmap e) w = Uop σs e w :=
  @jQ_idem (CPt σs A) _ _ _ (cpt_hsm σs A) (jbMul σs hAS hRC h119 A) (jm_jb σs hAS hRC h119 A)
    (jm_form σs hAS hRC h119 A) e he w

theorem ousNorm_unit_le' (A : C) : ousNorm (VA σs A) (ouUnit (VA σs A)) ≤ 1 :=
  ousNorm_le_rc zero_le_one (by rw [one_smul]; exact neg_le_self ou_unit_nonneg)
    (by rw [one_smul])

/-- A linear map out of `V_A` that is bounded and vanishes on the idempotents is zero. -/
theorem va_eq_zero_of_idem {A B : C} (h : VA σs A →ₗ[ℝ] VA σs B) (K : ℝ)
    (hK : ∀ x, ousNorm (VA σs B) (h x) ≤ K * ousNorm (VA σs A) x)
    (h0 : ∀ e : CPt σs A, Papers.SEA.IsIdempotent e → h (GP.gmap e) = 0) (x : VA σs A) : h x = 0 :=
  @linear_eq_zero_of_idem (CPt σs A) _ _ _ (VA σs B) _ _ _ _ (VA_isOUS σs B) h K hK h0 x

section Tensor

variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  [MonoidalSequentialEffectus C] (h0 : σs.s = 0)

include h0

theorem cpt_one_val (A : C) : (1 : CPt σs A).1 = truth A := cpt_all σs h0 (truth A)

theorem cpt_orth_val {A : C} (p : CPt σs A) : (orth p).1 = orth p.1 := cpt_all σs h0 (orth p.1)

omit [MonoidalSequentialEffectus C] in
/-- `(e ⊗ 1)⊥ = e⊥ ⊗ 1`. -/
theorem orth_cptTens_one {A B : C} (e : CPt σs A) :
    orth (cptTens σs e (1 : CPt σs B)) = cptTens σs (orth e) 1 := by
  obtain ⟨h', e'⟩ := ptens_ovee_left (EffectAlgebra.perp_orth e) (1 : CPt σs B).1
  refine (EffectAlgebra.orth_unique (a := cptTens σs e 1) (b := cptTens σs (orth e) 1) h' ?_).symm
  apply Subtype.ext
  show ovee (ptens e.1 (1 : CPt σs B).1) (ptens (orth e).1 (1 : CPt σs B).1) h' = (1 : CPt σs (A ⊗ B)).1
  rw [← e']
  have h1 : ovee e.1 (orth e).1 (EffectAlgebra.perp_orth e) = (1 : CPt σs A).1 :=
    congrArg Subtype.val (EffectAlgebra.ovee_orth e)
  rw [h1]
  exact congrArg Subtype.val (cptTens_one σs)

omit [MonoidalSequentialEffectus C] in
theorem orth_cptTens_one' {A B : C} (f : CPt σs B) :
    orth (cptTens σs (1 : CPt σs A) f) = cptTens σs 1 (orth f) := by
  obtain ⟨h', e'⟩ := ptens_ovee_right (1 : CPt σs A).1 (EffectAlgebra.perp_orth f)
  refine (EffectAlgebra.orth_unique (a := cptTens σs 1 f) (b := cptTens σs 1 (orth f)) h' ?_).symm
  apply Subtype.ext
  show ovee (ptens (1 : CPt σs A).1 f.1) (ptens (1 : CPt σs A).1 (orth f).1) h' = (1 : CPt σs (A ⊗ B)).1
  rw [← e']
  have h1 : ovee f.1 (orth f).1 (EffectAlgebra.perp_orth f) = (1 : CPt σs B).1 :=
    congrArg Subtype.val (EffectAlgebra.ovee_orth f)
  rw [h1]
  exact congrArg Subtype.val (cptTens_one σs)

theorem cptTens_idem {A B : C} {e : CPt σs A} {f : CPt σs B} (he : Papers.SEA.IsIdempotent e)
    (hf : Papers.SEA.IsIdempotent f) : Papers.SEA.IsIdempotent (cptTens σs e f) := by
  refine (cpt_idem_iff σs _).2 (isIdempotent_of_isSharp (rec124 ?_ ?_))
  · exact isSharp_of_isIdempotent ((cpt_idem_iff σs e).1 he)
  · exact isSharp_of_isIdempotent ((cpt_idem_iff σs f).1 hf)

theorem Uop_cptTens {A B : C} (e : CPt σs A) (f : CPt σs B) :
    Uop σs (cptTens σs e f) = stateLin σs (asrtS e.1 ⊗ₘ asrtS f.1) := by
  rw [Uop_eq_stateLin]; congr 1; exact rec123 e.1 f.1

theorem Uop_cptTens_apply {A B : C} (e : CPt σs A) (f : CPt σs B) (c : VA σs A) (d : VA σs B) :
    Uop σs (cptTens σs e f) (tensV σs c d) = tensV σs (Uop σs e c) (Uop σs f d) := by
  rw [Uop_cptTens σs h0, stateLin_tensor, Uop_eq_stateLin, Uop_eq_stateLin]

theorem Uop_one {A : C} (x : VA σs A) : Uop σs (1 : CPt σs A) x = x := by
  have := gp_linearMap_ext (f := Uop σs (1 : CPt σs A)) (g := LinearMap.id) fun b => by
    rw [Uop_gmap, LinearMap.id_apply, Papers.SEA.one_seq]
  exact congrArg (fun φ => φ x) this

theorem gmap_one_eq (A : C) : GP.gmap (1 : CPt σs A) = ouUnit (VA σs A) := rfl

/-- The key computation: `(e ⊗ 1) * (c ⊗ d) = (e * c) ⊗ d` for an idempotent `e`. -/
theorem jm_tens_idem_left {A B : C} {e : CPt σs A} (he : Papers.SEA.IsIdempotent e)
    (c : VA σs A) (d : VA σs B) :
    jm σs hAS hRC h119 (A ⊗ B) (tensV σs (GP.gmap e) (ouUnit (VA σs B))) (tensV σs c d) =
      tensV σs (jm σs hAS hRC h119 A (GP.gmap e) c) d := by
  rw [← gmap_one_eq σs h0, tensV_gmap, jm_form σs hAS hRC h119 _ _
    (cptTens_idem σs h0 he Papers.SEA.isIdempotent_one), jm_form σs hAS hRC h119 _ _ he,
    orth_cptTens_one σs h0]
  show (2⁻¹ : ℝ) • (tensV σs c d + (Uop σs (cptTens σs e 1) (tensV σs c d) -
      Uop σs (cptTens σs (orth e) 1) (tensV σs c d))) =
    tensV σs ((2⁻¹ : ℝ) • (c + (Uop σs e c - Uop σs (orth e) c))) d
  rw [Uop_cptTens_apply σs h0, Uop_cptTens_apply σs h0, Uop_one σs h0,
    tensV_smul_left, tensV_add_left, tensV_sub_left]

theorem jm_tens_idem_right {A B : C} {f : CPt σs B} (hf : Papers.SEA.IsIdempotent f)
    (c : VA σs A) (d : VA σs B) :
    jm σs hAS hRC h119 (A ⊗ B) (tensV σs (ouUnit (VA σs A)) (GP.gmap f)) (tensV σs c d) =
      tensV σs c (jm σs hAS hRC h119 B (GP.gmap f) d) := by
  rw [← gmap_one_eq σs h0, tensV_gmap, jm_form σs hAS hRC h119 _ _
    (cptTens_idem σs h0 Papers.SEA.isIdempotent_one hf), jm_form σs hAS hRC h119 _ _ hf,
    orth_cptTens_one' σs h0]
  show (2⁻¹ : ℝ) • (tensV σs c d + (Uop σs (cptTens σs 1 f) (tensV σs c d) -
      Uop σs (cptTens σs 1 (orth f)) (tensV σs c d))) =
    tensV σs c ((2⁻¹ : ℝ) • (d + (Uop σs f d - Uop σs (orth f) d)))
  rw [Uop_cptTens_apply σs h0, Uop_cptTens_apply σs h0, Uop_one σs h0,
    tensV_smul_right, tensV_add_right, tensV_sub_right]

/-- **REC 125** (short.tex:2307, Proposition), for a sharp `p`, as printed:
`T_{p⊗1} = ½ (id ⊗ id + asrt_p ⊗ id − asrt_{p⊥} ⊗ id)` as operators on `V_{A⊗B}` (the
right-hand side is the paper's `T_p ⊗ id`), and symmetrically for `1 ⊗ q`. -/
theorem rec125_sharp {A B : C} {p : CPt σs A} (hp : Papers.SEA.IsIdempotent p)
    (v : VA σs (A ⊗ B)) :
    jm σs hAS hRC h119 (A ⊗ B) (tensV σs (GP.gmap p) (ouUnit (VA σs B))) v =
      (2⁻¹ : ℝ) • (v + (stateLin σs (asrtS p.1 ⊗ₘ 𝟙 B) v -
        stateLin σs (asrtS (orth p).1 ⊗ₘ 𝟙 B) v)) := by
  rw [← gmap_one_eq σs h0, tensV_gmap, jm_form σs hAS hRC h119 _ _
    (cptTens_idem σs h0 hp Papers.SEA.isIdempotent_one), orth_cptTens_one σs h0]
  show (2⁻¹ : ℝ) • (v + (Uop σs (cptTens σs p 1) v - Uop σs (cptTens σs (orth p) 1) v)) = _
  rw [Uop_cptTens σs h0, Uop_cptTens σs h0, cpt_one_val σs h0,
    show asrtS (truth B) = 𝟙 B from asrtS_one B]

/-- **REC 125** (short.tex:2307, Proposition), for arbitrary `a ∈ V_A`, on product vectors:
`T_{a⊗1}(c ⊗ d) = T_a c ⊗ d` and `T_{1⊗b}(c ⊗ d) = c ⊗ T_b d`.  (The printed operator
`T_a ⊗ id` is only defined for `a` a combination of sharp elements — `rec125_sharp`; the
paper's proof extends by norm continuity, which on product vectors is this statement.)
Proof as printed: the sharp case, then the density of combinations of sharp elements
(REC 58) and the continuity of `a ↦ T_{a⊗1}`. -/
theorem rec125 {A B : C} (a c : VA σs A) (d : VA σs B) :
    jm σs hAS hRC h119 (A ⊗ B) (tensV σs a (ouUnit (VA σs B))) (tensV σs c d) =
      tensV σs (jm σs hAS hRC h119 A a c) d := by
  let h : VA σs A →ₗ[ℝ] VA σs (A ⊗ B) :=
    (jmL σs hAS hRC h119 (A ⊗ B) (tensV σs c d)) ∘ₗ (vtens σs (ouUnit (VA σs B))) -
      (vtens σs d) ∘ₗ (jmL σs hAS hRC h119 A c)
  have hK : ∀ x, ousNorm _ (h x) ≤ (ousNorm _ (tensV σs c d) + ousNorm _ c * ousNorm _ d) *
      ousNorm (VA σs A) x := by
    intro x
    show ousNorm _ (jm σs hAS hRC h119 (A ⊗ B) (tensV σs x (ouUnit (VA σs B))) (tensV σs c d) -
      tensV σs (jm σs hAS hRC h119 A x c) d) ≤ _
    rw [sub_eq_add_neg]
    refine (ousNorm_add_le _ _).trans ?_
    rw [ousNorm_neg]
    have h1 := jm_norm_le σs hAS hRC h119 (A ⊗ B) (tensV σs x (ouUnit (VA σs B))) (tensV σs c d)
    have h2 := tensV_norm_le σs x (ouUnit (VA σs B))
    have h3 := tensV_norm_le σs (jm σs hAS hRC h119 A x c) d
    have h4 := jm_norm_le σs hAS hRC h119 A x c
    have hu := ousNorm_unit_le' σs B
    have n1 := ousNorm_nonneg_rc x
    have n2 := ousNorm_nonneg_rc c
    have n3 := ousNorm_nonneg_rc d
    have n4 := ousNorm_nonneg_rc (tensV σs c d)
    have n5 := ousNorm_nonneg_rc (tensV σs x (ouUnit (VA σs B)))
    have n6 := ousNorm_nonneg_rc (jm σs hAS hRC h119 A x c)
    have n7 := ousNorm_nonneg_rc (ouUnit (VA σs B))
    have : ousNorm _ (tensV σs x (ouUnit (VA σs B))) ≤ ousNorm (VA σs A) x := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this n4, mul_le_mul_of_nonneg_right h4 n3]
  have := va_eq_zero_of_idem σs h _ hK (fun e he => by
    show jm σs hAS hRC h119 (A ⊗ B) (tensV σs (GP.gmap e) (ouUnit (VA σs B))) (tensV σs c d) -
      tensV σs (jm σs hAS hRC h119 A (GP.gmap e) c) d = 0
    rw [jm_tens_idem_left σs hAS hRC h119 h0 he, sub_self]) a
  exact sub_eq_zero.1 this

theorem rec125_right {A B : C} (b : VA σs B) (c : VA σs A) (d : VA σs B) :
    jm σs hAS hRC h119 (A ⊗ B) (tensV σs (ouUnit (VA σs A)) b) (tensV σs c d) =
      tensV σs c (jm σs hAS hRC h119 B b d) := by
  let h : VA σs B →ₗ[ℝ] VA σs (A ⊗ B) :=
    (jmL σs hAS hRC h119 (A ⊗ B) (tensV σs c d)) ∘ₗ
        ((vtens σs (A := A) (B := B)).flip (ouUnit (VA σs A))) -
      (vtens σs (A := A) (B := B)).flip c ∘ₗ (jmL σs hAS hRC h119 B d)
  have hK : ∀ x, ousNorm _ (h x) ≤ (ousNorm _ (tensV σs c d) + ousNorm _ c * ousNorm _ d) *
      ousNorm (VA σs B) x := by
    intro x
    show ousNorm _ (jm σs hAS hRC h119 (A ⊗ B) (tensV σs (ouUnit (VA σs A)) x) (tensV σs c d) -
      tensV σs c (jm σs hAS hRC h119 B x d)) ≤ _
    rw [sub_eq_add_neg]
    refine (ousNorm_add_le _ _).trans ?_
    rw [ousNorm_neg]
    have h1 := jm_norm_le σs hAS hRC h119 (A ⊗ B) (tensV σs (ouUnit (VA σs A)) x) (tensV σs c d)
    have h2 := tensV_norm_le σs (ouUnit (VA σs A)) x
    have h3 := tensV_norm_le σs c (jm σs hAS hRC h119 B x d)
    have h4 := jm_norm_le σs hAS hRC h119 B x d
    have hu := ousNorm_unit_le' σs A
    have n1 := ousNorm_nonneg_rc x
    have n2 := ousNorm_nonneg_rc c
    have n3 := ousNorm_nonneg_rc d
    have n4 := ousNorm_nonneg_rc (tensV σs c d)
    have n6 := ousNorm_nonneg_rc (jm σs hAS hRC h119 B x d)
    have n7 := ousNorm_nonneg_rc (ouUnit (VA σs A))
    have : ousNorm _ (tensV σs (ouUnit (VA σs A)) x) ≤ ousNorm (VA σs B) x := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this n4, mul_le_mul_of_nonneg_left h4 n2]
  have := va_eq_zero_of_idem σs h _ hK (fun f hf => by
    show jm σs hAS hRC h119 (A ⊗ B) (tensV σs (ouUnit (VA σs A)) (GP.gmap f)) (tensV σs c d) -
      tensV σs c (jm σs hAS hRC h119 B (GP.gmap f) d) = 0
    rw [jm_tens_idem_right σs hAS hRC h119 h0 hf, sub_self]) b
  exact sub_eq_zero.1 this

end Tensor

end JordanVA

/-! ### States separate `V_A`; REC 126–128 -/

section StatesSep

open SequentialEffectus

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (σs : ScalarSplit C)

/-- The states of the effectus separate `V_A` (REC 14, 100): if `Pred(ω)(v) = 0` in `V_I`
for every state `ω`, then `v = 0`. -/
theorem states_separate_VA {A : C} (v : VA σs A)
    (h : ∀ ω : Stat A, stateLin σs ω.1 v = 0) : v = 0 := by
  obtain ⟨N, a, hN, rfl⟩ := gp_affine_repr v
  set half : CPt σs A := Papers.OAP.ihalf • (1 : CPt σs A) with hhdef
  have ghalf : ∀ {X : C}, GP.gmap (Papers.OAP.ihalf • (1 : CPt σs X)) =
      (1 / 2 : ℝ) • (GP.gunit : VA σs X) := by
    intro X; rw [GP.gmap_smul]; rfl
  have key : a = half := by
    apply Subtype.ext
    apply separatedByStates
    intro ω
    have e := h ω
    rw [map_sub, map_smul, map_smul, stateLin_gmap] at e
    have hu : stateLin σs ω.1 (GP.gunit : VA σs A) = GP.gunit := by
      show stateLin σs ω.1 (GP.gmap 1) = GP.gmap 1
      rw [stateLin_gmap]; congr 1; apply Subtype.ext
      show ω.1 ≫ (truth A ≫ orth σs.s) = truth (effObj C) ≫ orth σs.s
      rw [← Category.assoc, ω.2]
    rw [hu] at e
    have e2 : GP.gmap (cptMk σs (ω.1 ≫ a.1) (by rw [Category.assoc, a.2])) =
        GP.gmap (Papers.OAP.ihalf • (1 : CPt σs (effObj C))) := by
      rw [ghalf]
      have e3 : (2 * N) • GP.gmap (cptMk σs (ω.1 ≫ a.1) (by rw [Category.assoc, a.2])) =
          N • (GP.gunit : VA σs (effObj C)) := sub_eq_zero.1 e
      have := congrArg (fun w => (2 * N)⁻¹ • w) e3
      simp only [_root_.smul_smul] at this
      rw [inv_mul_cancel₀ (by positivity), one_smul] at this
      rw [this]; congr 1; field_simp
    have e4 := congrArg Subtype.val (GP.gmap_injective (E := CPt σs (effObj C)) e2)
    simp only [cptMk_val] at e4
    rw [e4]
    show (truth (effObj C) ≫ orth σs.s) ≫ σs.c Papers.OAP.ihalf =
      ω.1 ≫ ((truth A ≫ orth σs.s) ≫ σs.c Papers.OAP.ihalf)
    rw [← Category.assoc, ← Category.assoc, ω.2]
  rw [key, hhdef, ghalf, _root_.smul_smul, show 2 * N * (1 / 2) = N by ring, sub_self]

end StatesSep

section Rec126

open MonoidalCategory SequentialEffectus
open scoped Papers.SEA

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (σs : ScalarSplit C) (hAS : AlfsenShultzJordanFromDerivations.{v})
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  [MonoidalSequentialEffectus C] (h0 : σs.s = 0)

include h0

theorem rec125_sharp_right {A B : C} {q : CPt σs B} (hq : Papers.SEA.IsIdempotent q)
    (v : VA σs (A ⊗ B)) :
    jm σs hAS hRC h119 (A ⊗ B) (tensV σs (ouUnit (VA σs A)) (GP.gmap q)) v =
      (2⁻¹ : ℝ) • (v + (stateLin σs (𝟙 A ⊗ₘ asrtS q.1) v -
        stateLin σs (𝟙 A ⊗ₘ asrtS (orth q).1) v)) := by
  rw [← gmap_one_eq σs h0, tensV_gmap, jm_form σs hAS hRC h119 _ _
    (cptTens_idem σs h0 Papers.SEA.isIdempotent_one hq), orth_cptTens_one' σs h0]
  show (2⁻¹ : ℝ) • (v + (Uop σs (cptTens σs 1 q) v - Uop σs (cptTens σs 1 (orth q)) v)) = _
  rw [Uop_cptTens σs h0, Uop_cptTens σs h0, cpt_one_val σs h0,
    show asrtS (truth A) = 𝟙 A from asrtS_one A]

omit h0 in
theorem stateLin_tens_comm {A B : C} (f : A ⟶ A) (g : B ⟶ B) (v : VA σs (A ⊗ B)) :
    stateLin σs (f ⊗ₘ 𝟙 B) (stateLin σs (𝟙 A ⊗ₘ g) v) =
      stateLin σs (𝟙 A ⊗ₘ g) (stateLin σs (f ⊗ₘ 𝟙 B) v) := by
  rw [← LinearMap.comp_apply, ← stateLin_comp, ← LinearMap.comp_apply, ← stateLin_comp,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
    Category.comp_id, Category.id_comp]

omit [MonoidalSequentialEffectus C] h0 in
theorem tens_one_norm_le {A B : C} (a : VA σs A) :
    ousNorm _ (tensV σs a (ouUnit (VA σs B))) ≤ ousNorm (VA σs A) a := by
  have h1 := tensV_norm_le σs a (ouUnit (VA σs B))
  have h2 := ousNorm_unit_le' σs B
  have h3 := ousNorm_nonneg_rc a
  nlinarith

omit [MonoidalSequentialEffectus C] h0 in
theorem one_tens_norm_le {A B : C} (b : VA σs B) :
    ousNorm _ (tensV σs (ouUnit (VA σs A)) b) ≤ ousNorm (VA σs B) b := by
  have h1 := tensV_norm_le σs (ouUnit (VA σs A)) b
  have h2 := ousNorm_unit_le' σs A
  have h3 := ousNorm_nonneg_rc b
  nlinarith

/-- `T_{e⊗1}` and `T_{1⊗f}` commute for idempotents `e`, `f`. -/
theorem rec126_idem {A B : C} {e : CPt σs A} {f : CPt σs B} (he : Papers.SEA.IsIdempotent e)
    (hf : Papers.SEA.IsIdempotent f) (v : VA σs (A ⊗ B)) :
    jm σs hAS hRC h119 (A ⊗ B) (tensV σs (GP.gmap e) (ouUnit (VA σs B)))
        (jm σs hAS hRC h119 (A ⊗ B) (tensV σs (ouUnit (VA σs A)) (GP.gmap f)) v) =
      jm σs hAS hRC h119 (A ⊗ B) (tensV σs (ouUnit (VA σs A)) (GP.gmap f))
        (jm σs hAS hRC h119 (A ⊗ B) (tensV σs (GP.gmap e) (ouUnit (VA σs B))) v) := by
  simp only [rec125_sharp σs hAS hRC h119 h0 he, rec125_sharp_right σs hAS hRC h119 h0 hf,
    map_add, map_sub, map_smul, stateLin_tens_comm σs (asrtS e.1),
    stateLin_tens_comm σs (asrtS (orth e).1)]
  module

/-- **REC 126** (short.tex:2325, Corollary): for all `a ∈ V_A` and `b ∈ V_B`, `a ⊗ 1` and
`1 ⊗ b` operator commute: `T_{a⊗1} T_{1⊗b} = T_{1⊗b} T_{a⊗1}` on `V_{A⊗B}`.  (The paper
derives it from REC 125's `T_{a⊗1} = T_a ⊗ id`; we prove it directly for sharp `a`, `b`,
where `T_{p⊗1}`, `T_{1⊗q}` are combinations of `Pred(asrt ⊗ id)` and `Pred(id ⊗ asrt)`,
which commute by bifunctoriality, and extend by density, REC 58.) -/
theorem rec126 {A B : C} (a : VA σs A) (b : VA σs B) (v : VA σs (A ⊗ B)) :
    jm σs hAS hRC h119 (A ⊗ B) (tensV σs a (ouUnit (VA σs B)))
        (jm σs hAS hRC h119 (A ⊗ B) (tensV σs (ouUnit (VA σs A)) b) v) =
      jm σs hAS hRC h119 (A ⊗ B) (tensV σs (ouUnit (VA σs A)) b)
        (jm σs hAS hRC h119 (A ⊗ B) (tensV σs a (ouUnit (VA σs B))) v) := by
  set J := jm σs hAS hRC h119 (A ⊗ B) with hJ
  -- step 1: `b` idempotent, `a` arbitrary
  have step1 : ∀ (f : CPt σs B), Papers.SEA.IsIdempotent f → ∀ (a : VA σs A) (w : VA σs (A ⊗ B)),
      J (tensV σs a (ouUnit (VA σs B))) (J (tensV σs (ouUnit (VA σs A)) (GP.gmap f)) w) =
        J (tensV σs (ouUnit (VA σs A)) (GP.gmap f)) (J (tensV σs a (ouUnit (VA σs B))) w) := by
    intro f hf a w
    set y := tensV σs (ouUnit (VA σs A)) (GP.gmap f)
    let h : VA σs A →ₗ[ℝ] VA σs (A ⊗ B) :=
      (jmL σs hAS hRC h119 (A ⊗ B) (J y w)) ∘ₗ (vtens σs (ouUnit (VA σs B))) -
        (jmT σs hAS hRC h119 (A ⊗ B) y) ∘ₗ (jmL σs hAS hRC h119 (A ⊗ B) w) ∘ₗ
          (vtens σs (ouUnit (VA σs B)))
    have hK : ∀ x, ousNorm _ (h x) ≤ (ousNorm _ (J y w) + ousNorm _ y * ousNorm _ w) *
        ousNorm (VA σs A) x := by
      intro x
      show ousNorm _ (J (tensV σs x (ouUnit (VA σs B))) (J y w) -
        J y (J (tensV σs x (ouUnit (VA σs B))) w)) ≤ _
      rw [sub_eq_add_neg]
      refine (ousNorm_add_le _ _).trans ?_
      rw [ousNorm_neg]
      have h1 := jm_norm_le σs hAS hRC h119 (A ⊗ B) (tensV σs x (ouUnit (VA σs B))) (J y w)
      have h2 := jm_norm_le σs hAS hRC h119 (A ⊗ B) y (J (tensV σs x (ouUnit (VA σs B))) w)
      have h3 := jm_norm_le σs hAS hRC h119 (A ⊗ B) (tensV σs x (ouUnit (VA σs B))) w
      have h4 := tens_one_norm_le σs (B := B) x
      have n1 := ousNorm_nonneg_rc x
      have n2 := ousNorm_nonneg_rc y
      have n3 := ousNorm_nonneg_rc w
      have n4 := ousNorm_nonneg_rc (J y w)
      have n5 := ousNorm_nonneg_rc (tensV σs x (ouUnit (VA σs B)))
      have n6 := ousNorm_nonneg_rc (J (tensV σs x (ouUnit (VA σs B))) w)
      have e1 : ousNorm _ (J (tensV σs x (ouUnit (VA σs B))) (J y w)) ≤
          ousNorm (VA σs A) x * ousNorm _ (J y w) :=
        h1.trans (mul_le_mul_of_nonneg_right h4 n4)
      have e2 : ousNorm _ (J (tensV σs x (ouUnit (VA σs B))) w) ≤ ousNorm (VA σs A) x * ousNorm _ w :=
        h3.trans (mul_le_mul_of_nonneg_right h4 n3)
      have e3 : ousNorm _ (J y (J (tensV σs x (ouUnit (VA σs B))) w)) ≤
          ousNorm _ y * (ousNorm (VA σs A) x * ousNorm _ w) :=
        h2.trans (mul_le_mul_of_nonneg_left e2 n2)
      nlinarith
    have := va_eq_zero_of_idem σs h _ hK (fun e he => by
      show J (tensV σs (GP.gmap e) (ouUnit (VA σs B))) (J y w) -
        J y (J (tensV σs (GP.gmap e) (ouUnit (VA σs B))) w) = 0
      rw [sub_eq_zero]; exact rec126_idem σs hAS hRC h119 h0 he hf w) a
    exact sub_eq_zero.1 this
  -- step 2: `b` arbitrary
  set x := tensV σs a (ouUnit (VA σs B))
  let h : VA σs B →ₗ[ℝ] VA σs (A ⊗ B) :=
    (jmT σs hAS hRC h119 (A ⊗ B) x) ∘ₗ (jmL σs hAS hRC h119 (A ⊗ B) v) ∘ₗ
        ((vtens σs (A := A) (B := B)).flip (ouUnit (VA σs A))) -
      (jmL σs hAS hRC h119 (A ⊗ B) (J x v)) ∘ₗ
        ((vtens σs (A := A) (B := B)).flip (ouUnit (VA σs A)))
  have hK : ∀ z, ousNorm _ (h z) ≤ (ousNorm _ x * ousNorm _ v + ousNorm _ (J x v)) *
      ousNorm (VA σs B) z := by
    intro z
    show ousNorm _ (J x (J (tensV σs (ouUnit (VA σs A)) z) v) -
      J (tensV σs (ouUnit (VA σs A)) z) (J x v)) ≤ _
    rw [sub_eq_add_neg]
    refine (ousNorm_add_le _ _).trans ?_
    rw [ousNorm_neg]
    have h1 := jm_norm_le σs hAS hRC h119 (A ⊗ B) x (J (tensV σs (ouUnit (VA σs A)) z) v)
    have h2 := jm_norm_le σs hAS hRC h119 (A ⊗ B) (tensV σs (ouUnit (VA σs A)) z) v
    have h3 := jm_norm_le σs hAS hRC h119 (A ⊗ B) (tensV σs (ouUnit (VA σs A)) z) (J x v)
    have h4 := one_tens_norm_le σs (A := A) z
    have n1 := ousNorm_nonneg_rc z
    have n2 := ousNorm_nonneg_rc x
    have n3 := ousNorm_nonneg_rc v
    have n4 := ousNorm_nonneg_rc (J x v)
    have e2 : ousNorm _ (J (tensV σs (ouUnit (VA σs A)) z) v) ≤ ousNorm (VA σs B) z * ousNorm _ v :=
      h2.trans (mul_le_mul_of_nonneg_right h4 n3)
    have e1 : ousNorm _ (J x (J (tensV σs (ouUnit (VA σs A)) z) v)) ≤
        ousNorm _ x * (ousNorm (VA σs B) z * ousNorm _ v) :=
      h1.trans (mul_le_mul_of_nonneg_left e2 n2)
    have e3 : ousNorm _ (J (tensV σs (ouUnit (VA σs A)) z) (J x v)) ≤
        ousNorm (VA σs B) z * ousNorm _ (J x v) :=
      h3.trans (mul_le_mul_of_nonneg_right h4 n4)
    nlinarith
  have := va_eq_zero_of_idem σs h _ hK (fun f hf => by
    show J x (J (tensV σs (ouUnit (VA σs A)) (GP.gmap f)) v) -
      J (tensV σs (ouUnit (VA σs A)) (GP.gmap f)) (J x v) = 0
    rw [sub_eq_zero]; exact step1 f hf a v) b
  exact sub_eq_zero.1 this

end Rec126

/-! ### REC 127 -/

section Rec127

open MonoidalCategory SequentialEffectus Limits
open scoped Papers.SEA

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (σs : ScalarSplit C) (hAS : AlfsenShultzJordanFromDerivations.{v})
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  [MonoidalSequentialEffectus C]

/-- `A ⊗ B → A ⊗ I ≅ A`, discarding `B`. -/
noncomputable def rhoMap (A B : C) : A ⊗ B ⟶ A :=
  (𝟙 A ⊗ₘ truth B) ≫ (A ◁ eqToHom (MonoidalEffectus.unit_eq (C := C)).symm) ≫ (ρ_ A).hom

theorem rhoMap_pred {A B : C} (p : Pred A) : rhoMap A B ≫ p = ptens p (truth B) := by
  unfold rhoMap ptens muI
  rw [Category.assoc, Category.assoc, rho_muOf, ← Category.assoc, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id]

/-- `A ⊗ B → B`, discarding `A`. -/
noncomputable def lamMap (A B : C) : A ⊗ B ⟶ B := (β_ A B).hom ≫ rhoMap B A

theorem lamMap_pred {A B : C} (q : Pred B) : lamMap A B ≫ q = ptens (truth A) q := by
  rw [lamMap, Category.assoc, rhoMap_pred, ptens_comm]

variable (h0 : σs.s = 0)
include h0

theorem vtens_one_eq (A B : C) :
    (vtens σs (A := A) (B := B) (ouUnit (VA σs B))) = stateLin σs (rhoMap A B) :=
  gp_linearMap_ext fun p => by
    show tensV σs (GP.gmap p) (GP.gmap (1 : CPt σs B)) = _
    rw [tensV_gmap, stateLin_gmap]; congr 1; apply Subtype.ext
    show ptens p.1 (1 : CPt σs B).1 = rhoMap A B ≫ p.1
    rw [rhoMap_pred, cpt_one_val σs h0]

theorem one_vtens_eq (A B : C) :
    (vtens σs (A := A) (B := B)).flip (ouUnit (VA σs A)) = stateLin σs (lamMap A B) :=
  gp_linearMap_ext fun q => by
    show tensV σs (GP.gmap (1 : CPt σs A)) (GP.gmap q) = _
    rw [tensV_gmap, stateLin_gmap]; congr 1; apply Subtype.ext
    show ptens (1 : CPt σs A).1 q.1 = lamMap A B ≫ q.1
    rw [lamMap_pred, cpt_one_val σs h0]

omit h0 in
theorem stateTensor_stateLin_left {A B : C} (ω : Stat A) (ω' : Stat B) (x : VA σs A) :
    stateLin σs (stateTensor ω.1 ω'.1) (tensV σs x (GP.gmap (1 : CPt σs B))) =
      stateLin σs ω.1 x := by
  have := gp_linearMap_ext (f := stateLin σs (stateTensor ω.1 ω'.1) ∘ₗ
      vtens σs (A := A) (B := B) (GP.gmap (1 : CPt σs B))) (g := stateLin σs ω.1) fun p => by
    rw [LinearMap.comp_apply]
    change stateLin σs (stateTensor ω.1 ω'.1) (tensV σs (GP.gmap p) (GP.gmap 1)) = _
    rw [tensV_gmap, stateLin_gmap, stateLin_gmap]; congr 1; apply Subtype.ext
    show stateTensor ω.1 ω'.1 ≫ ptens p.1 (truth B ≫ orth σs.s) = ω.1 ≫ p.1
    have hp : p.1 ≫ orth σs.s = p.1 := p.2
    rw [stateTensor_ptens, ← Category.assoc ω'.1, ω'.2, truth_effObj_eq_id, Category.id_comp,
      Category.assoc, hp]
  exact LinearMap.congr_fun this x

theorem stateTensor_stateLin_right {A B : C} (ω : Stat B) (ω' : Stat A) (y : VA σs B) :
    stateLin σs (stateTensor ω'.1 ω.1) (tensV σs (GP.gmap (1 : CPt σs A)) y) =
      stateLin σs ω.1 y := by
  have := gp_linearMap_ext (f := stateLin σs (stateTensor ω'.1 ω.1) ∘ₗ
      (vtens σs (A := A) (B := B)).flip (GP.gmap (1 : CPt σs A))) (g := stateLin σs ω.1) fun q => by
    rw [LinearMap.comp_apply]
    change stateLin σs (stateTensor ω'.1 ω.1) (tensV σs (GP.gmap 1) (GP.gmap q)) = _
    rw [tensV_gmap, stateLin_gmap, stateLin_gmap]; congr 1; apply Subtype.ext
    show stateTensor ω'.1 ω.1 ≫ ptens (1 : CPt σs A).1 q.1 = ω.1 ≫ q.1
    rw [cpt_one_val σs h0, stateTensor_ptens, ω'.2, truth_effObj_eq_id, Category.id_comp]
  exact LinearMap.congr_fun this y

/-- **REC 127** (`prop:tensor-is-Jordan-hom`, short.tex:2329, Proposition), corrected:
`a ↦ a ⊗ 1` is a unital, positive, normal Jordan homomorphism `V_A → V_{A⊗B}`, and it is
injective **when `B` has a state** (`rec127_false_as_printed`: without that proviso the
map need not be injective).  The paper's proof: Jordan from REC 125/126; injective by
`(ω ⊗ ω')(a ⊗ 1) = ω(a)` and state separation (this is where a state `ω'` of `B` is
needed); normal because an injective unital Jordan homomorphism is an order embedding.
Our normality argument differs (the paper's does not show that suprema in the image are
suprema in `V_{A⊗B}`): `a ↦ a ⊗ 1` is `Pred(ρ)` for the map `ρ : A ⊗ B → A ⊗ I ≅ A`,
and `Pred` of a map is normal (REC 30, `stateLin_normal`). -/
theorem rec127 (A B : C) :
    (∀ a a' : VA σs A, jm σs hAS hRC h119 (A ⊗ B) (tensV σs a (ouUnit (VA σs B)))
        (tensV σs a' (ouUnit (VA σs B))) = tensV σs (jm σs hAS hRC h119 A a a') (ouUnit (VA σs B))) ∧
    tensV σs (ouUnit (VA σs A)) (ouUnit (VA σs B)) = ouUnit (VA σs (A ⊗ B)) ∧
    (∀ a : VA σs A, 0 ≤ a → 0 ≤ tensV σs a (ouUnit (VA σs B))) ∧
    IsNormalMap (fun a : VA σs A => tensV σs a (ouUnit (VA σs B))) ∧
    (Nonempty (Stat B) → Function.Injective (fun a : VA σs A => tensV σs a (ouUnit (VA σs B)))) := by
  refine ⟨fun a a' => rec125 σs hAS hRC h119 h0 a a' _, tensV_unit σs,
    fun a ha => tensV_nonneg σs ha ou_unit_nonneg, ?_, ?_⟩
  · have : (fun a : VA σs A => tensV σs a (ouUnit (VA σs B))) = stateLin σs (rhoMap A B) := by
      funext a; exact LinearMap.congr_fun (vtens_one_eq σs h0 A B) a
    rw [this]; exact stateLin_normal σs _
  · rintro ⟨ω'⟩ a a' h
    rw [← sub_eq_zero]
    apply states_separate_VA σs
    intro ω
    rw [← stateTensor_stateLin_left σs ω ω', tensV_sub_left]
    have h' : tensV σs a (GP.gmap (1 : CPt σs B)) = tensV σs a' (GP.gmap (1 : CPt σs B)) := h
    rw [h', sub_self, map_zero]

/-- **REC 127**, the second map: `b ↦ 1 ⊗ b` (the paper: "the other one follows
analogously"). -/
theorem rec127_right (A B : C) :
    (∀ b b' : VA σs B, jm σs hAS hRC h119 (A ⊗ B) (tensV σs (ouUnit (VA σs A)) b)
        (tensV σs (ouUnit (VA σs A)) b') = tensV σs (ouUnit (VA σs A)) (jm σs hAS hRC h119 B b b')) ∧
    (∀ b : VA σs B, 0 ≤ b → 0 ≤ tensV σs (ouUnit (VA σs A)) b) ∧
    IsNormalMap (fun b : VA σs B => tensV σs (ouUnit (VA σs A)) b) ∧
    (Nonempty (Stat A) → Function.Injective (fun b : VA σs B => tensV σs (ouUnit (VA σs A)) b)) := by
  refine ⟨fun b b' => rec125_right σs hAS hRC h119 h0 b _ b', fun b hb => tensV_nonneg σs ou_unit_nonneg hb,
    ?_, ?_⟩
  · have : (fun b : VA σs B => tensV σs (ouUnit (VA σs A)) b) = stateLin σs (lamMap A B) := by
      funext b; exact LinearMap.congr_fun (one_vtens_eq σs h0 A B) b
    rw [this]; exact stateLin_normal σs _
  · rintro ⟨ω'⟩ b b' h
    rw [← sub_eq_zero]
    apply states_separate_VA σs
    intro ω
    rw [← stateTensor_stateLin_right σs h0 ω ω', tensV_sub_right]
    have h' : tensV σs (GP.gmap (1 : CPt σs A)) b = tensV σs (GP.gmap (1 : CPt σs A)) b' := h
    rw [h', sub_self, map_zero]

/-- **REC 127 is false as printed**: "`a ↦ a ⊗ 1` is injective" fails for `B` the
initial object `0` (every effectus has one): `1_0 = 0`, so `a ⊗ 1_0 = a ⊗ 0 = 0`, while
`V_I ≠ 0` as soon as the scalars are non-trivial (as they are in §6, `[0,1]`).  The
printed proof picks "any state `ω'` on the second system", which `0` does not have. -/
theorem rec127_false_as_printed (hnt : (𝟙 (effObj C) : Scal C) ≠ 0) :
    ¬ ∀ A B : C, Function.Injective (fun a : VA σs A => tensV σs a (ouUnit (VA σs B))) := by
  intro h
  have hI : HasInitial C := inferInstance
  have h1 : (1 : CPt σs (⊥_ C)) = 0 := Subtype.ext (Subsingleton.elim _ _)
  have hz : ∀ x : VA σs (effObj C), tensV σs x (ouUnit (VA σs (⊥_ C))) = 0 := by
    intro x
    rw [show ouUnit (VA σs (⊥_ C)) = GP.gmap (1 : CPt σs (⊥_ C)) from rfl, h1, GP.gmap_zero,
      tensV_zero_right]
  have := h (effObj C) (⊥_ C) (a₁ := ouUnit _) (a₂ := 0)
    (by simp only; rw [hz, hz])
  have h2 : (1 : CPt σs (effObj C)) = 0 := GP.gmap_injective (by rw [GP.gmap_zero]; exact this)
  apply hnt
  have := congrArg Subtype.val h2
  rw [cpt_one_val σs h0, truth_effObj_eq_id] at this
  exact this

end Rec127

/-! ### Quadratic forms: polarisation bookkeeping for REC 128 -/

section Quad

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  (Bf : M →ₗ[ℝ] M →ₗ[ℝ] N) (hsym : ∀ x y, Bf x y = Bf y x)

include hsym

theorem quad_two (x y : M) (α β : ℝ) :
    Bf (α • x + β • y) (α • x + β • y) = (α * α) • Bf x x + (β * β) • Bf y y +
      (α * β) • (Bf (x + y) (x + y) - Bf x x - Bf y y) := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [hsym y x]
  module

theorem quad_four (X Y Z W : M) (α β γ δ : ℝ) :
    Bf ((α * γ) • X + (α * δ) • Y + (β * γ) • Z + (β * δ) • W)
        ((α * γ) • X + (α * δ) • Y + (β * γ) • Z + (β * δ) • W) =
      ((α * γ) * (α * γ)) • Bf X X + ((α * δ) * (α * δ)) • Bf Y Y +
        ((β * γ) * (β * γ)) • Bf Z Z + ((β * δ) * (β * δ)) • Bf W W +
      ((α * γ) * (α * δ)) • (Bf (X + Y) (X + Y) - Bf X X - Bf Y Y) +
      ((β * γ) * (β * δ)) • (Bf (Z + W) (Z + W) - Bf Z Z - Bf W W) +
      ((α * γ) * (β * γ)) • (Bf (X + Z) (X + Z) - Bf X X - Bf Z Z) +
      ((α * δ) * (β * δ)) • (Bf (Y + W) (Y + W) - Bf Y Y - Bf W W) +
      (α * β * γ * δ) • (Bf (X + Y + Z + W) (X + Y + Z + W) - Bf X X - Bf Y Y - Bf Z Z - Bf W W
        - (Bf (X + Y) (X + Y) - Bf X X - Bf Y Y) - (Bf (Z + W) (Z + W) - Bf Z Z - Bf W W)
        - (Bf (X + Z) (X + Z) - Bf X X - Bf Z Z) - (Bf (Y + W) (Y + W) - Bf Y Y - Bf W W)) := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [hsym Y X, hsym Z X, hsym W X, hsym Z Y, hsym W Y, hsym W Z]
  module

end Quad

/-! ### REC 128, REC 134 -/

section Rec128

open MonoidalCategory SequentialEffectus
open scoped Papers.SEA

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (σs : ScalarSplit C) (hAS : AlfsenShultzJordanFromDerivations.{v})
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

/-- The triple product `Q_{a,c} v = a(cv) + c(av) − (ac)v` of `V_X`, as a bilinear map in
`(a, c)` for fixed `v`. -/
noncomputable def jQ2L (X : C) (v : VA σs X) : VA σs X →ₗ[ℝ] VA σs X →ₗ[ℝ] VA σs X :=
  LinearMap.mk₂ ℝ (fun a c => jm σs hAS hRC h119 X a (jm σs hAS hRC h119 X c v) +
      jm σs hAS hRC h119 X c (jm σs hAS hRC h119 X a v) -
      jm σs hAS hRC h119 X (jm σs hAS hRC h119 X a c) v)
    (fun a a' c => by
      simp only [jm_add_left, jm_add_right]; abel)
    (fun r a c => by
      simp only [jm_smul_left, jm_smul_right, smul_add, smul_sub])
    (fun a c c' => by
      simp only [jm_add_left, jm_add_right]; abel)
    (fun r a c => by
      simp only [jm_smul_left, jm_smul_right, smul_add, smul_sub])

theorem jQ2L_symm (X : C) (v : VA σs X) (a c : VA σs X) :
    jQ2L σs hAS hRC h119 X v a c = jQ2L σs hAS hRC h119 X v c a := by
  simp only [jQ2L, LinearMap.mk₂_apply]
  rw [jm_comm σs hAS hRC h119 X a c]; abel

theorem jQA_eq_jQ2L (X : C) (a v : VA σs X) :
    jQA σs hAS hRC h119 X a v = jQ2L σs hAS hRC h119 X v a a := by
  simp only [jQ2L, LinearMap.mk₂_apply, jQA, jQ]
  rw [two_smul]; rfl

theorem jQA_unit (X : C) (v : VA σs X) : jQA σs hAS hRC h119 X (ouUnit (VA σs X)) v = v := by
  simp only [jQA, jQ]
  show (2 : ℝ) • jm σs hAS hRC h119 X (ouUnit _) (jm σs hAS hRC h119 X (ouUnit _) v) -
    jm σs hAS hRC h119 X (jm σs hAS hRC h119 X (ouUnit _) (ouUnit _)) v = v
  simp only [jm_unit, two_smul, add_sub_cancel_right]

theorem jQA_apply_unit (X : C) (a : VA σs X) :
    jQA σs hAS hRC h119 X a (ouUnit (VA σs X)) = jm σs hAS hRC h119 X a a := by
  simp only [jQA, jQ]
  show (2 : ℝ) • jm σs hAS hRC h119 X a (jm σs hAS hRC h119 X a (ouUnit _)) -
    jm σs hAS hRC h119 X (jm σs hAS hRC h119 X a a) (ouUnit _) = jm σs hAS hRC h119 X a a
  rw [jm_comm σs hAS hRC h119 X a (ouUnit _), jm_unit, jm_comm σs hAS hRC h119 X _ (ouUnit _),
    jm_unit, two_smul, add_sub_cancel_right]

/-- `Q` of a two-block combination `α e + β e⊥` of an idempotent `e`. -/
theorem jQA_two {X : C} {e : CPt σs X} (he : Papers.SEA.IsIdempotent e) (α β : ℝ)
    (c : VA σs X) :
    jQA σs hAS hRC h119 X (α • GP.gmap e + β • GP.gmap (orth e)) c =
      (α * α) • Uop σs e c + (β * β) • Uop σs (orth e) c +
        (α * β) • (c - Uop σs e c - Uop σs (orth e) c) := by
  rw [jQA_eq_jQ2L, quad_two _ (jQ2L_symm σs hAS hRC h119 X c), ← jQA_eq_jQ2L, ← jQA_eq_jQ2L,
    ← jQA_eq_jQ2L, gmap_add_orth', jQA_unit, jQA_idem σs hAS hRC h119 X he,
    jQA_idem σs hAS hRC h119 X he.compl]

variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  [MonoidalSequentialEffectus C] (h0 : σs.s = 0)

include h0

/-- **REC 128** (`prop:tensor-quadratic`, short.tex:2346, Proposition), for `a`, `b`
two-block combinations of sharp elements, on product vectors:
`Q_{a⊗b}(c ⊗ d) = Q_a c ⊗ Q_b d` for `a = α e + β e⊥`, `b = γ f + δ f⊥` (`e`, `f`
idempotent).  This covers the symmetries `2e − 1`, which is what REC 134 uses.  The proof
follows the paper's polarisation argument, but only ever evaluates `Q` at *sharp product*
elements (`e ⊗ f`, `e ⊗ 1`, `1 ⊗ f`, `1 ⊗ 1`), where `Q_t = asrt_t` and REC 123 applies —
so no identification `asrt_a = Q_{√a}` for non-sharp `a` (van de Wetering's thesis,
Thm 4.6.17, which the paper cites) is needed: the unknown cross terms
`Q_{e⊗f, e⊥⊗f⊥} + Q_{e⊗f⊥, e⊥⊗f}` only occur summed, and their sum is fixed by
`Q_{1⊗1} = id`. -/
theorem rec128 {A B : C} {e : CPt σs A} {f : CPt σs B} (he : Papers.SEA.IsIdempotent e)
    (hf : Papers.SEA.IsIdempotent f) (α β γ δ : ℝ) (c : VA σs A) (d : VA σs B) :
    jQA σs hAS hRC h119 (A ⊗ B)
        (tensV σs (α • GP.gmap e + β • GP.gmap (orth e)) (γ • GP.gmap f + δ • GP.gmap (orth f)))
        (tensV σs c d) =
      tensV σs (jQA σs hAS hRC h119 A (α • GP.gmap e + β • GP.gmap (orth e)) c)
        (jQA σs hAS hRC h119 B (γ • GP.gmap f + δ • GP.gmap (orth f)) d) := by
  set v := tensV σs c d
  set X := tensV σs (GP.gmap e) (GP.gmap f) with hX
  set Y := tensV σs (GP.gmap e) (GP.gmap (orth f)) with hY
  set Z := tensV σs (GP.gmap (orth e)) (GP.gmap f) with hZ
  set W := tensV σs (GP.gmap (orth e)) (GP.gmap (orth f)) with hW
  have hab : tensV σs (α • GP.gmap e + β • GP.gmap (orth e)) (γ • GP.gmap f + δ • GP.gmap (orth f)) =
      (α * γ) • X + (α * δ) • Y + (β * γ) • Z + (β * δ) • W := by
    simp only [tensV_add_left, tensV_add_right, tensV_smul_left, tensV_smul_right]
    rw [hX, hY, hZ, hW]; module
  -- the values of `Q` at sharp products
  have hq : ∀ (x : CPt σs A) (y : CPt σs B), Papers.SEA.IsIdempotent x → Papers.SEA.IsIdempotent y →
      jQ2L σs hAS hRC h119 (A ⊗ B) v (GP.gmap (cptTens σs x y)) (GP.gmap (cptTens σs x y)) =
        tensV σs (Uop σs x c) (Uop σs y d) := by
    intro x y hx hy
    rw [← jQA_eq_jQ2L, jQA_idem σs hAS hRC h119 _ (cptTens_idem σs h0 hx hy),
      Uop_cptTens_apply σs h0]
  have g1 : GP.gmap (orth e) + GP.gmap e = GP.gmap (1 : CPt σs A) := by
    rw [add_comm]; exact gmap_add_orth' σs e
  have g2 : GP.gmap f + GP.gmap (orth f) = GP.gmap (1 : CPt σs B) := gmap_add_orth' σs f
  have g1' : GP.gmap e + GP.gmap (orth e) = GP.gmap (1 : CPt σs A) := gmap_add_orth' σs e
  have hXY : X + Y = GP.gmap (cptTens σs e 1) := by
    rw [hX, hY, ← tensV_add_right, g2, tensV_gmap]
  have hZW : Z + W = GP.gmap (cptTens σs (orth e) 1) := by
    rw [hZ, hW, ← tensV_add_right, g2, tensV_gmap]
  have hXZ : X + Z = GP.gmap (cptTens σs 1 f) := by
    rw [hX, hZ, ← tensV_add_left, g1', tensV_gmap]
  have hYW : Y + W = GP.gmap (cptTens σs 1 (orth f)) := by
    rw [hY, hW, ← tensV_add_left, g1', tensV_gmap]
  have hall : X + Y + Z + W = GP.gmap (cptTens σs (1 : CPt σs A) (1 : CPt σs B)) := by
    rw [add_assoc (X + Y), hXY, hZW, ← tensV_gmap, ← tensV_gmap, ← tensV_add_left, g1',
      tensV_gmap]
  rw [jQA_eq_jQ2L, hab, quad_four _ (jQ2L_symm σs hAS hRC h119 _ v), hall, hXY, hZW, hXZ, hYW,
    hX, hY, hZ, hW, tensV_gmap, tensV_gmap, tensV_gmap, tensV_gmap]
  rw [hq e f he hf, hq e (orth f) he hf.compl, hq (orth e) f he.compl hf,
    hq (orth e) (orth f) he.compl hf.compl, hq e 1 he Papers.SEA.isIdempotent_one,
    hq (orth e) 1 he.compl Papers.SEA.isIdempotent_one, hq 1 f Papers.SEA.isIdempotent_one hf,
    hq 1 (orth f) Papers.SEA.isIdempotent_one hf.compl,
    hq 1 1 Papers.SEA.isIdempotent_one Papers.SEA.isIdempotent_one,
    jQA_two σs hAS hRC h119 he, jQA_two σs hAS hRC h119 hf, Uop_one σs h0, Uop_one σs h0]
  simp only [tensV_add_left, tensV_add_right, tensV_smul_left, tensV_smul_right, tensV_sub_left,
    tensV_sub_right]
  module

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  [MonoidalSequentialEffectus C] h0 in
/-- A symmetry of `V_X` is `e − e⊥` for an idempotent `e`, namely `e = ½(1 + s)`. -/
theorem symmetry_repr (X : C) {s : VA σs X} (hs : jm σs hAS hRC h119 X s s = ouUnit (VA σs X)) :
    ∃ y : CPt σs X, Papers.SEA.IsIdempotent y ∧ s = (1 : ℝ) • GP.gmap y + (-1 : ℝ) • GP.gmap (orth y) := by
  set e := (2⁻¹ : ℝ) • (ouUnit (VA σs X) + s) with he
  have hee : jm σs hAS hRC h119 X e e = e := by
    rw [he, jm_smul_left, jm_smul_right, jm_add_left, jm_add_right, jm_add_right, jm_unit, jm_unit,
      jm_comm σs hAS hRC h119 X s (ouUnit _), jm_unit, hs, _root_.smul_smul]
    module
  obtain ⟨y, hy, hye⟩ := jm_idem_gmap σs hAS hRC h119 X hee
  refine ⟨y, hy, ?_⟩
  have h1 : GP.gmap (orth y) = ouUnit (VA σs X) - GP.gmap y := by
    rw [← gmap_add_orth' σs y]; abel
  rw [h1, ← hye, he]
  module

omit h0 in
theorem jm_idem_tens {A B : C} {p : VA σs A} {p' : VA σs B}
    (hp : jm σs hAS hRC h119 A p p = p) (hp' : jm σs hAS hRC h119 B p' p' = p') (h0 : σs.s = 0) :
    ∃ z : CPt σs (A ⊗ B), Papers.SEA.IsIdempotent z ∧ tensV σs p p' = GP.gmap z := by
  obtain ⟨x, hx, rfl⟩ := jm_idem_gmap σs hAS hRC h119 A hp
  obtain ⟨y, hy, rfl⟩ := jm_idem_gmap σs hAS hRC h119 B hp'
  exact ⟨cptTens σs x y, cptTens_idem σs h0 hx hy, tensV_gmap σs x y⟩

theorem jm_gmap_idem {X : C} {z : CPt σs X} (hz : Papers.SEA.IsIdempotent z) :
    jm σs hAS hRC h119 X (GP.gmap z) (GP.gmap z) = GP.gmap z := by
  rw [jm_sq_gmap]; congr 1

/-- **REC 134** (`lem:tensor-symmetry`, short.tex:2388, Lemma): if `p₁, q₁ ∈ V_A` are
idempotents exchanged by the symmetry `s₁` and `p₂, q₂ ∈ V_B` by `s₂`, then `p₁ ⊗ p₂` and
`q₁ ⊗ q₂` are idempotents exchanged by the symmetry `s₁ ⊗ s₂`.  The paper's proof: REC 124
for the idempotents and REC 128 for `(s₁ ⊗ s₂)² = Q_{s₁⊗s₂} 1 = 1` and
`Q_{s₁⊗s₂}(p₁ ⊗ p₂) = Q_{s₁} p₁ ⊗ Q_{s₂} p₂`; REC 128 is used in its two-block form
(`s = e − e⊥`, `symmetry_repr`). -/
theorem rec134 {A B : C} {p₁ q₁ s₁ : VA σs A} {p₂ q₂ s₂ : VA σs B}
    (hp₁ : jm σs hAS hRC h119 A p₁ p₁ = p₁) (hq₁ : jm σs hAS hRC h119 A q₁ q₁ = q₁)
    (hs₁ : jm σs hAS hRC h119 A s₁ s₁ = ouUnit (VA σs A)) (e₁ : jQA σs hAS hRC h119 A s₁ p₁ = q₁)
    (hp₂ : jm σs hAS hRC h119 B p₂ p₂ = p₂) (hq₂ : jm σs hAS hRC h119 B q₂ q₂ = q₂)
    (hs₂ : jm σs hAS hRC h119 B s₂ s₂ = ouUnit (VA σs B)) (e₂ : jQA σs hAS hRC h119 B s₂ p₂ = q₂) :
    jm σs hAS hRC h119 (A ⊗ B) (tensV σs p₁ p₂) (tensV σs p₁ p₂) = tensV σs p₁ p₂ ∧
    jm σs hAS hRC h119 (A ⊗ B) (tensV σs q₁ q₂) (tensV σs q₁ q₂) = tensV σs q₁ q₂ ∧
    jm σs hAS hRC h119 (A ⊗ B) (tensV σs s₁ s₂) (tensV σs s₁ s₂) = ouUnit (VA σs (A ⊗ B)) ∧
    jQA σs hAS hRC h119 (A ⊗ B) (tensV σs s₁ s₂) (tensV σs p₁ p₂) = tensV σs q₁ q₂ := by
  obtain ⟨y₁, hy₁, rfl⟩ := symmetry_repr σs hAS hRC h119 A hs₁
  obtain ⟨y₂, hy₂, rfl⟩ := symmetry_repr σs hAS hRC h119 B hs₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨z, hz, e⟩ := jm_idem_tens σs hAS hRC h119 hp₁ hp₂ h0
    rw [e]; exact jm_gmap_idem σs hAS hRC h119 h0 hz
  · obtain ⟨z, hz, e⟩ := jm_idem_tens σs hAS hRC h119 hq₁ hq₂ h0
    rw [e]; exact jm_gmap_idem σs hAS hRC h119 h0 hz
  · rw [← jQA_apply_unit, ← tensV_unit σs, rec128 σs hAS hRC h119 h0 hy₁ hy₂, jQA_apply_unit,
      jQA_apply_unit, hs₁, hs₂, tensV_unit]
  · rw [rec128 σs hAS hRC h119 h0 hy₁ hy₂, e₁, e₂]

end Rec128

/-! ## Corners: the comprehension of a central sharp predicate (for REC 135) -/

section Corner

open SequentialEffectus
open scoped Papers.SEA

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

theorem seqS_eq {X : C} (p q : Pred X) : p ⊙ q = SEA.seq p q := (seq_eq' p q).trans (seq_eq p q).symm

variable {A : C} {c : Pred A} (hcs : IsSharp c)

/-- `π_c ∘ π_c† = id` and `π_c† ∘ π_c = asrt_c` (REC 109, 110). -/
theorem compr_dag (hcs : IsSharp c) :
    comprMap c ≫ dag (comprMap c) = 𝟙 _ ∧ dag (comprMap c) ≫ comprMap c = asrtS c := by
  obtain ⟨ξ, hξ, e1, e2⟩ := rec109 hcs (isComprehension_comprMap c)
  rw [rec110 hcs (isComprehension_comprMap c) hξ e1 e2]
  exact ⟨e1, e2⟩

include hcs in
/-- For `e` commuting with the sharp `c`: `asrt_{e ∘ π_c} = π_c† ∘ asrt_e ∘ π_c`. -/
theorem asrt_corner {e : Pred A} (he : SEA.seq e c = SEA.seq c e) :
    asrtS (comprMap c ≫ e) = comprMap c ≫ asrtS e ≫ dag (comprMap c) := by
  have hπ := isComprehension_comprMap c
  obtain ⟨Y, g, hg, hag⟩ := (asrtS_spec e).2.1
  refine (asrtS_unique (pure_comp (isPure_compr hπ) (pure_comp (isPure_asrtS e)
    (pure_dag (isPure_compr hπ)))) ⟨Y, comprMap c ≫ g, pure_comp (isPure_compr hπ) hg, ?_⟩ ?_).symm
  · rw [dag_comp (isPure_compr hπ) hg, hag, Category.assoc, Category.assoc]
  · have ht : dag (comprMap c) ≫ truth (comprObj c) = c := by
      rw [← compr_total hπ, ← Category.assoc, (compr_dag hcs).2, asrtS_truth]
    rw [Category.assoc, Category.assoc, ht, ← seq_eq, he, seq_eq, ← Category.assoc,
      compr_asrtS hcs hπ]

include hcs in
theorem asrt_corner_apply {e : Pred A} (he : SEA.seq e c = SEA.seq c e) (w : Pred A) :
    asrtS (comprMap c ≫ e) ≫ comprMap c ≫ w = comprMap c ≫ SEA.seq e w := by
  have hπ := isComprehension_comprMap c
  have hc1 : Papers.SEA.Commutes e c := by
    show e ⊙ c = c ⊙ e; rw [seqS_eq, seqS_eq]; exact he
  have hc2 : Papers.SEA.Commutes c e := hc1.symm
  rw [asrt_corner hcs he, Category.assoc, Category.assoc, ← Category.assoc (dag _),
    (compr_dag hcs).2, ← seq_eq c w, ← seq_eq e]
  have h3 : SEA.seq e (SEA.seq c w) = SEA.seq c (SEA.seq e w) := by
    have a1 := hc1.assoc w
    have a2 := hc2.assoc w
    rw [seqS_eq, seqS_eq, seqS_eq, seqS_eq] at a1 a2
    rw [a1, a2, he]
  rw [h3, seq_eq c, ← Category.assoc, compr_asrtS hcs hπ]

include hcs in
theorem orth_corner (e : Pred A) : orth (comprMap c ≫ e) = comprMap c ≫ orth e := by
  have hπ := isComprehension_comprMap c
  obtain ⟨h', e'⟩ := FinPAC.ovee_comp (EffectAlgebra.perp_orth e) (comprMap c)
  refine (EffectAlgebra.orth_unique h' ?_).symm
  rw [← e', EffectAlgebra.ovee_orth]
  exact compr_total hπ

variable (σs : ScalarSplit C) (hAS : AlfsenShultzJordanFromDerivations.{v})
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C) (h0 : σs.s = 0)

include h0

theorem cpt_one_val0 (X : C) : (1 : CPt σs X).1 = truth X := cpt_all σs h0 (truth X)

theorem cpt_orth_val0 {X : C} (p : CPt σs X) : (orth p).1 = orth p.1 := cpt_all σs h0 (orth p.1)

/-- Two maps with the same action on predicates have the same `Pred` on `V`. -/
theorem stateLin_congr {X Y : C} {f g : X ⟶ Y} (h : ∀ w : Pred Y, f ≫ w = g ≫ w) :
    stateLin σs f = stateLin σs g :=
  gp_linearMap_ext fun a => by
    rw [stateLin_gmap, stateLin_gmap]; congr 1; exact Subtype.ext (h a.1)

include hcs in
/-- The corner map `J = Pred(π_c) : V_A → V_{A_c}` is a Jordan homomorphism when `c` is
sharp and central (commutes with every predicate). -/
theorem corner_jordan (hcomm : ∀ w : Pred A, SEA.seq w c = SEA.seq c w) (x w : VA σs A) :
    stateLin σs (comprMap c) (jm σs hAS hRC h119 A x w) =
      jm σs hAS hRC h119 (comprObj c) (stateLin σs (comprMap c) x) (stateLin σs (comprMap c) w) := by
  have hπ := isComprehension_comprMap c
  set J := stateLin σs (comprMap c)
  have hJ1 : J (ouUnit (VA σs A)) = ouUnit (VA σs (comprObj c)) := by
    show J (GP.gmap 1) = GP.gmap 1
    rw [stateLin_gmap]; congr 1; apply Subtype.ext
    show comprMap c ≫ (1 : CPt σs A).1 = (1 : CPt σs (comprObj c)).1
    rw [cpt_one_val0 σs h0, cpt_one_val0 σs h0]
    exact compr_total hπ
  have hJn : ∀ z, ousNorm _ (J z) ≤ ousNorm (VA σs A) z :=
    contraction_of_pos (fun _ hv => stateLin_nonneg σs _ hv) (le_of_eq hJ1)
  -- the idempotent case
  have hid : ∀ e : CPt σs A, Papers.SEA.IsIdempotent e →
      J (jm σs hAS hRC h119 A (GP.gmap e) w) = jm σs hAS hRC h119 _ (J (GP.gmap e)) (J w) := by
    intro e he
    set e' : CPt σs (comprObj c) := cptMk σs (comprMap c ≫ e.1) (cpt_all σs h0 _)
    have hJe : J (GP.gmap e) = GP.gmap e' := stateLin_gmap σs _ e
    have hce : ∀ e : CPt σs A, SEA.seq e.1 c = SEA.seq c e.1 := fun e => hcomm e.1
    have he' : Papers.SEA.IsIdempotent e' := by
      apply Subtype.ext
      show SEA.seq (comprMap c ≫ e.1) (comprMap c ≫ e.1) = comprMap c ≫ e.1
      rw [seq_eq, asrt_corner_apply hcs (hce e)]
      congr 1; exact (cpt_idem_iff σs e).1 he
    have horth : orth e' = cptMk σs (comprMap c ≫ (orth e).1) (cpt_all σs h0 _) := by
      apply Subtype.ext
      show (orth e').1 = comprMap c ≫ (orth e).1
      rw [cpt_orth_val0 σs h0, cpt_orth_val0 σs h0]
      exact orth_corner hcs e.1
    have hU : ∀ (f : CPt σs A), SEA.seq f.1 c = SEA.seq c f.1 →
        Uop σs (cptMk σs (comprMap c ≫ f.1) (cpt_all σs h0 _)) ∘ₗ J = J ∘ₗ Uop σs f := by
      intro f hf
      rw [Uop_eq_stateLin, Uop_eq_stateLin]
      show stateLin σs (asrtS (comprMap c ≫ f.1)) ∘ₗ stateLin σs (comprMap c) =
        stateLin σs (comprMap c) ∘ₗ stateLin σs (asrtS f.1)
      rw [← stateLin_comp, ← stateLin_comp]
      exact stateLin_congr σs h0 fun w' => by
        rw [Category.assoc, asrt_corner_apply hcs hf, Category.assoc, seq_eq]
    rw [jm_form σs hAS hRC h119 A e he, hJe, jm_form σs hAS hRC h119 _ e' he', horth]
    simp only [map_smul, map_add, map_sub]
    have k1 := LinearMap.congr_fun (hU e (hce e)) w
    have k2 := LinearMap.congr_fun (hU (orth e) (hce (orth e))) w
    simp only [LinearMap.comp_apply] at k1 k2
    show (2⁻¹ : ℝ) • (J w + (J (Uop σs e w) - J (Uop σs (orth e) w))) = _
    rw [← k1, ← k2]; rfl
  let h : VA σs A →ₗ[ℝ] VA σs (comprObj c) :=
    J ∘ₗ jmL σs hAS hRC h119 A w - jmL σs hAS hRC h119 _ (J w) ∘ₗ J
  have hK : ∀ z, ousNorm _ (h z) ≤ (2 * ousNorm (VA σs A) w) * ousNorm (VA σs A) z := by
    intro z
    show ousNorm _ (J (jm σs hAS hRC h119 A z w) - jm σs hAS hRC h119 _ (J z) (J w)) ≤ _
    rw [sub_eq_add_neg]
    refine (ousNorm_add_le _ _).trans ?_
    rw [ousNorm_neg]
    have h1 := hJn (jm σs hAS hRC h119 A z w)
    have h2 := jm_norm_le σs hAS hRC h119 A z w
    have h3 := jm_norm_le σs hAS hRC h119 _ (J z) (J w)
    have h4 := hJn z
    have h5 := hJn w
    have n1 := ousNorm_nonneg_rc z
    have n2 := ousNorm_nonneg_rc w
    have n3 := ousNorm_nonneg_rc (J z)
    have n4 := ousNorm_nonneg_rc (J w)
    nlinarith [mul_le_mul h4 h5 n4 n1]
  have := va_eq_zero_of_idem σs h _ hK (fun e he => by
    show J (jm σs hAS hRC h119 A (GP.gmap e) w) - jm σs hAS hRC h119 _ (J (GP.gmap e)) (J w) = 0
    rw [hid e he, sub_self]) x
  exact sub_eq_zero.1 this

theorem corner_section {A : C} {c : Pred A} (hcs : IsSharp c) (y : VA σs (comprObj c)) :
    stateLin σs (comprMap c) (stateLin σs (dag (comprMap c)) y) = y := by
  rw [← LinearMap.comp_apply, ← stateLin_comp, (compr_dag hcs).1, stateLin_id]; rfl

theorem corner_asrt {A : C} {c : Pred A} (hcs : IsSharp c) (x : VA σs A) :
    stateLin σs (comprMap c) (stateLin σs (asrtS c) x) = stateLin σs (comprMap c) x := by
  rw [← LinearMap.comp_apply, ← stateLin_comp, compr_asrtS hcs (isComprehension_comprMap c)]

omit h0 in
theorem jm_idem_Uop {A : C} {c₀ : CPt σs A} (hc : Papers.SEA.IsIdempotent c₀) (z : VA σs A) :
    jm σs hAS hRC h119 A (GP.gmap c₀) (Uop σs c₀ z) = Uop σs c₀ z := by
  rw [jm_form σs hAS hRC h119 A c₀ hc]
  show (2⁻¹ : ℝ) • (Uop σs c₀ z + (Uop σs c₀ (Uop σs c₀ z) - Uop σs (orth c₀) (Uop σs c₀ z))) = _
  rw [show Uop σs c₀ (Uop σs c₀ z) = Uop σs c₀ z from ulin_idem (cpt_hsm σs A) hc z,
    show Uop σs (orth c₀) (Uop σs c₀ z) = 0 from ulin_orth_zero' (cpt_hsm σs A) hc z]
  module

omit h0 in
/-- An operator-central idempotent (`c(xy) = x(cy)`) of `V_A` commutes, in the sequential
product, with every effect: `c & w + c⊥ & w = w`. -/
theorem central_of_jordan {A : C} {c₀ : CPt σs A} (hc : Papers.SEA.IsIdempotent c₀)
    (hcen : ∀ x y : VA σs A, jm σs hAS hRC h119 A (GP.gmap c₀) (jm σs hAS hRC h119 A x y) =
      jm σs hAS hRC h119 A x (jm σs hAS hRC h119 A (GP.gmap c₀) y)) (w : CPt σs A) :
    Papers.SEA.Commutes c₀ w := by
  set U := ULin (cpt_hsm σs A)
  set x : VA σs A := GP.gmap w
  set y := x - U c₀ x - U (orth c₀) x with hy
  have hUy : U c₀ y = 0 := by
    rw [hy, map_sub, map_sub, ulin_idem _ hc, ulin_orth_zero _ hc]; abel
  have hUy' : U (orth c₀) y = 0 := by
    rw [hy, map_sub, map_sub, ulin_orth_zero' _ hc, ulin_idem _ hc.compl]; abel
  have hTy : jm σs hAS hRC h119 A (GP.gmap c₀) y = (2⁻¹ : ℝ) • y := by
    rw [jm_form σs hAS hRC h119 A c₀ hc, hUy, hUy', sub_zero, add_zero]
  have hcc : jm σs hAS hRC h119 A (GP.gmap c₀) (GP.gmap c₀) = GP.gmap c₀ := by
    rw [jm_form σs hAS hRC h119 A c₀ hc, ULin_gmap, ULin_gmap, hc, hc.orth_seq, GP.gmap_zero]
    module
  have key := hcen y (GP.gmap c₀)
  rw [hcc, jm_comm σs hAS hRC h119 A y, hTy, jm_smul_right, hTy, _root_.smul_smul] at key
  have hy0 : y = 0 := by
    have : ((2⁻¹ : ℝ) * 2⁻¹ - 2⁻¹) • y = 0 := by rw [sub_smul, key, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · norm_num at h
    · exact h
  have hsplit : GP.gmap (c₀ ⊙ w) + GP.gmap (orth c₀ ⊙ w) = GP.gmap w := by
    have : x = U c₀ x + U (orth c₀) x := by rw [← sub_eq_zero, ← hy0, hy]; abel
    simp only [x, U, ULin_gmap] at this
    exact this.symm
  -- the SEA argument: `x := c & w ≤ c`, `y := c⊥ & w ≤ c⊥`, both commute with `c`
  have hx : c₀ ⊙ w ≼ c₀ := Papers.SEA.seq_le_left _ _
  have hy2 : orth c₀ ⊙ w ≼ orth c₀ := Papers.SEA.seq_le_left _ _
  have hp : Perp (c₀ ⊙ w) (orth c₀ ⊙ w) :=
    Papers.SEA.perp_of_le hx hy2 (EffectAlgebra.perp_orth c₀)
  have hw : ovee (c₀ ⊙ w) (orth c₀ ⊙ w) hp = w :=
    GP.gmap_injective (by rw [GP.gmap_ovee hp]; exact hsplit)
  have h1 : Papers.SEA.Commutes c₀ (c₀ ⊙ w) := by
    show c₀ ⊙ (c₀ ⊙ w) = (c₀ ⊙ w) ⊙ c₀
    rw [((Papers.SEA.sea17_5 hc _).1).1 hx, ((Papers.SEA.sea17_5 hc _).2.1).1 hx]
  have h2 : Papers.SEA.Commutes c₀ (orth c₀ ⊙ w) := by
    show c₀ ⊙ (orth c₀ ⊙ w) = (orth c₀ ⊙ w) ⊙ c₀
    have a := ((Papers.SEA.sea17_5 hc.compl _).2.2.2).1 hy2
    have b := ((Papers.SEA.sea17_5 hc.compl _).2.2.1).1 hy2
    rw [Papers.SEA.orth_orth] at a b
    rw [a, b]
  have := Papers.SEA.Commutes.ovee hp h1 h2
  rwa [hw] at this

include hcs in
/-- A purely exceptional part transfers to the corner: if every Jordan homomorphism of
`V_A` into a C*-algebra vanishes on `{x ; c x = x}`, then `V_{A_c}` is purely exceptional
(REC 51). -/
theorem corner_purelyExceptional {c₀ : CPt σs A} (hc₀ : c₀.1 = c) (hc : Papers.SEA.IsIdempotent c₀)
    (hcomm : ∀ w : Pred A, SEA.seq w c = SEA.seq c w)
    (hvan : ∀ (𝔅 : Type v) [CStarAlgebra 𝔅] (ψ : VA σs A →ₗ[ℝ] 𝔅),
      (letI := jbMul σs hAS hRC h119 A; IsJordanHomInto (VA σs A) 𝔅 ψ) →
        ∀ x, jm σs hAS hRC h119 A (GP.gmap c₀) x = x → ψ x = 0) :
    letI := jbMul σs hAS hRC h119 (comprObj c); IsPurelyExceptional.{v, v} (VA σs (comprObj c)) := by
  intro 𝔅 _ φ hφ
  set J := stateLin σs (comprMap c)
  have hψ : (letI := jbMul σs hAS hRC h119 A; IsJordanHomInto (VA σs A) 𝔅 (φ ∘ₗ J)) := by
    refine ⟨fun a => hφ.1 (J a), fun a b => ?_⟩
    show φ (J (jm σs hAS hRC h119 A a b)) = _
    rw [corner_jordan hcs σs hAS hRC h119 h0 hcomm]
    exact hφ.2 (J a) (J b)
  ext y
  rw [LinearMap.zero_apply]
  set z := stateLin σs (dag (comprMap c)) y
  have hy : y = J (Uop σs c₀ z) := by
    rw [Uop_eq_stateLin, hc₀, corner_asrt σs h0 hcs, corner_section σs h0 hcs]
  rw [hy]
  exact hvan 𝔅 (φ ∘ₗ J) hψ _ (jm_idem_Uop σs hAS hRC h119 hc z)

end Corner

/-! ## REC 135: `V_A` is a JW-algebra -/

section Rec135

open MonoidalCategory SequentialEffectus
open scoped Papers.SEA

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (hAS : AlfsenShultzJordanFromDerivations.{v})
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)
  (φ₀ : EffectMonoidHom (Scal C) I) (ψ₀ : EffectMonoidHom I (Scal C))
  (h1 : ∀ k, ψ₀.toFun (φ₀.toFun k) = k) (h2 : ∀ r, φ₀.toFun (ψ₀.toFun r) = r)

include h1 h2 in
/-- With scalars `[0,1]`, `V_X` is a JBW-algebra (REC 103). -/
theorem jbw_real (X : C) :
    @JBWAlgebra (VA (realSplit ψ₀) X) _ _ _ _ (jbMul (realSplit ψ₀) hAS hRC h119 X) :=
  @JBWAlgebra.mk (VA (realSplit ψ₀) X) _ _ _ _ (jbMul (realSplit ψ₀) hAS hRC h119 X)
    (jbMul_spec (realSplit ψ₀) hAS hRC h119 X) (VA_dc (realSplit ψ₀) X)
    (separating_normal_states φ₀ ψ₀ h1 h2 X)

omit h1 h2 in
include φ₀ in
/-- An object with a state has `V_X ≠ 0` (scalars `[0,1]`). -/
theorem unit_ne_zero_real {X : C} (hX : Nonempty (Stat X)) :
    ouUnit (VA (realSplit ψ₀) X) ≠ 0 := by
  intro h
  obtain ⟨ω⟩ := hX
  have e1 : (1 : CPt (realSplit ψ₀) X) = 0 :=
    GP.gmap_injective (E := CPt (realSplit ψ₀) X) (h.trans GP.gmap_zero.symm)
  have e2 : truth X = 0 := by
    have := congrArg Subtype.val e1
    rwa [show (1 : CPt (realSplit ψ₀) X).1 = truth X from
      cpt_all (realSplit ψ₀) rfl (truth X)] at this
  have e3 : truth (effObj C) = 0 := by rw [← ω.2, e2, FinPAC.comp_zero]
  have e4 := congrArg φ₀.toFun e3
  rw [show φ₀.toFun (truth (effObj C)) = 1 from φ₀.map_one, alg_emonHom_map_zero] at e4
  exact one_ne_zero e4

omit h1 in
theorem realVal_tens [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C] {A B : C}
    (ω : Stat A) (ω' : Stat B) (x : VA (realSplit ψ₀) A) (y : VA (realSplit ψ₀) B) :
    realVal φ₀ ψ₀ h2 (stateLin (realSplit ψ₀) (stateTensor ω.1 ω'.1) (tensV (realSplit ψ₀) x y)) =
      realVal φ₀ ψ₀ h2 (stateLin (realSplit ψ₀) ω.1 x) *
        realVal φ₀ ψ₀ h2 (stateLin (realSplit ψ₀) ω'.1 y) := by
  have key : (vtens (realSplit ψ₀) (A := A) (B := B)).compr₂
      (realVal φ₀ ψ₀ h2 ∘ₗ stateLin (realSplit ψ₀) (stateTensor ω.1 ω'.1)) =
      ((LinearMap.mul ℝ ℝ).compl₁₂ (realVal φ₀ ψ₀ h2 ∘ₗ stateLin (realSplit ψ₀) ω.1)
        (realVal φ₀ ψ₀ h2 ∘ₗ stateLin (realSplit ψ₀) ω'.1)).flip :=
    gp_linearMap_ext fun q => gp_linearMap_ext fun p => by
      simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, LinearMap.compl₁₂_apply,
        LinearMap.mul_apply', LinearMap.comp_apply]
      change realVal φ₀ ψ₀ h2 (stateLin (realSplit ψ₀) (stateTensor ω.1 ω'.1)
        (tensV (realSplit ψ₀) (GP.gmap p) (GP.gmap q))) = _
      rw [tensV_gmap, stateLin_gmap, stateLin_gmap, stateLin_gmap, realVal_gmap, realVal_gmap,
        realVal_gmap]
      show ((φ₀.toFun (stateTensor ω.1 ω'.1 ≫ ptens p.1 q.1) : I) : ℝ) =
        ((φ₀.toFun (ω.1 ≫ p.1) : I) : ℝ) * ((φ₀.toFun (ω'.1 ≫ q.1) : I) : ℝ)
      rw [stateTensor_ptens]
      rw [show (ω.1 ≫ p.1) ≫ (ω'.1 ≫ q.1) = (ω'.1 ≫ q.1) * (ω.1 ≫ p.1) from rfl, φ₀.map_mul]
      push_cast; ring
  exact LinearMap.congr_fun (LinearMap.congr_fun key y) x

omit h1 in
include h1 in
theorem realVal_eq_zero {v : VA (realSplit ψ₀) (effObj C)} (hv : realVal φ₀ ψ₀ h2 v = 0) :
    v = 0 := by
  have a := (realVal_le_iff φ₀ ψ₀ h1 h2 v 0).1 (by rw [hv, map_zero])
  have b := (realVal_le_iff φ₀ ψ₀ h1 h2 0 v).1 (by rw [hv, map_zero])
  exact le_antisymm a b

include h1 in
theorem exists_state_ne {X : C} {x : VA (realSplit ψ₀) X} (hx : x ≠ 0) :
    ∃ ω : Stat X, realVal φ₀ ψ₀ h2 (stateLin (realSplit ψ₀) ω.1 x) ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hx (states_separate_VA (realSplit ψ₀) x fun ω => realVal_eq_zero φ₀ ψ₀ h1 h2 (hc ω))

include h1 h2 in
theorem tens_ne_zero [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C] {A B : C}
    {x : VA (realSplit ψ₀) A} {y : VA (realSplit ψ₀) B} (hx : x ≠ 0) (hy : y ≠ 0) :
    tensV (realSplit ψ₀) x y ≠ 0 := by
  obtain ⟨ω, hω⟩ := exists_state_ne φ₀ ψ₀ h1 h2 hx
  obtain ⟨ω', hω'⟩ := exists_state_ne φ₀ ψ₀ h1 h2 hy
  intro h
  have := realVal_tens φ₀ ψ₀ h2 ω ω' x y
  rw [h, map_zero, map_zero] at this
  exact mul_ne_zero hω hω' this.symm

omit h1 h2 in
theorem Uop_zero_of_jm {σs : ScalarSplit C} {X : C} {a b : CPt σs X}
    (ha : Papers.SEA.IsIdempotent a) (h : jm σs hAS hRC h119 X (GP.gmap a) (GP.gmap b) = 0) :
    Uop σs a (GP.gmap b) = 0 := by
  rw [jm_form σs hAS hRC h119 X a ha] at h
  have e := congrArg (ULin (cpt_hsm σs X) a) h
  rw [map_zero, map_smul, map_add, map_sub, ulin_idem _ ha, ulin_orth_zero _ ha, sub_zero,
    ← two_smul ℝ, _root_.smul_smul, show (2⁻¹ : ℝ) * 2 = 1 by norm_num, one_smul] at e
  exact e

omit h1 h2 in
theorem jm_zero_of_Uop {σs : ScalarSplit C} {X : C} {a b : CPt σs X}
    (ha : Papers.SEA.IsIdempotent a) (h : Uop σs a (GP.gmap b) = 0) :
    jm σs hAS hRC h119 X (GP.gmap a) (GP.gmap b) = 0 := by
  have hab : a ⊙ b = 0 := by
    rw [Uop_gmap] at h; exact GP.gmap_injective (h.trans GP.gmap_zero.symm)
  have hle : b ≼ orth a := by
    have := ((Papers.SEA.sea17_5 ha.compl b).2.2.2).2
    rw [Papers.SEA.orth_orth] at this; exact this hab
  have h2 : orth a ⊙ b = b := ((Papers.SEA.sea17_5 ha.compl b).1).1 hle
  rw [jm_form σs hAS hRC h119 X a ha]
  show (2⁻¹ : ℝ) • (GP.gmap b + (Uop σs a (GP.gmap b) - Uop σs (orth a) (GP.gmap b))) = 0
  rw [h, Uop_gmap, h2]; simp

variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  [MonoidalSequentialEffectus C]

include h1 h2 in
/-- **REC 135** (short.tex:2395, Proposition): in a monoidal sequential effectus with
scalars `[0,1]`, every `V_A` is a JW-algebra (REC 50).  The paper's proof: split
`V_A = V₁ ⊕ V₂` with `V₁` JW and `V₂` purely exceptional (REC 52, named hypothesis
`HancheOlsenStormerDecomposition`) along a central idempotent `c`; if `V₂ ≠ 0`, the
comprehension `A_c` has `V_{A_c} ≅ V₂` purely exceptional (here: `Pred(π_c)` is a
surjective Jordan homomorphism killing `c⊥`, `corner_jordan`), so its unit is a sum of
three exchangeable idempotents (REC 133, from Shultz's theorem via the Albert algebra);
their nine tensors make `V_{A_c ⊗ A_c}` JW (REC 134, REC 132 = named hypothesis
`AlfsenShultzFourExchangeable`), and `a ↦ a ⊗ 1` (REC 127) embeds `V_{A_c}` into it — a
non-zero Jordan homomorphism of a purely exceptional algebra into a C*-algebra, which is
absurd.  (The paper goes through `W*(V)` (REC 129, 130) for the last step; the injective
Jordan homomorphism that REC 50 provides suffices, so REC 129 is not needed.) -/
theorem rec135 (hHOS : HancheOlsenStormerDecomposition.{v}) (hSh : ShultzExceptionalStructure.{v})
    (hAS4 : AlfsenShultzFourExchangeable.{v}) (A : C) :
    letI := jbMul (realSplit ψ₀) hAS hRC h119 A; IsJWAlgebra (VA (realSplit ψ₀) A) := by
  set σs := realSplit ψ₀ with hσs
  have h0 : σs.s = 0 := rfl
  letI iA := jbMul σs hAS hRC h119 A
  haveI := jm_jb σs hAS hRC h119 A
  obtain ⟨c, hcc, hcen, ⟨𝔄, i1, i2, i3, i4, φ, hφJ, hφn, hker⟩, hvan⟩ :=
    hHOS (VA σs A) (jbw_real hAS hRC h119 φ₀ ψ₀ h1 h2 A)
  by_cases hc0 : c = 0
  · refine ⟨𝔄, i1, i2, i3, i4, φ, hφJ, fun x y hxy => ?_, hφn⟩
    have e1 : φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have e2 := (hker (x - y)).1 e1
    rw [hc0, jb_zero_mul] at e2
    exact sub_eq_zero.1 e2.symm
  obtain ⟨c₀, hc₀, rfl⟩ := jm_idem_gmap σs hAS hRC h119 A hcc
  have hcs : IsSharp c₀.1 := isSharp_of_isIdempotent ((cpt_idem_iff σs c₀).1 hc₀)
  have hcomm : ∀ w : Pred A, SEA.seq w c₀.1 = SEA.seq c₀.1 w := by
    intro w
    have := central_of_jordan σs hAS hRC h119 hc₀ hcen (cptMk σs w (cpt_all σs h0 w))
    have e : SEA.seq c₀.1 w = SEA.seq w c₀.1 := congrArg Subtype.val this
    exact e.symm
  have hc0' : c₀.1 ≠ 0 := fun h => hc0 (by
    rw [show c₀ = 0 from Subtype.ext h, GP.gmap_zero])
  set W := comprObj c₀.1
  obtain ⟨ω⟩ := exists_state_compr hcs hc0'
  have hpe := corner_purelyExceptional hcs σs hAS hRC h119 h0 rfl hc₀ hcomm
    (fun 𝔅 _ ψ hψ x hx => hvan 𝔅 ψ hψ x hx)
  have hWne : ouUnit (VA σs W) ≠ 0 := unit_ne_zero_real φ₀ ψ₀ ⟨ω⟩
  letI iW := jbMul σs hAS hRC h119 W
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ :=
    rec133 hSh (VA σs W) (jbw_real hAS hRC h119 φ₀ ψ₀ h1 h2 W) hpe ⟨_, hWne⟩
  choose x hx hqx using fun i => jm_idem_gmap σs hAS hRC h119 W (hq1 i).1
  choose sy hsy hsyq using hq4
  let e9 : Fin (3 * 3) ≃ Fin 3 × Fin 3 := finProdFinEquiv.symm
  let P : Fin (3 * 3) → VA σs (W ⊗ W) := fun k => tensV σs (q (e9 k).1) (q (e9 k).2)
  letI iWW := jbMul σs hAS hRC h119 (W ⊗ W)
  have hJW : IsJWAlgebra (VA σs (W ⊗ W)) := by
    refine hAS4 (VA σs (W ⊗ W)) (jbw_real hAS hRC h119 φ₀ ψ₀ h1 h2 (W ⊗ W)) (3 * 3) (by norm_num) P
      (fun k => ⟨?_, ?_⟩) (fun i j hij => ?_) ?_ (fun i j => ?_)
    · obtain ⟨z, hz, e⟩ := jm_idem_tens σs hAS hRC h119 (hq1 (e9 k).1).1 (hq1 (e9 k).2).1 h0
      show jm σs hAS hRC h119 (W ⊗ W) (P k) (P k) = P k
      simp only [P]; rw [e]; exact jm_gmap_idem σs hAS hRC h119 h0 hz
    · exact tens_ne_zero φ₀ ψ₀ h1 h2 (hq1 _).2 (hq1 _).2
    · show jm σs hAS hRC h119 (W ⊗ W) (P i) (P j) = 0
      simp only [P]
      rw [hqx (e9 i).1, hqx (e9 i).2, hqx (e9 j).1, hqx (e9 j).2, tensV_gmap, tensV_gmap]
      refine jm_zero_of_Uop hAS hRC h119 (cptTens_idem σs h0 (hx _) (hx _)) ?_
      rw [← tensV_gmap, Uop_cptTens_apply σs h0]
      have hne : (e9 i).1 ≠ (e9 j).1 ∨ (e9 i).2 ≠ (e9 j).2 := by
        by_contra hc
        push_neg at hc
        exact hij (e9.injective (Prod.ext hc.1 hc.2))
      rcases hne with h | h
      · have := hq2 _ _ h
        rw [hqx, hqx] at this
        rw [Uop_zero_of_jm hAS hRC h119 (hx _) this, tensV_zero_left]
      · have := hq2 _ _ h
        rw [hqx, hqx] at this
        rw [Uop_zero_of_jm hAS hRC h119 (hx _) this, tensV_zero_right]
    · show ∑ k, P k = ouUnit (VA σs (W ⊗ W))
      rw [show (∑ k, P k) = ∑ ab : Fin 3 × Fin 3, tensV σs (q ab.1) (q ab.2) from
        Equiv.sum_comp e9 (fun ab => tensV σs (q ab.1) (q ab.2)), Fintype.sum_prod_type]
      simp only [Fin.sum_univ_three, tensV_add_left, tensV_add_right] at hq3 ⊢
      rw [← tensV_unit σs, ← hq3]
      simp only [tensV_add_left, tensV_add_right]
      abel
    · refine ⟨tensV σs (sy (e9 i).1 (e9 j).1) (sy (e9 i).2 (e9 j).2), ?_, ?_⟩
      · exact (rec134 σs hAS hRC h119 h0 (hq1 _).1 (hq1 _).1 (hsy _ _) (hsyq _ _)
          (hq1 _).1 (hq1 _).1 (hsy _ _) (hsyq _ _)).2.2.1
      · exact (rec134 σs hAS hRC h119 h0 (hq1 _).1 (hq1 _).1 (hsy _ _) (hsyq _ _)
          (hq1 _).1 (hq1 _).1 (hsy _ _) (hsyq _ _)).2.2.2
  obtain ⟨𝔄', j1, j2, j3, j4, φ', hφ'J, hφ'i, -⟩ := hJW
  have hψ : IsJordanHomInto (VA σs W) 𝔄' (φ' ∘ₗ vtens σs (ouUnit (VA σs W))) := by
    refine ⟨fun a => hφ'J.1 _, fun a b => ?_⟩
    show φ' (tensV σs (jm σs hAS hRC h119 W a b) (ouUnit _)) = _
    rw [← (rec127 σs hAS hRC h119 h0 W W).1 a b]
    exact hφ'J.2 _ _
  have hz := LinearMap.congr_fun (hpe 𝔄' _ hψ) (ouUnit (VA σs W))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
  have hu : tensV σs (ouUnit (VA σs W)) (ouUnit (VA σs W)) = 0 :=
    hφ'i (hz.trans (map_zero φ').symm)
  rw [tensV_unit] at hu
  exact (unit_ne_zero_real φ₀ ψ₀ ⟨⟨stateTensor ω.1 ω.1, stateTensor_total ω ω⟩⟩ hu).elim

end Rec135

/-! ## REC 136: the functor into `JW_npc` -/

/-- **REC 136** (short.tex:2407, running text): `JW_npc`, the full subcategory of
`JBW_npc` (REC 48) of the JW-algebras (REC 50). -/
structure JWnpcCat : Type (u + 1) where
  carrier : Type u
  [acg : AddCommGroup carrier]
  [mod : Module ℝ carrier]
  [po : PartialOrder carrier]
  [ous : OrderUnitSpace carrier]
  [mul : Mul carrier]
  jbw : JBWAlgebra carrier
  jw : IsJWAlgebra carrier

attribute [instance] JWnpcCat.acg JWnpcCat.mod JWnpcCat.po JWnpcCat.ous JWnpcCat.mul

instance : Category JWnpcCat.{u} where
  Hom A B := { f : A.carrier →ₗ[ℝ] B.carrier // IsNPC f }
  id _ := ⟨LinearMap.id, isNPC_id⟩
  comp f g := ⟨g.1 ∘ₗ f.1, isNPC_comp f.2 g.2⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

section Rec136

open MonoidalCategory SequentialEffectus

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (hAS : AlfsenShultzJordanFromDerivations.{v})
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

/-- The predicate functor `C → JW_npcᵒᵖ`, `A ↦ V_A`, `f ↦ Pred(f)`, given that every
`V_A` is a JW-algebra. -/
noncomputable def jwFunctor (σs : ScalarSplit C)
    (hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A))
    (hJW : ∀ A : C, letI := jbMul σs hAS hRC h119 A; IsJWAlgebra (VA σs A)) :
    C ⥤ JWnpcCat.{v}ᵒᵖ where
  obj A := Opposite.op (@JWnpcCat.mk (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A) (hJBW A) (hJW A))
  map f := Quiver.Hom.op ⟨stateLin σs f, stateLin_isNPC σs f⟩
  map_id A := by
    apply Quiver.Hom.unop_inj; apply Subtype.ext; exact stateLin_id σs A
  map_comp f g := by
    apply Quiver.Hom.unop_inj; apply Subtype.ext; exact stateLin_comp σs f g

theorem jwFunctor_spec (σs : ScalarSplit C) (h0 : σs.s = 0)
    (hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A))
    (hJW : ∀ A : C, letI := jbMul σs hAS hRC h119 A; IsJWAlgebra (VA σs A)) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) := by
  refine ⟨jwFunctor hAS hRC h119 σs hJBW hJW, fun A => ?_, ?_⟩
  · let e₁ : Pred A ≃ CPt σs A :=
      ⟨fun p => cptMk σs p (cpt_all σs h0 p), fun q => q.1, fun _ => rfl, fun _ => rfl⟩
    refine ⟨e₁.trans (Papers.OAP.gpEquiv (CPt σs A)), fun a b => ?_, fun a b h => ?_, ?_⟩
    · exact (PredPart.le_iff (orth_idem σs.hs) (p := cptMk σs a (cpt_all σs h0 a))
        (q := cptMk σs b (cpt_all σs h0 b))).symm.trans
          (Papers.OAP.gmap_le_gmap_iff (E := CPt σs A)).symm
    · show GP.gmap (cptMk σs (ovee a b h) _) = GP.gmap (cptMk σs a _) + GP.gmap (cptMk σs b _)
      have hp : Perp (cptMk σs a (cpt_all σs h0 a)) (cptMk σs b (cpt_all σs h0 b)) := h
      rw [← GP.gmap_ovee hp]; rfl
    · show GP.gmap (cptMk σs (truth A) _) = GP.gmap 1
      congr 1; apply Subtype.ext
      show truth A = truth A ≫ orth σs.s
      rw [cpt_all σs h0]
  · have key : ∀ {A B : C} (f g : A ⟶ B), (jwFunctor hAS hRC h119 σs hJBW hJW).map f =
        (jwFunctor hAS hRC h119 σs hJBW hJW).map g ↔ ∀ b : Pred B, f ≫ b = g ≫ b := by
      intro A B f g
      constructor
      · intro h b
        have hl : stateLin σs f = stateLin σs g :=
          congrArg Subtype.val (congrArg Quiver.Hom.unop h)
        have := congrArg (fun φ => φ (GP.gmap (cptMk σs (A := B) b (cpt_all σs h0 b)))) hl
        simp only [stateLin_gmap] at this
        exact congrArg (fun x : CPt σs A => x.1) (GP.gmap_injective this)
      · intro h
        apply Quiver.Hom.unop_inj; apply Subtype.ext
        refine gp_linearMap_ext fun a => ?_
        show stateLin σs f (GP.gmap a) = stateLin σs g (GP.gmap a)
        rw [stateLin_gmap, stateLin_gmap]; congr 1; exact Subtype.ext (h a.1)
    constructor
    · intro hF A B f g h
      exact hF.map_injective ((key f g).2 h)
    · intro hs
      exact ⟨fun {A B} {f g} h => hs f g ((key f g).1 h)⟩

/-- The scalar splitting for the trivial scalars `{0}` (`s = 0`, `c_λ = 0`). -/
noncomputable def trivSplit (hsub : Subsingleton (Scal C)) : ScalarSplit C where
  s := 0
  hs := FinPAC.zero_comp _
  bool _ _ _ := Subsingleton.elim _ _
  c := fun _ => 0
  c_mul _ _ := Subsingleton.elim _ _
  c_add _ _ _ := ⟨PCM.zero_perp 0, Subsingleton.elim _ _⟩
  c_one := Subsingleton.elim _ _

theorem va_subsingleton (hsub : Subsingleton (Scal C)) (A : C) :
    Subsingleton (VA (trivSplit hsub) A) := by
  have hp : ∀ p : CPt (trivSplit hsub) A, p = 0 := fun p => Subtype.ext (by
    show p.1 = 0
    rw [← Category.comp_id p.1, show (𝟙 (effObj C) : Scal C) = 0 from Subsingleton.elim _ _,
      FinPAC.comp_zero])
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : VA (trivSplit hsub) A, z = 0 := by
    intro z
    obtain ⟨r, t, a, b, -, -, rfl⟩ := gp_exists_repr z
    rw [hp a, hp b, GP.gmap_zero, smul_zero, smul_zero, sub_zero]
  rw [hx x, hx y]

/-- A subsingleton JB-algebra is a JW-algebra: `0` into `B(ℂ)` (thesis A's
`VonNeumannAlgebra (H →L[ℂ] H)`). -/
theorem isJW_of_subsingleton (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V]
    [OrderUnitSpace V] [Mul V] [Subsingleton V] : IsJWAlgebra V := by
  let H := EuclideanSpace ℂ (ULift.{v} (Fin 1))
  refine ⟨H →L[ℂ] H, inferInstance, inferInstance, inferInstance, inferInstance, 0,
    ⟨fun _ => by simp, fun _ _ => by simp⟩, fun _ _ _ => Subsingleton.elim _ _, ?_⟩
  intro S t hne _ _
  have : ((0 : V →ₗ[ℝ] (H →L[ℂ] H)) '' S) = {0} := by
    ext z; simp only [Set.mem_image, LinearMap.zero_apply, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, _, rfl⟩; rfl
    · rintro rfl; exact ⟨hne.some, hne.some_mem, rfl⟩
  rw [this, LinearMap.zero_apply]
  exact isLUB_singleton

variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  [MonoidalSequentialEffectus C]

include hAS hRC h119 in
/-- **REC 136** (`thm:JW-algebra`, short.tex:2409, Theorem): for a monoidal sequential
effectus (REC 122) with irreducible scalars not equal to `{0,1}` there is a functor
`F : C → JW_npcᵒᵖ` with `Pred(A) ≅ [0,1]_{F(A)}` (the print's `F(Pred(A))` is ill-typed,
PLAN flag 5), and `F` is faithful iff `C` is separated by predicates.  The paper's proof:
REC 103 gives the functor into `JBW_npcᵒᵖ` (`A ↦ V_A`), and REC 135 makes every `V_A` a
JW-algebra.  The scalars are `{0}` or `[0,1]` (REC 36); `{0}` gives trivial `V_A`, which
are JW trivially.  Named hypotheses: the three of REC 102/103 (`hAS`, `hRC`, `h119`), and
REC 52 (`hHOS`), REC 55 (`hSh`), REC 132 (`hAS4`). -/
theorem rec136 (hHOS : HancheOlsenStormerDecomposition.{v}) (hSh : ShultzExceptionalStructure.{v})
    (hAS4 : AlfsenShultzFourExchangeable.{v}) (hirr : IsIrreducible (Scal C))
    (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) := by
  rcases seq_scal_cases hirr with h | h | ⟨φ₀, ψ₀, h1, h2⟩
  · set σs := trivSplit h
    have hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A) := fun A =>
      haveI := va_subsingleton h A
      @JBWAlgebra.mk (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A) (jbMul_spec σs hAS hRC h119 A)
        (VA_dc σs A) (fun a b hab => (hab (Subsingleton.elim a b)).elim)
    have hJW : ∀ A : C, letI := jbMul σs hAS hRC h119 A; IsJWAlgebra (VA σs A) := fun A =>
      haveI := va_subsingleton h A
      @isJW_of_subsingleton (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A) _
    exact jwFunctor_spec hAS hRC h119 σs rfl hJBW hJW
  · exact (h01 h).elim
  · exact jwFunctor_spec hAS hRC h119 (realSplit ψ₀) rfl
      (jbw_real hAS hRC h119 φ₀ ψ₀ h1 h2) (rec135 hAS hRC h119 φ₀ ψ₀ h1 h2 hHOS hSh hAS4)

end Rec136

end Papers.REC
