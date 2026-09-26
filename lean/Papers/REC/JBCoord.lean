import Papers.REC.Rec136NoFour
import Papers.REC.JBPeirce
import Papers.REC.JBMacdonald
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Peirce specialisation: a purely exceptional algebra has no exchangeable corner copy

Plan (replaces the coordinatisation route for REC 136's `ExceptionalNoFourExch` input).
* Why not coordinatise the corner: `nofour_core` hands `ExceptionalNoFourExch` a family whose
  sum is not `1`, and corners of purely exceptional algebras need not be purely exceptional
  (`U_{e₁} H₃(𝕆) = ℝ`, `U_{e₁+e₂} H₃(𝕆)` a spin factor), so Jacobson's `H_n(D)` of the corner
  gives nothing.  What pure exceptionality forbids is a *Jordan copy of the whole algebra*
  inside a corner that has room outside it; REC's tensor product supplies exactly that.
1. Algebra (any Jordan algebra, `IsJordanMul`; only `jlin` and the Peirce rules):
   - `peirce_spec` (McCrimmon's Peirce specialisation): `a, b ∈ V₁(P)`, `x ∈ V½(P)` ⟹
     `(ab)x = a(bx) + b(ax)`, so `a ↦ 2L_a` is a Jordan hom `V₁(P) → End(V½(P))`;
   - `form_symm`: `aQ = 0`, `x, y ∈ V½(Q)` ⟹ `Q((ax)y) = Q((ay)x)`;
   - JB: `Q(xy) = U_Q(xy)` on `V½(Q)` and `U_Q U_x c = 2Q((cx)x)` for `Qc = 0` (`form_pos`).
2. Hilbert space (generic): a positive semidefinite symmetric form `β` on a real space `W`;
   `Cx β = W × W` with `ℂ`-structure and Hermitian form (a `PreInnerProductSpace.Core`),
   `Hs β` its completion; a `β`-bounded `T` gives `opC T : Hs →L[ℂ] Hs`, additive,
   multiplicative, unital, self-adjoint when `T` is `β`-symmetric.
3. Core (`corner_absurd`): `V` JB, `P ⊥ Q` idempotents connected by `v` (`v ∈ V½(P) ∩ V½(Q)`,
   `v² = P + Q`), `Q ≠ 0`; `U` purely exceptional, `ψ : U → V` Jordan with `ψ 1 = P`.  With
   `φ` a state, `φ Q > 0`: `W = V½(P) ∩ V½(Q)`, `β(x,y) = φ(Q(xy))`, `T_a x = 2ψ(a)x`.  `T_a`
   is Jordan (1), `β`-symmetric (`form_symm`), bounded: `β(T_a x, T_a x) = β(T_{a²}x, x)
   ≤ K β(x,x)` since `ψ(a)² ≤ K P` and `β(T_c x, x) = φ(U_Q U_x c) ≥ 0` for `c ≥ 0` in `V₁(P)`.
   `a ↦ opC T_a` is a Jordan hom into the C*-algebra `B(Hs)`, `= 1 ≠ 0` at `a = 1`
   (`β(v,v) = φ Q > 0`): contradiction.
4. `compress_mul`: `x, y` without `½`-part for `P` ⟹ `P(xy) = (Px)(Py)`.
5. REC glue (`summand_absurd`, `rec135_summand`, `rec136_summand_hypfree`, `rec136_HOS`): in
   `nofour_absurd`'s situation (`V_W ≠ 0` purely exceptional, `p ⊥ q` exchanged by `s`),
   `ψ(a) = P(a ⊗ 1) = a ⊗ p` into `V_{W⊗W}`, `P = 1 ⊗ p`, `Q = 1 ⊗ q` (exchanged by
   `1 ⊗ s`; REC 127's second map `b ↦ 1 ⊗ b` is Jordan).  Hence REC 135/136 from
   `JBWExceptionalSummand` alone; `ExceptionalNoFourExch` itself is not proved here.
-/

set_option linter.unusedSectionVars false

open Theses.B.Eff

namespace Papers.REC.JBCoord

open Papers.REC Papers.REC.JBPeirce

universe u v

/-! ## 1. Peirce specialisation and the Peirce form -/

section Alg

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [IsJordanMul V]

/-- **Peirce specialisation** (McCrimmon, *A Taste of Jordan Algebras*, II.9): for
`a, b ∈ V₁(P)` and `x ∈ V½(P)`, `(ab)x = a(bx) + b(ax)`; i.e. `a ↦ 2L_a|_{V½(P)}` is a
Jordan homomorphism of `V₁(P)` into the associative algebra `End(V½(P))`. -/
theorem peirce_spec {P a b x : V} (hP : P * P = P) (ha : a ∈ peirce P 1) (hb : b ∈ peirce P 1)
    (hx : x ∈ peirce P (1 / 2)) : (a * b) * x = a * (b * x) + b * (a * x) := by
  have hxa : x * a ∈ peirce P (1 / 2) := by
    rw [jmul_comm]; exact peirce_one_mul_half hP ha hx
  have hxab : x * a * b ∈ peirce P (1 / 2) := by
    rw [jmul_comm]; exact peirce_one_mul_half hP hb hxa
  have h := jlin a P x b
  rw [mem_peirce] at ha hb hx hxab
  have e1 : a * P = a := by rw [jmul_comm, ha, one_smul]
  rw [hx, e1, hb, one_smul, hxab] at h
  simp only [jsmul_mul, jmul_smul] at h
  have c1 : a * b * x = x * (a * b) := jmul_comm _ _
  have c2 : b * x = x * b := jmul_comm _ _
  have c3 : b * (a * x) = x * a * b := by rw [jmul_comm, jmul_comm a x]
  rw [c1, c2, c3]
  linear_combination (norm := module) (2 : ℝ) • h

/-- **The Peirce form is symmetric**: `aQ = 0`, `x, y ∈ V½(Q)` ⟹ `Q((ax)y) = Q((ay)x)`. -/
theorem form_symm {Q a x y : V} (ha : a * Q = 0) (hx : x ∈ peirce Q (1 / 2))
    (hy : y ∈ peirce Q (1 / 2)) : Q * ((a * x) * y) = Q * ((a * y) * x) := by
  have h1 := jlin a Q y x
  have h2 := jlin a Q x y
  rw [mem_peirce] at hx hy
  rw [hy, hx, ha, jzero_mul, jmul_zero, jzero_mul] at h1
  rw [hx, hy, ha, jzero_mul, jmul_zero, jzero_mul] at h2
  simp only [jsmul_mul, jmul_smul] at h1 h2
  have c1 : a * (y * x) = a * (x * y) := by rw [jmul_comm y x]
  have c2 : y * (a * x) = x * a * y := by rw [jmul_comm, jmul_comm a x]
  have c3 : x * (a * y) = y * a * x := by rw [jmul_comm, jmul_comm a y]
  have c4 : a * x * y = x * a * y := by rw [jmul_comm a x]
  have c5 : a * y * x = y * a * x := by rw [jmul_comm a y]
  rw [c4, c5]
  linear_combination (norm := module) h2 - h1 + (2⁻¹ : ℝ) • c1 - (2⁻¹ : ℝ) • c2
    + (2⁻¹ : ℝ) • c3

/-- On products of `½`-elements, `L_Q` is `U_Q`. -/
theorem Q_mul_eq_jQ {Q x y : V} (hQ : Q * Q = Q) (hx : x ∈ peirce Q (1 / 2))
    (hy : y ∈ peirce Q (1 / 2)) : Q * (x * y) = jQ Q (x * y) := by
  have h := peirce_half_mul_half hQ hx hy
  rw [Ph_apply] at h
  have h' : Q * (Q * (x * y)) = Q * (x * y) := by
    linear_combination (norm := module) (-(4 : ℝ)⁻¹) • h
  rw [jQ, hQ, h']
  module

/-- `U_Q U_x c = 2 Q((cx)x)` for `Qc = 0`, `x ∈ V½(Q)`. -/
theorem jQ_jQ_eq {Q x c : V} (hQ : Q * Q = Q) (hc : Q * c = 0) (hx : x ∈ peirce Q (1 / 2)) :
    jQ Q (jQ x c) = (2 : ℝ) • (Q * ((c * x) * x)) := by
  have hc0 : c ∈ peirce Q 0 := mem_peirce_zero_of_orth hc
  have hcx : c * x ∈ peirce Q (1 / 2) := peirce_zero_mul_half hQ hc0 hx
  have hm1 : Q * (x * x) ∈ peirce Q 1 := by
    rw [mem_peirce, one_smul]; exact peirce_half_sq hQ hx
  have hz : Q * (x * x * c) = 0 := by
    rw [jmul_comm (x * x) c, orth_commute hQ hc, jmul_comm]
    exact peirce_one_mul_zero hQ hm1 hc0
  have e1 : jQ Q (x * x * c) = 0 := by
    rw [jQ, hQ, hz, jmul_zero, smul_zero, sub_zero]
  have e2 : jQ Q (x * (x * c)) = Q * ((c * x) * x) := by
    rw [jmul_comm x c, jmul_comm x (c * x), ← Q_mul_eq_jQ hQ hcx hx]
  have lin : jQ Q (jQ x c) = (2 : ℝ) • jQ Q (x * (x * c)) - jQ Q (x * x * c) := by
    simp only [jQ, jmul_sub, jmul_smul]; module
  rw [lin, e1, e2, sub_zero]

end Alg

section JB

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

/-- Positivity of the Peirce form: `Q(x²) ≥ 0` for `x ∈ V½(Q)`. -/
theorem form_self_nonneg {Q x : V} (hQ : Q * Q = Q) (hx : x ∈ peirce Q (1 / 2)) :
    0 ≤ Q * (x * x) := by
  rw [Q_mul_eq_jQ hQ hx hx]; exact JBMac.jQ_nonneg Q (jb_sq_nonneg x)

/-- Positivity of the specialisation: `Q((cx)x) ≥ 0` for `c ≥ 0`, `Qc = 0`, `x ∈ V½(Q)`. -/
theorem form_pos {Q x c : V} (hQ : Q * Q = Q) (hc : Q * c = 0) (hc0 : 0 ≤ c)
    (hx : x ∈ peirce Q (1 / 2)) : 0 ≤ Q * ((c * x) * x) := by
  have h := JBMac.jQ_nonneg Q (JBMac.jQ_nonneg x hc0)
  rw [jQ_jQ_eq hQ hc hx] at h
  have := smul_nonneg (show (0 : ℝ) ≤ 2⁻¹ by norm_num) h
  rwa [_root_.smul_smul, show (2⁻¹ : ℝ) * 2 = 1 by norm_num, one_smul] at this

/-- In the corner: `a ∈ V₁(P)` ⟹ `a² ≤ K P` for some `K ≥ 0`. -/
theorem sq_le_corner {P a : V} (hP : P * P = P) (ha : a ∈ peirce P 1) :
    ∃ K : ℝ, 0 ≤ K ∧ a * a ≤ K • P := by
  set r := ousNorm V a + 1
  have hr : 0 < r := by have := ousNorm_nonneg_rc a; simp only [r]; linarith
  obtain ⟨-, h2⟩ := jb_sq_bounds (a := a) hr (by simp only [r]; linarith)
  refine ⟨r * r, by positivity, ?_⟩
  have hd := JBMac.jQ_nonneg P (sub_nonneg.2 h2)
  have hu : ∀ z : V, ouUnit V * z = z := JBAlgebra.one_mul
  have e1 : jQ P ((r * r) • ouUnit V - a * a) = (r * r) • P - a * a := by
    have l : jQ P ((r * r) • ouUnit V - a * a) = (r * r) • jQ P (ouUnit V) - jQ P (a * a) := by
      simp only [jQ, jmul_sub, jmul_smul]; module
    rw [l, jQ_apply_unit P hu, hP, ← P1_eq_jQ hP, P1_of_mem1 (peirce_one_mul_one hP ha ha)]
  rw [e1] at hd
  exact sub_nonneg.1 hd

end JB

/-! ## 2. The Hilbert space of a positive semidefinite form -/

noncomputable section

/-- A symmetric positive semidefinite bilinear form on a real vector space. -/
structure PsdForm (W : Type v) [AddCommGroup W] [Module ℝ W] where
  B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ
  symm : ∀ x y, B x y = B y x
  nonneg : ∀ x, 0 ≤ B x x

variable {W : Type v} [AddCommGroup W] [Module ℝ W]

/-- The complexification `W ⊕ iW` of the space of a form. -/
@[ext]
structure Cx (β : PsdForm W) where
  re : W
  im : W

namespace Cx

variable {β : PsdForm W}

/-- `Cx β ≃ W × W`. -/
def equivProd (β : PsdForm W) : Cx β ≃ W × W where
  toFun u := (u.re, u.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (Cx β) := (equivProd β).addCommGroup

@[simp] theorem add_re (u w : Cx β) : (u + w).re = u.re + w.re := rfl
@[simp] theorem add_im (u w : Cx β) : (u + w).im = u.im + w.im := rfl
@[simp] theorem zero_re : (0 : Cx β).re = 0 := rfl
@[simp] theorem zero_im : (0 : Cx β).im = 0 := rfl
@[simp] theorem neg_re (u : Cx β) : (-u).re = -u.re := rfl
@[simp] theorem neg_im (u : Cx β) : (-u).im = -u.im := rfl

instance : SMul ℂ (Cx β) where
  smul z u := ⟨z.re • u.re - z.im • u.im, z.re • u.im + z.im • u.re⟩

@[simp] theorem smul_re (z : ℂ) (u : Cx β) : (z • u).re = z.re • u.re - z.im • u.im := rfl
@[simp] theorem smul_im (z : ℂ) (u : Cx β) : (z • u).im = z.re • u.im + z.im • u.re := rfl

instance : Module ℂ (Cx β) where
  one_smul u := by ext <;> simp
  mul_smul z w u := by
    ext <;> simp only [smul_re, smul_im, Complex.mul_re, Complex.mul_im] <;> module
  smul_zero z := by ext <;> simp
  smul_add z u w := by ext <;> simp only [smul_re, smul_im, add_re, add_im] <;> module
  add_smul z w u := by
    ext <;> simp only [smul_re, smul_im, add_re, add_im, Complex.add_re, Complex.add_im] <;> module
  zero_smul u := by ext <;> simp

/-- The Hermitian form `⟨x + iy, x' + iy'⟩ = β(x,x') + β(y,y') + i(β(x,y') − β(y,x'))`. -/
def inn (u w : Cx β) : ℂ :=
  ⟨β.B u.re w.re + β.B u.im w.im, β.B u.re w.im - β.B u.im w.re⟩

instance core : PreInnerProductSpace.Core ℂ (Cx β) where
  inner := inn
  conj_inner_symm u w := by
    apply Complex.ext <;> simp [inn, β.symm u.re, β.symm u.im]
  re_inner_nonneg u := by
    simp only [inn, RCLike.re_to_complex]
    exact add_nonneg (β.nonneg _) (β.nonneg _)
  add_left u w z := by
    apply Complex.ext <;> simp [inn] <;> ring
  smul_left u w r := by
    apply Complex.ext <;> simp [inn] <;> ring

instance : SeminormedAddCommGroup (Cx β) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (Cx β) := InnerProductSpace.ofCore core

theorem inner_eq (u w : Cx β) : inner ℂ u w = inn u w := rfl

theorem norm_sq (u : Cx β) : ‖u‖ ^ 2 = β.B u.re u.re + β.B u.im u.im := by
  rw [@norm_sq_eq_re_inner ℂ, inner_eq]; simp [inn]

end Cx

/-- The Hilbert space of `β`. -/
abbrev Hs (β : PsdForm W) := UniformSpace.Completion (Cx β)

section Ops

variable {β : PsdForm W}

/-- `T` is `β`-bounded. -/
def IsBdd (β : PsdForm W) (T : W →ₗ[ℝ] W) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ x, β.B (T x) (T x) ≤ K * β.B x x

/-- The complexification of a real operator. -/
def Tc (β : PsdForm W) (T : W →ₗ[ℝ] W) : Cx β →ₗ[ℂ] Cx β where
  toFun u := ⟨T u.re, T u.im⟩
  map_add' u w := by ext <;> simp
  map_smul' z u := by ext <;> simp

@[simp] theorem Tc_re (T : W →ₗ[ℝ] W) (u : Cx β) : (Tc β T u).re = T u.re := rfl
@[simp] theorem Tc_im (T : W →ₗ[ℝ] W) (u : Cx β) : (Tc β T u).im = T u.im := rfl

theorem Tc_bound {T : W →ₗ[ℝ] W} {K : ℝ} (hK : 0 ≤ K) (h : ∀ x, β.B (T x) (T x) ≤ K * β.B x x)
    (u : Cx β) : ‖Tc β T u‖ ≤ √K * ‖u‖ := by
  apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
  rw [mul_pow, Real.sq_sqrt hK, Cx.norm_sq, Cx.norm_sq, Tc_re, Tc_im]
  nlinarith [h u.re, h u.im]

/-- The bounded operator `opC T` on `Hs β` (zero when `T` is unbounded). -/
noncomputable def opC (β : PsdForm W) (T : W →ₗ[ℝ] W) : Hs β →L[ℂ] Hs β := by
  classical
  exact if h : IsBdd β T then
    ((Tc β T).mkContinuous (√h.choose) (Tc_bound h.choose_spec.1 h.choose_spec.2)).completion
  else 0

theorem opC_coe {T : W →ₗ[ℝ] W} (h : IsBdd β T) (u : Cx β) :
    opC β T (u : Hs β) = ((Tc β T u : Cx β) : Hs β) := by
  simp only [opC, dif_pos h, ContinuousLinearMap.completion_apply_coe,
    LinearMap.mkContinuous_apply]

theorem clm_ext {f g : Hs β →L[ℂ] Hs β} (h : ∀ u : Cx β, f u = g u) : f = g :=
  ContinuousLinearMap.ext fun z =>
    UniformSpace.Completion.induction_on z (isClosed_eq f.continuous g.continuous) h

theorem isBdd_add {T S : W →ₗ[ℝ] W} (hT : IsBdd β T) (hS : IsBdd β S) : IsBdd β (T + S) := by
  obtain ⟨K, hK, hT⟩ := hT
  obtain ⟨L, hL, hS⟩ := hS
  refine ⟨2 * K + 2 * L, by linarith, fun x => ?_⟩
  have h := β.nonneg (T x - S x)
  simp only [map_sub, LinearMap.sub_apply, LinearMap.add_apply, map_add,
    LinearMap.add_apply] at h ⊢
  rw [β.symm (S x) (T x)] at h ⊢
  nlinarith [hT x, hS x, β.nonneg x]

theorem isBdd_smul (r : ℝ) {T : W →ₗ[ℝ] W} (hT : IsBdd β T) : IsBdd β (r • T) := by
  obtain ⟨K, hK, hT⟩ := hT
  refine ⟨r * r * K, mul_nonneg (mul_self_nonneg r) hK, fun x => ?_⟩
  simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  nlinarith [hT x, mul_self_nonneg r]

theorem isBdd_comp {T S : W →ₗ[ℝ] W} (hT : IsBdd β T) (hS : IsBdd β S) : IsBdd β (T ∘ₗ S) := by
  obtain ⟨K, hK, hT⟩ := hT
  obtain ⟨L, hL, hS⟩ := hS
  refine ⟨K * L, mul_nonneg hK hL, fun x => ?_⟩
  simp only [LinearMap.comp_apply]
  calc β.B (T (S x)) (T (S x)) ≤ K * β.B (S x) (S x) := hT _
    _ ≤ K * (L * β.B x x) := mul_le_mul_of_nonneg_left (hS x) hK
    _ = K * L * β.B x x := by ring

theorem isBdd_id : IsBdd β LinearMap.id := ⟨1, zero_le_one, fun x => by simp⟩

theorem opC_add {T S : W →ₗ[ℝ] W} (hT : IsBdd β T) (hS : IsBdd β S) :
    opC β (T + S) = opC β T + opC β S :=
  clm_ext fun u => by
    rw [ContinuousLinearMap.add_apply, opC_coe (isBdd_add hT hS), opC_coe hT, opC_coe hS,
      ← UniformSpace.Completion.coe_add]
    rfl

theorem opC_smul (r : ℝ) {T : W →ₗ[ℝ] W} (hT : IsBdd β T) :
    opC β (r • T) = (r : ℂ) • opC β T :=
  clm_ext fun u => by
    rw [ContinuousLinearMap.smul_apply, opC_coe (isBdd_smul r hT), opC_coe hT,
      ← UniformSpace.Completion.coe_smul]
    congr 1
    ext
    · show r • T u.re = (r : ℂ).re • T u.re - (r : ℂ).im • T u.im
      simp
    · show r • T u.im = (r : ℂ).re • T u.im + (r : ℂ).im • T u.re
      simp

theorem opC_comp {T S : W →ₗ[ℝ] W} (hT : IsBdd β T) (hS : IsBdd β S) :
    opC β (T ∘ₗ S) = opC β T * opC β S :=
  clm_ext fun u => by
    rw [ContinuousLinearMap.mul_apply, opC_coe (isBdd_comp hT hS), opC_coe hS, opC_coe hT]
    rfl

theorem opC_id : opC β LinearMap.id = 1 :=
  clm_ext fun u => by
    rw [opC_coe isBdd_id]; rfl

theorem opC_selfAdjoint {T : W →ₗ[ℝ] W} (hT : IsBdd β T)
    (hs : ∀ x y, β.B (T x) y = β.B x (T y)) : IsSelfAdjoint (opC β T) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro z w
  refine UniformSpace.Completion.induction_on₂ z w
    (p := fun z w => inner ℂ (opC β T z) w = inner ℂ z (opC β T w))
    (isClosed_eq (by fun_prop) (by fun_prop)) fun u w => ?_
  show inner ℂ (opC β T u) (w : Hs β) = inner ℂ (u : Hs β) (opC β T w)
  rw [opC_coe hT, opC_coe hT, UniformSpace.Completion.inner_coe,
    UniformSpace.Completion.inner_coe, Cx.inner_eq, Cx.inner_eq]
  simp only [Cx.inn, Tc_re, Tc_im, hs]

theorem one_ne_zero_of_pos {x : W} (hx : 0 < β.B x x) : (1 : Hs β →L[ℂ] Hs β) ≠ 0 := by
  intro h
  have := congrArg (fun f : Hs β →L[ℂ] Hs β => ‖f ((⟨x, 0⟩ : Cx β) : Hs β)‖) h
  simp only [ContinuousLinearMap.one_apply, ContinuousLinearMap.zero_apply, norm_zero,
    UniformSpace.Completion.norm_coe] at this
  have h2 := Cx.norm_sq (β := β) ⟨x, 0⟩
  rw [this] at h2
  simp at h2
  linarith

end Ops

end

/-! ## 3. The core: no Jordan copy of a purely exceptional algebra in an exchangeable corner -/

noncomputable section

section Core

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

variable {P Q : V}

/-- The joint off-diagonal Peirce space `V½(P) ∩ V½(Q)`. -/
def Wsp (P Q : V) : Submodule ℝ V := peirce P (1 / 2) ⊓ peirce Q (1 / 2)

theorem Q_mul_of_one (hP : P * P = P) (hPQ : P * Q = 0) {c : V} (hc : c ∈ peirce P 1) :
    Q * c = 0 := by
  rw [jmul_comm]; exact peirce_one_mul_zero hP hc (mem_peirce_zero_of_orth hPQ)

theorem mul_mem_Wsp (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0) {c : V}
    (hc : c ∈ peirce P 1) {x : V} (hx : x ∈ Wsp P Q) : c * x ∈ Wsp P Q :=
  ⟨peirce_one_mul_half hP hc hx.1,
    peirce_zero_mul_half hQ (mem_peirce_zero_of_orth (Q_mul_of_one hP hPQ hc)) hx.2⟩

/-- `x ↦ 2cx` on `W`, for `c ∈ V₁(P)`. -/
def Lc (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0) (c : V) (hc : c ∈ peirce P 1) :
    Wsp P Q →ₗ[ℝ] Wsp P Q where
  toFun x := ⟨(2 : ℝ) • (c * x.1), Submodule.smul_mem _ _ (mul_mem_Wsp hP hQ hPQ hc x.2)⟩
  map_add' x y := Subtype.ext (by
    simp only [Submodule.coe_add, jmul_add, smul_add])
  map_smul' r x := Subtype.ext (by
    simp only [Submodule.coe_smul, jmul_smul, RingHom.id_apply]; rw [smul_comm])


theorem Lc_val (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0) (c : V)
    (hc : c ∈ peirce P 1) (x : Wsp P Q) : (Lc hP hQ hPQ c hc x).1 = (2 : ℝ) • (c * x.1) := rfl

/-- The Peirce form `β(x, y) = φ(Q(xy))` on `W`. -/
def formW (hQ : Q * Q = Q) (φ : V →ₗ[ℝ] ℝ) (hφ : ∀ z, 0 ≤ z → 0 ≤ φ z) :
    PsdForm (Wsp P Q) where
  B := LinearMap.mk₂ ℝ (fun x y => φ (Q * (x.1 * y.1)))
    (fun x x' y => by simp only [Submodule.coe_add, jadd_mul, jmul_add, map_add])
    (fun r x y => by simp only [Submodule.coe_smul, jsmul_mul, jmul_smul, map_smul, smul_eq_mul])
    (fun x y y' => by simp only [Submodule.coe_add, jmul_add, map_add])
    (fun r x y => by simp only [Submodule.coe_smul, jmul_smul, map_smul, smul_eq_mul])
  symm x y := by simp only [LinearMap.mk₂_apply]; rw [jmul_comm x.1]
  nonneg x := hφ _ (form_self_nonneg hQ x.2.2)


theorem formW_apply (hQ : Q * Q = Q) (φ : V →ₗ[ℝ] ℝ) (hφ : ∀ z, 0 ≤ z → 0 ≤ φ z)
    (x y : Wsp P Q) : (formW hQ φ hφ).B x y = φ (Q * (x.1 * y.1)) := rfl

variable (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0)

include hP hQ hPQ

/-- `L` is a Jordan map: `L_{cd} = ½(L_c L_d + L_d L_c)` (`peirce_spec`). -/
theorem Lc_mul {c d : V} (hc : c ∈ peirce P 1) (hd : d ∈ peirce P 1) :
    Lc hP hQ hPQ (c * d) (peirce_one_mul_one hP hc hd) =
      (2⁻¹ : ℝ) • (Lc hP hQ hPQ c hc ∘ₗ Lc hP hQ hPQ d hd + Lc hP hQ hPQ d hd ∘ₗ Lc hP hQ hPQ c hc) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  simp only [Lc_val, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    Submodule.coe_smul, Submodule.coe_add, jmul_smul]
  rw [peirce_spec hP hc hd x.2.1]
  module

theorem Lc_P : Lc hP hQ hPQ P (by rw [mem_peirce, one_smul]; exact hP) = LinearMap.id := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  simp only [Lc_val, LinearMap.id_apply]
  rw [x.2.1, _root_.smul_smul]; norm_num

theorem Lc_symm (φ : V →ₗ[ℝ] ℝ) (hφ : ∀ z, 0 ≤ z → 0 ≤ φ z) {c : V} (hc : c ∈ peirce P 1)
    (x y : Wsp P Q) :
    (formW hQ φ hφ).B (Lc hP hQ hPQ c hc x) y = (formW hQ φ hφ).B x (Lc hP hQ hPQ c hc y) := by
  simp only [formW_apply, Lc_val, jsmul_mul, jmul_smul]
  have hcQ : c * Q = 0 := by rw [jmul_comm]; exact Q_mul_of_one hP hPQ hc
  rw [form_symm hcQ x.2.2 y.2.2, jmul_comm x.1]

theorem Lc_bdd (φ : V →ₗ[ℝ] ℝ) (hφ : ∀ z, 0 ≤ z → 0 ≤ φ z) {c : V} (hc : c ∈ peirce P 1) :
    IsBdd (formW hQ φ hφ) (Lc hP hQ hPQ c hc) := by
  obtain ⟨K, hK, hle⟩ := sq_le_corner hP hc
  refine ⟨K, hK, fun x => ?_⟩
  simp only [formW_apply, Lc_val, jsmul_mul, jmul_smul]
  have hcQ : c * Q = 0 := by rw [jmul_comm]; exact Q_mul_of_one hP hPQ hc
  -- `Q((cx)(cx)) = ½ Q(((cc)x)x)`
  have e1 : Q * (c * x.1 * (c * x.1)) = (2⁻¹ : ℝ) • (Q * (c * c * x.1 * x.1)) := by
    rw [form_symm hcQ x.2.2 (mul_mem_Wsp hP hQ hPQ hc x.2).2,
      peirce_spec hP hc hc x.2.1]
    rw [jadd_mul, jmul_add]; module
  -- positivity at `d = K P − c²`
  set d := K • P - c * c with hd
  have hdQ : Q * d = 0 := by
    rw [hd, jmul_sub, jmul_smul, jmul_comm Q P, hPQ, smul_zero, zero_sub,
      Q_mul_of_one hP hPQ (peirce_one_mul_one hP hc hc), neg_zero]
  have hpos := form_pos hQ hdQ (sub_nonneg.2 hle) x.2.2
  have hPx : P * x.1 = (1 / 2 : ℝ) • x.1 := x.2.1
  rw [hd, jsub_mul, jsmul_mul, hPx, jsub_mul, jsmul_mul, jsmul_mul, jmul_sub, jmul_smul] at hpos
  have := hφ _ hpos
  rw [e1]
  simp only [jmul_smul, map_sub, map_smul, smul_eq_mul] at this ⊢
  linarith

/-- **No Jordan copy of a purely exceptional algebra in a connected corner.**  `V` a
JB-algebra, `P ⊥ Q` idempotents connected by `w` (`w ∈ V½(P) ∩ V½(Q)`, `w² = P + Q`),
`Q ≠ 0`; `U` purely exceptional with a Jordan homomorphism `ψ : U → V`, `ψ 1 = P`.  Then
`a ↦ 2ψ(a)·` on the Hilbert space of the Peirce form `φ(Q(xy))` on `V½(P) ∩ V½(Q)` is a
non-zero Jordan homomorphism of `U` into the C*-algebra `B(Hs)`: contradiction. -/
theorem corner_absurd {U : Type v} [AddCommGroup U] [Module ℝ U] [PartialOrder U]
    [OrderUnitSpace U] [Mul U] (hpe : IsPurelyExceptional.{v, v} U)
    (hu : ∀ a : U, ouUnit U * a = a) (ψ : U →ₗ[ℝ] V) (hψ : ∀ a b, ψ (a * b) = ψ a * ψ b)
    (hψ1 : ψ (ouUnit U) = P) {w : V} (hwP : w ∈ peirce P (1 / 2))
    (hwQ : w ∈ peirce Q (1 / 2)) (hw : w * w = P + Q) (hQ0 : Q ≠ 0) : False := by
  -- a state positive at `Q`
  obtain ⟨f, hf, hfQ⟩ := JBCalc.exists_state_abs_eq_norm hQ0
  let φ : V →ₗ[ℝ] ℝ :=
    { toFun := f, map_add' := hf.1, map_smul' := fun r x => by
        rw [hf.2.1 r x, RingHom.id_apply, smul_eq_mul] }
  have hφ : ∀ z, 0 ≤ z → 0 ≤ φ z := hf.2.2.1
  have hQpos : 0 < φ Q := by
    have hQn : 0 ≤ Q := by rw [← hQ]; exact jb_sq_nonneg Q
    have h1 : 0 < ousNorm V Q := lt_of_le_of_ne (ousNorm_nonneg_rc Q)
      (fun h => hQ0 (IsOUS.norm_eq_zero Q h.symm))
    have h2 : 0 ≤ f Q := hf.2.2.1 Q hQn
    show 0 < f Q
    rw [abs_of_nonneg h2] at hfQ; linarith
  set β := formW hQ φ hφ with hβ
  have hmem : ∀ a, ψ a ∈ peirce P 1 := fun a => by
    rw [mem_peirce, one_smul, ← hψ1, ← hψ, hu]
  let T : U → Wsp P Q →ₗ[ℝ] Wsp P Q := fun a => Lc hP hQ hPQ (ψ a) (hmem a)
  have hTb : ∀ a, IsBdd β (T a) := fun a => Lc_bdd hP hQ hPQ φ hφ (hmem a)
  have hTadd : ∀ a b, T (a + b) = T a + T b := fun a b =>
    LinearMap.ext fun x => Subtype.ext (by
      simp only [T, Lc_val, LinearMap.add_apply, Submodule.coe_add, map_add, jadd_mul, smul_add])
  have hTsmul : ∀ (r : ℝ) a, T (r • a) = r • T a := fun r a =>
    LinearMap.ext fun x => Subtype.ext (by
      simp only [T, Lc_val, LinearMap.smul_apply, Submodule.coe_smul, map_smul, jsmul_mul]
      rw [smul_comm])
  have hTmul : ∀ a b, T (a * b) = (2⁻¹ : ℝ) • (T a ∘ₗ T b + T b ∘ₗ T a) := fun a b => by
    have h := Lc_mul hP hQ hPQ (hmem a) (hmem b)
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hx := congrArg (fun L : Wsp P Q →ₗ[ℝ] Wsp P Q => (L x).1) h
    rw [← hx]
    simp only [T, Lc_val, hψ]
  have hT1 : T (ouUnit U) = LinearMap.id := LinearMap.ext fun x => Subtype.ext (by
    simp only [T, Lc_val, hψ1, LinearMap.id_apply]
    rw [x.2.1, _root_.smul_smul]; norm_num)
  have hsm : ∀ (r : ℝ) (A : Hs β →L[ℂ] Hs β), (r : ℂ) • A = r • A := fun r A =>
    (RCLike.real_smul_eq_coe_smul (K := ℂ) r A).symm
  let Φ : U →ₗ[ℝ] (Hs β →L[ℂ] Hs β) :=
    { toFun := fun a => opC β (T a)
      map_add' := fun a b => by rw [hTadd, opC_add (hTb a) (hTb b)]
      map_smul' := fun r a => by
        rw [hTsmul, opC_smul r (hTb a), RingHom.id_apply, hsm] }
  have hΦJ : IsJordanHomInto U (Hs β →L[ℂ] Hs β) Φ := by
    refine ⟨fun a => opC_selfAdjoint (hTb a) (Lc_symm hP hQ hPQ φ hφ (hmem a)), fun a b => ?_⟩
    show opC β (T (a * b)) = _
    have hab := isBdd_comp (hTb a) (hTb b)
    have hba := isBdd_comp (hTb b) (hTb a)
    rw [hTmul, opC_smul _ (isBdd_add hab hba), opC_add hab hba, opC_comp (hTb a) (hTb b),
      opC_comp (hTb b) (hTb a), hsm]
    rfl
  have h0 := hpe (Hs β →L[ℂ] Hs β) Φ hΦJ
  have h1 : Φ (ouUnit U) = 1 := by
    show opC β (T (ouUnit U)) = 1
    rw [hT1, opC_id]
  refine one_ne_zero_of_pos (β := β) (x := ⟨w, hwP, hwQ⟩) ?_ (by rw [← h1, h0]; rfl)
  rw [hβ, formW_apply]
  show 0 < φ (Q * (w * w))
  rw [hw, jmul_add, jmul_comm Q P, hPQ, zero_add, hQ]
  exact hQpos

end Core

end

/-! ## 4. A corner lemma: a map commuting with `P` compresses to a Jordan map -/

section Compress

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [IsJordanMul V]

/-- If `x, y` have no `½`-part for `P` (`P(Px) = Px`), then `P(xy) = (Px)(Py)`. -/
theorem compress_mul {P x y : V} (hP : P * P = P) (hx : P * (P * x) = P * x)
    (hy : P * (P * y) = P * y) : P * (x * y) = (P * x) * (P * y) := by
  have hx1 : P * x ∈ peirce P 1 := by rw [mem_peirce, one_smul]; exact hx
  have hy1 : P * y ∈ peirce P 1 := by rw [mem_peirce, one_smul]; exact hy
  have hx0 : x - P * x ∈ peirce P 0 := by rw [mem_peirce, jmul_sub, hx, sub_self, zero_smul]
  have hy0 : y - P * y ∈ peirce P 0 := by rw [mem_peirce, jmul_sub, hy, sub_self, zero_smul]
  have e : x * y = (P * x) * (P * y) + (P * x) * (y - P * y) + (x - P * x) * (P * y)
      + (x - P * x) * (y - P * y) := by
    simp only [jmul_sub, jsub_mul]; abel
  have h11 := peirce_one_mul_one hP hx1 hy1
  have h00 := peirce_zero_mul_zero hP hx0 hy0
  rw [mem_peirce, one_smul] at h11
  rw [mem_peirce, zero_smul] at h00
  rw [e, peirce_one_mul_zero hP hx1 hy0, jmul_comm (x - P * x), peirce_one_mul_zero hP hy1 hx0,
    add_zero, add_zero, jmul_add, h11, h00, add_zero]

end Compress

/-! ## 5. REC glue: REC 135 and 136 from `JBWExceptionalSummand` alone -/

section Rec135Summand

open CategoryTheory MonoidalCategory SequentialEffectus
open scoped unitInterval

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)
  (φ₀ : EffectMonoidHom (Scal C) I) (ψ₀ : EffectMonoidHom I (Scal C))
  (h1 : ∀ k, ψ₀.toFun (φ₀.toFun k) = k) (h2 : ∀ r, φ₀.toFun (ψ₀.toFun r) = r)

include h1 h2 in
/-- The contradiction without `ExceptionalNoFourExch`: a purely exceptional `V_W ≠ 0` is
impossible.  `pe_exists_exch_pair` gives `p ⊥ q` exchanged by a symmetry `s`; in `V_{W⊗W}`,
`P = 1 ⊗ p`, `Q = 1 ⊗ q` are orthogonal idempotents exchanged by `1 ⊗ s` (REC 127, second
map), `Q ≠ 0`, and `a ↦ P(a ⊗ 1) = a ⊗ p` is a Jordan homomorphism with `1 ↦ P` (REC 127,
REC 121's formula for `P·`, `compress_mul`); `corner_absurd` concludes. -/
theorem summand_absurd [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
    [MonoidalSequentialEffectus C] {W : C} (hW : Nonempty (Stat W))
    (hpe : letI := jbMul (realSplit ψ₀) hRC h119 W;
      IsPurelyExceptional.{v, v} (VA (realSplit ψ₀) W)) : False := by
  set σs := realSplit ψ₀ with hσs
  have h0 : σs.s = 0 := rfl
  have hWne : ouUnit (VA σs W) ≠ 0 := unit_ne_zero_real φ₀ ψ₀ hW
  let iW := jbMul σs hRC h119 W
  have jW : JBWAlgebra (VA σs W) := jbw_real hRC h119 φ₀ ψ₀ h1 h2 W
  obtain ⟨p, q, hpq, -, hq0, hp, hq, s, hs, hspq⟩ := JBWProj.pe_exists_exch_pair hpe hWne
  let iX := jbMul σs hRC h119 (W ⊗ W)
  have jX : JBWAlgebra (VA σs (W ⊗ W)) := jbw_real hRC h119 φ₀ ψ₀ h1 h2 (W ⊗ W)
  have hκ : ∀ b b' : VA σs W, tensV σs (ouUnit (VA σs W)) b * tensV σs (ouUnit (VA σs W)) b'
      = tensV σs (ouUnit (VA σs W)) (b * b') := (rec127_right σs hRC h119 h0 W W).1
  have hι : ∀ a a' : VA σs W, tensV σs a (ouUnit (VA σs W)) * tensV σs a' (ouUnit (VA σs W))
      = tensV σs (a * a') (ouUnit (VA σs W)) := (rec127 σs hRC h119 h0 W W).1
  set P := tensV σs (ouUnit (VA σs W)) p with hPdef
  set Q := tensV σs (ouUnit (VA σs W)) q with hQdef
  set S := tensV σs (ouUnit (VA σs W)) s with hSdef
  have hP : P * P = P := by rw [hκ, hp]
  have hQ : Q * Q = Q := by rw [hκ, hq]
  have hPQ : P * Q = 0 := by rw [hκ, hpq, tensV_zero_right]
  have hS : S * S = ouUnit (VA σs (W ⊗ W)) := by
    rw [hκ]; rw [show s * s = ouUnit (VA σs W) from hs]; exact tensV_unit σs
  have hSP : jQ S P = Q := by
    rw [hQdef, hSdef, hPdef, ← hspq]
    simp only [jQ, hκ, ← tensV_smul_right, ← tensV_sub_right]
  obtain ⟨w, hwP, hwQ, hww⟩ :=
    JBPeirce.exch_connect (u' := ouUnit (VA σs (W ⊗ W))) JBAlgebra.one_mul hP hPQ hS hSP
  have hQ0 : Q ≠ 0 := tens_ne_zero φ₀ ψ₀ h1 h2 hWne hq0
  -- `P (a ⊗ t) = a ⊗ (p t)` (REC 121's formula for `P·`, both sides)
  obtain ⟨y, hy, hpy⟩ := jm_idem_gmap σs hRC h119 W hp
  have h1y : Papers.SEA.IsIdempotent (1 : CPt σs W) := Papers.SEA.one_seq _
  have hPg : P = GP.gmap (cptTens σs 1 y) := by
    rw [hPdef, hpy, ← tensV_gmap]; rfl
  have hPt : ∀ a t : VA σs W, P * tensV σs a t = tensV σs a (p * t) := by
    intro a t
    have e1 : GP.gmap (cptTens σs 1 y) * tensV σs a t = _ :=
      jm_form σs hRC h119 (W ⊗ W) (cptTens σs 1 y) (cptTens_idem σs h0 h1y hy) (tensV σs a t)
    have e2 : GP.gmap y * t = _ := jm_form σs hRC h119 W y hy t
    rw [hPg, hpy, e1, e2]
    change (2⁻¹ : ℝ) • (tensV σs a t + (Uop σs (cptTens σs 1 y) (tensV σs a t) -
      Uop σs (orth (cptTens σs 1 y)) (tensV σs a t))) =
      tensV σs a ((2⁻¹ : ℝ) • (t + (Uop σs y t - Uop σs (orth y) t)))
    rw [orth_cptTens_one' σs h0, Uop_cptTens_apply σs h0, Uop_cptTens_apply σs h0, Uop_one σs h0,
      tensV_smul_right, tensV_add_right, tensV_sub_right]
  -- the compressed embedding `ψ a = P (a ⊗ 1)`
  let ι : VA σs W →ₗ[ℝ] VA σs (W ⊗ W) := vtens σs (A := W) (B := W) (ouUnit (VA σs W))
  have hιa : ∀ a, ι a = tensV σs a (ouUnit (VA σs W)) := fun a => rfl
  let ψ : VA σs W →ₗ[ℝ] VA σs (W ⊗ W) := jbT P ∘ₗ ι
  have hψa : ∀ a, ψ a = P * tensV σs a (ouUnit (VA σs W)) := fun a => rfl
  have hPP : ∀ a, P * (P * ι a) = P * ι a := by
    intro a
    rw [hιa, hPt, hPt, JBAlgebra.mul_one, hp]
  have hψ : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    rw [hψa, hψa, hψa, ← hι]
    exact compress_mul hP (hPP a) (hPP b)
  have hψ1 : ψ (ouUnit (VA σs W)) = P := by
    rw [hψa, tensV_unit σs, JBAlgebra.mul_one]
  exact corner_absurd hP hQ hPQ hpe JBAlgebra.one_mul ψ hψ hψ1 hwP hwQ hww hQ0

include h1 h2 in
/-- **REC 135** (short.tex:2395, Proposition) from `JBWExceptionalSummand` (a corollary of
REC 52) alone: with scalars `[0,1]`, every `V_A` is a JW-algebra. -/
theorem rec135_summand (hP : JBWExceptionalSummand.{v})
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
    [MonoidalSequentialEffectus C] (A : C) :
    letI := jbMul (realSplit ψ₀) hRC h119 A; IsJWAlgebra (VA (realSplit ψ₀) A) := by
  set σs := realSplit ψ₀ with hσs
  have h0 : σs.s = 0 := rfl
  let iA := jbMul σs hRC h119 A
  rcases hP (VA σs A) (jbw_real hRC h119 φ₀ ψ₀ h1 h2 A) with hJW | ⟨c, hc0, hcc, hcen, hvan⟩
  · exact hJW
  exfalso
  obtain ⟨W, hW, hpe, -⟩ := corner_of_summand σs hRC h119 h0 A hc0 hcc hcen hvan
  exact summand_absurd hRC h119 φ₀ ψ₀ h1 h2 hW hpe

end Rec135Summand

section Rec136Summand

open CategoryTheory MonoidalCategory SequentialEffectus
open scoped unitInterval

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  [MonoidalSequentialEffectus C]
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

include hRC h119 in
/-- **REC 136** (`thm:JW-algebra`, short.tex:2409, Theorem), statement exactly as `rec136`,
from `JBWExceptionalSummand` alone; proof as `rec136_nofour`, with `rec135_summand`. -/
theorem rec136_summand (hP : JBWExceptionalSummand.{v})
    (hirr : IsIrreducible (Scal C)) (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) := by
  rcases seq_scal_cases hirr with h | h | ⟨φ₀, ψ₀, h1, h2⟩
  · set σs := trivSplit h
    have hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hRC h119 A) := fun A =>
      haveI := va_subsingleton h A
      @JBWAlgebra.mk (VA σs A) _ _ _ _ (jbMul σs hRC h119 A) (jbMul_spec σs hRC h119 A)
        (VA_dc σs A) (fun a b hab => (hab (Subsingleton.elim a b)).elim)
    have hJW : ∀ A : C, letI := jbMul σs hRC h119 A; IsJWAlgebra (VA σs A) := fun A =>
      haveI := va_subsingleton h A
      @isJW_of_subsingleton (VA σs A) _ _ _ _ (jbMul σs hRC h119 A) _
    exact jwFunctor_spec hRC h119 σs rfl hJBW hJW
  · exact (h01 h).elim
  · exact jwFunctor_spec hRC h119 (realSplit ψ₀) rfl
      (jbw_real hRC h119 φ₀ ψ₀ h1 h2) (rec135_summand hRC h119 φ₀ ψ₀ h1 h2 hP)

/-- **REC 136** (`rec136_hypfree`'s statement) with REC 119 and REC 121's criterion
discharged, from `JBWExceptionalSummand` (corollary of REC 52) alone: the
`ExceptionalNoFourExch` input of `rec136_nofour_hypfree` is not needed. -/
theorem rec136_summand_hypfree (hP : JBWExceptionalSummand.{v})
    (hirr : IsIrreducible (Scal C)) (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) :=
  rec136_summand alfsenShultzResolventCriterion_holds weteringStateOrderLemma_holds hP hirr h01

/-- **REC 136** from REC 52 (Hanche-Olsen–Størmer) alone. -/
theorem rec136_HOS (hHOS : HancheOlsenStormerDecomposition.{v})
    (hirr : IsIrreducible (Scal C)) (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) :=
  rec136_summand_hypfree (jbwExceptionalSummand_of_HOS hHOS) hirr h01

end Rec136Summand

end Papers.REC.JBCoord

#print axioms Papers.REC.JBCoord.corner_absurd
#print axioms Papers.REC.JBCoord.summand_absurd
#print axioms Papers.REC.JBCoord.rec136_summand_hypfree
#print axioms Papers.REC.JBCoord.rec136_HOS
