import Papers.EJA.Appendix
import Papers.EJA.Fundamental

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

/-!
# EJA, appendix (continued) and the examples

A. Westerbaan, B. Westerbaan, J. van de Wetering, *Pure Maps between Euclidean
Jordan Algebras*, QPL 2018, `../papers/1805.11496/main.tex`.

This file formalises, for the paper's own (possibly infinite-dimensional)
Euclidean Jordan algebras `PaperEJA` (EJA 1), the rest of Appendix A
(EJA 42–54), and Example 3 (the matrix algebras `M_n(F)^sa`).

## The route, and where it leaves the print

The print reaches the spectral theorem (Cor 46) through Prop 45, "an
associative EJA is `ℝⁿ`", which it proves with **Kadison's representation
theorem** (an associative complete Archimedean order unit space is `C(X)`),
together with the real operator square roots of `B(E)`.  Neither is in
Mathlib.  Prop 45 is proved here **without Kadison**, by an elementary
Hilbert-space argument that uses only EJA 41 (the product is bounded,
`‖a * b‖ ≤ r ‖a‖ ‖b‖`):

* a non-zero idempotent has `‖p‖ ≥ 1/r` (`p = p * p`), and orthogonal
  idempotents are orthogonal vectors with `⟨1, p⟩ = ‖p‖²`; so a family of
  pairwise orthogonal non-zero idempotents has at most `r² ‖1‖²` members
  (`IsIdemFamily.card_le`);
* hence `1` is a sum of idempotents that are minimal in a given closed
  associative subalgebra `S` (`exists_minimal_family`);
* for such a minimal `e`, the corner `K = e S` is a field: for `0 ≠ x ∈ K`
  the closure of the ideal `x S` is all of `K` (otherwise the projection of
  `e` onto the orthogonal complement of the ideal inside `K` would be a
  smaller idempotent), so it contains an element within `1/r` of `e`, which
  is invertible by a Neumann series (`corner_inv`);
* and a field of this kind is `ℝ e`: with `M` the supremum of the Rayleigh
  quotient of `L_a` on `K`, `M e − e a` is not invertible because `M` is an
  approximate eigenvalue (`corner_scalar`).

So every element of a closed associative subalgebra is a finite linear
combination of orthogonal idempotents (`assocSub_decomp`), which gives 45 and
46; 47–53 then follow the print (with the order unit norm computed from the
spectral decomposition).  EJA 54 rests on the Hanche-Olsen–Størmer
classification of type I JBW factors, which is taken as an explicit
hypothesis (`HOSClassification`); the reduction of an EJA to a finite direct
sum of factors, which the print also cites, is proved (`appendixjnw`).

## Contents

* EJA 42–43: `PaperJordan` (the algebraic half of EJA 1), `jL`, `jpow`,
  `jaeqs_1a`–`jaeqs_3b`.
* EJA 44–46: `cor_assocalg`, `associsdisc`, `cor_spectral`.
* EJA 47–53: `selfduality`, `ejaous_add`/`paperOUS`/`ejaous_archimedean`,
  `equivalenttopology` (order unit norm `ouNorm`), `EJAisJB` (`IsJBNorm`),
  `dircomplete`/`state_normal`, `atomicsum`, `typeI_finiteRank`.
* EJA 54: `appendixjnw`, conditional on `HOSClassification`.
* EJA 3: `HermMat n F` for scalars `F` with a trace (`EJAScalars`);
  `matrix_examples` (`ℝ`, `ℂ`, `ℍ`); the octonions `Oct` (Cayley–Dickson) and
  `exceptional_of_jordan` (`M_3(𝕆)^sa`, conditional on its Jordan identity).
-/

namespace Papers.EJA

open scoped InnerProductSpace
open Theses.B.Eff

universe u

/-! ## Jordan algebras, EJA 42 and EJA 43 -/

section Jordan

/-- The algebraic half of **EJA 1** (main.tex:194, Definition): a *Jordan
algebra* is a real vector space with a commutative bilinear product, a unit,
and the Jordan identity `(a * b) * (a * a) = a * (b * (a * a))`.  The fields
are those of `PaperEJA` without the inner product; every `PaperEJA` is one
(`PaperEJA.toPaperJordan`). -/
class PaperJordan (V : Type u) [AddCommGroup V] [Module ℝ V] [Mul V] [One V] : Prop where
  protected mul_comm : ∀ a b : V, a * b = b * a
  protected mul_add : ∀ a b c : V, a * (b + c) = a * b + a * c
  protected smul_mul : ∀ (r : ℝ) (a b : V), (r • a) * b = r • (a * b)
  protected one_mul : ∀ a : V, 1 * a = a
  protected jordan : ∀ a b : V, (a * b) * (a * a) = a * (b * (a * a))

instance PaperEJA.toPaperJordan (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [Mul E] [One E] [PaperEJA E] : PaperJordan E :=
  ⟨PaperEJA.mul_comm, PaperEJA.mul_add, PaperEJA.smul_mul, PaperEJA.one_mul,
    PaperEJA.jordan⟩

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V] [PaperJordan V]

theorem pj_mul_comm (a b : V) : a * b = b * a := PaperJordan.mul_comm a b

theorem pj_mul_add (a b c : V) : a * (b + c) = a * b + a * c := PaperJordan.mul_add a b c

theorem pj_add_mul (a b c : V) : (a + b) * c = a * c + b * c := by
  rw [pj_mul_comm, pj_mul_add, pj_mul_comm c a, pj_mul_comm c b]

theorem pj_smul_mul (r : ℝ) (a b : V) : (r • a) * b = r • (a * b) := PaperJordan.smul_mul r a b

theorem pj_mul_smul (r : ℝ) (a b : V) : a * (r • b) = r • (a * b) := by
  rw [pj_mul_comm, pj_smul_mul, pj_mul_comm]

theorem pj_one_mul (a : V) : 1 * a = a := PaperJordan.one_mul a

theorem pj_mul_one (a : V) : a * 1 = a := by rw [pj_mul_comm, pj_one_mul]

theorem pj_jordan (a b : V) : (a * b) * (a * a) = a * (b * (a * a)) := PaperJordan.jordan a b

theorem pj_zero_mul (a : V) : (0 : V) * a = 0 := by
  have h := pj_smul_mul (0 : ℝ) (0 : V) a
  rwa [zero_smul, zero_smul] at h

theorem pj_mul_zero (a : V) : a * (0 : V) = 0 := by rw [pj_mul_comm, pj_zero_mul]

theorem pj_neg_mul (a b : V) : (-a) * b = -(a * b) := by
  have h := pj_smul_mul (-1 : ℝ) a b
  rwa [neg_one_smul, neg_one_smul] at h

theorem pj_mul_neg (a b : V) : a * (-b) = -(a * b) := by
  rw [pj_mul_comm, pj_neg_mul, pj_mul_comm]

theorem pj_mul_sub (a b c : V) : a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg, pj_mul_add, pj_mul_neg, ← sub_eq_add_neg]

theorem pj_sub_mul (a b c : V) : (a - b) * c = a * c - b * c := by
  rw [pj_mul_comm, pj_mul_sub, pj_mul_comm c a, pj_mul_comm c b]

/-- **EJA 42** (main.tex:1065, Notation), item 2: the multiplication
operator `L_a b = a * b`, a linear map. -/
def jL (a : V) : V →ₗ[ℝ] V where
  toFun b := a * b
  map_add' := pj_mul_add a
  map_smul' r b := pj_mul_smul r a b

@[simp] theorem jL_apply (a b : V) : jL a b = a * b := rfl

theorem jL_add (a b : V) : jL (a + b) = jL a + jL b :=
  LinearMap.ext fun c => pj_add_mul a b c

theorem jL_smul (r : ℝ) (a : V) : jL (r • a) = r • jL a :=
  LinearMap.ext fun c => pj_smul_mul r a c

theorem jL_one : jL (1 : V) = 1 := LinearMap.ext fun c => pj_one_mul c

/-- `a ↦ L_a` is linear. -/
def jLL : V →ₗ[ℝ] Module.End ℝ V where
  toFun := jL
  map_add' := jL_add
  map_smul' := jL_smul

theorem pj_sum_mul {ι : Type*} (s : Finset ι) (f : ι → V) (b : V) :
    (∑ i ∈ s, f i) * b = ∑ i ∈ s, f i * b := by
  rw [pj_mul_comm]
  exact (map_sum (jL b) f s).trans (Finset.sum_congr rfl fun i _ => pj_mul_comm b (f i))

theorem pj_mul_sum {ι : Type*} (s : Finset ι) (a : V) (f : ι → V) :
    a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i := map_sum (jL a) f s

/-- **EJA 42**, item 1: the powers `a⁰ = 1`, `aⁿ⁺¹ = a * aⁿ`. -/
def jpow (a : V) : ℕ → V
  | 0 => 1
  | (n + 1) => a * jpow a n

omit [AddCommGroup V] [Module ℝ V] [PaperJordan V] in
@[simp] theorem jpow_zero (a : V) : jpow a 0 = 1 := rfl

omit [AddCommGroup V] [Module ℝ V] [PaperJordan V] in
theorem jpow_succ (a : V) (n : ℕ) : jpow a (n + 1) = a * jpow a n := rfl

theorem jpow_one (a : V) : jpow a 1 = a := by rw [jpow_succ, jpow_zero, pj_mul_one]

theorem jpow_two (a : V) : jpow a 2 = a * a := by rw [jpow_succ, jpow_one]

/-- The commutative non-associative ring structure of a Jordan algebra, used
only to borrow Mathlib's linearisation of the Jordan identity. -/
def pjRing (W : Type u) [AddCommGroup W] [Module ℝ W] [Mul W] [One W] [PaperJordan W] :
    NonUnitalNonAssocCommRing W :=
  { (inferInstance : AddCommGroup W), (inferInstance : Mul W) with
    left_distrib := pj_mul_add
    right_distrib := pj_add_mul
    zero_mul := pj_zero_mul
    mul_zero := pj_mul_zero
    mul_comm := pj_mul_comm }

omit [Mul V] [One V] [PaperJordan V] in
theorem pj_eq_zero_of_two_nsmul {y : V} (h : (2 : ℕ) • y = 0) : y = 0 := by
  have h2 : ((2 : ℕ) : ℝ) • y = 0 := by rwa [Nat.cast_smul_eq_nsmul]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact h3

/-- The linearised Jordan identity, applied to a vector:
`[L_a, L_{bc}] + [L_b, L_{ca}] + [L_c, L_{ab}] = 0`.  Mathlib's
`two_nsmul_lie_lmul_lmul_add_add_eq_zero`, with the factor `2` cancelled. -/
theorem pj_lin (a b c w : V) :
    a * (b * c * w) - b * c * (a * w) + (b * (c * a * w) - c * a * (b * w))
      + (c * (a * b * w) - a * b * (c * w)) = 0 := by
  have hj : ∀ x y : V, x * y * (x * x) = x * (y * (x * x)) := pj_jordan
  refine pj_eq_zero_of_two_nsmul ?_
  let _inst := pjRing V
  have _inst2 : IsCommJordan V := ⟨hj⟩
  exact EuclideanJordanAlgebra.two_nsmul_lin_aux a b c w

/-- **EJA 43** (`jaeqs`, main.tex:1083, Proposition), item 1, first
equation: `[L_a, L_{a²}] = 0`, the Jordan identity. -/
theorem jaeqs_1a (a : V) : ⁅jL a, jL (a * a)⁆ = 0 := by
  rw [Ring.lie_def]
  refine LinearMap.ext fun b => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, jL_apply, LinearMap.zero_apply]
  rw [pj_mul_comm (a * a) b, ← pj_jordan, pj_mul_comm (a * b), sub_self]

/-- **EJA 43**, item 1, third equation:
`[L_a, L_{b*c}] + [L_b, L_{c*a}] + [L_c, L_{a*b}] = 0`. -/
theorem jaeqs_1c (a b c : V) :
    ⁅jL a, jL (b * c)⁆ + ⁅jL b, jL (c * a)⁆ + ⁅jL c, jL (a * b)⁆ = 0 := by
  simp only [Ring.lie_def]
  refine LinearMap.ext fun w => ?_
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, jL_apply,
    LinearMap.zero_apply]
  exact pj_lin a b c w

/-- **EJA 43**, item 1, second equation: `[L_b, L_{a²}] = 2 [L_{a*b}, L_a]`
(the third equation with `c = a`). -/
theorem jaeqs_1b (a b : V) : ⁅jL b, jL (a * a)⁆ = (2 : ℝ) • ⁅jL (a * b), jL a⁆ := by
  have h := jaeqs_1c a b a
  simp only [Ring.lie_def] at h ⊢
  refine LinearMap.ext fun w => ?_
  have hw := congrArg (fun T : Module.End ℝ V => T w) h
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, jL_apply,
    LinearMap.zero_apply, LinearMap.smul_apply] at hw ⊢
  rw [pj_mul_comm b a] at hw
  linear_combination (norm := module) hw

/-- **EJA 43**, item 2:
`L_{a*(b*c)} = L_a L_{b*c} + L_b L_{c*a} + L_c L_{a*b} − L_b L_a L_c − L_c L_a L_b`.
The paper's argument: the right-hand side of item 1's third equation, applied
to `d`, is symmetric in `a ↔ d`. -/
theorem jaeqs_2 (a b c : V) :
    jL (a * (b * c)) = jL a * jL (b * c) + jL b * jL (c * a) + jL c * jL (a * b)
      - jL b * jL a * jL c - jL c * jL a * jL b := by
  refine LinearMap.ext fun d => ?_
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, jL_apply]
  have h1 := pj_lin a b c d
  have h2 := pj_lin d b c a
  simp only [pj_mul_comm] at h1 h2 ⊢
  linear_combination (norm := module) h2 - h1

/-- The operators `L_{aⁿ}` lie in the (commutative) subalgebra of operators
generated by `L_a` and `L_{a²}` — the paper's "repeatedly applying the
equation for `L_{a*(b*c)}`". -/
theorem jL_jpow_mem_adjoin (a : V) (n : ℕ) :
    jL (jpow a n) ∈ Algebra.adjoin ℝ ({jL a, jL (a * a)} : Set (Module.End ℝ V)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [jpow_zero, jL_one]; exact Subalgebra.one_mem _
    | 1, _ => rw [jpow_one]; exact Algebra.subset_adjoin (by simp)
    | 2, _ => rw [jpow_two]; exact Algebra.subset_adjoin (by simp)
    | (m + 3), ih =>
      have e : jpow a (m + 3) = a * (a * jpow a (m + 1)) := rfl
      rw [e, jaeqs_2]
      have h1 : jL (a * jpow a (m + 1)) ∈ Algebra.adjoin ℝ
          ({jL a, jL (a * a)} : Set (Module.End ℝ V)) := ih (m + 2) (by omega)
      have h1' : jL (jpow a (m + 1) * a) ∈ Algebra.adjoin ℝ
          ({jL a, jL (a * a)} : Set (Module.End ℝ V)) := by rw [pj_mul_comm (jpow a (m + 1)) a]; exact h1
      have h0 : jL a ∈ Algebra.adjoin ℝ ({jL a, jL (a * a)} : Set (Module.End ℝ V)) :=
        Algebra.subset_adjoin (by simp)
      have hsq : jL (a * a) ∈ Algebra.adjoin ℝ ({jL a, jL (a * a)} : Set (Module.End ℝ V)) :=
        Algebra.subset_adjoin (by simp)
      have hc := ih (m + 1) (by omega)
      refine Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.add_mem _
        (Subalgebra.add_mem _ (Subalgebra.mul_mem _ h0 h1) (Subalgebra.mul_mem _ h0 h1'))
        (Subalgebra.mul_mem _ hc hsq)) ?_) ?_
      · exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ h0 h0) hc
      · exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hc h0) h0

/-- The operators `L_{aⁿ}`, `L_{aᵐ}` commute. -/
theorem jL_jpow_commute (a : V) (n m : ℕ) : Commute (jL (jpow a n)) (jL (jpow a m)) := by
  have hgen : ∀ x ∈ ({jL a, jL (a * a)} : Set (Module.End ℝ V)),
      ∀ y ∈ ({jL a, jL (a * a)} : Set (Module.End ℝ V)), Commute x y := by
    have hc : Commute (jL a) (jL (a * a)) := by
      have h := jaeqs_1a a
      rw [Ring.lie_def, sub_eq_zero] at h
      exact h
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hc
    · exact hc.symm
    · exact Commute.refl _
  have hleft : ∀ x ∈ ({jL a, jL (a * a)} : Set (Module.End ℝ V)),
      Commute x (jL (jpow a m)) := fun x hx =>
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute (jL_jpow_mem_adjoin a m)
      (fun y hy => hgen x hx y hy)
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (jL_jpow_mem_adjoin a n)
    (fun x hx => (hleft x hx).symm)).symm

/-- **EJA 43**, item 3, first equation: `aⁿ * (b * aᵐ) = (aⁿ * b) * aᵐ`. -/
theorem jaeqs_3a (a b : V) (n m : ℕ) : jpow a n * (b * jpow a m) = (jpow a n * b) * jpow a m := by
  have h := congrArg (fun T : Module.End ℝ V => T b) (jL_jpow_commute a n m).eq
  simp only [Module.End.mul_apply, jL_apply] at h
  rw [pj_mul_comm b, h, pj_mul_comm (jpow a n * b)]

/-- **EJA 43**, item 3, second equation (power-associativity):
`aⁿ * aᵐ = aⁿ⁺ᵐ`, by induction on `m` as in the paper. -/
theorem jaeqs_3b (a : V) (n m : ℕ) : jpow a n * jpow a m = jpow a (n + m) := by
  induction m generalizing n with
  | zero => rw [jpow_zero, pj_mul_one, Nat.add_zero]
  | succ m ih =>
    rw [jpow_succ, jaeqs_3a a a n m, pj_mul_comm (jpow a n) a, ← jpow_succ, ih (n + 1)]
    congr 1
    omega

end Jordan

/-! ## The bounded product, and closed associative subalgebras -/

section Assoc

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Mul E] [One E] [PaperEJA E]

variable (E) in
/-- A constant `r > 0` with `‖a * b‖ ≤ r ‖a‖ ‖b‖` (EJA 41). -/
noncomputable def mulConst : ℝ := Classical.choose (prod_bounded (E := E))

theorem mulConst_pos : 0 < mulConst E := (Classical.choose_spec (prod_bounded (E := E))).1

theorem norm_mul_le' (a b : E) : ‖a * b‖ ≤ mulConst E * ‖a‖ * ‖b‖ :=
  (Classical.choose_spec (prod_bounded (E := E))).2 a b

variable (E) in
/-- The Jordan product as a bounded bilinear map. -/
noncomputable def mulCLM : E →L[ℝ] E →L[ℝ] E :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun a b : E => a * b) (fun a a' b => pj_add_mul a a' b)
      (fun r a b => pj_smul_mul r a b) (fun a b b' => pj_mul_add a b b')
      (fun r a b => pj_mul_smul r a b))
    (mulConst E) (fun a b => norm_mul_le' a b)

@[simp] theorem mulCLM_apply (a b : E) : mulCLM E a b = a * b := rfl

theorem continuous_mul₂ : Continuous (fun p : E × E => p.1 * p.2) :=
  (mulCLM E).continuous₂

theorem continuous_mul_left' (a : E) : Continuous (fun b : E => a * b) :=
  (mulCLM E a).continuous

theorem continuous_mul_right' (b : E) : Continuous (fun a : E => a * b) :=
  ((mulCLM E).flip b).continuous

/-- A **closed associative subalgebra**: a closed subspace containing `1`,
closed under the product, on which the product is associative. -/
structure IsAssocSub (S : Submodule ℝ E) : Prop where
  closed : IsClosed (S : Set E)
  one_mem : (1 : E) ∈ S
  mul_mem : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S
  assoc : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, (x * y) * z = x * (y * z)

/-- A finite set of pairwise orthogonal non-zero idempotents. -/
structure IsIdemFamily (T : Finset E) : Prop where
  idem : ∀ p ∈ T, p * p = p
  ne_zero : ∀ p ∈ T, p ≠ 0
  orth : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → p * q = 0

theorem idem_inner_one {p : E} (hp : p * p = p) : ⟪p, 1⟫_ℝ = ⟪p, p⟫_ℝ := by
  have h := PaperEJA.inner_mul p p (1 : E)
  rw [hp, pj_mul_one] at h
  exact h

theorem idem_inner_orth {p q : E} (hp : p * p = p) (h : p * q = 0) : ⟪p, q⟫_ℝ = 0 := by
  have h1 := PaperEJA.inner_mul p p q
  rw [hp, h, inner_zero_right] at h1
  exact h1

/-- A non-zero idempotent has Hilbert norm at least `1 / r`. -/
theorem idem_norm_ge {p : E} (hp : p * p = p) (h0 : p ≠ 0) : 1 ≤ mulConst E * ‖p‖ := by
  have hn : 0 < ‖p‖ := norm_pos_iff.mpr h0
  have h := norm_mul_le' p p
  rw [hp] at h
  have h2 : ‖p‖ * 1 ≤ ‖p‖ * (mulConst E * ‖p‖) := by nlinarith
  exact le_of_mul_le_mul_left h2 hn

theorem IsIdemFamily.inner_sum {T : Finset E} (hT : IsIdemFamily T) {q : E} (hq : q ∈ T)
    (c : E → ℝ) : ⟪∑ p ∈ T, c p • p, q⟫_ℝ = c q * ⟪q, q⟫_ℝ := by
  rw [sum_inner, Finset.sum_eq_single q]
  · rw [real_inner_smul_left]
  · intro p hp hpq
    rw [real_inner_smul_left, idem_inner_orth (hT.idem p hp) (hT.orth p hp q hq hpq), mul_zero]
  · intro h; exact absurd hq h

theorem IsIdemFamily.inner_sum_right {T : Finset E} (hT : IsIdemFamily T) {q : E} (hq : q ∈ T)
    (c : E → ℝ) : ⟪q, ∑ p ∈ T, c p • p⟫_ℝ = c q * ⟪q, q⟫_ℝ := by
  rw [real_inner_comm, hT.inner_sum hq]

theorem IsIdemFamily.mul_sum {T : Finset E} (hT : IsIdemFamily T) (c d : E → ℝ) :
    (∑ p ∈ T, c p • p) * (∑ p ∈ T, d p • p) = ∑ p ∈ T, (c p * d p) • p := by
  rw [pj_sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [pj_smul_mul, pj_mul_sum, Finset.sum_eq_single p]
  · rw [pj_mul_smul, hT.idem p hp, smul_smul]
  · intro q hq hqp
    rw [pj_mul_smul, hT.orth p hp q hq (Ne.symm hqp), smul_zero]
  · intro h; exact absurd hp h

theorem IsIdemFamily.mul_sum_single {T : Finset E} (hT : IsIdemFamily T) {q : E} (hq : q ∈ T)
    (c : E → ℝ) : q * (∑ p ∈ T, c p • p) = c q • q := by
  rw [pj_mul_sum, Finset.sum_eq_single q]
  · rw [pj_mul_smul, hT.idem q hq]
  · intro p hp hpq
    rw [pj_mul_smul, hT.orth q hq p hp (Ne.symm hpq), smul_zero]
  · intro h; exact absurd hq h

theorem IsIdemFamily.sum_idem {T : Finset E} (hT : IsIdemFamily T) :
    (∑ p ∈ T, p) * (∑ p ∈ T, p) = ∑ p ∈ T, p := by
  have h := hT.mul_sum (fun _ => 1) (fun _ => 1)
  simpa using h

/-- **Counting orthogonal idempotents**: a family of pairwise orthogonal
non-zero idempotents has at most `r² ‖1‖²` members.  (`⟨1, p⟩ = ‖p‖²`, the
`p` are orthogonal vectors with `‖Σ p‖ ≤ ‖1‖`, and `‖p‖ ≥ 1/r`.) -/
theorem IsIdemFamily.card_le {T : Finset E} (hT : IsIdemFamily T) :
    (T.card : ℝ) ≤ mulConst E ^ 2 * ‖(1 : E)‖ ^ 2 := by
  set s := ∑ p ∈ T, p with hs
  have hss : ⟪s, s⟫_ℝ = ∑ p ∈ T, ⟪p, p⟫_ℝ := by
    rw [hs, sum_inner]
    refine Finset.sum_congr rfl fun q hq => ?_
    have := hT.inner_sum_right hq (fun _ => 1)
    simpa using this
  have h1s : ⟪s, (1 : E)⟫_ℝ = ∑ p ∈ T, ⟪p, p⟫_ℝ := by
    rw [hs, sum_inner]
    exact Finset.sum_congr rfl fun p hp => idem_inner_one (hT.idem p hp)
  have hle : ⟪s, s⟫_ℝ ≤ ‖(1 : E)‖ ^ 2 := by
    have h2 : ⟪s, s⟫_ℝ ≤ ‖s‖ * ‖(1 : E)‖ := by
      rw [hss, ← h1s]; exact real_inner_le_norm _ _
    rw [real_inner_self_eq_norm_sq] at h2 ⊢
    have h0 := norm_nonneg s
    have h1 := norm_nonneg (1 : E)
    nlinarith
  have hp : ∀ p ∈ T, 1 ≤ mulConst E ^ 2 * ⟪p, p⟫_ℝ := by
    intro p hp
    have h := idem_norm_ge (hT.idem p hp) (hT.ne_zero p hp)
    rw [real_inner_self_eq_norm_sq]
    nlinarith
  have hsum : (T.card : ℝ) ≤ mulConst E ^ 2 * ∑ p ∈ T, ⟪p, p⟫_ℝ := by
    rw [Finset.mul_sum]
    have := Finset.sum_le_sum hp
    simpa using this
  rw [hss] at hle
  have hC : 0 ≤ mulConst E ^ 2 := by positivity
  calc (T.card : ℝ) ≤ mulConst E ^ 2 * ∑ p ∈ T, ⟪p, p⟫_ℝ := hsum
    _ ≤ mulConst E ^ 2 * ‖(1 : E)‖ ^ 2 := mul_le_mul_of_nonneg_left hle hC

theorem IsIdemFamily.insert [DecidableEq E] {T : Finset E} (hT : IsIdemFamily T) {f : E} (hf : f * f = f)
    (hf0 : f ≠ 0) (horth : ∀ q ∈ T, f * q = 0) : IsIdemFamily (insert f T) where
  idem p hp := by
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hf
    · exact hT.idem p hp
  ne_zero p hp := by
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hf0
    · exact hT.ne_zero p hp
  orth p hp q hq hpq := by
    rcases Finset.mem_insert.mp hp with hpf | hpT <;>
      rcases Finset.mem_insert.mp hq with hqf | hqT
    · exact absurd (hpf.trans hqf.symm) hpq
    · rw [hpf]; exact horth q hqT
    · rw [hqf, pj_mul_comm]; exact horth p hpT
    · exact hT.orth p hpT q hqT hpq

omit [InnerProductSpace ℝ E] [CompleteSpace E] [One E] [PaperEJA E] in
theorem IsIdemFamily.not_mem_of_orth {T : Finset E} {f : E} (hf : f * f = f)
    (hf0 : f ≠ 0) (horth : ∀ q ∈ T, f * q = 0) : f ∉ T := by
  intro h
  exact hf0 (by rw [← hf]; exact horth f h)

/-- In a closed associative subalgebra, `1` is a sum of pairwise orthogonal
non-zero idempotents each of which is **minimal** in the subalgebra: a family
of maximal size (it exists, by `IsIdemFamily.card_le`) cannot be refined. -/
theorem exists_minimal_family {S : Submodule ℝ E} (hS : IsAssocSub S) :
    ∃ T : Finset E, IsIdemFamily T ∧ (∀ p ∈ T, p ∈ S) ∧ ∑ p ∈ T, p = 1 ∧
      ∀ p ∈ T, ∀ f ∈ S, f * f = f → f * p = f → f = 0 ∨ f = p := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ T : Finset E, IsIdemFamily T ∧ (∀ p ∈ T, p ∈ S) ∧ ∑ p ∈ T, p = 1 ∧ T.card = k
  let B : ℕ := ⌊mulConst E ^ 2 * ‖(1 : E)‖ ^ 2⌋₊
  have hB : ∀ k, P k → k ≤ B := by
    rintro k ⟨T, hT, -, -, rfl⟩
    exact Nat.le_floor hT.card_le
  have hex : ∃ k, P k := by
    by_cases h1 : (1 : E) = 0
    · refine ⟨0, ∅, ⟨by simp, by simp, by simp⟩, by simp, by simp [h1], rfl⟩
    · refine ⟨1, {1}, ⟨?_, ?_, ?_⟩, ?_, by simp, rfl⟩
      · intro p hp; rw [Finset.mem_singleton.mp hp, pj_mul_one]
      · intro p hp; rw [Finset.mem_singleton.mp hp]; exact h1
      · intro p hp q hq hpq
        rw [Finset.mem_singleton.mp hp, Finset.mem_singleton.mp hq] at hpq
        exact absurd rfl hpq
      · intro p hp; rw [Finset.mem_singleton.mp hp]; exact hS.one_mem
  obtain ⟨k₀, hk₀⟩ := hex
  have hspec : P (Nat.findGreatest P B) := Nat.findGreatest_spec (hB k₀ hk₀) hk₀
  obtain ⟨T, hT, hTS, hsum, hcard⟩ := hspec
  refine ⟨T, hT, hTS, hsum, ?_⟩
  intro p hp f hfS hff hfp
  by_contra hcon
  push Not at hcon
  obtain ⟨hf0, hfp'⟩ := hcon
  have hpS := hTS p hp
  have hpf : p * f = f := by rw [pj_mul_comm]; exact hfp
  -- the new family
  have hfq : ∀ q ∈ T.erase p, f * q = 0 := by
    intro q hq
    obtain ⟨hqp, hq⟩ := Finset.mem_erase.mp hq
    rw [← hfp, hS.assoc f hfS p hpS q (hTS q hq), hT.orth p hp q hq (Ne.symm hqp), pj_mul_zero]
  have hg : (p - f) * (p - f) = p - f := by
    rw [pj_sub_mul, pj_mul_sub, pj_mul_sub, hT.idem p hp, hpf, hfp, hff]; abel
  have hg0 : p - f ≠ 0 := sub_ne_zero.mpr (Ne.symm hfp')
  have hgq : ∀ q ∈ T.erase p, (p - f) * q = 0 := by
    intro q hq
    obtain ⟨hqp, hq'⟩ := Finset.mem_erase.mp hq
    rw [pj_sub_mul, hT.orth p hp q hq' (Ne.symm hqp), hfq q hq, sub_zero]
  have hU : IsIdemFamily (T.erase p) :=
    ⟨fun q hq => hT.idem q (Finset.mem_of_mem_erase hq),
      fun q hq => hT.ne_zero q (Finset.mem_of_mem_erase hq),
      fun q hq q' hq' => hT.orth q (Finset.mem_of_mem_erase hq) q' (Finset.mem_of_mem_erase hq')⟩
  have hU2 := hU.insert hg hg0 hgq
  have hfg : ∀ q ∈ insert (p - f) (T.erase p), f * q = 0 := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · rw [pj_mul_sub, hff, hfp, sub_self]
    · exact hfq q hq
  have hU3 := hU2.insert hff hf0 hfg
  have hnf := IsIdemFamily.not_mem_of_orth hff hf0 hfg
  have hng := IsIdemFamily.not_mem_of_orth hg hg0 hgq
  have hP : P (Nat.findGreatest P B + 1) := by
    refine ⟨insert f (insert (p - f) (T.erase p)), hU3, ?_, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hfS
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact S.sub_mem hpS hfS
      · exact hTS q (Finset.mem_of_mem_erase hq)
    · rw [Finset.sum_insert hnf, Finset.sum_insert hng, ← add_assoc, add_sub_cancel,
        Finset.add_sum_erase T (fun q => q) hp, hsum]
    · rw [Finset.card_insert_of_notMem hnf, Finset.card_insert_of_notMem hng,
        Finset.card_erase_of_mem hp, hcard]
      have : 1 ≤ T.card := Finset.card_pos.mpr ⟨p, hp⟩
      omega
  have h1 := Nat.le_findGreatest (hB _ hP) hP
  omega

/-- The corner `{x ∈ S | e * x = x}` of a closed associative subalgebra. -/
def cornerSub (S : Submodule ℝ E) (e : E) : Submodule ℝ E :=
  S ⊓ LinearMap.ker (jL e - LinearMap.id)

theorem mem_cornerSub {S : Submodule ℝ E} {e x : E} : x ∈ cornerSub S e ↔ x ∈ S ∧ e * x = x := by
  simp [cornerSub, sub_eq_zero]

theorem cornerSub_closed {S : Submodule ℝ E} (hS : IsAssocSub S) (e : E) :
    IsClosed (cornerSub S e : Set E) := by
  have h2 : IsClosed {x : E | e * x = x} :=
    isClosed_eq (continuous_mul_left' e) continuous_id
  have : (cornerSub S e : Set E) = (S : Set E) ∩ {x : E | e * x = x} := by
    ext x; simp [mem_cornerSub]
  rw [this]
  exact hS.closed.inter h2

/-- Multiplication by an element of `S`, restricted to `S`, as a bounded
operator of norm at most `r ‖c‖`. -/
noncomputable def mulS {S : Submodule ℝ E} (hS : IsAssocSub S) (c : E) (hc : c ∈ S) :
    S →L[ℝ] S :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨c * x, hS.mul_mem c hc x x.2⟩
      map_add' := fun x y => Subtype.ext (pj_mul_add c x y)
      map_smul' := fun r x => Subtype.ext (pj_mul_smul r c x) }
    (mulConst E * ‖c‖) (fun x => by
      show ‖c * (x : E)‖ ≤ mulConst E * ‖c‖ * ‖(x : E)‖
      exact norm_mul_le' c x)

theorem mulS_norm_le {S : Submodule ℝ E} (hS : IsAssocSub S) (c : E) (hc : c ∈ S) :
    ‖mulS hS c hc‖ ≤ mulConst E * ‖c‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg mulConst_pos.le (norm_nonneg c)) _

/-- **The corner of a minimal idempotent is a field** (inverse relative to
`e`): if `e` is minimal among the idempotents of the closed associative
subalgebra `S`, every non-zero `x ∈ S` with `e * x = x` has some `y ∈ S`
with `x * y = e`. -/
theorem corner_inv {S : Submodule ℝ E} (hS : IsAssocSub S) {e : E} (he : e ∈ S)
    (hee : e * e = e) (hmin : ∀ f ∈ S, f * f = f → f * e = f → f = 0 ∨ f = e)
    {x : E} (hxS : x ∈ S) (hex : e * x = x) (hx0 : x ≠ 0) : ∃ y ∈ S, x * y = e := by
  classical
  set C := mulConst E with hCdef
  have hC : 0 < C := mulConst_pos
  let I : Submodule ℝ E := S.map (jL x)
  let J : Submodule ℝ E := I.topologicalClosure
  have hK : IsClosed (cornerSub S e : Set E) := cornerSub_closed hS e
  have hIK : I ≤ cornerSub S e := by
    rintro _ ⟨b, hb, rfl⟩
    refine mem_cornerSub.mpr ⟨hS.mul_mem x hxS b hb, ?_⟩
    show e * (x * b) = x * b
    rw [← hS.assoc e he x hxS b hb, hex]
  have hJK : J ≤ cornerSub S e := I.topologicalClosure_minimal hIK hK
  have hxI : ∀ b ∈ S, x * b ∈ J := fun b hb => I.le_topologicalClosure ⟨b, hb, rfl⟩
  by_cases heJ : e ∈ J
  · -- `e` is a limit of elements `x * b`: invert by a Neumann series in `S`
    have hδ : 0 < 1 / C := by positivity
    have hcl : e ∈ closure (I : Set E) := heJ
    obtain ⟨u, hu, hdu⟩ := Metric.mem_closure_iff.mp hcl (1 / C) hδ
    obtain ⟨b, hb, rfl⟩ := hu
    set c := e - x * b with hc
    have hcS : c ∈ S := S.sub_mem he (hS.mul_mem x hxS b hb)
    have hcn : ‖mulS hS c hcS‖ < 1 := by
      have h1 := mulS_norm_le hS c hcS
      have h2 : ‖c‖ < 1 / C := by rw [hc, ← dist_eq_norm]; exact hdu
      calc ‖mulS hS c hcS‖ ≤ C * ‖c‖ := h1
        _ < C * (1 / C) := mul_lt_mul_of_pos_left h2 hC
        _ = 1 := by field_simp
    have : CompleteSpace S := hS.closed.completeSpace_coe
    obtain ⟨g, hg⟩ := (isUnit_one_sub_of_norm_lt_one hcn).exists_right_inv
    set z : S := g ⟨e, he⟩ with hz
    have hz1 : (z : E) - c * z = e := by
      have := congrArg (fun T : S →L[ℝ] S => ((T ⟨e, he⟩ : S) : E)) hg
      simpa [mulS, hz] using this
    have hzS : (z : E) ∈ S := z.2
    have hmul : e * ((z : E) - c * z) = e := by rw [hz1, hee]
    have hec : e * c = c := by
      rw [hc, pj_mul_sub, hee, ← hS.assoc e he x hxS b hb, hex]
    rw [pj_mul_sub, ← hS.assoc e he c hcS z hzS, hec, hc, pj_sub_mul] at hmul
    have hxb : (x * b) * z = e := by rw [← hmul]; abel
    exact ⟨b * z, hS.mul_mem b hb z hzS, by rw [← hS.assoc x hxS b hb z hzS, hxb]⟩
  · -- otherwise the orthogonal complement of the ideal inside the corner
    -- carries a smaller idempotent
    exfalso
    have : CompleteSpace J := (I.isClosed_topologicalClosure).completeSpace_coe
    let W : Submodule ℝ E := cornerSub S e ⊓ Jᗮ
    have hWc : IsClosed (W : Set E) := hK.inter (Submodule.isClosed_orthogonal J)
    have : CompleteSpace W := hWc.completeSpace_coe
    have hWK : ∀ {y}, y ∈ W → y ∈ S ∧ e * y = y :=
      fun hy => mem_cornerSub.mp (Submodule.mem_inf.mp hy).1
    have hWJ : ∀ {y}, y ∈ W → ∀ v ∈ J, ⟪v, y⟫_ℝ = 0 :=
      fun hy v hv => (Submodule.mem_orthogonal J _).mp (Submodule.mem_inf.mp hy).2 v hv
    -- `W` is an ideal of `S`
    have hideal : ∀ {y}, y ∈ W → ∀ c ∈ S, y * c ∈ W := by
      intro y hy c hc
      obtain ⟨hyS, hey⟩ := hWK hy
      refine Submodule.mem_inf.mpr ⟨mem_cornerSub.mpr ⟨hS.mul_mem y hyS c hc, ?_⟩, ?_⟩
      · rw [← hS.assoc e he y hyS c hc, hey]
      · have hsub : J ≤ (Submodule.span ℝ {y * c})ᗮ := by
          refine I.topologicalClosure_minimal ?_ (Submodule.isClosed_orthogonal _)
          rintro _ ⟨b', hb', rfl⟩
          rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
          show ⟪y * c, x * b'⟫_ℝ = 0
          rw [pj_mul_comm y c, PaperEJA.inner_mul, real_inner_comm]
          have hm : c * (x * b') = x * (b' * c) := by
            rw [pj_mul_comm c, hS.assoc x hxS b' hb' c hc]
          rw [hm]
          exact hWJ hy _ (hxI _ (hS.mul_mem b' hb' c hc))
        rw [Submodule.mem_orthogonal]
        intro v hv
        have := hsub hv
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
        rw [real_inner_comm]; exact this
    -- a non-zero element of `W`
    set w' := e - J.starProjection e with hw'
    have hw'W : w' ∈ W := by
      refine Submodule.mem_inf.mpr ⟨?_, J.sub_starProjection_mem_orthogonal e⟩
      exact (cornerSub S e).sub_mem (mem_cornerSub.mpr ⟨he, hee⟩)
        (hJK (J.starProjection_apply_mem e))
    have hw'0 : w' ≠ 0 := by
      intro h
      apply heJ
      have : e = J.starProjection e := sub_eq_zero.mp h
      rw [this]; exact J.starProjection_apply_mem e
    -- the projection of `e` onto `W` is a unit for `W`
    set f := W.starProjection e with hf
    have hfW : f ∈ W := W.starProjection_apply_mem e
    have hfu : ∀ u ∈ W, ⟪f, u⟫_ℝ = ⟪e, u⟫_ℝ := by
      intro u hu
      have := W.starProjection_inner_eq_zero e u hu
      rw [inner_sub_left, sub_eq_zero] at this
      exact this.symm
    have hunit : ∀ u ∈ W, f * u = u := by
      intro u hu
      have hfuW : f * u ∈ W := by
        rw [pj_mul_comm]; exact hideal hu f (hWK hfW).1
      have hin : ∀ v ∈ W, ⟪f * u - u, v⟫_ℝ = 0 := by
        intro v hv
        have huv : u * v ∈ W := hideal hu v (hWK hv).1
        have h1 : ⟪f * u, v⟫_ℝ = ⟪u, v⟫_ℝ := by
          rw [pj_mul_comm f u, PaperEJA.inner_mul, hfu _ huv, ← PaperEJA.inner_mul,
            pj_mul_comm u e, (hWK hu).2]
        rw [inner_sub_left, h1, sub_self]
      have hd : f * u - u ∈ W := W.sub_mem hfuW hu
      have := hin _ hd
      rw [real_inner_self_eq_norm_sq] at this
      have h0 : ‖f * u - u‖ = 0 := by nlinarith [norm_nonneg (f * u - u)]
      exact sub_eq_zero.mp (norm_eq_zero.mp h0)
    have hff : f * f = f := hunit f hfW
    have hfe : f * e = f := by rw [pj_mul_comm]; exact (hWK hfW).2
    rcases hmin f (hWK hfW).1 hff hfe with h | h
    · apply hw'0
      rw [← hunit w' hw'W, h, pj_zero_mul]
    · have heW : e ∈ W := h ▸ hfW
      have hxx : x * x ∈ J := hxI x hxS
      have h1 := hWJ heW _ hxx
      have h2 : ⟪x * x, e⟫_ℝ = ⟪x, x⟫_ℝ := by
        rw [PaperEJA.inner_mul, pj_mul_comm x e, hex]
      rw [h2] at h1
      exact hx0 (inner_self_eq_zero.mp h1)

/-- **A minimal idempotent has a one-dimensional corner**: `e * a ∈ ℝ e`
for every `a ∈ S`.  The supremum `M` of the Rayleigh quotient of `L_{e a}` on
the corner is an approximate eigenvalue, so `e a − M e`, if non-zero, would
be invertible in the corner (`corner_inv`) and bounded below — a
contradiction. -/
theorem corner_scalar {S : Submodule ℝ E} (hS : IsAssocSub S) {e : E} (he : e ∈ S)
    (hee : e * e = e) (he0 : e ≠ 0) (hmin : ∀ f ∈ S, f * f = f → f * e = f → f = 0 ∨ f = e)
    {a : E} (haS : a ∈ S) : ∃ t : ℝ, e * a = t • e := by
  classical
  set C := mulConst E with hCdef
  have hC : 0 < C := mulConst_pos
  set a' := e * a with ha'
  have ha'S : a' ∈ S := hS.mul_mem e he a haS
  have ha'K : e * a' = a' := by rw [ha', ← hS.assoc e he e he a haS, hee]
  have hKmul : ∀ {x}, x ∈ S → e * x = x → e * (a' * x) = a' * x := by
    intro x hx hex
    rw [← hS.assoc e he a' ha'S x hx, ha'K]
  let R : Set ℝ := {t | ∃ x ∈ S, e * x = x ∧ ‖x‖ = 1 ∧ t = ⟪a' * x, x⟫_ℝ}
  have hR0 : R.Nonempty := by
    have hn : 0 < ‖e‖ := norm_pos_iff.mpr he0
    refine ⟨_, ‖e‖⁻¹ • e, S.smul_mem _ he, ?_, ?_, rfl⟩
    · rw [pj_mul_smul, hee]
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hRb : BddAbove R := by
    refine ⟨C * ‖a'‖, ?_⟩
    rintro t ⟨x, -, -, hx1, rfl⟩
    calc ⟪a' * x, x⟫_ℝ ≤ ‖a' * x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ C * ‖a'‖ * ‖x‖ * ‖x‖ := by gcongr; exact norm_mul_le' a' x
      _ = C * ‖a'‖ := by rw [hx1]; ring
  set M := sSup R with hM
  have hRay : ∀ x ∈ S, e * x = x → ⟪a' * x, x⟫_ℝ ≤ M * ‖x‖ ^ 2 := by
    intro x hx hex
    rcases eq_or_ne x 0 with rfl | hx0
    · simp [pj_mul_zero]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hmem : ⟪a' * (‖x‖⁻¹ • x), ‖x‖⁻¹ • x⟫_ℝ ∈ R := by
      refine ⟨‖x‖⁻¹ • x, S.smul_mem _ hx, ?_, ?_, rfl⟩
      · rw [pj_mul_smul, hex]
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h1 := le_csSup hRb hmem
    rw [pj_mul_smul, real_inner_smul_left, real_inner_smul_right] at h1
    have h2 : ‖x‖⁻¹ * (‖x‖⁻¹ * ⟪a' * x, x⟫_ℝ) = ⟪a' * x, x⟫_ℝ / ‖x‖ ^ 2 := by
      field_simp
    rw [h2, div_le_iff₀ (by positivity)] at h1
    exact h1
  by_contra hcon
  push Not at hcon
  set x0 := a' - M • e with hx0def
  have hx0 : x0 ≠ 0 := by
    intro h; apply hcon M; exact sub_eq_zero.mp h
  have hx0S : x0 ∈ S := S.sub_mem ha'S (S.smul_mem M he)
  have hx0K : e * x0 = x0 := by rw [hx0def, pj_mul_sub, pj_mul_smul, hee, ha'K]
  obtain ⟨y, hyS, hxy⟩ := corner_inv hS he hee hmin hx0S hx0K hx0
  -- the operator `s x = M x − a' x` on the corner
  set D := |M| + C * ‖a'‖ + 1 with hD
  have hDpos : 0 < D := by positivity
  have hs_bound : ∀ w : E, ‖M • w - a' * w‖ ≤ D * ‖w‖ := by
    intro w
    calc ‖M • w - a' * w‖ ≤ ‖M • w‖ + ‖a' * w‖ := norm_sub_le _ _
      _ ≤ |M| * ‖w‖ + C * ‖a'‖ * ‖w‖ := by
          rw [norm_smul, Real.norm_eq_abs]; gcongr; exact norm_mul_le' a' w
      _ ≤ D * ‖w‖ := by rw [hD]; nlinarith [norm_nonneg w]
  have hsym : ∀ v w : E, ⟪M • v - a' * v, w⟫_ℝ = ⟪v, M • w - a' * w⟫_ℝ := by
    intro v w
    rw [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      PaperEJA.inner_mul]
  have hq : ∀ x ∈ S, e * x = x → 0 ≤ ⟪M • x - a' * x, x⟫_ℝ := by
    intro x hx hex
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [hRay x hx hex]
  have hkey : ∀ x ∈ S, e * x = x →
      ‖M • x - a' * x‖ ^ 2 ≤ D * ⟪M • x - a' * x, x⟫_ℝ := by
    intro x hx hex
    set w := M • x - a' * x with hw
    have hwS : w ∈ S := S.sub_mem (S.smul_mem M hx) (hS.mul_mem a' ha'S x hx)
    have hwK : e * w = w := by
      rw [hw, pj_mul_sub, pj_mul_smul, hex, hKmul hx hex]
    set t := 1 / D with ht
    have hv := hq (x - t • w) (S.sub_mem hx (S.smul_mem t hwS))
      (by rw [pj_mul_sub, pj_mul_smul, hex, hwK])
    have hexp : ⟪M • (x - t • w) - a' * (x - t • w), x - t • w⟫_ℝ
        = ⟪w, x⟫_ℝ - 2 * t * ‖w‖ ^ 2 + t ^ 2 * ⟪M • w - a' * w, w⟫_ℝ := by
      have hl : M • (x - t • w) - a' * (x - t • w) = w - t • (M • w - a' * w) := by
        have hw' : M • x - a' * x = w := hw.symm
        rw [smul_sub, pj_mul_sub, pj_mul_smul]
        linear_combination (norm := module) hw'
      rw [hl, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      have hs2 : ⟪M • w - a' * w, x⟫_ℝ = ‖w‖ ^ 2 := by
        rw [hsym, ← hw, real_inner_self_eq_norm_sq]
      rw [hs2]; ring
    rw [hexp] at hv
    have hsw : ⟪M • w - a' * w, w⟫_ℝ ≤ D * ‖w‖ ^ 2 := by
      calc ⟪M • w - a' * w, w⟫_ℝ ≤ ‖M • w - a' * w‖ * ‖w‖ := real_inner_le_norm _ _
        _ ≤ D * ‖w‖ * ‖w‖ := by gcongr; exact hs_bound w
        _ = D * ‖w‖ ^ 2 := by ring
    have ht2 : t ^ 2 * ⟪M • w - a' * w, w⟫_ℝ ≤ t ^ 2 * (D * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsw (sq_nonneg t)
    have htD : t * D = 1 := by rw [ht]; field_simp
    have h3 : 0 ≤ ⟪w, x⟫_ℝ - 2 * t * ‖w‖ ^ 2 + t ^ 2 * (D * ‖w‖ ^ 2) := by linarith
    have h4 : t ^ 2 * (D * ‖w‖ ^ 2) = t * ‖w‖ ^ 2 := by
      rw [show t ^ 2 * (D * ‖w‖ ^ 2) = (t * D) * (t * ‖w‖ ^ 2) by ring, htD, one_mul]
    rw [h4] at h3
    have h5 : t * ‖w‖ ^ 2 ≤ ⟪w, x⟫_ℝ := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 hDpos.le
    rw [← mul_assoc, mul_comm D t, htD, one_mul] at h6
    exact h6
  -- the corner is bounded below by `x0`
  have hbelow : ∀ x ∈ S, e * x = x → ‖x‖ ≤ C * ‖y‖ * ‖M • x - a' * x‖ := by
    intro x hx hex
    have hx' : x = y * (x0 * x) := by
      rw [← hS.assoc y hyS x0 hx0S x hx, pj_mul_comm y x0, hxy, hex]
    have hneg : x0 * x = -(M • x - a' * x) := by
      rw [hx0def, pj_sub_mul, pj_smul_mul, pj_mul_comm e x, pj_mul_comm x e, hex]; abel
    calc ‖x‖ = ‖y * (x0 * x)‖ := by rw [← hx']
      _ ≤ C * ‖y‖ * ‖x0 * x‖ := norm_mul_le' _ _
      _ = C * ‖y‖ * ‖M • x - a' * x‖ := by rw [hneg, norm_neg]
  set A := C ^ 2 * ‖y‖ ^ 2 * D with hA
  have hApos : 0 ≤ A := by positivity
  set ε := 1 / (A + 1) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨t, ⟨x, hx, hex, hx1, rfl⟩, htx⟩ := exists_lt_of_lt_csSup hR0 (sub_lt_self M hεpos)
  have hqx : ⟪M • x - a' * x, x⟫_ℝ < ε := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hx1]
    linarith
  have h1 := hbelow x hx hex
  rw [hx1] at h1
  have h2 := hkey x hx hex
  have h3 : 1 ≤ C ^ 2 * ‖y‖ ^ 2 * ‖M • x - a' * x‖ ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one h1 2
    rw [one_pow] at this
    calc (1 : ℝ) ≤ (C * ‖y‖ * ‖M • x - a' * x‖) ^ 2 := this
      _ = C ^ 2 * ‖y‖ ^ 2 * ‖M • x - a' * x‖ ^ 2 := by ring
  have h4 : 1 ≤ A * ⟪M • x - a' * x, x⟫_ℝ := by
    calc (1 : ℝ) ≤ C ^ 2 * ‖y‖ ^ 2 * ‖M • x - a' * x‖ ^ 2 := h3
      _ ≤ C ^ 2 * ‖y‖ ^ 2 * (D * ⟪M • x - a' * x, x⟫_ℝ) := by gcongr
      _ = A * ⟪M • x - a' * x, x⟫_ℝ := by rw [hA]; ring
  have h5 : A * ⟪M • x - a' * x, x⟫_ℝ ≤ A * ε := mul_le_mul_of_nonneg_left hqx.le hApos
  have h6 : A * ε < 1 := by
    rw [hε, mul_one_div, div_lt_one (by positivity)]; linarith
  linarith

/-- `assocSub_decomp`, with the minimality of the idempotents: each `p` has a
one-dimensional corner, `p * a ∈ ℝ p` for `a ∈ S`. -/
theorem assocSub_decomp_min {S : Submodule ℝ E} (hS : IsAssocSub S) :
    ∃ T : Finset E, IsIdemFamily T ∧ (∀ p ∈ T, p ∈ S) ∧ ∑ p ∈ T, p = 1 ∧
      (∀ p ∈ T, ∀ a ∈ S, ∃ t : ℝ, p * a = t • p) ∧
      ∀ a ∈ S, ∃ c : E → ℝ, a = ∑ p ∈ T, c p • p := by
  classical
  obtain ⟨T, hT, hTS, hsum, hmin⟩ := exists_minimal_family hS
  have hsc : ∀ p ∈ T, ∀ a ∈ S, ∃ t : ℝ, p * a = t • p := fun p hp a ha =>
    corner_scalar hS (hTS p hp) (hT.idem p hp) (hT.ne_zero p hp) (hmin p hp) ha
  refine ⟨T, hT, hTS, hsum, hsc, fun a ha => ?_⟩
  have hc : ∀ p ∈ T, ∃ t : ℝ, p * a = t • p := fun p hp => hsc p hp a ha
  choose! c hc using hc
  refine ⟨c, ?_⟩
  calc a = 1 * a := (pj_one_mul a).symm
    _ = ∑ p ∈ T, p * a := by rw [← hsum, pj_sum_mul]
    _ = ∑ p ∈ T, c p • p := Finset.sum_congr rfl fun p hp => hc p hp

/-- **Spectral decomposition in a closed associative subalgebra**: there is a
finite family of pairwise orthogonal non-zero idempotents of `S` summing to
`1` such that every element of `S` is a linear combination of them.  (This
replaces the print's appeal to Kadison's representation theorem in EJA 45.) -/
theorem assocSub_decomp {S : Submodule ℝ E} (hS : IsAssocSub S) :
    ∃ T : Finset E, IsIdemFamily T ∧ (∀ p ∈ T, p ∈ S) ∧ ∑ p ∈ T, p = 1 ∧
      ∀ a ∈ S, ∃ c : E → ℝ, a = ∑ p ∈ T, c p • p := by
  obtain ⟨T, hT, hTS, hsum, -, hdec⟩ := assocSub_decomp_min hS
  exact ⟨T, hT, hTS, hsum, hdec⟩

/-! ## EJA 44–46: the algebra generated by an element, and the spectral theorem -/

/-- The span of the powers of `a` (the Jordan subalgebra generated by `a`). -/
def polySpan (a : E) : Submodule ℝ E := Submodule.span ℝ (Set.range (jpow a))

/-- `C(a)`, the closure of the algebra generated by `a` (EJA 44). -/
def Calg (a : E) : Submodule ℝ E := (polySpan a).topologicalClosure

theorem jpow_mem_polySpan (a : E) (n : ℕ) : jpow a n ∈ polySpan a :=
  Submodule.subset_span ⟨n, rfl⟩

theorem polySpan_mul_mem (a : E) {x y : E} (hx : x ∈ polySpan a) (hy : y ∈ polySpan a) :
    x * y ∈ polySpan a := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      rw [jaeqs_3b]; exact jpow_mem_polySpan a _
    | zero => rw [pj_mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [pj_mul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [pj_mul_smul]; exact Submodule.smul_mem _ r hy
  | zero => rw [pj_zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [pj_add_mul]; exact add_mem hx hz
  | smul r x _ hx => rw [pj_smul_mul]; exact Submodule.smul_mem _ r hx

theorem polySpan_assoc₁ (a : E) (i j : ℕ) {z : E} (hz : z ∈ polySpan a) :
    (jpow a i * jpow a j) * z = jpow a i * (jpow a j * z) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, rfl⟩ := hz
    rw [jaeqs_3b, jaeqs_3b, jaeqs_3b, jaeqs_3b, add_assoc]
  | zero => simp only [pj_mul_zero]
  | add y z _ _ hy hz => rw [pj_mul_add, pj_mul_add, pj_mul_add, hy, hz]
  | smul r y _ hy => rw [pj_mul_smul, pj_mul_smul, pj_mul_smul, hy]

theorem polySpan_assoc₂ (a : E) (i : ℕ) {y z : E} (hy : y ∈ polySpan a)
    (hz : z ∈ polySpan a) : (jpow a i * y) * z = jpow a i * (y * z) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact polySpan_assoc₁ a i j hz
  | zero => simp only [pj_mul_zero, pj_zero_mul]
  | add y y' _ _ hy hy' => rw [pj_mul_add, pj_add_mul, pj_add_mul, pj_mul_add, hy, hy']
  | smul r y _ hy => rw [pj_mul_smul, pj_smul_mul, pj_smul_mul, pj_mul_smul, hy]

theorem polySpan_assoc (a : E) {x y z : E} (hx : x ∈ polySpan a) (hy : y ∈ polySpan a)
    (hz : z ∈ polySpan a) : (x * y) * z = x * (y * z) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact polySpan_assoc₂ a i hy hz
  | zero => simp only [pj_zero_mul]
  | add x x' _ _ hx hx' => rw [pj_add_mul, pj_add_mul, pj_add_mul, hx, hx']
  | smul r x _ hx => rw [pj_smul_mul, pj_smul_mul, pj_smul_mul, hx]

/-- **EJA 44** (`cor:assocalg`, main.tex:1174, Corollary): the closure `C(a)`
of the algebra generated by `a` is a commutative associative (closed)
subalgebra containing `a`.  The paper's proof: the generated algebra is the
polynomials in `a`, associative by power-associativity (EJA 43.3), and the
product is continuous (EJA 41). -/
theorem cor_assocalg (a : E) : IsAssocSub (Calg a) ∧ a ∈ Calg a := by
  have hsub : ∀ {x}, x ∈ polySpan a → x ∈ Calg a := fun hx => (polySpan a).le_topologicalClosure hx
  have hcl : ∀ {x}, x ∈ Calg a → x ∈ closure (polySpan a : Set E) := fun hx => hx
  refine ⟨⟨(polySpan a).isClosed_topologicalClosure, hsub (jpow_mem_polySpan a 0), ?_, ?_⟩, ?_⟩
  · intro x hx y hy
    exact map_mem_closure₂ (f := fun x y : E => x * y) continuous_mul₂ (hcl hx) (hcl hy)
      (fun x hx y hy => polySpan_mul_mem a hx hy)
  · intro x hx y hy z hz
    -- extend associativity from the span to its closure, one variable at a time
    have h1 : ∀ x ∈ polySpan a, ∀ y ∈ polySpan a, ∀ z ∈ closure (polySpan a : Set E),
        (x * y) * z = x * (y * z) := by
      intro x hx y hy z hz
      have hc : IsClosed {z : E | (x * y) * z = x * (y * z)} :=
        isClosed_eq (continuous_mul_left' _) ((continuous_mul_left' x).comp
          (continuous_mul_left' y))
      exact closure_minimal (fun z hz => polySpan_assoc a hx hy hz) hc hz
    have h2 : ∀ x ∈ polySpan a, ∀ y ∈ closure (polySpan a : Set E),
        ∀ z ∈ closure (polySpan a : Set E), (x * y) * z = x * (y * z) := by
      intro x hx y hy z hz
      have hc : IsClosed {y : E | (x * y) * z = x * (y * z)} :=
        isClosed_eq ((continuous_mul_right' z).comp (continuous_mul_left' x))
          ((continuous_mul_left' x).comp (continuous_mul_right' z))
      exact closure_minimal (fun y hy => h1 x hx y hy z hz) hc hy
    have hc : IsClosed {x : E | (x * y) * z = x * (y * z)} :=
      isClosed_eq ((continuous_mul_right' z).comp (continuous_mul_right' y))
        (continuous_mul_right' _)
    exact closure_minimal (fun x hx => h2 x hx y (hcl hy) z (hcl hz)) hc (hcl hx)
  · have := hsub (jpow_mem_polySpan a 1)
    rwa [jpow_one] at this

/-- The coefficients of a combination of a family of orthogonal idempotents
are recovered by the inner product. -/
theorem IsIdemFamily.coeff {T : Finset E} (hT : IsIdemFamily T) {q : E} (hq : q ∈ T)
    (c : E → ℝ) : ⟪∑ p ∈ T, c p • p, q⟫_ℝ / ⟪q, q⟫_ℝ = c q := by
  rw [hT.inner_sum hq, mul_div_assoc, div_self, mul_one]
  exact (real_inner_self_pos.mpr (hT.ne_zero q hq)).ne'

theorem IsIdemFamily.inner_self_pos {T : Finset E} (hT : IsIdemFamily T) {q : E}
    (hq : q ∈ T) : 0 < ⟪q, q⟫_ℝ := real_inner_self_pos.mpr (hT.ne_zero q hq)

theorem IsIdemFamily.sum_eq_sum_iff {T : Finset E} (hT : IsIdemFamily T) (c d : E → ℝ) :
    ∑ p ∈ T, c p • p = ∑ p ∈ T, d p • p ↔ ∀ p ∈ T, c p = d p := by
  constructor
  · intro h p hp
    rw [← hT.coeff hp c, ← hT.coeff hp d, h]
  · intro h
    exact Finset.sum_congr rfl fun p hp => by rw [h p hp]

/-- **EJA 45** (`prop:associsdisc`, main.tex:1189, Proposition): an
associative EJA is isomorphic as an algebra to `ℝⁿ` with the pointwise
product, for some `n`.

The print derives this from Kadison's representation theorem (the algebra is
`C(X)`, and the Riesz vectors of the point evaluations make `X` discrete, so
finite); here, without Kadison, from `assocSub_decomp`: `E` is spanned by
finitely many pairwise orthogonal idempotents, and the coordinates
`a ↦ ⟨a, p⟩ / ⟨p, p⟩` are an algebra isomorphism onto `ℝⁿ`. -/
theorem associsdisc (hassoc : ∀ x y z : E, (x * y) * z = x * (y * z)) :
    ∃ n : ℕ, ∃ Φ : E ≃ₗ[ℝ] (Fin n → ℝ), (∀ a b, Φ (a * b) = Φ a * Φ b) ∧ Φ 1 = 1 := by
  classical
  have hS : IsAssocSub (⊤ : Submodule ℝ E) :=
    ⟨by simp, trivial, fun _ _ _ _ => trivial, fun x _ y _ z _ => hassoc x y z⟩
  obtain ⟨T, hT, -, hsum, hdec⟩ := assocSub_decomp hS
  set n := T.card
  let σ : Fin n ≃ {x // x ∈ T} := T.equivFin.symm
  let κ : E → E →ₗ[ℝ] ℝ := fun p => (⟪p, p⟫_ℝ)⁻¹ • innerₗ E p
  have hκ : ∀ p a, κ p a = ⟪a, p⟫_ℝ / ⟪p, p⟫_ℝ := by
    intro p a
    show (⟪p, p⟫_ℝ)⁻¹ • ⟪p, a⟫_ℝ = _
    rw [smul_eq_mul, real_inner_comm a p, div_eq_inv_mul]
  have hrep : ∀ a : E, a = ∑ p ∈ T, κ p a • p := by
    intro a
    obtain ⟨c, hc⟩ := hdec a trivial
    conv_lhs => rw [hc]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hκ, hc, hT.coeff hp]
  let Φl : E →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi fun i => κ (σ i)
  let Ψl : (Fin n → ℝ) →ₗ[ℝ] E :=
    { toFun := fun v => ∑ i, v i • ((σ i : T) : E)
      map_add' := fun v w => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r v => by simp [Finset.smul_sum, smul_smul] }
  have hsumσ : ∀ g : E → E, ∑ i, g ((σ i : T) : E) = ∑ p ∈ T, g p := by
    intro g
    rw [Equiv.sum_comp σ (fun x : T => g x), Finset.sum_coe_sort T g]
  have hΨ : ∀ v : Fin n → ℝ, Ψl v = ∑ p ∈ T, (fun p => if h : p ∈ T then v (σ.symm ⟨p, h⟩)
      else 0) p • p := by
    intro v
    show ∑ i, v i • ((σ i : T) : E) = _
    rw [← hsumσ (fun p => (if h : p ∈ T then v (σ.symm ⟨p, h⟩) else 0) • p)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  refine ⟨n, LinearEquiv.ofLinearMap (f := Φl) (g := Ψl) ?_ ?_, ?_, ?_⟩
  · refine LinearMap.ext fun v => funext fun i => ?_
    show κ (σ i) (Ψl v) = v i
    rw [hκ, hΨ, hT.coeff (σ i).2]
    simp
  · refine LinearMap.ext fun a => ?_
    show Ψl (Φl a) = a
    show ∑ i, κ (σ i) a • ((σ i : T) : E) = a
    rw [hsumσ (fun p => κ p a • p)]
    exact (hrep a).symm
  · intro a b
    funext i
    show κ (σ i) (a * b) = κ (σ i) a * κ (σ i) b
    have hab : a * b = ∑ p ∈ T, (κ p a * κ p b) • p := by
      conv_lhs => rw [hrep a, hrep b]
      exact hT.mul_sum _ _
    rw [hab, hκ, hT.coeff (σ i).2]
  · funext i
    show κ (σ i) 1 = 1
    rw [hκ, real_inner_comm, idem_inner_one (hT.idem _ (σ i).2)]
    exact div_self (hT.inner_self_pos (σ i).2).ne'

/-- The spectral theorem in the form used below: `a` is a combination of a
family of pairwise orthogonal non-zero idempotents of `C(a)` summing to `1`. -/
theorem spectral_family (a : E) :
    ∃ T : Finset E, IsIdemFamily T ∧ ∑ p ∈ T, p = 1 ∧ (∀ p ∈ T, p ∈ Calg a) ∧
      ∃ c : E → ℝ, a = ∑ p ∈ T, c p • p := by
  obtain ⟨hS, ha⟩ := cor_assocalg a
  obtain ⟨T, hT, hTS, hsum, hdec⟩ := assocSub_decomp hS
  exact ⟨T, hT, hsum, hTS, hdec a ha⟩

/-- **EJA 46** (`cor:spectral`, main.tex:1226, Corollary): every element of
an EJA is `a = Σᵢ λᵢ pᵢ` for real `λᵢ` and orthogonal idempotents `pᵢ`.
The paper's proof: `C(a)` is associative (EJA 44), hence `ℝⁿ` (EJA 45),
which is spanned by orthogonal idempotents.  (The `pᵢ` may moreover be taken
non-zero and summing to `1`: `spectral_family`.) -/
theorem cor_spectral (a : E) :
    ∃ n : ℕ, ∃ (lam : Fin n → ℝ) (p : Fin n → E), (∀ i, p i * p i = p i) ∧
      (∀ i j, i ≠ j → p i * p j = 0) ∧ a = ∑ i, lam i • p i := by
  classical
  obtain ⟨T, hT, -, -, c, hc⟩ := spectral_family a
  let σ : Fin T.card ≃ {x // x ∈ T} := T.equivFin.symm
  refine ⟨T.card, fun i => c (σ i), fun i => σ i, fun i => hT.idem _ (σ i).2,
    fun i j hij => hT.orth _ (σ i).2 _ (σ j).2 ?_, ?_⟩
  · intro h; exact hij (σ.injective (Subtype.ext h))
  · rw [hc, Equiv.sum_comp σ (fun x : T => c x • (x : E)), Finset.sum_coe_sort T (fun p => c p • p)]

end Assoc

/-! ## JB-algebras (for EJA 50) -/

section JB

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V]

/-- The defining properties of a **JB-algebra** (Hanche-Olsen–Størmer 3.1.4,
Alfsen–Shultz 1.5) for a function `N` on a Jordan algebra: `N` is a norm, the
space is complete for it, and `‖a * b‖ ≤ ‖a‖ ‖b‖`, `‖a²‖ = ‖a‖²`,
`‖a²‖ ≤ ‖a² + b²‖`.  JB-algebras are not in Mathlib; EJA 50 says the order
unit norm of an EJA has these properties. -/
structure IsJBNorm (N : V → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ N a
  eq_zero : ∀ a, N a = 0 → a = 0
  smul : ∀ (r : ℝ) (a : V), N (r • a) = |r| * N a
  triangle : ∀ a b, N (a + b) ≤ N a + N b
  complete : ∀ u : ℕ → V, (∀ ε > 0, ∃ K, ∀ m ≥ K, ∀ n ≥ K, N (u m - u n) < ε) →
    ∃ x, ∀ ε > 0, ∃ K, ∀ n ≥ K, N (u n - x) < ε
  mul_le : ∀ a b, N (a * b) ≤ N a * N b
  sq : ∀ a, N (a * a) = N a ^ 2
  sq_le : ∀ a b, N (a * a) ≤ N (a * a + b * b)

end JB

/-! ## EJA 47–53: order structure of an EJA -/

section Order

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Mul E] [One E] [PaperEJA E]

/-- **EJA 5** for the paper's EJAs, verbatim: `a` is *positive* when it is a
square. -/
def IsSq (a : E) : Prop := ∃ b : E, a = b * b

theorem isSq_mul_self (b : E) : IsSq (b * b) := ⟨b, rfl⟩

theorem idem_isSq {p : E} (hp : p * p = p) : IsSq p := ⟨p, hp.symm⟩

theorem isSq_one : IsSq (1 : E) := idem_isSq (pj_mul_one 1)

theorem isSq_smul {r : ℝ} (hr : 0 ≤ r) {a : E} (ha : IsSq a) : IsSq (r • a) := by
  obtain ⟨b, rfl⟩ := ha
  refine ⟨Real.sqrt r • b, ?_⟩
  rw [pj_smul_mul, pj_mul_smul, smul_smul, Real.mul_self_sqrt hr]

/-- The Peirce identity `2 L_p³ = 3 L_p² − L_p` of an idempotent, from EJA 43.2
with `a = b = c = p`. -/
theorem idem_peirce {p : E} (hp : p * p = p) (x : E) :
    (2 : ℝ) • (p * (p * (p * x))) = (3 : ℝ) • (p * (p * x)) - p * x := by
  have h := congrArg (fun T : Module.End ℝ E => T x) (jaeqs_2 p p p)
  simp only [hp, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, jL_apply] at h
  linear_combination (norm := module) h

/-- `L_p` is a positive operator for an idempotent `p`:
`⟨p x, x⟩ = ‖p x‖² + 4 ‖p x − p (p x)‖²` (from the Peirce identity). -/
theorem idem_inner_eq {p : E} (hp : p * p = p) (x : E) :
    ⟪p * x, x⟫_ℝ = ‖p * x‖ ^ 2 + 4 * ‖p * x - p * (p * x)‖ ^ 2 := by
  set u := p * x with hu
  set v := p * u with hv
  set w := p * v with hw
  set z := p * w with hz
  have h1 := idem_peirce hp x
  have h2 := idem_peirce hp u
  rw [← hu, ← hv, ← hw] at h1
  rw [← hv, ← hw, ← hz] at h2
  have hvec : u = v + (4 : ℝ) • (v - (2 : ℝ) • w + z) := by
    linear_combination (norm := module) h1 - (2 : ℝ) • h2
  have e1 : ⟪v, x⟫_ℝ = ⟪u, u⟫_ℝ := PaperEJA.inner_mul p u x
  have e2 : ⟪w, x⟫_ℝ = ⟪v, u⟫_ℝ := PaperEJA.inner_mul p v x
  have e3 : ⟪z, x⟫_ℝ = ⟪v, v⟫_ℝ := (PaperEJA.inner_mul p w x).trans (PaperEJA.inner_mul p v u)
  calc ⟪u, x⟫_ℝ = ⟪v + (4 : ℝ) • (v - (2 : ℝ) • w + z), x⟫_ℝ := by rw [← hvec]
    _ = ⟪v, x⟫_ℝ + 4 * (⟪v, x⟫_ℝ - 2 * ⟪w, x⟫_ℝ + ⟪z, x⟫_ℝ) := by
        simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
    _ = ‖u‖ ^ 2 + 4 * ‖u - v‖ ^ 2 := by
        rw [e1, e2, e3, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
          inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm u v]
        ring

theorem idem_inner_nonneg {p : E} (hp : p * p = p) (x : E) : 0 ≤ ⟪p * x, x⟫_ℝ := by
  rw [idem_inner_eq hp]; positivity

theorem idem_mul_eq_zero_of_inner {p : E} (hp : p * p = p) {x : E} (h : ⟪p * x, x⟫_ℝ = 0) :
    p * x = 0 := by
  rw [idem_inner_eq hp] at h
  have h1 : ‖p * x‖ ^ 2 = 0 := by
    have := sq_nonneg ‖p * x - p * (p * x)‖
    have := sq_nonneg ‖p * x‖
    linarith
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)

/-- `⟨c², p⟩ ≥ 0` for an idempotent `p` (the fact the print cites from Chu,
p. 107). -/
theorem inner_sq_idem_nonneg {p : E} (hp : p * p = p) (c : E) : 0 ≤ ⟪c * c, p⟫_ℝ := by
  rw [PaperEJA.inner_mul, pj_mul_comm c p, real_inner_comm]
  exact idem_inner_nonneg hp c

theorem IsIdemFamily.isSq_sum {T : Finset E} (hT : IsIdemFamily T) (c : E → ℝ)
    (hc : ∀ p ∈ T, 0 ≤ c p) : IsSq (∑ p ∈ T, c p • p) := by
  refine ⟨∑ p ∈ T, Real.sqrt (c p) • p, ?_⟩
  rw [hT.mul_sum]
  exact Finset.sum_congr rfl fun p hp => by rw [Real.mul_self_sqrt (hc p hp)]

/-- **EJA 47** (`prop:selfduality`, main.tex:1233, Proposition): `a` is
positive (a square) iff `⟨a, b⟩ ≥ 0` for all positive `b`.  The paper's
proof, with the cited `⟨p, a⟩ ≥ 0` (Chu) proved from the Peirce identity
(`inner_sq_idem_nonneg`). -/
theorem selfduality (a : E) : IsSq a ↔ ∀ b : E, IsSq b → 0 ≤ ⟪a, b⟫_ℝ := by
  constructor
  · rintro ⟨c, rfl⟩ b ⟨d, rfl⟩
    obtain ⟨T, hT, -, -, μ, hμ⟩ := spectral_family d
    rw [hμ, hT.mul_sum, inner_sum]
    exact Finset.sum_nonneg fun p hp => by
      rw [real_inner_smul_right]
      exact mul_nonneg (mul_self_nonneg _) (inner_sq_idem_nonneg (hT.idem p hp) c)
  · intro h
    obtain ⟨T, hT, -, -, c, hc⟩ := spectral_family a
    have hnn : ∀ q ∈ T, 0 ≤ c q := by
      intro q hq
      have h1 := h q (idem_isSq (hT.idem q hq))
      rw [hc, hT.inner_sum hq] at h1
      by_contra hn
      push Not at hn
      nlinarith [hT.inner_self_pos hq]
    rw [hc]; exact hT.isSq_sum c hnn

theorem IsIdemFamily.coeff_nonneg {T : Finset E} (hT : IsIdemFamily T) (c : E → ℝ)
    (h : IsSq (∑ p ∈ T, c p • p)) : ∀ q ∈ T, 0 ≤ c q := by
  intro q hq
  have h1 := (selfduality _).mp h q (idem_isSq (hT.idem q hq))
  rw [hT.inner_sum hq] at h1
  by_contra hn
  push Not at hn
  nlinarith [hT.inner_self_pos hq]

theorem IsIdemFamily.isSq_iff {T : Finset E} (hT : IsIdemFamily T) (c : E → ℝ) :
    IsSq (∑ p ∈ T, c p • p) ↔ ∀ p ∈ T, 0 ≤ c p :=
  ⟨hT.coeff_nonneg c, hT.isSq_sum c⟩

theorem family_smul_one_sub {T : Finset E} (hsum : ∑ p ∈ T, p = 1) (t : ℝ)
    (c : E → ℝ) : t • (1 : E) - ∑ p ∈ T, c p • p = ∑ p ∈ T, (t - c p) • p := by
  rw [← hsum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by rw [sub_smul]

theorem family_add_smul_one {T : Finset E} (hsum : ∑ p ∈ T, p = 1) (t : ℝ)
    (c : E → ℝ) : ∑ p ∈ T, c p • p + t • (1 : E) = ∑ p ∈ T, (c p + t) • p := by
  rw [← hsum, Finset.smul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by rw [add_smul]

/-- **EJA 48** (`cor:ejaous`, main.tex:1239, Corollary), first sentence: the
positive elements are closed under addition (from self-duality, as in the
paper). -/
theorem ejaous_add {a b : E} (ha : IsSq a) (hb : IsSq b) : IsSq (a + b) :=
  (selfduality _).mpr fun c hc => by
    rw [inner_add_left]
    exact add_nonneg ((selfduality a).mp ha c hc) ((selfduality b).mp hb c hc)

/-- The cone of sums of squares (the order `PaperEJA.order` of `Prelim`) is the
cone of squares. -/
theorem isSumSq_iff_isSq (a : E) : IsSumSq a ↔ IsSq a := by
  constructor
  · intro h
    induction h with
    | zero => exact ⟨0, (pj_mul_zero 0).symm⟩
    | sq_add b _ ih => exact ejaous_add (isSq_mul_self b) ih
  · rintro ⟨b, rfl⟩
    exact IsSumSq.mul_self b

attribute [local instance] PaperEJA.order

theorem pe_le_iff (x y : E) : x ≤ y ↔ IsSq (y - x) := isSumSq_iff_isSq (y - x)

theorem pe_nonneg_iff (x : E) : 0 ≤ x ↔ IsSq x := by rw [pe_le_iff, sub_zero]

/-- **EJA 48**, second sentence: an EJA, ordered by its cone of squares, is an
order unit space with unit `1` (in the tree's sense) … -/
noncomputable def paperOUS : OrderUnitSpace E where
  add_le_add_left x y h z := by
    rw [pe_le_iff] at h ⊢
    rwa [add_sub_add_right_eq_sub]
  smul_nonneg hr hx := by
    rw [pe_nonneg_iff] at hx ⊢
    exact isSq_smul hr hx
  unit := 1
  exists_le_smul_unit x := by
    obtain ⟨T, hT, hsum, -, c, hc⟩ := spectral_family x
    refine ⟨⌈∑ p ∈ T, |c p|⌉₊, ?_⟩
    rw [pe_le_iff, hc, family_smul_one_sub hsum]
    refine hT.isSq_sum _ fun p hp => ?_
    have h1 : c p ≤ ∑ q ∈ T, |c q| :=
      (le_abs_self _).trans (Finset.single_le_sum (fun q _ => abs_nonneg (c q)) hp)
    have h2 := Nat.le_ceil (∑ q ∈ T, |c q|)
    linarith

/-- **EJA 48**, second sentence, continued: … which is **Archimedean**.  The
paper's argument (the algebra generated by `a` is `ℝⁿ`), through the spectral
family of `a`. -/
theorem ejaous_archimedean : @OUSArchimedean E _ _ _ paperOUS := by
  intro x hx
  obtain ⟨T, hT, hsum, -, c, hc⟩ := spectral_family x
  have hle : ∀ q ∈ T, c q ≤ 0 := by
    intro q hq
    by_contra hpos
    push Not at hpos
    have h1 := hx (c q / 2) (by linarith)
    change x ≤ (c q / 2) • (1 : E) at h1
    rw [pe_le_iff, hc, family_smul_one_sub hsum, hT.isSq_iff] at h1
    have := h1 q hq
    linarith
  rw [pe_le_iff, zero_sub, hc, ← Finset.sum_neg_distrib]
  have he : ∑ p ∈ T, -(c p • p) = ∑ p ∈ T, (-c p) • p :=
    Finset.sum_congr rfl fun p _ => by rw [neg_smul]
  rw [he, hT.isSq_iff]
  intro p hp
  linarith [hle p hp]

/-! ### EJA 49: the order unit norm -/

/-- The **order unit norm** (EJA 7.2): `‖a‖ = inf {r ≥ 0 | −r·1 ≤ a ≤ r·1}`.
(The print takes the infimum over all real `r`; for a non-zero EJA the two
agree, and `r ≥ 0` keeps the definition sensible in the zero algebra.) -/
noncomputable def ouNorm (a : E) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ IsSq (t • (1 : E) - a) ∧ IsSq (a + t • (1 : E))}

theorem ouNorm_le {a : E} {t : ℝ} (ht : 0 ≤ t) (h1 : IsSq (t • (1 : E) - a))
    (h2 : IsSq (a + t • (1 : E))) : ouNorm a ≤ t :=
  csInf_le ⟨0, fun _ hs => hs.1⟩ ⟨ht, h1, h2⟩

/-- The largest absolute coefficient. -/
def coefMax (T : Finset E) (c : E → ℝ) : NNReal := T.sup fun p => ⟨|c p|, abs_nonneg _⟩

/-- For a combination of a family of orthogonal idempotents summing to `1`, the
order unit norm is the largest absolute coefficient. -/
theorem ouNorm_family {T : Finset E} (hT : IsIdemFamily T) (hsum : ∑ p ∈ T, p = 1)
    (c : E → ℝ) : IsLeast {t : ℝ | 0 ≤ t ∧ IsSq (t • (1 : E) - ∑ p ∈ T, c p • p) ∧
      IsSq (∑ p ∈ T, c p • p + t • (1 : E))}
      (coefMax T c : ℝ) := by
  have hmem : ∀ t : ℝ, (IsSq (t • (1 : E) - ∑ p ∈ T, c p • p) ∧
      IsSq (∑ p ∈ T, c p • p + t • (1 : E))) ↔ ∀ p ∈ T, |c p| ≤ t := by
    intro t
    rw [family_smul_one_sub hsum, family_add_smul_one hsum, hT.isSq_iff, hT.isSq_iff]
    constructor
    · rintro ⟨h1, h2⟩ p hp
      rw [abs_le]; constructor <;> linarith [h1 p hp, h2 p hp]
    · intro h
      exact ⟨fun p hp => by linarith [(abs_le.mp (h p hp)).2],
        fun p hp => by linarith [(abs_le.mp (h p hp)).1]⟩
  refine ⟨⟨NNReal.coe_nonneg _, (hmem _).mpr fun p hp => ?_⟩, ?_⟩
  · have := Finset.le_sup (f := fun p => (⟨|c p|, abs_nonneg _⟩ : NNReal)) hp
    have h2 : (⟨|c p|, abs_nonneg _⟩ : NNReal) ≤ coefMax T c := this
    exact_mod_cast h2
  · rintro t ⟨ht, h⟩
    have h' := (hmem t).mp h
    have : coefMax T c ≤ ⟨t, ht⟩ :=
      Finset.sup_le fun p hp => by exact_mod_cast h' p hp
    exact_mod_cast this

theorem ouNorm_family_eq {T : Finset E} (hT : IsIdemFamily T) (hsum : ∑ p ∈ T, p = 1)
    (c : E → ℝ) : ouNorm (∑ p ∈ T, c p • p) =
      (coefMax T c : ℝ) :=
  (ouNorm_family hT hsum c).csInf_eq

/-- `−‖a‖·1 ≤ a ≤ ‖a‖·1` (EJA 7.2's "`a ≤ ‖a‖ 1`"): the infimum is attained. -/
theorem ouNorm_spec (a : E) :
    0 ≤ ouNorm a ∧ IsSq (ouNorm a • (1 : E) - a) ∧ IsSq (a + ouNorm a • (1 : E)) := by
  obtain ⟨T, hT, hsum, -, c, hc⟩ := spectral_family a
  rw [hc, ouNorm_family_eq hT hsum c]
  exact (ouNorm_family hT hsum c).1

theorem ouNorm_nonneg (a : E) : 0 ≤ ouNorm a := (ouNorm_spec a).1

theorem abs_coeff_le_ouNorm {T : Finset E} (hT : IsIdemFamily T) (hsum : ∑ p ∈ T, p = 1)
    (c : E → ℝ) {q : E} (hq : q ∈ T) : |c q| ≤ ouNorm (∑ p ∈ T, c p • p) := by
  obtain ⟨-, h1, h2⟩ := ouNorm_spec (∑ p ∈ T, c p • p)
  rw [family_smul_one_sub hsum, hT.isSq_iff] at h1
  rw [family_add_smul_one hsum, hT.isSq_iff] at h2
  rw [abs_le]; constructor <;> linarith [h1 q hq, h2 q hq]

theorem ouNorm_le_of_coeff {T : Finset E} (hT : IsIdemFamily T) (hsum : ∑ p ∈ T, p = 1)
    (c : E → ℝ) {t : ℝ} (ht : 0 ≤ t) (h : ∀ p ∈ T, |c p| ≤ t) :
    ouNorm (∑ p ∈ T, c p • p) ≤ t := by
  refine ouNorm_le ht ?_ ?_
  · rw [family_smul_one_sub hsum, hT.isSq_iff]
    exact fun p hp => by linarith [(abs_le.mp (h p hp)).2]
  · rw [family_add_smul_one hsum, hT.isSq_iff]
    exact fun p hp => by linarith [(abs_le.mp (h p hp)).1]

theorem IsIdemFamily.inner_sum_sum {T : Finset E} (hT : IsIdemFamily T) (c : E → ℝ) :
    ⟪∑ p ∈ T, c p • p, ∑ p ∈ T, c p • p⟫_ℝ = ∑ p ∈ T, c p ^ 2 * ⟪p, p⟫_ℝ := by
  rw [_root_.inner_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [real_inner_smul_right, hT.inner_sum hq]; ring

/-- **EJA 49** (`prop:equivalenttopology`, main.tex:1246, Proposition): the
Hilbert norm and the order unit norm are equivalent,
`c ‖a‖₂ ≤ ‖a‖ ≤ d ‖a‖₂`.  First inequality as in the paper
(`‖a‖₂² ≤ ‖a‖² ‖1‖₂²`); for the second the paper shows by contradiction that
non-zero idempotents have Hilbert norm bounded below, which here is direct
from EJA 41 (`‖p‖₂ ≥ 1/r`, `idem_norm_ge`). -/
theorem equivalenttopology : ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
    ∀ a : E, c * ‖a‖ ≤ ouNorm a ∧ ouNorm a ≤ d * ‖a‖ := by
  refine ⟨1 / (‖(1 : E)‖ + 1), mulConst E, by positivity, mulConst_pos, fun a => ?_⟩
  obtain ⟨T, hT, hsum, -, c, hc⟩ := spectral_family a
  set m := ouNorm a with hm
  have hm0 : 0 ≤ m := ouNorm_nonneg a
  have hcoef : ∀ q ∈ T, |c q| ≤ m := fun q hq => by
    rw [hm, hc]; exact abs_coeff_le_ouNorm hT hsum c hq
  have hnorm : ‖a‖ ^ 2 = ∑ p ∈ T, c p ^ 2 * ⟪p, p⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, hc, hT.inner_sum_sum]
  have hone : ‖(1 : E)‖ ^ 2 = ∑ p ∈ T, ⟪p, p⟫_ℝ := by
    have := hT.inner_sum_sum (fun _ => 1)
    simp only [one_smul, one_pow, one_mul] at this
    rw [← real_inner_self_eq_norm_sq, ← hsum, this]
  constructor
  · have h1 : ‖a‖ ^ 2 ≤ (m * ‖(1 : E)‖) ^ 2 := by
      rw [hnorm, mul_pow, hone, Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      have hpp := (hT.inner_self_pos hp).le
      have : c p ^ 2 ≤ m ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hcoef p hp) 2
      exact mul_le_mul_of_nonneg_right this hpp
    have h2 : ‖a‖ ≤ m * ‖(1 : E)‖ :=
      abs_le_of_sq_le_sq h1 (mul_nonneg hm0 (norm_nonneg _)) |>.trans' (le_abs_self _)
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (1 : E)]
  · conv_lhs => rw [hm, hc]
    refine ouNorm_le_of_coeff hT hsum c (mul_nonneg mulConst_pos.le (norm_nonneg _))
      fun q hq => ?_
    have h1 : c q ^ 2 * ⟪q, q⟫_ℝ ≤ ‖a‖ ^ 2 := by
      rw [hnorm]
      exact Finset.single_le_sum (f := fun p => c p ^ 2 * ⟪p, p⟫_ℝ)
        (fun p hp => mul_nonneg (sq_nonneg _) (hT.inner_self_pos hp).le) hq
    have h2 : 1 ≤ mulConst E ^ 2 * ⟪q, q⟫_ℝ := by
      have := idem_norm_ge (hT.idem q hq) (hT.ne_zero q hq)
      rw [real_inner_self_eq_norm_sq]; nlinarith
    have h3 : c q ^ 2 ≤ (mulConst E * ‖a‖) ^ 2 := by
      have hC := mulConst_pos (E := E)
      have h4 : c q ^ 2 ≤ c q ^ 2 * (mulConst E ^ 2 * ⟪q, q⟫_ℝ) :=
        le_mul_of_one_le_right (sq_nonneg _) h2
      calc c q ^ 2 ≤ c q ^ 2 * (mulConst E ^ 2 * ⟪q, q⟫_ℝ) := h4
        _ = mulConst E ^ 2 * (c q ^ 2 * ⟪q, q⟫_ℝ) := by ring
        _ ≤ mulConst E ^ 2 * ‖a‖ ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (mulConst E * ‖a‖) ^ 2 := by ring
    exact abs_le_of_sq_le_sq h3 (mul_nonneg mulConst_pos.le (norm_nonneg a))

/-! ### EJA 50: an EJA is a JB-algebra -/

theorem ouNorm_smul_le (r : ℝ) (a : E) : ouNorm (r • a) ≤ |r| * ouNorm a := by
  obtain ⟨T, hT, hsum, -, c, hc⟩ := spectral_family a
  have hra : r • a = ∑ p ∈ T, (r * c p) • p := by
    rw [hc, Finset.smul_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [smul_smul]
  rw [hra]
  refine ouNorm_le_of_coeff hT hsum _ (mul_nonneg (abs_nonneg r) (ouNorm_nonneg a))
    fun p hp => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by rw [hc]; exact abs_coeff_le_ouNorm hT hsum c hp)
    (abs_nonneg r)

theorem ouNorm_zero : ouNorm (0 : E) = 0 :=
  le_antisymm (by simpa using ouNorm_smul_le (0 : ℝ) (0 : E)) (ouNorm_nonneg 0)

theorem ouNorm_smul (r : ℝ) (a : E) : ouNorm (r • a) = |r| * ouNorm a := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [ouNorm_zero]
  refine le_antisymm (ouNorm_smul_le r a) ?_
  have h := ouNorm_smul_le r⁻¹ (r • a)
  rw [smul_smul, inv_mul_cancel₀ hr, one_smul, abs_inv] at h
  have hr' : 0 < |r| := abs_pos.mpr hr
  calc |r| * ouNorm a ≤ |r| * (|r|⁻¹ * ouNorm (r • a)) := mul_le_mul_of_nonneg_left h hr'.le
    _ = ouNorm (r • a) := by field_simp

theorem ouNorm_add_le (a b : E) : ouNorm (a + b) ≤ ouNorm a + ouNorm b := by
  obtain ⟨ha0, ha1, ha2⟩ := ouNorm_spec a
  obtain ⟨hb0, hb1, hb2⟩ := ouNorm_spec b
  refine ouNorm_le (add_nonneg ha0 hb0) ?_ ?_
  · have := ejaous_add ha1 hb1
    convert this using 1; rw [add_smul]; abel
  · have := ejaous_add ha2 hb2
    convert this using 1; rw [add_smul]; abel

theorem ouNorm_eq_zero {a : E} (h : ouNorm a = 0) : a = 0 := by
  obtain ⟨T, hT, hsum, -, c, hc⟩ := spectral_family a
  have hz : ∀ p ∈ T, c p = 0 := fun p hp => by
    have := abs_coeff_le_ouNorm hT hsum c hp
    rw [← hc, h] at this
    exact abs_nonpos_iff.mp this
  rw [hc]
  exact Finset.sum_eq_zero fun p hp => by rw [hz p hp, zero_smul]

theorem ouNorm_mul_self (a : E) : ouNorm (a * a) = ouNorm a ^ 2 := by
  obtain ⟨T, hT, hsum, -, c, hc⟩ := spectral_family a
  have haa : a * a = ∑ p ∈ T, (c p * c p) • p := by rw [hc, hT.mul_sum]
  have hN := ouNorm_nonneg a
  refine le_antisymm ?_ ?_
  · rw [haa]
    refine ouNorm_le_of_coeff hT hsum _ (by positivity) fun p hp => ?_
    have := abs_coeff_le_ouNorm hT hsum c hp
    rw [← hc] at this
    rw [abs_mul, sq]
    exact mul_le_mul this this (abs_nonneg _) hN
  · have hsq : ouNorm a ≤ Real.sqrt (ouNorm (a * a)) := by
      conv_lhs => rw [hc]
      refine ouNorm_le_of_coeff hT hsum c (Real.sqrt_nonneg _) fun p hp => ?_
      have h1 := abs_coeff_le_ouNorm hT hsum (fun p => c p * c p) hp
      rw [← haa] at h1
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by rw [sq]; exact (le_abs_self _).trans h1)
    have := pow_le_pow_left₀ hN hsq 2
    rwa [Real.sq_sqrt (ouNorm_nonneg _)] at this

/-- `a² ≤ ‖a‖² · 1`. -/
theorem isSq_normsq_sub (a : E) : IsSq (ouNorm a ^ 2 • (1 : E) - a * a) := by
  have := (ouNorm_spec (a * a)).2.1
  rwa [ouNorm_mul_self] at this

/-- The step of the paper's proof of EJA 50: `−1 ≤ a ≤ 1` implies
`0 ≤ a² ≤ 1` (the hypothesis of Alfsen–Shultz 1.11). -/
theorem jb_criterion {a : E} (h1 : IsSq ((1 : E) - a)) (h2 : IsSq (a + 1)) :
    IsSq (a * a) ∧ IsSq ((1 : E) - a * a) := by
  refine ⟨isSq_mul_self a, ?_⟩
  have hN : ouNorm a ≤ 1 := ouNorm_le zero_le_one (by rwa [one_smul]) (by rwa [one_smul])
  have hN2 : ouNorm a ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (ouNorm_nonneg a) hN 2; rwa [one_pow] at this
  have := ejaous_add (isSq_normsq_sub a) (isSq_smul (sub_nonneg.mpr hN2) (isSq_one (E := E)))
  convert this using 1
  rw [sub_smul, one_smul]; abel

theorem ouNorm_mul_le (a b : E) : ouNorm (a * b) ≤ ouNorm a * ouNorm b := by
  set s := ouNorm a
  set t := ouNorm b
  rcases eq_or_lt_of_le (ouNorm_nonneg a) with hs | hs
  · have ha0 : a = 0 := ouNorm_eq_zero hs.symm
    rw [ha0, pj_zero_mul, ouNorm_zero]
    exact mul_nonneg (ouNorm_nonneg _) (ouNorm_nonneg _)
  rcases eq_or_lt_of_le (ouNorm_nonneg b) with ht | ht
  · have hb0 : b = 0 := ouNorm_eq_zero ht.symm
    rw [hb0, pj_mul_zero, ouNorm_zero]
    exact mul_nonneg (ouNorm_nonneg _) (ouNorm_nonneg _)
  have hs' : s ≠ 0 := hs.ne'
  have ht' : t ≠ 0 := ht.ne'
  set a' := s⁻¹ • a with ha'
  set b' := t⁻¹ • b with hb'
  have hna : ouNorm a' = 1 := by
    rw [ha', ouNorm_smul, abs_inv, abs_of_pos hs, inv_mul_cancel₀ hs.ne']
  have hnb : ouNorm b' = 1 := by
    rw [hb', ouNorm_smul, abs_inv, abs_of_pos ht, inv_mul_cancel₀ ht.ne']
  have hle4 : ∀ x : E, ouNorm x ≤ 2 → IsSq ((4 : ℝ) • (1 : E) - x * x) := by
    intro x hx
    have h2 : ouNorm x ^ 2 ≤ 4 := by
      have := pow_le_pow_left₀ (ouNorm_nonneg x) hx 2; norm_num at this; linarith
    have := ejaous_add (isSq_normsq_sub x) (isSq_smul (sub_nonneg.mpr h2) (isSq_one (E := E)))
    convert this using 1
    rw [sub_smul]; abel
  have hp : ouNorm (a' + b') ≤ 2 := by
    have := ouNorm_add_le a' b'; rw [hna, hnb] at this; linarith
  have hm : ouNorm (a' - b') ≤ 2 := by
    have := ouNorm_add_le a' (-b')
    rw [hna, ← neg_one_smul ℝ b', ouNorm_smul, hnb] at this
    rw [sub_eq_add_neg, ← neg_one_smul ℝ b']; norm_num at this ⊢; linarith
  have hpol : (a' + b') * (a' + b') - (a' - b') * (a' - b') = (4 : ℝ) • (a' * b') := by
    simp only [pj_add_mul, pj_mul_add, pj_sub_mul, pj_mul_sub, pj_mul_comm b' a']
    rw [show (4 : ℝ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul, one_smul]
    abel
  have hup : IsSq ((1 : ℝ) • (1 : E) - a' * b') := by
    have h := ejaous_add (hle4 _ hp) (isSq_mul_self (a' - b'))
    have h2 := isSq_smul (by norm_num : (0 : ℝ) ≤ 1 / 4) h
    convert h2 using 1
    have : (4 : ℝ) • (1 : E) - (a' + b') * (a' + b') + (a' - b') * (a' - b')
        = (4 : ℝ) • ((1 : E) - a' * b') := by
      rw [smul_sub, ← hpol]; abel
    rw [this, smul_smul]; norm_num
  have hdown : IsSq (a' * b' + (1 : ℝ) • (1 : E)) := by
    have h := ejaous_add (hle4 _ hm) (isSq_mul_self (a' + b'))
    have h2 := isSq_smul (by norm_num : (0 : ℝ) ≤ 1 / 4) h
    convert h2 using 1
    have : (4 : ℝ) • (1 : E) - (a' - b') * (a' - b') + (a' + b') * (a' + b')
        = (4 : ℝ) • (a' * b' + (1 : E)) := by
      rw [smul_add, ← hpol]; abel
    rw [this, smul_smul, one_smul]; norm_num
  have h1 : ouNorm (a' * b') ≤ 1 := ouNorm_le zero_le_one hup hdown
  have hab : a * b = (s * t) • (a' * b') := by
    rw [ha', hb', pj_smul_mul, pj_mul_smul, smul_smul, smul_smul]
    conv_lhs => rw [← one_smul ℝ (a * b)]
    congr 1
    field_simp
  rw [hab, ouNorm_smul, abs_of_pos (mul_pos hs ht)]
  calc s * t * ouNorm (a' * b') ≤ s * t * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = s * t := mul_one _

theorem ouNorm_sq_le (a b : E) : ouNorm (a * a) ≤ ouNorm (a * a + b * b) := by
  obtain ⟨h0, h1, h2⟩ := ouNorm_spec (a * a + b * b)
  refine ouNorm_le h0 ?_ ?_
  · have := ejaous_add h1 (isSq_mul_self b)
    convert this using 1; abel
  · exact ejaous_add (isSq_mul_self a) (isSq_smul h0 isSq_one)

/-- **EJA 50** (`prop:EJAisJB`, main.tex:1259, Proposition): an EJA is a
JB-algebra — its order unit norm is a complete norm with
`‖a * b‖ ≤ ‖a‖ ‖b‖`, `‖a²‖ = ‖a‖²` and `‖a²‖ ≤ ‖a² + b²‖`.  The paper
checks the hypothesis of Alfsen–Shultz 1.11 (`jb_criterion`) and cites the
theorem; the JB axioms are verified here directly (completeness from EJA 49,
the product inequality by polarisation `4 a b = (a + b)² − (a − b)²`). -/
theorem EJAisJB : IsJBNorm (ouNorm (E := E)) where
  nonneg := ouNorm_nonneg
  eq_zero _ h := ouNorm_eq_zero h
  smul := ouNorm_smul
  triangle := ouNorm_add_le
  complete u hu := by
    obtain ⟨c, d, hc, hd, hcd⟩ := equivalenttopology (E := E)
    have hcau : CauchySeq u := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨K, hK⟩ := hu (c * ε) (by positivity)
      refine ⟨K, fun m hm n hn => ?_⟩
      rw [dist_eq_norm]
      have := (hcd (u m - u n)).1.trans_lt (hK m hm n hn)
      exact lt_of_mul_lt_mul_left this hc.le
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcau
    refine ⟨x, fun ε hε => ?_⟩
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hx (ε / d) (by positivity)
    refine ⟨K, fun n hn => ?_⟩
    have h1 := hK n hn
    rw [dist_eq_norm] at h1
    calc ouNorm (u n - x) ≤ d * ‖u n - x‖ := (hcd _).2
      _ < d * (ε / d) := mul_lt_mul_of_pos_left h1 hd
      _ = ε := by field_simp
  mul_le := ouNorm_mul_le
  sq := ouNorm_mul_self
  sq_le := ouNorm_sq_le

/-! ### EJA 51: bounded directed completeness and normality of states -/

/-- `0 ≤ x ≤ y` implies `‖x‖₂ ≤ ‖y‖₂` (self-duality). -/
theorem norm_le_of_isSq {x y : E} (hx : IsSq x) (hxy : IsSq (y - x)) : ‖x‖ ≤ ‖y‖ := by
  have h1 : 0 ≤ ⟪x, y - x⟫_ℝ := (selfduality x).mp hx _ hxy
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at h1
  have h2 : ‖x‖ ^ 2 ≤ ‖x‖ * ‖y‖ := by linarith [real_inner_le_norm x y]
  rcases eq_or_lt_of_le (norm_nonneg x) with h | h
  · rw [← h]; exact norm_nonneg y
  · nlinarith

/-- Every element is a difference of two positive elements. -/
theorem exists_isSq_sub (b : E) : ∃ b₁ b₂ : E, IsSq b₁ ∧ IsSq b₂ ∧ b = b₁ - b₂ :=
  ⟨b + ouNorm b • 1, ouNorm b • 1, (ouNorm_spec b).2.2, isSq_smul (ouNorm_nonneg b) isSq_one,
    by abel⟩

/-- The core of EJA 51: a non-empty bounded directed set `D` has a least upper
bound `a`, which is moreover the weak limit of `D`: `⟨i, b⟩ → ⟨a, b⟩` along
`D` for every `b`.  (The paper's argument: `b ↦ sup_i ⟨i, b⟩` on positive `b`,
extended linearly, is a bounded functional, whose Riesz vector is `a`.) -/
theorem dircomplete_aux (D : Set E) (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (hbdd : BddAbove D) : ∃ a : E, IsLUB D a ∧
      ∀ b : E, Filter.Tendsto (fun i : D => ⟪(i : E), b⟫_ℝ) Filter.atTop (nhds ⟪a, b⟫_ℝ) := by
  obtain ⟨c, hc⟩ := hbdd
  have : Nonempty D := hne.to_subtype
  have : IsDirectedOrder D := ⟨fun i j => by
    obtain ⟨k, hk, hik, hjk⟩ := hdir i i.2 j j.2
    exact ⟨⟨k, hk⟩, hik, hjk⟩⟩
  let f : E → D → ℝ := fun b i => ⟪(i : E), b⟫_ℝ
  have hmono : ∀ b, IsSq b → Monotone (f b) := by
    intro b hb i j hij
    have h := (selfduality _).mp ((pe_le_iff _ _).mp hij) b hb
    rw [inner_sub_left] at h
    show ⟪(i : E), b⟫_ℝ ≤ ⟪(j : E), b⟫_ℝ
    linarith
  have hub : ∀ b, IsSq b → ∀ i : D, f b i ≤ ⟪c, b⟫_ℝ := by
    intro b hb i
    have h := (selfduality _).mp ((pe_le_iff _ _).mp (hc i.2)) b hb
    rw [inner_sub_left] at h
    show ⟪(i : E), b⟫_ℝ ≤ ⟪c, b⟫_ℝ
    linarith
  have hpos : ∀ b, IsSq b → ∃ L, Filter.Tendsto (f b) Filter.atTop (nhds L) := by
    intro b hb
    exact ⟨_, tendsto_atTop_ciSup (hmono b hb) ⟨⟪c, b⟫_ℝ, by
      rintro _ ⟨i, rfl⟩; exact hub b hb i⟩⟩
  have hconv : ∀ b, ∃ L, Filter.Tendsto (f b) Filter.atTop (nhds L) := by
    intro b
    obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := exists_isSq_sub b
    obtain ⟨L₁, hL₁⟩ := hpos b₁ h₁
    obtain ⟨L₂, hL₂⟩ := hpos b₂ h₂
    refine ⟨L₁ - L₂, ?_⟩
    have := hL₁.sub hL₂
    convert this using 1
    funext i
    simp only [f, inner_sub_right, Pi.sub_apply]
  choose L hL using hconv
  have hadd : ∀ b b', L (b + b') = L b + L b' := by
    intro b b'
    refine tendsto_nhds_unique (hL (b + b')) ?_
    have := (hL b).add (hL b')
    convert this using 1
    funext i; simp only [f, inner_add_right, Pi.add_apply]
  have hsmul : ∀ (r : ℝ) b, L (r • b) = r * L b := by
    intro r b
    refine tendsto_nhds_unique (hL (r • b)) ?_
    have := (hL b).const_mul r
    convert this using 1
    funext i; simp only [f, real_inner_smul_right]
  -- a bound, from any `i₀ ∈ D`
  obtain ⟨i₀, hi₀⟩ := hne
  set K := ‖i₀‖ + ‖c - i₀‖ with hK
  have hnorm : ∀ i : D, (⟨i₀, hi₀⟩ : D) ≤ i → ‖(i : E)‖ ≤ K := by
    intro i hi
    have h1 : IsSq ((i : E) - i₀) := (pe_le_iff _ _).mp hi
    have h2 : IsSq ((c - i₀) - ((i : E) - i₀)) := by
      rw [sub_sub_sub_cancel_right]; exact (pe_le_iff _ _).mp (hc i.2)
    have h3 := norm_le_of_isSq h1 h2
    calc ‖(i : E)‖ = ‖i₀ + ((i : E) - i₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖i₀‖ + ‖(i : E) - i₀‖ := norm_add_le _ _
      _ ≤ K := by rw [hK]; linarith
  have hbound : ∀ b, |L b| ≤ K * ‖b‖ := by
    intro b
    refine le_of_tendsto (hL b).abs (Filter.eventually_atTop.mpr ⟨⟨i₀, hi₀⟩, fun i hi => ?_⟩)
    calc |f b i| ≤ ‖(i : E)‖ * ‖b‖ := abs_real_inner_le_norm _ _
      _ ≤ K * ‖b‖ := mul_le_mul_of_nonneg_right (hnorm i hi) (norm_nonneg b)
  let Ll : E →ₗ[ℝ] ℝ := ⟨⟨L, hadd⟩, hsmul⟩
  let Lc : E →L[ℝ] ℝ := Ll.mkContinuous K (fun b => by rw [Real.norm_eq_abs]; exact hbound b)
  set a := (InnerProductSpace.toDual ℝ E).symm Lc with ha
  have haL : ∀ b, ⟪a, b⟫_ℝ = L b := fun b => by
    rw [ha, InnerProductSpace.toDual_symm_apply]; rfl
  refine ⟨a, ⟨fun i hi => ?_, fun u hu => ?_⟩, fun b => by rw [haL]; exact hL b⟩
  · rw [pe_le_iff, selfduality]
    intro b hb
    rw [inner_sub_left, haL]
    have := (hmono b hb).ge_of_tendsto (hL b) ⟨i, hi⟩
    exact sub_nonneg.mpr this
  · rw [pe_le_iff, selfduality]
    intro b hb
    rw [inner_sub_left, haL]
    have : L b ≤ ⟪u, b⟫_ℝ := le_of_tendsto' (hL b) fun i => by
      have h := (selfduality _).mp ((pe_le_iff _ _).mp (hu i.2)) b hb
      rw [inner_sub_left] at h
      show ⟪(i : E), b⟫_ℝ ≤ ⟪u, b⟫_ℝ
      linarith
    exact sub_nonneg.mpr this

/-- **EJA 51** (`prop:dircomplete`, main.tex:1266, Proposition), first half:
an EJA is bounded directed complete. -/
theorem dircomplete (D : Set E) (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (hbdd : BddAbove D) : ∃ a : E, IsLUB D a :=
  (dircomplete_aux D hne hdir hbdd).imp fun _ h => h.1

/-- **EJA 6** for the paper's EJAs: a *state* is a positive unital linear
functional. -/
def IsStateP (ω : E →ₗ[ℝ] ℝ) : Prop := (∀ a : E, IsSq a → 0 ≤ ω a) ∧ ω 1 = 1

/-- A positive functional is *normal* when it preserves suprema of bounded
directed sets. -/
def IsNormal (ω : E →ₗ[ℝ] ℝ) : Prop :=
  ∀ D : Set E, D.Nonempty → DirectedOn (· ≤ ·) D → ∀ a : E, IsLUB D a → IsLUB (ω '' D) (ω a)

/-- **EJA 51**, second half: every state is normal.  As in the paper: a
state is (bounded, by EJA 49, hence) an inner product with a fixed vector,
and suprema are weak limits (`dircomplete_aux`). -/
theorem state_normal {ω : E →ₗ[ℝ] ℝ} (hω : IsStateP ω) : IsNormal ω := by
  intro D hne hdir a ha
  obtain ⟨c, d, hc, hd, hcd⟩ := equivalenttopology (E := E)
  have hbd : ∀ x : E, |ω x| ≤ d * ‖x‖ := by
    intro x
    obtain ⟨h0, h1, h2⟩ := ouNorm_spec x
    have e1 := hω.1 _ h1
    have e2 := hω.1 _ h2
    rw [map_sub, map_smul, hω.2, smul_eq_mul, mul_one] at e1
    rw [map_add, map_smul, hω.2, smul_eq_mul, mul_one] at e2
    rw [abs_le]
    constructor <;> linarith [(hcd x).2]
  let ωc : E →L[ℝ] ℝ := ω.mkContinuous d (fun x => by rw [Real.norm_eq_abs]; exact hbd x)
  set b₀ := (InnerProductSpace.toDual ℝ E).symm ωc with hb₀
  have hωb : ∀ x, ω x = ⟪x, b₀⟫_ℝ := fun x => by
    rw [real_inner_comm, hb₀, InnerProductSpace.toDual_symm_apply]; rfl
  obtain ⟨a', ha', hlim⟩ := dircomplete_aux D hne hdir ⟨a, ha.1⟩
  have haa : a' = a := ha'.unique ha
  subst haa
  have : Nonempty D := hne.to_subtype
  have : IsDirectedOrder D := ⟨fun i j => by
    obtain ⟨k, hk, hik, hjk⟩ := hdir i i.2 j j.2
    exact ⟨⟨k, hk⟩, hik, hjk⟩⟩
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨i, hi, rfl⟩
    have := hω.1 _ ((pe_le_iff _ _).mp (ha.1 hi))
    rw [map_sub] at this; linarith
  · have hl := hlim b₀
    rw [hωb]
    exact le_of_tendsto' hl fun i => by rw [← hωb]; exact hu ⟨i, i.2, rfl⟩

/-! ### EJA 52: idempotents are finite sums of atomic idempotents -/

/-- **EJA 10** for the paper's EJAs: an idempotent is *atomic* when there is
no non-zero idempotent strictly below it. -/
def IsAtomicP (p : E) : Prop := p * p = p ∧ ∀ q : E, q * q = q → q ≤ p → q ≠ p → q = 0

theorem idem_one_sub {g : E} (hg : g * g = g) : (1 - g) * (1 - g) = 1 - g := by
  rw [pj_sub_mul, pj_mul_sub, pj_mul_sub, pj_one_mul, pj_one_mul, pj_mul_one, hg]; abel

/-- For idempotents, `f ≤ g` implies `f * g = f` (the paper's EJA 11, for the
paper's EJAs): `⟨f, 1 − g⟩ = 0` by self-duality, so `L_{1−g} f = 0`. -/
theorem idem_le_mul {f g : E} (hf : f * f = f) (hg : g * g = g) (hfg : f ≤ g) : f * g = f := by
  set e := 1 - g with he
  have hee : e * e = e := idem_one_sub hg
  have h1 : 0 ≤ ⟪f, e⟫_ℝ := (selfduality f).mp (idem_isSq hf) e (idem_isSq hee)
  have h2 : 0 ≤ ⟪g - f, e⟫_ℝ := (selfduality _).mp ((pe_le_iff _ _).mp hfg) e (idem_isSq hee)
  have h3 : ⟪g, e⟫_ℝ = 0 := by
    have := PaperEJA.inner_mul g g e
    rw [hg, he, pj_mul_sub, pj_mul_one, hg, sub_self, inner_zero_right] at this
    exact this
  rw [inner_sub_left, h3] at h2
  have h4 : ⟪f, e⟫_ℝ = 0 := le_antisymm (by linarith) h1
  have h5 : ⟪e * f, f⟫_ℝ = 0 := by
    rw [PaperEJA.inner_mul, pj_mul_comm e f, ← PaperEJA.inner_mul, hf]; exact h4
  have h6 := idem_mul_eq_zero_of_inner hee h5
  rw [he, pj_sub_mul, pj_one_mul, sub_eq_zero] at h6
  rw [pj_mul_comm]; exact h6.symm

/-- **EJA 52** (`prop:atomicsum`, main.tex:1276, Proposition): every
idempotent is a finite sum of pairwise orthogonal atomic idempotents.  The
paper splits non-atomic idempotents and argues that the process stops, since
an infinite orthogonal family would span an infinite-dimensional associative
subalgebra (contradicting EJA 45); here a family of maximal size (bounded by
`r² ‖1‖²`, `IsIdemFamily.card_le`) cannot be split further. -/
theorem atomicsum {p : E} (hp : p * p = p) :
    ∃ T : Finset E, IsIdemFamily T ∧ (∀ q ∈ T, IsAtomicP q) ∧ ∑ q ∈ T, q = p := by
  classical
  let P : ℕ → Prop := fun k => ∃ T : Finset E, IsIdemFamily T ∧ ∑ q ∈ T, q = p ∧ T.card = k
  let B : ℕ := ⌊mulConst E ^ 2 * ‖(1 : E)‖ ^ 2⌋₊
  have hB : ∀ k, P k → k ≤ B := by
    rintro k ⟨T, hT, -, rfl⟩
    exact Nat.le_floor hT.card_le
  have hex : ∃ k, P k := by
    by_cases h0 : p = 0
    · exact ⟨0, ∅, ⟨by simp, by simp, by simp⟩, by simp [h0], rfl⟩
    · refine ⟨1, {p}, ⟨?_, ?_, ?_⟩, by simp, rfl⟩
      · intro q hq; rw [Finset.mem_singleton.mp hq]; exact hp
      · intro q hq; rw [Finset.mem_singleton.mp hq]; exact h0
      · intro q hq q' hq' hqq
        rw [Finset.mem_singleton.mp hq, Finset.mem_singleton.mp hq'] at hqq
        exact absurd rfl hqq
  obtain ⟨k₀, hk₀⟩ := hex
  obtain ⟨T, hT, hsum, hcard⟩ := Nat.findGreatest_spec (hB k₀ hk₀) hk₀
  refine ⟨T, hT, fun q hq => ⟨hT.idem q hq, ?_⟩, hsum⟩
  intro f hff hfq hfq'
  by_contra hf0
  have hfq1 : f * q = f := idem_le_mul hff (hT.idem q hq) hfq
  have hqf : q * f = f := by rw [pj_mul_comm]; exact hfq1
  have hfo : ∀ q' ∈ T.erase q, f * q' = 0 := by
    intro q' hq'
    obtain ⟨hne, hq'T⟩ := Finset.mem_erase.mp hq'
    -- `f ≤ q ≤ 1 − q'`
    have hsq : IsSq ((1 - q') - q) := by
      refine idem_isSq ?_
      have hqq' : q * q' = 0 := hT.orth q hq q' hq'T (Ne.symm hne)
      have hq'q : q' * q = 0 := by rw [pj_mul_comm]; exact hqq'
      simp only [pj_sub_mul, pj_mul_sub, pj_one_mul, pj_mul_one, hT.idem q' hq'T,
        hT.idem q hq, hqq', hq'q]
      abel
    have hle : f ≤ 1 - q' := by
      rw [pe_le_iff]
      have := ejaous_add hsq ((pe_le_iff _ _).mp hfq)
      convert this using 1; abel
    have h1 := idem_le_mul hff (idem_one_sub (hT.idem q' hq'T)) hle
    rw [pj_mul_sub, pj_mul_one, sub_eq_self] at h1
    exact h1
  have hg : (q - f) * (q - f) = q - f := by
    rw [pj_sub_mul, pj_mul_sub, pj_mul_sub, hT.idem q hq, hqf, hfq1, hff]; abel
  have hg0 : q - f ≠ 0 := sub_ne_zero.mpr (Ne.symm hfq')
  have hgo : ∀ q' ∈ T.erase q, (q - f) * q' = 0 := by
    intro q' hq'
    obtain ⟨hne, hq'T⟩ := Finset.mem_erase.mp hq'
    rw [pj_sub_mul, hT.orth q hq q' hq'T (Ne.symm hne), hfo q' hq', sub_zero]
  have hU : IsIdemFamily (T.erase q) :=
    ⟨fun r hr => hT.idem r (Finset.mem_of_mem_erase hr),
      fun r hr => hT.ne_zero r (Finset.mem_of_mem_erase hr),
      fun r hr r' hr' => hT.orth r (Finset.mem_of_mem_erase hr) r' (Finset.mem_of_mem_erase hr')⟩
  have hU2 := hU.insert hg hg0 hgo
  have hfg : ∀ r ∈ insert (q - f) (T.erase q), f * r = 0 := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · rw [pj_mul_sub, hff, hfq1, sub_self]
    · exact hfo r hr
  have hU3 := hU2.insert hff hf0 hfg
  have hnf := IsIdemFamily.not_mem_of_orth hff hf0 hfg
  have hng := IsIdemFamily.not_mem_of_orth hg hg0 hgo
  have hP : P (Nat.findGreatest P B + 1) := by
    refine ⟨insert f (insert (q - f) (T.erase q)), hU3, ?_, ?_⟩
    · rw [Finset.sum_insert hnf, Finset.sum_insert hng, ← add_assoc, add_sub_cancel,
        Finset.add_sum_erase T (fun r => r) hq, hsum]
    · rw [Finset.card_insert_of_notMem hnf, Finset.card_insert_of_notMem hng,
        Finset.card_erase_of_mem hq, hcard]
      have : 1 ≤ T.card := Finset.card_pos.mpr ⟨q, hq⟩
      omega
  have h1 := Nat.le_findGreatest (hB _ hP) hP
  omega

/-! ### EJA 53: an EJA is a type I JBW-algebra of finite rank -/

/-- The defining properties of a **type I JBW-algebra of finite rank**, as
the paper's proof of EJA 53 spells them out (JBW-algebras are not in
Mathlib): a JB-algebra (for the order unit norm) that is bounded directed
complete and separated by normal states; *type I*: below every non-zero
idempotent there is a non-zero atomic idempotent; *finite rank*: `1` is a
finite sum of (orthogonal) atomic idempotents. -/
structure IsTypeIFiniteRankJBW (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [Mul E] [One E] [PaperEJA E] : Prop where
  jb : IsJBNorm (ouNorm (E := E))
  dircomplete : ∀ D : Set E, D.Nonempty → DirectedOn (· ≤ ·) D → BddAbove D →
    ∃ a : E, IsLUB D a
  separating : ∀ a : E, a ≠ 0 → ∃ ω : E →ₗ[ℝ] ℝ, IsStateP ω ∧ IsNormal ω ∧ ω a ≠ 0
  typeI : ∀ p : E, p * p = p → p ≠ 0 → ∃ q : E, IsAtomicP q ∧ q ≠ 0 ∧ q ≤ p
  finiteRank : ∃ T : Finset E, IsIdemFamily T ∧ (∀ q ∈ T, IsAtomicP q) ∧ ∑ q ∈ T, q = 1

/-- **EJA 53** (main.tex:1285, Proposition): an EJA is a type I JBW-algebra of
finite rank.  The paper's proof: JB by EJA 50, bounded directed complete with
all states normal by EJA 51 (states separate points: `⟨·, p⟩ / ⟨p, p⟩` for an
idempotent `p` of the spectral decomposition), type I and of finite rank by
EJA 52. -/
theorem typeI_finiteRank : IsTypeIFiniteRankJBW E where
  jb := EJAisJB
  dircomplete := dircomplete
  separating a ha := by
    obtain ⟨T, hT, -, -, c, hc⟩ := spectral_family a
    have : ∃ q ∈ T, c q ≠ 0 := by
      by_contra h
      push Not at h
      apply ha
      rw [hc]; exact Finset.sum_eq_zero fun p hp => by rw [h p hp, zero_smul]
    obtain ⟨q, hq, hcq⟩ := this
    have hqq := hT.inner_self_pos hq
    let ω : E →ₗ[ℝ] ℝ := (⟪q, q⟫_ℝ)⁻¹ • innerₗ E q
    have hωx : ∀ x, ω x = ⟪x, q⟫_ℝ / ⟪q, q⟫_ℝ := fun x => by
      show (⟪q, q⟫_ℝ)⁻¹ • ⟪q, x⟫_ℝ = _
      rw [smul_eq_mul, real_inner_comm x q, div_eq_inv_mul]
    have hst : IsStateP ω := by
      refine ⟨fun x hx => ?_, ?_⟩
      · rw [hωx]
        exact div_nonneg ((selfduality x).mp hx q (idem_isSq (hT.idem q hq))) hqq.le
      · rw [hωx, real_inner_comm, idem_inner_one (hT.idem q hq)]; exact div_self hqq.ne'
    refine ⟨ω, hst, state_normal hst, ?_⟩
    rw [hωx, hc, hT.coeff hq]; exact hcq
  typeI p hp hp0 := by
    classical
    obtain ⟨T, hT, hat, hsum⟩ := atomicsum hp
    have : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; rintro rfl; exact hp0 (by rw [← hsum]; simp)
    obtain ⟨q, hq⟩ := this
    refine ⟨q, hat q hq, hT.ne_zero q hq, ?_⟩
    rw [pe_le_iff, ← hsum, ← Finset.add_sum_erase T (fun r => r) hq, add_sub_cancel_left]
    refine idem_isSq ?_
    have hU : IsIdemFamily (T.erase q) :=
      ⟨fun r hr => hT.idem r (Finset.mem_of_mem_erase hr),
        fun r hr => hT.ne_zero r (Finset.mem_of_mem_erase hr),
        fun r hr r' hr' => hT.orth r (Finset.mem_of_mem_erase hr) r'
          (Finset.mem_of_mem_erase hr')⟩
    exact hU.sum_idem
  finiteRank := atomicsum (pj_mul_one (1 : E))

end Order

/-! ## EJA 3: the matrix algebras `M_n(F)^sa` -/

section Examples

open Matrix

/-- The scalars of EJA 3: a real star algebra `F` (possibly non-associative)
with a real-part functional `re` that is a trace (`re (x y) = re (y x)`,
`re ((x y) z) = re (x (y z))`) and positive definite (`re (x x*) ≥ 0`, with
equality only for `x = 0`).  The print's `ℝ`, `ℂ` and `ℍ` are instances; so
are the octonions (`Oct`, below). -/
class EJAScalars (F : Type u) [NonAssocRing F] [StarRing F] [Module ℝ F] where
  re : F →ₗ[ℝ] ℝ
  re_mul_comm : ∀ x y : F, re (x * y) = re (y * x)
  re_mul_assoc : ∀ x y z : F, re (x * y * z) = re (x * (y * z))
  re_mul_star_nonneg : ∀ x : F, 0 ≤ re (x * star x)
  eq_zero_of_re_mul_star : ∀ x : F, re (x * star x) = 0 → x = 0

variable (n : ℕ) (F : Type u) [NonAssocRing F] [StarRing F] [Module ℝ F] [StarModule ℝ F]
  [IsScalarTower ℝ F F] [SMulCommClass ℝ F F] [EJAScalars F]

/-- The self-adjoint `n × n` matrices over `F` (`A_{ij} = conj A_{ji}`). -/
def hermSub : Submodule ℝ (Matrix (Fin n) (Fin n) F) where
  carrier := {A | A.IsHermitian}
  add_mem' ha hb := IsHermitian.add ha hb
  zero_mem' := isHermitian_zero
  smul_mem' r A hA := by
    show (r • A).IsHermitian
    unfold Matrix.IsHermitian at hA ⊢
    rw [conjTranspose_smul, hA, star_trivial]

/-- `M_n(F)^sa`, the type of self-adjoint matrices (EJA 3). -/
def HermMat : Type u := ↥(hermSub n F)

instance : AddCommGroup (HermMat n F) := inferInstanceAs (AddCommGroup ↥(hermSub n F))

instance : Module ℝ (HermMat n F) := inferInstanceAs (Module ℝ ↥(hermSub n F))

variable {n F}

/-- The underlying matrix. -/
def HermMat.mat (A : HermMat n F) : Matrix (Fin n) (Fin n) F := (A : ↥(hermSub n F)).1

theorem HermMat.herm (A : HermMat n F) : A.mat.IsHermitian := (A : ↥(hermSub n F)).2

theorem HermMat.ext {A B : HermMat n F} (h : A.mat = B.mat) : A = B := Subtype.ext h

@[simp] theorem HermMat.mat_add (A B : HermMat n F) : (A + B).mat = A.mat + B.mat := rfl

@[simp] theorem HermMat.mat_smul (r : ℝ) (A : HermMat n F) : (r • A).mat = r • A.mat := rfl

@[simp] theorem HermMat.mat_zero : (0 : HermMat n F).mat = 0 := rfl

/-- The Jordan product `A * B = ½ (A B + B A)`. -/
noncomputable instance : Mul (HermMat n F) where
  mul A B := (⟨(1 / 2 : ℝ) • (A.mat * B.mat + B.mat * A.mat), by
    show ((1 / 2 : ℝ) • (A.mat * B.mat + B.mat * A.mat)).IsHermitian
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, star_trivial, conjTranspose_add, conjTranspose_mul,
      conjTranspose_mul, A.herm.eq, B.herm.eq, add_comm]⟩ : ↥(hermSub n F))

/-- The identity matrix. -/
instance : One (HermMat n F) where
  one := (⟨1, isHermitian_one⟩ : ↥(hermSub n F))

@[simp] theorem HermMat.mat_mul (A B : HermMat n F) :
    (A * B).mat = (1 / 2 : ℝ) • (A.mat * B.mat + B.mat * A.mat) := rfl

@[simp] theorem HermMat.mat_one : (1 : HermMat n F).mat = 1 := rfl

/-- `re tr (X Y) = Σᵢ Σⱼ re (X i j * Y j i)`. -/
theorem re_trace_mul (X Y : Matrix (Fin n) (Fin n) F) :
    EJAScalars.re (trace (X * Y)) = ∑ i, ∑ j, EJAScalars.re (X i j * Y j i) := by
  simp only [trace, diag, mul_apply, map_sum]

theorem re_trace_mul_comm (X Y : Matrix (Fin n) (Fin n) F) :
    EJAScalars.re (trace (X * Y)) = EJAScalars.re (trace (Y * X)) := by
  rw [re_trace_mul, re_trace_mul, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => EJAScalars.re_mul_comm _ _

theorem re_trace_mul_assoc (X Y Z : Matrix (Fin n) (Fin n) F) :
    EJAScalars.re (trace (X * Y * Z)) = EJAScalars.re (trace (X * (Y * Z))) := by
  rw [re_trace_mul, re_trace_mul]
  simp only [mul_apply, Finset.sum_mul, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    EJAScalars.re_mul_assoc _ _ _

/-- The inner product `⟨A, B⟩ = re tr (A B)` (the print writes `tr (A B)`;
for `F = ℍ` that is not real, and its real part is meant). -/
noncomputable def hermInner (A B : HermMat n F) : ℝ := EJAScalars.re (trace (A.mat * B.mat))

theorem hermInner_self (A : HermMat n F) :
    hermInner A A = ∑ i, ∑ j, EJAScalars.re (A.mat i j * star (A.mat i j)) := by
  rw [hermInner, re_trace_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [A.herm.apply j i]

theorem hermInner_self_nonneg (A : HermMat n F) : 0 ≤ hermInner A A := by
  rw [hermInner_self]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    EJAScalars.re_mul_star_nonneg _

theorem hermInner_self_eq_zero {A : HermMat n F} (h : hermInner A A = 0) : A = 0 := by
  rw [hermInner_self] at h
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    EJAScalars.re_mul_star_nonneg (A.mat i j)).mp h
  refine HermMat.ext (Matrix.ext fun i j => ?_)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
    EJAScalars.re_mul_star_nonneg (A.mat i j)).mp (h1 i (Finset.mem_univ _)) j (Finset.mem_univ _)
  exact EJAScalars.eq_zero_of_re_mul_star _ h2

noncomputable instance hermCore : InnerProductSpace.Core ℝ (HermMat n F) where
  inner := hermInner
  conj_inner_symm A B := by
    rw [conj_trivial]; exact re_trace_mul_comm _ _
  re_inner_nonneg A := by
    rw [RCLike.re_to_real]; exact hermInner_self_nonneg A
  add_left A B C := by
    show EJAScalars.re (trace ((A + B).mat * C.mat)) = _
    rw [HermMat.mat_add, Matrix.add_mul, trace_add, map_add]; rfl
  smul_left A B r := by
    show EJAScalars.re (trace ((r • A).mat * B.mat)) = _
    rw [HermMat.mat_smul, Matrix.smul_mul, trace_smul, map_smul, conj_trivial, smul_eq_mul]; rfl
  definite A h := hermInner_self_eq_zero h

noncomputable instance : NormedAddCommGroup (HermMat n F) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

noncomputable instance : InnerProductSpace ℝ (HermMat n F) :=
  InnerProductSpace.ofCore (hermCore (n := n) (F := F)).toCore

theorem hermMat_inner (A B : HermMat n F) :
    ⟪A, B⟫_ℝ = EJAScalars.re (trace (A.mat * B.mat)) := rfl

instance [FiniteDimensional ℝ F] : FiniteDimensional ℝ (HermMat n F) :=
  inferInstanceAs (FiniteDimensional ℝ ↥(hermSub n F))

instance [FiniteDimensional ℝ F] : CompleteSpace (HermMat n F) :=
  FiniteDimensional.complete ℝ (HermMat n F)

/-- All the axioms of EJA 1 for `M_n(F)^sa` except the Jordan identity, which
is the hypothesis: for any scalars `F` in the sense of `EJAScalars` (not
necessarily associative), `M_n(F)^sa` with `A * B = ½(AB + BA)`,
`⟨A, B⟩ = re tr (AB)` and unit the identity matrix is a Euclidean Jordan
algebra as soon as its product satisfies the Jordan identity. -/
theorem hermMat_paperEJA_of_jordan [FiniteDimensional ℝ F]
    (hJ : ∀ A B : HermMat n F, (A * B) * (A * A) = A * (B * (A * A))) :
    PaperEJA (HermMat n F) where
  mul_comm A B := HermMat.ext (by simp only [HermMat.mat_mul, add_comm])
  mul_add A B C := HermMat.ext (by
    simp only [HermMat.mat_mul, HermMat.mat_add, Matrix.mul_add, Matrix.add_mul, smul_add]
    abel)
  smul_mul r A B := HermMat.ext (by
    simp only [HermMat.mat_mul, HermMat.mat_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul, mul_comm r])
  one_mul A := HermMat.ext (by
    simp only [HermMat.mat_mul, HermMat.mat_one, Matrix.one_mul, Matrix.mul_one]
    rw [← two_smul ℝ A.mat, smul_smul]; norm_num)
  jordan := hJ
  inner_mul A B C := by
    simp only [hermMat_inner, HermMat.mat_mul, Matrix.smul_mul, Matrix.mul_smul, trace_smul,
      map_smul, Matrix.add_mul, Matrix.mul_add, trace_add, map_add, smul_eq_mul]
    congr 1
    have h1 := re_trace_mul_assoc A.mat B.mat C.mat
    have h2 := re_trace_mul_comm A.mat (B.mat * C.mat)
    have h3 := re_trace_mul_assoc B.mat C.mat A.mat
    have h4 := re_trace_mul_assoc B.mat A.mat C.mat
    linarith

/-- The Jordan identity for the symmetrised product `½(ab + ba)` of an
associative real algebra. -/
theorem sym_jordan {R : Type*} [Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    (a b : R) :
    let j : R → R → R := fun x y => (1 / 2 : ℝ) • (x * y + y * x)
    j (j a b) (j a a) = j a (j b (j a a)) := by
  intro j
  simp only [j, smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  module

/-- **EJA 3** (main.tex:212, Example), for associative scalars: `M_n(F)^sa`
is a Euclidean Jordan algebra, with `A * B = ½(AB + BA)`,
`⟨A, B⟩ = re tr (AB)` and the identity matrix as unit. -/
instance hermMat_paperEJA {F : Type u} [Ring F] [StarRing F] [Algebra ℝ F] [StarModule ℝ F]
    [EJAScalars F] [FiniteDimensional ℝ F] : PaperEJA (HermMat n F) :=
  hermMat_paperEJA_of_jordan fun A B => HermMat.ext (by
    have h := sym_jordan A.mat B.mat
    simp only [HermMat.mat_mul]
    exact h)

/-- `ℝ` as EJA scalars. -/
noncomputable instance : EJAScalars ℝ where
  re := LinearMap.id
  re_mul_comm x y := mul_comm x y
  re_mul_assoc x y z := mul_assoc x y z
  re_mul_star_nonneg x := by simp [mul_self_nonneg]
  eq_zero_of_re_mul_star x h := by simpa using h

/-- `ℂ` as EJA scalars (`re (z z̄) = |z|²`). -/
noncomputable instance : EJAScalars ℂ where
  re := Complex.reLm
  re_mul_comm x y := by rw [mul_comm]
  re_mul_assoc x y z := by rw [mul_assoc]
  re_mul_star_nonneg x := by
    simp only [Complex.reLm_coe, Complex.star_def, Complex.mul_conj]
    rw [Complex.ofReal_re]; exact Complex.normSq_nonneg x
  eq_zero_of_re_mul_star x h := by
    simp only [Complex.reLm_coe, Complex.star_def, Complex.mul_conj, Complex.ofReal_re] at h
    exact Complex.normSq_eq_zero.mp h

instance : StarModule ℝ (Quaternion ℝ) where
  star_smul r x := by ext <;> simp

/-- The quaternions `ℍ` as EJA scalars (`re (q q̄) = |q|²`). -/
noncomputable instance : EJAScalars (Quaternion ℝ) where
  re := QuaternionAlgebra.reₗ (-1) 0 (-1)
  re_mul_comm x y := by
    show (x * y).re = (y * x).re
    simp only [Quaternion.re_mul]; ring
  re_mul_assoc x y z := by rw [mul_assoc]
  re_mul_star_nonneg x := by
    show 0 ≤ (x * star x).re
    rw [Quaternion.self_mul_star, Quaternion.re_coe]; exact Quaternion.normSq_nonneg
  eq_zero_of_re_mul_star x h := by
    change (x * star x).re = 0 at h
    rw [Quaternion.self_mul_star, Quaternion.re_coe] at h
    exact Quaternion.normSq_eq_zero.mp h

/-- The quaternion `i`. -/
def qI : Quaternion ℝ := ⟨0, 1, 0, 0⟩

/-- The quaternion `j`. -/
def qJ : Quaternion ℝ := ⟨0, 0, 1, 0⟩

@[simp] theorem qI_re : qI.re = 0 := rfl
@[simp] theorem qI_imI : qI.imI = 1 := rfl
@[simp] theorem qI_imJ : qI.imJ = 0 := rfl
@[simp] theorem qI_imK : qI.imK = 0 := rfl
@[simp] theorem qJ_re : qJ.re = 0 := rfl
@[simp] theorem qJ_imI : qJ.imI = 0 := rfl
@[simp] theorem qJ_imJ : qJ.imJ = 1 := rfl
@[simp] theorem qJ_imK : qJ.imK = 0 := rfl

theorem star_qI : star qI = -qI := by ext <;> simp
theorem star_qJ : star qJ = -qJ := by ext <;> simp

/-- **EJA 3, as printed, is false for `F = ℍ`**: the print's inner product
`⟨A, B⟩ = tr (AB)` is not real-valued on `M_2(ℍ)^sa` — with `A`, `B` the
self-adjoint matrices with off-diagonal entries `i, −i` and `j, −j`,
`tr (AB) = −2k`.  The real part `re tr (AB)` is meant (`hermMat_inner`). -/
theorem example3_trace_not_real :
    ∃ A B : Matrix (Fin 2) (Fin 2) (Quaternion ℝ), A.IsHermitian ∧ B.IsHermitian ∧
      (trace (A * B)).imK ≠ 0 := by
  refine ⟨!![0, qI; -qI, 0], !![0, qJ; -qJ, 0], ?_, ?_, ?_⟩
  · refine Matrix.IsHermitian.ext fun a b => ?_
    fin_cases a <;> fin_cases b <;> simp [star_qI]
  · refine Matrix.IsHermitian.ext fun a b => ?_
    fin_cases a <;> fin_cases b <;> simp [star_qJ]
  · have h : trace (!![0, qI; -qI, 0] * !![0, qJ; -qJ, 0]) = -(qI * qJ) + -(qI * qJ) := by
      simp [trace_fin_two]
    rw [h]
    simp [Quaternion.imK_mul]

/-- **EJA 3** (main.tex:212, Example): for `F = ℝ, ℂ, ℍ`, `M_n(F)^sa` is a
Euclidean Jordan algebra. -/
theorem matrix_examples (n : ℕ) :
    PaperEJA (HermMat n ℝ) ∧ PaperEJA (HermMat n ℂ) ∧ PaperEJA (HermMat n (Quaternion ℝ)) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-! ### The octonions, and the exceptional example -/

/-- The **octonions** `𝕆 = ℍ ⊕ ℍ`, the Cayley–Dickson double of the
quaternions: `(a, b)(c, d) = (a c − d̄ b, d a + b c̄)`, `(a, b)* = (ā, −b)`.
(Not in Mathlib; built here only as far as EJA 3 needs.) -/
def Oct : Type := Quaternion ℝ × Quaternion ℝ

namespace Oct

noncomputable section

instance : AddCommGroup Oct := inferInstanceAs (AddCommGroup (Quaternion ℝ × Quaternion ℝ))

instance : Module ℝ Oct := inferInstanceAs (Module ℝ (Quaternion ℝ × Quaternion ℝ))

instance : FiniteDimensional ℝ Oct :=
  inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))

/-- The first quaternion coordinate. -/
def fst (x : Oct) : Quaternion ℝ := Prod.fst (α := Quaternion ℝ) (β := Quaternion ℝ) x

/-- The second quaternion coordinate. -/
def snd (x : Oct) : Quaternion ℝ := Prod.snd (α := Quaternion ℝ) (β := Quaternion ℝ) x

/-- An octonion from two quaternions. -/
def mk (a b : Quaternion ℝ) : Oct := (a, b)

@[simp] theorem mk_fst (a b : Quaternion ℝ) : (mk a b).fst = a := rfl
@[simp] theorem mk_snd (a b : Quaternion ℝ) : (mk a b).snd = b := rfl

theorem ext {x y : Oct} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := Prod.ext h1 h2

@[simp] theorem add_fst (x y : Oct) : (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem add_snd (x y : Oct) : (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem zero_fst : (0 : Oct).fst = 0 := rfl
@[simp] theorem zero_snd : (0 : Oct).snd = 0 := rfl
@[simp] theorem neg_fst (x : Oct) : (-x).fst = -x.fst := rfl
@[simp] theorem neg_snd (x : Oct) : (-x).snd = -x.snd := rfl
@[simp] theorem sub_fst (x y : Oct) : (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem sub_snd (x y : Oct) : (x - y).snd = x.snd - y.snd := rfl
@[simp] theorem smul_fst (r : ℝ) (x : Oct) : (r • x).fst = r • x.fst := rfl
@[simp] theorem smul_snd (r : ℝ) (x : Oct) : (r • x).snd = r • x.snd := rfl

instance : Mul Oct := ⟨fun x y => mk (x.fst * y.fst - star y.snd * x.snd)
  (y.snd * x.fst + x.snd * star y.fst)⟩

instance : One Oct := ⟨mk 1 0⟩

instance : Star Oct := ⟨fun x => mk (star x.fst) (-x.snd)⟩

@[simp] theorem mul_fst (x y : Oct) : (x * y).fst = x.fst * y.fst - star y.snd * x.snd := rfl
@[simp] theorem mul_snd (x y : Oct) : (x * y).snd = y.snd * x.fst + x.snd * star y.fst := rfl
@[simp] theorem one_fst : (1 : Oct).fst = 1 := rfl
@[simp] theorem one_snd : (1 : Oct).snd = 0 := rfl
@[simp] theorem star_fst (x : Oct) : (star x).fst = star x.fst := rfl
@[simp] theorem star_snd (x : Oct) : (star x).snd = -x.snd := rfl

instance : NatCast Oct := ⟨fun k => mk (k : Quaternion ℝ) 0⟩
instance : IntCast Oct := ⟨fun k => mk (k : Quaternion ℝ) 0⟩

@[simp] theorem natCast_fst (k : ℕ) : (k : Oct).fst = k := rfl
@[simp] theorem natCast_snd (k : ℕ) : (k : Oct).snd = 0 := rfl
@[simp] theorem intCast_fst (k : ℤ) : (k : Oct).fst = k := rfl
@[simp] theorem intCast_snd (k : ℤ) : (k : Oct).snd = 0 := rfl

instance : NonAssocRing Oct :=
  { (inferInstance : AddCommGroup Oct) with
    left_distrib := fun x y z => ext (by simp [mul_add, add_mul, star_add] <;> abel)
      (by simp [add_mul, mul_add] <;> abel)
    right_distrib := fun x y z => ext (by simp [add_mul, mul_add] <;> abel)
      (by simp [mul_add, add_mul, star_add] <;> abel)
    zero_mul := fun x => ext (by simp) (by simp)
    mul_zero := fun x => ext (by simp) (by simp)
    one_mul := fun x => ext (by simp) (by simp)
    mul_one := fun x => ext (by simp) (by simp)
    natCast_zero := ext (by simp) (by simp)
    natCast_succ := fun k => ext (by simp) (by simp)
    intCast_ofNat := fun k => ext (by simp) (by simp)
    intCast_negSucc := fun k => ext (by simp) (by simp) }

instance : StarRing Oct where
  star_involutive x := ext (by simp) (by simp)
  star_mul x y := ext (by simp [star_sub, star_mul]) (by simp [star_mul] <;> abel)
  star_add x y := ext (by simp [star_add]) (by simp <;> abel)

instance : StarModule ℝ Oct where
  star_smul r x := ext (by simp [star_smul]) (by simp)

instance : IsScalarTower ℝ Oct Oct where
  smul_assoc r x y := ext (by simp [smul_sub, smul_mul_assoc, mul_smul_comm])
    (by simp [smul_add, smul_mul_assoc, mul_smul_comm])

instance : SMulCommClass ℝ Oct Oct where
  smul_comm r x y := ext (by simp [smul_sub, smul_mul_assoc, mul_smul_comm, star_smul])
    (by simp [smul_add, smul_mul_assoc, mul_smul_comm, star_smul])

/-- The real part `re (a, b) = re a`. -/
def reL : Oct →ₗ[ℝ] ℝ where
  toFun x := x.fst.re
  map_add' x y := rfl
  map_smul' r x := by simp

theorem re_mul_star (x : Oct) :
    reL (x * star x) = Quaternion.normSq x.fst + Quaternion.normSq x.snd := by
  show (x * star x).fst.re = _
  simp only [mul_fst, star_fst, star_snd, star_neg, neg_mul, sub_neg_eq_add,
    Quaternion.re_add, Quaternion.self_mul_star, Quaternion.star_mul_self, Quaternion.re_coe]

/-- The octonions as EJA scalars: `re` is a trace (in particular
`re ((x y) z) = re (x (y z))` although `𝕆` is not associative). -/
noncomputable instance : EJAScalars Oct where
  re := reL
  re_mul_comm x y := by
    show (x * y).fst.re = (y * x).fst.re
    simp only [mul_fst, Quaternion.re_sub, Quaternion.re_mul, Quaternion.re_star,
      Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
    ring
  re_mul_assoc x y z := by
    show (x * y * z).fst.re = (x * (y * z)).fst.re
    simp only [mul_fst, mul_snd, Quaternion.re_sub, Quaternion.re_add, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
      Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, star_sub, star_add,
      star_mul, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
      Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add]
    ring
  re_mul_star_nonneg x := by
    rw [re_mul_star]; exact add_nonneg Quaternion.normSq_nonneg Quaternion.normSq_nonneg
  eq_zero_of_re_mul_star x h := by
    rw [re_mul_star] at h
    have h1 : Quaternion.normSq x.fst = 0 :=
      le_antisymm (by linarith [Quaternion.normSq_nonneg (a := x.snd)]) Quaternion.normSq_nonneg
    have h2 : Quaternion.normSq x.snd = 0 :=
      le_antisymm (by linarith [Quaternion.normSq_nonneg (a := x.fst)]) Quaternion.normSq_nonneg
    exact ext (Quaternion.normSq_eq_zero.mp h1) (Quaternion.normSq_eq_zero.mp h2)

/-- `𝕆` is not associative: `(i j) ℓ = k ℓ ≠ −k ℓ = i (j ℓ)` for `ℓ = (0, 1)`,
so the associative case of EJA 3 (`hermMat_paperEJA`) does not cover it. -/
theorem not_assoc : ∃ x y z : Oct, x * y * z ≠ x * (y * z) := by
  let qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
  let qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
  have hij : qi * qj ≠ qj * qi := by
    intro h
    have h1 := congrArg (fun q : Quaternion ℝ => q.imK) h
    simp only [Quaternion.imK_mul] at h1
    have e1 : qi.re = 0 := rfl
    have e2 : qi.imI = 1 := rfl
    have e3 : qi.imJ = 0 := rfl
    have e4 : qi.imK = 0 := rfl
    have f1 : qj.re = 0 := rfl
    have f2 : qj.imI = 0 := rfl
    have f3 : qj.imJ = 1 := rfl
    have f4 : qj.imK = 0 := rfl
    simp only [e1, e2, e3, e4, f1, f2, f3, f4] at h1
    norm_num at h1
  refine ⟨mk qi 0, mk qj 0, mk 0 1, fun h => hij ?_⟩
  have h2 := congrArg Oct.snd h
  simp only [mul_fst, mul_snd] at h2
  simp only [Oct.fst, Oct.snd, Oct.mk] at h2
  simpa using h2

end

end Oct

/-- **EJA 3** (main.tex:212, Example), second paragraph: the exceptional
algebra `M_3(𝕆)^sa`.  Every axiom of EJA 1 is verified for it (with `𝕆` the
Cayley–Dickson octonions `Oct`) except the Jordan identity of its product,
which the print asserts without proof and which is taken here as the explicit
hypothesis `hJ` (its classical proofs — via the alternative laws and the
cubic Hamilton–Cayley identity of `M_3(𝕆)^sa` — are not formalised). -/
theorem exceptional_of_jordan
    (hJ : ∀ A B : HermMat 3 Oct, (A * B) * (A * A) = A * (B * (A * A))) :
    PaperEJA (HermMat 3 Oct) :=
  hermMat_paperEJA_of_jordan hJ

end Examples


/-! ## EJA 54: the decomposition into factors -/

section Decomposition

/-- `z` is **central** (operator-commutes with everything):
`z * (x * y) = (z * x) * y` for all `x, y`. -/
def IsCentral {V : Type u} [Mul V] (z : V) : Prop := ∀ x y : V, z * (x * y) = (z * x) * y

/-- A Jordan algebra is a **factor** when its centre is `ℝ 1`. -/
def IsFactor (V : Type u) [AddCommGroup V] [Module ℝ V] [Mul V] [One V] : Prop :=
  ∀ w : V, IsCentral w → ∃ t : ℝ, w = t • (1 : V)

/-- An **isomorphism of (Euclidean) Jordan algebras**: a linear bijection
preserving product and unit.  (By EJA 36 these are the isomorphisms of
`EJA_psu`; the inner product need not be preserved.) -/
structure EJAIso (A B : Type u) [AddCommGroup A] [Module ℝ A] [Mul A] [One A]
    [AddCommGroup B] [Module ℝ B] [Mul B] [One B] where
  toLinearEquiv : A ≃ₗ[ℝ] B
  map_mul : ∀ x y : A, toLinearEquiv (x * y) = toLinearEquiv x * toLinearEquiv y
  map_one : toLinearEquiv 1 = 1

namespace EJAIso

variable {A B C : Type u} [AddCommGroup A] [Module ℝ A] [Mul A] [One A]
  [AddCommGroup B] [Module ℝ B] [Mul B] [One B] [AddCommGroup C] [Module ℝ C] [Mul C] [One C]

/-- Composition of isomorphisms. -/
def trans (f : EJAIso A B) (g : EJAIso B C) : EJAIso A C where
  toLinearEquiv := f.toLinearEquiv.trans g.toLinearEquiv
  map_mul x y := by simp [f.map_mul, g.map_mul]
  map_one := by simp [f.map_one, g.map_one]

end EJAIso

/-! ### Finite direct sums of EJAs -/

section Sums

variable {ι : Type u} [Fintype ι] (A : ι → Type u) [∀ i, NormedAddCommGroup (A i)]
  [∀ i, InnerProductSpace ℝ (A i)]

/-- The direct sum `⨁ᵢ Aᵢ` of a finite family of EJAs (`ℓ²` inner product,
componentwise product). -/
def EJAPi : Type u := PiLp 2 A

noncomputable instance : NormedAddCommGroup (EJAPi A) :=
  inferInstanceAs (NormedAddCommGroup (PiLp 2 A))

noncomputable instance : InnerProductSpace ℝ (EJAPi A) :=
  inferInstanceAs (InnerProductSpace ℝ (PiLp 2 A))

instance [∀ i, CompleteSpace (A i)] : CompleteSpace (EJAPi A) :=
  inferInstanceAs (CompleteSpace (PiLp 2 A))

instance [∀ i, FiniteDimensional ℝ (A i)] : FiniteDimensional ℝ (EJAPi A) :=
  inferInstanceAs (FiniteDimensional ℝ (PiLp 2 A))

variable {A}

/-- The `i`-th component. -/
def EJAPi.proj (x : EJAPi A) (i : ι) : A i := WithLp.ofLp (show PiLp 2 A from x) i

/-- An element from its components. -/
def EJAPi.mk (f : ∀ i, A i) : EJAPi A := WithLp.toLp 2 f

@[simp] theorem EJAPi.proj_mk (f : ∀ i, A i) (i : ι) : (EJAPi.mk f).proj i = f i := rfl

theorem EJAPi.ext {x y : EJAPi A} (h : ∀ i, x.proj i = y.proj i) : x = y := by
  show @Eq (PiLp 2 A) x y
  exact PiLp.ext h

@[simp] theorem EJAPi.proj_add (x y : EJAPi A) (i : ι) : (x + y).proj i = x.proj i + y.proj i :=
  rfl

@[simp] theorem EJAPi.proj_smul (r : ℝ) (x : EJAPi A) (i : ι) : (r • x).proj i = r • x.proj i :=
  rfl

@[simp] theorem EJAPi.proj_zero (i : ι) : (0 : EJAPi A).proj i = 0 := rfl

theorem EJAPi.inner_eq (x y : EJAPi A) : ⟪x, y⟫_ℝ = ∑ i, ⟪x.proj i, y.proj i⟫_ℝ :=
  PiLp.inner_apply (show PiLp 2 A from x) (show PiLp 2 A from y)

variable [∀ i, Mul (A i)] [∀ i, One (A i)]

noncomputable instance : Mul (EJAPi A) := ⟨fun x y => EJAPi.mk fun i => x.proj i * y.proj i⟩

instance : One (EJAPi A) := ⟨EJAPi.mk fun _ => 1⟩

@[simp] theorem EJAPi.proj_mul (x y : EJAPi A) (i : ι) : (x * y).proj i = x.proj i * y.proj i :=
  rfl

@[simp] theorem EJAPi.proj_one (i : ι) : (1 : EJAPi A).proj i = 1 := rfl

instance [∀ i, CompleteSpace (A i)] [∀ i, PaperEJA (A i)] : PaperEJA (EJAPi A) where
  mul_comm x y := EJAPi.ext fun i => by simp only [EJAPi.proj_mul]; exact PaperEJA.mul_comm _ _
  mul_add x y z := EJAPi.ext fun i => by
    simp only [EJAPi.proj_mul, EJAPi.proj_add]; exact PaperEJA.mul_add _ _ _
  smul_mul r x y := EJAPi.ext fun i => by
    simp only [EJAPi.proj_mul, EJAPi.proj_smul]; exact PaperEJA.smul_mul _ _ _
  one_mul x := EJAPi.ext fun i => by
    simp only [EJAPi.proj_mul, EJAPi.proj_one]; exact PaperEJA.one_mul _
  jordan x y := EJAPi.ext fun i => by simp only [EJAPi.proj_mul]; exact PaperEJA.jordan _ _
  inner_mul x y z := by
    simp only [EJAPi.inner_eq, EJAPi.proj_mul]
    exact Finset.sum_congr rfl fun i _ => PaperEJA.inner_mul _ _ _

variable (B C : Type u) [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]

/-- The direct sum `B ⊕ C` of two EJAs. -/
def EJASum : Type u := WithLp 2 (B × C)

noncomputable instance : NormedAddCommGroup (EJASum B C) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (B × C)))

noncomputable instance : InnerProductSpace ℝ (EJASum B C) :=
  inferInstanceAs (InnerProductSpace ℝ (WithLp 2 (B × C)))

instance [CompleteSpace B] [CompleteSpace C] : CompleteSpace (EJASum B C) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (B × C)))

variable {B C}

/-- The components. -/
def EJASum.fst (x : EJASum B C) : B := WithLp.fst (show WithLp 2 (B × C) from x)

/-- The components. -/
def EJASum.snd (x : EJASum B C) : C := WithLp.snd (show WithLp 2 (B × C) from x)

/-- An element from its components. -/
def EJASum.mk (b : B) (c : C) : EJASum B C := WithLp.toLp 2 (b, c)

@[simp] theorem EJASum.mk_fst (b : B) (c : C) : (EJASum.mk b c).fst = b := rfl
@[simp] theorem EJASum.mk_snd (b : B) (c : C) : (EJASum.mk b c).snd = c := rfl

theorem EJASum.ext {x y : EJASum B C} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := by
  exact WithLp.ofLp_injective 2 (Prod.ext h1 h2)

@[simp] theorem EJASum.add_fst (x y : EJASum B C) : (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem EJASum.add_snd (x y : EJASum B C) : (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem EJASum.smul_fst (r : ℝ) (x : EJASum B C) : (r • x).fst = r • x.fst := rfl
@[simp] theorem EJASum.smul_snd (r : ℝ) (x : EJASum B C) : (r • x).snd = r • x.snd := rfl

theorem EJASum.inner_eq (x y : EJASum B C) :
    ⟪x, y⟫_ℝ = ⟪x.fst, y.fst⟫_ℝ + ⟪x.snd, y.snd⟫_ℝ :=
  WithLp.prod_inner_apply (show WithLp 2 (B × C) from x) (show WithLp 2 (B × C) from y)

variable [Mul B] [One B] [Mul C] [One C]

noncomputable instance : Mul (EJASum B C) :=
  ⟨fun x y => EJASum.mk (x.fst * y.fst) (x.snd * y.snd)⟩

instance : One (EJASum B C) := ⟨EJASum.mk 1 1⟩

@[simp] theorem EJASum.mul_fst (x y : EJASum B C) : (x * y).fst = x.fst * y.fst := rfl
@[simp] theorem EJASum.mul_snd (x y : EJASum B C) : (x * y).snd = x.snd * y.snd := rfl
@[simp] theorem EJASum.one_fst : (1 : EJASum B C).fst = 1 := rfl
@[simp] theorem EJASum.one_snd : (1 : EJASum B C).snd = 1 := rfl

instance [CompleteSpace B] [CompleteSpace C] [PaperEJA B] [PaperEJA C] :
    PaperEJA (EJASum B C) where
  mul_comm x y := EJASum.ext (PaperEJA.mul_comm _ _) (PaperEJA.mul_comm _ _)
  mul_add x y z := EJASum.ext (PaperEJA.mul_add _ _ _) (PaperEJA.mul_add _ _ _)
  smul_mul r x y := EJASum.ext (PaperEJA.smul_mul _ _ _) (PaperEJA.smul_mul _ _ _)
  one_mul x := EJASum.ext (PaperEJA.one_mul _) (PaperEJA.one_mul _)
  jordan x y := EJASum.ext (PaperEJA.jordan _ _) (PaperEJA.jordan _ _)
  inner_mul x y z := by
    simp only [EJASum.inner_eq, EJASum.mul_fst, EJASum.mul_snd]
    rw [PaperEJA.inner_mul, PaperEJA.inner_mul (x.snd)]

end Sums

section SumIsos

variable {ι : Type u} [Fintype ι] {A A' : ι → Type u} [∀ i, NormedAddCommGroup (A i)]
  [∀ i, InnerProductSpace ℝ (A i)] [∀ i, Mul (A i)] [∀ i, One (A i)]
  [∀ i, NormedAddCommGroup (A' i)] [∀ i, InnerProductSpace ℝ (A' i)] [∀ i, Mul (A' i)]
  [∀ i, One (A' i)]

/-- Componentwise isomorphisms give an isomorphism of direct sums. -/
noncomputable def EJAIso.piCongr (f : ∀ i, EJAIso (A i) (A' i)) : EJAIso (EJAPi A) (EJAPi A') where
  toLinearEquiv :=
    { toFun := fun x => EJAPi.mk fun i => (f i).toLinearEquiv (x.proj i)
      invFun := fun y => EJAPi.mk fun i => (f i).toLinearEquiv.symm (y.proj i)
      map_add' := fun x y => EJAPi.ext fun i => by simp
      map_smul' := fun r x => EJAPi.ext fun i => by simp
      left_inv := fun x => EJAPi.ext fun i => by simp
      right_inv := fun y => EJAPi.ext fun i => by simp }
  map_mul x y := EJAPi.ext fun i => by simp [(f i).map_mul]
  map_one := EJAPi.ext fun i => by simp [(f i).map_one]

/-- Splitting a direct sum along a predicate on the index. -/
noncomputable def EJAIso.piSplit (P : ι → Prop) [DecidablePred P] :
    EJAIso (EJAPi A) (EJASum (EJAPi fun i : {i // P i} => A i)
      (EJAPi fun i : {i // ¬ P i} => A i)) where
  toLinearEquiv :=
    { toFun := fun x => EJASum.mk (EJAPi.mk fun i => x.proj i) (EJAPi.mk fun i => x.proj i)
      invFun := fun y => EJAPi.mk fun i =>
        if h : P i then y.fst.proj ⟨i, h⟩ else y.snd.proj ⟨i, h⟩
      map_add' := fun x y => EJASum.ext (EJAPi.ext fun i => by simp)
        (EJAPi.ext fun i => by simp)
      map_smul' := fun r x => EJASum.ext (EJAPi.ext fun i => by simp)
        (EJAPi.ext fun i => by simp)
      left_inv := fun x => EJAPi.ext fun i => by
        by_cases h : P i <;> simp [h]
      right_inv := fun y => EJASum.ext (EJAPi.ext fun i => by simp [i.2])
        (EJAPi.ext fun i => by simp [i.2]) }
  map_mul x y := EJASum.ext (EJAPi.ext fun i => by simp) (EJAPi.ext fun i => by simp)
  map_one := EJASum.ext (EJAPi.ext fun i => by simp) (EJAPi.ext fun i => by simp)

variable {B B' C : Type u} [NormedAddCommGroup B] [InnerProductSpace ℝ B] [Mul B] [One B]
  [NormedAddCommGroup B'] [InnerProductSpace ℝ B'] [Mul B'] [One B']
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [Mul C] [One C]

/-- An isomorphism on the second summand. -/
noncomputable def EJAIso.sumCongrRight (f : EJAIso B B') : EJAIso (EJASum C B) (EJASum C B') where
  toLinearEquiv :=
    { toFun := fun x => EJASum.mk x.fst (f.toLinearEquiv x.snd)
      invFun := fun y => EJASum.mk y.fst (f.toLinearEquiv.symm y.snd)
      map_add' := fun x y => EJASum.ext (by simp) (by simp)
      map_smul' := fun r x => EJASum.ext (by simp) (by simp)
      left_inv := fun x => EJASum.ext (by simp) (by simp)
      right_inv := fun y => EJASum.ext (by simp) (by simp) }
  map_mul x y := EJASum.ext (by simp) (by simp [f.map_mul])
  map_one := EJASum.ext (by simp) (by simp [f.map_one])

end SumIsos

/-! ### The centre and its corners -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Mul E] [One E] [PaperEJA E]

theorem central_comm {z : E} (hz : IsCentral z) (u y : E) : z * (u * y) = u * (z * y) := by
  rw [pj_mul_comm u (z * y), ← hz y u, pj_mul_comm y u]

/-- For a central idempotent `z`, `x ↦ z x` is multiplicative. -/
theorem central_idem_mul {z : E} (hz : IsCentral z) (hzz : z * z = z) (x y : E) :
    z * (x * y) = (z * x) * (z * y) := by
  rw [← hz x (z * y), ← central_comm hz x y, hz z (x * y), hzz]

variable (E) in
/-- The centre of `E`, a closed associative subalgebra. -/
def centerSub : Submodule ℝ E where
  carrier := {z | IsCentral z}
  add_mem' {z w} hz hw x y := by
    show (z + w) * (x * y) = ((z + w) * x) * y
    rw [pj_add_mul, pj_add_mul, pj_add_mul, hz x y, hw x y]
  zero_mem' x y := by
    show (0 : E) * (x * y) = ((0 : E) * x) * y
    rw [pj_zero_mul, pj_zero_mul, pj_zero_mul]
  smul_mem' r z hz x y := by
    show (r • z) * (x * y) = ((r • z) * x) * y
    rw [pj_smul_mul, pj_smul_mul, pj_smul_mul, hz x y]

theorem centerSub_isAssocSub : IsAssocSub (centerSub E) where
  closed := by
    have : (centerSub E : Set E) = ⋂ x : E, ⋂ y : E, {z : E | z * (x * y) = (z * x) * y} := by
      ext z; simp [centerSub, IsCentral]
    rw [this]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_mul_right' _) ((continuous_mul_right' y).comp
        (continuous_mul_right' x))
  one_mem x y := by
    show (1 : E) * (x * y) = ((1 : E) * x) * y
    rw [pj_one_mul, pj_one_mul]
  mul_mem z hz w hw x y := by
    show (z * w) * (x * y) = ((z * w) * x) * y
    rw [← hz w (x * y), hw x y, hz (w * x) y, hz w x]
  assoc z hz w _ v _ := (hz w v).symm

/-- The corner `{x | z * x = x}`. -/
def cornerSubm (z : E) : Submodule ℝ E := LinearMap.ker (jL z - LinearMap.id)

theorem mem_cornerSubm {z x : E} : x ∈ cornerSubm z ↔ z * x = x := by
  simp [cornerSubm, sub_eq_zero]

theorem cornerSubm_closed (z : E) : IsClosed (cornerSubm z : Set E) := by
  have : (cornerSubm z : Set E) = {x : E | z * x = x} := by ext x; simp [mem_cornerSubm]
  rw [this]
  exact isClosed_eq (continuous_mul_left' z) continuous_id

variable (E) in
/-- A central idempotent. -/
structure CentralIdem where
  val : E
  idem : val * val = val
  central : IsCentral val

/-- The corner `z E` of a central idempotent `z`, an EJA with unit `z`. -/
def Corner (c : CentralIdem E) : Type u := ↥(cornerSubm c.val)

variable {c : CentralIdem E}

noncomputable instance : NormedAddCommGroup (Corner c) :=
  inferInstanceAs (NormedAddCommGroup ↥(cornerSubm c.val))

noncomputable instance : InnerProductSpace ℝ (Corner c) :=
  inferInstanceAs (InnerProductSpace ℝ ↥(cornerSubm c.val))

instance : CompleteSpace (Corner c) := (cornerSubm_closed c.val).completeSpace_coe

/-- The underlying element. -/
def Corner.val (x : Corner c) : E := (x : ↥(cornerSubm c.val)).1

theorem Corner.mem (x : Corner c) : c.val * x.val = x.val :=
  mem_cornerSubm.mp (x : ↥(cornerSubm c.val)).2

theorem Corner.ext {x y : Corner c} (h : x.val = y.val) : x = y := Subtype.ext h

/-- An element of the corner from an element of `E` fixed by `z`. -/
def Corner.mk (x : E) (hx : c.val * x = x) : Corner c :=
  (⟨x, mem_cornerSubm.mpr hx⟩ : ↥(cornerSubm c.val))

@[simp] theorem Corner.mk_val (x : E) (hx : c.val * x = x) : (Corner.mk x hx : Corner c).val = x :=
  rfl

@[simp] theorem Corner.add_val (x y : Corner c) : (x + y).val = x.val + y.val := rfl
@[simp] theorem Corner.smul_val (r : ℝ) (x : Corner c) : (r • x).val = r • x.val := rfl
@[simp] theorem Corner.zero_val : (0 : Corner c).val = 0 := rfl

theorem Corner.inner_eq (x y : Corner c) : ⟪x, y⟫_ℝ = ⟪x.val, y.val⟫_ℝ := rfl

noncomputable instance : Mul (Corner c) :=
  ⟨fun x y => Corner.mk (x.val * y.val) (by rw [c.central, x.mem])⟩

instance : One (Corner c) := ⟨Corner.mk c.val c.idem⟩

@[simp] theorem Corner.mul_val (x y : Corner c) : (x * y).val = x.val * y.val := rfl
@[simp] theorem Corner.one_val : (1 : Corner c).val = c.val := rfl

instance : PaperEJA (Corner c) where
  mul_comm x y := Corner.ext (PaperEJA.mul_comm _ _)
  mul_add x y z := Corner.ext (PaperEJA.mul_add _ _ _)
  smul_mul r x y := Corner.ext (PaperEJA.smul_mul _ _ _)
  one_mul x := Corner.ext x.mem
  jordan x y := Corner.ext (PaperEJA.jordan _ _)
  inner_mul x y z := PaperEJA.inner_mul x.val y.val z.val

/-- An element of the corner that is central *in the corner* is central in
`E`. -/
theorem Corner.isCentral_val {w : Corner c} (hw : IsCentral w) : IsCentral w.val := by
  have hz := c.central
  -- `u ∈ z E` implies `u y = u (z y)`
  have hfix : ∀ u : E, c.val * u = u → ∀ y : E, u * y = u * (c.val * y) := by
    intro u hu y
    rw [← central_comm hz u y, hz u y, hu]
  have hmemz : ∀ y : E, c.val * (c.val * y) = c.val * y := fun y => by rw [hz, c.idem]
  intro x y
  have hwx : c.val * (w.val * x) = w.val * x := by rw [hz, w.mem]
  have h := hw (Corner.mk (c.val * x) (hmemz x)) (Corner.mk (c.val * y) (hmemz y))
  have h' := congrArg Corner.val h
  simp only [Corner.mul_val, Corner.mk_val] at h'
  rw [hfix _ w.mem, central_idem_mul hz c.idem, h', ← hfix _ w.mem x,
    ← hfix _ hwx y]

/-- If `z * w ∈ ℝ z` for every central `w` (a minimal central idempotent), the
corner `z E` is a factor. -/
theorem Corner.isFactor (hsc : ∀ w : E, IsCentral w → ∃ t : ℝ, c.val * w = t • c.val) :
    IsFactor (Corner c) := by
  intro w hw
  obtain ⟨t, ht⟩ := hsc w.val (Corner.isCentral_val hw)
  refine ⟨t, Corner.ext ?_⟩
  rw [Corner.smul_val, Corner.one_val, ← ht, w.mem]

/-- `E` is the direct sum of the corners of a family of pairwise orthogonal
central idempotents summing to `1`. -/
noncomputable def cornerDecomp {T : Finset E} (hT : IsIdemFamily T) (hsum : ∑ p ∈ T, p = 1)
    (hc : ∀ p ∈ T, IsCentral p) :
    EJAIso E (EJAPi fun p : {p // p ∈ T} => Corner (⟨p.1, hT.idem p.1 p.2, hc p.1 p.2⟩ :
      CentralIdem E)) where
  toLinearEquiv :=
    { toFun := fun x => EJAPi.mk fun p => Corner.mk (p.1 * x) (by
        rw [hc p.1 p.2, hT.idem p.1 p.2])
      invFun := fun f => ∑ p : {p // p ∈ T}, (f.proj p).val
      map_add' := fun x y => EJAPi.ext fun p => Corner.ext (by simp [pj_mul_add])
      map_smul' := fun r x => EJAPi.ext fun p => Corner.ext (by simp [pj_mul_smul])
      left_inv := fun x => by
        simp only [EJAPi.proj_mk, Corner.mk_val]
        rw [← pj_sum_mul, Finset.sum_coe_sort T (fun p => p), hsum, pj_one_mul]
      right_inv := fun f => EJAPi.ext fun q => Corner.ext (by
        simp only [EJAPi.proj_mk, Corner.mk_val]
        rw [pj_mul_sum, Finset.sum_eq_single q]
        · exact (f.proj q).mem
        · intro p _ hpq
          rw [← (f.proj p).mem, hc q.1 q.2, hT.orth q.1 q.2 p.1 p.2
            (fun h => hpq (Subtype.ext h.symm)), pj_zero_mul]
        · intro h; exact absurd (Finset.mem_univ q) h) }
  map_mul x y := EJAPi.ext fun p => Corner.ext (by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, EJAPi.proj_mk,
      Corner.mk_val, EJAPi.proj_mul, Corner.mul_val]
    exact central_idem_mul (hc p.1 p.2) (hT.idem p.1 p.2) x y)
  map_one := EJAPi.ext fun p => Corner.ext (by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, EJAPi.proj_mk,
      Corner.mk_val, EJAPi.proj_one, Corner.one_val]
    exact pj_mul_one _)

/-- A bundled EJA (a type with the structure of EJA 1). -/
structure EJABundle where
  carrier : Type u
  [ngroup : NormedAddCommGroup carrier]
  [ips : InnerProductSpace ℝ carrier]
  [complete : CompleteSpace carrier]
  [mul : Mul carrier]
  [one : One carrier]
  [eja : PaperEJA carrier]

attribute [instance] EJABundle.ngroup EJABundle.ips EJABundle.complete EJABundle.mul
  EJABundle.one EJABundle.eja

/-- A bundled real Hilbert space. -/
structure HilbBundle where
  carrier : Type u
  [ngroup : NormedAddCommGroup carrier]
  [ips : InnerProductSpace ℝ carrier]
  [complete : CompleteSpace carrier]

attribute [instance] HilbBundle.ngroup HilbBundle.ips HilbBundle.complete

/-- The classification of the (type I, finite rank) JBW factors
(Hanche-Olsen–Størmer, *Jordan operator algebras*, §6), as the print uses it
in EJA 54, specialised to EJAs (which are type I JBW-algebras of finite rank,
EJA 53): **an EJA that is a factor is finite-dimensional or (isomorphic to)
the spin factor of an infinite-dimensional Hilbert space.**  Not in Mathlib
and not formalised here; EJA 54 takes it as a hypothesis. -/
def HOSClassification : Prop :=
  ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [Mul F] [One F]
    [PaperEJA F], IsFactor F → FiniteDimensional ℝ F ∨
      ∃ H : HilbBundle.{u}, ¬ FiniteDimensional ℝ H.carrier ∧
        Nonempty (EJAIso F (SpinFactor H.carrier))

/-- **EJA 54** (`appendixjnw`, main.tex:1292, Corollary): every EJA is
isomorphic to `E_fin ⊕ E_inf`, with `E_fin` a finite-dimensional EJA and
`E_inf` a direct sum of infinite-dimensional spin factors — **given the
Hanche-Olsen–Størmer classification of factors** (`HOSClassification`,
cited by the print, not formalised).  The rest of the print's argument —
that `E` is a finite direct sum of factors — is proved: the centre is a closed
associative subalgebra, so `1` is a finite sum of minimal central idempotents
(`assocSub_decomp_min`), whose corners are factors (`Corner.isFactor`) and
decompose `E` (`cornerDecomp`). -/
theorem appendixjnw (hHOS : HOSClassification.{u}) :
    ∃ Ef : EJABundle.{u}, FiniteDimensional ℝ Ef.carrier ∧
      ∃ (ι : Type u) (_ : Fintype ι) (H : ι → HilbBundle.{u}),
        (∀ i, ¬ FiniteDimensional ℝ (H i).carrier) ∧
        Nonempty (EJAIso E (EJASum Ef.carrier (EJAPi fun i => SpinFactor (H i).carrier))) := by
  classical
  obtain ⟨T, hT, hTS, hsum, hsc, -⟩ := assocSub_decomp_min (centerSub_isAssocSub (E := E))
  have hc : ∀ p ∈ T, IsCentral p := fun p hp => hTS p hp
  let cz : {p // p ∈ T} → CentralIdem E := fun p => ⟨p.1, hT.idem p.1 p.2, hc p.1 p.2⟩
  have hfac : ∀ p : {p // p ∈ T}, IsFactor (Corner (cz p)) := fun p =>
    Corner.isFactor fun w hw => hsc p.1 p.2 w hw
  let P : {p // p ∈ T} → Prop := fun p => FiniteDimensional ℝ (Corner (cz p))
  have hspin : ∀ p : {p // ¬ P p}, ∃ H : HilbBundle.{u}, ¬ FiniteDimensional ℝ H.carrier ∧
      Nonempty (EJAIso (Corner (cz p.1)) (SpinFactor H.carrier)) := fun p =>
    (hHOS (Corner (cz p.1)) (hfac p.1)).resolve_left p.2
  choose H hHinf hHiso using hspin
  have hfin : ∀ p : {p // P p}, FiniteDimensional ℝ (Corner (cz p.1)) := fun p => p.2
  let Ef : EJABundle.{u} := ⟨EJAPi fun p : {p // P p} => Corner (cz p.1)⟩
  refine ⟨Ef, ?_, {p // ¬ P p}, inferInstance, H, hHinf, ⟨?_⟩⟩
  · show FiniteDimensional ℝ (EJAPi fun p : {p // P p} => Corner (cz p.1))
    infer_instance
  · exact ((cornerDecomp hT hsum hc).trans (EJAIso.piSplit P)).trans
      (EJAIso.sumCongrRight (EJAIso.piCongr fun p => (hHiso p).some))

end Decomposition

end Papers.EJA
