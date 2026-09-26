/-
Papers/REC/JBPeirce.lean

The **Peirce decomposition** of a Jordan algebra, as infrastructure for REC 136's structure
theory (exchangeable idempotents; the type-I₃ content of Shultz 1979 Thm 3.9).

Plan (all done, no `sorry`; purely algebraic — no norm, order, dimension or functional calculus).
* Setting: `IsJordanMul V` — a commutative, bilinear product on a real vector space with
  the Jordan identity `(ab)(aa) = a(b(aa))`; no unit.  Every `JBAlgebra` is one
  (`JBAlgebra.isJordanMul`).  A unit, when needed, is an explicit `u'` with `u' * a = a`.
  The only tool is the linearised Jordan identity (`jlin`, from Mathlib's
  `two_nsmul_lie_lmul_lmul_add_add_eq_zero`).
1. Idempotent `e`: `2L³ − 3L² + L = 0` (`peirce_cubic`); projections `P1 = 2L² − L = U_e`
   (`P1_eq_jQ`), `Ph = 4(L − L²)`, `P0 = id − 3L + 2L² = U_{u−e}` (`P0_eq_jQ`);
   `V = V₁ ⊕ V½ ⊕ V₀` (`peirce_decomp`, `peirce_unique`, `peirce_existsUnique`).
2. Peirce rules: `V₁V_j, V₀V_j ⊆ V_j` (`peirce_mul_of_ne_half`), `V₁V₀ = 0`,
   `V½V½ ⊆ V₁ + V₀` (`peirce_half_mul_half`); orthogonal idempotents have commuting `L`.
3. Symmetries: `U_{2e−u} = σ_e = id − 2P½` (`jQ_symm`), an involutive Jordan automorphism
   (`peirceRefl_mul`, no unit needed); every `s² = u` is `2e − u`, so `U_s` is an involutive
   automorphism (`jQ_mul_of_symm`, `jQ_jQ_of_symm`); `U_s p = q` carries `V_r(q)` to
   `V_r(p)` (`exch_peirce`).
4. Exchange ⟺ connecting element, for orthogonal idempotents (H-O–S 5.1.x;
   `exch_iff_connect`): `v ∈ V½(p) ∩ V½(q)`, `v² = p + q` ⟹ `s = v + (u − p − q)`
   (`connect_symm`); conversely `v = 2(P₁(f)p − P₀(f)p)`, `f = ½(u + s)` (`exch_connect`).
5. Frames: connected to one member ⟹ mutually exchangeable (`frame_exch`, via
   `U_{U_{s_j} s_i}`); `HasExchFamily V ⟺` a connected frame (`hasExchFamily_iff_connected_frame`).
6. Joint Peirce decomposition of a frame: `x = Σ P₁(e_i)x + ½ Σ_{i≠j} P½(e_i)P½(e_j)x`
   (`frame_decomp`, by induction over the frame), direct (`frame_decomp_unique`), and the
   rules `V_iiV_jj = 0`, `V_iiV_ij ⊆ V_ij`, `V_ijV_jk ⊆ V_ik`, `V_ijV_kl = 0`,
   `V_ijV_ij ⊆ V_ii + V_jj` (`frame_mul_*`).
Not here: the existence of a connected frame of size `≥ 2` in a non-zero purely exceptional
JBW-algebra (H-O–S 5.2, 7.2 / Shultz 3.9: comparison of projections, halving, type
classification), which needs the JBW order structure and the functional calculus.
-/
import Papers.REC.Rec136Hyps2

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

open Theses.B.Eff

namespace Papers.REC.JBPeirce

open Papers.REC

universe u

/-! ## The setting -/

/-- A (not necessarily unital) **Jordan algebra** over `ℝ`: a commutative bilinear product
satisfying the Jordan identity. -/
class IsJordanMul (V : Type u) [AddCommGroup V] [Module ℝ V] [Mul V] : Prop where
  mul_comm : ∀ a b : V, a * b = b * a
  add_mul : ∀ a b c : V, (a + b) * c = a * c + b * c
  smul_mul : ∀ (r : ℝ) (a b : V), (r • a) * b = r • (a * b)
  jordan : ∀ a b : V, (a * b) * (a * a) = a * (b * (a * a))

/-- Every JB-algebra (REC 44) is a Jordan algebra. -/
instance JBAlgebra.isJordanMul (A : Type u) [AddCommGroup A] [Module ℝ A] [PartialOrder A]
    [OrderUnitSpace A] [Mul A] [h : JBAlgebra A] : IsJordanMul A :=
  ⟨h.mul_comm, h.add_mul, h.smul_mul, h.jordan⟩

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [IsJordanMul V]

theorem jmul_comm (a b : V) : a * b = b * a := IsJordanMul.mul_comm a b

theorem jadd_mul (a b c : V) : (a + b) * c = a * c + b * c := IsJordanMul.add_mul a b c

theorem jmul_add (a b c : V) : a * (b + c) = a * b + a * c := by
  rw [jmul_comm, jadd_mul, jmul_comm b, jmul_comm c]

theorem jsmul_mul (r : ℝ) (a b : V) : (r • a) * b = r • (a * b) := IsJordanMul.smul_mul r a b

theorem jmul_smul (r : ℝ) (a b : V) : a * (r • b) = r • (a * b) := by
  rw [jmul_comm, jsmul_mul, jmul_comm]

theorem jzero_mul (a : V) : (0 : V) * a = 0 := by
  have h := jsmul_mul (0 : ℝ) (0 : V) a
  rwa [zero_smul, zero_smul] at h

theorem jmul_zero (a : V) : a * (0 : V) = 0 := by rw [jmul_comm, jzero_mul]

theorem jneg_mul (a b : V) : (-a) * b = -(a * b) := by
  rw [← neg_one_smul ℝ a, jsmul_mul, neg_one_smul]

theorem jmul_neg (a b : V) : a * (-b) = -(a * b) := by rw [jmul_comm, jneg_mul, jmul_comm]

theorem jsub_mul (a b c : V) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg, jadd_mul, jneg_mul, ← sub_eq_add_neg]

theorem jmul_sub (a b c : V) : a * (b - c) = a * b - a * c := by
  rw [jmul_comm, jsub_mul, jmul_comm b, jmul_comm c]

theorem jsum_mul {ι : Type*} (s : Finset ι) (f : ι → V) (c : V) :
    (∑ i ∈ s, f i) * c = ∑ i ∈ s, f i * c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jzero_mul]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, jadd_mul, ih]

theorem jmul_sum {ι : Type*} (s : Finset ι) (f : ι → V) (c : V) :
    c * (∑ i ∈ s, f i) = ∑ i ∈ s, c * f i := by
  rw [jmul_comm, jsum_mul]; simp only [jmul_comm c]

/-- The commutative non-associative ring structure, used only to borrow Mathlib's
linearisation of the Jordan identity. -/
def jRing (W : Type u) [AddCommGroup W] [Module ℝ W] [Mul W] [IsJordanMul W] :
    NonUnitalNonAssocCommRing W :=
  { (inferInstance : AddCommGroup W), (inferInstance : Mul W) with
    left_distrib := jmul_add
    right_distrib := jadd_mul
    zero_mul := jzero_mul
    mul_zero := jmul_zero
    mul_comm := jmul_comm }

theorem two_nsmul_jlin_aux {W : Type u} [NonUnitalNonAssocCommRing W] [IsCommJordan W]
    (a b c w : W) :
    (2 : ℕ) • (a * (b * c * w) - b * c * (a * w) + (b * (c * a * w) - c * a * (b * w))
      + (c * (a * b * w) - a * b * (c * w))) = 0 :=
  congrArg (fun f : AddMonoid.End W => f w) (two_nsmul_lie_lmul_lmul_add_add_eq_zero a b c)

/-- **The linearised Jordan identity** `[L_a, L_{bc}] + [L_b, L_{ca}] + [L_c, L_{ab}] = 0`,
applied to `w`. -/
theorem jlin (a b c w : V) :
    a * (b * c * w) - b * c * (a * w) + (b * (c * a * w) - c * a * (b * w))
      + (c * (a * b * w) - a * b * (c * w)) = 0 := by
  have hj : ∀ x y : V, x * y * (x * x) = x * (y * (x * x)) := IsJordanMul.jordan
  have h2 : ((2 : ℕ) : ℝ) • (a * (b * c * w) - b * c * (a * w) + (b * (c * a * w)
      - c * a * (b * w)) + (c * (a * b * w) - a * b * (c * w))) = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    let _inst := jRing V
    have _inst2 : IsCommJordan V := ⟨hj⟩
    exact two_nsmul_jlin_aux a b c w
  rcases smul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact h3

/-! ## 1. The Peirce decomposition of an idempotent -/

section Peirce

variable {e : V}

/-- **The Peirce relation** `2 L_e³ − 3 L_e² + L_e = 0` for an idempotent `e`
(the linearised Jordan identity at `(e, e, x; e)`). -/
theorem peirce_cubic (he : e * e = e) (x : V) :
    (2 : ℝ) • (e * (e * (e * x))) - (3 : ℝ) • (e * (e * x)) + e * x = 0 := by
  have h := jlin e e x e
  simp only [he, jmul_comm x e, jmul_comm (e * x) e] at h
  linear_combination (norm := module) h

/-- The Peirce space `V_r(e) = {x | e x = r x}`. -/
def peirce (e : V) (r : ℝ) : Submodule ℝ V where
  carrier := {x | e * x = r • x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at *
    rw [jmul_add, hx, hy, smul_add]
  zero_mem' := by simp [jmul_zero]
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at *
    rw [jmul_smul, hx, smul_comm]

theorem mem_peirce {r : ℝ} {x : V} : x ∈ peirce e r ↔ e * x = r • x := Iff.rfl

/-- The projection onto `V₁(e)`: `P₁ = 2 L_e² − L_e`. -/
def P1 (e : V) : V →ₗ[ℝ] V where
  toFun x := (2 : ℝ) • (e * (e * x)) - e * x
  map_add' x y := by simp only [jmul_add]; module
  map_smul' c x := by simp only [jmul_smul, RingHom.id_apply]; module

/-- The projection onto `V½(e)`: `P½ = 4 L_e − 4 L_e²`. -/
def Ph (e : V) : V →ₗ[ℝ] V where
  toFun x := (4 : ℝ) • (e * x) - (4 : ℝ) • (e * (e * x))
  map_add' x y := by simp only [jmul_add]; module
  map_smul' c x := by simp only [jmul_smul, RingHom.id_apply]; module

/-- The projection onto `V₀(e)`: `P₀ = id − 3 L_e + 2 L_e²`. -/
def P0 (e : V) : V →ₗ[ℝ] V where
  toFun x := x - (3 : ℝ) • (e * x) + (2 : ℝ) • (e * (e * x))
  map_add' x y := by simp only [jmul_add]; module
  map_smul' c x := by simp only [jmul_smul, RingHom.id_apply]; module

theorem P1_apply (e x : V) : P1 e x = (2 : ℝ) • (e * (e * x)) - e * x := rfl
theorem Ph_apply (e x : V) : Ph e x = (4 : ℝ) • (e * x) - (4 : ℝ) • (e * (e * x)) := rfl
theorem P0_apply (e x : V) : P0 e x = x - (3 : ℝ) • (e * x) + (2 : ℝ) • (e * (e * x)) := rfl

/-- `x = P₁ x + P½ x + P₀ x`. -/
theorem peirce_decomp (e x : V) : P1 e x + Ph e x + P0 e x = x := by
  simp only [P1_apply, Ph_apply, P0_apply]; module

theorem P1_mem (he : e * e = e) (x : V) : P1 e x ∈ peirce e 1 := by
  have h := peirce_cubic he x
  rw [mem_peirce, P1_apply, jmul_sub, jmul_smul]
  linear_combination (norm := module) h

theorem Ph_mem (he : e * e = e) (x : V) : Ph e x ∈ peirce e (1 / 2) := by
  have h := peirce_cubic he x
  rw [mem_peirce, Ph_apply, jmul_sub, jmul_smul, jmul_smul]
  linear_combination (norm := module) (-2 : ℝ) • h

theorem P0_mem (he : e * e = e) (x : V) : P0 e x ∈ peirce e 0 := by
  have h := peirce_cubic he x
  rw [mem_peirce, P0_apply, jmul_add, jmul_sub, jmul_smul, jmul_smul]
  linear_combination (norm := module) h

/-- The projections act on a Peirce eigenvector by the obvious scalars. -/
theorem P1_of_mem {r : ℝ} {x : V} (hx : x ∈ peirce e r) : P1 e x = (2 * r * r - r) • x := by
  rw [mem_peirce] at hx; rw [P1_apply, hx, jmul_smul, hx]; module

theorem Ph_of_mem {r : ℝ} {x : V} (hx : x ∈ peirce e r) :
    Ph e x = (4 * r - 4 * r * r) • x := by
  rw [mem_peirce] at hx; rw [Ph_apply, hx, jmul_smul, hx]; module

theorem P0_of_mem {r : ℝ} {x : V} (hx : x ∈ peirce e r) :
    P0 e x = (1 - 3 * r + 2 * r * r) • x := by
  rw [mem_peirce] at hx; rw [P0_apply, hx, jmul_smul, hx]; module

theorem P1_of_mem1 {x : V} (hx : x ∈ peirce e 1) : P1 e x = x := by
  rw [P1_of_mem hx]; norm_num
theorem P1_of_memh {x : V} (hx : x ∈ peirce e (1 / 2)) : P1 e x = 0 := by
  rw [P1_of_mem hx]; norm_num
theorem P1_of_mem0 {x : V} (hx : x ∈ peirce e 0) : P1 e x = 0 := by
  rw [P1_of_mem hx]; norm_num
theorem Ph_of_mem1 {x : V} (hx : x ∈ peirce e 1) : Ph e x = 0 := by
  rw [Ph_of_mem hx]; norm_num
theorem Ph_of_memh {x : V} (hx : x ∈ peirce e (1 / 2)) : Ph e x = x := by
  rw [Ph_of_mem hx]; norm_num
theorem Ph_of_mem0 {x : V} (hx : x ∈ peirce e 0) : Ph e x = 0 := by
  rw [Ph_of_mem hx]; norm_num
theorem P0_of_mem1 {x : V} (hx : x ∈ peirce e 1) : P0 e x = 0 := by
  rw [P0_of_mem hx]; norm_num
theorem P0_of_memh {x : V} (hx : x ∈ peirce e (1 / 2)) : P0 e x = 0 := by
  rw [P0_of_mem hx]; norm_num
theorem P0_of_mem0 {x : V} (hx : x ∈ peirce e 0) : P0 e x = x := by
  rw [P0_of_mem hx]; norm_num

/-- **The Peirce decomposition is direct.** -/
theorem peirce_unique {x₁ xh x₀ : V} (h1 : x₁ ∈ peirce e 1) (hh : xh ∈ peirce e (1 / 2))
    (h0 : x₀ ∈ peirce e 0) (h : x₁ + xh + x₀ = 0) : x₁ = 0 ∧ xh = 0 ∧ x₀ = 0 := by
  have a1 := congrArg (P1 e) h
  have ah := congrArg (Ph e) h
  have a0 := congrArg (P0 e) h
  simp only [map_add, map_zero, P1_of_mem1 h1, P1_of_memh hh, P1_of_mem0 h0, Ph_of_mem1 h1,
    Ph_of_memh hh, Ph_of_mem0 h0, P0_of_mem1 h1, P0_of_memh hh, P0_of_mem0 h0,
    add_zero, zero_add] at a1 ah a0
  exact ⟨a1, ah, a0⟩

/-- **The Peirce decomposition** `V = V₁(e) ⊕ V½(e) ⊕ V₀(e)`, with the projections
polynomials in `L_e`. -/
theorem peirce_existsUnique (he : e * e = e) (x : V) :
    ∃! t : V × V × V, t.1 ∈ peirce e 1 ∧ t.2.1 ∈ peirce e (1 / 2) ∧ t.2.2 ∈ peirce e 0 ∧
      t.1 + t.2.1 + t.2.2 = x := by
  refine ⟨(P1 e x, Ph e x, P0 e x), ⟨P1_mem he x, Ph_mem he x, P0_mem he x,
    peirce_decomp e x⟩, ?_⟩
  rintro ⟨a, b, c⟩ ⟨ha, hb, hc, hs⟩
  have hs' : (a - P1 e x) + (b - Ph e x) + (c - P0 e x) = 0 := by
    rw [← peirce_decomp e x] at hs
    linear_combination (norm := module) hs
  obtain ⟨h1, h2, h3⟩ := peirce_unique (Submodule.sub_mem _ ha (P1_mem he x))
    (Submodule.sub_mem _ hb (Ph_mem he x)) (Submodule.sub_mem _ hc (P0_mem he x)) hs'
  simp only [Prod.mk.injEq]
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2, sub_eq_zero.mp h3⟩

/-- The three Peirce spaces span `V` and are independent. -/
theorem peirce_sup_eq_top (he : e * e = e) :
    peirce e 1 ⊔ peirce e (1 / 2) ⊔ peirce e 0 = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  rw [← peirce_decomp e x]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left
    (Submodule.mem_sup_left (P1_mem he x))) (Submodule.mem_sup_left
    (Submodule.mem_sup_right (Ph_mem he x)))) (Submodule.mem_sup_right (P0_mem he x))

theorem P1_idem (he : e * e = e) (x : V) : P1 e (P1 e x) = P1 e x := P1_of_mem1 (P1_mem he x)
theorem Ph_idem (he : e * e = e) (x : V) : Ph e (Ph e x) = Ph e x := Ph_of_memh (Ph_mem he x)
theorem P0_idem (he : e * e = e) (x : V) : P0 e (P0 e x) = P0 e x := P0_of_mem0 (P0_mem he x)

/-- `P₁ = U_e`. -/
theorem P1_eq_jQ (he : e * e = e) (x : V) : P1 e x = jQ e x := by
  rw [P1_apply, jQ, he]

/-- With a unit `u`, `P₀ = U_{u − e}`, and `u − e` is an idempotent. -/
theorem one_sub_idem {u' : V} (hu : ∀ a : V, u' * a = a) (he : e * e = e) :
    (u' - e) * (u' - e) = u' - e := by
  rw [jsub_mul, jmul_sub, jmul_sub, hu, hu, he, jmul_comm e u', hu]; abel

theorem P0_eq_jQ {u' : V} (hu : ∀ a : V, u' * a = a) (he : e * e = e) (x : V) :
    P0 e x = jQ (u' - e) x := by
  rw [P0_apply, jQ, one_sub_idem hu he]
  simp only [jsub_mul, jmul_sub, hu]
  module

theorem peirce_one_sub {u' : V} (hu : ∀ a : V, u' * a = a) {r : ℝ} {x : V} :
    x ∈ peirce (u' - e) r ↔ x ∈ peirce e (1 - r) := by
  simp only [mem_peirce, jsub_mul, hu]
  constructor <;> intro h <;> linear_combination (norm := module) -h

end Peirce

/-! ## 2. The Peirce multiplication rules -/

section Rules

variable {e : V}

/-- The key instance of the linearised identity: for `x ∈ V_i(e)`, `y ∈ V_j(e)`,
`(2i − 1) e(xy) = (2i − 1) j (xy)`. -/
theorem peirce_mul_aux (he : e * e = e) {i j : ℝ} {x y : V} (hx : x ∈ peirce e i)
    (hy : y ∈ peirce e j) : (2 * i - 1) • (e * (x * y)) = ((2 * i - 1) * j) • (x * y) := by
  rw [mem_peirce] at hx hy
  have h := jlin e e x y
  have hx' : x * e = i • x := by rw [jmul_comm]; exact hx
  simp only [hx, hx', hy, he, jsmul_mul, jmul_smul] at h
  linear_combination (norm := module) h

/-- **Peirce rule**: for `i ≠ ½`, `V_i(e) V_j(e) ⊆ V_j(e)`; in particular `V₁V₁ ⊆ V₁`,
`V₀V₀ ⊆ V₀`, `V₁V½, V₀V½ ⊆ V½`. -/
theorem peirce_mul_of_ne_half (he : e * e = e) {i j : ℝ} (hi : i ≠ 1 / 2) {x y : V}
    (hx : x ∈ peirce e i) (hy : y ∈ peirce e j) : x * y ∈ peirce e j := by
  have h := peirce_mul_aux he hx hy
  have hi' : (2 * i - 1) ≠ 0 := by
    intro h0; apply hi; linarith
  rw [mem_peirce]
  calc e * (x * y) = (2 * i - 1)⁻¹ • ((2 * i - 1) • (e * (x * y))) := by
        rw [_root_.smul_smul, inv_mul_cancel₀ hi', one_smul]
    _ = j • (x * y) := by rw [h, _root_.smul_smul, ← mul_assoc, inv_mul_cancel₀ hi', one_mul]

theorem peirce_one_mul_one (he : e * e = e) {x y : V} (hx : x ∈ peirce e 1)
    (hy : y ∈ peirce e 1) : x * y ∈ peirce e 1 := peirce_mul_of_ne_half he (by norm_num) hx hy

theorem peirce_zero_mul_zero (he : e * e = e) {x y : V} (hx : x ∈ peirce e 0)
    (hy : y ∈ peirce e 0) : x * y ∈ peirce e 0 := peirce_mul_of_ne_half he (by norm_num) hx hy

theorem peirce_one_mul_half (he : e * e = e) {x y : V} (hx : x ∈ peirce e 1)
    (hy : y ∈ peirce e (1 / 2)) : x * y ∈ peirce e (1 / 2) :=
  peirce_mul_of_ne_half he (by norm_num) hx hy

theorem peirce_zero_mul_half (he : e * e = e) {x y : V} (hx : x ∈ peirce e 0)
    (hy : y ∈ peirce e (1 / 2)) : x * y ∈ peirce e (1 / 2) :=
  peirce_mul_of_ne_half he (by norm_num) hx hy

/-- **Peirce rule** `V₁(e) V₀(e) = 0`. -/
theorem peirce_one_mul_zero (he : e * e = e) {x y : V} (hx : x ∈ peirce e 1)
    (hy : y ∈ peirce e 0) : x * y = 0 := by
  have h1 := peirce_mul_of_ne_half he (by norm_num) hx hy
  have h2 := peirce_mul_of_ne_half he (by norm_num) hy hx
  rw [mem_peirce, jmul_comm y x] at h2
  rw [mem_peirce, h2, zero_smul] at h1
  rw [one_smul] at h1
  exact h1

/-- The square of a `½`-element has no `½`-part: `e(e(z²)) = e(z²)`
(the linearised identity at `(e, z, z; e)`). -/
theorem peirce_half_sq (he : e * e = e) {z : V} (hz : z ∈ peirce e (1 / 2)) :
    e * (e * (z * z)) = e * (z * z) := by
  rw [mem_peirce] at hz
  have h := jlin e z z e
  have e1 : z * z * e = e * (z * z) := jmul_comm _ _
  have e2 : z * e = (1 / 2 : ℝ) • z := by rw [jmul_comm]; exact hz
  simp only [e1, e2, hz, he, jsmul_mul, jmul_smul] at h
  linear_combination (norm := module) h

/-- **Peirce rule** `V½(e) V½(e) ⊆ V₁(e) + V₀(e)`: the `½`-part of a product of two
`½`-elements vanishes. -/
theorem peirce_half_mul_half (he : e * e = e) {x y : V} (hx : x ∈ peirce e (1 / 2))
    (hy : y ∈ peirce e (1 / 2)) : Ph e (x * y) = 0 := by
  have hxy := peirce_half_sq he (Submodule.add_mem _ hx hy)
  have hxx := peirce_half_sq he hx
  have hyy := peirce_half_sq he hy
  have hc : y * x = x * y := jmul_comm _ _
  simp only [jadd_mul, jmul_add, hc] at hxy
  rw [Ph_apply]
  linear_combination (norm := module) (-2 : ℝ) • (hxy - hxx - hyy)

theorem peirce_half_mul_half_eq (he : e * e = e) {x y : V} (hx : x ∈ peirce e (1 / 2))
    (hy : y ∈ peirce e (1 / 2)) : x * y = P1 e (x * y) + P0 e (x * y) := by
  have := peirce_decomp e (x * y)
  rw [peirce_half_mul_half he hx hy, add_zero] at this
  exact this.symm

/-- Orthogonal idempotents: `e f = 0` puts `f` in `V₀(e)`. -/
theorem mem_peirce_zero_of_orth {f : V} (hef : e * f = 0) : f ∈ peirce e 0 := by
  rw [mem_peirce, hef, zero_smul]

/-- Orthogonal idempotents have commuting multiplication operators. -/
theorem orth_commute (he : e * e = e) {f : V} (hef : e * f = 0) (x : V) :
    e * (f * x) = f * (e * x) := by
  have h := jlin e e f x
  have hfe : f * e = 0 := by rw [jmul_comm]; exact hef
  simp only [hef, hfe, he, jzero_mul, jmul_zero] at h
  linear_combination (norm := module) -h

end Rules

/-! ## 3. Symmetries and the Peirce automorphism -/

section Symmetry

variable {e : V}

/-- The **Peirce reflection** `σ_e = P₁ − P½ + P₀ = id − 2 P½` of an idempotent. -/
def peirceRefl (e : V) : V →ₗ[ℝ] V := LinearMap.id - (2 : ℝ) • Ph e

theorem peirceRefl_apply (e x : V) : peirceRefl e x = x - (2 : ℝ) • Ph e x := rfl

/-- The multiplicativity of `σ_e`, on Peirce components. -/
theorem peirceRefl_mul_aux (he : e * e = e) {x₁ xh x₀ y₁ yh y₀ : V}
    (hx₁ : x₁ ∈ peirce e 1) (hxh : xh ∈ peirce e (1 / 2)) (hx₀ : x₀ ∈ peirce e 0)
    (hy₁ : y₁ ∈ peirce e 1) (hyh : yh ∈ peirce e (1 / 2)) (hy₀ : y₀ ∈ peirce e 0) :
    peirceRefl e ((x₁ + xh + x₀) * (y₁ + yh + y₀))
      = peirceRefl e (x₁ + xh + x₀) * peirceRefl e (y₁ + yh + y₀) := by
  have hX : peirceRefl e (x₁ + xh + x₀) = x₁ - xh + x₀ := by
    rw [peirceRefl_apply, map_add, map_add, Ph_of_mem1 hx₁, Ph_of_memh hxh, Ph_of_mem0 hx₀]
    module
  have hY : peirceRefl e (y₁ + yh + y₀) = y₁ - yh + y₀ := by
    rw [peirceRefl_apply, map_add, map_add, Ph_of_mem1 hy₁, Ph_of_memh hyh, Ph_of_mem0 hy₀]
    module
  have a11 := Ph_of_mem1 (peirce_one_mul_one he hx₁ hy₁)
  have a1h := Ph_of_memh (peirce_one_mul_half he hx₁ hyh)
  have a10 := peirce_one_mul_zero he hx₁ hy₀
  have ah1 : Ph e (xh * y₁) = xh * y₁ := by
    rw [jmul_comm]; exact Ph_of_memh (peirce_one_mul_half he hy₁ hxh)
  have ahh := peirce_half_mul_half he hxh hyh
  have ah0 : Ph e (xh * y₀) = xh * y₀ := by
    rw [jmul_comm]; exact Ph_of_memh (peirce_zero_mul_half he hy₀ hxh)
  have a01 : x₀ * y₁ = 0 := by rw [jmul_comm]; exact peirce_one_mul_zero he hy₁ hx₀
  have a0h := Ph_of_memh (peirce_zero_mul_half he hx₀ hyh)
  have a00 := Ph_of_mem0 (peirce_zero_mul_zero he hx₀ hy₀)
  rw [hX, hY, peirceRefl_apply]
  simp only [jadd_mul, jmul_add, jsub_mul, jmul_sub, map_add, a10, a01, map_zero, a11, a1h,
    ah1, ahh, ah0, a0h, a00]
  module

/-- **The Peirce reflection is a Jordan automorphism**: `σ_e (x y) = σ_e x · σ_e y`
(no unit needed). -/
theorem peirceRefl_mul (he : e * e = e) (x y : V) :
    peirceRefl e (x * y) = peirceRefl e x * peirceRefl e y := by
  have h := peirceRefl_mul_aux he (P1_mem he x) (Ph_mem he x) (P0_mem he x) (P1_mem he y)
    (Ph_mem he y) (P0_mem he y)
  rwa [peirce_decomp, peirce_decomp] at h

/-- `σ_e` is an involution. -/
theorem peirceRefl_peirceRefl (he : e * e = e) (x : V) : peirceRefl e (peirceRefl e x) = x := by
  rw [peirceRefl_apply, peirceRefl_apply, map_sub, map_smul, Ph_idem he]
  module

theorem peirceRefl_bijective (he : e * e = e) : Function.Bijective (peirceRefl e) :=
  Function.Involutive.bijective (peirceRefl_peirceRefl he)

variable {u' : V}

theorem unit_mul_self (hu : ∀ a : V, u' * a = a) : u' * u' = u' := hu u'

theorem mul_unit (hu : ∀ a : V, u' * a = a) (a : V) : a * u' = a := by rw [jmul_comm, hu]

theorem jQ_unit (hu : ∀ a : V, u' * a = a) (x : V) : jQ u' x = x := by
  simp only [jQ, hu]; module

theorem jQ_apply_unit (a : V) (hu : ∀ a : V, u' * a = a) : jQ a u' = a * a := by
  rw [jQ, mul_unit hu, mul_unit hu]; module

/-- The unit has no `½`-part. -/
theorem Ph_unit (hu : ∀ a : V, u' * a = a) (he : e * e = e) : Ph e u' = 0 := by
  rw [Ph_apply, mul_unit hu, he, sub_self]

theorem peirceRefl_unit (hu : ∀ a : V, u' * a = a) (he : e * e = e) : peirceRefl e u' = u' := by
  rw [peirceRefl_apply, Ph_unit hu he, smul_zero, sub_zero]

/-- The symmetry `s = 2e − u` of an idempotent: `s² = u`. -/
theorem symm_sq (hu : ∀ a : V, u' * a = a) (he : e * e = e) :
    ((2 : ℝ) • e - u') * ((2 : ℝ) • e - u') = u' := by
  simp only [jsub_mul, jmul_sub, jsmul_mul, jmul_smul, he, hu, mul_unit hu]
  module

/-- `U_{2e−u} = σ_e = id − 2 P½(e)`. -/
theorem jQ_symm (hu : ∀ a : V, u' * a = a) (he : e * e = e) (x : V) :
    jQ ((2 : ℝ) • e - u') x = peirceRefl e x := by
  rw [jQ, symm_sq hu he, hu, peirceRefl_apply, Ph_apply]
  simp only [jsub_mul, jmul_sub, jsmul_mul, jmul_smul, hu]
  module

/-- Every symmetry is `2e − u` for the idempotent `e = ½(u + s)`. -/
theorem symm_repr (hu : ∀ a : V, u' * a = a) {s : V} (hs : s * s = u') :
    ((1 / 2 : ℝ) • (u' + s)) * ((1 / 2 : ℝ) • (u' + s)) = (1 / 2 : ℝ) • (u' + s) ∧
      s = (2 : ℝ) • ((1 / 2 : ℝ) • (u' + s)) - u' := by
  refine ⟨?_, by module⟩
  simp only [jsmul_mul, jmul_smul, jadd_mul, jmul_add, hu, mul_unit hu, hs]
  module

/-- For a symmetry `s`, `U_s = σ_f` with `f = ½(u + s)` idempotent. -/
theorem symm_refl (hu : ∀ a : V, u' * a = a) {s : V} (hs : s * s = u') :
    ∃ f : V, f * f = f ∧ ∀ x, jQ s x = peirceRefl f x := by
  obtain ⟨hf, hsf⟩ := symm_repr hu hs
  refine ⟨_, hf, fun x => ?_⟩
  conv_lhs => rw [hsf]
  exact jQ_symm hu hf x

/-- **`U_s` is a Jordan automorphism for every symmetry `s`** (`s² = u`). -/
theorem jQ_mul_of_symm (hu : ∀ a : V, u' * a = a) {s : V} (hs : s * s = u') (x y : V) :
    jQ s (x * y) = jQ s x * jQ s y := by
  obtain ⟨hf, hsf⟩ := symm_repr hu hs
  rw [hsf, jQ_symm hu hf, jQ_symm hu hf, jQ_symm hu hf]
  exact peirceRefl_mul hf x y

/-- `U_s` is an involution for every symmetry `s`. -/
theorem jQ_jQ_of_symm (hu : ∀ a : V, u' * a = a) {s : V} (hs : s * s = u') (x : V) :
    jQ s (jQ s x) = x := by
  obtain ⟨hf, hsf⟩ := symm_repr hu hs
  rw [hsf, jQ_symm hu hf, jQ_symm hu hf]
  exact peirceRefl_peirceRefl hf x

theorem jQ_add (a x y : V) : jQ a (x + y) = jQ a x + jQ a y := by
  simp only [jQ, jmul_add]; module

theorem jQ_smul (a : V) (r : ℝ) (x : V) : jQ a (r • x) = r • jQ a x := by
  simp only [jQ, jmul_smul]; module

/-- A multiplicative map conjugates the quadratic representation:
`φ (U_a b) = U_{φ a} (φ b)`. -/
theorem map_jQ (φ : V →ₗ[ℝ] V) (hφ : ∀ x y, φ (x * y) = φ x * φ y) (a b : V) :
    φ (jQ a b) = jQ (φ a) (φ b) := by
  simp only [jQ, map_sub, map_smul, hφ]

/-- A multiplicative map sends Peirce spaces of `p` into Peirce spaces of `φ p`. -/
theorem map_mem_peirce (φ : V →ₗ[ℝ] V) (hφ : ∀ x y, φ (x * y) = φ x * φ y) {p x : V} {r : ℝ}
    (hx : x ∈ peirce p r) : φ x ∈ peirce (φ p) r := by
  rw [mem_peirce] at hx ⊢; rw [← hφ, hx, map_smul]

/-- **Exchangeability and Peirce spaces**: if `U_s p = q` for a symmetry `s`, then `U_s`
maps `V_r(p)` onto `V_r(q)` for each `r`, and `U_s q = p`. -/
theorem exch_peirce (hu : ∀ a : V, u' * a = a) {s p q : V} (hs : s * s = u')
    (hpq : jQ s p = q) (r : ℝ) (x : V) : x ∈ peirce q r ↔ jQ s x ∈ peirce p r := by
  let φ : V →ₗ[ℝ] V := { toFun := jQ s, map_add' := jQ_add s, map_smul' := jQ_smul s }
  have hφ : ∀ x y, φ (x * y) = φ x * φ y := jQ_mul_of_symm hu hs
  have hqp : jQ s q = p := by rw [← hpq, jQ_jQ_of_symm hu hs]
  constructor
  · intro hx
    have := map_mem_peirce φ hφ hx
    simpa [φ, hqp] using this
  · intro hx
    have := map_mem_peirce φ hφ hx
    simpa [φ, hpq, jQ_jQ_of_symm hu hs] using this

theorem exch_symm (hu : ∀ a : V, u' * a = a) {s p q : V} (hs : s * s = u')
    (hpq : jQ s p = q) : jQ s q = p := by rw [← hpq, jQ_jQ_of_symm hu hs]

end Symmetry

/-! ## 4. Exchange by a connecting element -/

section Connect

variable {u' : V}

theorem add_idem_of_orth {p q : V} (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) :
    (p + q) * (p + q) = p + q := by
  rw [jadd_mul, jmul_add, jmul_add, hp, hq, hpq, jmul_comm q p, hpq]; abel

/-- An element of `V½(p) ∩ V½(q)`, `p ⊥ q`, lies in `V₁(p + q)`. -/
theorem mem_peirce_one_add {p q v : V} (hvp : v ∈ peirce p (1 / 2)) (hvq : v ∈ peirce q (1 / 2)) :
    v ∈ peirce (p + q) 1 := by
  rw [mem_peirce] at *; rw [jadd_mul, hvp, hvq]; module

/-- **The connecting-element symmetry** (Hanche-Olsen–Størmer §5.1, the algebraic half of
5.1.x/5.2.x): for orthogonal idempotents `p, q` and `v ∈ V½(p) ∩ V½(q)` with `v² = p + q`,
`s = v + (u − p − q)` is a symmetry with `U_s p = q`. -/
theorem connect_symm (hu : ∀ a : V, u' * a = a) {p q v : V} (hp : p * p = p) (hq : q * q = q)
    (hpq : p * q = 0) (hvp : p * v = (1 / 2 : ℝ) • v) (hvq : q * v = (1 / 2 : ℝ) • v)
    (hvv : v * v = p + q) :
    (v + (u' - p - q)) * (v + (u' - p - q)) = u' ∧ jQ (v + (u' - p - q)) p = q := by
  have hqp : q * p = 0 := by rw [jmul_comm]; exact hpq
  have hv1 : v * u' = v := mul_unit hu v
  have hvp' : v * p = (1 / 2 : ℝ) • v := by rw [jmul_comm]; exact hvp
  have hvq' : v * q = (1 / 2 : ℝ) • v := by rw [jmul_comm]; exact hvq
  have hpu : p * u' = p := mul_unit hu p
  have hqu : q * u' = q := mul_unit hu q
  constructor
  · simp only [jadd_mul, jmul_add, jsub_mul, jmul_sub, hu, hv1, hvp, hvq, hvp', hvq', hpu, hqu,
      hp, hq, hpq, hqp, hvv]
    module
  · have h1 : (v + (u' - p - q)) * p = (1 / 2 : ℝ) • v := by
      simp only [jadd_mul, jsub_mul, hu, hvp', hp, hqp]; module
    have h2 : (v + (u' - p - q)) * v = p + q := by
      simp only [jadd_mul, jsub_mul, hu, hvv, hvp, hvq]; module
    have hss : (v + (u' - p - q)) * (v + (u' - p - q)) = u' := by
      simp only [jadd_mul, jmul_add, jsub_mul, jmul_sub, hu, hv1, hvp, hvq, hvp', hvq', hpu, hqu,
        hp, hq, hpq, hqp, hvv]
      module
    rw [jQ, h1, jmul_smul, h2, hss, hu]
    module

/-- The connecting-element symmetry fixes every `g` with `p g = q g = 0`. -/
theorem connect_fix (hu : ∀ a : V, u' * a = a) {p q v g : V} (hp : p * p = p) (hq : q * q = q)
    (hpq : p * q = 0) (hvp : p * v = (1 / 2 : ℝ) • v) (hvq : q * v = (1 / 2 : ℝ) • v)
    (hvv : v * v = p + q) (hgp : p * g = 0) (hgq : q * g = 0) :
    jQ (v + (u' - p - q)) g = g := by
  have hvg : v * g = 0 := by
    have h1 : v ∈ peirce (p + q) 1 := mem_peirce_one_add hvp hvq
    have h0 : g ∈ peirce (p + q) 0 := by rw [mem_peirce, jadd_mul, hgp, hgq]; module
    exact peirce_one_mul_zero (add_idem_of_orth hp hq hpq) h1 h0
  have hs := (connect_symm hu hp hq hpq hvp hvq hvv).1
  have h1 : (v + (u' - p - q)) * g = g := by
    simp only [jadd_mul, jsub_mul, hu, hvg, hgp, hgq]; module
  rw [jQ, h1, h1, hs, hu]; module

end Connect

/-! ## 4′. The converse: exchangeable orthogonal idempotents are connected -/

section Converse

variable {u' : V}

theorem mem_peirce_one_of_mul {e y : V} (hy : e * y = y) : y ∈ peirce e 1 := by
  rw [mem_peirce, one_smul]; exact hy

/-- If `y ∈ V₁(f)` and `y ∈ V½(f)` then `y = 0`. -/
theorem eq_zero_of_mem_one_half {f y : V} (h1 : f * y = y) (hh : f * y = (1 / 2 : ℝ) • y) :
    y = 0 := by
  have : (1 / 2 : ℝ) • y = 0 := by linear_combination (norm := module) h1.symm.trans hh
  rcases smul_eq_zero.mp this with h | h
  · norm_num at h
  · exact h

/-- The core of `exch_connect`, on the Peirce components `p = p₁ + x + p₀` of `p` for the
idempotent `f` of the symmetry (`q = p₁ − x + p₀`). -/
theorem exch_connect_aux (hu : ∀ a : V, u' * a = a) {f p₁ x p₀ : V} (hf : f * f = f)
    (h1 : p₁ ∈ peirce f 1) (hh : x ∈ peirce f (1 / 2)) (h0 : p₀ ∈ peirce f 0)
    (hp : (p₁ + x + p₀) * (p₁ + x + p₀) = p₁ + x + p₀)
    (hpq : (p₁ + x + p₀) * (p₁ - x + p₀) = 0) :
    (p₁ + x + p₀) * ((2 : ℝ) • p₁ - (2 : ℝ) • p₀)
        = (1 / 2 : ℝ) • ((2 : ℝ) • p₁ - (2 : ℝ) • p₀) ∧
      (p₁ - x + p₀) * ((2 : ℝ) • p₁ - (2 : ℝ) • p₀)
        = (1 / 2 : ℝ) • ((2 : ℝ) • p₁ - (2 : ℝ) • p₀) ∧
      ((2 : ℝ) • p₁ - (2 : ℝ) • p₀) * ((2 : ℝ) • p₁ - (2 : ℝ) • p₀)
        = (p₁ + x + p₀) + (p₁ - x + p₀) := by
  have m10 : p₁ * p₀ = 0 := peirce_one_mul_zero hf h1 h0
  have m01 : p₀ * p₁ = 0 := by rw [jmul_comm]; exact m10
  have cx1 : x * p₁ = p₁ * x := jmul_comm _ _
  have cx0 : x * p₀ = p₀ * x := jmul_comm _ _
  -- the component equations
  have E3 : (2 : ℝ) • (p₁ * p₁) + (2 : ℝ) • (p₀ * p₀) + (2 : ℝ) • (p₁ * x) + (2 : ℝ) • (p₀ * x)
      = p₁ + x + p₀ := by
    have e1 := hp; have e2 := hpq
    simp only [jadd_mul, jmul_add, jmul_sub, m10, m01, cx1, cx0] at e1 e2
    linear_combination (norm := module) e1 + e2
  have q11 : p₁ * p₁ ∈ peirce f 1 := peirce_one_mul_one hf h1 h1
  have q00 : p₀ * p₀ ∈ peirce f 0 := peirce_zero_mul_zero hf h0 h0
  have q1h : p₁ * x ∈ peirce f (1 / 2) := peirce_one_mul_half hf h1 hh
  have q0h : p₀ * x ∈ peirce f (1 / 2) := peirce_zero_mul_half hf h0 hh
  have S1 : (2 : ℝ) • (p₁ * p₁) = p₁ := by
    have := congrArg (P1 f) E3
    simp only [map_add, map_smul, P1_of_mem1 q11, P1_of_mem0 q00, P1_of_memh q1h,
      P1_of_memh q0h, P1_of_mem1 h1, P1_of_memh hh, P1_of_mem0 h0, smul_zero, add_zero] at this
    exact this
  have S0 : (2 : ℝ) • (p₀ * p₀) = p₀ := by
    have := congrArg (P0 f) E3
    simp only [map_add, map_smul, P0_of_mem1 q11, P0_of_mem0 q00, P0_of_memh q1h,
      P0_of_memh q0h, P0_of_mem1 h1, P0_of_memh hh, P0_of_mem0 h0, smul_zero, add_zero,
      zero_add] at this
    exact this
  have Sh : (2 : ℝ) • (p₁ * x) + (2 : ℝ) • (p₀ * x) = x := by
    have := congrArg (Ph f) E3
    simp only [map_add, map_smul, Ph_of_mem1 q11, Ph_of_mem0 q00, Ph_of_memh q1h,
      Ph_of_memh q0h, Ph_of_mem1 h1, Ph_of_memh hh, Ph_of_mem0 h0, smul_zero, add_zero,
      zero_add] at this
    exact this
  -- `a = 2 p₁`, `b = 2 p₀`
  rw [mem_peirce, one_smul] at h1
  rw [mem_peirce, zero_smul] at h0
  rw [mem_peirce] at hh
  have hp1f : p₁ * f = p₁ := by rw [jmul_comm]; exact h1
  have hp0f : p₀ * f = 0 := by rw [jmul_comm]; exact h0
  have haa : ((2 : ℝ) • p₁) * ((2 : ℝ) • p₁) = (2 : ℝ) • p₁ := by
    rw [jsmul_mul, jmul_smul, S1]
  have hbb : ((2 : ℝ) • p₀) * ((2 : ℝ) • p₀) = (2 : ℝ) • p₀ := by
    rw [jsmul_mul, jmul_smul, S0]
  have hab : ((2 : ℝ) • p₁) * ((2 : ℝ) • p₀) = 0 := by
    rw [jsmul_mul, jmul_smul, m10, smul_zero, smul_zero]
  have haf : ((2 : ℝ) • p₁) * (u' - f) = 0 := by
    rw [jmul_sub, mul_unit hu, jsmul_mul, hp1f, sub_self]
  have hbf : ((2 : ℝ) • p₀) * f = 0 := by rw [jsmul_mul, hp0f, smul_zero]
  -- commutations
  have cA : ∀ z, p₁ * (f * z) = f * (p₁ * z) := by
    intro z
    have := orth_commute haa haf z
    simp only [jsub_mul, hu, jsmul_mul, jmul_smul, jmul_sub] at this
    have h2 : (2 : ℝ) • (p₁ * (f * z)) = (2 : ℝ) • (f * (p₁ * z)) := by
      linear_combination (norm := module) -this
    exact smul_right_injective V (two_ne_zero) h2
  have cB : ∀ z, p₀ * (f * z) = f * (p₀ * z) := by
    intro z
    have := orth_commute hbb hbf z
    simp only [jsmul_mul, jmul_smul] at this
    exact smul_right_injective V (two_ne_zero) this
  have cAB : ∀ z, p₁ * (p₀ * z) = p₀ * (p₁ * z) := by
    intro z
    have := orth_commute haa hab z
    simp only [jsmul_mul, jmul_smul, _root_.smul_smul] at this
    exact smul_right_injective V (by norm_num : (2 * 2 : ℝ) ≠ 0) this
  -- the `V₁(a)`-part of `x` vanishes
  have yA : (2 : ℝ) • (p₁ * (p₁ * x)) = (1 / 2 : ℝ) • (p₁ * x) := by
    let y := (2 : ℝ) • (((2 : ℝ) • p₁) * (((2 : ℝ) • p₁) * x)) - ((2 : ℝ) • p₁) * x
    have hy1 : ((2 : ℝ) • p₁) * y = y := by
      have := P1_mem haa x; rw [mem_peirce, one_smul] at this; exact this
    have hfa : ((2 : ℝ) • p₁) * (f - (2 : ℝ) • p₁) = 0 := by
      rw [jmul_sub, haa, jsmul_mul, hp1f, sub_self]
    have hy0 : y * (f - (2 : ℝ) • p₁) = 0 :=
      peirce_one_mul_zero haa (mem_peirce_one_of_mul hy1) (mem_peirce_zero_of_orth hfa)
    have hfy1 : f * y = y := by
      have : f * y = (f - (2 : ℝ) • p₁) * y + ((2 : ℝ) • p₁) * y := by
        rw [← jadd_mul]; congr 1; abel
      rw [this, jmul_comm (f - _) y, hy0, zero_add, hy1]
    have hfyh : f * y = (1 / 2 : ℝ) • y := by
      simp only [y, jmul_sub, jmul_smul, jsmul_mul, ← cA, hh]
      module
    have := eq_zero_of_mem_one_half hfy1 hfyh
    simp only [y, jsmul_mul, jmul_smul, _root_.smul_smul] at this
    linear_combination (norm := module) (1 / 4 : ℝ) • this
  have yB : (2 : ℝ) • (p₀ * (p₀ * x)) = (1 / 2 : ℝ) • (p₀ * x) := by
    let y := (2 : ℝ) • (((2 : ℝ) • p₀) * (((2 : ℝ) • p₀) * x)) - ((2 : ℝ) • p₀) * x
    have hy1 : ((2 : ℝ) • p₀) * y = y := by
      have := P1_mem hbb x; rw [mem_peirce, one_smul] at this; exact this
    have hy0 : y * f = 0 :=
      peirce_one_mul_zero hbb (mem_peirce_one_of_mul hy1) (mem_peirce_zero_of_orth hbf)
    have hfy0 : f * y = 0 := by rw [jmul_comm]; exact hy0
    have hfyh : f * y = (1 / 2 : ℝ) • y := by
      simp only [y, jmul_sub, jmul_smul, jsmul_mul, ← cB, hh]
      module
    have hy : y = 0 := by
      have h' : (1 / 2 : ℝ) • y = 0 := by rw [← hfyh, hfy0]
      rcases smul_eq_zero.mp h' with h | h
      · norm_num at h
      · exact h
    simp only [y, jsmul_mul, jmul_smul, _root_.smul_smul] at hy
    linear_combination (norm := module) (1 / 4 : ℝ) • hy
  -- hence `p₁ x = p₀ x = ¼ x`
  have hbx : p₀ * x = (1 / 2 : ℝ) • x - p₁ * x := by
    linear_combination (norm := module) (1 / 2 : ℝ) • Sh
  have k1 : p₁ * (p₀ * x) = (1 / 2 : ℝ) • (p₁ * x) - p₁ * (p₁ * x) := by
    rw [hbx, jmul_sub, jmul_smul]
  have k2 : p₀ * (p₀ * x) = (1 / 2 : ℝ) • (p₀ * x) - p₀ * (p₁ * x) := by
    conv_lhs => rw [hbx]
    rw [jmul_sub, jmul_smul]
  have hC := cAB x
  have ax : p₁ * x = (1 / 4 : ℝ) • x := by
    linear_combination (norm := module) yA - yB - (2 : ℝ) • k1 + (2 : ℝ) • k2 + (2 : ℝ) • hC
      + (1 / 2 : ℝ) • hbx
  have bx : p₀ * x = (1 / 4 : ℝ) • x := by rw [hbx, ax]; module
  have xa : x * p₁ = (1 / 4 : ℝ) • x := by rw [jmul_comm]; exact ax
  have xb : x * p₀ = (1 / 4 : ℝ) • x := by rw [jmul_comm]; exact bx
  have S1' : p₁ * p₁ = (1 / 2 : ℝ) • p₁ := by
    linear_combination (norm := module) (1 / 2 : ℝ) • S1
  have S0' : p₀ * p₀ = (1 / 2 : ℝ) • p₀ := by
    linear_combination (norm := module) (1 / 2 : ℝ) • S0
  set_option linter.unusedSimpArgs false in
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [jadd_mul, jmul_add, jsub_mul, jmul_sub, jsmul_mul, jmul_smul, S1', S0', m10, m01,
      xa, xb, ax, bx]
    module

/-- **Exchangeable orthogonal idempotents are connected** (the converse of
`connect_symm`; Hanche-Olsen–Størmer 5.1.x, proved here without the functional calculus
or Shirshov–Cohn).  If `p ⊥ q` are idempotents and `U_s p = q` for a symmetry `s`, then
`v = 2 (P₁(f) p − P₀(f) p)`, `f = ½(u + s)`, lies in `V½(p) ∩ V½(q)` and `v² = p + q`.

Proof: with `p = p₁ + x + p₀` the Peirce decomposition for `f`, `q = σ_f p = p₁ − x + p₀`;
`p² = p` and `pq = 0` give `2p₁² = p₁`, `2p₀² = p₀`, `2x(p₁ + p₀) = x`; so `a = 2p₁`,
`b = 2p₀` are orthogonal idempotents, `L_a, L_b, L_f` commute, the `V₁(a)`- and
`V₁(b)`-parts of `x ∈ V½(f)` vanish (they would lie in `V₁(f)`, resp. `V₀(f)`), and then
`a x = b x = ½ x` by a two-line computation with `(a + b) x = x`. -/
theorem exch_connect (hu : ∀ a : V, u' * a = a) {p q s : V} (hp : p * p = p)
    (hpq : p * q = 0) (hs : s * s = u') (hsp : jQ s p = q) :
    ∃ v : V, p * v = (1 / 2 : ℝ) • v ∧ q * v = (1 / 2 : ℝ) • v ∧ v * v = p + q := by
  obtain ⟨f, hf, hQ⟩ := symm_refl hu hs
  have hq : q = P1 f p - Ph f p + P0 f p := by
    rw [← hsp, hQ, peirceRefl_apply]
    conv_lhs => rw [← peirce_decomp f p]
    rw [map_add, map_add, Ph_of_mem1 (P1_mem hf p), Ph_of_memh (Ph_mem hf p),
      Ph_of_mem0 (P0_mem hf p)]
    module
  have hpd : p = P1 f p + Ph f p + P0 f p := (peirce_decomp f p).symm
  have key := exch_connect_aux hu hf (P1_mem hf p) (Ph_mem hf p) (P0_mem hf p)
    (by rw [← hpd]; exact hp) (by rw [← hpd, ← hq]; exact hpq)
  rw [← hpd, ← hq] at key
  exact ⟨_, key⟩

/-- **Exchangeability of orthogonal idempotents, Peirce form** (H-O–S 5.1.x): for
orthogonal idempotents `p, q` in a unital Jordan algebra, some symmetry exchanges them iff
some `v ∈ V½(p) ∩ V½(q)` has `v² = p + q`. -/
theorem exch_iff_connect (hu : ∀ a : V, u' * a = a) {p q : V} (hp : p * p = p)
    (hq : q * q = q) (hpq : p * q = 0) :
    (∃ s : V, s * s = u' ∧ jQ s p = q) ↔
      ∃ v : V, p * v = (1 / 2 : ℝ) • v ∧ q * v = (1 / 2 : ℝ) • v ∧ v * v = p + q := by
  constructor
  · rintro ⟨s, hs, hsp⟩; exact exch_connect hu hp hpq hs hsp
  · rintro ⟨v, hvp, hvq, hvv⟩
    exact ⟨_, connect_symm hu hp hq hpq hvp hvq hvv⟩

end Converse

/-! ## 5. Connected frames give mutually exchangeable families -/

section Frame

variable {u' : V}

/-- **Connected frames are mutually exchangeable.**  Let `e : ι → V` be pairwise orthogonal
idempotents and `i₀ : ι` such that each `e j` (`j ≠ i₀`) is connected to `e i₀` by some
`v ∈ V½(e i₀) ∩ V½(e j)` with `v² = e i₀ + e j`.  Then every two members are exchanged by a
symmetry: `e i₀ ↔ e j` by the connecting-element symmetry `s_j`, and `e i ↔ e j` by the
symmetry `U_{s_j} s_i` (`U_{U_{s_j} s_i} = U_{s_j} U_{s_i} U_{s_j}` on the frame, because
`U_{s_j}` is an automorphism). -/
theorem frame_exch (hu : ∀ a : V, u' * a = a) {ι : Type*} [DecidableEq ι] (e : ι → V)
    (he : ∀ i, e i * e i = e i) (horth : ∀ i j, i ≠ j → e i * e j = 0) (i₀ : ι)
    (v : ι → V) (hv0 : ∀ j, j ≠ i₀ → e i₀ * v j = (1 / 2 : ℝ) • v j)
    (hvj : ∀ j, j ≠ i₀ → e j * v j = (1 / 2 : ℝ) • v j)
    (hvv : ∀ j, j ≠ i₀ → v j * v j = e i₀ + e j) :
    ∀ i j, ∃ s : V, s * s = u' ∧ jQ s (e i) = e j := by
  -- the connecting symmetries
  let S : ι → V := fun j => v j + (u' - e i₀ - e j)
  have hS : ∀ j, j ≠ i₀ → S j * S j = u' ∧ jQ (S j) (e i₀) = e j := fun j hj =>
    connect_symm hu (he i₀) (he j) (horth i₀ j (Ne.symm hj)) (hv0 j hj) (hvj j hj) (hvv j hj)
  have hfix : ∀ j k, j ≠ i₀ → k ≠ i₀ → k ≠ j → jQ (S j) (e k) = e k := fun j k hj hk hkj =>
    connect_fix hu (he i₀) (he j) (horth i₀ j (Ne.symm hj)) (hv0 j hj) (hvj j hj) (hvv j hj)
      (horth i₀ k (Ne.symm hk)) (horth j k (Ne.symm hkj))
  intro i j
  by_cases hij : i = j
  · subst hij; exact ⟨u', unit_mul_self hu, jQ_unit hu _⟩
  by_cases hi : i = i₀
  · subst hi; exact ⟨S j, (hS j (Ne.symm hij)).1, (hS j (Ne.symm hij)).2⟩
  by_cases hj : j = i₀
  · subst hj
    exact ⟨S i, (hS i hi).1, exch_symm hu (hS i hi).1 (hS i hi).2⟩
  -- `i, j ≠ i₀`, `i ≠ j`: the symmetry `U_{S j} (S i)`
  obtain ⟨hsj, hsj0⟩ := hS j hj
  obtain ⟨hsi, hsi0⟩ := hS i hi
  let φ : V →ₗ[ℝ] V :=
    { toFun := jQ (S j), map_add' := jQ_add (S j), map_smul' := jQ_smul (S j) }
  have hφ : ∀ x y, φ (x * y) = φ x * φ y := jQ_mul_of_symm hu hsj
  refine ⟨jQ (S j) (S i), ?_, ?_⟩
  · have := hφ (S i) (S i)
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [← this, hsi, jQ_apply_unit _ hu, hsj]
  · have h1 : jQ (S j) (e i) = e i := hfix j i hj hi hij
    have h2 := map_jQ φ hφ (S i) (e i)
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk] at h2
    rw [← h1, ← h2, exch_symm hu hsi hsi0, hsj0]

/-- **Part (i) of `ExceptionalBoundedRank` from a connected frame**: a JB-algebra has an
exchangeable family (`HasExchFamily`) as soon as it has `n ≥ 2` pairwise orthogonal
idempotents summing to `1`, all connected to one of them. -/
theorem hasExchFamily_of_connected_frame {A : Type u} [AddCommGroup A] [Module ℝ A]
    [PartialOrder A] [OrderUnitSpace A] [Mul A] [hA : JBAlgebra A] (n : ℕ) (hn : 2 ≤ n)
    (e : Fin n → A) (he : ∀ i, e i * e i = e i) (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (hsum : ∑ i, e i = ouUnit A) (i₀ : Fin n) (v : Fin n → A)
    (hv0 : ∀ j, j ≠ i₀ → e i₀ * v j = (1 / 2 : ℝ) • v j)
    (hvj : ∀ j, j ≠ i₀ → e j * v j = (1 / 2 : ℝ) • v j)
    (hvv : ∀ j, j ≠ i₀ → v j * v j = e i₀ + e j) : HasExchFamily A :=
  ⟨n, hn, e, he, horth, hsum, frame_exch hA.one_mul e he horth i₀ v hv0 hvj hvv⟩

/-- **Exchangeable families are connected frames**, and conversely: part (i) of
`ExceptionalBoundedRank` (`HasExchFamily`) holds iff there are `n ≥ 2` pairwise orthogonal
idempotents summing to `1`, each connected to the first by some `v ∈ V½(e₀) ∩ V½(e_j)`
with `v² = e₀ + e_j`. -/
theorem hasExchFamily_iff_connected_frame {A : Type u} [AddCommGroup A] [Module ℝ A]
    [PartialOrder A] [OrderUnitSpace A] [Mul A] [hA : JBAlgebra A] :
    HasExchFamily A ↔ ∃ n : ℕ, ∃ hn : 2 ≤ n, ∃ e : Fin n → A, (∀ i, e i * e i = e i) ∧
      (∀ i j, i ≠ j → e i * e j = 0) ∧ ∑ i, e i = ouUnit A ∧
      ∀ j, j ≠ ⟨0, by omega⟩ → ∃ v : A, e ⟨0, by omega⟩ * v = (1 / 2 : ℝ) • v ∧
        e j * v = (1 / 2 : ℝ) • v ∧ v * v = e ⟨0, by omega⟩ + e j := by
  constructor
  · rintro ⟨n, hn, e, he, horth, hsum, hex⟩
    refine ⟨n, hn, e, he, horth, hsum, fun j hj => ?_⟩
    obtain ⟨s, hs, hsp⟩ := hex ⟨0, by omega⟩ j
    exact exch_connect hA.one_mul (he _) (horth _ _ (Ne.symm hj)) hs hsp
  · rintro ⟨n, hn, e, he, horth, hsum, hv⟩
    choose! v hv0 hvj hvv using hv
    exact hasExchFamily_of_connected_frame n hn e he horth hsum ⟨0, by omega⟩ v hv0 hvj hvv

end Frame

/-! ## 6. The joint Peirce decomposition of a frame -/

section Joint

/-- Multiplication by `a`, as a linear map. -/
def Lm (a : V) : V →ₗ[ℝ] V where
  toFun x := a * x
  map_add' := jmul_add a
  map_smul' r x := jmul_smul r a x

theorem Lm_apply (a x : V) : Lm a x = a * x := rfl

/-- A linear map commuting with `L_e` commutes with the Peirce projections of `e`. -/
theorem P1_comm (φ : V →ₗ[ℝ] V) {e : V} (hφ : ∀ z, φ (e * z) = e * φ z) (z : V) :
    φ (P1 e z) = P1 e (φ z) := by
  rw [P1_apply, P1_apply, map_sub, map_smul, hφ, hφ]

theorem Ph_comm (φ : V →ₗ[ℝ] V) {e : V} (hφ : ∀ z, φ (e * z) = e * φ z) (z : V) :
    φ (Ph e z) = Ph e (φ z) := by
  rw [Ph_apply, Ph_apply, map_sub, map_smul, map_smul, hφ, hφ, hφ]

theorem P0_comm (φ : V →ₗ[ℝ] V) {e : V} (hφ : ∀ z, φ (e * z) = e * φ z) (z : V) :
    φ (P0 e z) = P0 e (φ z) := by
  rw [P0_apply, P0_apply, map_add, map_sub, map_smul, map_smul, hφ, hφ, hφ]

variable {ι : Type*} [DecidableEq ι] {e : ι → V}

section Frame

variable (he : ∀ i, e i * e i = e i) (horth : ∀ i j, i ≠ j → e i * e j = 0)
include he horth

theorem frame_Lcomm (i j : ι) (z : V) : e i * (e j * z) = e j * (e i * z) := by
  by_cases h : i = j
  · subst h; rfl
  · exact orth_commute (he i) (horth i j h) z

/-- `L_{e_j}` commutes with the Peirce projections of `e_i`. -/
theorem frame_L_P1 (i j : ι) (z : V) : e j * P1 (e i) z = P1 (e i) (e j * z) :=
  P1_comm (Lm (e j)) (fun z => frame_Lcomm he horth j i z) z

theorem frame_L_Ph (i j : ι) (z : V) : e j * Ph (e i) z = Ph (e i) (e j * z) :=
  Ph_comm (Lm (e j)) (fun z => frame_Lcomm he horth j i z) z

theorem frame_L_P0 (i j : ι) (z : V) : e j * P0 (e i) z = P0 (e i) (e j * z) :=
  P0_comm (Lm (e j)) (fun z => frame_Lcomm he horth j i z) z

theorem frame_Ph_Ph (i j : ι) (z : V) : Ph (e i) (Ph (e j) z) = Ph (e j) (Ph (e i) z) :=
  (Ph_comm (Ph (e i)) (fun z => (frame_L_Ph he horth i j z).symm) z)

theorem frame_P1_Ph (i j : ι) (z : V) : P1 (e i) (Ph (e j) z) = Ph (e j) (P1 (e i) z) :=
  (Ph_comm (P1 (e i)) (fun z => (frame_L_P1 he horth i j z).symm) z)

theorem frame_P1_P1 (i j : ι) (z : V) : P1 (e i) (P1 (e j) z) = P1 (e j) (P1 (e i) z) :=
  (P1_comm (P1 (e i)) (fun z => (frame_L_P1 he horth i j z).symm) z)

theorem frame_Ph_P1 (i j : ι) (z : V) : Ph (e i) (P1 (e j) z) = P1 (e j) (Ph (e i) z) :=
  (P1_comm (Ph (e i)) (fun z => (frame_L_Ph he horth i j z).symm) z)

theorem frame_P1_P0 (i j : ι) (z : V) : P1 (e i) (P0 (e j) z) = P0 (e j) (P1 (e i) z) :=
  (P0_comm (P1 (e i)) (fun z => (frame_L_P1 he horth i j z).symm) z)

theorem frame_Ph_P0 (i j : ι) (z : V) : Ph (e i) (P0 (e j) z) = P0 (e j) (Ph (e i) z) :=
  (P0_comm (Ph (e i)) (fun z => (frame_L_Ph he horth i j z).symm) z)

/-- `V₁(e_i) ⊆ V₀(e_j)` for `j ≠ i`. -/
theorem frame_one_sub_zero {i j : ι} (hij : i ≠ j) {x : V} (hx : x ∈ peirce (e i) 1) :
    e j * x = 0 := by
  rw [jmul_comm]
  exact peirce_one_mul_zero (he i) hx (mem_peirce_zero_of_orth (horth i j hij))

/-- `V½(e_i) ∩ V½(e_j) ⊆ V₀(e_k)` for `k ∉ {i, j}`. -/
theorem frame_half_sub_zero {i j k : ι} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) {x : V}
    (hxi : x ∈ peirce (e i) (1 / 2)) (hxj : x ∈ peirce (e j) (1 / 2)) : e k * x = 0 := by
  have h1 : x ∈ peirce (e i + e j) 1 := mem_peirce_one_add hxi hxj
  have h0 : e k ∈ peirce (e i + e j) 0 := by
    rw [mem_peirce, jadd_mul, horth i k (Ne.symm hki), horth j k (Ne.symm hkj)]; module
  rw [jmul_comm]
  exact peirce_one_mul_zero (add_idem_of_orth (he i) (he j) (horth i j hij)) h1 h0

/-- The off-diagonal part, induction step: for `g` an idempotent orthogonal to the frame on
`S` and `y ∈ V½(Σ_S e) ∩ V½(g)`, `y = Σ_{j ∈ S} P½(e_j) y`. -/
theorem frame_half_sum (S : Finset ι) {g : V} (hg : g * g = g) (hgS : ∀ i ∈ S, g * e i = 0)
    {y : V} (hy : (∑ i ∈ S, e i) * y = (1 / 2 : ℝ) • y) (hgy : g * y = (1 / 2 : ℝ) • y) :
    y = ∑ j ∈ S, Ph (e j) y := by
  induction S using Finset.induction_on generalizing y with
  | empty =>
    rw [Finset.sum_empty, jzero_mul] at hy
    have : (1 / 2 : ℝ) • y = 0 := hy.symm
    rcases smul_eq_zero.mp this with h | h
    · norm_num at h
    · simp [h]
  | insert b S hb ih =>
    have hgS' : ∀ i ∈ S, g * e i = 0 := fun i hi => hgS i (Finset.mem_insert_of_mem hi)
    have hgb : g * e b = 0 := hgS b (Finset.mem_insert_self b S)
    have hbg : e b * g = 0 := by rw [jmul_comm]; exact hgb
    have hcg : ∀ z, g * (e b * z) = e b * (g * z) := fun z =>
      (orth_commute (he b) hbg z).symm
    rw [Finset.sum_insert hb] at hy ⊢
    rw [jadd_mul] at hy
    -- the `V₁(e_b)`-part vanishes
    have hP1 : P1 (e b) y = 0 := by
      have h1 : g * P1 (e b) y = 0 := by
        rw [jmul_comm]
        exact peirce_one_mul_zero (he b) (P1_mem (he b) y) (mem_peirce_zero_of_orth hbg)
      have h2 : g * P1 (e b) y = (1 / 2 : ℝ) • P1 (e b) y := by
        rw [← Lm_apply, P1_comm (Lm g) (fun z => hcg z), Lm_apply, hgy, map_smul]
      have : (1 / 2 : ℝ) • P1 (e b) y = 0 := by rw [← h2, h1]
      rcases smul_eq_zero.mp this with h | h
      · norm_num at h
      · exact h
    -- the `V₀(e_b)`-part, by induction
    set z := P0 (e b) y with hz
    have hSz : (∑ i ∈ S, e i) * z = (1 / 2 : ℝ) • z := by
      have hc : ∀ w, (∑ i ∈ S, e i) * (e b * w) = e b * ((∑ i ∈ S, e i) * w) := by
        intro w
        rw [jsum_mul, jsum_mul, jmul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        exact frame_Lcomm he horth i b w
      rw [hz, ← Lm_apply, P0_comm (Lm _) (fun w => hc w), Lm_apply]
      have : (∑ i ∈ S, e i) * y = (1 / 2 : ℝ) • y - e b * y := by
        rw [← hy]; abel
      rw [this, map_sub, map_smul]
      have hb0 : P0 (e b) (e b * y) = e b * P0 (e b) y := by
        rw [← Lm_apply (e b) (P0 (e b) y), P0_comm (Lm (e b)) (fun w => rfl), Lm_apply]
      rw [hb0, (P0_mem (he b) y : e b * P0 (e b) y = (0 : ℝ) • P0 (e b) y), zero_smul, sub_zero]
    have hgz : g * z = (1 / 2 : ℝ) • z := by
      rw [hz, ← Lm_apply, P0_comm (Lm g) (fun w => hcg w), Lm_apply, hgy, map_smul]
    have hIH := ih hgS' hSz hgz
    -- `P½(e_j) z = P½(e_j) y` for `j ∈ S`
    have hj : ∀ j ∈ S, Ph (e j) z = Ph (e j) y := by
      intro j hjS
      have hjb : j ≠ b := fun h => hb (h ▸ hjS)
      have hgj : g * e j = 0 := hgS' j hjS
      have hyd : y = P1 (e b) y + Ph (e b) y + z := (peirce_decomp (e b) y).symm
      have hPh : Ph (e j) (Ph (e b) y) = 0 := by
        apply Ph_of_mem0
        rw [mem_peirce, zero_smul]
        -- `P½(e_b) y ∈ V½(e_b) ∩ V½(g)`
        have hb' : Ph (e b) y ∈ peirce (e b) (1 / 2) := Ph_mem (he b) y
        have hg' : Ph (e b) y ∈ peirce g (1 / 2) := by
          rw [mem_peirce, ← Lm_apply, Ph_comm (Lm g) (fun w => hcg w), Lm_apply, hgy, map_smul]
        have h1 : Ph (e b) y ∈ peirce (e b + g) 1 := mem_peirce_one_add hb' hg'
        have h0 : e j ∈ peirce (e b + g) 0 := by
          rw [mem_peirce, jadd_mul, horth b j (Ne.symm hjb), hgj]; module
        rw [jmul_comm]
        exact peirce_one_mul_zero (add_idem_of_orth (he b) hg hbg) h1 h0
      conv_rhs => rw [hyd]
      rw [map_add, map_add, hP1, map_zero, hPh, zero_add, zero_add]
    rw [Finset.sum_congr rfl hj] at hIH
    have hyd : y = P1 (e b) y + Ph (e b) y + z := (peirce_decomp (e b) y).symm
    rw [hP1, zero_add] at hyd
    conv_lhs => rw [hyd]
    rw [← hIH]

/-- The joint decomposition on the corner of `Σ_S e`, by induction on `S`. -/
theorem frame_decomp_sum (S : Finset ι) {x : V} (hx : (∑ i ∈ S, e i) * x = x) :
    x = ∑ i ∈ S, P1 (e i) x
      + (1 / 2 : ℝ) • ∑ i ∈ S, ∑ j ∈ S.erase i, Ph (e i) (Ph (e j) x) := by
  induction S using Finset.induction_on generalizing x with
  | empty =>
    rw [Finset.sum_empty, jzero_mul] at hx
    rw [← hx]; simp [map_zero]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, jadd_mul] at hx
    have hca : ∀ w, (∑ i ∈ S, e i) * (e a * w) = e a * ((∑ i ∈ S, e i) * w) := by
      intro w
      rw [jsum_mul, jsum_mul, jmul_sum]
      exact Finset.sum_congr rfl fun i _ => frame_Lcomm he horth i a w
    have hS : (∑ i ∈ S, e i) * x = x - e a * x := by
      rw [eq_sub_iff_add_eq, add_comm]; exact hx
    -- the `V₀(e_a)`-part
    set z := P0 (e a) x with hz
    have hSz : (∑ i ∈ S, e i) * z = z := by
      rw [hz, ← Lm_apply, P0_comm (Lm _) (fun w => hca w), Lm_apply, hS, map_sub]
      have : P0 (e a) (e a * x) = e a * P0 (e a) x := by
        rw [← Lm_apply (e a) (P0 (e a) x), P0_comm (Lm (e a)) (fun w => rfl), Lm_apply]
      rw [this, (P0_mem (he a) x : e a * P0 (e a) x = (0 : ℝ) • P0 (e a) x), zero_smul, sub_zero]
    have hIH := ih hSz
    -- the `V½(e_a)`-part
    set w := Ph (e a) x with hw
    have hSw : (∑ i ∈ S, e i) * w = (1 / 2 : ℝ) • w := by
      rw [hw, ← Lm_apply, Ph_comm (Lm _) (fun w => hca w), Lm_apply, hS, map_sub]
      have : Ph (e a) (e a * x) = e a * Ph (e a) x := by
        rw [← Lm_apply (e a) (Ph (e a) x), Ph_comm (Lm (e a)) (fun w => rfl), Lm_apply]
      rw [this, (Ph_mem (he a) x : e a * Ph (e a) x = (1 / 2 : ℝ) • Ph (e a) x)]
      module
    have haS : ∀ i ∈ S, e a * e i = 0 := fun i hi => horth a i (fun h => ha (h ▸ hi))
    have hW := frame_half_sum he horth S (he a) haS hSw (Ph_mem (he a) x)
    -- rewriting the components of `z` as components of `x`
    have hxd : x = P1 (e a) x + w + z := (peirce_decomp (e a) x).symm
    have hP1z : ∀ i ∈ S, P1 (e i) z = P1 (e i) x := by
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      have h1 : P1 (e i) (P1 (e a) x) = 0 := by
        rw [frame_P1_P1 he horth]
        apply P1_of_mem0
        rw [mem_peirce, zero_smul]
        exact frame_one_sub_zero he horth hia (P1_mem (he i) _)
      have h2 : P1 (e i) w = 0 := by
        rw [hw, frame_P1_Ph he horth]
        apply Ph_of_mem0
        rw [mem_peirce, zero_smul]
        exact frame_one_sub_zero he horth hia (P1_mem (he i) _)
      conv_rhs => rw [hxd]
      rw [map_add, map_add, h1, h2, zero_add, zero_add]
    have hPhz : ∀ i ∈ S, ∀ j ∈ S.erase i, Ph (e i) (Ph (e j) z) = Ph (e i) (Ph (e j) x) := by
      intro i hi j hj
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      have hjS : j ∈ S := Finset.mem_of_mem_erase hj
      have hja : j ≠ a := fun h => ha (h ▸ hjS)
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hmem : ∀ t, Ph (e i) (Ph (e j) t) ∈ peirce (e i) (1 / 2) ∧
          Ph (e i) (Ph (e j) t) ∈ peirce (e j) (1 / 2) := fun t =>
        ⟨Ph_mem (he i) _, by rw [frame_Ph_Ph he horth]; exact Ph_mem (he j) _⟩
      have h1 : Ph (e i) (Ph (e j) (P1 (e a) x)) = 0 := by
        rw [frame_Ph_P1 he horth j a, frame_Ph_P1 he horth i a]
        apply P1_of_mem0
        rw [mem_peirce, zero_smul]
        exact frame_half_sub_zero he horth (Ne.symm hji) (Ne.symm hia) (Ne.symm hja)
          (hmem x).1 (hmem x).2
      have h2 : Ph (e i) (Ph (e j) w) = 0 := by
        rw [hw, frame_Ph_Ph he horth j a, frame_Ph_Ph he horth i a]
        apply Ph_of_mem0
        rw [mem_peirce, zero_smul]
        exact frame_half_sub_zero he horth (Ne.symm hji) (Ne.symm hia) (Ne.symm hja)
          (hmem x).1 (hmem x).2
      conv_rhs => rw [hxd]
      rw [map_add, map_add, map_add, map_add, h1, h2, zero_add, zero_add]
    rw [Finset.sum_congr rfl hP1z,
      Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (hPhz i hi))] at hIH
    -- reassemble
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.erase_insert ha]
    have hins : ∀ i ∈ S, ∑ j ∈ (insert a S).erase i, Ph (e i) (Ph (e j) x)
        = Ph (e i) w + ∑ j ∈ S.erase i, Ph (e i) (Ph (e j) x) := by
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne (Ne.symm hia), Finset.sum_insert
        (fun h => ha (Finset.mem_of_mem_erase h)), hw]
    rw [Finset.sum_congr rfl hins, Finset.sum_add_distrib]
    have hsym : ∑ j ∈ S, Ph (e a) (Ph (e j) x) = ∑ i ∈ S, Ph (e i) w := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hw, frame_Ph_Ph he horth]
    rw [hsym]
    conv_lhs => rw [hxd]
    rw [← hW]
    conv_lhs => rw [hIH]
    module

/-- **The joint Peirce decomposition** of a frame (pairwise orthogonal idempotents
`e₁, …, e_n` summing to the unit): every `x` is
`Σ_i x_ii + Σ_{i<j} x_ij` with `x_ii = P₁(e_i) x ∈ V₁(e_i)` and
`x_ij = P½(e_i) P½(e_j) x ∈ V½(e_i) ∩ V½(e_j)`; written with the symmetric off-diagonal
sum `½ Σ_{i ≠ j}`. -/
theorem frame_decomp [Fintype ι] {u' : V} (hu : ∀ a : V, u' * a = a)
    (hsum : ∑ i, e i = u') (x : V) :
    x = ∑ i, P1 (e i) x + (1 / 2 : ℝ) • ∑ i, ∑ j ∈ Finset.univ.erase i, Ph (e i) (Ph (e j) x) :=
  frame_decomp_sum he horth Finset.univ (by rw [hsum, hu])

/-- The off-diagonal joint components lie in `V_{ij} = V½(e_i) ∩ V½(e_j)`, and are
symmetric in `i, j`. -/
theorem frame_offdiag_mem (i j : ι) (x : V) :
    Ph (e i) (Ph (e j) x) ∈ peirce (e i) (1 / 2) ∧ Ph (e i) (Ph (e j) x) ∈ peirce (e j) (1 / 2) :=
  ⟨Ph_mem (he i) _, by rw [frame_Ph_Ph he horth]; exact Ph_mem (he j) _⟩

/-- **The joint decomposition is direct**: the components of `x` are recovered from any
decomposition `x = Σ_i y_ii + ½ Σ_{i ≠ j} y_ij` (with `y_ij = y_ji`) into joint Peirce
spaces. -/
theorem frame_decomp_unique [Fintype ι] (y : ι → ι → V)
    (hyd : ∀ i, y i i ∈ peirce (e i) 1)
    (hyo : ∀ i j, i ≠ j → y i j ∈ peirce (e i) (1 / 2) ∧ y i j ∈ peirce (e j) (1 / 2))
    (hsym : ∀ i j, y i j = y j i) {x : V}
    (hx : x = ∑ i, y i i + (1 / 2 : ℝ) • ∑ i, ∑ j ∈ Finset.univ.erase i, y i j) :
    (∀ k, P1 (e k) x = y k k) ∧ ∀ k l, k ≠ l → Ph (e k) (Ph (e l) x) = y k l := by
  -- how the projections act on each piece
  have P1d : ∀ k i, P1 (e k) (y i i) = if i = k then y k k else 0 := by
    intro k i
    split_ifs with h
    · subst h; exact P1_of_mem1 (hyd i)
    · apply P1_of_mem0; rw [mem_peirce, zero_smul]
      exact frame_one_sub_zero he horth h (hyd i)
  have P1o : ∀ k i j, i ≠ j → P1 (e k) (y i j) = 0 := by
    intro k i j hij
    by_cases hki : k = i
    · subst hki; exact P1_of_memh (hyo k j hij).1
    by_cases hkj : k = j
    · subst hkj; exact P1_of_memh (hyo i k hij).2
    apply P1_of_mem0; rw [mem_peirce, zero_smul]
    exact frame_half_sub_zero he horth hij hki hkj (hyo i j hij).1 (hyo i j hij).2
  have Phd : ∀ k i, Ph (e k) (y i i) = 0 := by
    intro k i
    by_cases h : i = k
    · subst h; exact Ph_of_mem1 (hyd i)
    · apply Ph_of_mem0; rw [mem_peirce, zero_smul]
      exact frame_one_sub_zero he horth h (hyd i)
  -- `P½(e_k) P½(e_l)` on `y_ij`, `i ≠ j`, `k ≠ l`
  have PPo : ∀ k l i j, k ≠ l → i ≠ j → Ph (e k) (Ph (e l) (y i j)) =
      if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then y i j else 0 := by
    intro k l i j hkl hij
    have hPh : ∀ m, Ph (e m) (y i j) = if m = i ∨ m = j then y i j else 0 := by
      intro m
      split_ifs with h
      · rcases h with h | h
        · subst h; exact Ph_of_memh (hyo m j hij).1
        · subst h; exact Ph_of_memh (hyo i m hij).2
      · push Not at h
        apply Ph_of_mem0; rw [mem_peirce, zero_smul]
        exact frame_half_sub_zero he horth hij h.1 h.2 (hyo i j hij).1 (hyo i j hij).2
    rw [hPh l]
    by_cases hl : l = i ∨ l = j
    · rw [ite_eq_left hl, hPh k]
      by_cases hk : k = i ∨ k = j
      · rw [ite_eq_left hk, ite_eq_left]
        rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;>
          first | exact absurd rfl hkl | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩
      · rw [ite_eq_right hk, ite_eq_right]
        rintro (⟨rfl, -⟩ | ⟨-, rfl⟩)
        · exact hk (Or.inl rfl)
        · exact hk (Or.inr rfl)
    · rw [ite_eq_right hl, map_zero, ite_eq_right]
      rintro (⟨-, rfl⟩ | ⟨rfl, -⟩)
      · exact hl (Or.inr rfl)
      · exact hl (Or.inl rfl)
  constructor
  · intro k
    rw [hx, map_add, map_smul, map_sum, map_sum]
    simp only [map_sum, P1d, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j hj =>
      P1o k i j (Ne.symm (Finset.ne_of_mem_erase hj))))]
    simp
  · intro k l hkl
    rw [hx, map_add, map_smul, map_sum, map_sum, map_add, map_smul, map_sum, map_sum]
    simp only [map_sum, Phd, map_zero, Finset.sum_const_zero, zero_add]
    have hoff : ∀ i, ∑ j ∈ Finset.univ.erase i, Ph (e k) (Ph (e l) (y i j))
        = (if i = k then y k l else 0) + (if i = l then y l k else 0) := by
      intro i
      rw [Finset.sum_congr rfl (fun j hj => PPo k l i j hkl
        (Ne.symm (Finset.ne_of_mem_erase hj)))]
      by_cases hik : i = k
      · rw [ite_eq_left hik, ite_eq_right (fun h => hkl (hik ▸ h)), add_zero]
        rw [Finset.sum_eq_single l]
        · rw [ite_eq_left (Or.inl ⟨hik, rfl⟩), hik]
        · intro j _ hjl
          rw [ite_eq_right]; rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact hjl h
          · exact hkl (hik ▸ h)
        · intro h; exact absurd (Finset.mem_erase.2 ⟨fun h' => hkl (hik ▸ h').symm,
            Finset.mem_univ _⟩) h
      by_cases hil : i = l
      · rw [ite_eq_right hik, ite_eq_left hil, zero_add]
        rw [Finset.sum_eq_single k]
        · rw [ite_eq_left (Or.inr ⟨hil, rfl⟩), hil]
        · intro j _ hjk
          rw [ite_eq_right]; rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact hik h
          · exact hjk h
        · intro h; exact absurd (Finset.mem_erase.2 ⟨fun h' => hik h'.symm,
            Finset.mem_univ _⟩) h
      rw [ite_eq_right hik, ite_eq_right hil, add_zero]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right]; rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact hik h
      · exact hil h
    rw [Finset.sum_congr rfl (fun i _ => hoff i), Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _), hsym l k]
    module

/-! ### Joint Peirce multiplication rules -/

/-- `V_ii V_jj = 0` for `i ≠ j`. -/
theorem frame_mul_diag_diag {i j : ι} (hij : i ≠ j) {x y : V} (hx : x ∈ peirce (e i) 1)
    (hy : y ∈ peirce (e j) 1) : x * y = 0 :=
  peirce_one_mul_zero (he i) hx (by
    rw [mem_peirce, zero_smul]; exact frame_one_sub_zero he horth (Ne.symm hij) hy)

/-- `V_ii V_ij ⊆ V_ij` for `i ≠ j`. -/
theorem frame_mul_diag_off {i j : ι} (hij : i ≠ j) {x y : V} (hx : x ∈ peirce (e i) 1)
    (hyi : y ∈ peirce (e i) (1 / 2)) (hyj : y ∈ peirce (e j) (1 / 2)) :
    x * y ∈ peirce (e i) (1 / 2) ∧ x * y ∈ peirce (e j) (1 / 2) :=
  ⟨peirce_one_mul_half (he i) hx hyi, peirce_zero_mul_half (he j) (by
    rw [mem_peirce, zero_smul]; exact frame_one_sub_zero he horth hij hx) hyj⟩

/-- `V_ii V_jk = 0` for `i ∉ {j, k}`, `j ≠ k`. -/
theorem frame_mul_diag_far {i j k : ι} (hjk : j ≠ k) (hij : i ≠ j) (hik : i ≠ k) {x y : V}
    (hx : x ∈ peirce (e i) 1) (hyj : y ∈ peirce (e j) (1 / 2))
    (hyk : y ∈ peirce (e k) (1 / 2)) : x * y = 0 :=
  peirce_one_mul_zero (he i) hx (by
    rw [mem_peirce, zero_smul]; exact frame_half_sub_zero he horth hjk hij hik hyj hyk)

/-- `V_ij V_jk ⊆ V_ik` for distinct `i, j, k`. -/
theorem frame_mul_off_off {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {x y : V}
    (hxi : x ∈ peirce (e i) (1 / 2)) (hxj : x ∈ peirce (e j) (1 / 2))
    (hyj : y ∈ peirce (e j) (1 / 2)) (hyk : y ∈ peirce (e k) (1 / 2)) :
    x * y ∈ peirce (e i) (1 / 2) ∧ x * y ∈ peirce (e k) (1 / 2) := by
  have hy0 : y ∈ peirce (e i) 0 := by
    rw [mem_peirce, zero_smul]; exact frame_half_sub_zero he horth hjk hij hik hyj hyk
  have hx0 : x ∈ peirce (e k) 0 := by
    rw [mem_peirce, zero_smul]
    exact frame_half_sub_zero he horth hij (Ne.symm hik) (Ne.symm hjk) hxi hxj
  refine ⟨?_, ?_⟩
  · rw [jmul_comm]; exact peirce_zero_mul_half (he i) hy0 hxi
  · exact peirce_zero_mul_half (he k) hx0 hyk

/-- `V_ij V_kl = 0` for disjoint `{i, j}`, `{k, l}`. -/
theorem frame_mul_off_disj {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hki : k ≠ i)
    (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) {x y : V}
    (hxi : x ∈ peirce (e i) (1 / 2)) (hxj : x ∈ peirce (e j) (1 / 2))
    (hyk : y ∈ peirce (e k) (1 / 2)) (hyl : y ∈ peirce (e l) (1 / 2)) : x * y = 0 := by
  have h1 : x ∈ peirce (e i + e j) 1 := mem_peirce_one_add hxi hxj
  have h0 : y ∈ peirce (e i + e j) 0 := by
    rw [mem_peirce, jadd_mul, frame_half_sub_zero he horth hkl (Ne.symm hki) (Ne.symm hli) hyk hyl,
      frame_half_sub_zero he horth hkl (Ne.symm hkj) (Ne.symm hlj) hyk hyl]
    module
  exact peirce_one_mul_zero (add_idem_of_orth (he i) (he j) (horth i j hij)) h1 h0

/-- `V_ij V_ij ⊆ V_ii + V_jj`: `x y = P₁(e_i)(x y) + P₁(e_j)(x y)`. -/
theorem frame_mul_off_same {i j : ι} (hij : i ≠ j) {x y : V}
    (hxi : x ∈ peirce (e i) (1 / 2)) (hxj : x ∈ peirce (e j) (1 / 2))
    (hyi : y ∈ peirce (e i) (1 / 2)) (hyj : y ∈ peirce (e j) (1 / 2)) :
    x * y = P1 (e i) (x * y) + P1 (e j) (x * y) := by
  have hij' := horth i j hij
  have h1 : x * y ∈ peirce (e i + e j) 1 :=
    peirce_one_mul_one (add_idem_of_orth (he i) (he j) hij') (mem_peirce_one_add hxi hxj)
      (mem_peirce_one_add hyi hyj)
  rw [mem_peirce, one_smul] at h1
  have hd := frame_decomp_sum he horth {i, j} (x := x * y) (by
    rw [Finset.sum_pair hij]; exact h1)
  have hPi : Ph (e i) (x * y) = 0 := peirce_half_mul_half (he i) hxi hyi
  have hPj : Ph (e j) (x * y) = 0 := peirce_half_mul_half (he j) hxj hyj
  rw [Finset.sum_pair hij, Finset.sum_pair hij, Finset.erase_insert (by simpa using hij),
    Finset.pair_comm, Finset.erase_insert (by simpa using hij.symm)] at hd
  simp only [Finset.sum_singleton, hPi, hPj, map_zero, add_zero, smul_zero] at hd
  exact hd

end Frame

end Joint

end Papers.REC.JBPeirce
