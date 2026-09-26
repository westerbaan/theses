import Papers.EJA.Appendix2

set_option linter.unusedSimpArgs false

/-!
# EJA 3, the exceptional case: the Albert algebra `M_3(𝕆)^sa` is Jordan

A. Westerbaan, B. Westerbaan, J. van de Wetering, *Pure Maps between Euclidean
Jordan Algebras*, QPL 2018, `../papers/1805.11496/main.tex:212` (Example 3).

`Appendix2.lean` builds the octonions `Oct` (Cayley–Dickson double of `ℍ`) and
proves every axiom of EJA 1 for `M_3(𝕆)^sa = HermMat 3 Oct` except the Jordan
identity (`exceptional_of_jordan`).  This file proves the Jordan identity, so
that `M_3(𝕆)^sa` is a Euclidean Jordan algebra unconditionally
(`albert_isEJA`).  The print asserts it without proof.

## The route: the cubic (Hamilton–Cayley) identity, linearised

Write `x ∘ y` for the Jordan product, `⟨x, y⟩ = re tr (x y)` for the (associative)
inner product, and

* `T x = ⟨x, 1⟩` (the trace), `S x = ½ (T x² − ⟨x, x⟩)`,
  `S(x; y) = T x T y − ⟨x, y⟩` (its polarisation),
* `x^# = x ∘ x − T x · x + S x · 1` (the adjoint), `N x = ⅓ ⟨x^#, x⟩` (the norm).

The one computation is the **linearised Hamilton–Cayley identity** (`Phi_eq_zero`)

  `y ∘ x² + 2 x ∘ (x ∘ y) − T y · x² − 2 T x · (x ∘ y) + S(x; y) · x + S x · y
     − ⟨x^#, y⟩ · 1 = 0`,

of degree 2 in `x` and 1 in `y`.  It is checked on the real coordinates of the
Hermitian matrix it defines (3 real diagonal entries, 3 octonion off-diagonal
entries of 8 real components each).  Reindexing (`perm`) is an automorphism of
everything in sight, so only the 9 coordinates at `(0,0)` and `(0,1)` are
computed: each is a polynomial identity of degree 3 in the 54 real coordinates
of `x` and `y`, closed by `ring` after expanding the Cayley–Dickson product into
quaternion and then real components.  No octonion law (alternativity, Moufang)
is needed separately.

Everything else is algebra in a commutative unital algebra with an associative
form.  At `y = x` the identity is `3 (x ∘ x² − T x · x² + S x · x − N x · 1) = 0`,
the cubic identity (`cubic`).  Solving the linearised identity for
`x² ∘ y` and applying it to `x ∘ y` on one side and multiplying it by `x` on the
other, both sides of `x² ∘ (x ∘ y) = x ∘ (x² ∘ y)` differ by
`c₂ · x² + c₁ · x + c₀ · 1` with scalar coefficients that vanish by the
associativity of the form (`T (x ∘ y) = ⟨x, y⟩`, `⟨x, x ∘ y⟩ = ⟨x², y⟩`) and
the cubic identity (`⟨x^#, x ∘ y⟩ = ⟨x ∘ x^#, y⟩ = N x · T y`).  This is the
classical derivation of the Jordan identity from a cubic norm structure
(Freudenthal, Springer, McCrimmon), specialised to the one step it needs.
-/

namespace Papers.EJA

open Matrix
open scoped InnerProductSpace

namespace Albert

/-- The Albert algebra `M_3(𝕆)^sa`. -/
abbrev Alb := HermMat 3 Oct

theorem ejare (z : Oct) : EJAScalars.re z = z.fst.re := rfl

@[simp] theorem mat_sub (A B : Alb) : (A - B).mat = A.mat - B.mat := rfl

@[simp] theorem mat_neg (A : Alb) : (-A).mat = -A.mat := rfl

/-! ### The Jordan product and the form: the non-Jordan axioms, restated -/

theorem mul_comm' (A B : Alb) : A * B = B * A :=
  HermMat.ext (by simp only [HermMat.mat_mul, add_comm])

theorem mul_add' (A B C : Alb) : A * (B + C) = A * B + A * C :=
  HermMat.ext (by
    simp only [HermMat.mat_mul, HermMat.mat_add, Matrix.mul_add, Matrix.add_mul, smul_add]
    abel)

theorem mul_smul' (r : ℝ) (A B : Alb) : A * (r • B) = r • (A * B) :=
  HermMat.ext (by
    simp only [HermMat.mat_mul, HermMat.mat_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul, mul_comm r])

theorem mul_sub' (A B C : Alb) : A * (B - C) = A * B - A * C := by
  rw [sub_eq_add_neg, sub_eq_add_neg, mul_add', ← neg_one_smul ℝ C, mul_smul', neg_one_smul]

theorem mul_one' (A : Alb) : A * 1 = A :=
  HermMat.ext (by
    simp only [HermMat.mat_mul, HermMat.mat_one, Matrix.one_mul, Matrix.mul_one]
    rw [← two_smul ℝ A.mat, smul_smul]; norm_num)

theorem inner_mul' (A B C : Alb) : ⟪A * B, C⟫_ℝ = ⟪B, A * C⟫_ℝ := by
  simp only [hermMat_inner, HermMat.mat_mul, Matrix.smul_mul, Matrix.mul_smul, trace_smul,
    map_smul, Matrix.add_mul, Matrix.mul_add, trace_add, map_add, smul_eq_mul]
  congr 1
  have h1 := re_trace_mul_assoc A.mat B.mat C.mat
  have h2 := re_trace_mul_comm A.mat (B.mat * C.mat)
  have h3 := re_trace_mul_assoc B.mat C.mat A.mat
  have h4 := re_trace_mul_assoc B.mat A.mat C.mat
  linarith

/-! ### The trace, the quadratic trace, the adjoint and the norm -/

/-- The trace `T x = ⟨x, 1⟩ = re tr x`. -/
noncomputable def T (x : Alb) : ℝ := ⟪x, 1⟫_ℝ

/-- The polarised quadratic trace `S(x; y) = T x T y − ⟨x, y⟩`. -/
noncomputable def S2 (x y : Alb) : ℝ := T x * T y - ⟪x, y⟫_ℝ

/-- The quadratic trace `S x = ½ (T x² − ⟨x, x⟩)`. -/
noncomputable def S (x : Alb) : ℝ := (T x * T x - ⟪x, x⟫_ℝ) / 2

/-- The adjoint `x^# = x ∘ x − T x · x + S x · 1`. -/
noncomputable def sharp (x : Alb) : Alb := x * x - T x • x + S x • 1

/-- The norm `N x = ⅓ ⟨x^#, x⟩`. -/
noncomputable def N (x : Alb) : ℝ := ⟪sharp x, x⟫_ℝ / 3

/-- The linearised Hamilton–Cayley expression; `Phi_eq_zero` says it vanishes. -/
noncomputable def Phi (x y : Alb) : Alb :=
  y * (x * x) + (2 : ℝ) • (x * (x * y)) - T y • (x * x) - (2 * T x) • (x * y) + S2 x y • x
    + S x • y - ⟪sharp x, y⟫_ℝ • (1 : Alb)

/-! ### Coordinates of a Hermitian octonion matrix -/

theorem h10 (A : Alb) : A.mat 1 0 = star (A.mat 0 1) := (A.herm.apply 1 0).symm
theorem h21 (A : Alb) : A.mat 2 1 = star (A.mat 1 2) := (A.herm.apply 2 1).symm
theorem h20 (A : Alb) : A.mat 2 0 = star (A.mat 0 2) := (A.herm.apply 2 0).symm

theorem diag_snd (A : Alb) (i : Fin 3) : (A.mat i i).snd = 0 := by
  have h := congrArg Oct.snd (A.herm.apply i i)
  simp only [Oct.star_snd] at h
  have : (2 : ℝ) • (A.mat i i).snd = 0 := by rw [two_smul]; nth_rw 1 [← h]; simp
  exact (smul_eq_zero.mp this).resolve_left two_ne_zero

theorem diag_fst_star (A : Alb) (i : Fin 3) : star (A.mat i i).fst = (A.mat i i).fst := by
  have h := congrArg Oct.fst (A.herm.apply i i)
  simpa only [Oct.star_fst] using h

theorem diag_imI (A : Alb) (i : Fin 3) : (A.mat i i).fst.imI = 0 := by
  have h := congrArg (fun q : Quaternion ℝ => q.imI) (diag_fst_star A i); simp at h; linarith

theorem diag_imJ (A : Alb) (i : Fin 3) : (A.mat i i).fst.imJ = 0 := by
  have h := congrArg (fun q : Quaternion ℝ => q.imJ) (diag_fst_star A i); simp at h; linarith

theorem diag_imK (A : Alb) (i : Fin 3) : (A.mat i i).fst.imK = 0 := by
  have h := congrArg (fun q : Quaternion ℝ => q.imK) (diag_fst_star A i); simp at h; linarith

/-- A Hermitian octonion matrix vanishes as soon as its 27 real coordinates do:
the real parts of the diagonal and the three upper off-diagonal entries. -/
theorem alb_eq_zero (Z : Alb) (d0 : (Z.mat 0 0).fst.re = 0) (d1 : (Z.mat 1 1).fst.re = 0)
    (d2 : (Z.mat 2 2).fst.re = 0) (e01 : Z.mat 0 1 = 0) (e12 : Z.mat 1 2 = 0)
    (e02 : Z.mat 0 2 = 0) : Z = 0 := by
  have hd : ∀ i : Fin 3, (Z.mat i i).fst.re = 0 → Z.mat i i = 0 := fun i h =>
    Oct.ext (Quaternion.ext _ _ h (diag_imI Z i) (diag_imJ Z i) (diag_imK Z i)) (diag_snd Z i)
  refine HermMat.ext (Matrix.ext fun i j => ?_)
  rw [HermMat.mat_zero, Matrix.zero_apply]
  fin_cases i <;> fin_cases j
  · exact hd 0 d0
  · exact e01
  · exact e02
  · show Z.mat 1 0 = 0; rw [h10, e01, star_zero]
  · exact hd 1 d1
  · exact e12
  · show Z.mat 2 0 = 0; rw [h20, e02, star_zero]
  · show Z.mat 2 1 = 0; rw [h21, e12, star_zero]
  · exact hd 2 d2

/-- Expand an expression in the entries of Hermitian octonion matrices `x`, `y`
into real coordinates (upper off-diagonal entries and the real diagonal). -/
macro "alb_simp" x:term:max y:term:max : tactic => `(tactic| (
  have s0 := diag_snd $x 0; have s1 := diag_snd $x 1; have s2 := diag_snd $x 2
  have t0 := diag_snd $y 0; have t1 := diag_snd $y 1; have t2 := diag_snd $y 2
  simp only [Phi, sharp, S, S2, T, hermMat_inner, ejare, HermMat.mat_add, mat_sub,
    HermMat.mat_smul, HermMat.mat_mul, HermMat.mat_one, HermMat.mat_zero, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply, Matrix.mul_apply, Fin.sum_univ_three,
    trace_fin_three, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.one_apply_eq, Matrix.one_apply_ne, h10, h21, h20, s0, s1, s2, t0, t1,
    t2, Oct.add_fst, Oct.add_snd, Oct.sub_fst, Oct.sub_snd, Oct.smul_fst, Oct.smul_snd,
    Oct.mul_fst, Oct.mul_snd, Oct.star_fst, Oct.star_snd, Oct.one_fst, Oct.one_snd, Oct.zero_fst,
    Oct.zero_snd, Quaternion.re_add, Quaternion.re_sub, Quaternion.re_mul, Quaternion.re_smul,
    Quaternion.re_star, Quaternion.re_neg, Quaternion.imI_add, Quaternion.imI_sub,
    Quaternion.imI_mul, Quaternion.imI_smul, Quaternion.imI_star, Quaternion.imI_neg,
    Quaternion.imJ_add, Quaternion.imJ_sub, Quaternion.imJ_mul, Quaternion.imJ_smul,
    Quaternion.imJ_star, Quaternion.imJ_neg, Quaternion.imK_add, Quaternion.imK_sub,
    Quaternion.imK_mul, Quaternion.imK_smul, Quaternion.imK_star, Quaternion.imK_neg,
    Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero,
    Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one, smul_eq_mul,
    diag_imI, diag_imJ, diag_imK, star_zero, neg_zero, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, Fin.isValue, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, Fin.reduceEq]))

/-! ### The linearised Hamilton–Cayley identity, coordinate by coordinate -/

set_option maxHeartbeats 1000000 in
theorem Phi_00 (x y : Alb) : ((Phi x y).mat 0 0).fst.re = 0 := by
  alb_simp x y; ring

set_option maxHeartbeats 1000000 in
theorem Phi_01_fst_re (x y : Alb) : ((Phi x y).mat 0 1).fst.re = 0 := by
  alb_simp x y; ring

set_option maxHeartbeats 1000000 in
theorem Phi_01_fst_imI (x y : Alb) : ((Phi x y).mat 0 1).fst.imI = 0 := by
  alb_simp x y; ring

set_option maxHeartbeats 1000000 in
theorem Phi_01_fst_imJ (x y : Alb) : ((Phi x y).mat 0 1).fst.imJ = 0 := by
  alb_simp x y; ring

set_option maxHeartbeats 1000000 in
theorem Phi_01_fst_imK (x y : Alb) : ((Phi x y).mat 0 1).fst.imK = 0 := by
  alb_simp x y; ring

set_option maxHeartbeats 1000000 in
theorem Phi_01_snd_re (x y : Alb) : ((Phi x y).mat 0 1).snd.re = 0 := by
  alb_simp x y; ring

set_option maxHeartbeats 1000000 in
theorem Phi_01_snd_imI (x y : Alb) : ((Phi x y).mat 0 1).snd.imI = 0 := by
  alb_simp x y; ring

set_option maxHeartbeats 1000000 in
theorem Phi_01_snd_imJ (x y : Alb) : ((Phi x y).mat 0 1).snd.imJ = 0 := by
  alb_simp x y; ring

set_option maxHeartbeats 1000000 in
theorem Phi_01_snd_imK (x y : Alb) : ((Phi x y).mat 0 1).snd.imK = 0 := by
  alb_simp x y; ring

theorem Phi_01 (x y : Alb) : (Phi x y).mat 0 1 = 0 :=
  Oct.ext
    (Quaternion.ext _ _ (Phi_01_fst_re x y) (Phi_01_fst_imI x y)
      (Phi_01_fst_imJ x y) (Phi_01_fst_imK x y))
    (Quaternion.ext _ _ (Phi_01_snd_re x y) (Phi_01_snd_imI x y)
      (Phi_01_snd_imJ x y) (Phi_01_snd_imK x y))

/-! ### Reindexing: the other coordinates by symmetry

Permuting the indices of a Hermitian matrix, `x ↦ x.submatrix e e`, preserves the
Jordan product, the unit and the form, hence `Phi`; so the coordinates of `Phi`
at `(1,1)`, `(2,2)`, `(1,2)`, `(0,2)` are those at `(0,0)` and `(0,1)` of `Phi`
at reindexed arguments. -/

/-- `x ↦ x.submatrix e e`, for a permutation `e` of the indices. -/
noncomputable def perm (e : Fin 3 ≃ Fin 3) (A : Alb) : Alb :=
  (⟨A.mat.submatrix e e, by
    show (A.mat.submatrix e e).IsHermitian
    unfold Matrix.IsHermitian
    rw [conjTranspose_submatrix, A.herm.eq]⟩ : ↥(hermSub 3 Oct))

@[simp] theorem perm_mat (e : Fin 3 ≃ Fin 3) (A : Alb) :
    (perm e A).mat = A.mat.submatrix e e := rfl

theorem perm_add (e : Fin 3 ≃ Fin 3) (A B : Alb) : perm e (A + B) = perm e A + perm e B := rfl

theorem perm_sub (e : Fin 3 ≃ Fin 3) (A B : Alb) : perm e (A - B) = perm e A - perm e B := rfl

theorem perm_smul (e : Fin 3 ≃ Fin 3) (r : ℝ) (A : Alb) : perm e (r • A) = r • perm e A := rfl

theorem perm_mul (e : Fin 3 ≃ Fin 3) (A B : Alb) : perm e (A * B) = perm e A * perm e B :=
  HermMat.ext (by
    simp only [perm_mat, HermMat.mat_mul]
    rw [submatrix_mul_equiv, submatrix_mul_equiv]; rfl)

theorem perm_one (e : Fin 3 ≃ Fin 3) : perm e 1 = 1 :=
  HermMat.ext (by simp only [perm_mat, HermMat.mat_one, submatrix_one_equiv])

theorem perm_inner (e : Fin 3 ≃ Fin 3) (A B : Alb) : ⟪perm e A, perm e B⟫_ℝ = ⟪A, B⟫_ℝ := by
  rw [hermMat_inner, hermMat_inner, perm_mat, perm_mat, submatrix_mul_equiv]
  congr 1
  simp only [trace, diag, submatrix_apply]
  exact Equiv.sum_comp e (fun i => (A.mat * B.mat) i i)

theorem T_perm (e : Fin 3 ≃ Fin 3) (x : Alb) : T (perm e x) = T x := by
  unfold T; rw [← perm_inner e x 1, perm_one]

theorem S2_perm (e : Fin 3 ≃ Fin 3) (x y : Alb) : S2 (perm e x) (perm e y) = S2 x y := by
  rw [S2, S2, T_perm, T_perm, perm_inner]

theorem S_perm (e : Fin 3 ≃ Fin 3) (x : Alb) : S (perm e x) = S x := by
  rw [S, S, T_perm, perm_inner]

theorem sharp_perm (e : Fin 3 ≃ Fin 3) (x : Alb) : perm e (sharp x) = sharp (perm e x) := by
  rw [sharp, sharp, perm_add, perm_sub, perm_smul, perm_smul, perm_mul, perm_one, T_perm, S_perm]

theorem perm_Phi (e : Fin 3 ≃ Fin 3) (x y : Alb) :
    perm e (Phi x y) = Phi (perm e x) (perm e y) := by
  rw [Phi, Phi]
  simp only [perm_add, perm_sub, perm_smul, perm_mul, perm_one, T_perm, S_perm, S2_perm,
    ← sharp_perm, perm_inner]

theorem Phi_apply (e : Fin 3 ≃ Fin 3) (x y : Alb) (i j : Fin 3) :
    (Phi x y).mat (e i) (e j) = (Phi (perm e x) (perm e y)).mat i j := by
  rw [← perm_Phi, perm_mat, submatrix_apply]

theorem Phi_11 (x y : Alb) : ((Phi x y).mat 1 1).fst.re = 0 := by
  have h := Phi_apply (Equiv.swap 0 1) x y 0 0
  simp only [Equiv.swap_apply_left] at h
  rw [h]; exact Phi_00 _ _

theorem Phi_22 (x y : Alb) : ((Phi x y).mat 2 2).fst.re = 0 := by
  have h := Phi_apply (Equiv.swap 0 2) x y 0 0
  simp only [Equiv.swap_apply_left] at h
  rw [h]; exact Phi_00 _ _

theorem Phi_12 (x y : Alb) : (Phi x y).mat 1 2 = 0 := by
  have h := Phi_apply ((Equiv.swap 0 1).trans (Equiv.swap 0 2)) x y 0 1
  have e0 : ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 0 2)) 0 = 1 := by decide
  have e1 : ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 0 2)) 1 = 2 := by decide
  rw [e0, e1] at h
  rw [h]; exact Phi_01 _ _

theorem Phi_02 (x y : Alb) : (Phi x y).mat 0 2 = 0 := by
  have h := Phi_apply (Equiv.swap 1 2) x y 0 1
  have e0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
  have e1 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
  rw [e0, e1] at h
  rw [h]; exact Phi_01 _ _

/-- The linearised Hamilton–Cayley identity of `M_3(𝕆)^sa`:
`y ∘ x² + 2 x ∘ (x ∘ y) − T y · x² − 2 T x · (x ∘ y) + S(x; y) · x + S x · y
= ⟨x^#, y⟩ · 1`. -/
theorem Phi_eq_zero (x y : Alb) : Phi x y = 0 :=
  alb_eq_zero _ (Phi_00 x y) (Phi_11 x y) (Phi_22 x y) (Phi_01 x y) (Phi_12 x y) (Phi_02 x y)

/-! ### From the linearised identity to the Jordan identity -/

theorem T_mul (x y : Alb) : T (x * y) = ⟪x, y⟫_ℝ := by
  rw [T, inner_mul', mul_one', real_inner_comm]

theorem inner_one (y : Alb) : ⟪(1 : Alb), y⟫_ℝ = T y := by
  rw [T, real_inner_comm]

theorem S2_self (x : Alb) : S2 x x = 2 * S x := by
  rw [S2, S]; ring

/-- `x² ∘ y`, solved from the linearised identity. -/
theorem sq_mul (x y : Alb) :
    (x * x) * y = -(2 : ℝ) • (x * (x * y)) + T y • (x * x) + (2 * T x) • (x * y) - S2 x y • x
      - S x • y + ⟪sharp x, y⟫_ℝ • (1 : Alb) := by
  have h := Phi_eq_zero x y
  rw [Phi, mul_comm' y] at h
  rw [← sub_eq_zero, ← h]
  module

/-- **The cubic (Hamilton–Cayley) identity** of `M_3(𝕆)^sa`:
`x ∘ x² = T x · x² − S x · x + N x · 1`. -/
theorem cubic (x : Alb) : x * (x * x) = T x • (x * x) - S x • x + N x • (1 : Alb) := by
  have h := Phi_eq_zero x x
  rw [Phi, S2_self, mul_comm' x (x * x)] at h
  have h3 : (3 : ℝ) • ((x * x) * x - (T x • (x * x) - S x • x + N x • (1 : Alb))) = 0 := by
    rw [← h, N]; module
  rw [mul_comm' x (x * x)]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_left (by norm_num))

/-- `x ∘ x^# = N x · 1`. -/
theorem mul_sharp (x : Alb) : x * sharp x = N x • (1 : Alb) := by
  rw [sharp, mul_add', mul_sub', mul_smul', mul_smul', mul_one', cubic]; module

theorem inner_sharp (x y : Alb) :
    ⟪sharp x, y⟫_ℝ = ⟪x * x, y⟫_ℝ - T x * ⟪x, y⟫_ℝ + S x * T y := by
  rw [sharp, inner_add_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    inner_one]

/-- **EJA 3** (main.tex:212, Example), the octonionic case: the Jordan identity
`(x ∘ y) ∘ x² = x ∘ (y ∘ x²)` of `M_3(𝕆)^sa`, from the linearised
Hamilton–Cayley identity (`sq_mul`) and the cubic identity (`cubic`). -/
theorem jordan (x y : Alb) : (x * y) * (x * x) = x * (y * (x * x)) := by
  rw [mul_comm' (x * y), mul_comm' y, sq_mul x (x * y), sq_mul x y]
  simp only [mul_add', mul_sub', mul_smul', mul_one']
  rw [cubic, T_mul, inner_sharp x (x * y), inner_sharp x y, S2, S2, T_mul]
  have e1 : ⟪x, x * y⟫_ℝ = ⟪x * x, y⟫_ℝ := (inner_mul' x x y).symm
  have e2 : ⟪x * x, x * y⟫_ℝ - T x * ⟪x, x * y⟫_ℝ + S x * T (x * y) = N x * T y := by
    rw [← inner_sharp, ← inner_mul', mul_sharp, real_inner_smul_left, inner_one]
  rw [T_mul] at e2
  rw [e1] at e2 ⊢
  rw [show ⟪x * x, x * y⟫_ℝ = N x * T y + T x * ⟪x * x, y⟫_ℝ - S x * ⟪x, y⟫_ℝ by linarith]
  module

end Albert

open Albert in
/-- **EJA 3** (main.tex:212, Example), second paragraph: the exceptional
algebra `M_3(𝕆)^sa` of Hermitian `3 × 3` octonion matrices, with
`A ∘ B = ½ (AB + BA)`, `⟨A, B⟩ = re tr (AB)` and the identity matrix as unit,
is a Euclidean Jordan algebra.  The Jordan identity is `Albert.jordan`; the
other axioms are `hermMat_paperEJA_of_jordan`. -/
instance albert_isEJA : PaperEJA (HermMat 3 Oct) :=
  exceptional_of_jordan Albert.jordan

end Papers.EJA
