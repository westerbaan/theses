/-
Papers/EJA/Prelim.lean

EJA §2 (Preliminaries), points 1–13: A. Westerbaan, B. Westerbaan,
J. van de Wetering, *Pure Maps between Euclidean Jordan Algebras*, QPL 2018,
arXiv:1805.11496, `../papers/1805.11496/main.tex`.

Design (see `Papers/EJA/PLAN.md` §0):
* The paper's Euclidean Jordan algebra (EJA 1) is a *possibly
  infinite-dimensional* real Hilbert space with a unital commutative Jordan
  product and `⟨a * b, c⟩ = ⟨b, a * c⟩`.  It is `PaperEJA` below, a Prop-mixin
  over Mathlib's `InnerProductSpace ℝ E` and `CompleteSpace E`.  A
  finite-dimensional `PaperEJA` is a Euclidean Jordan algebra in the sense of
  the theses tree (`Theses.B.Eff.EuclideanJordanAlgebra`, finite-dimensional
  and formally real, ordered by the cone of sums of squares):
  `PaperEJA.isEJA`, through the tree's `ofForm`.
* Points 5–13 are stated over the tree's class, i.e. in finite dimension; that
  is the recorded deviation of every audit row here.  Where the paper uses the
  inner product, the statements take an **arbitrary** symmetric, associative,
  positive definite bilinear form (`EJAForm`), which is exactly what the inner
  product of a finite-dimensional `PaperEJA` is (`PaperEJA.form`); the trace
  form of the tree is one instance (`EJAForm.trace`).
* EJA 9.4 is false as printed for arbitrary `a, b` — the counterexample lives
  in a spin factor (EJA 4) and is `quadraticrep_4_false`; the true statement,
  for positive `a, b`, is `eja_Q_eq_zero_iff_mul_eq_zero`.
-/
import Theses.B.Eff.JordanAlgebras

namespace Papers.EJA

open Theses.B.Eff Theses.B.Eff.EuclideanJordanAlgebra
open scoped InnerProductSpace

universe u

/-! ## EJA 1: the paper's definition -/

/-- **EJA 1** (main.tex:194, Definition): a *Jordan algebra* `(E, *, 1)` is a
real unital commutative (possibly non-associative) algebra satisfying the
Jordan identity `(a * b) * (a * a) = a * (b * (a * a))`; it is a *Euclidean
Jordan algebra* when it carries an inner product making it a real Hilbert space
with `⟨a * b, c⟩ = ⟨b, a * c⟩`.

The Hilbert space is Mathlib's `InnerProductSpace ℝ E` with `CompleteSpace E`;
the algebra structure is a bilinear commutative product with a unit.  No
finite-dimensionality is assumed (EJA 2). -/
class PaperEJA (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [Mul E] [One E] : Prop where
  /-- the product is commutative -/
  mul_comm : ∀ a b : E, a * b = b * a
  /-- ... additive in the second (hence either) argument -/
  mul_add : ∀ a b c : E, a * (b + c) = a * b + a * c
  /-- ... and real-homogeneous -/
  smul_mul : ∀ (r : ℝ) (a b : E), (r • a) * b = r • (a * b)
  /-- `1` is a unit -/
  one_mul : ∀ a : E, 1 * a = a
  /-- the Jordan identity -/
  jordan : ∀ a b : E, (a * b) * (a * a) = a * (b * (a * a))
  /-- the inner product is associative -/
  inner_mul : ∀ a b c : E, ⟪a * b, c⟫_ℝ = ⟪b, a * c⟫_ℝ

/-! ## Associative forms on a (tree) Euclidean Jordan algebra -/

section Form

variable (V : Type u) [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- An **associative inner product** on a Euclidean Jordan algebra of the tree:
a symmetric, positive definite bilinear form with `B (x * y) z = B y (x * z)`.
In finite dimension this is exactly the inner product of EJA 1 (a
finite-dimensional inner product space is complete); `PaperEJA.form` is the
bridge, and the trace form of the tree is one instance (`EJAForm.trace`). -/
structure EJAForm where
  /-- the form -/
  B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  /-- it is symmetric -/
  symm : ∀ x y : V, B x y = B y x
  /-- it is associative -/
  assoc : ∀ x y z : V, B (x * y) z = B y (x * z)
  /-- it is positive definite -/
  pos : ∀ x : V, x ≠ 0 → 0 < B x x

/-- The trace form `B x y = tr L (x * y)` of the tree is an associative inner
product. -/
noncomputable def EJAForm.trace : EJAForm V where
  B := ejaBl V
  symm x y := ejaB_symm x y
  assoc x y z := ejaB_assoc x y z
  pos _ hx := ejaB_self_pos hx

end Form

/-! ## The bridge: a finite-dimensional `PaperEJA` is a Euclidean Jordan
algebra of the tree -/

section Bridge

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [Mul E] [One E] [PaperEJA E]

theorem PaperEJA.formallyReal :
    ∀ {a s : E}, IsSumSq s → a * a + s = 0 → a = 0 :=
  formallyReal_of_form (innerₗ E) (fun x y z => PaperEJA.inner_mul x y z)
    (fun a => (PaperEJA.mul_comm a 1).trans (PaperEJA.one_mul a))
    (fun x => real_inner_self_nonneg) (fun x h => inner_self_eq_zero.mp h)

/-- The order of a `PaperEJA`: the cone of sums of squares (EJA 5 calls the
squares positive; that the two cones agree is the tree's
`eja_nonneg_iff_exists_sq`, restated as `paper_nonneg_iff` below). -/
def PaperEJA.order : PartialOrder E :=
  sumSqPartialOrder E (mul_zero_of_mul_add PaperEJA.mul_add 0)
    (PaperEJA.formallyReal E)

/-- **EJA 1 and EJA 2** (main.tex:194 and 205, Definition and Note): a
*finite-dimensional* Euclidean Jordan algebra in the paper's sense is one in the
classical sense the theses tree uses — Note 2's remark that the original
definition additionally requires finite dimension.  Through the tree's
`ofForm`, the inner product being an associative positive definite form. -/
theorem PaperEJA.isEJA [FiniteDimensional ℝ E] :
    @EuclideanJordanAlgebra E _ _ _ _ (PaperEJA.order E) :=
  EuclideanJordanAlgebra.ofForm E PaperEJA.mul_comm PaperEJA.mul_add
    PaperEJA.smul_mul PaperEJA.one_mul PaperEJA.jordan inferInstance (innerₗ E)
    (fun x y z => PaperEJA.inner_mul x y z) (fun x => real_inner_self_nonneg)
    (fun x h => inner_self_eq_zero.mp h)

/-- The inner product of a finite-dimensional `PaperEJA` is an associative
inner product in the sense of `EJAForm`. -/
noncomputable def PaperEJA.form [FiniteDimensional ℝ E] :
    letI := PaperEJA.order E
    haveI := PaperEJA.isEJA E
    EJAForm E :=
  letI := PaperEJA.order E
  haveI := PaperEJA.isEJA E
  { B := innerₗ E
    symm := fun x y => real_inner_comm y x
    assoc := fun x y z => PaperEJA.inner_mul x y z
    pos := fun x hx => real_inner_self_pos.mpr hx }

end Bridge

/-! ## EJA 4: spin factors -/

section Spin

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The **spin factor** `H ⊕ ℝ` of a real inner product space `H`, with the
`ℓ²` inner product `⟨(a,t),(b,s)⟩ = ⟨a,b⟩ + t s`. -/
abbrev SpinFactor : Type u := WithLp 2 (H × ℝ)

variable {H}

/-- `(a,t) * (b,s) = (s a + t b, ⟨a,b⟩ + t s)`. -/
noncomputable instance : Mul (SpinFactor H) where
  mul x y := WithLp.toLp 2 (y.snd • x.fst + x.snd • y.fst, ⟪x.fst, y.fst⟫_ℝ + x.snd * y.snd)

noncomputable instance : One (SpinFactor H) where
  one := WithLp.toLp 2 (0, 1)

@[simp] theorem spin_mul_fst (x y : SpinFactor H) :
    (x * y).fst = y.snd • x.fst + x.snd • y.fst := rfl

@[simp] theorem spin_mul_snd (x y : SpinFactor H) :
    (x * y).snd = ⟪x.fst, y.fst⟫_ℝ + x.snd * y.snd := rfl

@[simp] theorem spin_one_fst : (1 : SpinFactor H).fst = 0 := rfl

@[simp] theorem spin_one_snd : (1 : SpinFactor H).snd = 1 := rfl

theorem spin_ext {x y : SpinFactor H} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) :
    x = y := by
  rw [WithLp.ext_iff]
  exact Prod.ext h1 h2

theorem spin_inner (x y : SpinFactor H) :
    ⟪x, y⟫_ℝ = ⟪x.fst, y.fst⟫_ℝ + x.snd * y.snd := by
  rw [WithLp.prod_inner_apply]
  simp [mul_comm]

/-- **EJA 4** (main.tex:227, Example): for any real Hilbert space `H` (possibly
infinite-dimensional) the spin factor `H ⊕ ℝ` with
`(a,t) * (b,s) = (s a + t b, ⟨a,b⟩ + t s)` and
`⟨(a,t),(b,s)⟩ = ⟨a,b⟩ + t s` is a Euclidean Jordan algebra. -/
instance spinFactor_paperEJA [CompleteSpace H] : PaperEJA (SpinFactor H) where
  mul_comm x y := spin_ext (by simp [add_comm]) (by simp [real_inner_comm, mul_comm])
  mul_add x y z := spin_ext
    (by simp only [spin_mul_fst, WithLp.add_fst, WithLp.add_snd]; module)
    (by simp only [spin_mul_snd, WithLp.add_fst, WithLp.add_snd, inner_add_right]; ring)
  smul_mul r x y := spin_ext
    (by simp only [spin_mul_fst, WithLp.smul_fst, WithLp.smul_snd]; module)
    (by simp only [spin_mul_snd, WithLp.smul_fst, WithLp.smul_snd, real_inner_smul_left,
          smul_eq_mul]; ring)
  one_mul x := spin_ext (by simp) (by simp)
  jordan x y := by
    refine spin_ext ?_ ?_
    · simp only [spin_mul_fst, spin_mul_snd, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm y.fst x.fst]
      module
    · simp only [spin_mul_fst, spin_mul_snd, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm y.fst x.fst]
      ring
  inner_mul x y z := by
    simp only [spin_inner, spin_mul_fst, spin_mul_snd, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm y.fst x.fst]
    ring

end Spin

/-! ## EJA 8: the quadratic representation, for any bilinear product -/

section Quad

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V]

/-- **EJA 8** (main.tex:308, Definition): the *quadratic representation*
`Q_a = 2 L_a² − L_{a²}`, i.e. `Q_a b = 2 a * (a * b) − (a * a) * b`, as a plain
function (for the paper's EJAs, which need not be the tree's).  On a Euclidean
Jordan algebra of the tree it is the tree's `ejaU` (`quadRep_eq_ejaU`). -/
def quadRep (a b : V) : V := (2 : ℝ) • (a * (a * b)) - (a * a) * b

end Quad

theorem quadRep_eq_ejaU {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
    [PartialOrder V] [EuclideanJordanAlgebra V] (a b : V) :
    quadRep a b = ejaU a b := (ejaU_apply a b).symm

/-! ## EJA 9.4 is false as printed -/

section Counterexample

/-- The spin factor `ℝ² ⊕ ℝ` (`≅ M₂(ℝ)^sa`). -/
abbrev Spin2 : Type := SpinFactor (EuclideanSpace ℝ (Fin 2))

/-- **EJA 9.4 is false as printed** (`prop:quadraticrep`, main.tex:323,
Proposition, item 4: "for any EJA `E` and `a, b ∈ E`,
`Q_a b = 0 ⟺ Q_b a = 0 ⟺ a * b = 0`").  In the spin factor `ℝ² ⊕ ℝ` take the
idempotent `a = (e₁/2, 1/2)` and `b = (e₂, 0)`: then `Q_a b = 0`, while
`a * b = (e₂/2, 0) ≠ 0` and `Q_b a = (−e₁/2, 1/2) ≠ 0`.  (In `M₂(ℝ)^sa`:
`a = diag(1,0)` and `b` the flip, `aba = 0 ≠ ½(ab + ba)`.)  The cited
Alfsen–Shultz Lemma 1.26 is for *positive* `a, b`, the only case the paper
uses; that corrected statement is `eja_Q_eq_zero_iff_mul_eq_zero`. -/
theorem quadraticrep_4_false :
    ∃ a b : Spin2, quadRep a b = 0 ∧ a * b ≠ 0 ∧ quadRep b a ≠ 0 := by
  set e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1 with he₁
  set e₂ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1 with he₂
  have h11 : ⟪e₁, e₁⟫_ℝ = 1 := by simp [he₁]
  have h22 : ⟪e₂, e₂⟫_ℝ = 1 := by simp [he₂]
  have h12 : ⟪e₁, e₂⟫_ℝ = 0 := by
    rw [he₁, EuclideanSpace.inner_single_left]; simp [he₂]
  have h21 : ⟪e₂, e₁⟫_ℝ = 0 := by
    rw [he₂, EuclideanSpace.inner_single_left]; simp [he₁]
  have he₂ne : e₂ ≠ 0 := by
    intro h
    have := h22
    rw [h, inner_zero_left] at this
    exact zero_ne_one this
  refine ⟨WithLp.toLp 2 ((2 : ℝ)⁻¹ • e₁, (2 : ℝ)⁻¹), WithLp.toLp 2 (e₂, 0), ?_, ?_, ?_⟩
  · refine spin_ext ?_ ?_
    · simp only [quadRep, WithLp.sub_fst, WithLp.smul_fst, spin_mul_fst, spin_mul_snd,
        WithLp.toLp_fst, WithLp.toLp_snd, real_inner_smul_left, real_inner_smul_right,
        h12, h11, WithLp.zero_fst]
      module
    · simp only [quadRep, WithLp.sub_snd, WithLp.smul_snd, spin_mul_fst, spin_mul_snd,
        WithLp.toLp_fst, WithLp.toLp_snd, inner_add_right, inner_add_left, real_inner_smul_left,
        real_inner_smul_right, WithLp.zero_snd, inner_zero_right, inner_zero_left,
        smul_eq_mul]
      simp only [real_inner_smul_right, real_inner_smul_left, h12, h11]
      ring
  · intro h
    have h2 := congrArg WithLp.fst h
    simp only [spin_mul_fst, WithLp.toLp_fst, WithLp.toLp_snd, WithLp.zero_fst] at h2
    apply he₂ne
    have h3 : (2 : ℝ)⁻¹ • e₂ = 0 := by rw [← h2]; module
    rcases smul_eq_zero.mp h3 with h4 | h4
    · norm_num at h4
    · exact h4
  · intro h
    have h2 := congrArg WithLp.snd h
    simp only [quadRep, WithLp.sub_snd, WithLp.smul_snd, spin_mul_fst, spin_mul_snd,
      WithLp.toLp_fst, WithLp.toLp_snd, inner_add_right, inner_add_left, real_inner_smul_left,
      real_inner_smul_right, WithLp.zero_snd, inner_zero_right,
      inner_zero_left, smul_eq_mul] at h2
    rw [h22] at h2
    norm_num at h2

end Counterexample

/-! ## EJA 5–8: positivity, maps, states, effects, the cone

From here on, `V` is a Euclidean Jordan algebra of the tree (finite
dimensional), and `F` an associative inner product on it. -/

section Tree

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- **EJA 5** (main.tex:244, Definition): `a` is *positive*, `a ≥ 0`, when it is
a square `a = b * b`; and `a ≥ c` when `a - c ≥ 0`.  The tree orders a
Euclidean Jordan algebra by the cone of *sums* of squares; that this is the
cone of squares is the tree's `eja_nonneg_iff_exists_sq`. -/
theorem paper_nonneg_iff (a : V) : 0 ≤ a ↔ ∃ b : V, a = b * b :=
  eja_nonneg_iff_exists_sq a

/-- **EJA 5**, the order: `c ≤ a` iff `a - c ≥ 0`. -/
theorem paper_le_iff (a c : V) : c ≤ a ↔ 0 ≤ a - c := eja_sub_nonneg.symm

/-- **EJA 5**, maps: a linear map between Euclidean Jordan algebras is
*positive* when it maps positive elements to positive elements. -/
def IsPositiveMap {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W]
    (f : V →ₗ[ℝ] W) : Prop := ∀ a : V, 0 ≤ a → 0 ≤ f a

/-- **EJA 5**, the category `EJA_psu`: its morphisms, the tree's `EJAPSUMap`,
are exactly the positive subunital (`f 1 ≤ 1`) linear maps. -/
def ejapsuMapEquiv (A B : EJAPsu.{u}) :
    EJAPSUMap A B ≃ {f : A.carrier →ₗ[ℝ] B.carrier // IsPositiveMap f ∧ f 1 ≤ 1} where
  toFun f := ⟨f.toLinearMap, f.map_nonneg', f.map_subunital'⟩
  invFun f := ⟨f.1, f.2.1, f.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **EJA 6** (main.tex:262, Definition): a *state* is a positive unital linear
functional. -/
def IsState (ω : V →ₗ[ℝ] ℝ) : Prop := (∀ a : V, 0 ≤ a → 0 ≤ ω a) ∧ ω 1 = 1

/-- **EJA 6**, effects: an effect is a positive subunital map `ℝ → E`, and
corresponds to an `a ∈ E` with `0 ≤ a ≤ 1`.  In the tree's partial-form
effectus `EJA_psuᵒᵖ` the effects of `A` (maps `A → I` there, i.e. positive
subunital `ℝ → A`) are the tree's `ejapsu_pred_val`. -/
noncomputable def effectEquiv (A : EJAPsu.{u}) := ejapsu_pred_val A

/-- **EJA 7** (`theor:chu`, main.tex:291, Theorem), first sentence: sums of
positive elements are positive, so the positive elements form a cone. -/
theorem chu_add_nonneg {a b : V} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  rw [eja_nonneg_iff] at ha hb ⊢
  exact ha.add hb

/-- **EJA 7.1**: `1` is a strong unit: `-n·1 ≤ a ≤ n·1` for some `n`. -/
theorem chu_strong_unit (a : V) : ∃ n : ℕ, -((n : ℝ) • (1 : V)) ≤ a ∧ a ≤ (n : ℝ) • 1 := by
  obtain ⟨n, hn⟩ := eja_exists_isSumSq_nsmul_one_sub a
  obtain ⟨m, hm⟩ := eja_exists_isSumSq_nsmul_one_sub (-a)
  refine ⟨n + m, ?_, ?_⟩
  · rw [eja_le_iff]
    have he : a - -(((n + m : ℕ) : ℝ) • (1 : V))
        = ((m : ℝ) • (1 : V) - -a) + (n : ℝ) • (1 : V) := by
      push_cast; rw [add_smul]; abel
    rw [he]
    exact hm.add (eja_isSumSq_smul_one (Nat.cast_nonneg n))
  · rw [eja_le_iff]
    have he : ((n + m : ℕ) : ℝ) • (1 : V) - a
        = ((n : ℝ) • (1 : V) - a) + (m : ℝ) • (1 : V) := by
      push_cast; rw [add_smul]; abel
    rw [he]
    exact hn.add (eja_isSumSq_smul_one (Nat.cast_nonneg m))

/-- **EJA 7.1**, the Archimedean half: if `a ≤ (1/n)·1` for all `n ≥ 1` then
`a ≤ 0`.  Read off the spectral decomposition (tree `eja_spectral`). -/
theorem chu_archimedean {a : V} (h : ∀ n : ℕ, 0 < n → a ≤ (1 / (n : ℝ)) • (1 : V)) :
    a ≤ 0 := by
  classical
  obtain ⟨s, e, hidem, horth, hne0, hsum, hdec⟩ := eja_spectral a
  have hone : ∀ c : ℝ, c • (1 : V) - a = ∑ l ∈ s, (c - l) • e l := by
    intro c
    conv_lhs => rw [← hsum, hdec, Finset.smul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [sub_smul]
  have hl : ∀ l ∈ s, l ≤ 0 := by
    intro l hl
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / l)
    have hn0 : 0 < n := by
      have : (0 : ℝ) < n := lt_trans (by positivity) hn
      exact_mod_cast this
    have h1 := h n hn0
    rw [eja_le_iff, hone] at h1
    have h2 := (eja_ortho_isSumSq_iff hidem horth hne0 (fun l => 1 / (n : ℝ) - l)).mp h1 l hl
    have h3 : 1 / (n : ℝ) < l := by
      rw [div_lt_iff₀ (by exact_mod_cast hn0)]
      rw [div_lt_iff₀ hlt] at hn
      linarith
    linarith
  rw [eja_le_iff, zero_sub, hdec, ← Finset.sum_neg_distrib]
  have he : ∑ l ∈ s, -(l • e l) = ∑ l ∈ s, (-l) • e l :=
    Finset.sum_congr rfl fun l _ => by rw [neg_smul]
  rw [he, eja_ortho_isSumSq_iff hidem horth hne0 (fun l => -l)]
  intro l hl'
  linarith [hl l hl']

/-- **EJA 7.2**: a Euclidean Jordan algebra is an order unit space with unit
`1` (the tree's `toOrderUnitSpace`, whose order-unit axiom is
`eja_exists_isSumSq_nsmul_one_sub`); the order unit norm of 7.2 and the norm
comparison of 7.3 are EJA 49, planned in `Appendix.lean`. -/
noncomputable def chu_orderUnitSpace : OrderUnitSpace V := toOrderUnitSpace V

/-- **EJA 8** (main.tex:308, Definition): `L_a b = a * b` and
`Q_a = 2 L_a² − L_{a²}`; in the tree `ejaLm` and `ejaU`. -/
theorem ejaU_eq_L (a : V) : ejaU a = (2 : ℝ) • (ejaLm a * ejaLm a) - ejaLm (a * a) := rfl

end Tree

/-! ## Associative inner products: self-adjointness and self-duality -/

section FormLemmas

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V] (F : EJAForm V)

namespace EJAForm

theorem mul_left (a x y : V) : F.B (a * x) y = F.B x (a * y) := F.assoc a x y

theorem mul_right (a x y : V) : F.B x (a * y) = F.B (a * x) y := (F.assoc a x y).symm

theorem self_nonneg (x : V) : 0 ≤ F.B x x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (F.pos x hx).le

theorem eq_zero_of_self (x : V) (h : F.B x x = 0) : x = 0 := by
  by_contra hx
  have := F.pos x hx
  linarith

/-- **EJA 9.3** (`prop:quadraticrep`, main.tex:323, Proposition, item 3):
`⟨Q_a b, c⟩ = ⟨b, Q_a c⟩`, for any associative inner product. -/
theorem U_self_adj (a b c : V) : F.B (ejaU a b) c = F.B b (ejaU a c) := by
  simp only [ejaU_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [F.mul_left, F.mul_left, F.mul_left, F.mul_right a b (a * c), F.mul_right (a * a) b c]

/-- The Peirce `1`-projection of an idempotent is `F`-self-adjoint. -/
theorem pone_self_adj (p x y : V) : F.B (ejaPone p x) y = F.B x (ejaPone p y) := by
  simp only [ejaPone_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [F.mul_left, F.mul_left, F.mul_left]

theorem phalf_self_adj (p x y : V) : F.B (ejaPhalf p x) y = F.B x (ejaPhalf p y) := by
  simp only [ejaPhalf_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [F.mul_left, F.mul_left, F.mul_left]

/-- `2 ⟨x, p * x⟩ = 2 ⟨P₁x, P₁x⟩ + ⟨P½x, P½x⟩` for an idempotent `p`:
`2 L_p = 2 P₁ + P½` with both projections `F`-self-adjoint idempotents. -/
theorem idem_apply_eq {p : V} (hp : p * p = p) (x : V) :
    (2 : ℝ) * F.B x (p * x)
      = 2 * F.B (ejaPone p x) (ejaPone p x) + F.B (ejaPhalf p x) (ejaPhalf p x) := by
  have h : (2 : ℝ) • (p * x) = (2 : ℝ) • ejaPone p x + ejaPhalf p x := by
    have hpe := congrArg (fun f : V →ₗ[ℝ] V => f x) (ejaLm_eq_peirce (V := V) p)
    simpa using hpe
  have h1 : F.B x (ejaPone p x) = F.B (ejaPone p x) (ejaPone p x) := by
    conv_lhs => rw [← (show ejaPone p (ejaPone p x) = ejaPone p x from
      congrArg (fun f : V →ₗ[ℝ] V => f x) (ejaPone_idem p hp))]
    rw [← F.pone_self_adj]
  have h2 : F.B x (ejaPhalf p x) = F.B (ejaPhalf p x) (ejaPhalf p x) := by
    conv_lhs => rw [← (show ejaPhalf p (ejaPhalf p x) = ejaPhalf p x from
      congrArg (fun f : V →ₗ[ℝ] V => f x) (ejaPhalf_idem p hp))]
    rw [← F.phalf_self_adj]
  have h3 : (2 : ℝ) * F.B x (p * x)
      = 2 * F.B x (ejaPone p x) + F.B x (ejaPhalf p x) := by
    have := congrArg (F.B x) h
    simpa [map_add, map_smul] using this
  rw [h3, h1, h2]

/-- `0 ≤ ⟨x, p * x⟩` for an idempotent `p`. -/
theorem idem_apply_nonneg {p : V} (hp : p * p = p) (x : V) : 0 ≤ F.B x (p * x) := by
  have h := F.idem_apply_eq hp x
  have := F.self_nonneg (ejaPone p x)
  have := F.self_nonneg (ejaPhalf p x)
  nlinarith

/-- A positive element pairs non-negatively with an idempotent. -/
theorem nonneg_idem {a : V} (ha : 0 ≤ a) {p : V} (hp : p * p = p) : 0 ≤ F.B a p := by
  obtain ⟨b, rfl⟩ := (eja_nonneg_iff_exists_sq a).mp ha
  rw [F.mul_left, eja_mul_comm b p]
  exact F.idem_apply_nonneg hp b

theorem sum_left {ι : Type*} (t : Finset ι) (f : ι → V) (y : V) :
    F.B (∑ i ∈ t, f i) y = ∑ i ∈ t, F.B (f i) y := by
  rw [map_sum, LinearMap.sum_apply]

theorem sum_right {ι : Type*} (t : Finset ι) (x : V) (f : ι → V) :
    F.B x (∑ i ∈ t, f i) = ∑ i ∈ t, F.B x (f i) := map_sum _ _ _

/-- The inner product of two positive elements is non-negative. -/
theorem nonneg_nonneg {a c : V} (ha : 0 ≤ a) (hc : 0 ≤ c) : 0 ≤ F.B a c := by
  classical
  obtain ⟨s, e, hidem, horth, hne0, _, hdec⟩ := eja_spectral c
  have hl : ∀ l ∈ s, 0 ≤ l := by
    refine (eja_ortho_isSumSq_iff hidem horth hne0 (fun r => r)).mp ?_
    rw [← hdec]; exact (eja_nonneg_iff c).mp hc
  rw [hdec, F.sum_right]
  refine Finset.sum_nonneg fun l hl' => ?_
  rw [map_smul, smul_eq_mul]
  exact mul_nonneg (hl l hl') (F.nonneg_idem ha (hidem l hl'))

/-- Orthogonal idempotents are `F`-orthogonal. -/
theorem idem_orth {p q : V} (hp : p * p = p) (h : p * q = 0) : F.B p q = 0 := by
  rw [← hp, F.mul_left, h, map_zero]

/-- The coefficient of a spectral decomposition, read off by `F`. -/
theorem ortho_coeff {s : Finset ℝ} {e : ℝ → V}
    (hidem : ∀ l ∈ s, e l * e l = e l)
    (horth : ∀ l ∈ s, ∀ k ∈ s, l ≠ k → e l * e k = 0) (c : ℝ → ℝ) {l : ℝ} (hl : l ∈ s) :
    F.B (∑ k ∈ s, c k • e k) (e l) = c l * F.B (e l) (e l) := by
  classical
  rw [F.sum_left, Finset.sum_eq_single l]
  · rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  · intro k hk hkl
    rw [map_smul, LinearMap.smul_apply, F.idem_orth (hidem k hk) (horth k hk l hl hkl),
      smul_zero]
  · intro h; exact absurd hl h

/-- **EJA 7.4** (`theor:chu`, main.tex:291, item 4): **the cone is self-dual**,
`a ≥ 0` iff `⟨a, b⟩ ≥ 0` for every `b ≥ 0` — for any associative inner
product. -/
theorem selfDual (a : V) : 0 ≤ a ↔ ∀ b : V, 0 ≤ b → 0 ≤ F.B a b := by
  classical
  constructor
  · intro ha b hb
    exact F.nonneg_nonneg ha hb
  · intro h
    obtain ⟨s, e, hidem, horth, hne0, _, hdec⟩ := eja_spectral a
    rw [hdec, eja_nonneg_iff, eja_ortho_isSumSq_iff hidem horth hne0 (fun r => r)]
    intro l hl
    have h1 := h (e l) (eja_idem_nonneg (hidem l hl))
    rw [hdec, F.ortho_coeff hidem horth (fun r => r) hl] at h1
    have h2 := F.pos (e l) (hne0 l hl)
    exact nonneg_of_mul_nonneg_left h1 h2

end EJAForm

end FormLemmas

/-! ## EJA 9: the quadratic representation -/

section Quadratic

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- **EJA 9.1** (`prop:quadraticrep`, main.tex:323, Proposition, item 1):
`Q_1 = id` (tree `ejaU_one`). -/
theorem quadraticrep_1 : ejaU (1 : V) = LinearMap.id := ejaU_one

/-- **EJA 9.2** (`prop:quadraticrep`, item 2): `Q_a 1 = a²` (tree
`ejaU_apply_one`). -/
theorem quadraticrep_2 (a : V) : ejaU a 1 = a * a := ejaU_apply_one a

/-- **EJA 9.3** (`prop:quadraticrep`, item 3): `⟨Q_a b, c⟩ = ⟨b, Q_a c⟩` for
the associative inner product `F`.  (Also `EJAForm.U_self_adj`; for the trace
form it is the tree's `ejaB_U_self_adj`.) -/
theorem quadraticrep_3 (F : EJAForm V) (a b c : V) :
    F.B (ejaU a b) c = F.B b (ejaU a c) := F.U_self_adj a b c

/-- A combination of an orthogonal family of idempotents with non-negative
coefficients that is trace-orthogonal to a positive `b` annihilates `b`, and so
does every combination with the same zero coefficients. -/
theorem ortho_mul_eq_zero_of_ejaB {s : Finset ℝ} {e : ℝ → V}
    (hidem : ∀ l ∈ s, e l * e l = e l) {b : V} (hb : 0 ≤ b) (c g : ℝ → ℝ)
    (hc : ∀ l ∈ s, 0 ≤ c l) (hB : ejaB (∑ l ∈ s, c l • e l) b = 0)
    (hg : ∀ l ∈ s, c l = 0 → g l = 0) : (∑ l ∈ s, g l • e l) * b = 0 := by
  have hterm : ∀ l ∈ s, 0 ≤ c l * ejaB (e l) b := fun l hl =>
    mul_nonneg (hc l hl) (by
      rw [ejaB_symm]
      exact eja_isSumSq_ejaB_idem_nonneg ((eja_nonneg_iff b).mp hb) _ (hidem l hl))
  have hsum : ∑ l ∈ s, c l * ejaB (e l) b = 0 := by
    rw [← hB, ejaB_sum_left]
    exact Finset.sum_congr rfl fun l _ => (ejaB_smul_left _ _ _).symm
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum
  rw [eja_sum_mul]
  refine Finset.sum_eq_zero fun l hl => ?_
  rw [eja_smul_mul]
  rcases eq_or_ne (c l) 0 with h0 | h0
  · rw [hg l hl h0, zero_smul]
  · have hB0 : ejaB (e l) b = 0 := by
      rcases mul_eq_zero.mp (hz l hl) with h | h
      · exact absurd h h0
      · exact h
    rw [eja_idem_mul_nonneg_eq_zero (hidem l hl) hb hB0, smul_zero]

/-- For `a, b ≥ 0`: `Q_a b = 0 ⟺ a * b = 0`. -/
theorem eja_U_eq_zero_iff {a b : V} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ejaU a b = 0 ↔ a * b = 0 := by
  classical
  obtain ⟨s, e, hidem, horth, hne0, _, hdec⟩ := eja_spectral a
  have hl : ∀ l ∈ s, 0 ≤ l := by
    refine (eja_ortho_isSumSq_iff hidem horth hne0 (fun r => r)).mp ?_
    rw [← hdec]; exact (eja_nonneg_iff a).mp ha
  have hsq : a * a = ∑ l ∈ s, (l * l) • e l := by
    rw [hdec, eja_ortho_mul hidem horth]
  constructor
  · intro h
    have hB : ejaB (a * a) b = 0 := by
      rw [← ejaU_apply_one, ← ejaB_U_self_adj, h]
      simp [ejaB, eja_mul_zero]
    rw [hsq] at hB
    rw [hdec]
    exact ortho_mul_eq_zero_of_ejaB hidem hb (fun l => l * l) (fun l => l)
      (fun l _ => mul_self_nonneg l) hB (fun l _ h0 => mul_self_eq_zero.mp h0)
  · intro h
    have hB : ejaB (∑ l ∈ s, l • e l) b = 0 := by
      rw [← hdec]
      show ejaTrL (a * b) = 0
      rw [h, map_zero]
    have haa : (a * a) * b = 0 := by
      rw [hsq]
      exact ortho_mul_eq_zero_of_ejaB hidem hb (fun l => l) (fun l => l * l) hl hB
        (fun l _ h0 => by simp [h0])
    rw [ejaU_apply, h, haa, eja_mul_zero, smul_zero, sub_zero]

/-- **EJA 9.4, corrected** (`prop:quadraticrep`, item 4, for **positive**
`a, b` — the hypothesis of the cited Alfsen–Shultz Lemma 1.26, and the only case
the paper uses): `Q_a b = 0 ⟺ Q_b a = 0 ⟺ a * b = 0`.  As printed, for all
`a, b`, it is false: `quadraticrep_4_false`. -/
theorem eja_Q_eq_zero_iff_mul_eq_zero {a b : V} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (ejaU a b = 0 ↔ ejaU b a = 0) ∧ (ejaU b a = 0 ↔ a * b = 0) := by
  rw [eja_U_eq_zero_iff ha hb, eja_U_eq_zero_iff hb ha, eja_mul_comm b a]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **EJA 9.7** (`prop:quadraticrep`, item 7, first half): `Q_a` is a positive
operator for *every* `a`, not only positive `a` (tree `eja_U_nonneg'`).  The
second half ("if invertible, an order automorphism") rests on 9.6, not yet
formalised. -/
theorem quadraticrep_7 (a : V) {x : V} (hx : 0 ≤ x) : 0 ≤ ejaU a x := eja_U_nonneg' a hx

end Quadratic

/-! ## EJA 10–11: idempotents -/

section Idem

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- **EJA 10** (main.tex:356, Definition): an idempotent is automatically
positive and below the identity (tree `eja_idem_nonneg`, `eja_idem_le_one`). -/
theorem idem_nonneg_le_one {p : V} (hp : p * p = p) : 0 ≤ p ∧ p ≤ 1 :=
  ⟨eja_idem_nonneg hp, eja_idem_le_one hp⟩

/-- **EJA 10**, atomic idempotents: `p` is *atomic* when there is no non-zero
idempotent strictly below it.  Literally, as printed, `0` is atomic; for
`p ≠ 0` this is the tree's `EJAPrimitive` (`isAtomic_iff_primitive`). -/
def IsAtomic (p : V) : Prop :=
  p * p = p ∧ ∀ q : V, q * q = q → q ≤ p → q ≠ p → q = 0

/-- **EJA 10**, orthogonality: idempotents `p, q` are orthogonal, `p * q = 0`,
exactly when `⟨p, q⟩ = 0`, for any associative inner product. -/
theorem idem_orth_iff (F : EJAForm V) {p q : V} (hp : p * p = p) (hq : q * q = q) :
    p * q = 0 ↔ F.B p q = 0 := by
  constructor
  · exact F.idem_orth hp
  · intro h
    have h1 : F.B q (p * q) = 0 := by
      rw [F.mul_right, eja_mul_comm p q, F.mul_left, hq]; exact h
    have h2 := F.idem_apply_eq hp q
    rw [h1, mul_zero] at h2
    have h3 := F.self_nonneg (ejaPone p q)
    have h4 := F.self_nonneg (ejaPhalf p q)
    have h5 : F.B (ejaPone p q) (ejaPone p q) = 0 := by linarith
    have h6 : F.B (ejaPhalf p q) (ejaPhalf p q) = 0 := by linarith
    have h7 := F.eq_zero_of_self _ h5
    have h8 := F.eq_zero_of_self _ h6
    have h9 : (2 : ℝ) • (p * q) = (2 : ℝ) • ejaPone p q + ejaPhalf p q := by
      have hpe := congrArg (fun f : V →ₗ[ℝ] V => f q) (ejaLm_eq_peirce (V := V) p)
      simpa using hpe
    rw [h7, h8, smul_zero, add_zero] at h9
    rcases smul_eq_zero.mp h9 with h10 | h10
    · norm_num at h10
    · exact h10

/-- **EJA 11** (`prop:EJAidempotent`, main.tex:365, Proposition), first claim:
`Q_p` is idempotent (tree `ejaPone_idem`; the paper derives it from the
fundamental equality, which is not needed). -/
theorem idem_Q_idem {p : V} (hp : p * p = p) : ejaU p * ejaU p = ejaU p := by
  rw [ejaU_idem hp]; exact ejaPone_idem p hp

/-- **EJA 11**, second claim: for `a ≥ 0` (in particular an effect),
`Q_p a = 0 ⟺ ⟨a, p⟩ = 0`. -/
theorem idem_Q_eq_zero_iff (F : EJAForm V) {p : V} (hp : p * p = p) {a : V}
    (ha : 0 ≤ a) : ejaU p a = 0 ↔ F.B a p = 0 := by
  have hadj : F.B (ejaU p a) 1 = F.B a p := by
    rw [F.U_self_adj, ejaU_apply_one, hp]
  constructor
  · intro h
    rw [← hadj, h, map_zero, LinearMap.zero_apply]
  · intro h
    obtain ⟨c, hc⟩ := (eja_nonneg_iff_exists_sq _).mp (eja_U_nonneg' p ha)
    have h1 : F.B c c = 0 := by
      rw [← h, ← hadj, hc, F.mul_left, eja_mul_one]
    rw [hc, F.eq_zero_of_self c h1, eja_mul_zero]

/-- **EJA 11**, third claim (last equivalence): for an effect `a`,
`a ≤ p ⟺ p * a = a`.  The paper's argument: `⟨a, pᗮ⟩ = 0` by self-duality,
hence `Q_{pᗮ} a = 0`, hence `pᗮ * a = 0` (9.4, for positive elements). -/
theorem idem_le_iff_mul {p : V} (hp : p * p = p) {a : V} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    a ≤ p ↔ p * a = a := by
  have hq : (1 - p) * (1 - p) = 1 - p := eja_one_sub_idem hp
  constructor
  · intro h
    let F := EJAForm.trace V
    have hr : 0 ≤ p - a := eja_sub_nonneg.mpr h
    have hpq : F.B p (1 - p) = 0 := F.idem_orth hp (by
      rw [eja_mul_sub, eja_mul_one, hp, sub_self])
    have hsplit : F.B a (1 - p) + F.B (p - a) (1 - p) = F.B p (1 - p) := by
      rw [← LinearMap.add_apply, ← map_add, add_sub_cancel]
    have h1 := F.nonneg_idem ha0 hq
    have h2 := F.nonneg_idem hr hq
    have h3 : F.B a (1 - p) = 0 := by linarith
    have h4 : ejaU (1 - p) a = 0 := (idem_Q_eq_zero_iff F hq ha0).mpr h3
    have h5 : (1 - p) * a = 0 :=
      (eja_U_eq_zero_iff (eja_idem_nonneg hq) ha0).mp h4
    rw [eja_sub_mul, eja_one_mul, sub_eq_zero] at h5
    exact h5.symm
  · intro h
    have h1 : ejaU p a = a := by
      rw [ejaU_apply, h, h, hp, h]; module
    calc a = ejaU p a := h1.symm
      _ ≤ ejaU p 1 := eja_U_mono p ha1
      _ = p := by rw [ejaU_apply_one, hp]

/-- **EJA 11**, third claim (first equivalence): for an effect `a`,
`Q_p a = a ⟺ a ≤ p`. -/
theorem idem_Q_eq_self_iff {p : V} (hp : p * p = p) {a : V} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ejaU p a = a ↔ a ≤ p := by
  rw [idem_le_iff_mul hp ha0 ha1, ejaU_idem hp]
  exact eja_pone_eq_self_iff p hp a

/-- **EJA 10**, atomic = primitive: a non-zero idempotent is atomic exactly when
its Peirce `1`-space is a line (the tree's `EJAPrimitive`). -/
theorem isAtomic_iff_primitive {p : V} (hp0 : p ≠ 0) : IsAtomic p ↔ EJAPrimitive p := by
  constructor
  · rintro ⟨hp, hat⟩
    by_contra hnp
    obtain ⟨q, r, hq, hr, hqp, hrp, hsum, hqr, _⟩ := eja_idem_split hp hp0 hnp
    have hle : q ≤ p := by
      rw [eja_le_iff, hsum, add_sub_cancel_left, ← hr]
      exact IsSumSq.mul_self r
    have hq0 : q = 0 := hat q hq hle hqp
    apply hrp
    rw [hsum, hq0, zero_add]
  · intro hprim
    refine ⟨hprim.idem, fun q hq hle hne => ?_⟩
    have hmul : p * q = q :=
      (idem_le_iff_mul hprim.idem (eja_idem_nonneg hq) (eja_idem_le_one hq)).mp hle
    obtain ⟨r, hr⟩ := hprim.line q hmul
    have hrr : (r * r) • p = r • p := by
      have h := hq
      rw [hr, eja_smul_mul, eja_mul_smul, hprim.idem, smul_smul] at h
      exact h
    have hr2 : r * (r - 1) = 0 := by
      have h := sub_eq_zero.mpr hrr
      rw [← sub_smul] at h
      rcases smul_eq_zero.mp h with h' | h'
      · linarith
      · exact absurd h' hp0
    rcases mul_eq_zero.mp hr2 with h0 | h1
    · rw [hr, h0, zero_smul]
    · exact absurd (by rw [hr, sub_eq_zero.mp h1, one_smul]) hne

end Idem

/-! ## EJA 12: the spectral theorem with atomic idempotents -/

section Spectral

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- Every idempotent is a finite sum of pairwise orthogonal primitive
idempotents lying in its Peirce `1`-space: split a non-primitive idempotent
(tree `eja_idem_split`) and recurse on the dimension of the Peirce `1`-space,
which drops strictly (tree `eja_V1_lt`). -/
theorem idem_sum_primitive : ∀ (n : ℕ) (e : V), e * e = e →
    Module.finrank ℝ (ejaV1 e) ≤ n →
    ∃ (m : ℕ) (f : Fin m → V), (∀ i, EJAPrimitive (f i)) ∧
      (∀ i j, i ≠ j → f i * f j = 0) ∧ (∀ i, e * f i = f i) ∧ e = ∑ i, f i := by
  intro n
  induction n with
  | zero =>
    intro e he hn
    have hV : ejaV1 e = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn)
    have he0 : e = 0 := by
      have : e ∈ ejaV1 e := eja_mem_V1.mpr he
      rw [hV] at this
      exact (Submodule.mem_bot ℝ).mp this
    exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by simp [he0]⟩
  | succ n ih =>
    intro e he hn
    by_cases he0 : e = 0
    · exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        by simp [he0]⟩
    by_cases hprim : EJAPrimitive e
    · refine ⟨1, fun _ => e, fun _ => hprim, fun i j hij => absurd (Subsingleton.elim i j) hij,
        fun _ => he, by simp⟩
    obtain ⟨p, r, hp, hr, hpe, hre, hsum, hpr, hrp⟩ := eja_idem_split he he0 hprim
    have hltp : Module.finrank ℝ (ejaV1 p) < Module.finrank ℝ (ejaV1 e) :=
      Submodule.finrank_lt_finrank_of_lt (eja_V1_lt he hp hpr hsum hpe)
    have hltr : Module.finrank ℝ (ejaV1 r) < Module.finrank ℝ (ejaV1 e) :=
      Submodule.finrank_lt_finrank_of_lt
        (eja_V1_lt he hr hrp (by rw [hsum, add_comm]) hre)
    obtain ⟨m₁, f₁, hprim₁, horth₁, hmem₁, hsum₁⟩ := ih p hp (by omega)
    obtain ⟨m₂, f₂, hprim₂, horth₂, hmem₂, hsum₂⟩ := ih r hr (by omega)
    -- parts of `p` kill `r`, and parts of `r` kill `p`
    have hk₁ : ∀ i, f₁ i * r = 0 := fun i => eja_peirce_one_mul_zero hp (hmem₁ i) hpr
    have hk₂ : ∀ j, f₂ j * p = 0 := fun j => eja_peirce_one_mul_zero hr (hmem₂ j) hrp
    have hx : ∀ i j, f₁ i * f₂ j = 0 := by
      intro i j
      have h := eja_peirce_one_mul_zero hr (hmem₂ j)
        (show r * f₁ i = 0 by rw [eja_mul_comm]; exact hk₁ i)
      rw [eja_mul_comm]; exact h
    refine ⟨m₁ + m₂, Fin.append f₁ f₂, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hprim₁ i
      · rw [Fin.append_right]; exact hprim₂ j
    · intro i j hij
      induction i using Fin.addCases with
      | left i =>
        induction j using Fin.addCases with
        | left j =>
          rw [Fin.append_left, Fin.append_left]
          exact horth₁ i j (fun h => hij (by rw [h]))
        | right j => rw [Fin.append_left, Fin.append_right]; exact hx i j
      | right i =>
        induction j using Fin.addCases with
        | left j =>
          rw [Fin.append_right, Fin.append_left, eja_mul_comm]; exact hx j i
        | right j =>
          rw [Fin.append_right, Fin.append_right]
          exact horth₂ i j (fun h => hij (by rw [h]))
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [Fin.append_left, hsum, eja_add_mul, hmem₁ i, eja_mul_comm r, hk₁ i, add_zero]
      · rw [Fin.append_right, hsum, eja_add_mul, hmem₂ j, eja_mul_comm p, hk₂ j, zero_add]
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [← hsum₁, ← hsum₂, hsum]

/-- The spectral theorem with *primitive* idempotents summing to `1`. -/
theorem spectral_primitive (a : V) :
    ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℝ) (p : ι → V),
      (∀ i, EJAPrimitive (p i)) ∧ (∀ i j, i ≠ j → p i * p j = 0) ∧
      ∑ i, p i = 1 ∧ a = ∑ i, lam i • p i := by
  classical
  obtain ⟨s, e, hidem, horth, _, hsum, hdec⟩ := eja_spectral a
  have hdecomp : ∀ l : s, ∃ (m : ℕ) (f : Fin m → V), (∀ i, EJAPrimitive (f i)) ∧
      (∀ i j, i ≠ j → f i * f j = 0) ∧ (∀ i, e l * f i = f i) ∧ e l = ∑ i, f i :=
    fun l => idem_sum_primitive _ (e l) (hidem l l.2) le_rfl
  choose m f hprim horth' hmem hsum' using hdecomp
  refine ⟨Σ l : s, Fin (m l), inferInstance, fun x => (x.1 : ℝ), fun x => f x.1 x.2,
    fun x => hprim x.1 x.2, ?_, ?_, ?_⟩
  · rintro ⟨l, i⟩ ⟨k, j⟩ hne
    by_cases hlk : l = k
    · subst hlk
      exact horth' l i j (fun h => hne (by rw [h]))
    · have hlk' : (l : ℝ) ≠ k := fun h => hlk (Subtype.ext h)
      have hek : e l * e k = 0 := horth l l.2 k k.2 hlk'
      have h1 : f l i * e k = 0 := eja_peirce_one_mul_zero (hidem l l.2) (hmem l i) hek
      have h2 : f k j * f l i = 0 := eja_peirce_one_mul_zero (hidem k k.2) (hmem k j)
        (by rw [eja_mul_comm]; exact h1)
      show f l i * f k j = 0
      rw [eja_mul_comm]; exact h2
  · rw [Fintype.sum_sigma]
    simp_rw [← hsum']
    rw [Finset.sum_coe_sort s e, hsum]
  · rw [Fintype.sum_sigma]
    simp_rw [← Finset.smul_sum, ← hsum']
    rw [Finset.sum_coe_sort s (fun l => l • e l), ← hdec]

/-- **EJA 12** (main.tex:402, Proposition): every element is a real linear
combination `a = ∑ λᵢ pᵢ` of finitely many pairwise orthogonal atomic
idempotents.  The index is any finite type (the paper's `1, …, n`). -/
theorem spectral_atomic (a : V) :
    ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℝ) (p : ι → V),
      (∀ i, IsAtomic (p i)) ∧ (∀ i j, i ≠ j → p i * p j = 0) ∧ a = ∑ i, lam i • p i := by
  obtain ⟨ι, hι, lam, p, hprim, horth, _, hdec⟩ := spectral_primitive a
  exact ⟨ι, hι, lam, p, fun i => (isAtomic_iff_primitive (hprim i).ne_zero).mpr (hprim i),
    horth, hdec⟩

end Spectral

/-! ## EJA 13: ceiling and floor -/

section CeilFloor

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- `p` is the least idempotent above `a`. -/
def IsLeastIdemAbove (a p : V) : Prop :=
  p * p = p ∧ a ≤ p ∧ ∀ q : V, q * q = q → a ≤ q → p ≤ q

/-- `p` is the greatest idempotent below `a`. -/
def IsGreatestIdemBelow (a p : V) : Prop :=
  p * p = p ∧ p ≤ a ∧ ∀ q : V, q * q = q → q ≤ a → q ≤ p

theorem IsLeastIdemAbove.unique {a p p' : V} (h : IsLeastIdemAbove a p)
    (h' : IsLeastIdemAbove a p') : p = p' :=
  le_antisymm (h.2.2 p' h'.1 h'.2.1) (h'.2.2 p h.1 h.2.1)

open Classical in
/-- **EJA 13**, the ceiling `⌈a⌉`: the least idempotent above `a` (for an
effect `a` it exists, `ceil_spec`; elsewhere the value is junk `0`). -/
noncomputable def ejaCeil (a : V) : V :=
  if h : ∃ p, IsLeastIdemAbove a p then h.choose else 0

/-- **EJA 13**, the floor `⌊a⌋ = ⌈aᗮ⌉ᗮ`. -/
noncomputable def ejaFloor (a : V) : V := 1 - ejaCeil (1 - a)

theorem sum_idem_of_orth {ι : Type*} [Fintype ι] {p : ι → V} (hidem : ∀ i, p i * p i = p i)
    (horth : ∀ i j, i ≠ j → p i * p j = 0) (c : ι → ℝ) (j : ι) :
    (∑ i, c i • p i) * p j = c j • p j := by
  classical
  rw [eja_sum_mul, Finset.sum_eq_single j]
  · rw [eja_smul_mul, hidem]
  · intro i _ hij; rw [eja_smul_mul, horth i j hij, smul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- For an effect `a = ∑ λᵢ pᵢ` with `λᵢ > 0` and pairwise orthogonal
idempotents `pᵢ`, the sum `∑ pᵢ` is the least idempotent above `a` — the
paper's proof of EJA 13 (and it shows `⌈a⌉` does not depend on the
decomposition). -/
theorem sum_isLeastIdemAbove {ι : Type*} [Fintype ι] {lam : ι → ℝ} {p : ι → V}
    (hidem : ∀ i, p i * p i = p i) (horth : ∀ i j, i ≠ j → p i * p j = 0)
    (hpos : ∀ i, 0 < lam i) {a : V} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hdec : a = ∑ i, lam i • p i) : IsLeastIdemAbove a (∑ i, p i) := by
  classical
  let F := EJAForm.trace V
  have hS : (∑ j, p j) * (∑ j, p j) = ∑ j, p j := by
    rw [eja_mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := sum_idem_of_orth hidem horth (fun _ => 1) j
    simpa using this
  have hpa : ∀ i, p i * a = lam i • p i := fun i => by
    rw [eja_mul_comm, hdec]; exact sum_idem_of_orth hidem horth lam i
  have hB : ∀ i, F.B a (p i) = lam i * F.B (p i) (p i) := by
    intro i
    conv_lhs => rw [← hidem i]
    rw [F.mul_right, hpa i, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hB1 : ∀ i, F.B 1 (p i) = F.B (p i) (p i) := by
    intro i
    conv_lhs => rw [← hidem i]
    rw [F.mul_right, eja_mul_one]
  have hle1 : ∀ i, p i ≠ 0 → lam i ≤ 1 := by
    intro i hi
    have h1 := F.nonneg_idem (eja_sub_nonneg.mpr ha1) (hidem i)
    rw [map_sub, LinearMap.sub_apply, hB1, hB] at h1
    have h2 := F.pos (p i) hi
    nlinarith
  have hdiff : (∑ i, p i) - a = ∑ i, (1 - lam i) • p i := by
    rw [hdec, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [sub_smul, one_smul]
  have hle : a ≤ ∑ i, p i := by
    rw [← eja_sub_nonneg, hdiff]
    refine eja_sum_nonneg fun i _ => ?_
    rcases eq_or_ne (p i) 0 with h0 | h0
    · rw [h0, smul_zero]
    · rw [eja_nonneg_iff]
      exact eja_isSumSq_smul (by linarith [hle1 i h0])
        ((eja_nonneg_iff _).mp (eja_idem_nonneg (hidem i)))
  have hterm : ∀ j, 0 ≤ lam j • p j := fun j => (eja_nonneg_iff _).mpr
    (eja_isSumSq_smul (hpos j).le ((eja_nonneg_iff _).mp (eja_idem_nonneg (hidem j))))
  have hpi_le : ∀ i, lam i • p i ≤ a := by
    intro i
    rw [← eja_sub_nonneg, hdec, ← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      add_sub_cancel_right]
    exact eja_sum_nonneg fun j _ => hterm j
  refine ⟨hS, hle, fun q hq haq => ?_⟩
  have hqp : ∀ i, q * p i = p i := by
    intro i
    have h1 : q * (lam i • p i) = lam i • p i :=
      (idem_le_iff_mul hq (hterm i) (le_trans (hpi_le i) ha1)).mp (le_trans (hpi_le i) haq)
    rw [eja_mul_smul] at h1
    exact smul_right_injective V (hpos i).ne' h1
  refine (idem_le_iff_mul hq (eja_idem_nonneg hS) (eja_idem_le_one hS)).mpr ?_
  rw [eja_mul_sum]
  exact Finset.sum_congr rfl fun i _ => hqp i

/-- Any effect has a decomposition `a = ∑ λᵢ pᵢ` with `λᵢ > 0` and pairwise
orthogonal non-zero atomic idempotents `pᵢ` (first sentence of EJA 13). -/
theorem effect_decomp {a : V} (ha0 : 0 ≤ a) :
    ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℝ) (p : ι → V),
      (∀ i, 0 < lam i) ∧ (∀ i, EJAPrimitive (p i)) ∧ (∀ i j, i ≠ j → p i * p j = 0) ∧
      a = ∑ i, lam i • p i := by
  classical
  obtain ⟨ι, hι, lam, p, hprim, horth, _, hdec⟩ := spectral_primitive a
  let F := EJAForm.trace V
  have hlam : ∀ i, 0 ≤ lam i := by
    intro i
    have h1 := F.nonneg_idem ha0 (hprim i).idem
    have hpa : p i * a = lam i • p i := by
      rw [eja_mul_comm, hdec]; exact sum_idem_of_orth (fun j => (hprim j).idem) horth lam i
    have h2 : F.B a (p i) = lam i * F.B (p i) (p i) := by
      conv_lhs => rw [← (hprim i).idem]
      rw [F.mul_right, hpa, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [h2] at h1
    exact nonneg_of_mul_nonneg_left h1 (F.pos _ (hprim i).ne_zero)
  refine ⟨{i // lam i ≠ 0}, inferInstance, fun i => lam i.1, fun i => p i.1,
    fun i => lt_of_le_of_ne (hlam i.1) (Ne.symm i.2), fun i => hprim i.1,
    fun i j hij => horth i.1 j.1 (fun h => hij (Subtype.ext h)), ?_⟩
  rw [hdec]
  show ∑ i, lam i • p i = ∑ i : {i // lam i ≠ 0}, lam i.1 • p i.1
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => lam i ≠ 0)
    (fun i => by simp) (fun i => lam i • p i), Finset.sum_filter_of_ne]
  intro i _ hne h0
  exact hne (by rw [h0, zero_smul])

/-- **EJA 13** (`prop:EJAceilfloor`, main.tex:418, Proposition): for an effect
`a` there are `λᵢ > 0` and orthogonal atomic idempotents `pᵢ` with
`a = ∑ λᵢ pᵢ`; for *any* such decomposition, `⌈a⌉ = ∑ pᵢ`, and `⌈a⌉` is the
least idempotent above `a` (so independent of the decomposition); and
`⌊a⌋ = ⌈aᗮ⌉ᗮ` is the greatest idempotent below `a`. -/
theorem EJAceilfloor {a : V} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℝ) (p : ι → V),
      (∀ i, 0 < lam i) ∧ (∀ i, IsAtomic (p i)) ∧ (∀ i j, i ≠ j → p i * p j = 0) ∧
      a = ∑ i, lam i • p i) ∧
    (∀ (ι : Type) [Fintype ι] (lam : ι → ℝ) (p : ι → V), (∀ i, 0 < lam i) →
      (∀ i, p i * p i = p i) → (∀ i j, i ≠ j → p i * p j = 0) →
      a = ∑ i, lam i • p i → ejaCeil a = ∑ i, p i) ∧
    IsLeastIdemAbove a (ejaCeil a) ∧ IsGreatestIdemBelow a (ejaFloor a) := by
  classical
  have hceil : ∀ {b : V}, 0 ≤ b → b ≤ 1 → IsLeastIdemAbove b (ejaCeil b) := by
    intro b hb0 hb1
    obtain ⟨ι, hι, lam, p, hpos, hprim, horth, hdec⟩ := effect_decomp hb0
    have hex : ∃ q, IsLeastIdemAbove b q :=
      ⟨_, sum_isLeastIdemAbove (fun i => (hprim i).idem) horth hpos hb0 hb1 hdec⟩
    rw [ejaCeil, dif_pos hex]
    exact hex.choose_spec
  refine ⟨?_, ?_, hceil ha0 ha1, ?_⟩
  · obtain ⟨ι, hι, lam, p, hpos, hprim, horth, hdec⟩ := effect_decomp ha0
    exact ⟨ι, hι, lam, p, hpos,
      fun i => (isAtomic_iff_primitive (hprim i).ne_zero).mpr (hprim i), horth, hdec⟩
  · intro ι _ lam p hpos hidem horth hdec
    exact (hceil ha0 ha1).unique (sum_isLeastIdemAbove hidem horth hpos ha0 ha1 hdec)
  · have hb0 : (0 : V) ≤ 1 - a := eja_sub_nonneg.mpr ha1
    have hb1 : 1 - a ≤ 1 := by
      rw [← eja_sub_nonneg, sub_sub_cancel]; exact ha0
    obtain ⟨hc, hle, hmin⟩ := hceil hb0 hb1
    refine ⟨eja_one_sub_idem hc, ?_, fun q hq hqa => ?_⟩
    · rw [ejaFloor, ← eja_sub_nonneg]
      rw [← eja_sub_nonneg] at hle
      convert hle using 1; abel
    · have h1 : 1 - a ≤ 1 - q := by
        rw [← eja_sub_nonneg] at hqa ⊢
        convert hqa using 1; abel
      have h2 := hmin (1 - q) (eja_one_sub_idem hq) h1
      rw [ejaFloor, ← eja_sub_nonneg]
      rw [← eja_sub_nonneg] at h2
      convert h2 using 1; abel

end CeilFloor

end Papers.EJA
