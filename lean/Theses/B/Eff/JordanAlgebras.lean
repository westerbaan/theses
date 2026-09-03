/-
Theses/B/Eff/JordanAlgebras.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), line 2063:
the third example of an effectus in total form listed in the Examples
189aIII — the category `EJAᵒᵖ` of Euclidean Jordan algebras with positive
unit-preserving linear maps in the opposite direction.

Design:
* eff.tex prints no definition of a Euclidean Jordan algebra; it refers to
  the joint paper with van de Wetering.  `EuclideanJordanAlgebra` here is
  the classical *formally real* definition (Jordan–von Neumann–Wigner): a
  finite-dimensional real commutative algebra with a unit whose
  multiplication satisfies the Jordan identity and in which a sum of
  squares vanishes only if each summand does.  The Jordan identity is
  written exactly as Mathlib's `IsCommJordan.lmul_comm_rmul_rmul`, and
  formal reality exactly as the hypothesis of Mathlib's
  `IsFormallyReal.of_eq_zero_of_eq_zero_of_mul_self_add`; both bridges are
  `EuclideanJordanAlgebra.isCommJordan` and
  `EuclideanJordanAlgebra.isFormallyReal` below.  The *Euclidean* form of
  the definition — a positive definite bilinear form with
  `B (x * y) z = B y (x * z)`, i.e. the trace form — is carried too, in
  the direction that is needed: `formallyReal_of_form` derives formal
  reality from such a form, so `EJAObj.ofForm` turns the textbook data
  into an object of the category.  The converse (that a formally real
  finite-dimensional Jordan algebra carries such a form) is the
  Jordan–von Neumann–Wigner theorem and is not formalized; nothing here
  uses it.
* Like `OrderUnitSpace` in `OrderUnit.lean`, the class is a *mixin*, here
  over `AddCommGroup`, `Module ℝ`, `Mul`, `One` and `PartialOrder`, so
  that `ULift`s, products and the one-point algebra carry exactly
  Mathlib's own algebra and order.  The order is not extra data: the
  axiom `le_iff` says that `x ≤ y` holds precisely when `y - x` is a sum
  of squares, which is the order of the cone of squares — in a Euclidean
  Jordan algebra a sum of squares is again a square, but that is the
  spectral theorem, which is neither needed nor proved here.  That this
  relation is antisymmetric is *not* an extra assumption: it is formal
  reality, `eja_eq_zero_of_isSumSq_of_neg`.
* The mathematical work of the file is `eja_exists_isSumSq_nsmul_one_sub`:
  the unit of a Euclidean Jordan algebra is an order unit, i.e. every `x`
  satisfies `x ≤ n · 1` for some natural `n`.  This is the one point where
  finite-dimensionality and formal reality are both used, and it is proved
  by separation rather than by spectral theory: if the set of elements
  bounded by a multiple of `1` were not everything, a finite-dimensional
  Hahn–Banach argument would give a non-zero linear `f` with `f ≤ 0` on
  that set, hence `f(a * a) ≥ 0` for all `a` and `f 1 = 0`; expanding
  `0 ≤ f((a + t · 1) * (a + t · 1)) = f(a * a) + 2t · f(a)` for all real
  `t` forces `f a = 0` for every `a`.  With that, `toOrderUnitSpace` makes
  every Euclidean Jordan algebra an order unit space in the sense of
  `OrderUnit.lean`, with the cone of (sums of) squares and the Jordan unit
  as order unit.
* `EJA` is then the full subcategory of `OUS` spanned by the order unit
  spaces whose order and unit come from a Euclidean Jordan structure
  (`EJAObj.of` and `EJAObj.ofForm` put every Euclidean Jordan algebra
  there, and fullness makes its morphisms the positive unital maps), in
  exactly the way `CvN` is the full subcategory of `vN` spanned by the
  commutative algebras (`VNExamples.lean`).  `ℝᵤ`, the one-point algebra
  and a product of Euclidean Jordan algebras are Euclidean Jordan
  algebras, so the concrete presentation `ousPres` of `OUSᵒᵖ` restricts,
  and the three axioms of 180I are pulled back along the fully faithful
  inclusion `EJAᵒᵖ ⥤ OUSᵒᵖ`; no order-unit theory is redone.
* Not formalized: the ⋄-effectus clause of 206III for `EJAᵒᵖ` (see the
  comment at the end of the file), the description of its predicates,
  states and scalars (190V), and the &- and †-structures of eff.tex 209I
  and 213I.
-/
import Theses.B.Eff.OrderUnit

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits

namespace Theses.B.Eff

universe u v

noncomputable section

/-! ## Sums of squares in `ULift`s and products

Two transfer lemmas for Mathlib's `IsSumSq`, needed because the objects of
`OUS` live in a single universe (`ULift`) and because the binary
coproducts of `OUSᵒᵖ` are products. -/

/-- A `ULift` of an element is a sum of squares exactly when the element
is. -/
theorem isSumSq_ulift_iff {α : Type u} [AddZeroClass α] [Mul α]
    {x : ULift.{v} α} : IsSumSq x ↔ IsSumSq x.down := by
  constructor
  · intro h
    induction h with
    | zero => exact IsSumSq.zero
    | @sq_add a s _ ih => exact IsSumSq.sq_add a.down ih
  · intro h
    have key : ∀ y : α, IsSumSq y → IsSumSq (ULift.up.{v} y) := by
      intro y hy
      induction hy with
      | zero => exact IsSumSq.zero
      | @sq_add a s _ ih => exact IsSumSq.sq_add (ULift.up.{v} a) ih
    simpa using key x.down h

/-- The first component of a sum of squares in a product is a sum of
squares. -/
theorem isSumSq_fst {α : Type u} {β : Type v} [AddZeroClass α] [Mul α]
    [AddZeroClass β] [Mul β] {p : α × β} (h : IsSumSq p) : IsSumSq p.1 := by
  induction h with
  | zero => exact IsSumSq.zero
  | @sq_add a s _ ih => exact IsSumSq.sq_add a.1 ih

/-- The second component of a sum of squares in a product is a sum of
squares. -/
theorem isSumSq_snd {α : Type u} {β : Type v} [AddZeroClass α] [Mul α]
    [AddZeroClass β] [Mul β] {p : α × β} (h : IsSumSq p) : IsSumSq p.2 := by
  induction h with
  | zero => exact IsSumSq.zero
  | @sq_add a s _ ih => exact IsSumSq.sq_add a.2 ih

/-- A sum of squares in the left factor, placed in a product. -/
theorem isSumSq_inl {α : Type u} {β : Type v} [AddZeroClass α] [Mul α]
    [AddZeroClass β] [Mul β] (hz : (0 : β) * (0 : β) = 0) {a : α}
    (h : IsSumSq a) : IsSumSq ((a, 0) : α × β) := by
  induction h with
  | zero => exact IsSumSq.zero
  | @sq_add b s _ ih =>
    have he : ((b * b + s, (0 : β)) : α × β)
        = ((b, (0 : β)) : α × β) * ((b, (0 : β)) : α × β) + ((s, (0 : β)) : α × β) :=
      Prod.ext rfl (by simp [hz])
    rw [he]
    exact IsSumSq.sq_add _ ih

/-- A sum of squares in the right factor, placed in a product. -/
theorem isSumSq_inr {α : Type u} {β : Type v} [AddZeroClass α] [Mul α]
    [AddZeroClass β] [Mul β] (hz : (0 : α) * (0 : α) = 0) {b : β}
    (h : IsSumSq b) : IsSumSq (((0 : α), b) : α × β) := by
  induction h with
  | zero => exact IsSumSq.zero
  | @sq_add c s _ ih =>
    have he : (((0 : α), c * c + s) : α × β)
        = (((0 : α), c) : α × β) * ((0 : α), c) + (((0 : α), s) : α × β) :=
      Prod.ext (by simp [hz]) rfl
    rw [he]
    exact IsSumSq.sq_add _ ih

/-- **Formal reality makes the cone of sums of squares proper**: if `x`
and `y` are sums of squares with `x + y = 0`, then `x = 0`.  Stated with
the two algebraic facts as hypotheses, since it is used both inside the
class `EuclideanJordanAlgebra` and to build the partial order that the
class asks for. -/
theorem isSumSq_eq_zero_of_add {V : Type u} [AddCommGroup V] [Mul V]
    (hz : (0 : V) * (0 : V) = 0)
    (hfr : ∀ {a s : V}, IsSumSq s → a * a + s = 0 → a = 0)
    {x y : V} (h₁ : IsSumSq x) (h₂ : IsSumSq y) (h : x + y = 0) : x = 0 := by
  induction h₁ generalizing y with
  | zero => rfl
  | @sq_add a s hs ih =>
    have hsy : IsSumSq (s + y) := hs.add h₂
    have ha : a = 0 := by
      refine hfr hsy ?_
      rw [← add_assoc]
      exact h
    have haa : a * a = (0 : V) := by rw [ha]; exact hz
    have hsy0 : s + y = 0 := by
      have h' := h
      rw [haa, zero_add] at h'
      exact h'
    have hs0 : s = 0 := ih h₂ hsy0
    rw [haa, hs0, add_zero]

/-- The order of the cone of sums of squares is a partial order as soon as
the algebra is formally real; this is the order the `le_iff` axiom of
`EuclideanJordanAlgebra` demands, so that axiom constrains the order
rather than adding an assumption. -/
def sumSqPartialOrder (V : Type u) [AddCommGroup V] [Mul V]
    (hz : (0 : V) * (0 : V) = 0)
    (hfr : ∀ {a s : V}, IsSumSq s → a * a + s = 0 → a = 0) : PartialOrder V where
  le x y := IsSumSq (y - x)
  le_refl x := by
    show IsSumSq (x - x)
    simp
  le_trans x y z hxy hyz := by
    show IsSumSq (z - x)
    have he : z - x = (z - y) + (y - x) := by abel
    rw [he]
    exact IsSumSq.add hyz hxy
  le_antisymm x y hxy hyx := by
    have h₁ : IsSumSq (y - x) := hxy
    have h₂ : IsSumSq (x - y) := hyx
    have h : (y - x) + (x - y) = 0 := by abel
    have h0 : y - x = 0 := isSumSq_eq_zero_of_add hz hfr h₁ h₂ h
    exact (sub_eq_zero.mp h0).symm

/-! ## Euclidean Jordan algebras (189aIII) -/

/-- **189aIII** (`effexamplesintro`, eff.tex:2063, Examples): a **Euclidean
Jordan algebra**.

eff.tex prints no definition (it points at the joint paper with van de
Wetering); this is the classical *formally real* one: a finite-dimensional
real vector space with a commutative bilinear product satisfying the
Jordan identity `(a * b) * (a * a) = a * (b * (a * a))`, a unit for it,
and formal reality — `a * a + s = 0` with `s` a sum of squares forces
`a = 0`.  By the Jordan–von Neumann–Wigner theorem these are exactly the
algebras carrying an inner product with `⟪x * y, z⟫ = ⟪y, x * z⟫` (the
trace form), which is the definition usually spelled out; that equivalence
is not formalized here and is not used.

Stated as a mixin over `AddCommGroup X`, `Module ℝ X`, `Mul X`, `One X`
and `PartialOrder X`, in the style of `OrderUnitSpace`: the last axiom
`le_iff` says the order is the one of the cone of sums of squares. -/
class EuclideanJordanAlgebra (V : Type u) [AddCommGroup V] [Module ℝ V]
    [Mul V] [One V] [PartialOrder V] : Prop where
  /-- the Jordan product is commutative -/
  protected mul_comm : ∀ a b : V, a * b = b * a
  /-- ... and additive in its second (hence, by commutativity, either)
  argument -/
  protected mul_add : ∀ a b c : V, a * (b + c) = a * b + a * c
  /-- ... and real-homogeneous -/
  protected smul_mul : ∀ (r : ℝ) (a b : V), (r • a) * b = r • (a * b)
  /-- `1` is a unit for the Jordan product -/
  protected one_mul : ∀ a : V, 1 * a = a
  /-- the **Jordan identity**, verbatim Mathlib's
  `IsCommJordan.lmul_comm_rmul_rmul` -/
  protected lmul_comm_rmul_rmul : ∀ a b : V, a * b * (a * a) = a * (b * (a * a))
  /-- the algebra is finite-dimensional -/
  protected finiteDimensional : FiniteDimensional ℝ V
  /-- the algebra is **formally real**, verbatim the hypothesis of
  Mathlib's `IsFormallyReal.of_eq_zero_of_eq_zero_of_mul_self_add` -/
  protected formallyReal : ∀ {a s : V}, IsSumSq s → a * a + s = 0 → a = 0
  /-- the order is that of the cone of sums of squares -/
  protected le_iff : ∀ x y : V, x ≤ y ↔ IsSumSq (y - x)

namespace EuclideanJordanAlgebra

section Basic

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

instance toFiniteDimensional : FiniteDimensional ℝ V :=
  EuclideanJordanAlgebra.finiteDimensional

theorem eja_mul_comm (a b : V) : a * b = b * a := EuclideanJordanAlgebra.mul_comm a b

theorem eja_mul_add (a b c : V) : a * (b + c) = a * b + a * c :=
  EuclideanJordanAlgebra.mul_add a b c

theorem eja_add_mul (a b c : V) : (a + b) * c = a * c + b * c := by
  rw [eja_mul_comm, eja_mul_add, eja_mul_comm c a, eja_mul_comm c b]

/-- The full expansion of a product of two sums, used for the square of
`a + t · 1`. -/
theorem eja_add_mul_add (a b c d : V) :
    (a + b) * (c + d) = a * c + a * d + (b * c + b * d) := by
  rw [eja_add_mul, eja_mul_add, eja_mul_add]

theorem eja_smul_mul (r : ℝ) (a b : V) : (r • a) * b = r • (a * b) :=
  EuclideanJordanAlgebra.smul_mul r a b

theorem eja_mul_smul (r : ℝ) (a b : V) : a * (r • b) = r • (a * b) := by
  rw [eja_mul_comm, eja_smul_mul, eja_mul_comm]

theorem eja_one_mul (a : V) : 1 * a = a := EuclideanJordanAlgebra.one_mul a

theorem eja_mul_one (a : V) : a * 1 = a := by rw [eja_mul_comm, eja_one_mul]

theorem eja_zero_mul (a : V) : (0 : V) * a = 0 := by
  have h : (0 : V) * a + 0 * a = 0 * a + 0 := by
    rw [← eja_add_mul, add_zero, add_zero]
  exact add_left_cancel h

theorem eja_mul_zero (a : V) : a * (0 : V) = 0 := by
  rw [eja_mul_comm, eja_zero_mul]

theorem eja_mul_sub (a b c : V) : a * (b - c) = a * b - a * c := by
  have h : a * (b - c) + a * c = a * b := by
    rw [← eja_mul_add]
    congr 1
    abel
  exact eq_sub_of_add_eq h

theorem eja_sub_mul (a b c : V) : (a - b) * c = a * c - b * c := by
  rw [eja_mul_comm, eja_mul_sub, eja_mul_comm c a, eja_mul_comm c b]

/-- The Jordan identity of an `EuclideanJordanAlgebra` is Mathlib's: with
the commutative magma structure of the product, the algebra satisfies
`IsCommJordan`. -/
def commMagma (V : Type u) [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
    [PartialOrder V] [EuclideanJordanAlgebra V] : CommMagma V where
  mul := (· * ·)
  mul_comm := eja_mul_comm

theorem isCommJordan : @IsCommJordan V (commMagma V) := by
  have h := EuclideanJordanAlgebra.lmul_comm_rmul_rmul (V := V)
  exact @IsCommJordan.mk V (commMagma V) h

/-- The additive and multiplicative structure of a Euclidean Jordan
algebra is a non-unital non-associative ring; this is what lets Mathlib's
`IsFormallyReal` machinery apply. -/
def nonUnitalNonAssocRing (V : Type u) [AddCommGroup V] [Module ℝ V] [Mul V]
    [One V] [PartialOrder V] [EuclideanJordanAlgebra V] :
    NonUnitalNonAssocRing V :=
  { (inferInstance : AddCommGroup V), (inferInstance : Mul V) with
    left_distrib := eja_mul_add
    right_distrib := eja_add_mul
    zero_mul := eja_zero_mul
    mul_zero := eja_mul_zero }

/-- **A Euclidean Jordan algebra is formally real** in the sense of
Mathlib's `IsFormallyReal`. -/
theorem isFormallyReal : IsFormallyReal V := by
  have key : ∀ {a s : V}, IsSumSq s → a * a + s = 0 → a = 0 :=
    fun hs h => EuclideanJordanAlgebra.formallyReal hs h
  let _ := nonUnitalNonAssocRing V
  exact IsFormallyReal.of_eq_zero_of_eq_zero_of_mul_self_add key

/-- **The cone of sums of squares is proper**: if both `x` and `-x` are
sums of squares then `x = 0`.  This is formal reality, and it is what
makes the order of `le_iff` antisymmetric — so requiring a `PartialOrder`
in the class is no extra assumption. -/
theorem eja_eq_zero_of_isSumSq_add {x y : V} (h₁ : IsSumSq x) (h₂ : IsSumSq y)
    (h : x + y = 0) : x = 0 :=
  isSumSq_eq_zero_of_add (eja_zero_mul 0)
    (fun hs hh => EuclideanJordanAlgebra.formallyReal hs hh) h₁ h₂ h

theorem eja_eq_zero_of_isSumSq_of_neg {x : V} (h₁ : IsSumSq x)
    (h₂ : IsSumSq (-x)) : x = 0 :=
  eja_eq_zero_of_isSumSq_add h₁ h₂ (add_neg_cancel x)

/-! ### The cone of sums of squares -/

theorem eja_le_iff (x y : V) : x ≤ y ↔ IsSumSq (y - x) :=
  EuclideanJordanAlgebra.le_iff x y

theorem eja_nonneg_iff (x : V) : 0 ≤ x ↔ IsSumSq x := by
  rw [eja_le_iff]
  simp

/-- A non-negative multiple of a sum of squares is a sum of squares:
`r · (a * a) = (√r · a) * (√r · a)`. -/
theorem eja_isSumSq_smul {r : ℝ} (hr : 0 ≤ r) {s : V} (hs : IsSumSq s) :
    IsSumSq (r • s) := by
  induction hs with
  | zero => simp
  | @sq_add a s _ ih =>
    have hsq : (Real.sqrt r • a) * (Real.sqrt r • a) = r • (a * a) := by
      rw [eja_smul_mul, eja_mul_smul, smul_smul, Real.mul_self_sqrt hr]
    have he : r • (a * a + s) = (Real.sqrt r • a) * (Real.sqrt r • a) + r • s := by
      rw [hsq, smul_add]
    rw [he]
    exact IsSumSq.sq_add _ ih

/-- `1` is a sum of squares. -/
theorem eja_isSumSq_one : IsSumSq (1 : V) := by
  have h := IsSumSq.mul_self (1 : V)
  rwa [eja_mul_one] at h

/-- A non-negative multiple of `1` is a sum of squares. -/
theorem eja_isSumSq_smul_one {r : ℝ} (hr : 0 ≤ r) : IsSumSq (r • (1 : V)) :=
  eja_isSumSq_smul hr eja_isSumSq_one

/-- `4 · x = (x + 1) * (x + 1) - (x - 1) * (x - 1)`: every element is a
difference of two squares, up to a positive scalar. -/
theorem eja_four_smul (x : V) :
    (4 : ℝ) • x = (x + 1) * (x + 1) - (x - 1) * (x - 1) := by
  have h₁ : (x + 1) * (x + 1) = x * x + (x + x) + 1 := by
    rw [eja_add_mul_add, eja_mul_one, eja_one_mul, eja_mul_one]
    abel
  have h₂ : (x - 1) * (x - 1) = x * x - (x + x) + 1 := by
    rw [eja_sub_mul, eja_mul_sub, eja_mul_sub, eja_mul_one, eja_one_mul,
      eja_mul_one]
    abel
  have h₄ : (4 : ℝ) • x = x + x + (x + x) := by
    rw [show (4 : ℝ) = 2 + 2 by norm_num, add_smul, two_smul]
  rw [h₁, h₂, h₄]
  abel

end Basic

/-! ### The unit is an order unit

The one substantial theorem of the file. -/

section OrderUnit

/-- A convex cone in a finite-dimensional real normed space that spans and
on which every linear functional bounded above by `0` vanishes is the whole
space.  This is the finite-dimensional Hahn–Banach separation argument,
isolated from the Jordan-algebraic input. -/
theorem convexCone_eq_univ_of_forall_functional {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {W : Set E} (hconv : Convex ℝ W)
    (hcone : ∀ r : ℝ, 0 < r → ∀ x ∈ W, r • x ∈ W) (h0 : (0 : E) ∈ W)
    (hsub : ∀ x : E, ∃ a ∈ W, ∃ b ∈ W, x = a - b)
    (hfun : ∀ f : E →ₗ[ℝ] ℝ, (∀ w ∈ W, f w ≤ 0) → ∀ x, f x = 0) :
    ∀ x : E, x ∈ W := by
  intro x₀
  by_contra hx₀
  have hspan : affineSpan ℝ W = ⊤ := by
    have hsp : Submodule.span ℝ W = ⊤ := by
      refine Submodule.eq_top_iff'.mpr fun x => ?_
      obtain ⟨a, ha, b, hb, rfl⟩ := hsub x
      exact Submodule.sub_mem _ (Submodule.subset_span ha) (Submodule.subset_span hb)
    have hne : ((affineSpan ℝ W : AffineSubspace ℝ E) : Set E).Nonempty :=
      ⟨0, subset_affineSpan ℝ W h0⟩
    rw [← AffineSubspace.direction_eq_top_iff_of_nonempty hne, direction_affineSpan,
      vectorSpan_eq_span_vsub_set_right ℝ h0]
    have himg : ((fun x => x -ᵥ (0 : E)) '' W) = W := by
      ext y
      simp
    rw [himg]
    exact hsp
  obtain ⟨v₀, hv₀⟩ := hconv.interior_nonempty_iff_affineSpan_eq_top.mpr hspan
  obtain ⟨f, u, hf1, hf2⟩ := geometric_hahn_banach_open (E := E)
    hconv.interior isOpen_interior (convex_singleton x₀)
    (Set.disjoint_singleton_right.mpr fun h => hx₀ (interior_subset h))
  have hfx₀ : u ≤ f x₀ := hf2 x₀ rfl
  have hle : ∀ w ∈ W, f w ≤ 0 := by
    intro w hw
    by_contra hcon
    have hpos : 0 < f w := not_le.mp hcon
    set s : ℝ := max 1 ((2 * u - f v₀ + 1) / f w) with hsdef
    have hs1 : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hsw : s • w ∈ W := hcone s hs1 w hw
    have hmem : (2 : ℝ)⁻¹ • v₀ + (2 : ℝ)⁻¹ • (s • w) ∈ interior W :=
      hconv.combo_interior_closure_mem_interior hv₀ (subset_closure hsw)
        (by norm_num) (by norm_num) (by norm_num)
    have hlt := hf1 _ hmem
    rw [map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul] at hlt
    have hge : (2 * u - f v₀ + 1) / f w ≤ s := le_max_right _ _
    have hmul : 2 * u - f v₀ + 1 ≤ s * f w := (div_le_iff₀ hpos).mp hge
    linarith
  have hzero := hfun f.toLinearMap hle
  have h1 : f v₀ = 0 := hzero v₀
  have h2 : f x₀ = 0 := hzero x₀
  have h3 := hf1 v₀ hv₀
  linarith

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- The elements of a Euclidean Jordan algebra that are below some natural
multiple of the unit.  The order-unit theorem says this is everything. -/
def ejaBdd (V : Type u) [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
    [PartialOrder V] [EuclideanJordanAlgebra V] : Set V :=
  {y : V | ∃ n : ℕ, IsSumSq ((n : ℝ) • (1 : V) - y)}

theorem eja_neg_mem_bdd {s : V} (hs : IsSumSq s) : -s ∈ ejaBdd V := by
  refine ⟨0, ?_⟩
  simpa using hs

theorem eja_zero_mem_bdd : (0 : V) ∈ ejaBdd V := by
  refine ⟨0, ?_⟩
  simp

theorem eja_one_mem_bdd : (1 : V) ∈ ejaBdd V := by
  refine ⟨1, ?_⟩
  simp

theorem eja_bdd_add {x y : V} (hx : x ∈ ejaBdd V) (hy : y ∈ ejaBdd V) :
    x + y ∈ ejaBdd V := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  refine ⟨n + m, ?_⟩
  have he : ((n + m : ℕ) : ℝ) • (1 : V) - (x + y)
      = ((n : ℝ) • (1 : V) - x) + ((m : ℝ) • (1 : V) - y) := by
    push_cast
    rw [add_smul]
    abel
  rw [he]
  exact hn.add hm

theorem eja_bdd_smul {r : ℝ} (hr : 0 ≤ r) {x : V} (hx : x ∈ ejaBdd V) :
    r • x ∈ ejaBdd V := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨⌈r * n⌉₊, ?_⟩
  have h₁ : IsSumSq (r • ((n : ℝ) • (1 : V) - x)) := eja_isSumSq_smul hr hn
  have h₂ : IsSumSq (((⌈r * n⌉₊ : ℝ) - r * n) • (1 : V)) :=
    eja_isSumSq_smul_one (by
      have := Nat.le_ceil (r * (n : ℝ))
      linarith)
  have he : ((⌈r * n⌉₊ : ℕ) : ℝ) • (1 : V) - r • x
      = (((⌈r * n⌉₊ : ℝ) - r * n) • (1 : V)) + r • ((n : ℝ) • (1 : V) - x) := by
    rw [smul_sub, sub_smul, smul_smul]
    abel
  rw [he]
  exact h₂.add h₁

theorem eja_bdd_convex : Convex ℝ (ejaBdd V) := fun _ hx _ hy _ _ ha hb _ =>
  eja_bdd_add (eja_bdd_smul ha hx) (eja_bdd_smul hb hy)

theorem eja_bdd_sub (x : V) :
    ∃ a ∈ ejaBdd V, ∃ b ∈ ejaBdd V, x = a - b := by
  refine ⟨-((4 : ℝ)⁻¹ • ((x - 1) * (x - 1))),
    eja_neg_mem_bdd (eja_isSumSq_smul (by norm_num) (IsSumSq.mul_self _)),
    -((4 : ℝ)⁻¹ • ((x + 1) * (x + 1))),
    eja_neg_mem_bdd (eja_isSumSq_smul (by norm_num) (IsSumSq.mul_self _)), ?_⟩
  have key : (4 : ℝ)⁻¹ • ((x + 1) * (x + 1)) - (4 : ℝ)⁻¹ • ((x - 1) * (x - 1)) = x := by
    rw [← smul_sub, ← eja_four_smul x, smul_smul]
    norm_num
  rw [neg_sub_neg]
  exact key.symm

/-- Every linear functional that is `≤ 0` on `ejaBdd V` vanishes: it is
`≥ 0` on squares and kills `1`, so `0 ≤ f(a * a) + 2t · f(a)` for all real
`t`. -/
theorem eja_functional_eq_zero (f : V →ₗ[ℝ] ℝ)
    (hf : ∀ w ∈ ejaBdd V, f w ≤ 0) : ∀ x, f x = 0 := by
  have hsq : ∀ a : V, 0 ≤ f (a * a) := by
    intro a
    have h := hf _ (eja_neg_mem_bdd (IsSumSq.mul_self a))
    rw [map_neg] at h
    linarith
  have hone : f 1 = 0 := by
    have h₁ := hf _ (eja_one_mem_bdd (V := V))
    have h₂ := hf _ (eja_neg_mem_bdd (eja_isSumSq_one (V := V)))
    rw [map_neg] at h₂
    linarith
  intro a
  have hquad : ∀ t : ℝ, 0 ≤ f (a * a) + t * f a + t * f a := by
    intro t
    have he : (a + t • (1 : V)) * (a + t • (1 : V))
        = a * a + t • a + (t • a + (t * t) • (1 : V)) := by
      rw [eja_add_mul_add, eja_mul_smul, eja_mul_one, eja_smul_mul, eja_one_mul,
        eja_smul_mul, eja_mul_smul, eja_mul_one, smul_smul]
    have h := hsq (a + t • (1 : V))
    rw [he] at h
    simp only [map_add, map_smul, smul_eq_mul, hone, mul_zero, add_zero] at h
    linarith
  by_contra hfa
  have hd : (-(f (a * a) + 1) / (2 * f a)) * f a = -(f (a * a) + 1) / 2 := by
    field_simp
  have key := hquad (-(f (a * a) + 1) / (2 * f a))
  rw [hd] at key
  linarith

/-- **The unit of a Euclidean Jordan algebra is an order unit**: every
element is below some natural multiple of `1`.  Proved by separation (see
the file header); this is where finite-dimensionality is used. -/
theorem eja_exists_isSumSq_nsmul_one_sub (x : V) :
    ∃ n : ℕ, IsSumSq ((n : ℝ) • (1 : V) - x) := by
  classical
  obtain ⟨e⟩ : Nonempty (V ≃ₗ[ℝ] (Module.Free.ChooseBasisIndex ℝ V → ℝ)) :=
    ⟨(Module.Free.chooseBasis ℝ V).equivFun⟩
  have hSconv : Convex ℝ (⇑e.symm ⁻¹' ejaBdd V) := by
    simpa using (eja_bdd_convex (V := V)).linear_preimage
      (e.symm : (Module.Free.ChooseBasisIndex ℝ V → ℝ) →ₗ[ℝ] V)
  have hScone : ∀ r : ℝ, 0 < r → ∀ y ∈ ⇑e.symm ⁻¹' ejaBdd V,
      r • y ∈ ⇑e.symm ⁻¹' ejaBdd V := by
    intro r hr y hy
    have hsm : e.symm (r • y) = r • e.symm y := map_smul _ _ _
    show e.symm (r • y) ∈ ejaBdd V
    rw [hsm]
    exact eja_bdd_smul hr.le hy
  have hS0 : (0 : Module.Free.ChooseBasisIndex ℝ V → ℝ) ∈ ⇑e.symm ⁻¹' ejaBdd V := by
    show e.symm 0 ∈ ejaBdd V
    rw [map_zero]
    exact eja_zero_mem_bdd
  have hSsub : ∀ y : (Module.Free.ChooseBasisIndex ℝ V → ℝ),
      ∃ a ∈ ⇑e.symm ⁻¹' ejaBdd V, ∃ b ∈ ⇑e.symm ⁻¹' ejaBdd V, y = a - b := by
    intro y
    obtain ⟨a, ha, c, hc, hy⟩ := eja_bdd_sub (e.symm y)
    refine ⟨e a, ?_, e c, ?_, ?_⟩
    · show e.symm (e a) ∈ ejaBdd V
      rwa [e.symm_apply_apply]
    · show e.symm (e c) ∈ ejaBdd V
      rwa [e.symm_apply_apply]
    · have hc2 := congrArg e hy
      rw [e.apply_symm_apply, map_sub] at hc2
      exact hc2
  have hSfun : ∀ f : (Module.Free.ChooseBasisIndex ℝ V → ℝ) →ₗ[ℝ] ℝ,
      (∀ w ∈ ⇑e.symm ⁻¹' ejaBdd V, f w ≤ 0) → ∀ y, f y = 0 := by
    intro f hf y
    have hg : ∀ w ∈ ejaBdd V, (f.comp (e : V →ₗ[ℝ] _)) w ≤ 0 := by
      intro w hw
      refine hf (e w) ?_
      show e.symm (e w) ∈ ejaBdd V
      rwa [e.symm_apply_apply]
    have hgz := eja_functional_eq_zero (f.comp (e : V →ₗ[ℝ] _)) hg (e.symm y)
    have hgz2 : f (e (e.symm y)) = 0 := hgz
    rwa [e.apply_symm_apply] at hgz2
  have hall := convexCone_eq_univ_of_forall_functional hSconv hScone hS0 hSsub hSfun
  have hx : e.symm (e x) ∈ ejaBdd V := hall (e x)
  rw [e.symm_apply_apply] at hx
  exact hx

/-- **A Euclidean Jordan algebra is an order unit space** (in the sense of
`OrderUnit.lean`), with the cone of sums of squares and the Jordan unit as
order unit.  Not an instance: `ℝ`, `ULift ℝ` and products already carry
their own `OrderUnitSpace` structures, and this one coincides with them
(the order is fixed by `le_iff` and the unit by `unit = 1`). -/
def toOrderUnitSpace (V : Type u) [AddCommGroup V] [Module ℝ V] [Mul V]
    [One V] [PartialOrder V] [EuclideanJordanAlgebra V] : OrderUnitSpace V where
  add_le_add_left x y h z := by
    rw [eja_le_iff] at h ⊢
    have he : y + z - (x + z) = y - x := by abel
    rw [he]
    exact h
  smul_nonneg hr hx := by
    rw [eja_nonneg_iff] at hx ⊢
    exact eja_isSumSq_smul hr hx
  unit := 1
  exists_le_smul_unit x := by
    obtain ⟨n, hn⟩ := eja_exists_isSumSq_nsmul_one_sub x
    exact ⟨n, (eja_le_iff _ _).mpr hn⟩

end OrderUnit

/-! ### The basic examples of Euclidean Jordan algebras -/

/-- `ℝ` is a Euclidean Jordan algebra: the one-dimensional one. -/
instance _root_.Real.euclideanJordanAlgebra : EuclideanJordanAlgebra ℝ where
  mul_comm := mul_comm
  mul_add := mul_add
  smul_mul r a b := by simp [smul_eq_mul, mul_assoc]
  one_mul := one_mul
  lmul_comm_rmul_rmul a b := by ring
  finiteDimensional := inferInstance
  formallyReal {a s} hs h := by
    have h₁ : 0 ≤ s := IsSumSq.nonneg hs
    have h₂ : 0 ≤ a * a := mul_self_nonneg a
    have : a * a = 0 := by linarith
    exact mul_self_eq_zero.mp this
  le_iff x y := by
    constructor
    · intro h
      have h₀ : 0 ≤ y - x := sub_nonneg.mpr h
      have := IsSumSq.mul_self (Real.sqrt (y - x))
      rwa [Real.mul_self_sqrt h₀] at this
    · intro h
      have := IsSumSq.nonneg h
      linarith

/-- A `ULift` of a Euclidean Jordan algebra is one (needed because the
objects of `OUS` live in a single universe). -/
instance ULift.euclideanJordanAlgebra (V : Type u) [AddCommGroup V]
    [Module ℝ V] [Mul V] [One V] [PartialOrder V] [EuclideanJordanAlgebra V] :
    EuclideanJordanAlgebra (ULift.{v} V) where
  mul_comm a b := ULift.down_injective (eja_mul_comm a.down b.down)
  mul_add a b c := ULift.down_injective (eja_mul_add a.down b.down c.down)
  smul_mul r a b := ULift.down_injective (eja_smul_mul r a.down b.down)
  one_mul a := ULift.down_injective (eja_one_mul a.down)
  lmul_comm_rmul_rmul a b :=
    ULift.down_injective (EuclideanJordanAlgebra.lmul_comm_rmul_rmul a.down b.down)
  finiteDimensional := Module.Finite.equiv (ULift.moduleEquiv (R := ℝ) (M := V)).symm
  formallyReal {a s} hs h := by
    refine ULift.down_injective ?_
    refine EuclideanJordanAlgebra.formallyReal (isSumSq_ulift_iff.mp hs) ?_
    exact congrArg ULift.down h
  le_iff x y := by
    rw [isSumSq_ulift_iff]
    exact eja_le_iff x.down y.down

/-- The one-point algebra (in which `1 = 0`) is a Euclidean Jordan
algebra; it is the final object of `EJA`, hence the initial object of
`EJAᵒᵖ`. -/
instance PUnit.euclideanJordanAlgebra :
    EuclideanJordanAlgebra PUnit.{u + 1} where
  mul_comm _ _ := Subsingleton.elim _ _
  mul_add _ _ _ := Subsingleton.elim _ _
  smul_mul _ _ _ := Subsingleton.elim _ _
  one_mul _ := Subsingleton.elim _ _
  lmul_comm_rmul_rmul _ _ := Subsingleton.elim _ _
  finiteDimensional := by
    refine Module.Finite.of_surjective (0 : ℝ →ₗ[ℝ] PUnit.{u + 1}) ?_
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  formallyReal _ _ := Subsingleton.elim _ _
  le_iff x y := by
    constructor
    · intro _
      have he : y - x = 0 := Subsingleton.elim _ _
      rw [he]
      exact IsSumSq.zero
    · intro _
      exact le_of_eq (Subsingleton.elim _ _)

/-- A product of two Euclidean Jordan algebras is one; this is the binary
coproduct of `EJAᵒᵖ`. -/
instance Prod.euclideanJordanAlgebra (V : Type u) (W : Type u) [AddCommGroup V]
    [Module ℝ V] [Mul V] [One V] [PartialOrder V] [EuclideanJordanAlgebra V]
    [AddCommGroup W] [Module ℝ W] [Mul W] [One W] [PartialOrder W]
    [EuclideanJordanAlgebra W] : EuclideanJordanAlgebra (V × W) where
  mul_comm a b := Prod.ext (eja_mul_comm a.1 b.1) (eja_mul_comm a.2 b.2)
  mul_add a b c := Prod.ext (eja_mul_add a.1 b.1 c.1) (eja_mul_add a.2 b.2 c.2)
  smul_mul r a b := Prod.ext (eja_smul_mul r a.1 b.1) (eja_smul_mul r a.2 b.2)
  one_mul a := Prod.ext (eja_one_mul a.1) (eja_one_mul a.2)
  lmul_comm_rmul_rmul a b :=
    Prod.ext (EuclideanJordanAlgebra.lmul_comm_rmul_rmul a.1 b.1)
      (EuclideanJordanAlgebra.lmul_comm_rmul_rmul a.2 b.2)
  finiteDimensional := inferInstance
  formallyReal {a s} hs h := by
    refine Prod.ext ?_ ?_
    · exact EuclideanJordanAlgebra.formallyReal (isSumSq_fst hs) (congrArg Prod.fst h)
    · exact EuclideanJordanAlgebra.formallyReal (isSumSq_snd hs) (congrArg Prod.snd h)
  le_iff x y := by
    constructor
    · intro h
      have h₁ : IsSumSq (y.1 - x.1) := (eja_le_iff _ _).mp (Prod.le_def.mp h).1
      have h₂ : IsSumSq (y.2 - x.2) := (eja_le_iff _ _).mp (Prod.le_def.mp h).2
      have he : y - x = ((y.1 - x.1, (0 : W)) : V × W) + ((0 : V), y.2 - x.2) :=
        Prod.ext (by simp) (by simp)
      rw [he]
      exact (isSumSq_inl (eja_mul_zero (0 : W)) h₁).add (isSumSq_inr (eja_mul_zero (0 : V)) h₂)
    · intro h
      refine Prod.le_def.mpr ⟨(eja_le_iff _ _).mpr ?_, (eja_le_iff _ _).mpr ?_⟩
      · exact isSumSq_fst h
      · exact isSumSq_snd h

/-! ### The textbook ("Euclidean") form of the definition

A Euclidean Jordan algebra is usually presented as a finite-dimensional
real unital commutative Jordan algebra carrying an inner product with
`⟪x * y, z⟫ = ⟪y, x * z⟫` — the trace form.  The two lemmas below turn
that presentation into the class above: such a form makes the algebra
formally real (`formallyReal_of_form`), and the cone of sums of squares
then carries the order (`sumSqPartialOrder`), so the textbook data
produces an object of the category (`EJAObj.ofForm`). -/

/-- Multiplication by `0` is `0` in any algebra with an additive
multiplication. -/
theorem mul_zero_of_mul_add {V : Type u} [AddCommGroup V] [Mul V]
    (hadd : ∀ a b c : V, a * (b + c) = a * b + a * c) (a : V) :
    a * (0 : V) = 0 := by
  have h := hadd a 0 0
  rw [add_zero] at h
  have h2 : a * (0 : V) + 0 = a * (0 : V) + a * (0 : V) := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h2).symm

/-- **A positive definite associative bilinear form makes a Jordan algebra
formally real.**  Indeed `B (a * a) 1 = B a (a * 1) = B a a ≥ 0`, so the
value of `B (·) 1` on a sum of squares is a sum of the numbers `B aᵢ aᵢ`;
if that sum vanishes each of them does, and definiteness gives
`aᵢ = 0`. -/
theorem formallyReal_of_form {V : Type u} [AddCommGroup V] [Module ℝ V]
    [Mul V] [One V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hassoc : ∀ x y z : V, B (x * y) z = B y (x * z))
    (hone : ∀ a : V, a * 1 = a) (hpos : ∀ x : V, 0 ≤ B x x)
    (hdef : ∀ x : V, B x x = 0 → x = 0) :
    ∀ {a s : V}, IsSumSq s → a * a + s = 0 → a = 0 := by
  have hsq : ∀ x : V, B (x * x) 1 = B x x := by
    intro x
    rw [hassoc, hone]
  have hsum : ∀ s : V, IsSumSq s → 0 ≤ B s 1 := by
    intro s hs
    induction hs with
    | zero => simp
    | @sq_add a t _ ih =>
      have he : B (a * a + t) 1 = B (a * a) 1 + B t 1 := by
        rw [map_add]
        rfl
      rw [he, hsq]
      have := hpos a
      linarith
  intro a s hs h
  have h0 : B (a * a + s) 1 = 0 := by
    rw [h]
    simp
  have he : B (a * a + s) 1 = B a a + B s 1 := by
    rw [map_add]
    have : (B (a * a) + B s) 1 = B (a * a) 1 + B s 1 := rfl
    rw [this, hsq]
  have h1 := hpos a
  have h2 := hsum s hs
  refine hdef a ?_
  rw [he] at h0
  linarith

/-- **The textbook data makes a Euclidean Jordan algebra** in the sense of
the class above, with the order of the cone of sums of squares. -/
theorem ofForm (V : Type u) [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
    (hcomm : ∀ a b : V, a * b = b * a)
    (hadd : ∀ a b c : V, a * (b + c) = a * b + a * c)
    (hsmul : ∀ (r : ℝ) (a b : V), (r • a) * b = r • (a * b))
    (hone : ∀ a : V, 1 * a = a)
    (hjordan : ∀ a b : V, a * b * (a * a) = a * (b * (a * a)))
    (hfin : FiniteDimensional ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hassoc : ∀ x y z : V, B (x * y) z = B y (x * z))
    (hpos : ∀ x : V, 0 ≤ B x x) (hdef : ∀ x : V, B x x = 0 → x = 0) :
    @EuclideanJordanAlgebra V _ _ _ _
      (sumSqPartialOrder V
        (mul_zero_of_mul_add hadd 0)
        (formallyReal_of_form B hassoc (fun a => (hcomm a 1).trans (hone a)) hpos
          hdef)) :=
  letI := sumSqPartialOrder V
    (mul_zero_of_mul_add hadd 0)
    (formallyReal_of_form B hassoc (fun a => (hcomm a 1).trans (hone a)) hpos hdef)
  { mul_comm := hcomm
    mul_add := hadd
    smul_mul := hsmul
    one_mul := hone
    lmul_comm_rmul_rmul := hjordan
    finiteDimensional := hfin
    formallyReal := formallyReal_of_form B hassoc
      (fun a => (hcomm a 1).trans (hone a)) hpos hdef
    le_iff := fun _ _ => Iff.rfl }

end EuclideanJordanAlgebra

/-! ## The category `EJA` (189aIII)

`EJA` is the full subcategory of `OUS` spanned by the order unit spaces
whose order is the cone of squares of a Euclidean Jordan structure and
whose order unit is its Jordan unit; the morphisms are, as in `OUS`, all
positive unit-preserving linear maps, which for these objects are exactly
the positive unital maps of Euclidean Jordan algebras. -/

open EuclideanJordanAlgebra

/-- Carrying a Euclidean Jordan structure whose cone of sums of squares is
the order and whose unit is the order unit, as a property of the objects
of `OUS`. -/
def IsEJA : ObjectProperty OUS.{u} := fun X =>
  ∃ (_ : Mul X.carrier) (_ : One X.carrier),
    ∃ _ : EuclideanJordanAlgebra X.carrier, (1 : X.carrier) = X.unit

/-- The way `IsEJA` is verified: exhibit the instances. -/
theorem isEJA_of (X : OUS.{u}) [Mul X.carrier] [One X.carrier]
    [EuclideanJordanAlgebra X.carrier] (h : (1 : X.carrier) = X.unit) :
    IsEJA X := ⟨inferInstance, inferInstance, inferInstance, h⟩

/-- **`EJA`**: the full subcategory of `OUS` spanned by the Euclidean
Jordan algebras. -/
abbrev EJAObj : Type (u + 1) := IsEJA.{u}.FullSubcategory

/-- **Every Euclidean Jordan algebra is an object of `EJA`**: its cone of
sums of squares and its Jordan unit make it an order unit space
(`EuclideanJordanAlgebra.toOrderUnitSpace`, whose order-unit axiom is the
separation theorem `eja_exists_isSumSq_nsmul_one_sub`), and that order and
unit are by construction the ones `IsEJA` asks for.  Together with fullness
this is what makes `EJA` the category of Euclidean Jordan algebras with
positive unital maps: the objects are exactly the order unit spaces of
Euclidean Jordan algebras and the morphisms are exactly the positive
unital linear maps between them, so `EJA` is equivalent to the category
whose objects are Euclidean Jordan structures themselves (two Jordan
structures with the same order and unit are, in that category, isomorphic
by the identity). -/
def EJAObj.of (V : Type u) [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
    [PartialOrder V] [EuclideanJordanAlgebra V] : EJAObj.{u} :=
  letI := EuclideanJordanAlgebra.toOrderUnitSpace V
  ⟨OUS.of V, isEJA_of (OUS.of V) rfl⟩

/-- **Every Euclidean Jordan algebra in the usual, trace-form sense is an
object of `EJA`**: a finite-dimensional real unital commutative Jordan
algebra with a positive definite bilinear form satisfying
`B (x * y) z = B y (x * z)`, ordered by its cone of sums of squares.  This
and `EJAObj.of` are what pin `EJA` down as the category eff.tex names. -/
def EJAObj.ofForm (V : Type u) [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
    (hcomm : ∀ a b : V, a * b = b * a)
    (hadd : ∀ a b c : V, a * (b + c) = a * b + a * c)
    (hsmul : ∀ (r : ℝ) (a b : V), (r • a) * b = r • (a * b))
    (hone : ∀ a : V, 1 * a = a)
    (hjordan : ∀ a b : V, a * b * (a * a) = a * (b * (a * a)))
    (hfin : FiniteDimensional ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hassoc : ∀ x y z : V, B (x * y) z = B y (x * z))
    (hpos : ∀ x : V, 0 ≤ B x x) (hdef : ∀ x : V, B x x = 0 → x = 0) :
    EJAObj.{u} :=
  letI := sumSqPartialOrder V
    (EuclideanJordanAlgebra.mul_zero_of_mul_add hadd 0)
    (EuclideanJordanAlgebra.formallyReal_of_form B hassoc
      (fun a => (hcomm a 1).trans (hone a)) hpos hdef)
  letI := EuclideanJordanAlgebra.ofForm V hcomm hadd hsmul hone hjordan hfin B
    hassoc hpos hdef
  EJAObj.of V

/-- The scalars `ℝᵤ` as an object of `EJA`. -/
def ejaScal : EJAObj.{u} :=
  ⟨ousScal.{u}, isEJA_of ousScal.{u} rfl⟩

/-- The product of two Euclidean Jordan algebras, as an object of `EJA`
(the effectus coproduct of `EJAᵒᵖ`). -/
def ejaProd (X Y : EJAObj.{u}) : EJAObj.{u} := by
  refine ⟨X.obj.prod Y.obj, ?_⟩
  obtain ⟨mX, oX, eX, hX⟩ := X.property
  obtain ⟨mY, oY, eY, hY⟩ := Y.property
  let _ := mX; let _ := oX; let _ := eX; let _ := mY; let _ := oY; let _ := eY
  exact isEJA_of (X.obj.prod Y.obj) (Prod.ext hX hY)

/-- The one-point algebra as an object of `EJA`. -/
def ejaTriv : EJAObj.{u} :=
  ⟨ousTriv.{u}, isEJA_of ousTriv.{u} (Subsingleton.elim _ _)⟩

theorem eja_hom_ext {X Y : EJAObj.{u}} {f g : X ⟶ Y}
    (h : ∀ x, f.hom.toLinearMap x = g.hom.toLinearMap x) : f = g :=
  InducedCategory.hom_ext (ous_hom_ext h)

theorem ejaop_hom_ext {X Y : EJAObj.{u}ᵒᵖ} {f g : X ⟶ Y}
    (h : ∀ x, f.unop.hom.toLinearMap x = g.unop.hom.toLinearMap x) : f = g :=
  Quiver.Hom.unop_inj (eja_hom_ext h)

theorem ejaop_comp_apply {X Y Z : EJAObj.{u}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Z.unop.obj.carrier) :
    (f ≫ g).unop.hom.toLinearMap x
      = f.unop.hom.toLinearMap (g.unop.hom.toLinearMap x) :=
  ous_comp_apply g.unop.hom f.unop.hom x

theorem ejaop_congr {X Y : EJAObj.{u}ᵒᵖ} {f g : X ⟶ Y} (h : f = g)
    (x : Y.unop.obj.carrier) :
    f.unop.hom.toLinearMap x = g.unop.hom.toLinearMap x := by rw [h]

theorem eja_id_apply {X : EJAObj.{u}} (x : X.obj.carrier) :
    (𝟙 X : X ⟶ X).hom.toLinearMap x = x := rfl

/-- Postcomposition with a fixed map, pointwise. -/
theorem ejaop_comp_congr {Z P X : EJAObj.{u}ᵒᵖ} {F : P ⟶ X} {a b : Z ⟶ P}
    (h : a ≫ F = b ≫ F) (x : X.unop.obj.carrier) :
    a.unop.hom.toLinearMap (F.unop.hom.toLinearMap x)
      = b.unop.hom.toLinearMap (F.unop.hom.toLinearMap x) :=
  ((ejaop_comp_apply a F x).symm.trans (ejaop_congr h x)).trans
    (ejaop_comp_apply b F x)

/-- `ℝᵤ` is initial in `EJA`, hence final in `EJAᵒᵖ`. -/
def ejaScalIsInitial : IsInitial (ejaScal.{u}) :=
  IsInitial.ofUniqueHom (fun X => InducedCategory.homMk (ousUnitMap X.obj))
    (fun _ f => InducedCategory.hom_ext (ousUnitMap_unique f.hom))

/-- The one-point algebra is final in `EJA`, hence initial in `EJAᵒᵖ`. -/
def ejaTrivIsTerminal : IsTerminal (ejaTriv.{u}) :=
  IsTerminal.ofUniqueHom (fun X => InducedCategory.homMk (ousTrivMap X.obj))
    (fun _ _ => InducedCategory.hom_ext
      (ous_hom_ext fun _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _))

/-- The concrete presentation of `EJAᵒᵖ`, the restriction of `ousPres`:
the final object is `ℝᵤ`, the binary coproducts are the products. -/
def ejaPres : CoprodPres (EJAObj.{u}ᵒᵖ) where
  T := Opposite.op ejaScal
  hT := IsInitial.op (EJAObj.{u}) ejaScalIsInitial
  P X Y := Opposite.op (ejaProd X.unop Y.unop)
  pinl X Y := Quiver.Hom.op
    (InducedCategory.homMk (ousFst X.unop.obj Y.unop.obj))
  pinr X Y := Quiver.Hom.op
    (InducedCategory.homMk (ousSnd X.unop.obj Y.unop.obj))
  hP X Y := BinaryCofan.IsColimit.mk _
    (fun {_} u v => Quiver.Hom.op
      (InducedCategory.homMk (ousPair u.unop.hom v.unop.hom)))
    (fun {_} _ _ => ejaop_hom_ext fun x => ejaop_comp_apply _ _ x)
    (fun {_} _ _ => ejaop_hom_ext fun x => ejaop_comp_apply _ _ x)
    (fun {_} _ _ m h₁ h₂ => ejaop_hom_ext fun x => by
      refine Prod.ext ?_ ?_
      · exact (ejaop_comp_apply _ m x).symm.trans (ejaop_congr h₁ x)
      · exact (ejaop_comp_apply _ m x).symm.trans (ejaop_congr h₂ x))

/-- The unique morphism into the final object of `EJAᵒᵖ` is `r ↦ r · 1`. -/
theorem ejaPres_from_apply (Y : EJAObj.{u}ᵒᵖ) (r : ULift.{u} ℝ) :
    (ejaPres.hT.from Y).unop.hom.toLinearMap r = r.down • Y.unop.obj.unit := by
  have h : ejaPres.hT.from Y
      = Quiver.Hom.op (InducedCategory.homMk (ousUnitMap Y.unop.obj)) :=
    ejaPres.hT.hom_ext _ _
  rw [h]
  rfl

/-- The coproduct of two morphisms of `EJAᵒᵖ` acts coordinatewise. -/
theorem ejaPres_pmap_apply {X X' Y Y' : EJAObj.{u}ᵒᵖ} (f : X ⟶ X') (g : Y ⟶ Y')
    (p : (ejaPres.P X' Y').unop.obj.carrier) :
    (ejaPres.pmap f g).unop.hom.toLinearMap p
      = (f.unop.hom.toLinearMap p.1, g.unop.hom.toLinearMap p.2) := by
  refine Prod.ext ?_ ?_
  · exact ejaop_comp_apply f _ p
  · exact ejaop_comp_apply g _ p

/-- **189aIII** (`effexamplesintro`, eff.tex:2063, Examples): the category
`EJAᵒᵖ` of Euclidean Jordan algebras with positive unit-preserving linear
maps in the opposite direction is an effectus in total form.

The point gives no proof (it refers to the joint paper with van de
Wetering).  Ours restricts the presentation `ousPres` of `OUSᵒᵖ` to
`EJAᵒᵖ` — `ℝᵤ`, the one-point algebra and a product of Euclidean Jordan
algebras are Euclidean Jordan algebras, so the final object, the initial
object and the binary coproducts of `OUSᵒᵖ` stay inside the subcategory —
and then pulls the three axioms of 180I back along the inclusion
`EJAᵒᵖ ⥤ OUSᵒᵖ`, which is fully faithful and therefore reflects pullbacks
(`IsPullback.of_map_of_faithful`).  So `ous_isPushout1`, `ous_isPushout2`
and `ous_jointlyMonic_aux` are reused verbatim; the Jordan-algebraic input
is exactly that every Euclidean Jordan algebra is an order unit space
(`EuclideanJordanAlgebra.toOrderUnitSpace`). -/
theorem effectus_eja : Nonempty (EffectusTotalStructure EJAObj.{u}ᵒᵖ) := by
  have : HasTerminal (EJAObj.{u}ᵒᵖ) := ejaPres.hT.hasTerminal
  have : HasInitial (EJAObj.{u}ᵒᵖ) :=
    (IsTerminal.op (EJAObj.{u}) ejaTrivIsTerminal).hasInitial
  have : ∀ X Y : EJAObj.{u}ᵒᵖ, HasColimit (pair X Y) := fun X Y =>
    HasColimit.mk ⟨_, ejaPres.hP X Y⟩
  have : HasBinaryCoproducts (EJAObj.{u}ᵒᵖ) :=
    hasBinaryCoproducts_of_hasColimit_pair _
  have : HasFiniteCoproducts (EJAObj.{u}ᵒᵖ) :=
    hasFiniteCoproducts_of_has_binary_and_initial
  refine ⟨{ hasFiniteCoproducts := inferInstance
            hasTerminal := inferInstance
            effectus := effectusTotalForm_of_pres ejaPres ?_ ?_ ?_ }⟩
  · intro X Y
    refine IsPullback.of_map_of_faithful (IsEJA.{u}.ι.op) ?_
    have e₁ : (IsEJA.{u}.ι.op).map (ejaPres.pmap (𝟙 X) (ejaPres.hT.from Y))
        = Quiver.Hom.op (ousSq1i X.unop.obj Y.unop.obj) := by
      refine ousop_hom_ext fun p => (ejaPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext rfl ?_
      exact ejaPres_from_apply Y p.2
    have e₂ : (IsEJA.{u}.ι.op).map (ejaPres.pmap (ejaPres.hT.from X) (𝟙 Y))
        = Quiver.Hom.op (ousSq1h X.unop.obj Y.unop.obj) := by
      refine ousop_hom_ext fun p => (ejaPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ rfl
      exact ejaPres_from_apply X p.1
    have e₃ : (IsEJA.{u}.ι.op).map
          (ejaPres.pmap (ejaPres.hT.from X) (𝟙 ejaPres.T))
        = Quiver.Hom.op (ousSq1g X.unop.obj) := by
      refine ousop_hom_ext fun p => (ejaPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ rfl
      exact ejaPres_from_apply X p.1
    have e₄ : (IsEJA.{u}.ι.op).map
          (ejaPres.pmap (𝟙 ejaPres.T) (ejaPres.hT.from Y))
        = Quiver.Hom.op (ousSq1f Y.unop.obj) := by
      refine ousop_hom_ext fun p => (ejaPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext rfl ?_
      exact ejaPres_from_apply Y p.2
    rw [e₁, e₂, e₃, e₄]
    exact (ous_isPushout1 X.unop.obj Y.unop.obj).op
  · intro X Y
    refine IsPullback.of_map_of_faithful (IsEJA.{u}.ι.op) ?_
    have f₁ : (IsEJA.{u}.ι.op).map (ejaPres.hT.from X)
        = Quiver.Hom.op (ousSq2i X.unop.obj) :=
      ousop_hom_ext fun z => ejaPres_from_apply X z
    have f₄ : (IsEJA.{u}.ι.op).map
          (ejaPres.pmap (ejaPres.hT.from X) (ejaPres.hT.from Y))
        = Quiver.Hom.op (ousSq2f X.unop.obj Y.unop.obj) := by
      refine ousop_hom_ext fun p => (ejaPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ ?_
      · exact ejaPres_from_apply X p.1
      · exact ejaPres_from_apply Y p.2
    rw [f₄, f₁]
    exact (ous_isPushout2 X.unop.obj Y.unop.obj).op
  · intro Z a b hf hg
    apply Quiver.Hom.unop_inj
    refine InducedCategory.hom_ext ?_
    refine ous_jointlyMonic_aux a.unop.hom b.unop.hom (fun x => ?_) (fun x => ?_)
    · exact ejaop_comp_congr hf x
    · exact ejaop_comp_congr hg x

/-! ## The ⋄-effectus clause of 206III, and what it would take

206III (eff.tex:4460, Examples) says that `vNᵒᵖ`, `CvNᵒᵖ`, `EJAᵒᵖ` and
`Set` are all ⋄-effectuses.  The `EJAᵒᵖ` clause is *not* carried here, and
the reason is not the effectus axioms — it is that a ⋄-effectus lives in
the **partial** form, which needs a different category and a theory of
Jordan compressions that neither this tree nor Mathlib has.  Precisely:

* `DiamondEffectus` (`DiamondAmp.lean`) presupposes, as instances,
  `HasFiniteCoproducts`, a `PCM` on every hom-set, `FinPAC` and
  `EffectusPartialForm`.  For von Neumann algebras those live on the
  *subunital* category `WStarCPSU` (`WStarCat.lean`), not on the unital
  one; the corresponding `EJA_psu` — Euclidean Jordan algebras with
  positive **subunital** maps — does not exist here, and the vN precedent
  (`VNExamples.lean`, `section VNPartial`) puts that infrastructure at
  about 500 lines, plus about 180 for the bridge that identifies the
  predicates on an object with its effects `0 ≤ a ≤ 1`.
* On top of that come the four obligations of a ⋄-effectus, about 230
  lines for `vNᵒᵖ`, and each needs a piece of Jordan theory that is
  missing: comprehension needs the *compression* `U_p` onto the Peirce-1
  subalgebra of an idempotent `p` together with the fact that this corner
  is again a Euclidean Jordan algebra (the vN analogue is the standard
  corner `b ↦ ⌊a⌋ b ⌊a⌋`, `Dils/Pure.lean`); quotients need the filter
  `b ↦ U_{√(1 - a)} b`, hence *square roots*, hence a continuous
  functional calculus; images need the range (support) projection of a
  positive map and the ceiling `⌈a⌉` of an effect; and `orth_sharp` needs
  that the sharp predicates are exactly the idempotents, so that `1 - p`
  is sharp when `p` is.
* All four rest on the **spectral theorem for a single element** of a
  formally real Jordan algebra — `x` generates an associative, reduced,
  finite-dimensional real algebra, hence a copy of `ℝᵏ` — which needs
  power-associativity of Jordan algebras first.  Mathlib has the Jordan
  identity (`IsJordan`, `IsCommJordan`, `Mathlib/Algebra/Jordan/Basic.lean`)
  and nothing beyond it: no power-associativity, no spectral decomposition,
  no Peirce decomposition, no quadratic representation.  That prerequisite
  alone is a development of its own, and it is the real cost of the
  `EJAᵒᵖ` clause of 206III.

Nothing in this file depends on any of that: an effectus in *total* form
needs only the order unit space structure, which is what
`toOrderUnitSpace` supplies. -/

end

end Theses.B.Eff
