/-
Copyright: the authors of the theses formalisation.

# SEA §2.3 and §3: an interesting SEA, and Boolean SEAs

A. Westerbaan, B. Westerbaan, J. van de Wetering, *The three types of normal
sequential effect algebras*, Quantum 2020 (arXiv:2004.12749),
`../papers/2004.12749/second.tex`, points **SEA 38**–**SEA 44**.

Conventions: `Papers/README.md`; plan: `Papers/SEA/PLAN.md`.

* §3 (SEA 41–44): Boolean SEAs are Boolean algebras.  SEA 44 is proved
  without the citation of OAP 47 (which is about ω-complete effect monoids):
  the lattice operations are `a ⊓ b = a ⊙ b`, `a ⊔ b = (a⊥ ⊙ b⊥)⊥`, and
  distributivity is a direct computation.  As a by-product the hypotheses
  `OAP47` and `OAP43` of `Papers.SEA.Basic` are discharged here
  (`oap47_holds`, `oap43_holds`, the latter from `Papers.OAP.FloorCeiling`),
  and the Basic declarations that took them are restated without them.
* §2.3 (SEA 38–40): the effect monoid `[0,id]` of linear maps on an ordered
  vector space (SEA 38), and the 2×2 example (SEA 39, 40).
-/
import Papers.SEA.Basic
import Papers.OAP.FloorCeiling

namespace Papers.SEA

open Theses.B.Eff

universe u

/-! ## §2.3 An interesting sequential effect algebra (SEA 38–40) -/

/-! ### SEA 38: `[0,id]` of the linear maps on an ordered vector space -/

/-- The space `R` of linear maps `V → V` of SEA 38 (a type synonym of
`Module.End ℝ V`, to carry the order of SEA 38). -/
def LinEnd (V : Type u) [AddCommGroup V] [Module ℝ V] : Type u := Module.End ℝ V

namespace LinEnd

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

instance : Ring (LinEnd V) := inferInstanceAs (Ring (Module.End ℝ V))
instance : Module ℝ (LinEnd V) := inferInstanceAs (Module ℝ (Module.End ℝ V))
instance : FunLike (LinEnd V) V V := inferInstanceAs (FunLike (Module.End ℝ V) V V)
instance : LinearMapClass (LinEnd V) ℝ V V :=
  inferInstanceAs (LinearMapClass (Module.End ℝ V) ℝ V V)

@[simp] theorem zero_apply (v : V) : (0 : LinEnd V) v = 0 := rfl
@[simp] theorem one_apply (v : V) : (1 : LinEnd V) v = v := rfl
@[simp] theorem add_apply (f g : LinEnd V) (v : V) : (f + g) v = f v + g v := rfl
@[simp] theorem sub_apply (f g : LinEnd V) (v : V) : (f - g) v = f v - g v := rfl
@[simp] theorem neg_apply (f : LinEnd V) (v : V) : (-f) v = -f v := rfl
@[simp] theorem smul_apply (t : ℝ) (f : LinEnd V) (v : V) : (t • f) v = t • f v := rfl
@[simp] theorem mul_apply (f g : LinEnd V) (v : V) : (f * g) v = f (g v) := rfl

theorem ext {f g : LinEnd V} (h : ∀ v, f v = g v) : f = g := DFunLike.ext f g h

end LinEnd

section EndOrder

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V]

/-- **SEA 38** (`ex:effect-monoids`, second.tex:970, Example): the relation
on `R`: `f ≤ g` when `f(v) ≤ g(v)` for all `v ≥ 0` in `V`. -/
def RLe (f g : LinEnd V) : Prop := ∀ v : V, 0 ≤ v → f v ≤ g v

variable (V) in
/-- The positive cone of `V` is *generating*: every vector is a difference of
positive vectors.  This is what makes SEA 38's relation antisymmetric. -/
def Generating : Prop := ∀ v : V, ∃ p q : V, 0 ≤ p ∧ 0 ≤ q ∧ v = p - q

variable [Fact (Generating V)]

/-- **SEA 38**: for a generating cone, `RLe` is a partial order on `R`. -/
instance LinEnd.partialOrder : PartialOrder (LinEnd V) where
  le := RLe
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ h1 h2 v hv := (h1 v hv).trans (h2 v hv)
  le_antisymm f g h1 h2 := LinEnd.ext fun v => by
    obtain ⟨p, q, hp, hq, rfl⟩ := (Fact.out : Generating V) v
    rw [map_sub, map_sub, le_antisymm (h1 p hp) (h2 p hp), le_antisymm (h1 q hq) (h2 q hq)]

theorem LinEnd.le_def {f g : LinEnd V} : f ≤ g ↔ ∀ v : V, 0 ≤ v → f v ≤ g v := Iff.rfl

theorem LinEnd.zero_le_one' : (0 : LinEnd V) ≤ 1 := fun v hv => by simpa using hv

theorem LinEnd.mul_nonneg' (f g : LinEnd V) (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f * g :=
  fun v hv => by
    have h1 : (0 : V) ≤ g v := by simpa using hg v hv
    simpa using hf (g v) h1

variable [IsOrderedAddMonoid V]

instance : IsOrderedAddMonoid (LinEnd V) where
  add_le_add_left f g h c v hv := by
    simp only [LinEnd.add_apply]; exact add_le_add (h v hv) le_rfl

instance [PosSMulMono ℝ V] : PosSMulMono ℝ (LinEnd V) :=
  ⟨fun t ht f g h v hv => by
    simp only [LinEnd.smul_apply]; exact smul_le_smul_of_nonneg_left (h v hv) ht⟩

instance [SMulPosMono ℝ V] : SMulPosMono ℝ (LinEnd V) :=
  ⟨fun f hf s t hst v hv => by
    simp only [LinEnd.smul_apply]
    have : (0 : V) ≤ f v := by simpa using hf v hv
    exact smul_le_smul_of_nonneg_right hst this⟩

/-- **SEA 38** (`ex:effect-monoids`, second.tex:970, Example), first claim:
`R` with `f ≤ g ⟺ ∀ v ≥ 0, f(v) ≤ g(v)` is an ordered vector space — for a
*generating* positive cone (`Fact (Generating V)`, which the print does not
state; see `sea38_not_antisymm_as_printed`). -/
theorem sea38_orderedVectorSpace [PosSMulMono ℝ V] :
    (∀ f g : LinEnd V, f ≤ g ↔ ∀ v : V, 0 ≤ v → f v ≤ g v) ∧
    (∀ f g h : LinEnd V, f ≤ g → f + h ≤ g + h) ∧
    (∀ (t : ℝ) (f g : LinEnd V), 0 ≤ t → f ≤ g → t • f ≤ t • g) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ hfg => add_le_add hfg le_rfl,
    fun _ _ _ ht h => smul_le_smul_of_nonneg_left h ht⟩

/-- **SEA 38** (`ex:effect-monoids`, second.tex:970, Example): `M := [0,id]_R`
with `f ⋁ g = f + g` (defined when `f ≤ id - g`) and `f · g = f ∘ g` is an
effect monoid (the interval effect monoid of SEA 31 for the ordered ring
`R`: composition of positive maps is positive, `id` is the unit). -/
noncomputable instance sea38EM : EffectMonoid (Set.Icc (0 : LinEnd V) 1) :=
  intervalEffectMonoid LinEnd.zero_le_one' LinEnd.mul_nonneg'

/-- **SEA 38**: the sum is `+` and the product is composition. -/
theorem sea38_ops :
    (∀ (f g : Set.Icc (0 : LinEnd V) 1), Perp f g ↔ (f : LinEnd V) + g ≤ 1) ∧
    (∀ (f g : Set.Icc (0 : LinEnd V) 1) (h : Perp f g),
      ((ovee f g h : Set.Icc (0 : LinEnd V) 1) : LinEnd V) = f + g) ∧
    (∀ (f g : Set.Icc (0 : LinEnd V) 1) (v : V),
      ((f * g : Set.Icc (0 : LinEnd V) 1) : LinEnd V) v = (f : LinEnd V) ((g : LinEnd V) v)) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- **SEA 38** (`ex:effect-monoids`, second.tex:970, Example): `M` is a
convex effect algebra (SEA 9 for the ordered vector space `R`). -/
theorem sea38_convex [PosSMulMono ℝ V] [SMulPosMono ℝ V] :
    IsConvex (Set.Icc (0 : LinEnd V) 1) :=
  sea9_interval_convex (LinEnd V) 1 LinEnd.zero_le_one'

end EndOrder

/-- `ℝ` with the discrete order: positive cone `{0}`. -/
def DiscR : Type := ℝ

namespace DiscR

instance : AddCommGroup DiscR := inferInstanceAs (AddCommGroup ℝ)
instance : Module ℝ DiscR := inferInstanceAs (Module ℝ ℝ)
instance : PartialOrder DiscR where
  le x y := x = y
  le_refl _ := rfl
  le_trans _ _ _ h1 h2 := h1.trans h2
  le_antisymm _ _ h _ := h
instance : IsOrderedAddMonoid DiscR where
  add_le_add_left a b h c := by show a + c = b + c; rw [show a = b from h]
instance : PosSMulMono ℝ DiscR :=
  ⟨fun t _ a b h => by show t • a = t • b; rw [show a = b from h]⟩
instance : SMulPosMono ℝ DiscR :=
  ⟨fun b hb s t _ => by
    have : (0 : DiscR) = b := hb
    show s • b = t • b
    rw [← this, smul_zero, smul_zero]⟩

end DiscR

/-- **SEA 38** (`ex:effect-monoids`, second.tex:970, Example), **false as
printed**: "this makes `R` into an ordered vector space" needs the positive
cone of `V` to be generating.  For `V = ℝ` with the discrete order (positive
cone `{0}`, an ordered vector space), `0 ≤ id` and `id ≤ 0` in SEA 38's
relation, yet `0 ≠ id` (so also `id + id ≤ id`, and "`[0,id]_R`" is not an
effect algebra; not formalised).  Repaired: the cone must be generating,
`Fact (Generating V)` in `LinEnd.partialOrder`; SEA 39's cone is
(`V39.generating`). -/
theorem sea38_not_antisymm_as_printed :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℝ V) (_ : PartialOrder V)
      (_ : IsOrderedAddMonoid V) (_ : PosSMulMono ℝ V) (_ : SMulPosMono ℝ V),
      ∃ f g : LinEnd V, RLe f g ∧ RLe g f ∧ f ≠ g := by
  refine ⟨DiscR, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, 1, fun v hv => ?_, fun v hv => ?_, fun h => ?_⟩
  · have : (0 : DiscR) = v := hv
    subst this
    show (0 : LinEnd DiscR) 0 = (1 : LinEnd DiscR) 0
    simp
  · have : (0 : DiscR) = v := hv
    subst this
    show (1 : LinEnd DiscR) 0 = (0 : LinEnd DiscR) 0
    simp
  · have := congrArg (fun f : LinEnd DiscR => f (show DiscR from (1 : ℝ))) h
    exact zero_ne_one (α := ℝ) this

/-! ### SEA 39: the 2×2 example -/

/-- `ℝ²` with SEA 39's positive cone: `(a,b) > 0` iff `a + b > 0`
(so `v ≤ w` iff `v = w` or `φ(w - v) > 0`, `φ(a,b) = a + b`). -/
def V39 : Type := ℝ × ℝ

namespace V39

instance : AddCommGroup V39 := inferInstanceAs (AddCommGroup (ℝ × ℝ))
instance : Module ℝ V39 := inferInstanceAs (Module ℝ (ℝ × ℝ))

/-- The vector `(x, y)`. -/
def mk (x y : ℝ) : V39 := (x, y)
/-- First coordinate. -/
def x (v : V39) : ℝ := Prod.fst (α := ℝ) (β := ℝ) v
/-- Second coordinate. -/
def y (v : V39) : ℝ := Prod.snd (α := ℝ) (β := ℝ) v

@[simp] theorem x_mk (a b : ℝ) : (mk a b).x = a := rfl
@[simp] theorem y_mk (a b : ℝ) : (mk a b).y = b := rfl
@[simp] theorem x_add (v w : V39) : (v + w).x = v.x + w.x := rfl
@[simp] theorem y_add (v w : V39) : (v + w).y = v.y + w.y := rfl
@[simp] theorem x_sub (v w : V39) : (v - w).x = v.x - w.x := rfl
@[simp] theorem y_sub (v w : V39) : (v - w).y = v.y - w.y := rfl
@[simp] theorem x_neg (v : V39) : (-v).x = -v.x := rfl
@[simp] theorem y_neg (v : V39) : (-v).y = -v.y := rfl
@[simp] theorem x_zero : (0 : V39).x = 0 := rfl
@[simp] theorem y_zero : (0 : V39).y = 0 := rfl
@[simp] theorem x_smul (t : ℝ) (v : V39) : (t • v).x = t * v.x := rfl
@[simp] theorem y_smul (t : ℝ) (v : V39) : (t • v).y = t * v.y := rfl

theorem ext {v w : V39} (h1 : v.x = w.x) (h2 : v.y = w.y) : v = w := Prod.ext h1 h2

/-- `φ(a, b) = a + b`. -/
def phi (v : V39) : ℝ := v.x + v.y

@[simp] theorem phi_add (v w : V39) : phi (v + w) = phi v + phi w := by
  simp only [phi, x_add, y_add]; ring
@[simp] theorem phi_sub (v w : V39) : phi (v - w) = phi v - phi w := by
  simp only [phi, x_sub, y_sub]; ring
@[simp] theorem phi_neg (v : V39) : phi (-v) = -phi v := by
  simp only [phi, x_neg, y_neg]; ring
@[simp] theorem phi_smul (t : ℝ) (v : V39) : phi (t • v) = t * phi v := by
  simp only [phi, x_smul, y_smul]; ring
@[simp] theorem phi_zero : phi 0 = 0 := by simp [phi]

/-- **SEA 39** (`ex:assoc-SEA`, second.tex:977): the order of `V`. -/
instance : PartialOrder V39 where
  le v w := v = w ∨ 0 < phi (w - v)
  le_refl _ := Or.inl rfl
  le_trans u v w h1 h2 := by
    rcases h1 with rfl | h1
    · exact h2
    rcases h2 with rfl | h2
    · exact Or.inr h1
    right
    have : w - u = (w - v) + (v - u) := by abel
    rw [this, phi_add]; linarith
  le_antisymm v w h1 h2 := by
    rcases h1 with h1 | h1
    · exact h1
    rcases h2 with h2 | h2
    · exact h2.symm
    exfalso
    have : v - w = -(w - v) := by abel
    rw [this, phi_neg] at h2; linarith

theorem le_def {v w : V39} : v ≤ w ↔ v = w ∨ 0 < phi (w - v) := Iff.rfl

theorem nonneg_iff {v : V39} : 0 ≤ v ↔ v = 0 ∨ 0 < phi v := by
  rw [le_def, sub_zero]; exact or_congr eq_comm Iff.rfl

instance : IsOrderedAddMonoid V39 where
  add_le_add_left a b h c := by
    rcases h with rfl | h
    · exact Or.inl rfl
    · right; rwa [show b + c - (a + c) = b - a by abel]

instance : PosSMulMono ℝ V39 :=
  ⟨fun t ht v w h => by
    rcases h with rfl | h
    · exact Or.inl rfl
    rcases ht.eq_or_lt with rfl | ht
    · left; simp
    · right; rw [← smul_sub, phi_smul]; exact mul_pos ht h⟩

instance : SMulPosMono ℝ V39 :=
  ⟨fun b hb s t hst => by
    rcases nonneg_iff.mp hb with rfl | hb
    · left; simp
    rcases hst.eq_or_lt with rfl | hst
    · exact Or.inl rfl
    · right; rw [← sub_smul, phi_smul]; exact mul_pos (sub_pos.mpr hst) hb⟩

/-- **SEA 39**: the positive cone `{0} ∪ {a + b > 0}` is generating. -/
instance generating : Fact (Generating V39) :=
  ⟨fun v => by
    refine ⟨v + mk (|phi v| + 1) (|phi v| + 1), mk (|phi v| + 1) (|phi v| + 1), ?_, ?_, ?_⟩
    · refine nonneg_iff.mpr (Or.inr ?_)
      rw [phi_add]
      simp only [phi, x_mk, y_mk]
      linarith [neg_abs_le (v.x + v.y), abs_nonneg (v.x + v.y)]
    · refine nonneg_iff.mpr (Or.inr ?_)
      simp only [phi, x_mk, y_mk]
      linarith [abs_nonneg (v.x + v.y)]
    · abel⟩

/-- `e₁ = (1, 0)`. -/
def e1 : V39 := mk 1 0
/-- `e₂ = (0, 1)`. -/
def e2 : V39 := mk 0 1

theorem decomp (v : V39) : v = v.x • e1 + v.y • e2 := ext (by simp [e1, e2]) (by simp [e1, e2])

end V39

open V39

/-- `R` for SEA 39: linear maps on `V39` (2×2 real matrices). -/
abbrev R39 : Type := LinEnd V39

/-- `M = [0, id]_R` for SEA 39. -/
abbrev M39 : Type := Set.Icc (0 : R39) 1

/-- The matrix entries of `A = (a b; c d)`: `a = m11`, `b = m12`, `c = m21`,
`d = m22` (columns `A e₁ = (a, c)`, `A e₂ = (b, d)`). -/
def m11 (A : R39) : ℝ := (A e1).x
/-- Entry `b`. -/
def m12 (A : R39) : ℝ := (A e2).x
/-- Entry `c`. -/
def m21 (A : R39) : ℝ := (A e1).y
/-- Entry `d`. -/
def m22 (A : R39) : ℝ := (A e2).y

/-- The column sums: `col1 A = a + c`, `col2 A = b + d`. -/
def col1 (A : R39) : ℝ := phi (A e1)
/-- Second column sum. -/
def col2 (A : R39) : ℝ := phi (A e2)

theorem col1_eq (A : R39) : col1 A = m11 A + m21 A := rfl
theorem col2_eq (A : R39) : col2 A = m12 A + m22 A := rfl

/-- "Of course `R` is just the space of 2×2 real matrices": `A` acts by its
entries. -/
theorem r39_apply (A : R39) (v : V39) :
    A v = mk (m11 A * v.x + m12 A * v.y) (m21 A * v.x + m22 A * v.y) := by
  conv_lhs => rw [decomp v]
  rw [map_add, map_smul, map_smul]
  refine ext ?_ ?_ <;> simp [m11, m12, m21, m22] <;> ring

theorem phi_apply (A : R39) (v : V39) : phi (A v) = v.x * col1 A + v.y * col2 A := by
  rw [r39_apply]; simp only [phi, x_mk, y_mk, col1_eq, col2_eq]; ring

/-- The matrix `(a b; c d)` as an element of `R`. -/
def mk2 (a b c d : ℝ) : R39 :=
  (show Module.End ℝ V39 from
    { toFun := fun v => mk (a * v.x + b * v.y) (c * v.x + d * v.y)
      map_add' := fun v w => ext (by simp; ring) (by simp; ring)
      map_smul' := fun t v => ext (by simp; ring) (by simp; ring) })

theorem mk2_apply (a b c d : ℝ) (v : V39) :
    mk2 a b c d v = mk (a * v.x + b * v.y) (c * v.x + d * v.y) := rfl

@[simp] theorem col1_mk2 (a b c d : ℝ) : col1 (mk2 a b c d) = a + c := by
  simp [col1, mk2_apply, e1, phi]
@[simp] theorem col2_mk2 (a b c d : ℝ) : col2 (mk2 a b c d) = b + d := by
  simp [col2, mk2_apply, e2, phi]

@[simp] theorem col1_zero : col1 0 = 0 := by simp [col1]
@[simp] theorem col2_zero : col2 0 = 0 := by simp [col2]
@[simp] theorem col1_one : col1 1 = 1 := by simp [col1, e1, phi]
@[simp] theorem col2_one : col2 1 = 1 := by simp [col2, e2, phi]
@[simp] theorem col1_add (A B : R39) : col1 (A + B) = col1 A + col1 B := by simp [col1]
@[simp] theorem col2_add (A B : R39) : col2 (A + B) = col2 A + col2 B := by simp [col2]
@[simp] theorem col1_sub (A B : R39) : col1 (A - B) = col1 A - col1 B := by simp [col1]
@[simp] theorem col2_sub (A B : R39) : col2 (A - B) = col2 A - col2 B := by simp [col2]
@[simp] theorem col1_neg (A : R39) : col1 (-A) = -col1 A := by simp [col1]
@[simp] theorem col2_neg (A : R39) : col2 (-A) = -col2 A := by simp [col2]
@[simp] theorem col1_smul (t : ℝ) (A : R39) : col1 (t • A) = t * col1 A := by simp [col1]
@[simp] theorem col2_smul (t : ℝ) (A : R39) : col2 (t • A) = t * col2 A := by simp [col2]

theorem col1_nsmul (n : ℕ) (A : R39) : col1 (n • A) = n * col1 A := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, col1_add, ih]; push_cast; ring

/-- `col1 (A B) = col1 A · col1 B` when the column sums of `A` agree. -/
theorem col1_mul (A B : R39) (h : col1 A = col2 A) : col1 (A * B) = col1 A * col1 B := by
  show phi (A (B e1)) = _
  rw [phi_apply, ← h]; simp only [col1, phi]; ring

theorem col2_mul (A B : R39) (h : col1 A = col2 A) : col2 (A * B) = col1 A * col2 B := by
  show phi (A (B e2)) = _
  rw [phi_apply, ← h]; simp only [col1, col2, phi]; ring

/-- The positive cone of `R`: `A ≥ 0` iff `A = 0` or the column sums of `A`
agree and are positive. -/
theorem r39_nonneg_iff (A : R39) : 0 ≤ A ↔ A = 0 ∨ (col1 A = col2 A ∧ 0 < col1 A) := by
  constructor
  · intro h
    have hA : ∀ v : V39, 0 < phi v → A v = 0 ∨ 0 < phi (A v) := fun v hv => by
      have : (0 : V39) ≤ A v := by simpa using h v (nonneg_iff.mpr (Or.inr hv))
      exact nonneg_iff.mp this
    have heq : col1 A = col2 A := by
      by_contra hne
      have hab : col1 A - col2 A ≠ 0 := sub_ne_zero.mpr hne
      set t : ℝ := -(|col2 A| + 1) / (col1 A - col2 A) with ht
      have key : t * (col1 A - col2 A) = -(|col2 A| + 1) := by rw [ht]; field_simp
      have hv : phi (mk t (1 - t)) = 1 := by simp [phi]
      have hAv : phi (A (mk t (1 - t))) = t * col1 A + (1 - t) * col2 A := by
        rw [phi_apply]; simp
      have e : t * col1 A + (1 - t) * col2 A = col2 A + t * (col1 A - col2 A) := by ring
      rcases hA _ (by rw [hv]; exact one_pos) with h0 | hpos
      · rw [h0, phi_zero] at hAv
        linarith [le_abs_self (col2 A)]
      · linarith [le_abs_self (col2 A)]
    by_cases hα : 0 < col1 A
    · exact Or.inr ⟨heq, hα⟩
    · left
      have h1 : A e1 = 0 := by
        rcases hA e1 (by simp [e1, phi]) with h0 | hp
        · exact h0
        · exact absurd hp hα
      have h2 : A e2 = 0 := by
        rcases hA e2 (by simp [e2, phi]) with h0 | hp
        · exact h0
        · exact absurd (heq ▸ hp) hα
      refine LinEnd.ext fun v => ?_
      rw [decomp v, map_add, map_smul, map_smul, h1, h2]
      simp
  · rintro (rfl | ⟨heq, hα⟩)
    · exact le_rfl
    · intro v hv
      rw [LinEnd.zero_apply]
      rcases nonneg_iff.mp hv with rfl | hv
      · rw [map_zero]
      · refine nonneg_iff.mpr (Or.inr ?_)
        rw [phi_apply, ← heq]
        have : v.x * col1 A + v.y * col1 A = col1 A * phi v := by simp only [phi]; ring
        rw [this]; exact mul_pos hα hv

/-- `A ≤ B` in `R` iff `A = B` or the column sums of `B - A` agree and are
positive. -/
theorem r39_le_iff (A B : R39) :
    A ≤ B ↔ A = B ∨ (col1 B - col1 A = col2 B - col2 A ∧ col1 A < col1 B) := by
  rw [← sub_nonneg, r39_nonneg_iff, sub_eq_zero, eq_comm, col1_sub, col2_sub, sub_pos]

/-- Membership in `M = [0, id]`, in terms of column sums. -/
theorem m39_mem_iff' (A : R39) : A ∈ Set.Icc (0 : R39) 1 ↔
    (A = 0 ∨ (col1 A = col2 A ∧ 0 < col1 A)) ∧ (A = 1 ∨ (col1 A = col2 A ∧ col1 A < 1)) := by
  rw [Set.mem_Icc, r39_nonneg_iff, r39_le_iff]
  refine and_congr Iff.rfl (or_congr Iff.rfl ?_)
  simp only [col1_one, col2_one]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩

/-- **SEA 39** (`ex:assoc-SEA`, second.tex:977, Example), the membership
criterion "`A = (a b; c d) ∈ M` iff `A = 0` or `A = id` or
`1 > a + c = b + d > 0`" — as printed. -/
theorem sea39_mem_iff (A : R39) : A ∈ Set.Icc (0 : R39) 1 ↔
    A = 0 ∨ A = 1 ∨
      (1 > m11 A + m21 A ∧ m11 A + m21 A = m12 A + m22 A ∧ m12 A + m22 A > 0) := by
  rw [m39_mem_iff', ← col1_eq, ← col2_eq]
  constructor
  · rintro ⟨h0 | ⟨he, hp⟩, h1 | ⟨_, hl⟩⟩
    · exact Or.inl h0
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨hl, he, he ▸ hp⟩)
  · rintro (rfl | rfl | ⟨hl, he, hp⟩)
    · exact ⟨Or.inl rfl, Or.inr ⟨by simp, by simp⟩⟩
    · exact ⟨Or.inr ⟨by simp, by simp⟩, Or.inl rfl⟩
    · exact ⟨Or.inr ⟨he, he ▸ hp⟩, Or.inr ⟨he, hl⟩⟩

/-- The column sums of an element of `M` agree. -/
theorem m39_col_eq (A : M39) : col1 A.1 = col2 A.1 := by
  rcases (m39_mem_iff' A.1).mp A.2 with ⟨h0 | ⟨he, _⟩, _⟩
  · rw [h0]; simp
  · exact he

/-- **SEA 39**: the map `τ : M → [0,1]`, `τ(a b; c d) = a + c = b + d`. -/
def tau (A : M39) : ℝ := col1 A.1

theorem tau_mem (A : M39) : 0 ≤ tau A ∧ tau A ≤ 1 := by
  rcases (m39_mem_iff' A.1).mp A.2 with ⟨h0 | ⟨_, hp⟩, h1 | ⟨_, hl⟩⟩
  · simp [tau, h0]
  · simp [tau, h0]
  · simp [tau, h1]
  · exact ⟨hp.le, hl.le⟩

theorem tau_eq_zero_iff (A : M39) : tau A = 0 ↔ A = 0 := by
  constructor
  · intro h
    rcases (m39_mem_iff' A.1).mp A.2 with ⟨h0 | ⟨_, hp⟩, _⟩
    · exact Subtype.ext h0
    · exact absurd h (ne_of_gt hp)
  · rintro rfl; show col1 0 = 0; simp

/-- The effect-algebra order of `M` in terms of `τ`: `A ≼ B` iff `A = B` or
`τ(A) < τ(B)`. -/
theorem m39_le_iff (A B : M39) : A ≼ B ↔ A = B ∨ tau A < tau B := by
  rw [interval_le_iff, r39_le_iff, m39_col_eq A, m39_col_eq B, Subtype.ext_iff]
  simp only [tau, m39_col_eq, true_and]

/-- **SEA 39** (`ex:assoc-SEA`, second.tex:977, Example): `τ` is monotone,
multiplicative, and `A = 0` iff `τ(A) = 0`. -/
theorem sea39_tau :
    (∀ A B : M39, A ≼ B → tau A ≤ tau B) ∧ (∀ A B : M39, tau (A * B) = tau A * tau B) ∧
    (∀ A : M39, A = 0 ↔ tau A = 0) := by
  refine ⟨fun A B h => ?_, fun A B => col1_mul A.1 B.1 (m39_col_eq A), fun A =>
    (tau_eq_zero_iff A).symm⟩
  rcases (m39_le_iff A B).mp h with rfl | h
  · exact le_rfl
  · exact h.le

/-- **SEA 39**: `A ⊙ B = 0` iff `A = 0` or `B = 0`. -/
theorem sea39_mul_eq_zero (A B : M39) : A * B = 0 ↔ A = 0 ∨ B = 0 := by
  rw [← tau_eq_zero_iff, ← tau_eq_zero_iff, ← tau_eq_zero_iff, sea39_tau.2.1, mul_eq_zero]

/-- **SEA 39** (`ex:assoc-SEA`, second.tex:977, Example): `M` satisfies
`A ⊙ B = 0 ⟺ B ⊙ A = 0`, so it is a SEA with `A ∘ B = A · B` (SEA 31's
`emSEA`). -/
noncomputable instance sea39SEA : SEAlgebra M39 :=
  emSEA M39 fun A B h => by
    rw [sea39_mul_eq_zero] at h ⊢; exact h.symm

/-- **SEA 39**: the sequential product of `M` is composition. -/
theorem sea39_seq (A B : M39) : ((A ⊙ B : M39) : R39) = A.1 * B.1 := rfl

/-- The two elements `(½ ½; 0 0)` and `(0 0; ½ ½)` of `M`. -/
noncomputable def P39 : M39 := ⟨mk2 (1/2) (1/2) 0 0, (sea39_mem_iff _).mpr (Or.inr (Or.inr (by
  simp only [m11, m12, m21, m22, mk2_apply, e1, e2, x_mk, y_mk]; norm_num)))⟩
/-- See `P39`. -/
noncomputable def Q39 : M39 := ⟨mk2 0 0 (1/2) (1/2), (sea39_mem_iff _).mpr (Or.inr (Or.inr (by
  simp only [m11, m12, m21, m22, mk2_apply, e1, e2, x_mk, y_mk]; norm_num)))⟩

/-- **SEA 39** (`ex:assoc-SEA`, second.tex:977; "a non-commutative sequential
effect algebra"): `M` is a SEA that is not commutative; its product is
associative (it is an effect monoid). -/
theorem sea39_noncommutative : ¬ IsCommutativeSEA M39 ∧
    ∀ A B C : M39, A ⊙ B ⊙ C = A ⊙ (B ⊙ C) := by
  refine ⟨fun h => ?_, fun A B C => EffectMonoid.mul_assoc A B C⟩
  have := congrArg (fun A : M39 => (A.1 e1).x) (h P39 Q39)
  simp only [sea39_seq, LinEnd.mul_apply, P39, Q39, mk2_apply, e1, x_mk, y_mk] at this
  norm_num at this

/-- **SEA 39** (`ex:assoc-SEA`, second.tex:977), "convex": `M` is a convex
effect algebra (SEA 38). -/
theorem sea39_convex : IsConvex M39 := sea38_convex

/-! ### SEA 40 and the text around it -/

/-- **SEA 40** (second.tex:996, Remark): an effect algebra *has no non-zero
infinitesimals* ("Archimedean") when the only `a` whose `n`-fold sums `na`
all exist is `0`. -/
def NoInfinitesimals (E : Type u) [EffectAlgebra E] : Prop :=
  ∀ a : E, (∀ n : ℕ, ∃ s, PCM.IsSumOf (List.replicate n a) s) → a = 0

/-- In `M`, an `n`-fold sum of `A` is `n • A`. -/
theorem m39_sum_replicate {A : M39} : ∀ {n : ℕ} {s : M39},
    PCM.IsSumOf (List.replicate n A) s → s.1 = n • A.1
  | 0, s, h => by
    rw [List.replicate_zero, PCM.isSumOf_nil_iff] at h
    subst h; rw [zero_nsmul]; rfl
  | n + 1, s, h => by
    obtain ⟨t, ht, hp, e⟩ := isSumOf_replicate_succ.mp h
    subst e
    show A.1 + t.1 = (n + 1) • A.1
    rw [m39_sum_replicate ht, succ_nsmul']

/-- The text after SEA 39 (second.tex:993): `M` "contains no non-zero
infinitesimal elements: if `nA ∈ M` for all `n`, then `A = 0`". -/
theorem sea39_noInfinitesimals : NoInfinitesimals M39 := by
  intro A h
  have hn : ∀ n : ℕ, (n : ℝ) * tau A ≤ 1 := fun n => by
    obtain ⟨s, hs⟩ := h n
    have := (tau_mem s).2
    rwa [tau, m39_sum_replicate hs, col1_nsmul] at this
  have h0 : tau A ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨n, hn'⟩ := exists_nat_gt (1 / tau A)
    have := hn n
    rw [div_lt_iff₀ hpos] at hn'
    linarith
  exact (tau_eq_zero_iff A).mp (le_antisymm h0 (tau_mem A).1)

/-- The span `W` of `M` in `R` consists of maps with equal column sums. -/
theorem sea40_span_col_eq {X : R39}
    (hX : X ∈ Submodule.span ℝ (Set.range (Subtype.val : M39 → R39))) : col1 X = col2 X := by
  induction hX using Submodule.span_induction with
  | mem x hx => obtain ⟨A, rfl⟩ := hx; exact m39_col_eq A
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul t x _ hx => simp [hx]

/-- The text after SEA 40 (second.tex:1004): on the span `W` of `M` the
order-unit (semi)norm is `‖A‖ = inf{λ > 0 ; -λ id ≤ A ≤ λ id} = |τ(A)|`
(stated for every `A` with equal column sums, which includes `W`,
`sea40_span_col_eq`). -/
theorem sea40_ouNorm (A : R39) (hA : col1 A = col2 A) :
    IsGLB {l : ℝ | 0 < l ∧ -(l • (1 : R39)) ≤ A ∧ A ≤ l • 1} |col1 A| := by
  have up : ∀ l : ℝ, A ≤ l • 1 ↔ A = l • 1 ∨ col1 A < l := fun l => by
    rw [r39_le_iff]; simp [hA]
  have lo : ∀ l : ℝ, -(l • (1 : R39)) ≤ A ↔ -(l • 1) = A ∨ -l < col1 A := fun l => by
    rw [r39_le_iff]; simp [hA]
  refine ⟨fun l ⟨_, h1, h2⟩ => ?_, fun y hy => ?_⟩
  · have a1 : col1 A ≤ l := by
      rcases (up l).mp h2 with h | h
      · rw [h]; simp
      · exact h.le
    have a2 : -l ≤ col1 A := by
      rcases (lo l).mp h1 with h | h
      · rw [← h]; simp
      · exact h.le
    exact abs_le.mpr ⟨by linarith, a1⟩
  · by_contra hy'
    push Not at hy'
    have hl : (|col1 A| + y) / 2 ∈ {l : ℝ | 0 < l ∧ -(l • (1 : R39)) ≤ A ∧ A ≤ l • 1} := by
      have := abs_nonneg (col1 A)
      have h1 := le_abs_self (col1 A)
      have h2 := neg_abs_le (col1 A)
      refine ⟨by linarith, (lo _).mpr (Or.inr (by linarith)), (up _).mpr (Or.inr (by linarith))⟩
    have := hy hl
    linarith

/-- The text after SEA 40 (second.tex:1004): on `W` the norm is
multiplicative, `|τ(AB)| = |τ(A)| |τ(B)|`, whence the sequential product is
continuous. -/
theorem sea40_ouNorm_mul (A B : R39) (hA : col1 A = col2 A) :
    |col1 (A * B)| = |col1 A| * |col1 B| := by
  rw [col1_mul A B hA, abs_mul]

/-- **SEA 40** (second.tex:996, Remark), **false as printed**: "having no
non-zero infinitesimals is equivalent to the order unit semi-norm being a
norm".  In SEA 39's `M` there are no non-zero infinitesimals
(`sea39_noInfinitesimals`), yet on its span `W` the order-unit seminorm is
not a norm: `X = (1 -1; -½ 3/2) - (½ 0; 0 ½) ∈ W` is non-zero with
`-λ id ≤ X ≤ λ id` for every `λ > 0`.  (Likewise the text's "its order-unit
semi-norm is in fact a norm" fails; `‖A‖ = |τ(A)|` is right as a seminorm,
`sea40_ouNorm`.)  What is equivalent to the seminorm being a norm is the
absence of non-zero `a ∈ V` with `-λ1 ≤ a ≤ λ1` for all `λ > 0`, which is not
an effect-algebra condition. -/
theorem sea40_equiv_false_as_printed :
    NoInfinitesimals M39 ∧ ∃ B C : M39, B.1 - C.1 ≠ 0 ∧
      ∀ l : ℝ, 0 < l → -(l • (1 : R39)) ≤ B.1 - C.1 ∧ B.1 - C.1 ≤ l • 1 := by
  refine ⟨sea39_noInfinitesimals, ⟨mk2 1 (-1) (-1/2) (3/2), (sea39_mem_iff _).mpr
    (Or.inr (Or.inr (by simp only [m11, m12, m21, m22, mk2_apply, e1, e2, x_mk, y_mk]; norm_num)))⟩,
    ⟨mk2 (1/2) 0 0 (1/2), (sea39_mem_iff _).mpr
    (Or.inr (Or.inr (by simp only [m11, m12, m21, m22, mk2_apply, e1, e2, x_mk, y_mk]; norm_num)))⟩,
    fun h => ?_, fun l hl => ?_⟩
  · have := congrArg (fun X : R39 => (X e1).x) h
    simp only [LinEnd.sub_apply, mk2_apply, e1, x_mk, y_mk, x_sub, LinEnd.zero_apply, x_zero] at this
    norm_num at this
  · have hc : col1 (mk2 1 (-1) (-1/2) (3/2) - mk2 (1/2) 0 0 (1/2)) = 0 := by simp; norm_num
    have hc2 : col2 (mk2 1 (-1) (-1/2) (3/2) - mk2 (1/2) 0 0 (1/2)) = 0 := by simp; norm_num
    refine ⟨(r39_le_iff _ _).mpr (Or.inr ⟨?_, ?_⟩), (r39_le_iff _ _).mpr (Or.inr ⟨?_, ?_⟩)⟩ <;>
      simp only [hc, hc2, col1_neg, col2_neg, col1_smul, col2_smul, col1_one, col2_one] <;>
      linarith

/-- `t · id ∈ M` for `0 < t < 1`. -/
def scM (t : ℝ) (h0 : 0 < t) (h1 : t < 1) : M39 :=
  ⟨t • 1, (m39_mem_iff' _).mpr ⟨Or.inr ⟨by simp, by simpa using h0⟩,
    Or.inr ⟨by simp, by simpa using h1⟩⟩⟩

@[simp] theorem tau_scM (t : ℝ) (h0 : 0 < t) (h1 : t < 1) : tau (scM t h0 h1) = t := by
  simp [tau, scM]

/-- The text after SEA 40 (second.tex:1011) and the opening of §2.3 (second.tex:969, "a
sequential effect algebra that is not directed complete"): `M` is not
directed complete.  The directed set `{t · id ; 0 < t < ½}` has the two
incomparable minimal upper bounds `½ id` and `½ id + (1 -1; -1 1)`. -/
theorem sea39_not_directedComplete : ¬ DirectedComplete M39 := by
  intro hdc
  let S : Set M39 := {A | ∃ t : ℝ, ∃ (h0 : 0 < t) (h1 : t < 1/2), A = scM t h0 (by linarith)}
  have hS : EDirected S := by
    refine ⟨⟨_, 1/4, by norm_num, by norm_num, rfl⟩, ?_⟩
    rintro _ ⟨s, hs0, hs1, rfl⟩ _ ⟨t, ht0, ht1, rfl⟩
    rcases le_total s t with hst | hst
    · refine ⟨_, ⟨t, ht0, ht1, rfl⟩, (m39_le_iff _ _).mpr ?_, le_refl' _⟩
      rcases hst.eq_or_lt with rfl | hst
      · exact Or.inl rfl
      · exact Or.inr (by simpa using hst)
    · refine ⟨_, ⟨s, hs0, hs1, rfl⟩, le_refl' _, (m39_le_iff _ _).mpr ?_⟩
      rcases hst.eq_or_lt with rfl | hst
      · exact Or.inl rfl
      · exact Or.inr (by simpa using hst)
  obtain ⟨x, hx⟩ := hdc S hS
  let X0 : R39 := mk2 1 (-1) (-1) 1
  let U1 : M39 := scM (1/2) (by norm_num) (by norm_num)
  have hU2 : (1/2 : ℝ) • (1 : R39) + X0 ∈ Set.Icc (0 : R39) 1 :=
    (m39_mem_iff' _).mpr ⟨Or.inr ⟨by simp [X0], by simp [X0]⟩,
      Or.inr ⟨by simp [X0], by simp [X0]; norm_num⟩⟩
  let U2 : M39 := ⟨_, hU2⟩
  have tU2 : tau U2 = 1/2 := by simp [tau, U2, X0]
  have ub : ∀ U : M39, tau U = 1/2 → ∀ s ∈ S, s ≼ U := by
    rintro U hU _ ⟨t, h0, h1, rfl⟩
    exact (m39_le_iff _ _).mpr (Or.inr (by rw [hU, tau_scM]; exact h1))
  have tx : 1/2 ≤ tau x := by
    by_contra hlt
    push Not at hlt
    set t := (max (tau x) 0 + 1/2) / 2 with ht
    have ht0 : 0 < t := by have := le_max_right (tau x) 0; linarith
    have ht1 : t < 1/2 := by
      have := max_lt hlt (show (0 : ℝ) < 1/2 by norm_num); linarith
    have hle := hx.1 _ ⟨t, ht0, ht1, rfl⟩
    have htx : tau x < t := by have := le_max_left (tau x) 0; linarith
    rcases (m39_le_iff _ _).mp hle with h | h
    · rw [← h, tau_scM] at htx; linarith
    · rw [tau_scM] at h; linarith
  have eq_of : ∀ U : M39, tau U = 1/2 → x = U := fun U hU => by
    rcases (m39_le_iff _ _).mp (hx.2 U (ub U hU)) with h | h
    · exact h
    · linarith
  have e := (eq_of U1 (by simp [U1])).symm.trans (eq_of U2 tU2)
  have := congrArg (fun A : M39 => (A.1 e1).x) e
  simp only [U1, U2, scM, X0, LinEnd.add_apply, LinEnd.smul_apply, LinEnd.one_apply,
    mk2_apply, e1, x_add, x_smul, x_mk, y_mk] at this
  norm_num at this

/-! ## §3 Boolean sequential effect algebras (SEA 41–44) -/

section BooleanLemmas

variable {E : Type u} [EffectAlgebra E] [SEAlgebra E]

/-- **SEA 41** (`lem:amultbidempotent`, second.tex:1016, Lemma), first claim:
if `a ⊙ b` is idempotent then `a ⊙ b ≼ b`.  Proof as printed: `a ⊙ b ≼ a` and
`a ⊙ b` idempotent give `a ⊙ b | a` and `(a ⊙ b) ⊙ a = a ⊙ b` (SEA 17.4), so by
S4 `a ⊙ b = (a ⊙ b) ⊙ (a ⊙ b) = ((a ⊙ b) ⊙ a) ⊙ b = (a ⊙ b) ⊙ b`, whence
`a ⊙ b ≼ b` (SEA 17.4). -/
theorem sea41_le {a b : E} (h : IsIdempotent (a ⊙ b)) : a ⊙ b ≼ b := by
  have hpa : a ⊙ b ≼ a := seq_le_left a b
  have e1 : a ⊙ b ⊙ a = a ⊙ b := ((sea17_4 h a).1).mp hpa
  have e2 : a ⊙ (a ⊙ b) = a ⊙ b := ((sea17_4 h a).2.1).mp hpa
  have hc : Commutes (a ⊙ b) a := by show a ⊙ b ⊙ a = a ⊙ (a ⊙ b); rw [e1, e2]
  have hh : a ⊙ b ⊙ (a ⊙ b) = a ⊙ b := h
  have : a ⊙ b ⊙ b = a ⊙ b := by
    calc a ⊙ b ⊙ b = a ⊙ b ⊙ a ⊙ b := by rw [e1]
      _ = a ⊙ b ⊙ (a ⊙ b) := (hc.assoc b).symm
      _ = a ⊙ b := hh
  exact ((sea17_4 h b).1).mpr this

/-- **SEA 41** (`lem:amultbidempotent`, second.tex:1016, Lemma), second claim:
if `a ⊙ b` and `a ⊙ b⊥` are both idempotent, then `a ⊙ b = b ⊙ a`.  Proof as
printed: `a ⊙ b⊥ ≼ b⊥` gives `b ⊙ (a ⊙ b⊥) = 0` (SEA 17.4), so
`b ⊙ a = b ⊙ (a ⊙ b) ⋁ b ⊙ (a ⊙ b⊥) = b ⊙ (a ⊙ b)`, and `a ⊙ b ≼ b` gives
`b ⊙ (a ⊙ b) = a ⊙ b`. -/
theorem sea41_comm {a b : E} (h1 : IsIdempotent (a ⊙ b)) (h2 : IsIdempotent (a ⊙ orth b)) :
    a ⊙ b = b ⊙ a := by
  have hle1 : a ⊙ b ≼ b := sea41_le h1
  have hle2 : a ⊙ orth b ≼ orth b := sea41_le h2
  have z : b ⊙ (a ⊙ orth b) = 0 := by
    have := ((sea17_4 h2 (orth b)).2.2.1).mp hle2
    rwa [orth_orth] at this
  have e : b ⊙ (a ⊙ b) = a ⊙ b := ((sea17_4 h1 b).2.1).mp hle1
  obtain ⟨hs, es⟩ := seq_split a b
  obtain ⟨h', e'⟩ := seq_ovee b hs
  have : b ⊙ a = a ⊙ b := by
    calc b ⊙ a = b ⊙ ovee (a ⊙ b) (a ⊙ orth b) hs := by rw [es]
      _ = ovee (b ⊙ (a ⊙ b)) (b ⊙ (a ⊙ orth b)) h' := e'
      _ = ovee (a ⊙ b) 0 (PCM.perp_zero _) := PCM.ovee_congr e z _ _
      _ = a ⊙ b := ovee_zero_eq _ _
  exact this.symm

/-- **SEA 41** (`lem:amultbidempotent`, second.tex:1016, Lemma), both claims. -/
theorem sea41 {a b : E} (h1 : IsIdempotent (a ⊙ b)) :
    a ⊙ b ≼ b ∧ (IsIdempotent (a ⊙ orth b) → a ⊙ b = b ⊙ a) :=
  ⟨sea41_le h1, sea41_comm h1⟩

/-- **SEA 42** (`cor:booleans-central`, second.tex:1048, Corollary): a Boolean
idempotent is central.  Proof as printed: `p ⊙ b` and `p ⊙ b⊥` lie below the
Boolean idempotent `p`, so they are idempotents, and SEA 41 applies. -/
theorem sea42_central {p : E} (hp : IsBooleanIdempotent p) : IsCentral p := fun b =>
  sea41_comm (hp.2 _ (seq_le_left p b)) (hp.2 _ (seq_le_left p (orth b)))

/-- **SEA 43** (second.tex:1093, Proposition), first claim: for idempotents
`p, q`, `p ⊙ q` is idempotent iff `p | q`.  Proof as printed: `⇐` is the
computation `(p⊙q)(p⊙q) = p⊙(q⊙(q⊙p)) = p⊙(q⊙p) = p⊙(p⊙q) = p⊙q` by S4;
for `⇒`, `p ⊙ q⊥` is idempotent too (it is `p ⊖ p ⊙ q`, SEA 17.7) and SEA 41
applies. -/
theorem sea43_iff {p q : E} (hp : IsIdempotent p) (hq : IsIdempotent q) :
    IsIdempotent (p ⊙ q) ↔ Commutes p q := by
  constructor
  · intro h
    obtain ⟨hs, es⟩ := seq_split p q
    have h2 : IsIdempotent (p ⊙ orth q) := (sea17_7 h hs).mpr (by rw [es]; exact hp)
    exact sea41_comm h h2
  · intro hc
    have hp' : p ⊙ p = p := hp
    have hq' : q ⊙ q = q := hq
    have hc' : p ⊙ q = q ⊙ p := hc
    have e1 : q ⊙ (p ⊙ q) = p ⊙ q := by
      rw [hc', (commutes_refl q).assoc, hq']
    show p ⊙ q ⊙ (p ⊙ q) = p ⊙ q
    rw [← hc.assoc, e1, (commutes_refl p).assoc, hp']

/-- **SEA 43** (second.tex:1093, Proposition), second claim: if the
idempotents `p, q` commute, `p ⊙ q` is the infimum of `p` and `q`.  Proof as
printed: a lower bound by SEA 41; for `r ≼ p, q`, `r ⊙ p = r = r ⊙ q` and
`r | p`, so `r ⊙ (p ⊙ q) = (r ⊙ p) ⊙ q = r`, whence `r ≼ p ⊙ q`. -/
theorem sea43_inf {p q : E} (hp : IsIdempotent p) (hq : IsIdempotent q) (hc : Commutes p q) :
    EIsInf {p, q} (p ⊙ q) := by
  have hi := (sea43_iff hp hq).mpr hc
  refine ⟨?_, ?_⟩
  · rintro s (rfl | rfl)
    · exact seq_le_left _ _
    · exact sea41_le hi
  · intro r hr
    have hrp : r ≼ p := hr p (Set.mem_insert _ _)
    have hrq : r ≼ q := hr q (Set.mem_insert_of_mem _ rfl)
    have e1 : r ⊙ p = r := ((sea17_5 hp r).2.1).mp hrp
    have e2 : p ⊙ r = r := ((sea17_5 hp r).1).mp hrp
    have e3 : r ⊙ q = r := ((sea17_5 hq r).2.1).mp hrq
    have hc' : Commutes r p := by show r ⊙ p = p ⊙ r; rw [e1, e2]
    have : r ⊙ (p ⊙ q) = r := by rw [hc'.assoc, e1, e3]
    exact ((sea17_5 hi r).2.1).mpr this

/-- **SEA 43** (second.tex:1093, Proposition), both claims. -/
theorem sea43 {p q : E} (hp : IsIdempotent p) (hq : IsIdempotent q) :
    (IsIdempotent (p ⊙ q) ↔ Commutes p q) ∧ (Commutes p q → EIsInf {p, q} (p ⊙ q)) :=
  ⟨sea43_iff hp hq, sea43_inf hp hq⟩

end BooleanLemmas

/-! ### SEA 44: a Boolean SEA is a Boolean algebra -/

section BooleanSEA

variable {E : Type u} [EffectAlgebra E] [SEAlgebra E]

/-- The effect-algebra order `≼`, bundled as a partial order. -/
@[reducible] def boolPO (E : Type u) [EffectAlgebra E] : PartialOrder E where
  le := PCM.le
  le_refl := le_refl'
  le_trans _ _ _ := le_trans'
  le_antisymm _ _ := le_antisymm'

variable (hB : IsBooleanSEA E)
include hB

/-- In a Boolean SEA all elements commute (SEA 43). -/
theorem bool_comm (a b : E) : a ⊙ b = b ⊙ a := (sea43_iff (hB a) (hB b)).mp (hB _)

/-- In a Boolean SEA `⊙` is associative (S4 and `bool_comm`). -/
theorem bool_assoc (a b c : E) : a ⊙ b ⊙ c = a ⊙ (b ⊙ c) :=
  ((show Commutes a b from bool_comm hB a b).assoc c).symm

/-- In a Boolean SEA `a ⊙ b` is the infimum of `a` and `b` (SEA 43). -/
theorem bool_isInf (a b : E) : EIsInf {a, b} (a ⊙ b) :=
  sea43_inf (hB a) (hB b) (bool_comm hB a b)

/-- In a Boolean SEA `(a⊥ ⊙ b⊥)⊥` is the supremum of `a` and `b`. -/
theorem bool_isSup (a b : E) : EIsSup {a, b} (orth (orth a ⊙ orth b)) := by
  have := eIsSup_orth_of_eIsInf (bool_isInf hB (orth a) (orth b))
  rwa [Set.image_pair, orth_orth, orth_orth] at this

/-- `a ⊙ (a ⊙ b)⊥ = a ⊙ b⊥` in a Boolean SEA (cancel `a ⊙ b` from the two
splittings of `a`). -/
theorem bool_seq_orth_seq (a b : E) : a ⊙ orth (a ⊙ b) = a ⊙ orth b := by
  obtain ⟨h1, e1⟩ := seq_split a (a ⊙ b)
  obtain ⟨h2, e2⟩ := seq_split a b
  have eab : a ⊙ (a ⊙ b) = a ⊙ b := by
    rw [← bool_assoc hB]; exact congrArg (· ⊙ b) (hB a)
  have h1' : Perp (a ⊙ b) (a ⊙ orth (a ⊙ b)) := by
    have := h1; rwa [eab] at this
  refine cancel_left h1' h2 ?_
  rw [← PCM.ovee_congr eab rfl h1 h1', e1, e2]

/-- `a ∧ (b ∨ c) ≤ (a ∧ b) ∨ (a ∧ c)`: `x ≼ s` for the idempotent `s` iff
`x ⊙ s⊥ = 0` (SEA 17.5), and `a (b ∨ c) (ab)⊥ (ac)⊥ = a (b ∨ c) b⊥ c⊥
= a (b ∨ c)(b ∨ c)⊥ = 0`. -/
theorem bool_distrib (a b c : E) :
    a ⊙ orth (orth b ⊙ orth c) ≼ orth (orth (a ⊙ b) ⊙ orth (a ⊙ c)) := by
  refine ((sea17_5 (hB _) _).2.2.1).mpr ?_
  rw [orth_orth]
  let _ : CommSemigroup E :=
    { mul := fun x y => x ⊙ y, mul_assoc := bool_assoc hB, mul_comm := bool_comm hB }
  have haa : a * a = a := hB a
  have hb : a * orth (a * b) = a * orth b := bool_seq_orth_seq hB a b
  have hc : a * orth (a * c) = a * orth c := bool_seq_orth_seq hB a c
  have hd : orth (orth (orth b * orth c)) * orth (orth b * orth c) = 0 :=
    (hB (orth (orth b * orth c))).orth_seq
  rw [orth_orth] at hd
  have hz : a * a * 0 = 0 := seq_zero _
  show a * orth (orth b * orth c) * (orth (a * b) * orth (a * c)) = 0
  calc a * orth (orth b * orth c) * (orth (a * b) * orth (a * c))
      = a * a * orth (orth b * orth c) * (orth (a * b) * orth (a * c)) := by rw [haa]
    _ = (a * orth (a * b)) * (a * orth (a * c)) * orth (orth b * orth c) := by ac_rfl
    _ = (a * orth b) * (a * orth c) * orth (orth b * orth c) := by rw [hb, hc]
    _ = a * a * ((orth b * orth c) * orth (orth b * orth c)) := by ac_rfl
    _ = 0 := by rw [hd, hz]

/-- `a ⊥ b` iff `a ⊙ b = 0` in a Boolean SEA. -/
theorem bool_perp_iff (a b : E) : Perp a b ↔ a ⊙ b = 0 := by
  rw [perp_iff_le_orth, (sea17_5 (hB (orth b)) a).2.2.1, orth_orth]

/-- `a ⋁ b = (a⊥ ⊙ b⊥)⊥` in a Boolean SEA: both are the supremum of `a, b`
(SEA 18 for the sum). -/
theorem bool_ovee_eq (a b : E) (h : Perp a b) : ovee a b h = orth (orth a ⊙ orth b) := by
  refine EIsSup.unique ?_ (bool_isSup hB a b)
  refine ⟨?_, fun u hu => ?_⟩
  · rintro s (rfl | rfl)
    · exact left_le_ovee h
    · exact right_le_ovee h
  · exact sea18_ovee_le (hB u) (hu a (Set.mem_insert _ _)) (hu b (Set.mem_insert_of_mem _ rfl)) h

/-- The lattice of a Boolean SEA: `≤` is `≼`, `a ⊓ b = a ⊙ b`,
`a ⊔ b = (a⊥ ⊙ b⊥)⊥`. -/
@[reducible] noncomputable def boolLattice : Lattice E :=
  { boolPO E with
    sup := fun a b => orth (orth a ⊙ orth b)
    inf := fun a b => a ⊙ b
    le_sup_left := fun a b => (bool_isSup hB a b).1 a (Set.mem_insert _ _)
    le_sup_right := fun a b => (bool_isSup hB a b).1 b (Set.mem_insert_of_mem _ rfl)
    sup_le := fun a b c ha hb => (bool_isSup hB a b).2 c (by
      rintro s (rfl | rfl)
      · exact ha
      · exact hb)
    inf_le_left := fun a b => (bool_isInf hB a b).1 a (Set.mem_insert _ _)
    inf_le_right := fun a b => (bool_isInf hB a b).1 b (Set.mem_insert_of_mem _ rfl)
    le_inf := fun a b c hb hc => (bool_isInf hB b c).2 a (by
      rintro s (rfl | rfl)
      · exact hb
      · exact hc) }

/-- **SEA 44** (`prop:SEAsharpisBoolean`, second.tex:1121): the Boolean
algebra of a Boolean SEA, on the carrier `E` itself: `≤` is `≼`,
`a ⊓ b = a ⊙ b`, `a ⊔ b = (a⊥ ⊙ b⊥)⊥`, `⊥ = 0`, `⊤ = 1`, `aᶜ = a⊥`. -/
@[reducible] noncomputable def boolBA : BooleanAlgebra E :=
  letI lat : Lattice E := boolLattice hB
  letI dl : DistribLattice E :=
    DistribLattice.ofInfSupLe fun a b c => bool_distrib hB a b c
  { dl with
    compl := orth
    top := 1
    bot := 0
    inf_compl_le_bot := fun x => by
      show x ⊙ orth x ≼ (0 : E)
      rw [(hB x).seq_orth]
      exact le_refl' 0
    top_le_sup_compl := fun x => by
      show (1 : E) ≼ orth (orth x ⊙ orth (orth x))
      rw [orth_orth, (hB x).orth_seq, eabasics_orth_zero]
      exact le_refl' 1
    le_top := fun a => le_one' a
    bot_le := fun a => zero_le' a }

/-- **SEA 44** (`prop:SEAsharpisBoolean`, second.tex:1121, Proposition),
first two claims: a Boolean SEA `E` is a Boolean algebra, and
`a ⊙ b = a ∧ b`.  Precisely: there is a Boolean algebra structure on `E`
whose order is the effect-algebra order, whose meet is `⊙`, and whose
effect-algebra structure (SEA 3: `a ⊥ b ⟺ a ∧ b = 0`, `a ⋁ b = a ∨ b`,
`a⊥ = aᶜ`) is that of `E`.

Proof as printed (all elements are idempotent, so by SEA 43 they commute and
`a ⊙ b = a ∧ b`), except for its last step: the print concludes by citing
OAP 47, which is about ω-complete Boolean effect monoids; here the lattice is
built directly (`boolBA`), with `a ∨ b = (a⊥ ⊙ b⊥)⊥` and distributivity by
computation (`bool_distrib`). -/
theorem sea44_booleanAlgebra :
    ∃ _ : BooleanAlgebra E, (∀ a b : E, a ≤ b ↔ a ≼ b) ∧ (∀ a b : E, a ⊙ b = a ⊓ b) ∧
      (∀ a b : E, Perp a b ↔ a ⊓ b = ⊥) ∧ (∀ (a b : E) (h : Perp a b), ovee a b h = a ⊔ b) ∧
      (0 : E) = ⊥ ∧ (1 : E) = ⊤ ∧ ∀ a : E, orth a = aᶜ :=
  ⟨boolBA hB, fun _ _ => Iff.rfl, fun _ _ => rfl, bool_perp_iff hB, bool_ovee_eq hB,
    rfl, rfl, fun _ => rfl⟩

/-- In a directed-complete Boolean SEA every subset has a supremum (for the
order `≼`): the finite joins of `S` form a directed set whose supremum is
that of `S`. -/
theorem bool_exists_lub (hdc : DirectedComplete E) (S : Set E) :
    ∃ x, @IsLUB E (boolBA hB).toPartialOrder.toPreorder.toLE S x := by
  let _ := boolBA hB
  let T : Set E := {x | ∃ F : Finset E, ↑F ⊆ S ∧ x = F.sup id}
  have hT : EDirected T := by
    refine ⟨⟨_, ∅, by simp, rfl⟩, ?_⟩
    rintro _ ⟨F, hF, rfl⟩ _ ⟨G, hG, rfl⟩
    classical
    refine ⟨(F ∪ G).sup id, ⟨F ∪ G, by
      rw [Finset.coe_union]; exact Set.union_subset hF hG, rfl⟩, ?_, ?_⟩
    · show F.sup id ≤ (F ∪ G).sup id
      exact Finset.sup_mono (f := id) (Finset.subset_union_left (s₂ := G))
    · show G.sup id ≤ (F ∪ G).sup id
      exact Finset.sup_mono (f := id) (Finset.subset_union_right (s₁ := F))
  obtain ⟨x, hx⟩ := hdc T hT
  refine ⟨x, fun s hs => ?_, fun y hy => ?_⟩
  · have : s ∈ T := ⟨{s}, by simpa using hs, by simp⟩
    exact hx.1 s this
  · refine hx.2 y ?_
    rintro _ ⟨F, hF, rfl⟩
    exact Finset.sup_le fun b hb => hy (hF hb)

/-- The complete Boolean algebra of a directed-complete Boolean SEA. -/
@[reducible] noncomputable def boolCBA (hdc : DirectedComplete E) : CompleteBooleanAlgebra E :=
  letI := boolBA hB
  { boolBA hB with
    sSup := fun S => Classical.choose (bool_exists_lub hB hdc S)
    sInf := fun S => (Classical.choose (bool_exists_lub hB hdc (compl '' S)))ᶜ
    isLUB_sSup := fun S => Classical.choose_spec (bool_exists_lub hB hdc S)
    isGLB_sInf := fun S => by
      refine ⟨fun s hs => ?_, fun y hy => ?_⟩
      · show (Classical.choose (bool_exists_lub hB hdc (compl '' S)))ᶜ ≤ s
        rw [compl_le_iff_compl_le]
        exact (Classical.choose_spec (bool_exists_lub hB hdc (compl '' S))).1 ⟨s, hs, rfl⟩
      · show y ≤ (Classical.choose (bool_exists_lub hB hdc (compl '' S)))ᶜ
        rw [le_compl_comm]
        refine (Classical.choose_spec (bool_exists_lub hB hdc (compl '' S))).2 ?_
        rintro _ ⟨s, hs, rfl⟩
        exact compl_le_compl (hy hs) }

/-- **SEA 44** for directed-complete Boolean SEAs: `E` is a *complete*
Boolean algebra (with the properties of `sea44_booleanAlgebra`).  Only
directed completeness is used; the print's hypothesis "normal" is
`sea44_complete`. -/
theorem sea44_complete_of_dc (hdc : DirectedComplete E) :
    ∃ _ : CompleteBooleanAlgebra E, (∀ a b : E, a ≤ b ↔ a ≼ b) ∧ (∀ a b : E, a ⊙ b = a ⊓ b) ∧
      (∀ a b : E, Perp a b ↔ a ⊓ b = ⊥) ∧ (∀ (a b : E) (h : Perp a b), ovee a b h = a ⊔ b) ∧
      (0 : E) = ⊥ ∧ (1 : E) = ⊤ ∧ ∀ a : E, orth a = aᶜ :=
  ⟨boolCBA hB hdc, fun _ _ => Iff.rfl, fun _ _ => rfl, bool_perp_iff hB, bool_ovee_eq hB,
    rfl, rfl, fun _ => rfl⟩

end BooleanSEA

/-- **SEA 44** (`prop:SEAsharpisBoolean`, second.tex:1121, Proposition), last
claim: a normal Boolean SEA is a complete Boolean algebra.  Proof: the
print's "directed-complete Boolean effect monoid … OAP 47"; here
`sea44_complete_of_dc` (the finite joins of a set are directed). -/
theorem sea44_complete {E : Type u} [EffectAlgebra E] [NormalSEA E] (hB : IsBooleanSEA E) :
    ∃ _ : CompleteBooleanAlgebra E, (∀ a b : E, a ≤ b ↔ a ≼ b) ∧ (∀ a b : E, a ⊙ b = a ⊓ b) ∧
      (∀ a b : E, Perp a b ↔ a ⊓ b = ⊥) ∧ (∀ (a b : E) (h : Perp a b), ovee a b h = a ⊔ b) ∧
      (0 : E) = ⊥ ∧ (1 : E) = ⊤ ∧ ∀ a : E, orth a = aᶜ :=
  sea44_complete_of_dc hB NormalSEA.directedComplete

/-! ### Discharging `OAP47` and `OAP43` -/

/-- The hypothesis `OAP47` of `Papers.SEA.Basic` (OAP 47 in the
directed-complete form SEA uses) holds: a Boolean effect monoid is
commutative (its elements are idempotent, hence central, OAP 20 =
`em_idempotent_central`), hence a Boolean SEA, hence (SEA 44) a complete
Boolean algebra when directed complete; the identity map is the
isomorphism. -/
theorem oap47_holds : OAP47.{u} := by
  intro M _ hdc hB
  have hc : EffectMonoid.Commutative M := fun a b => em_idempotent_central (hB a) b
  let _ : SEAlgebra M := commEMToSEA M hc
  have hB' : IsBooleanSEA M := hB
  let cba : CompleteBooleanAlgebra M := boolCBA hB' hdc
  refine ⟨M, cba, ⟨@EMIso.mk M M _ (@booleanEffectMonoid M cba.toBooleanAlgebra)
    (@EAIso.mk M M _ (@booleanEffectAlgebra M cba.toBooleanAlgebra) (Equiv.refl M) rfl
      (fun a b => (bool_perp_iff hB' a b).symm) (fun a b h _ => bool_ovee_eq hB' a b h))
    (fun _ _ => rfl)⟩⟩

section OAP43

open scoped Papers.OAP

/-- The hypothesis `OAP43` of `Papers.SEA.Basic` holds: it is OAP 43 point 1
(`Papers.OAP.oap43_1`, with `b' = 1`); a directed-complete effect algebra is
ω-complete. -/
theorem oap43_holds : OAP43.{u} := by
  intro M _ hdc a S x hS hx
  have : Papers.OAP.OmegaComplete M := ⟨fun f hf => by
    obtain ⟨s, hs⟩ := hdc _ (eDirected_range_of_monotone fun n => hf (Nat.le_succ n))
    exact ⟨s, fun _ hy => hs.1 _ hy, fun _ hy => hs.2 _ fun _ hz => hy hz⟩⟩
  have hx' : IsLUB S x := ⟨fun _ hy => hx.1 _ hy, fun _ hy => hx.2 _ fun _ hz => hy hz⟩
  have := Papers.OAP.oap43_1 hS.1 hx' a 1
  simp only [EffectMonoid.mul_one] at this
  exact ⟨fun _ hy => this.1 hy, fun _ hy => this.2 fun _ hz => hy _ hz⟩

end OAP43

/-- **SEA 32** (`prop:commutativemonoidissequential`, second.tex:878,
Example), second claim, ⇐, with `OAP43` discharged (`oap43_holds`): a
directed-complete commutative effect monoid is a normal commutative SEA with
`a ∘ b := a ⊙ b`. -/
@[instance_reducible] noncomputable def sea32_dc_to_normal' (M : Type u) [EffectMonoid M]
    (hc : EffectMonoid.Commutative M) (hdc : DirectedComplete M) : NormalSEA M :=
  sea32_dc_to_normal oap43_holds M hc hdc

/-- **SEA 30** (`ex:booleanalgebra`, second.tex:844, Example), the converse,
in the directed-complete form (`OAP47`, discharged): a directed-complete
Boolean effect monoid is a complete Boolean algebra. -/
theorem sea30_converse (M : Type u) [EffectMonoid M] (hdc : DirectedComplete M)
    (hB : IsBooleanEM M) :
    ∃ (B : Type u) (_ : CompleteBooleanAlgebra B), Nonempty (@EMIso M B _ (booleanEffectMonoid B)) :=
  oap47_holds M hdc hB

/-- **SEA 36** (`seaspectral`, second.tex:917, Corollary), with `OAP47`
discharged (`oap47_holds`); still takes SEA 35 (OAP 57 + 69) as a hypothesis. -/
theorem sea36_spectral' (h35 : SEA35.{u}) {E : Type u} [EffectAlgebra E] [NormalSEA E] (a : E) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X),
      ExtremallyDisconnected X ∧ ∃ (B : Type u) (_ : CompleteBooleanAlgebra B),
        Nonempty (@EMIso (bicommutantSub ({a} : Set E)).carrier (CXI X × B)
          (bicommEM {a} (singleton_commuting a)) (@prodEM _ _ _ (booleanEffectMonoid B))) :=
  sea36_spectral h35 oap47_holds a

/-- **SEA 37** (second.tex:933, Corollary), with `OAP47` discharged
(`oap47_holds`); still takes SEA 35 (OAP 57 + 69) as a hypothesis. -/
theorem sea37_sqrt' (h35 : SEA35.{u}) {E : Type u} [EffectAlgebra E] [NormalSEA E] (a : E) :
    ∃! b : E, b ⊙ b = a :=
  sea37_sqrt h35 oap47_holds a

end Papers.SEA
