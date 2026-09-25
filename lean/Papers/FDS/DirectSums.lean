/-
FDS: T. Fritz, B. Westerbaan, *The universal property of infinite direct sums
in C*-categories and W*-categories*, Appl. Categ. Structures 2019,
arXiv:1907.04714 — `../papers/1907.04714/direct_sums.tex`.

Points are numbered within sections (`**FDS 5.1**` is Theorem 5.1); the
index is `../papers/FDS-points.csv`, the plan `Papers/FDS/PLAN.md`.

Conventions (see `PLAN.md`):

* A category enriched in complex vector spaces is Mathlib's
  `[Category C] [Preadditive C] [Linear ℂ C]`; the involution, the norms and
  the C*/W* axioms are the classes `StarCategory`, `NormedStarCategory`,
  `CStarCategory`, `WStarCategory` below.  Composition is Mathlib's
  diagrammatic `f ≫ g`, which is the paper's `g f` (= `g ∘ f`); the paper's
  `a*` is `a†`.
* `End A` is a C*-algebra, ordered by its spectral (= star) order; in it
  `x * y = y ≫ x`, as in Mathlib's `End`.
* Hilbert modules are mirrored as in the theses tree (`Theses/B/Dils`, and
  Mathlib's `CStarModule`): `A ⟶ B` is a *left* `End B`-module
  (`b • f = f ≫ b`) with inner product `⟪f, g⟫ = f† ≫ g` (the paper's
  `g f*`).  The paper's `C(B,A)` as a right `C(B,B)`-module with
  `⟨g, f⟩ = g* f` is its image under `†`.
-/
import Theses.B.Dils.Pure

open CategoryTheory CategoryTheory.Limits
open scoped ComplexOrder CStarAlgebra
open Filter Topology Theses Theses.A.VN Theses.B.Dils

universe v u w v₂ u₂ u₁

noncomputable section

namespace Papers.FDS

/-! ## Section 2: C*-categories and W*-categories -/

section Defs

variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]

/-- **FDS 2.1** (direct_sums.tex:226, Definition): a **complex `*`-category**.
Condition 1 (enrichment over complex vector spaces, bilinear composition) is
`[Preadditive C] [Linear ℂ C]`; the fields are condition 2 (an
identity-on-objects, involutive, conjugate-linear contravariant functor
`a ↦ a†`) and condition 3 (a) `a*a = b*b` for some endomorphism `b`,
(b) `a*a = 0 ⇒ a = 0`.  In diagrammatic order `a*a` is `a ≫ a†`. -/
class StarCategory where
  /-- the involution `a ↦ a*`, written `a†` -/
  adj : ∀ {X Y : C}, (X ⟶ Y) → (Y ⟶ X)
  adj_id : ∀ X : C, adj (𝟙 X) = 𝟙 X
  adj_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), adj (f ≫ g) = adj g ≫ adj f
  adj_adj : ∀ {X Y : C} (f : X ⟶ Y), adj (adj f) = f
  adj_add : ∀ {X Y : C} (f g : X ⟶ Y), adj (f + g) = adj f + adj g
  adj_smul : ∀ {X Y : C} (c : ℂ) (f : X ⟶ Y), adj (c • f) = (starRingEnd ℂ c) • adj f
  exists_eq_adj_comp : ∀ {X Y : C} (a : X ⟶ Y), ∃ b : X ⟶ X, a ≫ adj a = b ≫ adj b
  eq_zero_of_comp_adj : ∀ {X Y : C} (a : X ⟶ Y), a ≫ adj a = 0 → a = 0

@[inherit_doc] scoped postfix:max "†" => StarCategory.adj

/-- **FDS 2.2** (direct_sums.tex:255, Definition), part 1: a **normed
`*`-category**: every hom-set is a normed space (`homNorm`, `homCore`) and
`‖ab‖ ≤ ‖a‖ ‖b‖`.  The normed-group and normed-space instances on `X ⟶ Y`
are derived from these fields (`homNormedAddCommGroup`), so that the
additive group is the `Preadditive` one. -/
class NormedStarCategory [StarCategory C] where
  /-- the norm of each hom-set -/
  homNorm : ∀ X Y : C, Norm (X ⟶ Y)
  /-- it is a norm making `X ⟶ Y` a complex normed space -/
  homCore : ∀ X Y : C, NormedSpace.Core ℂ (X ⟶ Y)
  norm_comp_le : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), ‖f ≫ g‖ ≤ ‖f‖ * ‖g‖

attribute [instance] NormedStarCategory.homNorm

variable {C} in
/-- The normed-group structure of a hom-set of a normed `*`-category. -/
instance homNormedAddCommGroup [StarCategory C] [NormedStarCategory C] (X Y : C) :
    NormedAddCommGroup (X ⟶ Y) :=
  NormedAddCommGroup.ofCore (NormedStarCategory.homCore X Y)

variable {C} in
instance homNormedSpace [StarCategory C] [NormedStarCategory C] (X Y : C) :
    NormedSpace ℂ (X ⟶ Y) :=
  NormedSpace.ofCore (NormedStarCategory.homCore X Y)

/-- **FDS 2.2** (direct_sums.tex:255, Definition), part 2: a normed
`*`-category is a **C\*-category** when every hom-set is complete and the
C*-identity `‖a‖² = ‖a*a‖` holds (in diagrammatic order `a*a = a ≫ a†`). -/
class CStarCategory [StarCategory C] [NormedStarCategory C] : Prop where
  complete : ∀ X Y : C, CompleteSpace (X ⟶ Y)
  norm_comp_adj : ∀ {X Y : C} (f : X ⟶ Y), ‖f ≫ f†‖ = ‖f‖ ^ 2

attribute [instance] CStarCategory.complete

end Defs

/-! ### Elementary facts in a C*-category, and the C*-algebra `End A` -/

section Basic

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [StarCategory C]

namespace StarCategory

@[simp] theorem adj_adj' {X Y : C} (f : X ⟶ Y) : f†† = f := adj_adj f

@[simp] theorem adj_comp' {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g)† = g† ≫ f† :=
  adj_comp f g

@[simp] theorem adj_id' (X : C) : (𝟙 X)† = 𝟙 X := adj_id X

@[simp] theorem adj_add' {X Y : C} (f g : X ⟶ Y) : (f + g)† = f† + g† := adj_add f g

theorem adj_injective {X Y : C} : Function.Injective (adj : (X ⟶ Y) → (Y ⟶ X)) :=
  fun f g h => by rw [← adj_adj f, h, adj_adj]

/-- The involution as an additive equivalence. -/
def adjAddEquiv (X Y : C) : (X ⟶ Y) ≃+ (Y ⟶ X) where
  toFun := adj
  invFun := adj
  left_inv f := adj_adj f
  right_inv f := adj_adj f
  map_add' := adj_add

@[simp] theorem adj_zero' {X Y : C} : (0 : X ⟶ Y)† = 0 :=
  map_zero (adjAddEquiv X Y)

@[simp] theorem adj_neg' {X Y : C} (f : X ⟶ Y) : (-f)† = -f† :=
  map_neg (adjAddEquiv X Y) f

@[simp] theorem adj_sub' {X Y : C} (f g : X ⟶ Y) : (f - g)† = f† - g† :=
  map_sub (adjAddEquiv X Y) f g

theorem adj_sum {ι : Type w} {X Y : C} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (∑ i ∈ s, f i)† = ∑ i ∈ s, (f i)† :=
  map_sum (adjAddEquiv X Y) f s

@[simp] theorem adj_smul' {X Y : C} (c : ℂ) (f : X ⟶ Y) :
    (c • f)† = (starRingEnd ℂ c) • f† := adj_smul c f

end StarCategory

open StarCategory

/-- **FDS 2.2** (direct_sums.tex:255, Definition), last paragraph: a morphism
`a : A → B` is an **isometry** when `a*a = 1` (diagrammatically
`a ≫ a† = 𝟙 A`). -/
def IsIsometry {X Y : C} (a : X ⟶ Y) : Prop := a ≫ a† = 𝟙 X

/-- **FDS 2.2** (direct_sums.tex:255, Definition), last paragraph: a
**unitary** is an isometry with moreover `aa* = 1`. -/
def IsUnitary {X Y : C} (a : X ⟶ Y) : Prop := IsIsometry a ∧ a† ≫ a = 𝟙 Y

/-- A morphism `X ⟶ X` as an element of the C*-algebra `End X` (so that
order and algebra on `End X` apply to composites of morphisms). -/
abbrev toEnd {X : C} (f : X ⟶ X) : End X := f

variable [NormedStarCategory C]

section EndInstances

variable [CStarCategory C]

theorem norm_adj_le {X Y : C} (f : X ⟶ Y) : ‖f‖ ≤ ‖f†‖ := by
  have h := CStarCategory.norm_comp_adj f
  have h2 := NormedStarCategory.norm_comp_le f f†
  rw [h] at h2
  rcases (norm_nonneg f).lt_or_eq with hpos | hzero
  · nlinarith [norm_nonneg f†]
  · rw [← hzero]; exact norm_nonneg _

@[simp] theorem norm_adj {X Y : C} (f : X ⟶ Y) : ‖f†‖ = ‖f‖ :=
  le_antisymm (by simpa using norm_adj_le f†) (norm_adj_le f)

theorem norm_adj_comp {X Y : C} (f : X ⟶ Y) : ‖f† ≫ f‖ = ‖f‖ ^ 2 := by
  simpa using CStarCategory.norm_comp_adj f†

/-- `End A` is a normed ring (multiplication `x * y = y ≫ x`). -/
instance endNormedRing (A : C) : NormedRing (End A) :=
  { (inferInstance : Ring (End A)) with
    toNorm := (inferInstance : Norm (A ⟶ A))
    toMetricSpace := (inferInstance : MetricSpace (A ⟶ A))
    dist_eq := fun x y => NormedAddCommGroup.dist_eq (E := A ⟶ A) x y
    norm_mul_le := fun f g => (NormedStarCategory.norm_comp_le g f).trans_eq (mul_comm _ _) }

instance endNormedAlgebra (A : C) : NormedAlgebra ℂ (End A) :=
  { (inferInstance : Algebra ℂ (End A)) with
    norm_smul_le := fun c f => le_of_eq ((NormedStarCategory.homCore A A).norm_smul c f) }

instance endStarRing (A : C) : StarRing (End A) where
  star := adj
  star_involutive := adj_adj
  star_mul f g := adj_comp g f
  star_add := adj_add

instance endStarModule (A : C) : StarModule ℂ (End A) where
  star_smul c f := adj_smul c f

instance endCompleteSpace (A : C) : CompleteSpace (End A) :=
  inferInstanceAs (CompleteSpace (A ⟶ A))

instance endCStarRing (A : C) : CStarRing (End A) where
  norm_mul_self_le f := by
    show ‖f‖ * ‖f‖ ≤ ‖f ≫ f†‖
    rw [CStarCategory.norm_comp_adj, sq]

/-- **FDS 2.2**, part 2: in a C*-category every `C(A,A)` is a C*-algebra. -/
instance endCStarAlgebra (A : C) : CStarAlgebra (End A) where

/-- The order of the C*-algebra `End A`: its spectral order, i.e. the unique
star order (`x ≤ y` iff `y - x = s*s` for some `s`). -/
instance endPartialOrder (A : C) : PartialOrder (End A) :=
  CStarAlgebra.spectralOrder (End A)

instance endStarOrderedRing (A : C) : StarOrderedRing (End A) :=
  CStarAlgebra.spectralOrderedRing (End A)

@[simp] theorem end_star_def {A : C} (f : End A) : star f = (f : A ⟶ A)† := rfl

theorem end_mul_def {A : C} (f g : End A) : f * g = (g : A ⟶ A) ≫ f := rfl

theorem end_one_def (A : C) : (1 : End A) = 𝟙 A := rfl

/-- `a*a ≥ 0` for every morphism `a` (condition 3(a) of **FDS 2.1**):
diagrammatically `0 ≤ a ≫ a†` in `End X`. -/
theorem comp_adj_nonneg {X Y : C} (a : X ⟶ Y) : (0 : End X) ≤ toEnd (a ≫ a†) := by
  obtain ⟨b, hb⟩ := StarCategory.exists_eq_adj_comp a
  rw [hb]
  exact star_mul_self_nonneg (toEnd b)

/-- `aa* ≥ 0` for every morphism `a`: `0 ≤ a† ≫ a` in `End Y`. -/
theorem adj_comp_nonneg {X Y : C} (a : X ⟶ Y) : (0 : End Y) ≤ toEnd (a† ≫ a) := by
  simpa using comp_adj_nonneg a†

/-- Conjugation by a morphism is monotone between endomorphism algebras:
`x ≤ y` in `End Y` gives `a x a* ≤ a y a*`... in diagrammatic form, for
`a : X ⟶ Y`, `a ≫ x ≫ a† ≤ a ≫ y ≫ a†` in `End X`. -/
theorem conj_le_conj {X Y : C} (a : X ⟶ Y) {x y : End Y} (h : x ≤ y) :
    toEnd (a ≫ (x : Y ⟶ Y) ≫ a†) ≤ toEnd (a ≫ (y : Y ⟶ Y) ≫ a†) := by
  rw [← sub_nonneg] at h ⊢
  obtain ⟨s, hs⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h
  have hs' : (y : Y ⟶ Y) - x = s ≫ s† := hs
  have : toEnd (a ≫ (y : Y ⟶ Y) ≫ a†) - toEnd (a ≫ (x : Y ⟶ Y) ≫ a†)
      = toEnd ((a ≫ (s : Y ⟶ Y)) ≫ (a ≫ (s : Y ⟶ Y))†) := by
    show a ≫ (y : Y ⟶ Y) ≫ a† - a ≫ (x : Y ⟶ Y) ≫ a†
      = (a ≫ (s : Y ⟶ Y)) ≫ (a ≫ (s : Y ⟶ Y))†
    rw [← Preadditive.comp_sub, ← Preadditive.sub_comp, hs', adj_comp', Category.assoc,
      Category.assoc]
  rw [this]
  exact comp_adj_nonneg _

theorem conj_nonneg {X Y : C} (a : X ⟶ Y) {x : End Y} (h : 0 ≤ x) :
    (0 : End X) ≤ toEnd (a ≫ (x : Y ⟶ Y) ≫ a†) := by
  have := conj_le_conj a h
  simpa [show ((0 : End Y) : Y ⟶ Y) = 0 from rfl] using this

theorem conj_le_comp_adj {X Y : C} (a : X ⟶ Y) {x : End Y} (h : x ≤ 1) :
    toEnd (a ≫ (x : Y ⟶ Y) ≫ a†) ≤ toEnd (a ≫ a†) := by
  have := conj_le_conj a h
  have e : toEnd (a ≫ ((1 : End Y) : Y ⟶ Y) ≫ a†) = toEnd (a ≫ a†) := by
    show a ≫ 𝟙 Y ≫ a† = a ≫ a†
    rw [Category.id_comp]
  rwa [e] at this

/-- **FDS 2.2**, part 3, the module structure (mirrored, see the file
header): `A ⟶ B` is a Hilbert `End B`-module with `b • f = f ≫ b` and
inner product `⟪f, g⟫ = f† ≫ g` (the paper's `g f*`). -/
instance homCStarModule (A B : C) : CStarModule (End B) (A ⟶ B) where
  inner f g := toEnd (f† ≫ g)
  inner_add_right := Preadditive.comp_add _ _ _ _ _ _
  inner_self_nonneg := adj_comp_nonneg _
  inner_self {f} := by
    constructor
    · intro h
      have h1 : f† ≫ f†† = 0 := by rw [adj_adj']; exact h
      have := eq_zero_of_comp_adj f† h1
      rw [← adj_adj' f, this, adj_zero']
    · rintro rfl
      show (0 : A ⟶ B)† ≫ 0 = 0
      simp
  inner_op_smul_right {b f g} := (Category.assoc _ _ _).symm
  inner_smul_right_complex {c f g} := Linear.comp_smul _ _ _ _ _ _
  star_inner f g := by
    show (f† ≫ g)† = g† ≫ f
    simp
  norm_eq_sqrt_norm_inner_self f := by
    show ‖f‖ = Real.sqrt ‖f† ≫ f‖
    rw [norm_adj_comp, Real.sqrt_sq (norm_nonneg f)]

theorem inner_def {A B : C} (f g : A ⟶ B) : (inner (End B) f g : End B) = toEnd (f† ≫ g) := rfl

theorem smul_def {A B : C} (b : End B) (f : A ⟶ B) : b • f = f ≫ (b : B ⟶ B) := rfl

end EndInstances

variable (C) in
/-- **FDS 2.2** (direct_sums.tex:255, Definition), part 3, the print's
definition: every hom-set has a Banach-space predual.  (Kept for reference;
`WStarCategory` uses the print's equivalent characterisation, cited from
[GLR, Prop. 2.15].) -/
def HomsHavePreduals : Prop :=
  ∀ X Y : C, ∃ (E : Type v) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E),
    Nonempty (StrongDual ℂ E ≃ₗᵢ[ℂ] (X ⟶ Y))

variable (C) in
/-- **FDS 2.2** (direct_sums.tex:255, Definition), part 3: a C*-category is
a **W\*-category** when — in the print's "equivalently [GLR, Prop. 2.15]"
form, which is the one its proofs use — every `C(A,A)` is a W*-algebra (the
theses' Kadison `VonNeumannAlgebra`) and every `C(A,B)` is a self-dual
Hilbert module.  Mirrored: `A ⟶ B` is self dual as a Hilbert `End B`-module
(`homCStarModule`), for all `A, B` — the print's condition (`C(B,A)` self
dual over `C(B,B)` with `⟨a,b⟩ = a*b`) transported by `†`. -/
class WStarCategory [CStarCategory C] : Prop where
  vonNeumann : ∀ A : C, VonNeumannAlgebra (End A)
  selfDual : ∀ A B : C, SelfDual (End B) (A ⟶ B)

attribute [instance] WStarCategory.vonNeumann

end Basic

/-! ## Section 3: Universal properties in C*-categories -/

section Sec3

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [StarCategory C]
  [NormedStarCategory C] [CStarCategory C]

open StarCategory

theorem proj_adj {X : C} {s : End X} (hs : IsStarProjection s) : (s : X ⟶ X)† = s :=
  hs.isSelfAdjoint.star_eq

theorem proj_comp_self {X : C} {s : End X} (hs : IsStarProjection s) :
    (s : X ⟶ X) ≫ s = s :=
  hs.isIdempotentElem.eq

theorem proj_le_one {X : C} {s : End X} (hs : IsStarProjection s) : s ≤ 1 :=
  sub_nonneg.mp hs.one_sub.nonneg

/-- `‖a‖ ≤ 1` gives `a*a ≤ 1`. -/
theorem comp_adj_le_one {X Y : C} (a : X ⟶ Y) (ha : ‖a‖ ≤ 1) : toEnd (a ≫ a†) ≤ 1 := by
  have h0 := comp_adj_nonneg a
  refine (CStarAlgebra.norm_le_one_iff_of_nonneg _ h0).mp ?_
  show ‖a ≫ a†‖ ≤ 1
  rw [CStarCategory.norm_comp_adj]
  nlinarith [norm_nonneg a]

/-- The core of **FDS 3.1**: `a*ta ≤ 1 - s ⇔ tas = 0`. -/
theorem conj_le_one_sub_iff {X Y : C} (a : X ⟶ Y) (ha : ‖a‖ ≤ 1) {s : End X} {t : End Y}
    (hs : IsStarProjection s) (ht : IsStarProjection t) :
    toEnd (a ≫ (t : Y ⟶ Y) ≫ a†) ≤ 1 - s ↔ (s : X ⟶ X) ≫ a ≫ t = 0 := by
  set x : End X := toEnd (a ≫ (t : Y ⟶ Y) ≫ a†) with hx
  have hx0 : 0 ≤ x := conj_nonneg a ht.nonneg
  constructor
  · intro h
    -- `0 ≤ s a* t a s ≤ s (1-s) s = 0`
    have h1 : s * x * s ≤ s * (1 - s) * s := hs.isSelfAdjoint.conjugate_le_conjugate h
    have h2 : s * (1 - s) * s = 0 := by rw [hs.mul_one_sub_self, zero_mul]
    have h3 : 0 ≤ s * x * s := hs.isSelfAdjoint.conjugate_nonneg hx0
    have h4 : s * x * s = 0 := le_antisymm (h2 ▸ h1) h3
    apply eq_zero_of_comp_adj
    have h5 : ((s : X ⟶ X) ≫ a ≫ t) ≫ ((s : X ⟶ X) ≫ a ≫ t)† = s * x * s := by
      simp only [adj_comp', proj_adj hs, proj_adj ht, Category.assoc, hx, end_mul_def]
      rw [← Category.assoc (t : Y ⟶ Y) t, proj_comp_self ht]
    rw [h5, h4]
  · intro h
    have h' : (t : Y ⟶ Y) ≫ a† ≫ (s : X ⟶ X) = 0 := by
      have := congrArg adj h
      simpa only [adj_comp', proj_adj hs, proj_adj ht, adj_zero', Category.assoc] using this
    -- `a ≫ t = (1 - s) ≫ a ≫ t` and `t ≫ a† = t ≫ a† ≫ (1 - s)`
    have hsx : s * x = 0 := by
      show (a ≫ (t : Y ⟶ Y) ≫ a†) ≫ (s : X ⟶ X) = 0
      simp only [Category.assoc, h', Limits.comp_zero]
    have hxs : x * s = 0 := by
      show (s : X ⟶ X) ≫ (a ≫ (t : Y ⟶ Y) ≫ a†) = 0
      rw [← Category.assoc, ← Category.assoc, Category.assoc (s : X ⟶ X) a, h,
        Limits.zero_comp]
    have e1 : x = (1 - s) * x * (1 - s) := by
      have : (1 - s) * x * (1 - s) = x - s * x - x * s + s * x * s := by noncomm_ring
      rw [this, hsx, hxs, zero_mul]; simp
    have hx1 : x ≤ 1 := (conj_le_comp_adj a (proj_le_one ht)).trans (comp_adj_le_one a ha)
    rw [e1]
    have := (hs.one_sub.isSelfAdjoint).conjugate_le_conjugate hx1
    rwa [mul_one, hs.one_sub.isIdempotentElem.eq] at this

/-- **FDS 3.1** (direct_sums.tex:327, Lemma): for `a : A → B` with `‖a‖ ≤ 1`
and projections `s : A → A`, `t : B → B` the following are equivalent:
(a) `a*ta ≤ 1 - s`; (b) `asa* ≤ 1 - t`; (c) `tas = 0`; (d) `sa*t = 0`.
Diagrammatically: `a ≫ t ≫ a†`, `a† ≫ s ≫ a`, `s ≫ a ≫ t`, `t ≫ a† ≫ s`. -/
theorem contrapositionlemma {A B : C} (a : A ⟶ B) (ha : ‖a‖ ≤ 1) {s : End A} {t : End B}
    (hs : IsStarProjection s) (ht : IsStarProjection t) :
    List.TFAE [toEnd (a ≫ (t : B ⟶ B) ≫ a†) ≤ 1 - s,
      toEnd (a† ≫ (s : A ⟶ A) ≫ a) ≤ 1 - t,
      (s : A ⟶ A) ≫ a ≫ t = 0,
      (t : B ⟶ B) ≫ a† ≫ s = 0] := by
  have hcd : (s : A ⟶ A) ≫ a ≫ t = 0 ↔ (t : B ⟶ B) ≫ a† ≫ s = 0 := by
    constructor
    · intro h
      have := congrArg adj h
      simpa only [adj_comp', proj_adj hs, proj_adj ht, adj_zero', Category.assoc] using this
    · intro h
      have := congrArg adj h
      simpa only [adj_comp', proj_adj hs, proj_adj ht, adj_zero', Category.assoc,
        adj_adj'] using this
  have hb : toEnd (a† ≫ (s : A ⟶ A) ≫ a) ≤ 1 - t ↔ (t : B ⟶ B) ≫ a† ≫ s = 0 := by
    have := conj_le_one_sub_iff a† (by rwa [norm_adj]) ht hs
    simpa only [adj_adj'] using this
  tfae_have 1 ↔ 3 := conj_le_one_sub_iff a ha hs ht
  tfae_have 2 ↔ 4 := hb
  tfae_have 3 ↔ 4 := hcd
  tfae_finish

/-- A projection-valued corollary used twice in **FDS 3.2**: if `b` is an
isometry then `b*b`... diagrammatically `b† ≫ b` is a projection. -/
theorem isStarProjection_adj_comp {X Y : C} (b : X ⟶ Y) (hb : IsIsometry b) :
    IsStarProjection (toEnd (b† ≫ b)) where
  isIdempotentElem := by
    show (b† ≫ b) ≫ (b† ≫ b) = b† ≫ b
    rw [Category.assoc, ← Category.assoc b, show b ≫ b† = 𝟙 X from hb, Category.id_comp]
  isSelfAdjoint := by
    show (b† ≫ b)† = b† ≫ b
    simp

/-- **FDS 3.2** (direct_sums.tex:354, Lemma): for `a : A ⇄ B : b` with
`‖a‖ ≤ 1`, `‖b‖ ≤ 1` and `ab = 1` (diagrammatically `b ≫ a = 𝟙 B`), `b` is an
isometry and `a = b*`.  The paper's proof, through **FDS 3.1**. -/
theorem isometrylemma {A B : C} (a : A ⟶ B) (b : B ⟶ A) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hab : b ≫ a = 𝟙 B) : IsIsometry b ∧ a = b† := by
  -- `a*a ≤ 1`, `b*b ≤ 1`, and likewise for the adjoints
  have haa : toEnd (a ≫ a†) ≤ 1 := comp_adj_le_one a ha
  have hbb : toEnd (b ≫ b†) ≤ 1 := comp_adj_le_one b hb
  have haa' : toEnd (a† ≫ a) ≤ 1 := by
    simpa using comp_adj_le_one a† (by rwa [norm_adj])
  have hbb' : toEnd (b† ≫ b) ≤ 1 := by
    simpa using comp_adj_le_one b† (by rwa [norm_adj])
  -- `1 = b*a*ab ≤ b*b ≤ 1`
  have hiso : b ≫ b† = 𝟙 B := by
    have h1 : toEnd (b ≫ (a ≫ a†) ≫ b†) = 1 := by
      rw [← Category.assoc, ← Category.assoc, hab, Category.id_comp, ← adj_comp', hab,
        adj_id']; rfl
    have h2 := conj_le_comp_adj b haa
    rw [h1] at h2
    have := le_antisymm hbb h2
    exact this
  -- `1 = abb*a* ≤ aa* ≤ 1`
  have hco : a† ≫ a = 𝟙 B := by
    have h1 : toEnd (a† ≫ (b† ≫ b) ≫ a††) = 1 := by
      rw [adj_adj', ← Category.assoc, ← Category.assoc, ← adj_comp', hab, adj_id',
        Category.id_comp, hab]; rfl
    have h2 := conj_le_comp_adj a† hbb'
    rw [h1, adj_adj'] at h2
    have := le_antisymm haa' h2
    exact this
  -- `a*a ≤ bb*` and `bb* ≤ a*a` by **FDS 3.1**
  have hp1 : IsStarProjection (1 - toEnd (b† ≫ b)) :=
    (isStarProjection_adj_comp b hiso).one_sub
  have hp2 : IsStarProjection (1 - toEnd (a ≫ a†)) := by
    have := (isStarProjection_adj_comp a† (by
      show a† ≫ a†† = 𝟙 B; rw [adj_adj']; exact hco)).one_sub
    simpa using this
  have hle1 : toEnd (a ≫ a†) ≤ toEnd (b† ≫ b) := by
    have h := (contrapositionlemma a ha hp1 (IsStarProjection.one (End B))).out 1 0
    have hb2 : toEnd (a† ≫ ((1 - toEnd (b† ≫ b) : End A) : A ⟶ A) ≫ a) ≤ 1 - 1 := by
      have : toEnd (a† ≫ ((1 - toEnd (b† ≫ b) : End A) : A ⟶ A) ≫ a) = 0 := by
        show a† ≫ (𝟙 A - b† ≫ b) ≫ a = 0
        rw [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, hco,
          Category.assoc, hab, Category.comp_id, ← adj_comp', hab, adj_id', sub_self]
      rw [this, sub_self]
    have h2 := h.mp hb2
    have e : toEnd (a ≫ ((1 : End B) : B ⟶ B) ≫ a†) = toEnd (a ≫ a†) := by
      show a ≫ 𝟙 B ≫ a† = a ≫ a†
      rw [Category.id_comp]
    rw [e, sub_sub_cancel] at h2
    exact h2
  have hle2 : toEnd (b† ≫ b) ≤ toEnd (a ≫ a†) := by
    have h := (contrapositionlemma b† (by rwa [norm_adj]) hp2 (IsStarProjection.one (End B))).out 1 0
    have hb2 : toEnd (b†† ≫ ((1 - toEnd (a ≫ a†) : End A) : A ⟶ A) ≫ b†) ≤ 1 - 1 := by
      have : toEnd (b†† ≫ ((1 - toEnd (a ≫ a†) : End A) : A ⟶ A) ≫ b†) = 0 := by
        show b†† ≫ (𝟙 A - a ≫ a†) ≫ b† = 0
        rw [adj_adj', Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, hiso,
          Category.assoc, ← Category.assoc b a, hab, Category.id_comp, ← adj_comp', hab,
          adj_id', sub_self]
      rw [this, sub_self]
    have h2 := h.mp hb2
    have e : toEnd (b† ≫ ((1 : End B) : B ⟶ B) ≫ b††) = toEnd (b† ≫ b) := by
      show b† ≫ 𝟙 B ≫ b†† = b† ≫ b
      rw [Category.id_comp, adj_adj']
    rw [e, sub_sub_cancel] at h2
    exact h2
  have heq' : toEnd (a ≫ a†) = toEnd (b† ≫ b) := le_antisymm hle1 hle2
  have heq : a ≫ a† = b† ≫ b := heq'
  refine ⟨hiso, ?_⟩
  -- `a = aa*a = abb* = b*`
  calc a = (a ≫ a†) ≫ a := by rw [Category.assoc, hco, Category.comp_id]
    _ = (b† ≫ b) ≫ a := by rw [heq]
    _ = b† := by rw [Category.assoc, hab, Category.comp_id]

/-- **FDS 3.3** (`unitaries`, direct_sums.tex:374, Corollary): an invertible
morphism `u` with `‖u‖ ≤ 1` and `‖u⁻¹‖ ≤ 1` is unitary. -/
theorem unitaries {A B : C} (u : A ⟶ B) [IsIso u] (hu : ‖u‖ ≤ 1) (hu' : ‖inv u‖ ≤ 1) :
    IsUnitary u := by
  obtain ⟨-, h⟩ := isometrylemma u (inv u) hu hu' (IsIso.inv_hom_id u)
  have hu' : u† = inv u := by rw [← adj_adj' (inv u), ← h]
  refine ⟨?_, ?_⟩
  · show u ≫ u† = 𝟙 A
    rw [hu', IsIso.hom_inv_id]
  · rw [hu', IsIso.inv_hom_id]

/-- `‖𝟙 A‖ ≤ 1` in a C*-category (`‖1‖ = ‖1*1‖ = ‖1‖²`). -/
theorem norm_id_le_one (A : C) : ‖𝟙 A‖ ≤ 1 := by
  have h := CStarCategory.norm_comp_adj (𝟙 A)
  rw [adj_id', Category.id_comp] at h
  nlinarith [norm_nonneg (𝟙 A)]

variable (C) in
/-- **FDS 3.4** (`def_univ`, direct_sums.tex:381, Definition), the functors:
a `Ban`-enriched functor `C → Ban` (`Ban` = complex Banach spaces and
contractions, enriched over itself by the bounded operators with the operator
norm): an object map to Banach spaces and, on morphisms, a map which is
functorial and, as a map between hom-objects, a contractive linear map. -/
structure BanFunctor where
  /-- the Banach space `F X` -/
  obj : C → Type w
  instNormedAddCommGroup : ∀ X, NormedAddCommGroup (obj X)
  instNormedSpace : ∀ X, NormedSpace ℂ (obj X)
  instCompleteSpace : ∀ X, CompleteSpace (obj X)
  /-- the bounded operator `F f` -/
  map : ∀ {X Y : C}, (X ⟶ Y) → (obj X →L[ℂ] obj Y)
  map_id : ∀ X, map (𝟙 X) = ContinuousLinearMap.id ℂ (obj X)
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map g).comp (map f)
  map_add : ∀ {X Y : C} (f g : X ⟶ Y), map (f + g) = map f + map g
  map_smul : ∀ {X Y : C} (c : ℂ) (f : X ⟶ Y), map (c • f) = c • map f
  norm_map_le : ∀ {X Y : C} (f : X ⟶ Y), ‖map f‖ ≤ ‖f‖

attribute [instance] BanFunctor.instNormedAddCommGroup BanFunctor.instNormedSpace
  BanFunctor.instCompleteSpace

/-- **FDS 3.4** (`def_univ`, direct_sums.tex:381, Definition): a
representation of a `Ban`-functor `F` by an object `A`: a natural isomorphism
`C(A,-) ≅ F` that is componentwise an isometric isomorphism of Banach
spaces. -/
structure BanFunctor.Representation (F : BanFunctor C) (A : C) where
  /-- the component `C(A,X) ≅ F X` -/
  iso : ∀ X : C, (A ⟶ X) ≃ₗᵢ[ℂ] F.obj X
  natural : ∀ {X Y : C} (f : A ⟶ X) (g : X ⟶ Y), iso Y (f ≫ g) = F.map g (iso X f)

/-- **FDS 3.4** (`def_univ`, direct_sums.tex:381, Definition): `F` is
represented by `A`. -/
def BanFunctor.IsRepresentedBy (F : BanFunctor C) (A : C) : Prop :=
  Nonempty (F.Representation A)

/-- **FDS 3.4** (`def_univ`, direct_sums.tex:381, Definition): `F` is
**representable**. -/
def BanFunctor.IsRepresentable (F : BanFunctor C) : Prop :=
  ∃ A : C, F.IsRepresentedBy A

variable (C) in
/-- The hom-functor `C(A,-) : C → Ban` ("every C*-category is
`Ban`-enriched", direct_sums.tex:379). -/
def homBanFunctor (A : C) : BanFunctor C where
  obj X := A ⟶ X
  instNormedAddCommGroup X := inferInstance
  instNormedSpace X := inferInstance
  instCompleteSpace X := inferInstance
  map {X Y} g := LinearMap.mkContinuous
    { toFun := fun f => f ≫ g
      map_add' := fun f f' => Preadditive.add_comp _ _ _ _ _ _
      map_smul' := fun c f => Linear.smul_comp _ _ _ _ _ _ } ‖g‖
    (fun f => by
      simpa [mul_comm] using NormedStarCategory.norm_comp_le f g)
  map_id X := by ext f; simp
  map_comp f g := by ext h; simp
  map_add f g := by ext h; simp
  map_smul c f := by ext h; simp
  norm_map_le g := LinearMap.mkContinuous_norm_le _ (norm_nonneg g) _

theorem homBanFunctor_map_apply (A : C) {X Y : C} (g : X ⟶ Y) (f : A ⟶ X) :
    (homBanFunctor C A).map g f = f ≫ g := rfl

/-- The tautological representation of `C(A,-)` by `A`. -/
def homBanFunctor.representation (A : C) : (homBanFunctor C A).Representation A where
  iso X := LinearIsometryEquiv.refl ℂ (A ⟶ X)
  natural f g := rfl

/-- **FDS 3.5** (`unique_up_to_unitary`, direct_sums.tex:388, Corollary): the
representing object of a representable functor `C → Ban` is unique up to
unique *unitary* isomorphism: given representations of `F` by `A` and by `B`
there is exactly one morphism `u : A → B` compatible with them
(`φ (u ≫ h) = ψ h`), and it is unitary.  The paper's proof: the (weak)
enriched Yoneda lemma gives the isomorphism, isometric naturality gives
`‖u‖, ‖u⁻¹‖ ≤ 1`, and **FDS 3.3** makes it unitary. -/
theorem unique_up_to_unitary (F : BanFunctor C) {A B : C} (φ : F.Representation A)
    (ψ : F.Representation B) :
    ∃ u : A ⟶ B, IsUnitary u ∧ (∀ (X : C) (h : B ⟶ X), φ.iso X (u ≫ h) = ψ.iso X h) ∧
      ∀ u' : A ⟶ B, (∀ (X : C) (h : B ⟶ X), φ.iso X (u' ≫ h) = ψ.iso X h) → u' = u := by
  -- Yoneda: `u = φ_B⁻¹ (ψ_B 1)` and `v = ψ_A⁻¹ (φ_A 1)`
  set u : A ⟶ B := (φ.iso B).symm (ψ.iso B (𝟙 B)) with hu
  set v : B ⟶ A := (ψ.iso A).symm (φ.iso A (𝟙 A)) with hv
  have hu_compat : ∀ (X : C) (h : B ⟶ X), φ.iso X (u ≫ h) = ψ.iso X h := by
    intro X h
    rw [φ.natural, hu, LinearIsometryEquiv.apply_symm_apply, ← ψ.natural, Category.id_comp]
  have hv_compat : ∀ (X : C) (h : A ⟶ X), ψ.iso X (v ≫ h) = φ.iso X h := by
    intro X h
    rw [ψ.natural, hv, LinearIsometryEquiv.apply_symm_apply, ← φ.natural, Category.id_comp]
  have huv : u ≫ v = 𝟙 A := by
    apply (φ.iso A).injective
    rw [hu_compat, ← Category.comp_id v, hv_compat]
  have hvu : v ≫ u = 𝟙 B := by
    apply (ψ.iso B).injective
    rw [hv_compat, ← Category.comp_id u, hu_compat]
  have hnu : ‖u‖ ≤ 1 := by
    rw [hu, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
    exact norm_id_le_one B
  have hnv : ‖v‖ ≤ 1 := by
    rw [hv, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
    exact norm_id_le_one A
  haveI : IsIso u := ⟨⟨v, huv, hvu⟩⟩
  have hinv : inv u = v := by
    rw [← Category.id_comp (inv u), ← hvu, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  refine ⟨u, unitaries u hnu (hinv ▸ hnv), hu_compat, fun u' hu' => ?_⟩
  apply (φ.iso B).injective
  have h1 := hu' B (𝟙 B)
  have h2 := hu_compat B (𝟙 B)
  rw [Category.comp_id] at h1 h2
  rw [h1, h2]

end Sec3

/-! ## Section 4: The universal property of infinite direct sums -/

section Sec4

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [StarCategory C]
  [NormedStarCategory C] [CStarCategory C]

open StarCategory

/-! ### Continuity of the involution and of composition -/

theorem isometry_adj (X Y : C) : Isometry (adj : (X ⟶ Y) → (Y ⟶ X)) :=
  AddMonoidHomClass.isometry_of_norm (adjAddEquiv X Y) (fun f => norm_adj f)

theorem continuous_adj (X Y : C) : Continuous (adj : (X ⟶ Y) → (Y ⟶ X)) :=
  (isometry_adj X Y).continuous

/-- Composition as a bounded bilinear map. -/
def compCLM₂ (X Y Z : C) : (X ⟶ Y) →L[ℂ] (Y ⟶ Z) →L[ℂ] (X ⟶ Z) :=
  LinearMap.mkContinuous₂ (Linear.comp X Y Z) 1
    (fun f g => by simpa using NormedStarCategory.norm_comp_le f g)

theorem continuous_comp' {X Y Z : C} :
    Continuous (fun p : (X ⟶ Y) × (Y ⟶ Z) => p.1 ≫ p.2) :=
  (compCLM₂ X Y Z).continuous₂

variable {I : Type w}

/-! ### The Banach space `⊕ᵢ C(Aᵢ, B)` -/

/-- The finite partial sums `∑_{i∈S} fᵢ fᵢ*` of a family `fᵢ : Aᵢ → B`, in
`End B` (diagrammatically `fᵢ* ∘`… `fᵢ fᵢ* = fᵢ† ≫ fᵢ`). -/
def psum {A : I → C} {B : C} (f : ∀ i, A i ⟶ B) (S : Finset I) : End B :=
  ∑ i ∈ S, toEnd ((f i)† ≫ f i)

/-- The condition `∑ᵢ fᵢ fᵢ* < ∞` of (4.1) in a C*-category: in the print's
words, "there is a fixed element which upper bounds all partial sums
`∑_{i∈S} fᵢ fᵢ*` for finite `S ⊆ I`". -/
def SqSummable {A : I → C} {B : C} (f : ∀ i, A i ⟶ B) : Prop :=
  BddAbove (Set.range (psum f))

/-- `‖∑ᵢ fᵢ fᵢ*‖`, read as the print does in a C*-category: the supremum of
the norms of the finite partial sums.  (The squared norm of `(fᵢ)ᵢ`.) -/
def sqNorm {A : I → C} {B : C} (f : ∀ i, A i ⟶ B) : ℝ :=
  ⨆ S : Finset I, ‖psum f S‖

section PSum

variable {A : I → C} {B : C}

theorem psum_nonneg (f : ∀ i, A i ⟶ B) (S : Finset I) : 0 ≤ psum f S :=
  Finset.sum_nonneg fun i _ => adj_comp_nonneg (f i)

theorem psum_mono (f : ∀ i, A i ⟶ B) : Monotone (psum f) := by
  intro S T hST
  exact Finset.sum_le_sum_of_subset_of_nonneg hST fun i _ _ => adj_comp_nonneg (f i)

theorem psum_singleton (f : ∀ i, A i ⟶ B) (j : I) :
    psum f {j} = toEnd ((f j)† ≫ f j) := by
  simp [psum]

theorem norm_psum_singleton (f : ∀ i, A i ⟶ B) (j : I) : ‖psum f {j}‖ = ‖f j‖ ^ 2 := by
  rw [psum_singleton]; exact norm_adj_comp (f j)

theorem sum_comp_end {X Y : C} (S : Finset I) (x : I → End X) (g : X ⟶ Y) :
    ((∑ i ∈ S, x i : End X) : X ⟶ X) ≫ g = ∑ i ∈ S, ((x i : X ⟶ X) ≫ g) :=
  Preadditive.sum_comp _ _ _

theorem comp_sum_end {X Y : C} (S : Finset I) (x : I → End Y) (g : X ⟶ Y) :
    g ≫ ((∑ i ∈ S, x i : End Y) : Y ⟶ Y) = ∑ i ∈ S, (g ≫ (x i : Y ⟶ Y)) :=
  Preadditive.comp_sum _ _ _

/-- Functoriality of the partial sums:
`∑ (g fᵢ)(g fᵢ)* = g (∑ fᵢ fᵢ*) g*`. -/
theorem psum_comp (f : ∀ i, A i ⟶ B) {B' : C} (g : B ⟶ B') (S : Finset I) :
    psum (fun i => f i ≫ g) S = toEnd (g† ≫ (psum f S : B ⟶ B) ≫ g) := by
  simp only [psum]
  show (∑ i ∈ S, (f i ≫ g)† ≫ (f i ≫ g) : B' ⟶ B') = g† ≫ (∑ i ∈ S, (f i)† ≫ f i) ≫ g
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Category.assoc]

theorem psum_smul (f : ∀ i, A i ⟶ B) (c : ℂ) (S : Finset I) :
    psum (c • f) S = ((starRingEnd ℂ c) * c) • psum f S := by
  simp only [psum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (c • f i)† ≫ (c • f i) = ((starRingEnd ℂ c) * c) • ((f i)† ≫ f i)
  rw [adj_smul', Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]

theorem psum_add_add_psum_sub (f g : ∀ i, A i ⟶ B) (S : Finset I) :
    psum (f + g) S + psum (f - g) S = (psum f S + psum f S) + (psum g S + psum g S) := by
  simp only [psum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ((f i + g i)† ≫ (f i + g i) : B ⟶ B) + (f i - g i)† ≫ (f i - g i)
    = ((f i)† ≫ f i + (f i)† ≫ f i) + ((g i)† ≫ g i + (g i)† ≫ g i)
  simp only [adj_add', adj_sub', Preadditive.add_comp, Preadditive.comp_add,
    Preadditive.sub_comp, Preadditive.comp_sub]
  abel

theorem psum_zero (S : Finset I) : psum (0 : ∀ i, A i ⟶ B) S = 0 := by
  simp only [psum]
  refine Finset.sum_eq_zero fun i _ => ?_
  show ((0 : A i ⟶ B)† ≫ (0 : A i ⟶ B) : B ⟶ B) = 0
  simp

theorem norm_psum_le_of_le {f : ∀ i, A i ⟶ B} {b : End B} (h : ∀ S, psum f S ≤ b)
    (S : Finset I) : ‖psum f S‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le (psum_nonneg f S) (h S)

theorem sqSummable_iff_norm {f : ∀ i, A i ⟶ B} :
    SqSummable f ↔ ∃ M : ℝ, ∀ S, ‖psum f S‖ ≤ M := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨‖b‖, norm_psum_le_of_le (fun S => hb ⟨S, rfl⟩)⟩
  · rintro ⟨M, hM⟩
    refine ⟨algebraMap ℝ (End B) M, ?_⟩
    rintro _ ⟨S, rfl⟩
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM S)
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ hM0 (psum_nonneg f S)).mp (hM S)

theorem norm_psum_le_sqNorm {f : ∀ i, A i ⟶ B} (hf : SqSummable f) (S : Finset I) :
    ‖psum f S‖ ≤ sqNorm f := by
  obtain ⟨M, hM⟩ := sqSummable_iff_norm.mp hf
  exact le_ciSup (f := fun S => ‖psum f S‖) ⟨M, by rintro _ ⟨T, rfl⟩; exact hM T⟩ S

theorem sqNorm_le {f : ∀ i, A i ⟶ B} {M : ℝ} (h : ∀ S, ‖psum f S‖ ≤ M) : sqNorm f ≤ M :=
  ciSup_le h

theorem sqNorm_nonneg (f : ∀ i, A i ⟶ B) : 0 ≤ sqNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem norm_le_sqNorm {f : ∀ i, A i ⟶ B} (hf : SqSummable f) (j : I) :
    ‖f j‖ ^ 2 ≤ sqNorm f := by
  rw [← norm_psum_singleton]; exact norm_psum_le_sqNorm hf {j}

theorem sqSummable_comp {f : ∀ i, A i ⟶ B} (hf : SqSummable f) {B' : C} (g : B ⟶ B') :
    SqSummable (fun i => f i ≫ g) := by
  obtain ⟨b, hb⟩ := hf
  refine ⟨toEnd (g† ≫ (b : B ⟶ B) ≫ g), ?_⟩
  rintro _ ⟨S, rfl⟩
  rw [psum_comp]
  have := conj_le_conj g† (hb ⟨S, rfl⟩)
  simpa only [adj_adj'] using this

theorem sqNorm_comp_le {f : ∀ i, A i ⟶ B} (hf : SqSummable f) {B' : C} (g : B ⟶ B') :
    sqNorm (fun i => f i ≫ g) ≤ ‖g‖ ^ 2 * sqNorm f := by
  refine sqNorm_le fun S => ?_
  rw [psum_comp]
  calc ‖toEnd (g† ≫ (psum f S : B ⟶ B) ≫ g)‖
      ≤ ‖g†‖ * (‖(psum f S : B ⟶ B)‖ * ‖g‖) :=
        (NormedStarCategory.norm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (NormedStarCategory.norm_comp_le _ _) (norm_nonneg _))
    _ = ‖g‖ ^ 2 * ‖psum f S‖ := by rw [norm_adj]; ring
    _ ≤ ‖g‖ ^ 2 * sqNorm f :=
        mul_le_mul_of_nonneg_left (norm_psum_le_sqNorm hf S) (sq_nonneg _)

theorem continuous_psum (S : Finset I) :
    Continuous (fun f : (∀ i, A i ⟶ B) => psum f S) := by
  simp only [psum]
  refine continuous_finsetSum S fun i _ => ?_
  have h1 : Continuous fun f : (∀ i, A i ⟶ B) => f i := continuous_apply i
  exact continuous_comp'.comp ((continuous_adj _ _).comp h1 |>.prodMk h1)

/-- The finite-`S` inner product `[x, y]_S = ∑_{i∈S} yᵢ xᵢ*` on families,
as a (possibly indefinite) `End B`-valued inner product in the sense of the
theses (`BInner`); its seminorm `‖[x,x]_S‖^½` is what the norm of
`⊕ᵢ C(Aᵢ,B)` is the supremum of. -/
def psInner (S : Finset I) : BInner (End B) (∀ i, A i ⟶ B) where
  inner x y := ∑ i ∈ S, toEnd ((x i)† ≫ y i)
  inner_add_right x y z := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Preadditive.comp_add _ _ _ _ _ _
  inner_op_smul_right b x y := by
    show ∑ i ∈ S, toEnd ((x i)† ≫ (y i ≫ b)) = ((∑ i ∈ S, toEnd ((x i)† ≫ y i)) : B ⟶ B) ≫ b
    rw [sum_comp_end]
    exact Finset.sum_congr rfl fun i _ => (Category.assoc _ _ _).symm
  inner_smul_right_complex c x y := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Linear.comp_smul _ _ _ _ _ _
  star_inner x y := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show ((x i)† ≫ y i)† = (y i)† ≫ x i
    simp
  inner_self_nonneg x := Finset.sum_nonneg fun i _ => adj_comp_nonneg (x i)

theorem psInner_norm (S : Finset I) (x : ∀ i, A i ⟶ B) :
    (psInner S).norm x = Real.sqrt ‖psum x S‖ := rfl

end PSum

variable (A : I → C) (B : C)

/-- The families `(fᵢ : Aᵢ → B)ᵢ` with `∑ᵢ fᵢ fᵢ* < ∞` (4.1), as a subspace
of all families.  Closure under addition is the print's
`fᵢgᵢ* + gᵢfᵢ* ≤ fᵢfᵢ* + gᵢgᵢ*`, in the form
`(f+g)(f+g)* ≤ 2ff* + 2gg*`. -/
def dsumSub : Submodule ℂ (∀ i, A i ⟶ B) where
  carrier := {f | SqSummable f}
  zero_mem' := ⟨0, by rintro _ ⟨S, rfl⟩; exact (psum_zero S).le⟩
  add_mem' := by
    rintro f g ⟨bf, hbf⟩ ⟨bg, hbg⟩
    refine ⟨(bf + bf) + (bg + bg), ?_⟩
    rintro _ ⟨S, rfl⟩
    have h := psum_add_add_psum_sub f g S
    have h0 := psum_nonneg (f - g) S
    calc psum (f + g) S ≤ psum (f + g) S + psum (f - g) S := le_add_of_nonneg_right h0
      _ = (psum f S + psum f S) + (psum g S + psum g S) := h
      _ ≤ (bf + bf) + (bg + bg) := by
          have h1 := hbf ⟨S, rfl⟩; have h2 := hbg ⟨S, rfl⟩
          exact add_le_add (add_le_add h1 h1) (add_le_add h2 h2)
  smul_mem' := by
    intro c f hf
    have h := sqSummable_comp hf (c • 𝟙 B)
    have he : (fun i => f i ≫ (c • 𝟙 B)) = c • f := by
      funext i; simp [Linear.comp_smul]
    show SqSummable (c • f)
    rwa [he] at h

/-- **FDS 4.1** (the space of (4.1)): the Banach space
`⊕ᵢ C(Aᵢ,B) = {(fᵢ : Aᵢ → B)ᵢ | ∑ᵢ fᵢfᵢ* < ∞}` with the norm
`‖(fᵢ)ᵢ‖ = ‖∑ᵢ fᵢfᵢ*‖^½` (supremum of the finite partial sums). -/
def DSum : Type (max w v) := ↥(dsumSub A B)

namespace DSum

variable {A B}

instance : AddCommGroup (DSum A B) := inferInstanceAs (AddCommGroup ↥(dsumSub A B))
instance : Module ℂ (DSum A B) := inferInstanceAs (Module ℂ ↥(dsumSub A B))

/-- The underlying family. -/
def val (x : DSum A B) : ∀ i, A i ⟶ B := Subtype.val x

theorem val_injective : Function.Injective (val : DSum A B → ∀ i, A i ⟶ B) :=
  Subtype.val_injective

@[ext] theorem ext {x y : DSum A B} (h : ∀ i, x.val i = y.val i) : x = y :=
  val_injective (funext h)

theorem sqSummable (x : DSum A B) : SqSummable x.val := x.2

/-- Constructor. -/
def mk (f : ∀ i, A i ⟶ B) (hf : SqSummable f) : DSum A B := ⟨f, hf⟩

@[simp] theorem val_mk (f : ∀ i, A i ⟶ B) (hf : SqSummable f) : (mk f hf).val = f := rfl
@[simp] theorem val_add (x y : DSum A B) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_sub (x y : DSum A B) : (x - y).val = x.val - y.val := rfl
@[simp] theorem val_neg (x : DSum A B) : (-x).val = -x.val := rfl
@[simp] theorem val_zero : (0 : DSum A B).val = 0 := rfl
@[simp] theorem val_smul (c : ℂ) (x : DSum A B) : (c • x).val = c • x.val := rfl

instance : Norm (DSum A B) := ⟨fun x => Real.sqrt (sqNorm x.val)⟩

theorem norm_def (x : DSum A B) : ‖x‖ = Real.sqrt (sqNorm x.val) := rfl

theorem norm_sq (x : DSum A B) : ‖x‖ ^ 2 = sqNorm x.val :=
  Real.sq_sqrt (sqNorm_nonneg _)

theorem norm_psum_le (x : DSum A B) (S : Finset I) : ‖psum x.val S‖ ≤ ‖x‖ ^ 2 := by
  rw [norm_sq]; exact norm_psum_le_sqNorm x.sqSummable S

theorem norm_le_of {x : DSum A B} {M : ℝ} (hM : 0 ≤ M) (h : ∀ S, ‖psum x.val S‖ ≤ M ^ 2) :
    ‖x‖ ≤ M := by
  rw [norm_def]
  exact Real.sqrt_le_iff.mpr ⟨hM, sqNorm_le h⟩

theorem norm_val_le (x : DSum A B) (j : I) : ‖x.val j‖ ≤ ‖x‖ := by
  have h := norm_le_sqNorm x.sqSummable j
  rw [← norm_sq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.sqrt_nonneg _) two_ne_zero).mp h

theorem normedSpaceCore : NormedSpace.Core ℂ (DSum A B) where
  norm_nonneg x := Real.sqrt_nonneg _
  norm_smul c x := by
    rw [norm_def, norm_def, val_smul]
    have h : ∀ S, ‖psum (c • x.val) S‖ = ‖c‖ ^ 2 * ‖psum x.val S‖ := by
      intro S
      rw [psum_smul, norm_smul, norm_mul, RCLike.norm_conj]; ring
    have hs : sqNorm (c • x.val) = ‖c‖ ^ 2 * sqNorm x.val := by
      simp only [sqNorm, h]
      exact (Real.mul_iSup_of_nonneg (sq_nonneg _) _).symm
    rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  norm_triangle x y := by
    refine norm_le_of (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) fun S => ?_
    have h := (module_seminorm_2 (psInner (A := A) (B := B) S) x.val y.val 1 1).1
    simp only [psInner_norm] at h
    have hx : Real.sqrt ‖psum x.val S‖ ≤ ‖x‖ :=
      Real.sqrt_le_iff.mpr ⟨Real.sqrt_nonneg _, norm_psum_le x S⟩
    have hy : Real.sqrt ‖psum y.val S‖ ≤ ‖y‖ :=
      Real.sqrt_le_iff.mpr ⟨Real.sqrt_nonneg _, norm_psum_le y S⟩
    have h2 : Real.sqrt ‖psum (x + y).val S‖ ≤ ‖x‖ + ‖y‖ := by
      rw [val_add]; linarith
    have h3 := Real.sqrt_le_iff.mp h2
    exact h3.2
  norm_eq_zero_iff x := by
    constructor
    · intro h
      ext j
      have h1 := norm_val_le x j
      rw [h] at h1
      exact norm_le_zero_iff.mp h1
    · rintro rfl
      rw [norm_def, val_zero]
      have : sqNorm (0 : ∀ i, A i ⟶ B) = 0 := by
        refine le_antisymm (sqNorm_le fun S => ?_) (sqNorm_nonneg _)
        rw [psum_zero, norm_zero]
      rw [this, Real.sqrt_zero]

instance : NormedAddCommGroup (DSum A B) := NormedAddCommGroup.ofCore normedSpaceCore

instance : NormedSpace ℂ (DSum A B) := NormedSpace.ofCore normedSpaceCore

/-- The projection `⊕ᵢ C(Aᵢ,B) → C(Aⱼ,B)`, bounded (of norm `≤ 1`). -/
def proj (j : I) : DSum A B →L[ℂ] (A j ⟶ B) :=
  LinearMap.mkContinuous
    { toFun := fun x => x.val j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun x => by rw [one_mul]; exact norm_val_le x j)

@[simp] theorem proj_apply (j : I) (x : DSum A B) : proj j x = x.val j := rfl

/-- **FDS 4.1** (`lem_complete`, direct_sums.tex:432, Lemma): `⊕ᵢ C(Aᵢ,B)` is
complete, hence a Banach space.  The paper's proof: a Cauchy sequence is
componentwise Cauchy (the projections are bounded), with limit `f`; the
sequence is bounded by some `C`, and passing to the limit in each finite
partial sum gives `‖∑_{i∈S} fᵢfᵢ*‖^½ ≤ C`, so `f ∈ ⊕ᵢ C(Aᵢ,B)`; the same
argument on differences gives convergence. -/
theorem lem_complete : CompleteSpace (DSum A B) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  -- componentwise limits
  have hcomp : ∀ j, CauchySeq fun n => (u n).val j := fun j =>
    (proj j).uniformContinuous.comp_cauchySeq hu
  choose f hf using fun j => cauchySeq_tendsto_of_complete (hcomp j)
  have hpi : Tendsto (fun n => (u n).val) atTop (𝓝 f) := tendsto_pi_nhds.mpr hf
  -- uniform bound
  obtain ⟨R, -, hR⟩ := cauchySeq_bdd hu
  set K : ℝ := ‖u 0‖ + R with hK
  have hbound : ∀ n, ‖u n‖ ≤ K := by
    intro n
    have h1 := hR n 0
    rw [dist_eq_norm] at h1
    have h2 := norm_le_insert' (u n) (u 0)
    linarith
  have hlim : ∀ S, Tendsto (fun n => psum (u n).val S) atTop (𝓝 (psum f S)) := fun S =>
    ((continuous_psum S).tendsto f).comp hpi
  have hfS : ∀ S, ‖psum f S‖ ≤ K ^ 2 := by
    intro S
    refine le_of_tendsto ((continuous_norm.tendsto _).comp (hlim S))
      (Eventually.of_forall fun n => ?_)
    exact (norm_psum_le (u n) S).trans (pow_le_pow_left₀ (norm_nonneg _) (hbound n) 2)
  have hsum : SqSummable f := sqSummable_iff_norm.mpr ⟨K ^ 2, hfS⟩
  refine ⟨mk f hsum, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hle : ‖u n - mk f hsum‖ ≤ ε / 2 := by
    refine norm_le_of (half_pos hε).le fun S => ?_
    have hlim' : Tendsto (fun m => psum ((u n).val - (u m).val) S) atTop
        (𝓝 (psum ((u n).val - f) S)) :=
      ((continuous_psum S).tendsto _).comp (tendsto_const_nhds.sub hpi)
    refine le_of_tendsto ((continuous_norm.tendsto _).comp hlim') ?_
    filter_upwards [eventually_ge_atTop N] with m hm
    have h1 := hN n hn m hm
    rw [dist_eq_norm] at h1
    have h2 := norm_psum_le (u n - u m) S
    rw [val_sub] at h2
    refine h2.trans ?_
    exact pow_le_pow_left₀ (norm_nonneg _) h1.le 2
  linarith

instance : CompleteSpace (DSum A B) := lem_complete

/-- The action of `⊕ᵢ C(Aᵢ, -)` on a morphism `g : B → B'`:
`(fᵢ)ᵢ ↦ (g fᵢ)ᵢ`, of norm `≤ ‖g‖`. -/
def map {B' : C} (g : B ⟶ B') : DSum A B →L[ℂ] DSum A B' :=
  LinearMap.mkContinuous
    { toFun := fun x => mk (fun i => x.val i ≫ g) (sqSummable_comp x.sqSummable g)
      map_add' := fun x y => by ext i; simp [Preadditive.add_comp]
      map_smul' := fun c x => by ext i; simp [Linear.smul_comp] } ‖g‖
    (fun x => by
      refine norm_le_of (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun S => ?_
      calc ‖psum (fun i => x.val i ≫ g) S‖ ≤ sqNorm (fun i => x.val i ≫ g) :=
            norm_psum_le_sqNorm (sqSummable_comp x.sqSummable g) S
        _ ≤ ‖g‖ ^ 2 * sqNorm x.val := sqNorm_comp_le x.sqSummable g
        _ = (‖g‖ * ‖x‖) ^ 2 := by rw [mul_pow, norm_sq])

@[simp] theorem map_val {B' : C} (g : B ⟶ B') (x : DSum A B) (i : I) :
    (map g x).val i = x.val i ≫ g := rfl

end DSum

/-- **FDS 4.2** (`directsumdef`, direct_sums.tex:476), the functor: the
`Ban`-enriched functor `⊕ᵢ C(Aᵢ,-) : C → Ban`, `B ↦ ⊕ᵢ C(Aᵢ,B)`
(direct_sums.tex:470). -/
def dsumFunctor : BanFunctor C where
  obj B := DSum A B
  instNormedAddCommGroup B := inferInstance
  instNormedSpace B := inferInstance
  instCompleteSpace B := inferInstance
  map g := DSum.map g
  map_id X := by ext x i; simp
  map_comp f g := by ext x i; simp
  map_add f g := by ext x i; simp [Preadditive.comp_add]
  map_smul c f := by ext x i; simp [Linear.comp_smul]
  norm_map_le g := LinearMap.mkContinuous_norm_le _ (norm_nonneg g) _

/-- **FDS 4.2** (`directsumdef`, direct_sums.tex:476, Definition): an
**`I`-indexed direct sum** of `(Aᵢ)ᵢ` is an object representing the
`Ban`-enriched functor `⊕ᵢ C(Aᵢ,-)`. -/
def IsDirectSum (X : C) : Prop := (dsumFunctor A).IsRepresentedBy X

end Sec4

/-! **FDS 4.3** (direct_sums.tex:496, Remark) — not converted: for finite `I`
the direct sums are dagger limits in the sense of [daglims], for infinite `I`
they are not limits at all ([daglims, Thm 5.2]); neither the tree nor Mathlib
has dagger limits.

**FDS 4.4** (direct_sums.tex:500, Remark) — not converted: the authors'
belief that no weight in `Ban` yields `⊕ᵢ C(Aᵢ,-)`; no formal claim. -/

/-! ### Remark 4.5: direct sums with a kernel

The print writes `⊕ᵢ^K C(Aᵢ,B) = {(fᵢ : Aᵢ → B)ᵢ | ∑ᵢⱼ Kᵢⱼ fᵢ fⱼ* < ∞}` for a
family `(Aᵢ)ᵢ`; the terms `fᵢ fⱼ*` (`fⱼ* : B → Aⱼ`, `fᵢ : Aᵢ → B`) are only
composable when `Aᵢ = Aⱼ`, so we take a constant family `Aᵢ = A` (as in the
print's own example, `Aᵢ = ℂ`).  The "norm" `‖∑ᵢⱼ Kᵢⱼ fᵢ fⱼ*‖^½` is only a
seminorm unless every `Kⱼⱼ > 0` (for `K = 0` it vanishes identically); under
that hypothesis the space is a Banach space, "the completeness proof working
in the same way as the proof of **FDS 4.1**". -/

section Kernel

open scoped MatrixOrder

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [StarCategory C]
  [NormedStarCategory C] [CStarCategory C]

open StarCategory

variable {I : Type w}

/-- A positive semidefinite kernel `K ∈ ℂ^{I×I}`: every finite principal
submatrix is positive semidefinite. -/
def IsPSDKernel (K : I → I → ℂ) : Prop :=
  ∀ S : Finset I, (Matrix.of fun i j : S => K i j).PosSemidef

variable {A B : C}

/-- The partial sums `∑_{i,j∈S} Kᵢⱼ fᵢ fⱼ*` (diagrammatically `fᵢ fⱼ* = fⱼ† ≫ fᵢ`). -/
def kpsum (K : I → I → ℂ) (f : I → (A ⟶ B)) (S : Finset I) : End B :=
  ∑ i ∈ S, ∑ j ∈ S, K i j • toEnd ((f j)† ≫ f i)

theorem IsPSDKernel.conj_eq {K : I → I → ℂ} (hK : IsPSDKernel K) (i j : I) :
    starRingEnd ℂ (K i j) = K j i := by
  classical
  have h := (hK {i, j}).1.apply (⟨j, by simp⟩ : ({i, j} : Finset I)) ⟨i, by simp⟩
  simpa using h

/-- `∑ᵢⱼ Kᵢⱼ fᵢfⱼ* ≥ 0` for a positive semidefinite kernel: with `K|_S = R*R`
(`R = √(K|_S)`), it is `∑ₖ gₖ gₖ*` for `gₖ = ∑ᵢ R̄ₖᵢ fᵢ`. -/
theorem kpsum_nonneg {K : I → I → ℂ} (hK : IsPSDKernel K) (f : I → (A ⟶ B)) (S : Finset I) :
    0 ≤ kpsum K f S := by
  classical
  set M : Matrix S S ℂ := Matrix.of fun i j => K i j with hMdef
  have hM : 0 ≤ M := (hK S).nonneg
  set R := CFC.sqrt M with hRdef
  have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M hM
  have hRsa : star R = R := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)).star_eq
  have hRik : ∀ i k : S, R i k = starRingEnd ℂ (R k i) := by
    intro i k
    have h := congrFun (congrFun hRsa i) k
    rw [Matrix.star_apply] at h
    rw [← h]; rfl
  have hK' : ∀ i j : S, K i j = ∑ k : S, starRingEnd ℂ (R k i) * R k j := by
    intro i j
    have h1 : M i j = (R * R) i j := by rw [hRR]
    rw [Matrix.mul_apply] at h1
    rw [show K i j = M i j from rfl, h1]
    exact Finset.sum_congr rfl fun k _ => by rw [hRik]
  set g : S → (A ⟶ B) := fun k => ∑ i : S, starRingEnd ℂ (R k i) • f i with hg
  have key : kpsum K f S = ∑ k : S, toEnd ((g k)† ≫ g k) := by
    have hterm : ∀ k : S, toEnd ((g k)† ≫ g k)
        = ∑ i : S, ∑ j : S, (starRingEnd ℂ (R k i) * R k j) • toEnd ((f j)† ≫ f i) := by
      intro k
      show (∑ j : S, starRingEnd ℂ (R k j) • f j)† ≫ (∑ i : S, starRingEnd ℂ (R k i) • f i)
        = ((∑ i : S, ∑ j : S, (starRingEnd ℂ (R k i) * R k j) • ((f j)† ≫ f i) : B ⟶ B))
      rw [adj_sum, Preadditive.sum_comp, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [adj_smul', Linear.smul_comp, Linear.comp_smul, smul_smul, Complex.conj_conj,
        mul_comm]
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_comm]
    simp only [kpsum]
    rw [← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul, ← hK']
  rw [key]
  exact Finset.sum_nonneg fun k _ => adj_comp_nonneg (g k)

/-- The kernel inner product on families, for fixed finite `S`. -/
def kInner {K : I → I → ℂ} (hK : IsPSDKernel K) (S : Finset I) :
    BInner (End B) (I → (A ⟶ B)) where
  inner x y := ∑ i ∈ S, ∑ j ∈ S, K i j • toEnd ((x j)† ≫ y i)
  inner_add_right x y z := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_add]
    congr 1
    exact Preadditive.comp_add _ _ _ _ _ _
  inner_op_smul_right b x y := by
    show ∑ i ∈ S, ∑ j ∈ S, K i j • toEnd ((x j)† ≫ (y i ≫ b))
      = ((∑ i ∈ S, ∑ j ∈ S, K i j • toEnd ((x j)† ≫ y i) : End B) : B ⟶ B) ≫ b
    rw [sum_comp_end]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_comp_end]
    refine Finset.sum_congr rfl fun j _ => ?_
    show K i j • ((x j)† ≫ y i ≫ b) = (K i j • ((x j)† ≫ y i)) ≫ b
    rw [Linear.smul_comp, Category.assoc]
  inner_smul_right_complex c x y := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show K i j • ((x j)† ≫ (c • y i)) = c • (K i j • ((x j)† ≫ y i))
    rw [Linear.comp_smul, smul_comm]
  star_inner x y := by
    simp only [star_sum, star_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    show starRingEnd ℂ (K j i) • ((x i)† ≫ y j)† = K i j • ((y j)† ≫ x i)
    rw [hK.conj_eq]
    simp
  inner_self_nonneg x := kpsum_nonneg hK x S

theorem kInner_self {K : I → I → ℂ} (hK : IsPSDKernel K) (S : Finset I) (f : I → (A ⟶ B)) :
    (kInner hK S).inner f f = kpsum K f S := rfl

/-- `∑ᵢⱼ Kᵢⱼ fᵢfⱼ* < ∞`. -/
def KSqSummable (K : I → I → ℂ) (f : I → (A ⟶ B)) : Prop := BddAbove (Set.range (kpsum K f))

/-- `‖∑ᵢⱼ Kᵢⱼ fᵢfⱼ*‖`, as the supremum over finite partial sums. -/
def ksqNorm (K : I → I → ℂ) (f : I → (A ⟶ B)) : ℝ := ⨆ S : Finset I, ‖kpsum K f S‖

section KFacts

variable {K : I → I → ℂ}

theorem kpsum_zero (S : Finset I) : kpsum K (0 : I → (A ⟶ B)) S = 0 := by
  simp only [kpsum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  show K i j • (((0 : A ⟶ B))† ≫ (0 : A ⟶ B)) = 0
  simp

theorem kpsum_add_add_kpsum_sub (f g : I → (A ⟶ B)) (S : Finset I) :
    kpsum K (f + g) S + kpsum K (f - g) S
      = (kpsum K f S + kpsum K f S) + (kpsum K g S + kpsum K g S) := by
  simp only [kpsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show K i j • ((f j + g j)† ≫ (f i + g i) : B ⟶ B) + K i j • ((f j - g j)† ≫ (f i - g i))
    = (K i j • ((f j)† ≫ f i) + K i j • ((f j)† ≫ f i))
      + (K i j • ((g j)† ≫ g i) + K i j • ((g j)† ≫ g i))
  simp only [adj_add', adj_sub', Preadditive.add_comp, Preadditive.comp_add,
    Preadditive.sub_comp, Preadditive.comp_sub, smul_add, smul_sub]
  abel

theorem kpsum_smul (f : I → (A ⟶ B)) (c : ℂ) (S : Finset I) :
    kpsum K (c • f) S = ((starRingEnd ℂ c) * c) • kpsum K f S := by
  simp only [kpsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show K i j • ((c • f j)† ≫ (c • f i)) = ((starRingEnd ℂ c) * c) • (K i j • ((f j)† ≫ f i))
  rw [adj_smul', Linear.smul_comp, Linear.comp_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

theorem kpsum_comp (f : I → (A ⟶ B)) {B' : C} (g : B ⟶ B') (S : Finset I) :
    kpsum K (fun i => f i ≫ g) S = toEnd (g† ≫ (kpsum K f S : B ⟶ B) ≫ g) := by
  simp only [kpsum]
  show (∑ i ∈ S, ∑ j ∈ S, K i j • ((f j ≫ g)† ≫ (f i ≫ g)) : B' ⟶ B')
    = g† ≫ (∑ i ∈ S, ∑ j ∈ S, K i j • ((f j)† ≫ f i)) ≫ g
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Linear.smul_comp, Linear.comp_smul]
  simp [Category.assoc]

theorem kpsum_singleton (f : I → (A ⟶ B)) (j : I) :
    kpsum K f {j} = K j j • toEnd ((f j)† ≫ f j) := by
  simp [kpsum]

theorem norm_kpsum_singleton (hK : IsPSDKernel K) (f : I → (A ⟶ B)) (j : I) :
    ‖kpsum K f {j}‖ = ‖K j j‖ * ‖f j‖ ^ 2 := by
  rw [kpsum_singleton, norm_smul]
  congr 1
  exact norm_adj_comp (f j)

theorem continuous_kpsum (S : Finset I) : Continuous (fun f : I → (A ⟶ B) => kpsum K f S) := by
  simp only [kpsum]
  refine continuous_finsetSum S fun i _ => continuous_finsetSum S fun j _ => ?_
  have hi : Continuous fun f : I → (A ⟶ B) => f i := continuous_apply i
  have hj : Continuous fun f : I → (A ⟶ B) => f j := continuous_apply j
  exact (continuous_comp'.comp (((continuous_adj _ _).comp hj).prodMk hi)).const_smul _

theorem kSqSummable_iff_norm (hK : IsPSDKernel K) {f : I → (A ⟶ B)} :
    KSqSummable K f ↔ ∃ M : ℝ, ∀ S, ‖kpsum K f S‖ ≤ M := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨‖b‖, fun S => CStarAlgebra.norm_le_norm_of_nonneg_of_le (kpsum_nonneg hK f S)
      (hb ⟨S, rfl⟩)⟩
  · rintro ⟨M, hM⟩
    refine ⟨algebraMap ℝ (End B) M, ?_⟩
    rintro _ ⟨S, rfl⟩
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM S)
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ hM0 (kpsum_nonneg hK f S)).mp (hM S)

theorem norm_kpsum_le_ksqNorm (hK : IsPSDKernel K) {f : I → (A ⟶ B)} (hf : KSqSummable K f)
    (S : Finset I) : ‖kpsum K f S‖ ≤ ksqNorm K f := by
  obtain ⟨M, hM⟩ := (kSqSummable_iff_norm hK).mp hf
  exact le_ciSup (f := fun S => ‖kpsum K f S‖) ⟨M, by rintro _ ⟨T, rfl⟩; exact hM T⟩ S

theorem ksqNorm_le {f : I → (A ⟶ B)} {M : ℝ} (h : ∀ S, ‖kpsum K f S‖ ≤ M) :
    ksqNorm K f ≤ M :=
  ciSup_le h

theorem ksqNorm_nonneg (f : I → (A ⟶ B)) : 0 ≤ ksqNorm K f :=
  Real.iSup_nonneg fun _ => norm_nonneg _

end KFacts

variable (A B)

/-- The subspace `⊕ᵢ^K C(A,B)` of `K`-square-summable families. -/
def kSumSub {K : I → I → ℂ} (hK : IsPSDKernel K) : Submodule ℂ (I → (A ⟶ B)) where
  carrier := {f | KSqSummable K f}
  zero_mem' := ⟨0, by rintro _ ⟨S, rfl⟩; exact (kpsum_zero S).le⟩
  add_mem' := by
    rintro f g ⟨bf, hbf⟩ ⟨bg, hbg⟩
    refine ⟨(bf + bf) + (bg + bg), ?_⟩
    rintro _ ⟨S, rfl⟩
    have h := kpsum_add_add_kpsum_sub (K := K) f g S
    have h0 := kpsum_nonneg hK (f - g) S
    calc kpsum K (f + g) S ≤ kpsum K (f + g) S + kpsum K (f - g) S :=
          le_add_of_nonneg_right h0
      _ = (kpsum K f S + kpsum K f S) + (kpsum K g S + kpsum K g S) := h
      _ ≤ (bf + bf) + (bg + bg) := by
          have h1 := hbf ⟨S, rfl⟩; have h2 := hbg ⟨S, rfl⟩
          exact add_le_add (add_le_add h1 h1) (add_le_add h2 h2)
  smul_mem' := by
    rintro c f ⟨b, hb⟩
    refine ⟨toEnd ((c • 𝟙 B)† ≫ (b : B ⟶ B) ≫ (c • 𝟙 B)), ?_⟩
    rintro _ ⟨S, rfl⟩
    have he : (c • f) = fun i => f i ≫ (c • 𝟙 B) := by
      funext i; simp [Linear.comp_smul]
    show kpsum K (c • f) S ≤ _
    rw [he, kpsum_comp]
    have := conj_le_conj (c • 𝟙 B)† (hb ⟨S, rfl⟩)
    simpa only [adj_adj'] using this

/-- **FDS 4.5** (direct_sums.tex:504, Remark): the space `⊕ᵢ^K C(A,B)` of
families `(fᵢ : A → B)ᵢ` with `∑ᵢⱼ Kᵢⱼ fᵢfⱼ* < ∞`, for a positive
semidefinite kernel `K`. -/
def KSum {K : I → I → ℂ} (hK : IsPSDKernel K) : Type (max w v) := ↥(kSumSub A B hK)

namespace KSum

variable {A B} {K : I → I → ℂ} {hK : IsPSDKernel K}

instance : AddCommGroup (KSum A B hK) := inferInstanceAs (AddCommGroup ↥(kSumSub A B hK))
instance : Module ℂ (KSum A B hK) := inferInstanceAs (Module ℂ ↥(kSumSub A B hK))

/-- The underlying family. -/
def val (x : KSum A B hK) : I → (A ⟶ B) := Subtype.val x

theorem val_injective : Function.Injective (val : KSum A B hK → I → (A ⟶ B)) :=
  Subtype.val_injective

@[ext] theorem ext {x y : KSum A B hK} (h : ∀ i, x.val i = y.val i) : x = y :=
  val_injective (funext h)

theorem summable (x : KSum A B hK) : KSqSummable K x.val := x.2

/-- Constructor. -/
def mk (f : I → (A ⟶ B)) (hf : KSqSummable K f) : KSum A B hK := ⟨f, hf⟩

@[simp] theorem val_add (x y : KSum A B hK) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_sub (x y : KSum A B hK) : (x - y).val = x.val - y.val := rfl
@[simp] theorem val_zero : (0 : KSum A B hK).val = 0 := rfl
@[simp] theorem val_smul (c : ℂ) (x : KSum A B hK) : (c • x).val = c • x.val := rfl

instance : Norm (KSum A B hK) := ⟨fun x => Real.sqrt (ksqNorm K x.val)⟩

theorem norm_def (x : KSum A B hK) : ‖x‖ = Real.sqrt (ksqNorm K x.val) := rfl

theorem norm_sq (x : KSum A B hK) : ‖x‖ ^ 2 = ksqNorm K x.val :=
  Real.sq_sqrt (ksqNorm_nonneg _)

theorem norm_kpsum_le (x : KSum A B hK) (S : Finset I) : ‖kpsum K x.val S‖ ≤ ‖x‖ ^ 2 := by
  rw [norm_sq]; exact norm_kpsum_le_ksqNorm hK x.summable S

theorem norm_le_of {x : KSum A B hK} {M : ℝ} (hM : 0 ≤ M) (h : ∀ S, ‖kpsum K x.val S‖ ≤ M ^ 2) :
    ‖x‖ ≤ M := by
  rw [norm_def]
  exact Real.sqrt_le_iff.mpr ⟨hM, ksqNorm_le h⟩

/-- The component bound `‖Kⱼⱼ‖ ‖fⱼ‖² ≤ ‖f‖²`. -/
theorem norm_val_sq_le (x : KSum A B hK) (j : I) : ‖K j j‖ * ‖x.val j‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [← norm_kpsum_singleton hK]; exact norm_kpsum_le x {j}

variable (hdiag : ∀ j, 0 < ‖K j j‖)
include hdiag

/-- Under `Kⱼⱼ ≠ 0` for all `j`, the "norm" is a norm. -/
theorem normedSpaceCore : NormedSpace.Core ℂ (KSum A B hK) where
  norm_nonneg x := Real.sqrt_nonneg _
  norm_smul c x := by
    rw [norm_def, norm_def, val_smul]
    have h : ∀ S, ‖kpsum K (c • x.val) S‖ = ‖c‖ ^ 2 * ‖kpsum K x.val S‖ := by
      intro S
      rw [kpsum_smul, norm_smul, norm_mul, RCLike.norm_conj]; ring
    have hs : ksqNorm K (c • x.val) = ‖c‖ ^ 2 * ksqNorm K x.val := by
      simp only [ksqNorm, h]
      exact (Real.mul_iSup_of_nonneg (sq_nonneg _) _).symm
    rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  norm_triangle x y := by
    refine norm_le_of (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) fun S => ?_
    have h := (module_seminorm_2 (kInner hK S) x.val y.val 1 1).1
    simp only [BInner.norm, kInner_self] at h
    have hx : Real.sqrt ‖kpsum K x.val S‖ ≤ ‖x‖ :=
      Real.sqrt_le_iff.mpr ⟨Real.sqrt_nonneg _, norm_kpsum_le x S⟩
    have hy : Real.sqrt ‖kpsum K y.val S‖ ≤ ‖y‖ :=
      Real.sqrt_le_iff.mpr ⟨Real.sqrt_nonneg _, norm_kpsum_le y S⟩
    have h2 : Real.sqrt ‖kpsum K (x + y).val S‖ ≤ ‖x‖ + ‖y‖ := by
      rw [val_add]; linarith
    exact (Real.sqrt_le_iff.mp h2).2
  norm_eq_zero_iff x := by
    constructor
    · intro h
      ext j
      have h1 := norm_val_sq_le x j
      rw [h] at h1
      have h2 : ‖x.val j‖ ^ 2 ≤ 0 := by
        have := hdiag j
        nlinarith [sq_nonneg ‖x.val j‖]
      exact norm_le_zero_iff.mp (by nlinarith [norm_nonneg (x.val j)])
    · rintro rfl
      rw [norm_def, val_zero]
      have : ksqNorm K (0 : I → (A ⟶ B)) = 0 := by
        refine le_antisymm (ksqNorm_le fun S => ?_) (ksqNorm_nonneg _)
        rw [kpsum_zero, norm_zero]
      rw [this, Real.sqrt_zero]

/-- The normed group of `⊕ᵢ^K C(A,B)` (for `Kⱼⱼ ≠ 0`). -/
abbrev normedAddCommGroup : NormedAddCommGroup (KSum A B hK) :=
  NormedAddCommGroup.ofCore (normedSpaceCore hdiag)

/-- **FDS 4.5** (direct_sums.tex:504, Remark), the completeness claim: for a
positive semidefinite kernel with `Kⱼⱼ ≠ 0` for all `j`, `⊕ᵢ^K C(A,B)` is
complete — the proof of **FDS 4.1** verbatim, with the component bound
`‖fⱼ‖² ≤ ‖f‖²/‖Kⱼⱼ‖`. -/
theorem kernel_complete : @CompleteSpace (KSum A B hK)
    (@PseudoMetricSpace.toUniformSpace _
      (@SeminormedAddCommGroup.toPseudoMetricSpace _
        (@NormedAddCommGroup.toSeminormedAddCommGroup _
          (normedAddCommGroup (A := A) (B := B) (hK := hK) hdiag)))) := by
  letI := normedAddCommGroup (A := A) (B := B) (hK := hK) hdiag
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  -- the projections are Lipschitz
  have hproj : ∀ j, LipschitzWith (Real.toNNReal (1 / Real.sqrt ‖K j j‖))
      (fun x : KSum A B hK => x.val j) := by
    intro j
    refine LipschitzWith.of_dist_le' fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have h1 := norm_val_sq_le (x - y) j
    rw [val_sub] at h1
    have hkj := hdiag j
    have hsq : 0 < Real.sqrt ‖K j j‖ := Real.sqrt_pos.mpr hkj
    have h2 : ‖(x.val - y.val) j‖ * Real.sqrt ‖K j j‖ ≤ ‖x - y‖ := by
      have h3 : (‖(x.val - y.val) j‖ * Real.sqrt ‖K j j‖) ^ 2 ≤ ‖x - y‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hkj.le, mul_comm]; exact h1
      exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h3
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hsq]
    exact h2
  have hcomp : ∀ j, CauchySeq fun n => (u n).val j := fun j =>
    (hproj j).uniformContinuous.comp_cauchySeq hu
  choose f hf using fun j => cauchySeq_tendsto_of_complete (hcomp j)
  have hpi : Tendsto (fun n => (u n).val) atTop (𝓝 f) := tendsto_pi_nhds.mpr hf
  obtain ⟨R, -, hR⟩ := cauchySeq_bdd hu
  set M : ℝ := ‖u 0‖ + R with hM
  have hbound : ∀ n, ‖u n‖ ≤ M := by
    intro n
    have h1 := hR n 0
    rw [dist_eq_norm] at h1
    have h2 := norm_le_insert' (u n) (u 0)
    linarith
  have hlim : ∀ S, Tendsto (fun n => kpsum K (u n).val S) atTop (𝓝 (kpsum K f S)) := fun S =>
    ((continuous_kpsum S).tendsto f).comp hpi
  have hfS : ∀ S, ‖kpsum K f S‖ ≤ M ^ 2 := by
    intro S
    refine le_of_tendsto ((continuous_norm.tendsto _).comp (hlim S))
      (Eventually.of_forall fun n => ?_)
    exact (norm_kpsum_le (u n) S).trans (pow_le_pow_left₀ (norm_nonneg _) (hbound n) 2)
  have hsum : KSqSummable K f := (kSqSummable_iff_norm hK).mpr ⟨M ^ 2, hfS⟩
  refine ⟨mk f hsum, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hle : ‖u n - mk f hsum‖ ≤ ε / 2 := by
    refine norm_le_of (half_pos hε).le fun S => ?_
    have hlim' : Tendsto (fun m => kpsum K ((u n).val - (u m).val) S) atTop
        (𝓝 (kpsum K ((u n).val - f) S)) :=
      ((continuous_kpsum S).tendsto _).comp (tendsto_const_nhds.sub hpi)
    refine le_of_tendsto ((continuous_norm.tendsto _).comp hlim') ?_
    filter_upwards [eventually_ge_atTop N] with m hm
    have h1 := hN n hn m hm
    rw [dist_eq_norm] at h1
    have h2 := norm_kpsum_le (u n - u m) S
    rw [val_sub] at h2
    exact h2.trans (pow_le_pow_left₀ (norm_nonneg _) h1.le 2)
  linarith

end KSum

end Kernel

/-! ## Section 5: Direct sums in W*-categories

### Helpers on the ultranorm uniformity of Hilbert modules over a von Neumann
algebra (in the theses' encoding, `Theses.B.Dils.UnTendsto`). -/

section UltranormHelpers

variable {𝒷 : Type*} [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]

theorem fds_np_re_mono (ω : NPFunctional 𝒷) {a b : 𝒷} (h : a ≤ b) : (ω a).re ≤ (ω b).re :=
  (Complex.le_def.mp (npFunctional_mono ω h)).1

theorem fds_np_re_nonneg (ω : NPFunctional 𝒷) {a : 𝒷} (h : 0 ≤ a) : 0 ≤ (ω a).re := by
  simpa using (Complex.le_def.mp (npFunctional_nonneg ω h)).1

theorem fds_np_re_smul (ω : NPFunctional 𝒷) (r : ℝ) (a : 𝒷) :
    (ω (r • a)).re = r * (ω a).re := by
  have h : (r • a) = ((r : ℂ) • a) := (RCLike.real_smul_eq_coe_smul (K := ℂ) r a)
  rw [h, show ω ((r : ℂ) • a) = (r : ℂ) • ω a from map_smul ω.toPositiveLinearMap _ _,
    smul_eq_mul, Complex.re_ofReal_mul]

/-- A monotone net of self-adjoint elements with supremum `s` converges
ultraweakly to `s` (normality of the np-functionals). -/
theorem fds_uwTendsto_of_isLUB {ι : Type*} (x : Finset ι → 𝒷) (hmono : Monotone x)
    (hsa : ∀ S, IsSelfAdjoint (x S)) {s : 𝒷} (hs : IsLUB (Set.range x) s) :
    UWTendsto x atTop s := by
  classical
  rw [uwTendsto_iff]
  intro ω
  have hssa : IsSelfAdjoint s := by
    have h0 : x ∅ ≤ s := hs.1 ⟨∅, rfl⟩
    have := (IsSelfAdjoint.of_nonneg (sub_nonneg.mpr h0)).add (hsa ∅)
    simpa using this
  set D : Set (selfAdjoint 𝒷) := Set.range fun S => (⟨x S, hsa S⟩ : selfAdjoint 𝒷) with hD
  have himg : Subtype.val '' D = Set.range x := by
    ext y; constructor
    · rintro ⟨_, ⟨S, rfl⟩, rfl⟩; exact ⟨S, rfl⟩
    · rintro ⟨S, rfl⟩; exact ⟨_, ⟨S, rfl⟩, rfl⟩
  have hlub : IsLUB D ⟨s, hssa⟩ := isLUB_sa_of_isLUB (by rw [himg]; exact hs)
  have hne : D.Nonempty := ⟨_, ⟨∅, rfl⟩⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨S, rfl⟩ _ ⟨T, rfl⟩
    exact ⟨_, ⟨S ∪ T, rfl⟩, hmono Finset.subset_union_left, hmono Finset.subset_union_right⟩
  have hω : IsLUB ((fun d : selfAdjoint 𝒷 => ω (d : 𝒷)) '' D) (ω s) :=
    ω.preservesDirSups' D ⟨s, hssa⟩ hne hdir hlub
  have hreal : ∀ w ∈ (fun d : selfAdjoint 𝒷 => ω (d : 𝒷)) '' D, w.im = 0 := by
    rintro w ⟨d, -, rfl⟩
    exact npFunctional_im_eq_zero ω d.2
  have hre := isLUB_re_of_isLUB hreal hω
  have hrange : Complex.re '' ((fun d : selfAdjoint 𝒷 => ω (d : 𝒷)) '' D)
      = Set.range fun S => (ω (x S)).re := by
    ext r; constructor
    · rintro ⟨_, ⟨_, ⟨S, rfl⟩, rfl⟩, rfl⟩; exact ⟨S, rfl⟩
    · rintro ⟨S, rfl⟩; exact ⟨_, ⟨_, ⟨S, rfl⟩, rfl⟩, rfl⟩
  rw [hrange] at hre
  have hm : Monotone fun S => (ω (x S)).re := fun S T h => fds_np_re_mono ω (hmono h)
  have hlim := tendsto_atTop_isLUB hm hre
  have hcast : ∀ z : ℂ, z.im = 0 → ((z.re : ℂ)) = z := fun z hz =>
    Complex.ext (by simp) (by simp [hz])
  have := (Complex.continuous_ofReal.tendsto _).comp hlim
  simp only [Function.comp_def] at this
  rw [hcast _ (npFunctional_im_eq_zero ω hssa)] at this
  exact this.congr fun S => hcast _ (npFunctional_im_eq_zero ω (hsa S))

theorem fds_uwTendsto_unique [VonNeumannAlgebra 𝒷] {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → 𝒷} {a c : 𝒷} (ha : UWTendsto f l a) (hc : UWTendsto f l c) : a = c :=
  @tendsto_nhds_unique 𝒷 ι (ultraweak 𝒷) (vn_positive_basic_1 (A := 𝒷)).1 _ _ _ _ _ ha hc

/-- Conversely, the ultraweak limit of a monotone net of self-adjoint
elements is its supremum (np-functionals are order separating, thesis A
**44XI**). -/
theorem fds_isLUB_of_uwTendsto [VonNeumannAlgebra 𝒷] {ι : Type*} (x : Finset ι → 𝒷)
    (hmono : Monotone x) (hsa : ∀ S, IsSelfAdjoint (x S)) {s : 𝒷}
    (h : UWTendsto x atTop s) : IsLUB (Set.range x) s := by
  have hre : ∀ ω : NPFunctional 𝒷, Tendsto (fun S => (ω (x S)).re) atTop (𝓝 (ω s).re) :=
    fun ω => (Complex.continuous_re.tendsto _).comp ((uwTendsto_iff _ _ _).mp h ω)
  have hstar : UWTendsto x atTop (star s) := by
    rw [uwTendsto_iff] at h ⊢
    intro ω
    have h1 := (Complex.continuous_conj.tendsto _).comp (h ω)
    have h2 : ω (star s) = starRingEnd ℂ (ω s) := map_star ω.toPositiveLinearMap s
    rw [h2]
    refine h1.congr fun S => ?_
    exact Complex.conj_eq_iff_im.mpr (npFunctional_im_eq_zero ω (hsa S))
  have hssa : IsSelfAdjoint s := fds_uwTendsto_unique hstar h
  have hle : ∀ a b : 𝒷, IsSelfAdjoint a → IsSelfAdjoint b →
      (∀ ω : NPFunctional 𝒷, (ω a).re ≤ (ω b).re) → a ≤ b := by
    intro a b ha hb hab
    refine np_orderSeparating a b ha hb fun ω => ?_
    rw [Complex.le_def]
    exact ⟨hab ω, by rw [npFunctional_im_eq_zero ω ha, npFunctional_im_eq_zero ω hb]⟩
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨S, rfl⟩
    refine hle _ _ (hsa S) hssa fun ω => ?_
    refine ge_of_tendsto (hre ω) ?_
    filter_upwards [eventually_ge_atTop S] with T hT
    exact fds_np_re_mono ω (hmono hT)
  · have husa : IsSelfAdjoint u := by
      have h0 : x ∅ ≤ u := hu ⟨∅, rfl⟩
      simpa using (IsSelfAdjoint.of_nonneg (sub_nonneg.mpr h0)).add (hsa ∅)
    refine hle _ _ hssa husa fun ω => ?_
    exact le_of_tendsto (hre ω) (Eventually.of_forall fun S => fds_np_re_mono ω (hu ⟨S, rfl⟩))

variable {X Y : Type*}

theorem fds_unSeminorm_neg [AddCommGroup X] [Module ℂ X] [SMul 𝒷 X] (B : BInner 𝒷 X)
    (ω : NPFunctional 𝒷) (x : X) : unSeminorm ω B.inner (-x) = unSeminorm ω B.inner x := by
  have h : B.inner (-x) (-x) = B.inner x x := by
    have h1 : -x = (-1 : ℂ) • x := by simp
    rw [h1, B.inner_smul_right_complex, ← B.star_inner, B.inner_smul_right_complex,
      star_smul, B.star_inner]
    simp
  rw [unSeminorm, unSeminorm, h]

theorem fds_unSeminorm_zero [AddCommGroup X] [Module ℂ X] [SMul 𝒷 X] (B : BInner 𝒷 X)
    (ω : NPFunctional 𝒷) : unSeminorm ω B.inner 0 = 0 := by
  have h : B.inner 0 0 = 0 := by
    have := B.inner_smul_right_complex 0 0 0
    simpa using this
  rw [unSeminorm, h, npFunctional_zero]; simp

/-- Bounded module maps preserve ultranorm limits (**148I** of thesis B, in
the seminorm form `unSeminorm_boundedModuleMap_le`). -/
theorem fds_unTendsto_map [AddCommGroup X] [Module ℂ X] [SMul 𝒷 X]
    [AddCommGroup Y] [Module ℂ Y] [SMul 𝒷 Y] (B₁ : BInner 𝒷 X) (B₂ : BInner 𝒷 Y)
    {C₀ : ℝ} (hC : 0 ≤ C₀) {T : X → Y} (hT : IsBoundedModuleMap B₁ B₂ C₀ T)
    {ι : Type*} {l : Filter ι} {v : ι → X} {x : X} (h : UnTendsto B₁.inner v l x) :
    UnTendsto B₂.inner (fun i => T (v i)) l (T x) := by
  intro ω
  have hsub : ∀ i, T (v i) - T x = T (v i - x) := by
    intro i
    have := hT.add (v i - x) x
    rw [sub_add_cancel] at this
    rw [this]; abel
  refine squeeze_zero (fun i => unSeminorm_nonneg _ _ _) (fun i => ?_)
    (by simpa using (h ω).const_mul C₀)
  rw [hsub]
  exact unSeminorm_boundedModuleMap_le B₁ B₂ C₀ hC T hT ω (v i - x)

variable [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]

/-- Ultranorm limits in a Hilbert module over a von Neumann algebra are
unique. -/
theorem fds_unTendsto_unique [VonNeumannAlgebra 𝒷] {ι : Type*} {l : Filter ι} [l.NeBot]
    {v : ι → X} {x y : X} (hx : UnTendsto (inner 𝒷 : X → X → 𝒷) v l x)
    (hy : UnTendsto (inner 𝒷 : X → X → 𝒷) v l y) : x = y := by
  have key : ∀ ω : NPFunctional 𝒷, unSeminorm ω (inner 𝒷 : X → X → 𝒷) (x - y) = 0 := by
    intro ω
    have h1 : ∀ i, unSeminorm ω (inner 𝒷 : X → X → 𝒷) (x - y)
        ≤ unSeminorm ω (inner 𝒷 : X → X → 𝒷) (v i - y)
          + unSeminorm ω (inner 𝒷 : X → X → 𝒷) (v i - x) := by
      intro i
      have h := unSeminorm_add_le ω (cstarBInner 𝒷 X) (v i - y) (-(v i - x))
      have e : (v i - y) + -(v i - x) = x - y := by abel
      rw [e, fds_unSeminorm_neg] at h
      exact h
    have hlim : Tendsto (fun i => unSeminorm ω (inner 𝒷 : X → X → 𝒷) (v i - y)
        + unSeminorm ω (inner 𝒷 : X → X → 𝒷) (v i - x)) l (𝓝 0) := by
      simpa using (hy ω).add (hx ω)
    exact le_antisymm (ge_of_tendsto' hlim h1) (unSeminorm_nonneg _ _ _)
  have hz : (inner 𝒷 (x - y) (x - y) : 𝒷) = 0 := by
    refine VonNeumannAlgebra.np_faithful _ CStarModule.inner_self_nonneg fun ω => ?_
    have h := key ω
    rw [unSeminorm, Real.sqrt_eq_zero'] at h
    have hnn := npFunctional_nonneg ω (CStarModule.inner_self_nonneg (A := 𝒷) (x := x - y))
    have h2 := Complex.le_def.mp hnn
    exact Complex.ext (le_antisymm h (by simpa using h2.1)) (by simpa using h2.2.symm)
  exact sub_eq_zero.mp (CStarModule.inner_self.mp hz)

/-- Existence of the ultranorm limit of a norm-bounded net whose Gram
matrix `⟪v S, v T⟫ = G (S ∩ T)` comes from a bounded increasing family — the
argument of thesis B's `exists_unTendsto_of_l2Summable` (**149VIII**),
isolated from its orthonormal family. -/
theorem fds_exists_unTendsto_of_gram [VonNeumannAlgebra 𝒷] (hX : BddUnComplete 𝒷 X)
    {ι : Type*} [DecidableEq ι] (v : Finset ι → X) (G : Finset ι → 𝒷)
    (hgram : ∀ S T, (inner 𝒷 (v S) (v T) : 𝒷) = G (S ∩ T))
    (hGmono : Monotone G) (hGnn : ∀ S, 0 ≤ G S) (M : ℝ) (hGleM : ∀ S, ‖G S‖ ≤ M) :
    ∃ x : X, UnTendsto (inner 𝒷 : X → X → 𝒷) v atTop x := by
  classical
  set F : Filter X := Filter.map v atTop with hFdef
  haveI hFne : F.NeBot := Filter.map_neBot
  have hvcau : UnCauchy (inner 𝒷 : X → X → 𝒷) F := by
    intro ω ε hε
    set g : Finset ι → ℝ := fun S => (ω (G S)).re with hgdef
    have hgmono : ∀ {S T : Finset ι}, S ⊆ T → g S ≤ g T :=
      fun hST => fds_np_re_mono ω (hGmono hST)
    have hgbdd : BddAbove (Set.range g) := ⟨M * (ω 1).re, by
      rintro r ⟨S, rfl⟩
      have h1 : G S ≤ (‖G S‖ : ℝ) • (1 : 𝒷) := le_norm_smul_one (hGnn S)
      have h2 := fds_np_re_mono ω h1
      rw [fds_np_re_smul] at h2
      have h3 : (0 : ℝ) ≤ (ω 1).re := fds_np_re_nonneg ω zero_le_one
      calc g S ≤ ‖G S‖ * (ω 1).re := h2
        _ ≤ M * (ω 1).re := mul_le_mul_of_nonneg_right (hGleM S) h3⟩
    set σ : ℝ := sSup (Set.range g) with hσdef
    have hne' : (Set.range g).Nonempty := ⟨g ∅, ⟨∅, rfl⟩⟩
    obtain ⟨r₀, ⟨S₀, rfl⟩, hS₀⟩ := exists_lt_of_lt_csSup hne'
      (show σ - ε ^ 2 / 2 < σ by nlinarith)
    refine ⟨v '' Set.Ici S₀, ?_, ?_⟩
    · rw [hFdef, Filter.mem_map]
      exact Filter.mem_of_superset (Filter.Ici_mem_atTop S₀)
        (Set.subset_preimage_image v _)
    · rintro z ⟨S, hS, rfl⟩ z' ⟨T, hT, rfl⟩
      have hSS : S₀ ⊆ S ∩ T := Finset.subset_inter hS hT
      have hinner : (inner 𝒷 (v S - v T) (v S - v T) : 𝒷)
          = G S + G T - G (S ∩ T) - G (S ∩ T) := by
        rw [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
          CStarModule.inner_sub_right, hgram S S, hgram S T, hgram T S,
          hgram T T, Finset.inter_self, Finset.inter_self, Finset.inter_comm T S]
        abel
      have hre : (ω (inner 𝒷 (v S - v T) (v S - v T) : 𝒷)).re
          = g S + g T - g (S ∩ T) - g (S ∩ T) := by
        rw [hinner, npFunctional_sub, npFunctional_sub,
          show ω (G S + G T) = ω (G S) + ω (G T) from map_add ω.toPositiveLinearMap _ _,
          Complex.sub_re, Complex.sub_re, Complex.add_re]
      have hbound : g S + g T - g (S ∩ T) - g (S ∩ T) ≤ ε ^ 2 := by
        have h1 : g S ≤ σ := le_csSup hgbdd ⟨S, rfl⟩
        have h2 : g T ≤ σ := le_csSup hgbdd ⟨T, rfl⟩
        have h3 : σ - ε ^ 2 / 2 < g (S ∩ T) := lt_of_lt_of_le hS₀ (hgmono hSS)
        linarith
      rw [unSeminorm]
      calc Real.sqrt (ω (inner 𝒷 (v S - v T) (v S - v T) : 𝒷)).re
          ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt (by rw [hre]; exact hbound)
        _ = ε := Real.sqrt_sq hε.le
  have hvnorm : ∀ S, ‖v S‖ ≤ Real.sqrt M := by
    intro S
    have h1 : ‖v S‖ = Real.sqrt ‖(inner 𝒷 (v S) (v S) : 𝒷)‖ :=
      CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷) (E := X) (v S)
    rw [h1, hgram S S, Finset.inter_self]
    exact Real.sqrt_le_sqrt (hGleM S)
  obtain ⟨x, hx⟩ := hX F hFne hvcau ⟨Real.sqrt M, Set.range v, by
      rw [hFdef, Filter.mem_map]
      exact Filter.univ_mem' fun S => Set.mem_range_self S,
    by rintro z ⟨S, rfl⟩; exact hvnorm S⟩
  refine ⟨x, fun ω => ?_⟩
  have h1 := hx ω
  rwa [hFdef, Filter.tendsto_map'_iff] at h1

end UltranormHelpers

section Sec5

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [StarCategory C]
  [NormedStarCategory C] [CStarCategory C]

open StarCategory

variable {I : Type w} (A : I → C)

/-- **FDS 5.1** (`directsum_equiv`, direct_sums.tex:520, Theorem), condition
(b): a family `κⱼ : Aⱼ → A` with `∑ⱼ κⱼκⱼ* < ∞` such that every family
`fⱼ : Aⱼ → B` with `∑ⱼ fⱼfⱼ* < ∞` factors as `fⱼ = f κⱼ` through a unique
`f : A → B`, and moreover such an `f` has `‖f‖² = ‖∑ⱼ fⱼfⱼ*‖`
(`sqNorm`: the supremum of the norms of the partial sums).
Diagrammatically `f κⱼ = κⱼ ≫ f`. -/
def IsUniversalFamily {X : C} (κ : ∀ j, A j ⟶ X) : Prop :=
  SqSummable κ ∧
    (∀ (B : C) (f : ∀ j, A j ⟶ B), SqSummable f → ∃! g : X ⟶ B, ∀ j, κ j ≫ g = f j) ∧
    ∀ (B : C) (f : ∀ j, A j ⟶ B) (g : X ⟶ B), SqSummable f → (∀ j, κ j ≫ g = f j) →
      ‖g‖ ^ 2 = sqNorm f

/-- **FDS 5.1** (`directsum_equiv`, direct_sums.tex:520, Theorem), condition
(c), the definition of Ghez, Lima and Roberts: `κᵢ*κⱼ = δᵢⱼ` (diagrammatically
`κⱼ ≫ κᵢ† = δᵢⱼ`) and `∑ⱼ κⱼκⱼ* = 1`, the sum of the positive family read as
the supremum of its partial sums (the print's footnote: for positive families
the ultraweak sum is the supremum; see `isLUB_iff_uwTendsto`). -/
def IsOrthogonalSum {X : C} (κ : ∀ j, A j ⟶ X) : Prop :=
  (∀ i, κ i ≫ (κ i)† = 𝟙 (A i)) ∧ (∀ i j, i ≠ j → κ j ≫ (κ i)† = 0) ∧
    IsLUB (Set.range (psum κ)) 1

variable {A}

/-- The comparison map `C(X,B) → ⊕ᵢ C(Aᵢ,B)`, `f ↦ (f κᵢ)ᵢ`. -/
def familyMap {X : C} {κ : ∀ j, A j ⟶ X} (hκ : SqSummable κ) (B : C) :
    (X ⟶ B) →ₗ[ℂ] DSum A B where
  toFun g := DSum.mk (fun j => κ j ≫ g) (sqSummable_comp hκ g)
  map_add' g g' := by ext j; simp [Preadditive.comp_add]
  map_smul' c g := by ext j; simp [Linear.comp_smul]

@[simp] theorem familyMap_val {X : C} {κ : ∀ j, A j ⟶ X} (hκ : SqSummable κ) {B : C}
    (g : X ⟶ B) : (familyMap hκ B g).val = fun j => κ j ≫ g := rfl

/-- **FDS 5.1** (`directsum_equiv`, direct_sums.tex:520, Theorem),
(a) ⇔ (b), valid in any C*-category: "(b) is a simple reformulation of the
universal property (a) via the Yoneda lemma" — the family is the image of
`1_A`, naturality computes the isomorphism as `f ↦ (f κᵢ)ᵢ`, and isometry is
the norm clause. -/
theorem isDirectSum_iff_exists_isUniversalFamily (X : C) :
    IsDirectSum A X ↔ ∃ κ : ∀ j, A j ⟶ X, IsUniversalFamily A κ := by
  constructor
  · rintro ⟨φ⟩
    let e : ∀ B : C, (X ⟶ B) ≃ₗᵢ[ℂ] DSum A B := fun B => φ.iso B
    set κ : ∀ j, A j ⟶ X := (e X (𝟙 X)).val with hκdef
    have hnat : ∀ (B : C) (g : X ⟶ B), (e B g).val = fun j => κ j ≫ g := by
      intro B g
      have h := φ.natural (𝟙 X) g
      rw [Category.id_comp] at h
      show DSum.val (φ.iso B g) = _
      rw [h]; rfl
    refine ⟨κ, (e X (𝟙 X)).sqSummable, fun B f hf => ?_, fun B f g hf hg => ?_⟩
    · refine ⟨(e B).symm (DSum.mk f hf), fun j => ?_, fun g hg => ?_⟩
      · have h := hnat B ((e B).symm (DSum.mk f hf))
        rw [LinearIsometryEquiv.apply_symm_apply] at h
        exact (congrFun h j).symm
      · apply (e B).injective
        rw [LinearIsometryEquiv.apply_symm_apply]
        apply DSum.val_injective
        rw [hnat]; funext j; exact hg j
    · have h1 : e B g = DSum.mk f hf :=
        DSum.val_injective (by rw [hnat]; funext j; exact hg j)
      have h2 := (e B).norm_map g
      rw [h1] at h2
      rw [← h2]
      exact DSum.norm_sq (DSum.mk f hf)
  · rintro ⟨κ, hκ, huniv, hnorm⟩
    have hbij : ∀ B : C, Function.Bijective (familyMap hκ B) := by
      intro B
      constructor
      · intro g g' h
        obtain ⟨g₀, -, huniq⟩ := huniv B _ (DSum.sqSummable (familyMap hκ B g))
        have h1 := huniq g (fun j => rfl)
        have h2 := huniq g' (fun j => by
          have := congrArg (fun x => DSum.val x j) h
          exact this.symm)
        rw [h1, h2]
      · intro x
        obtain ⟨g, hg, -⟩ := huniv B x.val x.sqSummable
        exact ⟨g, DSum.ext fun j => hg j⟩
    let e : ∀ B : C, (X ⟶ B) ≃ₗᵢ[ℂ] DSum A B := fun B =>
      { LinearEquiv.ofBijective (familyMap hκ B) (hbij B) with
        norm_map' := fun g => by
          show ‖familyMap hκ B g‖ = ‖g‖
          have h := hnorm B _ g (DSum.sqSummable (familyMap hκ B g)) (fun j => rfl)
          rw [DSum.norm_def, ← h, Real.sqrt_sq (norm_nonneg g)] }
    refine ⟨{ iso := e, natural := fun f g => ?_ }⟩
    apply DSum.ext
    intro j
    show κ j ≫ f ≫ g = (κ j ≫ f) ≫ g
    rw [Category.assoc]

open Classical in
/-- The family `(δᵢⱼ : Aᵢ → Aⱼ)ᵢ` of the proof of **FDS 5.1**. -/
def delta (j i : I) : A i ⟶ A j :=
  if h : i = j then eqToHom (congrArg A h) else 0

theorem delta_self (j : I) : delta (A := A) j j = 𝟙 (A j) := by
  simp [delta]

theorem delta_ne {i j : I} (h : i ≠ j) : delta (A := A) j i = 0 := by
  simp [delta, h]

theorem psum_delta_le (j : I) (S : Finset I) : psum (delta (A := A) j) S ≤ 1 := by
  classical
  have hterm : ∀ i, toEnd ((delta (A := A) j i)† ≫ delta j i) = if i = j then 1 else 0 := by
    intro i
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, delta_self]
      show (𝟙 (A i))† ≫ 𝟙 (A i) = 𝟙 (A i)
      simp
    · rw [if_neg h, delta_ne h]
      show (0 : A i ⟶ A j)† ≫ 0 = 0
      simp
  simp only [psum, hterm]
  rw [Finset.sum_ite_eq']
  split_ifs
  · exact le_rfl
  · exact zero_le_one' (End (A j))

theorem sqSummable_delta (j : I) : SqSummable (delta (A := A) j) :=
  ⟨1, by rintro _ ⟨S, rfl⟩; exact psum_delta_le j S⟩

theorem sqNorm_delta_le (j : I) : sqNorm (delta (A := A) j) ≤ 1 :=
  sqNorm_le fun S => (CStarAlgebra.norm_le_norm_of_nonneg_of_le (psum_nonneg _ S)
    (psum_delta_le j S)).trans (norm_id_le_one (A j))

/-- Under the relations `κᵢ*κⱼ = δᵢⱼ` the partial sums `∑_{j∈S} κⱼκⱼ*` are
projections. -/
theorem isStarProjection_psum {X : C} {κ : ∀ j, A j ⟶ X}
    (hiso : ∀ i, κ i ≫ (κ i)† = 𝟙 (A i)) (horth : ∀ i j, i ≠ j → κ j ≫ (κ i)† = 0)
    (S : Finset I) : IsStarProjection (psum κ S) := by
  classical
  refine ⟨?_, ?_⟩
  · show (∑ i ∈ S, (κ i)† ≫ κ i : X ⟶ X) ≫ (∑ i ∈ S, (κ i)† ≫ κ i) =
      ∑ i ∈ S, (κ i)† ≫ κ i
    rw [Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Preadditive.comp_sum, Finset.sum_eq_single i]
    · rw [Category.assoc, ← Category.assoc (κ i), hiso, Category.id_comp]
    · intro j _ hji
      rw [Category.assoc, ← Category.assoc (κ i), horth j i hji, Limits.zero_comp,
        Limits.comp_zero]
    · intro h; exact absurd hi h
  · show (∑ i ∈ S, (κ i)† ≫ κ i : X ⟶ X)† = ∑ i ∈ S, (κ i)† ≫ κ i
    rw [adj_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp

/-- **FDS 5.1** (`directsum_equiv`, direct_sums.tex:520, Theorem), (b) ⇒ (c),
the paper's proof: `‖κⱼ‖ ≤ 1` from the norm clause; the family `(δᵢⱼ)ᵢ` gives
`πⱼ` with `πⱼκᵢ = δᵢⱼ` and `‖πⱼ‖ ≤ 1`, so **FDS 3.2** makes `κⱼ` an isometry
with `πⱼ = κⱼ*`; for completeness, a projection `p` orthogonal to all `κⱼκⱼ*`
(here `1 - ⋁_S ∑_{j∈S} κⱼκⱼ*`) corresponds to the family `(pκⱼ) = 0`, so
`p = 0` by uniqueness. -/
theorem isOrthogonalSum_of_isUniversalFamily [WStarCategory C] {X : C}
    {κ : ∀ j, A j ⟶ X} (h : IsUniversalFamily A κ) : IsOrthogonalSum A κ := by
  classical
  obtain ⟨hκ, huniv, hnorm⟩ := h
  -- `‖κⱼ‖ ≤ 1`
  have hid := hnorm X κ (𝟙 X) hκ (fun j => Category.comp_id _)
  have hκn : ∀ j, ‖κ j‖ ≤ 1 := by
    intro j
    have h1 := norm_le_sqNorm hκ j
    rw [← hid] at h1
    have h2 := norm_id_le_one X
    have h3 : ‖κ j‖ ^ 2 ≤ 1 := h1.trans (by nlinarith [norm_nonneg (𝟙 X)])
    nlinarith [norm_nonneg (κ j)]
  -- the morphisms `πⱼ`
  have hπ : ∀ j, ∃ π : X ⟶ A j, (∀ i, κ i ≫ π = delta j i) ∧ ‖π‖ ≤ 1 := by
    intro j
    obtain ⟨π, hπ, -⟩ := huniv (A j) (delta j) (sqSummable_delta j)
    refine ⟨π, hπ, ?_⟩
    have h1 := hnorm (A j) (delta j) π (sqSummable_delta j) hπ
    have h2 := sqNorm_delta_le (A := A) j
    nlinarith [norm_nonneg π]
  choose π hπκ hπn using hπ
  have hiso : ∀ j, IsIsometry (κ j) ∧ π j = (κ j)† := fun j =>
    isometrylemma (π j) (κ j) (hπn j) (hκn j) (by rw [hπκ, delta_self])
  have horth : ∀ i j, i ≠ j → κ j ≫ (κ i)† = 0 := by
    intro i j hij
    rw [← (hiso i).2, hπκ, delta_ne (Ne.symm hij)]
  refine ⟨fun i => (hiso i).1, horth, ?_⟩
  -- completeness
  have hproj : ∀ S, IsStarProjection (psum κ S) :=
    isStarProjection_psum (fun i => (hiso i).1) horth
  set D : Set (End X) := Set.range (psum κ) with hDdef
  have hD : ∀ p ∈ D, IsStarProjection p := by rintro _ ⟨S, rfl⟩; exact hproj S
  have hne : D.Nonempty := ⟨_, ⟨∅, rfl⟩⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨S, rfl⟩ _ ⟨T, rfl⟩
    exact ⟨_, ⟨S ∪ T, rfl⟩, psum_mono κ Finset.subset_union_left,
      psum_mono κ Finset.subset_union_right⟩
  have hlub := isLUB_projSup_of_directed D hD hne hdir
  set q := projSup D with hqdef
  have hq : IsStarProjection q := (projSup_spec hD).1
  -- `p = 1 - q` is orthogonal to every `κⱼκⱼ*`, hence `pκⱼ`… `κⱼ ≫ p = 0`
  have hpκ : ∀ j, κ j ≫ ((1 - q : End X) : X ⟶ X) = 0 := by
    intro j
    have hle : psum κ {j} ≤ q := hlub.1 ⟨{j}, rfl⟩
    have hqe : q * psum κ {j} = psum κ {j} :=
      ((projection_below_effect q (psum κ {j}) ⟨hq.nonneg, proj_le_one hq⟩ (hproj {j})).out 0 6).mp hle
    have h1 : toEnd ((κ j)† ≫ κ j ≫ ((1 - q : End X) : X ⟶ X)) = 0 := by
      have : (1 - q) * psum κ {j} = 0 := by rw [sub_mul, one_mul, hqe, sub_self]
      rw [psum_singleton] at this
      simpa [end_mul_def, Category.assoc] using this
    calc κ j ≫ ((1 - q : End X) : X ⟶ X)
        = (κ j ≫ (κ j)†) ≫ κ j ≫ ((1 - q : End X) : X ⟶ X) := by
          rw [(hiso j).1, Category.id_comp]
      _ = 0 := by rw [Category.assoc]; exact (congrArg (κ j ≫ ·) h1).trans (Limits.comp_zero)
  have hq1 : q = 1 := by
    obtain ⟨g₀, -, huniq⟩ := huniv X (0 : ∀ j, A j ⟶ X) ⟨0, by
      rintro _ ⟨S, rfl⟩; exact (psum_zero S).le⟩
    have h1 := huniq ((1 - q : End X) : X ⟶ X) (fun j => hpκ j)
    have h2 := huniq 0 (fun j => Limits.comp_zero)
    have : (1 - q : End X) = 0 := h1.trans h2.symm
    exact (sub_eq_zero.mp this).symm
  rw [← hq1]
  exact hlub

/-- The Gram matrix of the partial sums `∑_{j∈S} fⱼκⱼ*` (diagrammatically
`∑ κⱼ† ≫ fⱼ`) under the relations `κᵢ*κⱼ = δᵢⱼ`. -/
theorem gram_psum [DecidableEq I] {X B : C} {κ : ∀ j, A j ⟶ X} (hiso : ∀ i, κ i ≫ (κ i)† = 𝟙 (A i))
    (horth : ∀ i j, i ≠ j → κ j ≫ (κ i)† = 0) (f : ∀ j, A j ⟶ B) (S T : Finset I) :
    (inner (End B) (∑ j ∈ S, (κ j)† ≫ f j) (∑ j ∈ T, (κ j)† ≫ f j) : End B)
      = psum f (S ∩ T) := by
  classical
  show (∑ j ∈ S, (κ j)† ≫ f j)† ≫ (∑ j ∈ T, (κ j)† ≫ f j) = ∑ i ∈ S ∩ T, (f i)† ≫ f i
  rw [adj_sum, Preadditive.sum_comp]
  have hterm : ∀ i ∈ S, ((κ i)† ≫ f i)† ≫ (∑ j ∈ T, (κ j)† ≫ f j)
      = if i ∈ T then (f i)† ≫ f i else 0 := by
    intro i _
    rw [Preadditive.comp_sum]
    have h2 : ∀ j, ((κ i)† ≫ f i)† ≫ (κ j)† ≫ f j
        = if i = j then (f i)† ≫ f i else 0 := by
      intro j
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, adj_comp', adj_adj', Category.assoc, ← Category.assoc (κ i),
          hiso, Category.id_comp]
      · rw [if_neg hij, adj_comp', adj_adj', Category.assoc, ← Category.assoc (κ i),
          horth j i (Ne.symm hij), Limits.zero_comp, Limits.comp_zero]
    simp only [h2]
    rw [Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_mem]

/-- In a W*-category every `∑ᵢ fᵢfᵢ* < ∞` has a supremum. -/
theorem exists_isLUB_psum [WStarCategory C] {B : C} {f : ∀ i, A i ⟶ B}
    (hf : SqSummable f) : ∃ s : End B, IsLUB (Set.range (psum f)) s := by
  classical
  set D : Set (selfAdjoint (End B)) :=
    Set.range fun S => (⟨psum f S, (IsSelfAdjoint.of_nonneg (psum_nonneg f S))⟩ :
      selfAdjoint (End B)) with hD
  have hne : D.Nonempty := ⟨_, ⟨∅, rfl⟩⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨S, rfl⟩ _ ⟨T, rfl⟩
    exact ⟨_, ⟨S ∪ T, rfl⟩, psum_mono f Finset.subset_union_left,
      psum_mono f Finset.subset_union_right⟩
  have hbdd : BddAbove D := by
    obtain ⟨M, hM⟩ := sqSummable_iff_norm.mp hf
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM ∅)
    refine ⟨⟨algebraMap ℝ (End B) M, IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all M)⟩, ?_⟩
    rintro _ ⟨S, rfl⟩
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ hM0 (psum_nonneg f S)).mp (hM S)
  obtain ⟨s, hs⟩ := VonNeumannAlgebra.isLUB_of_bddAbove_directed D hne hdir hbdd
  refine ⟨s, ?_⟩
  have := isLUB_coe_of_isLUB hne hs
  have himg : Subtype.val '' D = Set.range (psum f) := by
    ext y; constructor
    · rintro ⟨_, ⟨S, rfl⟩, rfl⟩; exact ⟨S, rfl⟩
    · rintro ⟨S, rfl⟩; exact ⟨_, ⟨S, rfl⟩, rfl⟩
  rwa [himg] at this

/-- `‖∑ᵢ fᵢfᵢ*‖` for the supremum in a W*-category is `sqNorm`, the supremum
of the norms of the partial sums. -/
theorem norm_eq_sqNorm_of_isLUB {B : C} {f : ∀ i, A i ⟶ B} {s : End B}
    (hs : IsLUB (Set.range (psum f)) s) : ‖s‖ = sqNorm f := by
  have hs0 : 0 ≤ s := (psum_nonneg f ∅).trans (hs.1 ⟨∅, rfl⟩)
  have hf : SqSummable f := ⟨s, hs.1⟩
  apply le_antisymm
  · have hub : ∀ S, psum f S ≤ algebraMap ℝ (End B) (sqNorm f) := fun S =>
      (CStarAlgebra.norm_le_iff_le_algebraMap _ (sqNorm_nonneg f) (psum_nonneg f S)).mp
        (norm_psum_le_sqNorm hf S)
    have := hs.2 (by rintro _ ⟨S, rfl⟩; exact hub S)
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ (sqNorm_nonneg f) hs0).mpr this
  · exact sqNorm_le fun S =>
      CStarAlgebra.norm_le_norm_of_nonneg_of_le (psum_nonneg f S) (hs.1 ⟨S, rfl⟩)

/-- The print's reading of `∑ⱼ fⱼfⱼ*` in a W*-category (the footnote to (4.1)):
for the positive family the ultraweak sum and the supremum of the partial sums
coincide. -/
theorem isLUB_iff_uwTendsto [WStarCategory C] {B : C} {f : ∀ i, A i ⟶ B} (s : End B) :
    IsLUB (Set.range (psum f)) s ↔ UWTendsto (psum f) atTop s :=
  ⟨fds_uwTendsto_of_isLUB _ (psum_mono f) (fun S => IsSelfAdjoint.of_nonneg (psum_nonneg f S)),
    fds_isLUB_of_uwTendsto _ (psum_mono f) (fun S => IsSelfAdjoint.of_nonneg (psum_nonneg f S))⟩

/-- **FDS 5.1** (`directsum_equiv`, direct_sums.tex:520, Theorem), (c) ⇒ (b),
the paper's proof (mirrored by `†`, see the file header).  The partial sums
`∑_{j∈S} fⱼκⱼ*` have Gram matrix `∑_{j∈S∩T} fⱼfⱼ*`, so they are ultranorm
Cauchy and bounded, and converge in the self-dual (hence bounded-ultranorm
complete, thesis B **149V**) module `C(A,B)` to some `f`; the bounded module
map `g ↦ g κⱼ` is ultranorm continuous, giving `f κⱼ = fⱼ`; the inner product
is ultraweakly continuous, giving `⟨f,f⟩ = ∑ⱼ fⱼfⱼ*` and the norm; and
uniqueness is `f' = f' ∑ⱼ κⱼκⱼ*`, the sum converging ultrastrongly. -/
theorem isUniversalFamily_of_isOrthogonalSum [WStarCategory C] {X : C}
    {κ : ∀ j, A j ⟶ X} (h : IsOrthogonalSum A κ) : IsUniversalFamily A κ := by
  classical
  obtain ⟨hiso, horth, hlub⟩ := h
  have hκ : SqSummable κ := ⟨1, hlub.1⟩
  have hκn : ∀ j, ‖κ j‖ ≤ 1 := fun j => by
    have h1 : ‖κ j‖ ^ 2 = ‖𝟙 (A j)‖ := by rw [← CStarCategory.norm_comp_adj, hiso]
    have h2 := norm_id_le_one (A j)
    nlinarith [norm_nonneg (κ j)]
  have hproj : ∀ S, IsStarProjection (psum κ S) := isStarProjection_psum hiso horth
  -- existence, with the norm
  have hex : ∀ (B : C) (f : ∀ j, A j ⟶ B), SqSummable f →
      ∃ g : X ⟶ B, (∀ j, κ j ≫ g = f j) ∧ ‖g‖ ^ 2 = sqNorm f := by
    intro B f hf
    set v : Finset I → (X ⟶ B) := fun S => ∑ j ∈ S, (κ j)† ≫ f j with hv
    obtain ⟨M, hM⟩ := sqSummable_iff_norm.mp hf
    obtain ⟨g, hg⟩ := fds_exists_unTendsto_of_gram
      (bddUnComplete_of_selfDual (WStarCategory.selfDual X B)) v (psum f)
      (gram_psum hiso horth f) (psum_mono f) (psum_nonneg f) M hM
    refine ⟨g, fun j => ?_, ?_⟩
    · -- the bounded module map `h ↦ h κⱼ` is ultranorm continuous
      have hT : IsBoundedModuleMap (cstarBInner (End B) (X ⟶ B))
          (cstarBInner (End B) (A j ⟶ B)) 1 (fun h => κ j ≫ h) :=
        { add := fun x y => Preadditive.comp_add _ _ _ _ _ _
          smul_complex := fun c x => Linear.comp_smul _ _ _ _ _ _
          smul := fun b x => (Category.assoc _ _ _).symm
          bound := fun x => by
            rw [cstarBInner_norm, cstarBInner_norm, one_mul]
            exact (NormedStarCategory.norm_comp_le _ _).trans
              (mul_le_of_le_one_left (norm_nonneg _) (hκn j)) }
      have h1 := fds_unTendsto_map _ _ zero_le_one hT hg
      have hev : ∀ S, j ∈ S → κ j ≫ v S = f j := by
        intro S hS
        simp only [hv]
        rw [Preadditive.comp_sum, Finset.sum_eq_single j]
        · rw [← Category.assoc, hiso, Category.id_comp]
        · intro i _ hij
          rw [← Category.assoc, horth i j hij, Limits.zero_comp]
        · intro h; exact absurd hS h
      have h2 : UnTendsto (cstarBInner (End B) (A j ⟶ B)).inner (fun S => κ j ≫ v S) atTop
          (f j) := by
        intro ω
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop {j}] with S hS
        rw [hev S (hS (Finset.mem_singleton_self j)), sub_self, fds_unSeminorm_zero]
      exact fds_unTendsto_unique h1 h2
    · -- the norm, through `⟨f,f⟩ = uwlim ⟨v S, v S⟩ = ∑ⱼ fⱼfⱼ*`
      obtain ⟨s, hs⟩ := exists_isLUB_psum hf
      have h1 := innerprod_ultraweak (cstarBInner (End B) (X ⟶ B)) v v g g hg hg
      have h1' : UWTendsto (psum f) atTop (inner (End B) g g) := by
        unfold UWTendsto at h1 ⊢
        refine h1.congr fun S => ?_
        show (inner (End B) (v S) (v S) : End B) = psum f S
        rw [gram_psum hiso horth f, Finset.inter_self]
      have h2 := fds_uwTendsto_of_isLUB (psum f) (psum_mono f)
        (fun S => IsSelfAdjoint.of_nonneg (psum_nonneg f S)) hs
      have h3 : (inner (End B) g g : End B) = s := fds_uwTendsto_unique h1' h2
      rw [← norm_eq_sqNorm_of_isLUB hs, ← h3]
      exact CStarModule.norm_sq_eq (End B)
  -- uniqueness: `d κⱼ = 0` for all `j` forces `d = 0`
  have huniq : ∀ (B : C) (d : X ⟶ B), (∀ j, κ j ≫ d = 0) → d = 0 := by
    intro B d hd
    have hP : UnTendsto (mulInner (End X)) (psum κ) atTop 1 := by
      intro ω
      have hconv := (uwTendsto_iff _ _ _).mp (fds_uwTendsto_of_isLUB (psum κ) (psum_mono κ)
        (fun S => (hproj S).isSelfAdjoint) hlub) ω
      have heq : ∀ S, unSeminorm ω (mulInner (End X)) (psum κ S - 1)
          = Real.sqrt ((ω 1).re - (ω (psum κ S)).re) := by
        intro S
        have hp := hproj S
        have hpp : psum κ S * psum κ S = psum κ S := hp.isIdempotentElem.eq
        have e : (psum κ S - 1) * star (psum κ S - 1) = 1 - psum κ S := by
          rw [star_sub, star_one, hp.isSelfAdjoint.star_eq]
          calc (psum κ S - 1) * (psum κ S - 1)
              = psum κ S * psum κ S - psum κ S - psum κ S + 1 := by noncomm_ring
            _ = 1 - psum κ S := by rw [hpp]; abel
        rw [unSeminorm, mulInner, e, npFunctional_sub, Complex.sub_re]
      simp_rw [heq]
      have h1 : Tendsto (fun S => (ω 1).re - (ω (psum κ S)).re) atTop (𝓝 0) := by
        have := (Complex.continuous_re.tendsto _).comp hconv
        simpa using (tendsto_const_nhds (x := (ω 1).re)).sub this
      have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at h2
      exact h2
    have hT : IsBoundedModuleMap (mulBInner (End X)) (cstarBInner (End X) (B ⟶ X)) ‖d†‖
        (fun y : End X => d† ≫ (y : X ⟶ X)) :=
      { add := fun x y => Preadditive.comp_add _ _ _ _ _ _
        smul_complex := fun c x => Linear.comp_smul _ _ _ _ _ _
        smul := fun b x => (Category.assoc _ _ _).symm
        bound := fun x => by
          rw [cstarBInner_norm, mulBInner_norm]
          exact NormedStarCategory.norm_comp_le _ _ }
    have h1 := fds_unTendsto_map _ _ (norm_nonneg _) hT hP
    have hzero : ∀ S, d† ≫ (psum κ S : X ⟶ X) = 0 := by
      intro S
      show d† ≫ (∑ j ∈ S, (κ j)† ≫ κ j) = 0
      rw [Preadditive.comp_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Category.assoc, ← adj_comp', hd, adj_zero', Limits.zero_comp]
    have h2 : UnTendsto (cstarBInner (End X) (B ⟶ X)).inner
        (fun S => d† ≫ (psum κ S : X ⟶ X)) atTop 0 := by
      intro ω
      simp only [hzero, sub_zero, fds_unSeminorm_zero]
      exact tendsto_const_nhds
    have h3 : d† ≫ ((1 : End X) : X ⟶ X) = 0 := fds_unTendsto_unique h1 h2
    rw [end_one_def, Category.comp_id] at h3
    rw [← adj_adj' d, h3, adj_zero']
  refine ⟨hκ, fun B f hf => ?_, fun B f g hf hg => ?_⟩
  · obtain ⟨g, hg, -⟩ := hex B f hf
    refine ⟨g, hg, fun g' hg' => ?_⟩
    have := huniq B (g' - g) (fun j => by rw [Preadditive.comp_sub, hg, hg', sub_self])
    exact sub_eq_zero.mp this
  · obtain ⟨g₀, hg₀, hn⟩ := hex B f hf
    have : g = g₀ :=
      sub_eq_zero.mp (huniq B (g - g₀) (fun j => by rw [Preadditive.comp_sub, hg, hg₀, sub_self]))
    rw [this, hn]

/-- **FDS 5.1** (`directsum_equiv`, direct_sums.tex:520, Theorem): in a
W*-category, (b) ⇔ (c) for a given family `κ`. -/
theorem isUniversalFamily_iff_isOrthogonalSum [WStarCategory C] {X : C}
    (κ : ∀ j, A j ⟶ X) : IsUniversalFamily A κ ↔ IsOrthogonalSum A κ :=
  ⟨isOrthogonalSum_of_isUniversalFamily, isUniversalFamily_of_isOrthogonalSum⟩

/-- **FDS 5.1** (`directsum_equiv`, direct_sums.tex:520, Theorem): for a
family `(Aᵢ)ᵢ` in a W*-category and an object `X`, the following are
equivalent: (a) `X` is an `I`-indexed direct sum `⊕ᵢ Aᵢ`; (b) there is a
family `κⱼ : Aⱼ → X` with the universal property with norms; (c) there is a
family `κⱼ : Aⱼ → X` with `κᵢ*κⱼ = δᵢⱼ` and `∑ⱼ κⱼκⱼ* = 1` (GLR). -/
theorem directsum_equiv [WStarCategory C] (X : C) :
    List.TFAE [IsDirectSum A X, ∃ κ : ∀ j, A j ⟶ X, IsUniversalFamily A κ,
      ∃ κ : ∀ j, A j ⟶ X, IsOrthogonalSum A κ] := by
  tfae_have 1 ↔ 2 := isDirectSum_iff_exists_isUniversalFamily X
  tfae_have 2 ↔ 3 := exists_congr fun κ => isUniversalFamily_iff_isOrthogonalSum κ
  tfae_finish

end Sec5

/-! ### Corollary 5.2: normal `*`-functors preserve direct sums -/

section Cor52

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [StarCategory C]
  [NormedStarCategory C] [CStarCategory C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear ℂ D] [StarCategory D]
  [NormedStarCategory D] [CStarCategory D]

open StarCategory

/-- A **normal `*`-functor** between W*-categories (Ghez–Lima–Roberts): a
ℂ-linear functor commuting with the involution whose restriction to each
endomorphism algebra `C(X,X) → D(FX,FX)` is normal (preserves suprema of
bounded directed sets of self-adjoint elements). -/
structure IsNormalStarFunctor (F : C ⥤ D) [F.Additive] [F.Linear ℂ] : Prop where
  map_adj : ∀ {X Y : C} (f : X ⟶ Y), F.map f† = (F.map f)†
  normal : ∀ X : C, PreservesDirSups (fun x : End X => toEnd (F.map (x : X ⟶ X)))

/-- **FDS 5.2** (direct_sums.tex:635, Corollary): every normal `*`-functor
between W*-categories preserves direct sums — "straightforward" from the
characterisation **FDS 5.1**(c): the relations `κᵢ*κⱼ = δᵢⱼ` are preserved by
any `*`-functor, and `∑ⱼ κⱼκⱼ* = 1` by normality. -/
theorem normal_functor_preserves_directSum [WStarCategory C] [WStarCategory D]
    (F : C ⥤ D) [F.Additive] [F.Linear ℂ] (hF : IsNormalStarFunctor F)
    {I : Type w} {A : I → C} {X : C} (h : IsDirectSum A X) :
    IsDirectSum (fun i => F.obj (A i)) (F.obj X) := by
  classical
  obtain ⟨κ, hiso, horth, hlub⟩ := ((directsum_equiv (A := A) X).out 0 2).mp h
  suffices hc : ∃ κ' : ∀ j, F.obj (A j) ⟶ F.obj X, IsOrthogonalSum (fun i => F.obj (A i)) κ' from
    ((directsum_equiv (A := fun i => F.obj (A i)) (F.obj X)).out 0 2).mpr hc
  refine ⟨fun j => F.map (κ j), fun i => ?_, fun i j hij => ?_, ?_⟩
  · rw [← hF.map_adj, ← F.map_comp, hiso i, F.map_id]
  · rw [← hF.map_adj, ← F.map_comp, horth i j hij, F.map_zero]
  · have hps : ∀ S, psum (fun j => F.map (κ j)) S = toEnd (F.map (psum κ S : X ⟶ X)) := by
      intro S
      show (∑ j ∈ S, (F.map (κ j))† ≫ F.map (κ j) : F.obj X ⟶ F.obj X)
        = F.map (∑ j ∈ S, (κ j)† ≫ κ j)
      rw [F.map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [F.map_comp, hF.map_adj]
    set E : Set (selfAdjoint (End X)) :=
      Set.range fun S => (⟨psum κ S, IsSelfAdjoint.of_nonneg (psum_nonneg κ S)⟩ :
        selfAdjoint (End X)) with hE
    have himg : Subtype.val '' E = Set.range (psum κ) := by
      ext y; constructor
      · rintro ⟨_, ⟨S, rfl⟩, rfl⟩; exact ⟨S, rfl⟩
      · rintro ⟨S, rfl⟩; exact ⟨_, ⟨S, rfl⟩, rfl⟩
    have hlubE : IsLUB E ⟨1, selfAdjoint.mem_iff.mpr (IsSelfAdjoint.one _)⟩ :=
      isLUB_sa_of_isLUB (by rw [himg]; exact hlub)
    have hne : E.Nonempty := ⟨_, ⟨∅, rfl⟩⟩
    have hdir : DirectedOn (· ≤ ·) E := by
      rintro _ ⟨S, rfl⟩ _ ⟨T, rfl⟩
      exact ⟨_, ⟨S ∪ T, rfl⟩, psum_mono κ Finset.subset_union_left,
        psum_mono κ Finset.subset_union_right⟩
    have hn := hF.normal X E ⟨1, selfAdjoint.mem_iff.mpr (IsSelfAdjoint.one _)⟩ hne hdir hlubE
    have himg2 : (fun d : selfAdjoint (End X) => toEnd (F.map ((d : End X) : X ⟶ X))) '' E
        = Set.range (psum fun j => F.map (κ j)) := by
      ext y; constructor
      · rintro ⟨_, ⟨S, rfl⟩, rfl⟩; exact ⟨S, (hps S)⟩
      · rintro ⟨S, rfl⟩; exact ⟨_, ⟨S, rfl⟩, (hps S).symm⟩
    rw [himg2] at hn
    have hn' : IsLUB (Set.range (psum fun j => F.map (κ j))) (toEnd (F.map (𝟙 X))) := hn
    rw [F.map_id] at hn'
    exact hn'

end Cor52

/-! ## Section 1: the classical case (Theorem 1.1) -/

section Thm11

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **FDS 1.1**(a): `A` represents `C → Ab`, `B ↦ C(A₁,B) × C(A₂,B)`: a
natural isomorphism of abelian groups `C(A,B) ≅ C(A₁,B) × C(A₂,B)`. -/
def RepresentsCoprod (A₁ A₂ A : C) : Prop :=
  ∃ φ : ∀ B : C, (A ⟶ B) ≃+ (A₁ ⟶ B) × (A₂ ⟶ B),
    ∀ {B B' : C} (f : A ⟶ B) (g : B ⟶ B'), φ B' (f ≫ g) = ((φ B f).1 ≫ g, (φ B f).2 ≫ g)

/-- **FDS 1.1**(b): `A` represents `Cᵒᵖ → Ab`, `B ↦ C(B,A₁) × C(B,A₂)`. -/
def RepresentsProd (A₁ A₂ A : C) : Prop :=
  ∃ φ : ∀ B : C, (B ⟶ A) ≃+ (B ⟶ A₁) × (B ⟶ A₂),
    ∀ {B B' : C} (g : B' ⟶ B) (f : B ⟶ A), φ B' (g ≫ f) = (g ≫ (φ B f).1, g ≫ (φ B f).2)

/-- **FDS 1.1**(c): morphisms `pᵢ : A → Aᵢ`, `κᵢ : Aᵢ → A` with the
biproduct equations `pᵢκⱼ = δᵢⱼ`, `κ₁p₁ + κ₂p₂ = 1`. -/
def IsBiprodData (A₁ A₂ A : C) : Prop :=
  ∃ (p₁ : A ⟶ A₁) (p₂ : A ⟶ A₂) (κ₁ : A₁ ⟶ A) (κ₂ : A₂ ⟶ A),
    κ₁ ≫ p₁ = 𝟙 A₁ ∧ κ₂ ≫ p₂ = 𝟙 A₂ ∧ κ₁ ≫ p₂ = 0 ∧ κ₂ ≫ p₁ = 0 ∧
      p₁ ≫ κ₁ + p₂ ≫ κ₂ = 𝟙 A

/-- **FDS 1.1** (`directsum_equiv_trad`, direct_sums.tex:152, Theorem, cited
from Borceux Prop. 1.2.4): in an additive (here: preadditive suffices)
category, for objects `A₁, A₂, A` the following are equivalent: (a) `A`
represents `B ↦ C(A₁,B) × C(A₂,B)`; (b) `A` represents
`B ↦ C(B,A₁) × C(B,A₂)`; (c) there are `pᵢ`, `κᵢ` satisfying the biproduct
equations.  (The print cites the result; the proof here is the standard
Yoneda argument.) -/
theorem directsum_equiv_trad (A₁ A₂ A : C) :
    List.TFAE [RepresentsCoprod A₁ A₂ A, RepresentsProd A₁ A₂ A, IsBiprodData A₁ A₂ A] := by
  tfae_have 1 → 3 := by
    rintro ⟨φ, hφ⟩
    set κ₁ := (φ A (𝟙 A)).1
    set κ₂ := (φ A (𝟙 A)).2
    have hnat : ∀ (B : C) (g : A ⟶ B), φ B g = (κ₁ ≫ g, κ₂ ≫ g) := by
      intro B g
      have := hφ (𝟙 A) g
      rwa [Category.id_comp] at this
    set p₁ := (φ A₁).symm (𝟙 A₁, 0)
    set p₂ := (φ A₂).symm (0, 𝟙 A₂)
    have h1 : φ A₁ p₁ = (𝟙 A₁, 0) := (φ A₁).apply_symm_apply _
    have h2 : φ A₂ p₂ = (0, 𝟙 A₂) := (φ A₂).apply_symm_apply _
    rw [hnat] at h1 h2
    simp only [Prod.mk.injEq] at h1 h2
    obtain ⟨h11, h21⟩ := h1
    obtain ⟨h12, h22⟩ := h2
    refine ⟨p₁, p₂, κ₁, κ₂, h11, h22, h12, h21, ?_⟩
    apply (φ A).injective
    rw [map_add, hnat, hnat, hnat]
    simp only [← Category.assoc, h11, h21, h12, h22, Category.id_comp, Category.comp_id,
      Limits.zero_comp, Prod.mk_add_mk, add_zero, zero_add]
  tfae_have 3 → 1 := by
    rintro ⟨p₁, p₂, κ₁, κ₂, h11, h22, h12, h21, htot⟩
    refine ⟨fun B => { toFun := fun g => (κ₁ ≫ g, κ₂ ≫ g)
                       invFun := fun f => p₁ ≫ f.1 + p₂ ≫ f.2
                       left_inv := fun g => by
                         simp only [← Category.assoc, ← Preadditive.add_comp, htot,
                           Category.id_comp]
                       right_inv := fun f => by
                         ext
                         · simp [Preadditive.comp_add, ← Category.assoc, h11, h12]
                         · simp [Preadditive.comp_add, ← Category.assoc, h21, h22]
                       map_add' := fun g g' => by simp [Preadditive.comp_add] }, ?_⟩
    intro B B' f g
    simp
  tfae_have 2 → 3 := by
    rintro ⟨φ, hφ⟩
    set p₁ := (φ A (𝟙 A)).1
    set p₂ := (φ A (𝟙 A)).2
    have hnat : ∀ (B : C) (g : B ⟶ A), φ B g = (g ≫ p₁, g ≫ p₂) := by
      intro B g
      have := hφ g (𝟙 A)
      rwa [Category.comp_id] at this
    set κ₁ := (φ A₁).symm (𝟙 A₁, 0)
    set κ₂ := (φ A₂).symm (0, 𝟙 A₂)
    have h1 : φ A₁ κ₁ = (𝟙 A₁, 0) := (φ A₁).apply_symm_apply _
    have h2 : φ A₂ κ₂ = (0, 𝟙 A₂) := (φ A₂).apply_symm_apply _
    rw [hnat] at h1 h2
    simp only [Prod.mk.injEq] at h1 h2
    obtain ⟨h11, h12⟩ := h1
    obtain ⟨h21, h22⟩ := h2
    refine ⟨p₁, p₂, κ₁, κ₂, h11, h22, h12, h21, ?_⟩
    apply (φ A).injective
    rw [map_add, hnat, hnat, hnat]
    simp only [Category.assoc, h11, h21, h12, h22, Category.id_comp, Category.comp_id,
      Limits.comp_zero, Prod.mk_add_mk, add_zero, zero_add]
  tfae_have 3 → 2 := by
    rintro ⟨p₁, p₂, κ₁, κ₂, h11, h22, h12, h21, htot⟩
    refine ⟨fun B => { toFun := fun g => (g ≫ p₁, g ≫ p₂)
                       invFun := fun f => f.1 ≫ κ₁ + f.2 ≫ κ₂
                       left_inv := fun g => by
                         simp only [Category.assoc, ← Preadditive.comp_add, htot,
                           Category.comp_id]
                       right_inv := fun f => by
                         ext
                         · simp [Preadditive.add_comp, h11, h21]
                         · simp [Preadditive.add_comp, h12, h22]
                       map_add' := fun g g' => by simp [Preadditive.add_comp] }, ?_⟩
    intro B B' g f
    simp
  tfae_finish

end Thm11

/-! ## W*-categories from linking objects

The examples **FDS 2.3**–**2.5** are W*-categories "in the obvious way"; the
print refers to [GLR] for the proofs.  Our route: in a C*-category, if `A`
and `B` embed isometrically into an object `S` whose endomorphism algebra is
a von Neumann algebra, then `End A` is the corner `p End(S) p` and `C(A,B)`
is cut out of the self-dual `q End(S)`-module `q End(S)` (thesis B **171II**,
`cornerLeft_selfDual`). -/

section Linking

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [StarCategory C]
  [NormedStarCategory C] [CStarCategory C]

open StarCategory

theorem norm_le_one_of_isIsometry {X Y : C} {ι : X ⟶ Y} (h : IsIsometry ι) : ‖ι‖ ≤ 1 := by
  have h1 := CStarCategory.norm_comp_adj ι
  rw [show ι ≫ ι† = 𝟙 X from h] at h1
  have := norm_id_le_one X
  nlinarith [norm_nonneg ι]

theorem isometry_comp_adj_comp {X Y Z : C} {ι : X ⟶ Y} (h : IsIsometry ι) (g : X ⟶ Z) :
    ι ≫ ι† ≫ g = g := by
  rw [← Category.assoc, show ι ≫ ι† = 𝟙 X from h, Category.id_comp]

/-- The corner isomorphism `p End(S) p ≅ End A` for an isometry `ι : A → S`,
`p = ι ι*`. -/
def cornerEquiv {A S : C} (ι : A ⟶ S) (hι : IsIsometry ι)
    [Fact (IsStarProjection (toEnd (ι† ≫ ι)))] :
    cornerSet (End S) (toEnd (ι† ≫ ι)) ≃⋆ₐ[ℂ] End A where
  toFun y := toEnd (ι ≫ (y.1 : S ⟶ S) ≫ ι†)
  invFun x := ⟨toEnd (ι† ≫ (x : A ⟶ A) ≫ ι), by
    show (ι† ≫ ι) ≫ (ι† ≫ (x : A ⟶ A) ≫ ι) ≫ (ι† ≫ ι) = ι† ≫ (x : A ⟶ A) ≫ ι
    simp only [Category.assoc, isometry_comp_adj_comp hι]⟩
  left_inv y := by
    apply cornerSet.val_injective
    show ι† ≫ (ι ≫ (y.1 : S ⟶ S) ≫ ι†) ≫ ι = y.1
    have h2 : (ι† ≫ ι) ≫ (y.1 : S ⟶ S) ≫ (ι† ≫ ι) = y.1 := y.2
    simpa only [Category.assoc] using h2
  right_inv x := by
    show ι ≫ (ι† ≫ (x : A ⟶ A) ≫ ι) ≫ ι† = x
    simp only [Category.assoc, isometry_comp_adj_comp hι]
    rw [show ι ≫ ι† = 𝟙 A from hι, Category.comp_id]
  map_mul' y y' := by
    show ι ≫ ((y'.1 : S ⟶ S) ≫ y.1) ≫ ι† = (ι ≫ (y'.1 : S ⟶ S) ≫ ι†) ≫ ι ≫ (y.1 : S ⟶ S) ≫ ι†
    have h : (y'.1 : S ⟶ S) ≫ (ι† ≫ ι) = y'.1 := cornerSet.mul_left y'
    have h' : ∀ {Z : C} (g : S ⟶ Z), (y'.1 : S ⟶ S) ≫ ι† ≫ ι ≫ g = (y'.1 : S ⟶ S) ≫ g := by
      intro Z g
      have := congrArg (· ≫ g) h
      simpa only [Category.assoc] using this
    simp only [Category.assoc, h']
  map_add' y y' := by
    show ι ≫ ((y.1 : S ⟶ S) + y'.1) ≫ ι† = ι ≫ (y.1 : S ⟶ S) ≫ ι† + ι ≫ (y'.1 : S ⟶ S) ≫ ι†
    rw [Preadditive.add_comp, Preadditive.comp_add]
  map_star' y := by
    show ι ≫ (y.1 : S ⟶ S)† ≫ ι† = (ι ≫ (y.1 : S ⟶ S) ≫ ι†)†
    simp [Category.assoc]
  map_smul' c y := by
    show ι ≫ (c • (y.1 : S ⟶ S)) ≫ ι† = c • (ι ≫ (y.1 : S ⟶ S) ≫ ι†)
    rw [Linear.smul_comp, Linear.comp_smul]

/-- The endomorphism algebra of an object embedded isometrically in an
object with a von Neumann endomorphism algebra is a von Neumann algebra
(thesis A proc.tex **94II**, corners of von Neumann algebras). -/
theorem vonNeumann_of_isometry {A S : C} (ι : A ⟶ S) (hι : IsIsometry ι)
    [VonNeumannAlgebra (End S)] : VonNeumannAlgebra (End A) := by
  haveI : Fact (IsStarProjection (toEnd (ι† ≫ ι))) := ⟨isStarProjection_adj_comp ι hι⟩
  haveI := cornerSet_vonNeumannAlgebra (End S) (toEnd (ι† ≫ ι))
  exact vonNeumannAlgebra_of_starAlgEquiv (cornerEquiv ι hι)

/-- If `A` and `B` embed isometrically into `S` with `End S` a von Neumann
algebra, then `C(A,B)` is a self-dual Hilbert `End B`-module: a bounded
module map `τ : C(A,B) → End B` is transported to the self-dual module
`q End(S)` over `q End(S) q` (thesis B **171II**, `cornerLeft_selfDual`),
represented there, and the representing vector is cut down again. -/
theorem selfDual_of_isometries {A B S : C} (ιA : A ⟶ S) (ιB : B ⟶ S) (hA : IsIsometry ιA)
    (hB : IsIsometry ιB) [VonNeumannAlgebra (End S)] : SelfDual (End B) (A ⟶ B) := by
  set q : End S := toEnd (ιB† ≫ ιB) with hq
  haveI : Fact (IsStarProjection q) := ⟨isStarProjection_adj_comp ιB hB⟩
  haveI := cornerSet_vonNeumannAlgebra (End S) q
  intro τ hmod ⟨K, hK⟩
  -- the cut-down `y ↦ ιA ≫ y ≫ ιB†` (the paper's `ιB* y ιA`)
  let r : cornerLeft q → (A ⟶ B) := fun y => ιA ≫ ((y : End S) : S ⟶ S) ≫ ιB†
  have hr_add : ∀ y y', r (y + y') = r y + r y' := fun y y' => by
    show ιA ≫ (((y : End S) : S ⟶ S) + (y' : End S)) ≫ ιB† = _
    rw [Preadditive.add_comp, Preadditive.comp_add]
  have hr_smul : ∀ (c : ℂ) y, r (c • y) = c • r y := fun c y => by
    show ιA ≫ (c • ((y : End S) : S ⟶ S)) ≫ ιB† = _
    rw [Linear.smul_comp, Linear.comp_smul]
  have hr_norm : ∀ y, ‖r y‖ ≤ ‖y‖ := fun y => by
    calc ‖r y‖ ≤ ‖ιA‖ * (‖((y : End S) : S ⟶ S)‖ * ‖ιB†‖) :=
          (NormedStarCategory.norm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (NormedStarCategory.norm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖((y : End S) : S ⟶ S)‖ * 1) := by
          gcongr
          · exact norm_le_one_of_isIsometry hA
          · rw [norm_adj]; exact norm_le_one_of_isIsometry hB
      _ = ‖y‖ := by rw [one_mul, mul_one]; rfl
  -- the transported functional `τ' : q End(S) → q End(S) q`
  have hcorner : ∀ w : B ⟶ B, q * toEnd (ιB† ≫ w ≫ ιB) * q = toEnd (ιB† ≫ w ≫ ιB) := by
    intro w
    show (ιB† ≫ ιB) ≫ (ιB† ≫ w ≫ ιB) ≫ (ιB† ≫ ιB) = ιB† ≫ w ≫ ιB
    simp only [Category.assoc, isometry_comp_adj_comp hB]
  let τ' : cornerLeft q →ₗ[ℂ] cornerSet (End S) q :=
    { toFun := fun y => ⟨toEnd (ιB† ≫ (τ (r y) : B ⟶ B) ≫ ιB), hcorner _⟩
      map_add' := fun y y' => by
        apply cornerSet.val_injective
        show ιB† ≫ (τ (r (y + y')) : B ⟶ B) ≫ ιB
          = ιB† ≫ (τ (r y) : B ⟶ B) ≫ ιB + ιB† ≫ (τ (r y') : B ⟶ B) ≫ ιB
        rw [hr_add, map_add]
        show ιB† ≫ ((τ (r y) : B ⟶ B) + τ (r y')) ≫ ιB = _
        rw [Preadditive.add_comp, Preadditive.comp_add]
      map_smul' := fun c y => by
        apply cornerSet.val_injective
        show ιB† ≫ (τ (r (c • y)) : B ⟶ B) ≫ ιB = c • (ιB† ≫ (τ (r y) : B ⟶ B) ≫ ιB)
        rw [hr_smul, map_smul]
        show ιB† ≫ (c • (τ (r y) : B ⟶ B)) ≫ ιB = _
        rw [Linear.smul_comp, Linear.comp_smul] }
  have hτ'_val : ∀ y, ((τ' y).1 : S ⟶ S) = ιB† ≫ (τ (r y) : B ⟶ B) ≫ ιB := fun y => rfl
  have hmod' : ∀ (b : cornerSet (End S) q) (y : cornerLeft q), τ' (b • y) = b * τ' y := by
    intro b y
    apply cornerSet.val_injective
    -- `r (b • y) = r y ≫ b''` with `b'' = ιB ≫ b ≫ ιB†`
    have hb1 : ((ιB† ≫ ιB) ≫ (b.1 : S ⟶ S) : S ⟶ S) = b.1 := cornerSet.mul_right b
    have hb2 : ((b.1 : S ⟶ S) ≫ (ιB† ≫ ιB) : S ⟶ S) = b.1 := cornerSet.mul_left b
    have hb1' : ∀ {Z : C} (g : S ⟶ Z), ιB† ≫ ιB ≫ (b.1 : S ⟶ S) ≫ g = (b.1 : S ⟶ S) ≫ g := by
      intro Z g
      have := congrArg (· ≫ g) hb1
      simpa only [Category.assoc] using this
    have hb2' : ∀ {Z : C} (g : S ⟶ Z), (b.1 : S ⟶ S) ≫ ιB† ≫ ιB ≫ g = (b.1 : S ⟶ S) ≫ g := by
      intro Z g
      have := congrArg (· ≫ g) hb2
      simpa only [Category.assoc] using this
    have hrb : r (b • y) = toEnd (ιB ≫ (b.1 : S ⟶ S) ≫ ιB†) • r y := by
      show ιA ≫ (((y : End S) : S ⟶ S) ≫ b.1) ≫ ιB†
        = (ιA ≫ ((y : End S) : S ⟶ S) ≫ ιB†) ≫ ιB ≫ (b.1 : S ⟶ S) ≫ ιB†
      simp only [Category.assoc, hb1']
    show ιB† ≫ (τ (r (b • y)) : B ⟶ B) ≫ ιB = (ιB† ≫ (τ (r y) : B ⟶ B) ≫ ιB) ≫ (b.1 : S ⟶ S)
    rw [hrb, hmod]
    show ιB† ≫ ((τ (r y) : B ⟶ B) ≫ ιB ≫ (b.1 : S ⟶ S) ≫ ιB†) ≫ ιB = _
    simp only [Category.assoc]
    rw [hb2]
  have hbdd' : ∃ C₀ : ℝ, ∀ y, ‖τ' y‖ ≤ C₀ * ‖y‖ := by
    refine ⟨max K 0, fun y => ?_⟩
    have h1 : ‖τ' y‖ ≤ ‖τ (r y)‖ := by
      show ‖ιB† ≫ (τ (r y) : B ⟶ B) ≫ ιB‖ ≤ _
      calc ‖ιB† ≫ (τ (r y) : B ⟶ B) ≫ ιB‖
          ≤ ‖ιB†‖ * (‖(τ (r y) : B ⟶ B)‖ * ‖ιB‖) :=
            (NormedStarCategory.norm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_left (NormedStarCategory.norm_comp_le _ _) (norm_nonneg _))
        _ ≤ 1 * (‖(τ (r y) : B ⟶ B)‖ * 1) := by
            gcongr
            · rw [norm_adj]; exact norm_le_one_of_isIsometry hB
            · exact norm_le_one_of_isIsometry hB
        _ = ‖τ (r y)‖ := by rw [one_mul, mul_one]
    calc ‖τ' y‖ ≤ ‖τ (r y)‖ := h1
      _ ≤ K * ‖r y‖ := hK (r y)
      _ ≤ max K 0 * ‖r y‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max K 0 * ‖y‖ := mul_le_mul_of_nonneg_left (hr_norm y) (le_max_right _ _)
  obtain ⟨t, ht⟩ := cornerLeft_selfDual τ' hmod' hbdd'
  refine ⟨ιA ≫ ((t : End S) : S ⟶ S) ≫ ιB†, fun x => ?_⟩
  -- evaluate at `y = ιA* x ιB` hmm, diagrammatically `ιA† ≫ x ≫ ιB`
  have hy : q * toEnd (ιA† ≫ x ≫ ιB) = toEnd (ιA† ≫ x ≫ ιB) := by
    show (ιA† ≫ x ≫ ιB) ≫ (ιB† ≫ ιB) = ιA† ≫ x ≫ ιB
    simp only [Category.assoc, isometry_comp_adj_comp hB]
  set y : cornerLeft q := ⟨toEnd (ιA† ≫ x ≫ ιB), hy⟩ with hydef
  have hry : r y = x := by
    show ιA ≫ (ιA† ≫ x ≫ ιB) ≫ ιB† = x
    simp only [Category.assoc, isometry_comp_adj_comp hA]
    rw [show ιB ≫ ιB† = 𝟙 B from hB, Category.comp_id]
  have h2 : ((inner (cornerSet (End S) q) t y : cornerSet (End S) q).1 : S ⟶ S)
      = ((t : End S) : S ⟶ S)† ≫ (ιA† ≫ x ≫ ιB) := rfl
  have h1 : ((τ' y).1 : S ⟶ S)
      = ((inner (cornerSet (End S) q) t y : cornerSet (End S) q).1 : S ⟶ S) :=
    congrArg (fun z : cornerSet (End S) q => ((z.1 : End S) : S ⟶ S)) (ht y)
  rw [hτ'_val, hry, h2] at h1
  show τ x = toEnd ((ιA ≫ ((t : End S) : S ⟶ S) ≫ ιB†)† ≫ x)
  calc (τ x : B ⟶ B) = ιB ≫ (ιB† ≫ (τ x : B ⟶ B) ≫ ιB) ≫ ιB† := by
        simp only [Category.assoc, isometry_comp_adj_comp hB]
        rw [show ιB ≫ ιB† = 𝟙 B from hB, Category.comp_id]
    _ = ιB ≫ (((t : End S) : S ⟶ S)† ≫ (ιA† ≫ x ≫ ιB)) ≫ ιB† := by rw [h1]
    _ = (ιA ≫ ((t : End S) : S ⟶ S) ≫ ιB†)† ≫ x := by
        simp only [adj_comp', adj_adj', Category.assoc]
        rw [show ιB ≫ ιB† = 𝟙 B from hB, Category.comp_id]

/-- A C*-category in which any two objects embed isometrically into an
object with a von Neumann endomorphism algebra is a W*-category. -/
theorem WStarCategory.of_linking
    (h : ∀ A B : C, ∃ (S : C) (ιA : A ⟶ S) (ιB : B ⟶ S),
      IsIsometry ιA ∧ IsIsometry ιB ∧ VonNeumannAlgebra (End S)) :
    WStarCategory C where
  vonNeumann A := by
    obtain ⟨S, ι, -, hι, -, hS⟩ := h A A
    exact vonNeumann_of_isometry ι hι
  selfDual A B := by
    obtain ⟨S, ιA, ιB, hA, hB, hS⟩ := h A B
    exact selfDual_of_isometries ιA ιB hA hB

end Linking

/-! ## Examples 2.3–2.5: concrete W*-categories of Hilbert spaces

A *concrete `*`-category* (`ConcreteStarCat`) has for objects Hilbert spaces
(possibly with structure) and for morphisms a norm-closed subspace of the
bounded operators, closed under composition, identities and adjoints.  Such a
category is a C*-category (`ConcreteStarCat.instCStarCategory`), and it is a
W*-category as soon as its endomorphism algebras are von Neumann subalgebras
of `B(H)` and any two objects embed isometrically in a third
(`ConcreteStarCat.wStarCategory_of`).  Hilbert spaces (**FDS 2.3**),
non-degenerate representations of a C*-algebra (**FDS 2.4**) and normal
representations of a W*-algebra (**FDS 2.5**) are instances. -/

/-- A complex Hilbert space, bundled. -/
structure HilbObj : Type (u + 1) where
  /-- the underlying space -/
  carrier : Type u
  [instNACG : NormedAddCommGroup carrier]
  [instIPS : InnerProductSpace ℂ carrier]
  [instCS : CompleteSpace carrier]

attribute [instance] HilbObj.instNACG HilbObj.instIPS HilbObj.instCS

instance : CoeSort HilbObj.{u} (Type u) := ⟨HilbObj.carrier⟩

/-- A concrete `*`-category of Hilbert spaces over the object type `O`. -/
structure ConcreteStarCat (O : Type u₂) where
  /-- the Hilbert space of an object -/
  hs : O → HilbObj.{u}
  /-- the admissible operators -/
  hom : ∀ X Y : O, Submodule ℂ (hs X →L[ℂ] hs Y)
  isClosed_hom : ∀ X Y : O, IsClosed (hom X Y : Set (hs X →L[ℂ] hs Y))
  id_mem : ∀ X : O, ContinuousLinearMap.id ℂ (hs X) ∈ hom X X
  comp_mem : ∀ {X Y Z : O} {f : hs X →L[ℂ] hs Y} {g : hs Y →L[ℂ] hs Z},
    f ∈ hom X Y → g ∈ hom Y Z → g.comp f ∈ hom X Z
  adjoint_mem : ∀ {X Y : O} {f : hs X →L[ℂ] hs Y},
    f ∈ hom X Y → ContinuousLinearMap.adjoint f ∈ hom Y X

namespace ConcreteStarCat

variable {O : Type u₂} (D : ConcreteStarCat.{u} O)

set_option linter.unusedVariables false in
/-- The objects (a type synonym, carrying the category structure). -/
def Obj (D : ConcreteStarCat.{u} O) : Type u₂ := O

/-- The morphisms: admissible bounded operators, wrapped. -/
@[ext] structure Hom (X Y : D.Obj) where
  /-- the operator -/
  val : D.hs X →L[ℂ] D.hs Y
  mem : val ∈ D.hom X Y

instance category : Category.{u} D.Obj where
  Hom X Y := D.Hom X Y
  id X := ⟨ContinuousLinearMap.id ℂ _, D.id_mem X⟩
  comp f g := ⟨g.val.comp f.val, D.comp_mem f.mem g.mem⟩
  id_comp _ := Hom.ext rfl
  comp_id _ := Hom.ext rfl
  assoc _ _ _ := Hom.ext rfl

variable {D}

@[simp] theorem val_comp {X Y Z : D.Obj} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.val (f ≫ g) = (Hom.val g).comp (Hom.val f) := rfl

@[simp] theorem val_id (X : D.Obj) : Hom.val (𝟙 X) = ContinuousLinearMap.id ℂ _ := rfl

theorem hom_ext {X Y : D.Obj} {f g : X ⟶ Y} (h : Hom.val f = Hom.val g) : f = g := Hom.ext h

section Group

variable {X Y : D.Obj}

instance : Zero (D.Hom X Y) := ⟨⟨0, zero_mem _⟩⟩
instance : Add (D.Hom X Y) := ⟨fun f g => ⟨f.val + g.val, add_mem f.mem g.mem⟩⟩
instance : Neg (D.Hom X Y) := ⟨fun f => ⟨-f.val, neg_mem f.mem⟩⟩
instance : Sub (D.Hom X Y) := ⟨fun f g => ⟨f.val - g.val, sub_mem f.mem g.mem⟩⟩
instance : SMul ℕ (D.Hom X Y) := ⟨fun n f => ⟨n • f.val, nsmul_mem f.mem n⟩⟩
instance : SMul ℤ (D.Hom X Y) := ⟨fun n f => ⟨n • f.val, zsmul_mem f.mem n⟩⟩
instance : SMul ℂ (D.Hom X Y) := ⟨fun c f => ⟨c • f.val, (D.hom X Y).smul_mem c f.mem⟩⟩

instance : AddCommGroup (D.Hom X Y) :=
  Function.Injective.addCommGroup Hom.val (fun _ _ h => Hom.ext h) rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- `Hom.val` as an additive map. -/
def valAddHom : D.Hom X Y →+ (D.hs X →L[ℂ] D.hs Y) := ⟨⟨Hom.val, rfl⟩, fun _ _ => rfl⟩

instance : Module ℂ (D.Hom X Y) :=
  Function.Injective.module ℂ valAddHom (fun _ _ h => Hom.ext h) (fun _ _ => rfl)

@[simp] theorem val_add (f g : D.Hom X Y) : (f + g).val = f.val + g.val := rfl
@[simp] theorem val_zero : (0 : D.Hom X Y).val = 0 := rfl
@[simp] theorem val_smul (c : ℂ) (f : D.Hom X Y) : (c • f).val = c • f.val := rfl

end Group

instance preadditive : Preadditive D.Obj where
  homGroup X Y := (inferInstance : AddCommGroup (D.Hom X Y))
  add_comp _ _ _ f f' g := Hom.ext (ContinuousLinearMap.comp_add g.val f.val f'.val)
  comp_add _ _ _ f g g' := Hom.ext (ContinuousLinearMap.add_comp g.val g'.val f.val)

instance linear : Linear ℂ D.Obj where
  homModule X Y := (inferInstance : Module ℂ (D.Hom X Y))
  smul_comp _ _ _ c f g := Hom.ext (ContinuousLinearMap.comp_smul g.val c f.val)
  comp_smul _ _ _ f c g := Hom.ext (ContinuousLinearMap.smul_comp c g.val f.val)

/-- The endomorphisms of an object, as a star subalgebra of `B(H)`. -/
def endSubalgebra (X : D.Obj) : StarSubalgebra ℂ (D.hs X →L[ℂ] D.hs X) where
  carrier := D.hom X X
  mul_mem' ha hb := D.comp_mem hb ha
  one_mem' := D.id_mem X
  add_mem' := add_mem
  zero_mem' := zero_mem _
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (D.hom X X).smul_mem c (D.id_mem X)
  star_mem' ha := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact D.adjoint_mem ha

theorem isClosed_endSubalgebra (X : D.Obj) :
    IsClosed ((D.endSubalgebra X : Set (D.hs X →L[ℂ] D.hs X))) :=
  D.isClosed_hom X X

instance starCategory : StarCategory D.Obj where
  adj f := ⟨ContinuousLinearMap.adjoint f.val, D.adjoint_mem f.mem⟩
  adj_id X := Hom.ext (ContinuousLinearMap.adjoint_id)
  adj_comp f g := Hom.ext (ContinuousLinearMap.adjoint_comp g.val f.val)
  adj_adj f := Hom.ext (ContinuousLinearMap.adjoint_adjoint f.val)
  adj_add f g := Hom.ext (map_add _ f.val g.val)
  adj_smul c f := Hom.ext (by
    show ContinuousLinearMap.adjoint (c • f.val) = (starRingEnd ℂ c) • ContinuousLinearMap.adjoint f.val
    exact LinearIsometryEquiv.map_smulₛₗ _ c f.val)
  exists_eq_adj_comp {X Y} a := by
    set T : D.hs X →L[ℂ] D.hs X := (ContinuousLinearMap.adjoint a.val).comp a.val with hT
    have hT0 : 0 ≤ T := (ContinuousLinearMap.nonneg_iff_isPositive T).mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self a.val)
    have hmem : T ∈ D.endSubalgebra X := D.comp_mem a.mem (D.adjoint_mem a.mem)
    have hsq : CFC.sqrt T ∈ D.endSubalgebra X :=
      VNSub.sqrt_mem (D.isClosed_endSubalgebra X) T hT0 hmem
    refine ⟨⟨CFC.sqrt T, hsq⟩, Hom.ext ?_⟩
    show T = (ContinuousLinearMap.adjoint (CFC.sqrt T)).comp (CFC.sqrt T)
    have hsa : IsSelfAdjoint (CFC.sqrt T) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)
    rw [← ContinuousLinearMap.star_eq_adjoint, hsa.star_eq]
    exact (CFC.sqrt_mul_sqrt_self T hT0).symm
  eq_zero_of_comp_adj {X Y} a h := by
    apply Hom.ext
    have h1 : (ContinuousLinearMap.adjoint a.val).comp a.val = 0 := congrArg Hom.val h
    have h2 := ContinuousLinearMap.norm_adjoint_comp_self a.val
    rw [h1, norm_zero] at h2
    have h3 : ‖a.val‖ = 0 := by nlinarith [norm_nonneg a.val]
    exact norm_eq_zero.mp h3

@[simp] theorem val_adj {X Y : D.Obj} (f : X ⟶ Y) :
    Hom.val (StarCategory.adj f) = ContinuousLinearMap.adjoint (Hom.val f) := rfl

/-- The operator norm on morphisms. -/
def homNormC (X Y : D.Obj) : Norm (X ⟶ Y) := ⟨fun f => ‖Hom.val f‖⟩

theorem homCoreC (X Y : D.Obj) : @NormedSpace.Core ℂ (X ⟶ Y) _ _ _ (homNormC X Y) := by
  letI := homNormC X Y
  exact
    { norm_nonneg := fun f => norm_nonneg (Hom.val f)
      norm_smul := fun c f => norm_smul c (Hom.val f)
      norm_triangle := fun f g => norm_add_le (Hom.val f) (Hom.val g)
      norm_eq_zero_iff := fun f => ⟨fun h => Hom.ext (norm_eq_zero.mp h),
        fun h => by subst h; exact norm_zero (E := D.hs X →L[ℂ] D.hs Y)⟩ }

instance normedStarCategory : NormedStarCategory D.Obj where
  homNorm X Y := homNormC X Y
  homCore X Y := homCoreC X Y
  norm_comp_le f g := by
    show ‖(Hom.val g).comp (Hom.val f)‖ ≤ ‖Hom.val f‖ * ‖Hom.val g‖
    rw [mul_comm]; exact ContinuousLinearMap.opNorm_comp_le _ _

theorem norm_def {X Y : D.Obj} (f : X ⟶ Y) : ‖f‖ = ‖Hom.val f‖ := rfl

instance cstarCategory : CStarCategory D.Obj where
  complete X Y := by
    have hiso : Isometry (fun f : X ⟶ Y => Hom.val f) := by
      refine Isometry.of_dist_eq fun f g => ?_
      rw [dist_eq_norm, dist_eq_norm]; rfl
    rw [completeSpace_iff_isComplete_range hiso.isUniformInducing]
    have hr : Set.range (fun f : X ⟶ Y => Hom.val f) = (D.hom X Y : Set _) := by
      ext T; constructor
      · rintro ⟨f, rfl⟩; exact f.mem
      · intro hT; exact ⟨⟨T, hT⟩, rfl⟩
    rw [hr]
    exact (D.isClosed_hom X Y).isComplete
  norm_comp_adj f := by
    show ‖(ContinuousLinearMap.adjoint (Hom.val f)).comp (Hom.val f)‖ = ‖Hom.val f‖ ^ 2
    rw [ContinuousLinearMap.norm_adjoint_comp_self, sq]

theorem isIsometry_iff {X Y : D.Obj} (f : X ⟶ Y) :
    IsIsometry f ↔ ∀ x, ‖Hom.val f x‖ = ‖x‖ := by
  rw [ContinuousLinearMap.norm_map_iff_adjoint_comp_self]
  constructor
  · intro h; exact congrArg Hom.val h
  · intro h; exact Hom.ext h

/-- `End X` is the bundled von Neumann subalgebra `endSubalgebra X`. -/
def endEquivVNSub (X : D.Obj) (hX : IsVNSubalgebra _ (D.endSubalgebra X)) :
    VNSub (D.hs X →L[ℂ] D.hs X) (D.endSubalgebra X) hX ≃⋆ₐ[ℂ] End X where
  toFun a := (⟨a.val, a.property⟩ : D.Hom X X)
  invFun f := ⟨Hom.val (show D.Hom X X from f), (show D.Hom X X from f).mem⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_star' a := Hom.ext (ContinuousLinearMap.star_eq_adjoint a.val)
  map_smul' _ _ := rfl

/-- A concrete `*`-category whose endomorphism algebras are von Neumann
subalgebras of `B(H)`, and in which any two objects embed isometrically into a
third, is a W*-category. -/
theorem wStarCategory_of (hvn : ∀ X : D.Obj, IsVNSubalgebra _ (D.endSubalgebra X))
    (hsum : ∀ X Y : D.Obj, ∃ (S : D.Obj) (ιX : X ⟶ S) (ιY : Y ⟶ S),
      IsIsometry ιX ∧ IsIsometry ιY) :
    WStarCategory D.Obj := by
  refine WStarCategory.of_linking fun A B => ?_
  obtain ⟨S, ιA, ιB, hA, hB⟩ := hsum A B
  exact ⟨S, ιA, ιB, hA, hB, vonNeumannAlgebra_of_starAlgEquiv (endEquivVNSub S (hvn S))⟩

end ConcreteStarCat

/-! ### Example 2.3: Hilbert spaces -/

/-- The concrete data of `Hilb`: all bounded operators. -/
def hilbData : ConcreteStarCat.{u} HilbObj.{u} where
  hs := id
  hom _ _ := ⊤
  isClosed_hom _ _ := by rw [Submodule.top_coe]; exact isClosed_univ
  id_mem _ := Submodule.mem_top
  comp_mem _ _ := Submodule.mem_top
  adjoint_mem _ := Submodule.mem_top

/-- **FDS 2.3**: the category `Hilb` of Hilbert spaces and bounded operators,
with `*` the adjoint and the operator norm. -/
abbrev Hilb := hilbData.{u}.Obj

/-- A morphism of `Hilb` from a bounded operator. -/
def Hilb.ofCLM {H K : Hilb.{u}} (f : hilbData.{u}.hs H →L[ℂ] hilbData.{u}.hs K) : H ⟶ K :=
  ⟨f, trivial⟩

/-- The Hilbert direct sum `H ⊕ K = WithLp 2 (H × K)` of two Hilbert spaces. -/
def HilbObj.prod (H K : HilbObj.{u}) : HilbObj.{u} := ⟨WithLp 2 (H × K)⟩

/-- The first inclusion `H → H ⊕ K`. -/
def inlCLM (H K : HilbObj.{u}) : H →L[ℂ] H.prod K :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H K)

/-- The second inclusion `K → H ⊕ K`. -/
def inrCLM (H K : HilbObj.{u}) : K →L[ℂ] H.prod K :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ H K)

@[simp] theorem inlCLM_apply (H K : HilbObj.{u}) (x : H) :
    inlCLM H K x = WithLp.toLp 2 (x, 0) := rfl

@[simp] theorem inrCLM_apply (H K : HilbObj.{u}) (y : K) :
    inrCLM H K y = WithLp.toLp 2 (0, y) := rfl

theorem norm_inlCLM (H K : HilbObj.{u}) (x : H) : ‖inlCLM H K x‖ = ‖x‖ := by
  show ‖(WithLp.toLp 2 (x, 0) : WithLp 2 (H × K))‖ = ‖x‖
  rw [WithLp.prod_norm_eq_of_L2]
  simp [Real.sqrt_sq (norm_nonneg x)]

theorem norm_inrCLM (H K : HilbObj.{u}) (y : K) : ‖inrCLM H K y‖ = ‖y‖ := by
  show ‖(WithLp.toLp 2 (0, y) : WithLp 2 (H × K))‖ = ‖y‖
  rw [WithLp.prod_norm_eq_of_L2]
  simp [Real.sqrt_sq (norm_nonneg y)]

theorem hilb_isVNSubalgebra (X : Hilb.{u}) :
    IsVNSubalgebra _ (hilbData.{u}.endSubalgebra X) where
  isClosed := hilbData.{u}.isClosed_endSubalgebra X
  dirSup_mem _ _ _ _ _ _ := trivial

/-- **FDS 2.3** (direct_sums.tex:296, Example): the category of Hilbert
spaces with bounded linear maps is a W*-category, `*` taking each operator
to its adjoint and the norm being the operator norm.  (C*: `Hilb` is a
concrete `*`-category; W*: `B(H)` is a von Neumann algebra, theses **42V**,
and `H`, `K` embed isometrically in `H ⊕ K`.) -/
instance hilb_wStarCategory : WStarCategory Hilb.{u} :=
  ConcreteStarCat.wStarCategory_of hilb_isVNSubalgebra fun H K =>
    ⟨(H : HilbObj).prod K, Hilb.ofCLM (inlCLM H K), Hilb.ofCLM (inrCLM H K),
      (ConcreteStarCat.isIsometry_iff _).mpr (norm_inlCLM H K),
      (ConcreteStarCat.isIsometry_iff _).mpr (norm_inrCLM H K)⟩

/-! ### Block-diagonal operators on `H ⊕ K` -/

section BlockDiag

variable {H K : HilbObj.{u}}

/-- The block-diagonal operator `T₁ ⊕ T₂` on `H ⊕ K`. -/
def blockDiag (T₁ : H →L[ℂ] H) (T₂ : K →L[ℂ] K) : H.prod K →L[ℂ] H.prod K :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
    ((T₁.prodMap T₂).comp (WithLp.prodContinuousLinearEquiv 2 ℂ H K).toContinuousLinearMap)

theorem blockDiag_apply (T₁ : H →L[ℂ] H) (T₂ : K →L[ℂ] K) (z : H.prod K) :
    blockDiag T₁ T₂ z
      = (WithLp.toLp 2 (T₁ (WithLp.ofLp (z : WithLp 2 (H × K))).1,
          T₂ (WithLp.ofLp (z : WithLp 2 (H × K))).2) : WithLp 2 (H × K)) := rfl

theorem blockDiag_mul (S₁ T₁ : H →L[ℂ] H) (S₂ T₂ : K →L[ℂ] K) :
    blockDiag (S₁ * T₁) (S₂ * T₂) = blockDiag S₁ S₂ * blockDiag T₁ T₂ :=
  ContinuousLinearMap.ext fun _ => rfl

theorem blockDiag_one : blockDiag (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 :=
  ContinuousLinearMap.ext fun _ => rfl

theorem blockDiag_zero : blockDiag (0 : H →L[ℂ] H) (0 : K →L[ℂ] K) = 0 :=
  ContinuousLinearMap.ext fun _ => rfl

theorem blockDiag_add (S₁ T₁ : H →L[ℂ] H) (S₂ T₂ : K →L[ℂ] K) :
    blockDiag (S₁ + T₁) (S₂ + T₂) = blockDiag S₁ S₂ + blockDiag T₁ T₂ :=
  ContinuousLinearMap.ext fun _ => rfl

theorem blockDiag_smul (c : ℂ) (T₁ : H →L[ℂ] H) (T₂ : K →L[ℂ] K) :
    blockDiag (c • T₁) (c • T₂) = c • blockDiag T₁ T₂ :=
  ContinuousLinearMap.ext fun _ => rfl

theorem adjoint_blockDiag (T₁ : H →L[ℂ] H) (T₂ : K →L[ℂ] K) :
    ContinuousLinearMap.adjoint (blockDiag T₁ T₂)
      = blockDiag (ContinuousLinearMap.adjoint T₁) (ContinuousLinearMap.adjoint T₂) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => ?_).symm
  show inner ℂ (ContinuousLinearMap.adjoint T₁ (WithLp.ofLp (x : WithLp 2 (H × K))).1)
        (WithLp.ofLp (y : WithLp 2 (H × K))).1
      + inner ℂ (ContinuousLinearMap.adjoint T₂ (WithLp.ofLp (x : WithLp 2 (H × K))).2)
        (WithLp.ofLp (y : WithLp 2 (H × K))).2
    = inner ℂ (WithLp.ofLp (x : WithLp 2 (H × K))).1 (T₁ (WithLp.ofLp (y : WithLp 2 (H × K))).1)
      + inner ℂ (WithLp.ofLp (x : WithLp 2 (H × K))).2 (T₂ (WithLp.ofLp (y : WithLp 2 (H × K))).2)
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]

theorem inlCLM_comp_eq (T₁ : H →L[ℂ] H) (T₂ : K →L[ℂ] K) :
    (inlCLM H K).comp T₁ = (blockDiag T₁ T₂).comp (inlCLM H K) :=
  ContinuousLinearMap.ext fun x => by
    show (WithLp.toLp 2 (T₁ x, 0) : WithLp 2 (H × K)) = WithLp.toLp 2 (T₁ x, T₂ 0)
    rw [map_zero]

theorem inrCLM_comp_eq (T₁ : H →L[ℂ] H) (T₂ : K →L[ℂ] K) :
    (inrCLM H K).comp T₂ = (blockDiag T₁ T₂).comp (inrCLM H K) :=
  ContinuousLinearMap.ext fun y => by
    show (WithLp.toLp 2 (0, T₂ y) : WithLp 2 (H × K)) = WithLp.toLp 2 (T₁ 0, T₂ y)
    rw [map_zero]

theorem inl_add_inr (z : WithLp 2 (H × K)) :
    z = inlCLM H K (WithLp.ofLp z).1 + inrCLM H K (WithLp.ofLp z).2 := by
  calc z = WithLp.toLp 2 (WithLp.ofLp z) := rfl
    _ = WithLp.toLp 2 (((WithLp.ofLp z).1, 0) + (0, (WithLp.ofLp z).2)) := by
        rw [Prod.mk_add_mk, add_zero, zero_add]
    _ = _ := rfl

end BlockDiag

/-! ### Examples 2.4 and 2.5: representations and intertwiners -/

section Reps

variable (𝒜 : Type u₁) [CStarAlgebra 𝒜]

/-- A unital `*`-representation of the (unital) C*-algebra `𝒜` on a Hilbert
space.  For a unital C*-algebra the non-degenerate representations of
**FDS 2.4** are exactly the unital ones. -/
structure RepObj : Type (max u₁ (u + 1)) where
  /-- the Hilbert space -/
  hs : HilbObj.{u}
  /-- the representation -/
  π : 𝒜 →⋆ₐ[ℂ] (hs →L[ℂ] hs)

variable {𝒜}

/-- The intertwiners `f π₁(a) = π₂(a) f`. -/
def intertwiners (X Y : RepObj 𝒜) : Submodule ℂ (X.hs →L[ℂ] Y.hs) where
  carrier := {f | ∀ a, f.comp (X.π a) = (Y.π a).comp f}
  add_mem' {f g} hf hg a := by
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hf a, hg a]
  zero_mem' a := by rw [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  smul_mem' c f hf a := by
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hf a]

theorem mem_intertwiners {X Y : RepObj 𝒜} {f : X.hs →L[ℂ] Y.hs} :
    f ∈ intertwiners X Y ↔ ∀ a, f.comp (X.π a) = (Y.π a).comp f := Iff.rfl

theorem isClosed_intertwiners (X Y : RepObj 𝒜) :
    IsClosed (intertwiners X Y : Set (X.hs →L[ℂ] Y.hs)) := by
  have h : (intertwiners X Y : Set (X.hs →L[ℂ] Y.hs))
      = ⋂ a, {f | f.comp (X.π a) = (Y.π a).comp f} := by
    ext f; simp [mem_intertwiners]
  rw [h]
  exact isClosed_iInter fun a =>
    isClosed_eq (continuous_id.clm_comp continuous_const) (continuous_const.clm_comp continuous_id)

theorem adjoint_mem_intertwiners {X Y : RepObj 𝒜} {f : X.hs →L[ℂ] Y.hs}
    (hf : f ∈ intertwiners X Y) : ContinuousLinearMap.adjoint f ∈ intertwiners Y X := by
  intro a
  have h := congrArg ContinuousLinearMap.adjoint (hf (star a))
  simp only [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint, ← map_star,
    star_star] at h
  exact h.symm

variable (𝒜) in
/-- The concrete data of the category of representations of `𝒜` satisfying
a predicate `P`, with the intertwiners as morphisms. -/
def repData (P : RepObj 𝒜 → Prop) : ConcreteStarCat.{u} {X : RepObj 𝒜 // P X} where
  hs X := X.1.hs
  hom X Y := intertwiners X.1 Y.1
  isClosed_hom X Y := isClosed_intertwiners X.1 Y.1
  id_mem X a := by rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  comp_mem {X Y Z f g} hf hg a := by
    rw [ContinuousLinearMap.comp_assoc, hf a, ← ContinuousLinearMap.comp_assoc, hg a,
      ContinuousLinearMap.comp_assoc]
  adjoint_mem hf := adjoint_mem_intertwiners hf

/-- The endomorphisms of a representation form a von Neumann subalgebra of
`B(H)` (the commutant of `π(𝒜)`): suprema commute with what every member
commutes with (theses **44XIII** `vna_supremum_commutes`). -/
theorem rep_isVNSubalgebra (P : RepObj 𝒜 → Prop) (X : (repData 𝒜 P).Obj) :
    IsVNSubalgebra _ ((repData 𝒜 P).endSubalgebra X) where
  isClosed := (repData 𝒜 P).isClosed_endSubalgebra X
  dirSup_mem D s hD hne hdir hlub := by
    show ∀ a, (s.1 : X.1.hs →L[ℂ] X.1.hs).comp (X.1.π a)
      = (X.1.π a).comp (s.1 : X.1.hs →L[ℂ] X.1.hs)
    intro a
    have hbdd : BddAbove D := ⟨s, hlub.1⟩
    have h := vna_supremum_commutes D ⟨hne, hdir, hbdd⟩ (X.1.π a)
      (fun d hd => (hD d hd a).symm)
    have hs : dirSup D ⟨hne, hdir, hbdd⟩ = s := (isLUB_dirSup D _).unique hlub
    rw [hs] at h
    exact h.symm

/-- The direct sum `π₁ ⊕ π₂` of two representations. -/
def prodRep (X Y : RepObj 𝒜) : 𝒜 →⋆ₐ[ℂ] (X.hs.prod Y.hs →L[ℂ] X.hs.prod Y.hs) where
  toFun a := blockDiag (X.π a) (Y.π a)
  map_one' := by rw [map_one, map_one]; exact blockDiag_one
  map_mul' a b := by rw [map_mul, map_mul]; exact blockDiag_mul _ _ _ _
  map_zero' := by rw [map_zero, map_zero]; exact blockDiag_zero
  map_add' a b := by rw [map_add, map_add]; exact blockDiag_add _ _ _ _
  commutes' c := by
    rw [AlgHomClass.commutes, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, blockDiag_smul,
      blockDiag_one]
  map_star' a := by
    rw [map_star, map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      adjoint_blockDiag]

theorem prodRep_apply (X Y : RepObj 𝒜) (a : 𝒜) :
    prodRep X Y a = blockDiag (X.π a) (Y.π a) := rfl

/-- The direct sum of two representations. -/
def RepObj.prod (X Y : RepObj 𝒜) : RepObj 𝒜 := ⟨X.hs.prod Y.hs, prodRep X Y⟩

theorem inl_mem_intertwiners (X Y : RepObj 𝒜) :
    inlCLM X.hs Y.hs ∈ intertwiners X (X.prod Y) := fun a =>
  inlCLM_comp_eq (X.π a) (Y.π a)

theorem inr_mem_intertwiners (X Y : RepObj 𝒜) :
    inrCLM X.hs Y.hs ∈ intertwiners Y (X.prod Y) := fun a =>
  inrCLM_comp_eq (X.π a) (Y.π a)

/-- A concrete category of representations closed under binary direct sums
is a W*-category. -/
theorem repData_wStarCategory (P : RepObj 𝒜 → Prop) (hP : ∀ X Y, P X → P Y → P (X.prod Y)) :
    WStarCategory (repData 𝒜 P).Obj :=
  ConcreteStarCat.wStarCategory_of (rep_isVNSubalgebra P) fun X Y =>
    ⟨(⟨X.1.prod Y.1, hP _ _ X.2 Y.2⟩ : {X : RepObj 𝒜 // P X}),
      ⟨inlCLM X.1.hs Y.1.hs, inl_mem_intertwiners X.1 Y.1⟩,
      ⟨inrCLM X.1.hs Y.1.hs, inr_mem_intertwiners X.1 Y.1⟩,
      (ConcreteStarCat.isIsometry_iff _).mpr (norm_inlCLM X.1.hs Y.1.hs),
      (ConcreteStarCat.isIsometry_iff _).mpr (norm_inrCLM X.1.hs Y.1.hs)⟩

variable (𝒜) in
/-- **FDS 2.4** (`rep_ex`, direct_sums.tex:301): the category `Rep 𝒜` of
non-degenerate (for unital `𝒜`: unital) representations of `𝒜` on Hilbert
spaces, with the intertwiners as morphisms. -/
abbrev Rep := (repData 𝒜 fun _ => True).Obj

/-- **FDS 2.4** (`rep_ex`, direct_sums.tex:301, Example): `Rep 𝒜` is a
W*-category, with the operator norm and the Hermitian adjoint. -/
instance rep_wStarCategory : WStarCategory (Rep 𝒜) :=
  repData_wStarCategory _ fun _ _ _ _ => trivial

/-- The forgetful functor `Rep ℂ ⥤ Hilb`. -/
def repForget : Rep.{0, u} ℂ ⥤ Hilb.{u} where
  obj X := X.1.hs
  map f := Hilb.ofCLM f.val
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **FDS 2.4** (`rep_ex`, direct_sums.tex:301, Example), last sentence: in
the most basic case `𝒜 = ℂ`, `Rep ℂ ≅ Hilb` — the forgetful functor is an
equivalence (every Hilbert space carries exactly one unital representation of
`ℂ`, and every operator intertwines it), and it commutes with `*`. -/
theorem rep_complex_equiv_hilb :
    repForget.{u}.IsEquivalence ∧
      ∀ {X Y : Rep.{0, u} ℂ} (f : X ⟶ Y), repForget.map f† = (repForget.map f)† := by
  refine ⟨⟨?_, ?_, ?_⟩, fun f => rfl⟩
  · refine ⟨fun {X Y} f g h => ConcreteStarCat.Hom.ext ?_⟩
    have := congrArg ConcreteStarCat.Hom.val h
    exact this
  · refine ⟨fun {X Y} g => ⟨⟨g.val, fun a => ?_⟩, rfl⟩⟩
    have hX : X.1.π a = a • (1 : X.1.hs →L[ℂ] X.1.hs) := by
      rw [← Algebra.algebraMap_eq_smul_one, ← AlgHomClass.commutes X.1.π a]; rfl
    have hY : Y.1.π a = a • (1 : Y.1.hs →L[ℂ] Y.1.hs) := by
      rw [← Algebra.algebraMap_eq_smul_one, ← AlgHomClass.commutes Y.1.π a]; rfl
    refine ContinuousLinearMap.ext fun x => ?_
    show g.val (X.1.π a x) = Y.1.π a (g.val x)
    rw [hX, hY]
    exact map_smul g.val a x
  · refine ⟨fun H => ⟨(⟨⟨hilbData.{u}.hs H,
      StarAlgHom.ofId ℂ (hilbData.{u}.hs H →L[ℂ] hilbData.{u}.hs H)⟩, trivial⟩ : Rep.{0, u} ℂ),
      ⟨Iso.refl _⟩⟩⟩

variable (N : Type u) [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]

/-- A representation is **normal** when it preserves suprema of bounded
directed sets of self-adjoint elements. -/
def RepObj.IsNormal (X : RepObj.{u, u} N) : Prop := PreservesDirSups ⇑X.π

/-- **FDS 2.5** (`nrep_ex`, direct_sums.tex:315): the category `NRep N` of
normal unital representations of a W*-algebra `N`, with intertwiners. -/
abbrev NRep := (repData N (RepObj.IsNormal N)).Obj

variable {N} [VonNeumannAlgebra N]

/-- The direct sum of two normal representations is normal: the vector
functionals at `x ⊕ 0` and `0 ⊕ y`, which separate the operators, are normal
(theses `starAlgHom_preservesDirSups_of_vectors`). -/
theorem RepObj.IsNormal.prod {X Y : RepObj.{u, u} N} (hX : X.IsNormal N) (hY : Y.IsNormal N) :
    (X.prod Y).IsNormal N := by
  refine starAlgHom_preservesDirSups_of_vectors (prodRep X Y)
    (Set.range (inlCLM X.hs Y.hs) ∪ Set.range (inrCLM X.hs Y.hs)) ?_ ?_
  · intro R hR
    refine ContinuousLinearMap.ext fun z => ?_
    rw [inl_add_inr z, map_add, hR _ (Or.inl ⟨_, rfl⟩), hR _ (Or.inr ⟨_, rfl⟩), add_zero]
    rfl
  · rintro _ (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · refine ⟨compNP (starAlgHomP X.π) (show PreservesDirSups ⇑(starAlgHomP X.π) from hX)
        (vectorNP x), fun a => ?_⟩
      rw [compNP_apply, starAlgHomP_apply, vectorNP_apply]
      show inner ℂ x (X.π a x) + inner ℂ (0 : Y.hs) (Y.π a 0) = inner ℂ x (X.π a x)
      rw [inner_zero_left, add_zero]
    · refine ⟨compNP (starAlgHomP Y.π) (show PreservesDirSups ⇑(starAlgHomP Y.π) from hY)
        (vectorNP y), fun a => ?_⟩
      rw [compNP_apply, starAlgHomP_apply, vectorNP_apply]
      show inner ℂ (0 : X.hs) (X.π a 0) + inner ℂ y (Y.π a y) = inner ℂ y (Y.π a y)
      rw [inner_zero_left, zero_add]

/-- **FDS 2.5** (`nrep_ex`, direct_sums.tex:315, Example): `NRep N` is a
W*-category.  (The print's further claim `NRep(A**) ≅ Rep A` for the
enveloping W*-algebra `A**` is not converted: no enveloping W*-algebra is
available.) -/
instance nrep_wStarCategory : WStarCategory (NRep N) :=
  repData_wStarCategory _ fun _ _ hX hY => hX.prod hY

end Reps

/-! ### Proposition 5.3: `ℓ²`-direct sums of normal representations -/

section L2Sum

open scoped ENNReal Classical

/-- The operator underlying an endomorphism of a concrete `*`-category. -/
def ConcreteStarCat.endVal {O : Type u₂} {D : ConcreteStarCat.{u} O} {X : D.Obj} (f : End X) :
    D.hs X →L[ℂ] D.hs X :=
  ConcreteStarCat.Hom.val (id f : D.Hom X X)

theorem ConcreteStarCat.endVal_sum {O : Type u₂} {D : ConcreteStarCat.{u} O} {X : D.Obj}
    {ι : Type*} (S : Finset ι) (g : ι → End X) :
    ConcreteStarCat.endVal (∑ j ∈ S, g j) = ∑ j ∈ S, ConcreteStarCat.endVal (g j) := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- An `IsLUB` in `B(H)` of endomorphisms of a concrete `*`-category whose
endomorphism algebra is a von Neumann subalgebra is an `IsLUB` in `End X`
(for its own, spectral, order). -/
theorem ConcreteStarCat.isLUB_of_isLUB_val {O : Type u₂} {D : ConcreteStarCat.{u} O}
    (X : D.Obj) (hX : IsVNSubalgebra _ (D.endSubalgebra X)) {F : Set (End X)} {s : End X}
    (h : IsLUB (ConcreteStarCat.endVal '' F) (ConcreteStarCat.endVal s)) : IsLUB F s := by
  set E := D.endEquivVNSub X hX with hE
  have hEmono : ∀ {a b}, a ≤ b → E a ≤ E b := fun h => starAlgHom_mono_general E.toStarAlgHom h
  have hEsymm : ∀ {a b}, a ≤ b → E.symm a ≤ E.symm b := fun h =>
    starAlgHom_mono_general E.symm.toStarAlgHom h
  refine ⟨fun f hf => ?_, fun u hu => ?_⟩
  · have h1 : E.symm f ≤ E.symm s := by
      rw [VNSub.le_def]
      exact h.1 ⟨f, hf, rfl⟩
    simpa using hEmono h1
  · have h1 : E.symm s ≤ E.symm u := by
      rw [VNSub.le_def]
      refine h.2 ?_
      rintro _ ⟨f, hf, rfl⟩
      have := hEsymm (hu hf)
      rw [VNSub.le_def] at this
      exact this
    simpa using hEmono h1

variable {N : Type u} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N] [VonNeumannAlgebra N]
  {I : Type u} (B : I → RepObj.{u, u} N)

/-- The Hilbert space `⊕ᵢ Hᵢ = {(ξᵢ)ᵢ | ∑ᵢ ⟨ξᵢ,ξᵢ⟩ < ∞}` of (5.3). -/
abbrev L2 := lp (fun i => (B i).hs.carrier) 2

/-- `⊕ᵢ Hᵢ` bundled. -/
abbrev l2Hilb : HilbObj.{u} := ⟨L2 B⟩

/-- The componentwise operator `(ξᵢ)ᵢ ↦ (Tᵢ ξᵢ)ᵢ` of a bounded family. -/
def lpDiag (T : ∀ i, (B i).hs →L[ℂ] (B i).hs) (C : ℝ) (hT : ∀ i, ‖T i‖ ≤ C) :
    L2 B →L[ℂ] L2 B :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun i => T i (f i), by
        refine ((lp.memℓp f).const_smul ((max C 0 : ℝ) : ℂ)).mono' fun i => ?_
        show ‖T i (f i)‖ ≤ ‖((max C 0 : ℝ) : ℂ) • f i‖
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right ((hT i).trans (le_max_left _ _)) (norm_nonneg _))⟩
      map_add' := fun f g => lp.ext (funext fun i => map_add (T i) (f i) (g i))
      map_smul' := fun c f => lp.ext (funext fun i => map_smul (T i) c (f i)) }
    (max C 0)
    (fun f => by
      have h : ∀ i, ‖T i (f i)‖ ≤ ‖(((max C 0 : ℝ) : ℂ) • f) i‖ := by
        intro i
        rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (le_max_right _ _)]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right ((hT i).trans (le_max_left _ _)) (norm_nonneg _))
      refine (lp.norm_mono (by norm_num) (y := ((max C 0 : ℝ) : ℂ) • f) h).trans_eq ?_
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)])

theorem lpDiag_apply (T : ∀ i, (B i).hs →L[ℂ] (B i).hs) (C : ℝ) (hT : ∀ i, ‖T i‖ ≤ C)
    (f : L2 B) (i : I) : lpDiag B T C hT f i = T i (f i) := rfl

theorem lpDiag_congr {T T' : ∀ i, (B i).hs →L[ℂ] (B i).hs} {C C' : ℝ}
    (hT : ∀ i, ‖T i‖ ≤ C) (hT' : ∀ i, ‖T' i‖ ≤ C') (h : T = T') :
    lpDiag B T C hT = lpDiag B T' C' hT' := by
  subst h; exact ContinuousLinearMap.ext fun f => lp.ext rfl

theorem adjoint_lpDiag (T : ∀ i, (B i).hs →L[ℂ] (B i).hs) (C : ℝ) (hT : ∀ i, ‖T i‖ ≤ C) :
    ContinuousLinearMap.adjoint (lpDiag B T C hT)
      = lpDiag B (fun i => ContinuousLinearMap.adjoint (T i)) C
        (fun i => by rw [LinearIsometryEquiv.norm_map]; exact hT i) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun f g => ?_).symm
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  rw [lpDiag_apply, lpDiag_apply, ContinuousLinearMap.adjoint_inner_left]

/-- The componentwise representation of `N` on `⊕ᵢ Hᵢ`. -/
def lpRep : N →⋆ₐ[ℂ] (L2 B →L[ℂ] L2 B) where
  toFun n := lpDiag B (fun i => (B i).π n) ‖n‖ (fun i => NonUnitalStarAlgHom.norm_apply_le _ n)
  map_one' := ContinuousLinearMap.ext fun f => lp.ext (funext fun i => by
    rw [lpDiag_apply, map_one]; rfl)
  map_mul' a b := ContinuousLinearMap.ext fun f => lp.ext (funext fun i => by
    rw [lpDiag_apply, map_mul]; rfl)
  map_zero' := ContinuousLinearMap.ext fun f => lp.ext (funext fun i => by
    rw [lpDiag_apply, map_zero]; rfl)
  map_add' a b := ContinuousLinearMap.ext fun f => lp.ext (funext fun i => by
    rw [lpDiag_apply, map_add]; rfl)
  commutes' c := ContinuousLinearMap.ext fun f => lp.ext (funext fun i => by
    rw [lpDiag_apply, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one]; rfl)
  map_star' a := by
    show lpDiag B (fun i => (B i).π (star a)) _ _
      = star (lpDiag B (fun i => (B i).π a) _ _)
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_lpDiag]
    refine lpDiag_congr B _ _ (funext fun i => ?_)
    rw [map_star, ContinuousLinearMap.star_eq_adjoint]

theorem lpRep_apply (n : N) (f : L2 B) (i : I) : lpRep B n f i = (B i).π n (f i) := rfl

/-- The inclusion `Hᵢ → ⊕ᵢ Hᵢ`. -/
def singleCLM (i : I) : (B i).hs →L[ℂ] L2 B :=
  LinearMap.mkContinuous
    { toFun := fun x => lp.single (E := fun i => (B i).hs.carrier) 2 i x
      map_add' := fun x y => lp.single_add (E := fun i => (B i).hs.carrier) 2 i x y
      map_smul' := fun c x => lp.single_smul (E := fun i => (B i).hs.carrier) 2 i c x } 1
    (fun x => by
      rw [one_mul]
      exact (lp.norm_single (E := fun i => (B i).hs.carrier) (p := 2) (by norm_num) i x).le)

theorem singleCLM_apply (i : I) (x : (B i).hs) :
    singleCLM B i x = lp.single (E := fun i => (B i).hs.carrier) 2 i x := rfl

theorem norm_singleCLM (i : I) (x : (B i).hs) : ‖singleCLM B i x‖ = ‖x‖ :=
  lp.norm_single (E := fun i => (B i).hs.carrier) (p := 2) (by norm_num) i x

theorem adjoint_singleCLM_apply (i : I) (f : L2 B) :
    ContinuousLinearMap.adjoint (singleCLM B i) f = f i := by
  refine ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, singleCLM_apply, lp.inner_single_right]

/-- The componentwise representation of normal representations is normal:
the vector functionals at the `ξ` in a summand separate operators and are
normal (theses `starAlgHom_preservesDirSups_of_vectors`). -/
theorem lpRep_normal (hB : ∀ i, (B i).IsNormal N) : PreservesDirSups ⇑(lpRep B) := by
  refine starAlgHom_preservesDirSups_of_vectors (lpRep B)
    (⋃ i, Set.range (singleCLM B i)) ?_ ?_
  · intro R hR
    refine ContinuousLinearMap.ext fun f => ?_
    have h := (lp.hasSum_single (p := 2) (by simp) f).mapL R
    have h0 : ∀ i, R (lp.single (E := fun i => (B i).hs.carrier) 2 i (f i)) = 0 := fun i =>
      hR _ (Set.mem_iUnion.mpr ⟨i, f i, rfl⟩)
    simp only [h0] at h
    exact h.unique hasSum_zero
  · intro y hy
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp hy
    refine ⟨compNP (starAlgHomP (B i).π)
      (show PreservesDirSups ⇑(starAlgHomP (B i).π) from hB i) (vectorNP x), fun n => ?_⟩
    rw [compNP_apply, starAlgHomP_apply, vectorNP_apply, singleCLM_apply,
      lp.inner_single_left, lpRep_apply, lp.single_apply_self]

variable (hB : ∀ i, (B i).IsNormal N)

/-- The `ℓ²`-direct sum `⊕ᵢ Aᵢ` of normal representations, with the
componentwise representation, as an object of `NRep N`. -/
def lpSum : NRep N := (⟨⟨l2Hilb B, lpRep B⟩, lpRep_normal B hB⟩ : {X : RepObj N // X.IsNormal N})

/-- The summands as objects of `NRep N`. -/
def lpSummand (i : I) : NRep N := (⟨B i, hB i⟩ : {X : RepObj N // X.IsNormal N})

theorem singleCLM_mem (i : I) : singleCLM B i ∈ intertwiners (B i) ⟨l2Hilb B, lpRep B⟩ := by
  intro n
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun j => ?_)
  show lp.single (E := fun i => (B i).hs.carrier) 2 i ((B i).π n x) j
    = (B j).π n (lp.single (E := fun i => (B i).hs.carrier) 2 i x j)
  by_cases h : j = i
  · subst h
    rw [lp.single_apply_self, lp.single_apply_self]
  · rw [lp.single_apply_ne 2 i _ h, lp.single_apply_ne 2 i _ h, map_zero]

/-- The inclusions `κᵢ : Aᵢ → ⊕ᵢ Aᵢ` in `NRep N`. -/
def lpIncl (i : I) : lpSummand B hB i ⟶ lpSum B hB := ⟨singleCLM B i, singleCLM_mem B i⟩

theorem lpIncl_isometry (i : I) : lpIncl B hB i ≫ (lpIncl B hB i)† = 𝟙 (lpSummand B hB i) :=
  (ConcreteStarCat.isIsometry_iff _).mpr (norm_singleCLM B i)

theorem lpIncl_orth (i j : I) (hij : i ≠ j) : lpIncl B hB j ≫ (lpIncl B hB i)† = 0 := by
  apply ConcreteStarCat.Hom.ext
  refine ContinuousLinearMap.ext fun x => ?_
  show ContinuousLinearMap.adjoint (singleCLM B i) (singleCLM B j x) = 0
  rw [adjoint_singleCLM_apply]
  exact lp.single_apply_ne (E := fun i => (B i).hs.carrier) 2 j x hij

/-- The partial sums `∑_{j∈S} κⱼκⱼ*` are the restrictions to the coordinates
in `S`. -/
theorem endVal_psum_lpIncl (S : Finset I) :
    ConcreteStarCat.endVal (psum (lpIncl B hB) S)
      = ∑ j ∈ S, (singleCLM B j).comp (ContinuousLinearMap.adjoint (singleCLM B j)) := by
  rw [psum, ConcreteStarCat.endVal_sum]
  rfl

/-- In `B(⊕ᵢ Hᵢ)` the restrictions to finite `S` increase to `1`. -/
theorem isLUB_restrict_one :
    IsLUB (Set.range fun S : Finset I =>
      ∑ j ∈ S, (singleCLM B j).comp (ContinuousLinearMap.adjoint (singleCLM B j))) 1 := by
  set P : Finset I → (L2 B →L[ℂ] L2 B) :=
    fun S => ∑ j ∈ S, (singleCLM B j).comp (ContinuousLinearMap.adjoint (singleCLM B j)) with hP
  have hPapply : ∀ S f, P S f = ∑ j ∈ S, lp.single (E := fun i => (B i).hs.carrier) 2 j (f j) := by
    intro S f
    simp only [hP, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.comp_apply,
      adjoint_singleCLM_apply, singleCLM_apply]
  have hPcoord : ∀ S f i, P S f i = if i ∈ S then f i else 0 := by
    intro S f i
    rw [hPapply, lp.coeFn_sum, Finset.sum_apply]
    by_cases hi : i ∈ S
    · rw [if_pos hi, Finset.sum_eq_single i]
      · exact lp.single_apply_self 2 i _
      · intro j _ hji; exact lp.single_apply_ne 2 j _ (Ne.symm hji)
      · intro h; exact absurd hi h
    · rw [if_neg hi]
      exact Finset.sum_eq_zero fun j hj => lp.single_apply_ne 2 j _ (fun h => hi (h ▸ hj))
  have hinner : ∀ S f, RCLike.re (inner ℂ (P S f) f) = ∑ j ∈ S, ‖f j‖ ^ 2 := by
    intro S f
    rw [hPapply, sum_inner, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [lp.inner_single_left, inner_self_eq_norm_sq]
  have hproj : ∀ S, IsStarProjection (P S) := by
    intro S
    refine ⟨ContinuousLinearMap.ext fun f => lp.ext (funext fun i => ?_), ?_⟩
    · show P S (P S f) i = P S f i
      rw [hPcoord, hPcoord]
      split_ifs <;> rfl
    · show star (P S) = P S
      rw [ContinuousLinearMap.star_eq_adjoint]
      simp only [hP, map_sum, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint]
  refine ⟨?_, fun T hT => ?_⟩
  · rintro _ ⟨S, rfl⟩
    exact sub_nonneg.mp (hproj S).one_sub.nonneg
  · -- `T ≥ P S` for all `S` gives `re ⟪T f, f⟫ ≥ ∑_{i∈S} ‖fᵢ‖² → ‖f‖²`
    have hT0 : (0 : L2 B →L[ℂ] L2 B) ≤ T := by
      have h := hT ⟨∅, rfl⟩
      simpa [hP] using h
    have hTsa : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg hT0
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
    refine ⟨hTsa.sub (IsSelfAdjoint.one _), fun f => ?_⟩
    have hS : ∀ S, (∑ j ∈ S, ‖f j‖ ^ 2) ≤ RCLike.re (inner ℂ (T f) f) := by
      intro S
      have h := (ContinuousLinearMap.le_def _ _).mp (hT ⟨S, rfl⟩)
      have h2 := h.re_inner_nonneg_left f
      rw [ContinuousLinearMap.sub_apply, inner_sub_left, map_sub, hinner] at h2
      linarith
    have hlim : Tendsto (fun S : Finset I => ∑ j ∈ S, ‖f j‖ ^ 2) atTop (𝓝 (‖f‖ ^ 2)) := by
      have h1 : HasSum (fun j => ‖f j‖ ^ 2) (‖f‖ ^ 2) := by
        have := (lp.hasSum_norm (p := 2) (by norm_num) f)
        simpa [ENNReal.toReal_ofNat, Real.rpow_two] using this
      exact h1
    have hle : ‖f‖ ^ 2 ≤ RCLike.re (inner ℂ (T f) f) :=
      le_of_tendsto hlim (Eventually.of_forall hS)
    show 0 ≤ RCLike.re (inner ℂ ((T - 1) f) f)
    rw [ContinuousLinearMap.sub_apply, inner_sub_left, map_sub, ContinuousLinearMap.one_apply,
      inner_self_eq_norm_sq]
    linarith

theorem lpIncl_isOrthogonalSum : IsOrthogonalSum (lpSummand B hB) (lpIncl B hB) := by
  refine ⟨lpIncl_isometry B hB, lpIncl_orth B hB, ?_⟩
  refine ConcreteStarCat.isLUB_of_isLUB_val (lpSum B hB) (rep_isVNSubalgebra _ _) ?_
  have himg : ConcreteStarCat.endVal '' Set.range (psum (lpIncl B hB))
      = Set.range fun S : Finset I =>
        ∑ j ∈ S, (singleCLM B j).comp (ContinuousLinearMap.adjoint (singleCLM B j)) := by
    ext T; constructor
    · rintro ⟨_, ⟨S, rfl⟩, rfl⟩
      exact ⟨S, (endVal_psum_lpIncl B hB S).symm⟩
    · rintro ⟨S, rfl⟩
      exact ⟨_, ⟨S, rfl⟩, endVal_psum_lpIncl B hB S⟩
  rw [himg]
  exact isLUB_restrict_one B

/-- **FDS 5.3** (`concrete_directsum`, direct_sums.tex:641, Proposition), first
half: in `NRep N` the `ℓ²`-direct sum `⊕ᵢ Aᵢ` with the componentwise
representation is an `I`-indexed direct sum.  The paper's proof: the
inclusions satisfy condition (c) of **FDS 5.1**. -/
theorem concrete_directsum (A : I → NRep N) :
    IsDirectSum A (lpSum (fun i => (A i).1) (fun i => (A i).2)) := by
  have h : ∃ κ : ∀ j, A j ⟶ lpSum (fun i => (A i).1) (fun i => (A i).2),
      IsOrthogonalSum A κ :=
    ⟨lpIncl (fun i => (A i).1) (fun i => (A i).2),
      lpIncl_isOrthogonalSum (fun i => (A i).1) (fun i => (A i).2)⟩
  exact ((directsum_equiv (A := A) _).out 0 2).mpr h

/-- **FDS 5.3** (`concrete_directsum`, direct_sums.tex:641, Proposition),
converse: every `I`-indexed direct sum in `NRep N` is of this form — unitarily
isomorphic to the `ℓ²`-direct sum, by the uniqueness up to unitaries
**FDS 3.5** ("the uniqueness up to unique unitaries therefore implies that
every direct sum is of this form"). -/
theorem concrete_directsum_unique (A : I → NRep N) {X : NRep N} (h : IsDirectSum A X) :
    ∃ u : lpSum (fun i => (A i).1) (fun i => (A i).2) ⟶ X, IsUnitary u := by
  obtain ⟨φ⟩ := concrete_directsum A
  obtain ⟨ψ⟩ := h
  obtain ⟨u, hu, -⟩ := unique_up_to_unitary _ φ ψ
  exact ⟨u, hu⟩

end L2Sum

end Papers.FDS
