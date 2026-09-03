/-
Theses/B/Eff/OrderUnit.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), lines
2032–2041: the two order-theoretic examples of an effectus in total form
listed in point 189aII — the category `OUSᵒᵖ` of order unit spaces
(189aII.1) and the category `OUGᵒᵖ` of order unit groups (189aII.2).

Design:
* `OrderUnitSpace X` and `OrderUnitGroup G` are *mixins* over Mathlib's
  `AddCommGroup` / `Module ℝ` / `PartialOrder`, in the style of `WStar`
  in `WStarCat.lean`: translation-invariance of `≤`, closure of the
  positive cone under non-negative scalars (spaces only), a distinguished
  `unit`, and the order-unit axiom `∀ x, ∃ n : ℕ, x ≤ n • unit`.  Being a
  mixin, the definition adds no instance of an algebraic class, so the
  products, `ULift`s and one-point spaces below carry exactly Mathlib's
  own algebraic and order structure.
* Archimedeanness is deliberately *not* part of the definition: 190IV.1
  states that the states of a single order unit space are separating
  precisely when it is archimedean, so it is a property, not an axiom.
* Positivity of the unit is an axiom for order unit *groups* and a
  *theorem* for order unit *spaces* (`ou_unit_nonneg`): in the real case
  `-u ≤ n • u` gives `0 ≤ (n+1) • u`, and one may divide by `n+1`.  In a
  group one may not — `ℤ` with positive cone `2ℕ` is a partially ordered
  abelian group in which `1` is an order unit that is not positive — so
  there the standard (Goodearl) requirement `0 ≤ unit` is listed.
* Objects are bundled (`OUS`, `OUG` : `Type (u+1)`) and morphisms are
  structures on top of Mathlib's `→ₗ[ℝ]` resp. `→+`, so that identity,
  composition and the three category laws are definitional.
* The effectus proofs are the `vNᵒᵖ` proofs of `VNExamples.lean`
  transcribed: the same concrete presentation of `CoprodPres` (final
  object = the scalars, binary coproducts = products), the same two
  mediating maps `γ(x,y) = β(x,0) + α(0,y)` and `γ(x) = α(x,0)`, and the
  same joint monicity argument on `1+1+1`.  The two places where the
  C\*-argument used the norm are replaced by the order unit: every
  element is a difference of two positive elements
  (`ou_eq_sub_of_nonneg`, `oug_eq_sub_of_nonneg`), and `c ≤ n • 1` for
  `c ≥ 0`, which is the order-unit axiom itself.
* Not separately formalized: the remaining items of 189aII (extensive
  categories with a final object, and the examples `Set`, `CRngᵒᵖ`, `CH`
  of 189aII.3), and the descriptions of the predicates, states and
  scalars of `OUSᵒᵖ` and `OUGᵒᵖ` in 190IV.
-/
import Theses.B.Eff.StatesPredicates

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits

namespace Theses.B.Eff

universe u v

noncomputable section

/-! ## Order unit spaces (189aII.1) -/

/-- **189aII.1** (`effexamplesintro`, eff.tex:2032, Examples): an **order
unit space** is an ordered real vector space with a distinguished order
unit.  Stated as a mixin over `AddCommGroup X`, `Module ℝ X` and
`PartialOrder X`: the order is translation-invariant, the positive cone is
closed under multiplication by non-negative reals, and the distinguished
element `unit` is an order unit, i.e. every element is below some natural
multiple of it.

Archimedeanness is *not* required (see 190IV.1), and positivity of `unit`
is not listed because it follows (`ou_unit_nonneg`). -/
class OrderUnitSpace (X : Type u) [AddCommGroup X] [Module ℝ X]
    [PartialOrder X] where
  /-- the order is translation-invariant -/
  protected add_le_add_left (x y : X) : x ≤ y → ∀ z, x + z ≤ y + z
  /-- the positive cone is closed under non-negative scalars -/
  protected smul_nonneg {r : ℝ} {x : X} : 0 ≤ r → 0 ≤ x → 0 ≤ r • x
  /-- the distinguished order unit -/
  unit : X
  /-- ... which is an order unit -/
  protected exists_le_smul_unit (x : X) : ∃ n : ℕ, x ≤ (n : ℝ) • unit

section OUSBasic

variable {X : Type u} [AddCommGroup X] [Module ℝ X] [PartialOrder X]
  [OrderUnitSpace X]

/-- The distinguished order unit of an order unit space, with the space as
an explicit argument. -/
abbrev ouUnit (X : Type u) [AddCommGroup X] [Module ℝ X] [PartialOrder X]
    [OrderUnitSpace X] : X := OrderUnitSpace.unit

/-- An order unit space is an ordered additive monoid; this unlocks
Mathlib's `sub_nonneg`, `add_le_add` and friends. -/
instance OrderUnitSpace.toIsOrderedAddMonoid : IsOrderedAddMonoid X where
  add_le_add_left := OrderUnitSpace.add_le_add_left

/-- Translation-invariance of the order, as a lemma. -/
theorem ou_add_le_add_right {x y : X} (h : x ≤ y) (z : X) : x + z ≤ y + z :=
  OrderUnitSpace.add_le_add_left x y h z

/-- The positive cone is closed under multiplication by a non-negative
real. -/
theorem ou_smul_nonneg {r : ℝ} {x : X} (hr : 0 ≤ r) (hx : 0 ≤ x) :
    0 ≤ r • x := OrderUnitSpace.smul_nonneg hr hx

/-- The order-unit axiom. -/
theorem ou_exists_le_smul_unit (x : X) : ∃ n : ℕ, x ≤ (n : ℝ) • ouUnit X :=
  OrderUnitSpace.exists_le_smul_unit x

/-- Multiplication by a non-negative real is monotone. -/
theorem ou_smul_le_smul {r : ℝ} (hr : 0 ≤ r) {x y : X} (h : x ≤ y) :
    r • x ≤ r • y := by
  have h0 : (0 : X) ≤ y - x := sub_nonneg.mpr h
  have h1 := ou_smul_nonneg hr h0
  rw [smul_sub] at h1
  exact sub_nonneg.mp h1

/-- **The order unit is positive.**  Applying the order-unit axiom to
`-unit` gives `0 ≤ (n+1) • unit`, and the positive cone is closed under
multiplication by `(n+1)⁻¹ ≥ 0`. -/
theorem ou_unit_nonneg : (0 : X) ≤ ouUnit X := by
  obtain ⟨n, hn⟩ := ou_exists_le_smul_unit (-(ouUnit X))
  have h1 : (0 : X) ≤ (n : ℝ) • ouUnit X + ouUnit X := by
    have h := ou_add_le_add_right hn (ouUnit X)
    simpa using h
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : ((n : ℝ) + 1) • ouUnit X = (n : ℝ) • ouUnit X + ouUnit X := by
    rw [add_smul, one_smul]
  rw [← h2] at h1
  have h3 := ou_smul_nonneg (le_of_lt (inv_pos.mpr hpos)) h1
  rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul] at h3

/-- A non-negative multiple of the order unit is positive. -/
theorem ou_smul_unit_nonneg {r : ℝ} (hr : 0 ≤ r) : (0 : X) ≤ r • ouUnit X :=
  ou_smul_nonneg hr ou_unit_nonneg

/-- The multiples of the order unit are monotone in the scalar. -/
theorem ou_smul_unit_mono {r s : ℝ} (h : r ≤ s) :
    r • ouUnit X ≤ s • ouUnit X := by
  have h1 := ou_smul_nonneg (sub_nonneg.mpr h) (ou_unit_nonneg (X := X))
  rw [sub_smul] at h1
  exact sub_nonneg.mp h1

/-- **Every element of an order unit space is a difference of two positive
elements**: from `x ≤ n • 1` one gets `x = n•1 - (n•1 - x)`.  This is the
order-unit substitute for the C\*-algebraic decomposition of an element
into four positive ones used in `linear_eq_zero_of_nonneg`. -/
theorem ou_eq_sub_of_nonneg (x : X) :
    ∃ p q : X, 0 ≤ p ∧ 0 ≤ q ∧ x = p - q := by
  obtain ⟨n, hn⟩ := ou_exists_le_smul_unit x
  refine ⟨(n : ℝ) • ouUnit X, (n : ℝ) • ouUnit X - x,
    ou_smul_unit_nonneg (Nat.cast_nonneg n), sub_nonneg.mpr hn, ?_⟩
  abel

end OUSBasic

/-! ### The basic examples of order unit spaces -/

/-- `ℝ` itself is an order unit space with order unit `1`. -/
instance Real.orderUnitSpace : OrderUnitSpace ℝ where
  add_le_add_left x y h z := by
    rw [add_comm x z, add_comm y z]; exact add_le_add_right h z
  smul_nonneg hr hx := by
    rw [smul_eq_mul]; exact mul_nonneg hr hx
  unit := 1
  exists_le_smul_unit x := ⟨⌈x⌉₊, by simpa using Nat.le_ceil x⟩

/-- An order unit space stays one after `ULift`ing (needed because the
objects of `OUS` live in a single universe, while `ℝ : Type`). -/
instance ULift.orderUnitSpace (X : Type u) [AddCommGroup X] [Module ℝ X]
    [PartialOrder X] [OrderUnitSpace X] :
    OrderUnitSpace (ULift.{v} X) where
  add_le_add_left x y h z := by
    show x.down + z.down ≤ y.down + z.down
    exact ou_add_le_add_right (show x.down ≤ y.down from h) z.down
  smul_nonneg hr hx := by
    show (0 : X) ≤ _
    exact ou_smul_nonneg hr hx
  unit := ULift.up (ouUnit X)
  exists_le_smul_unit x := by
    obtain ⟨n, hn⟩ := ou_exists_le_smul_unit x.down
    exact ⟨n, hn⟩

/-- The one-point space is an order unit space (with unit `0`); it is the
final object of `OUS`, hence the initial object of `OUSᵒᵖ`. -/
instance PUnit.orderUnitSpace : OrderUnitSpace PUnit.{u + 1} where
  add_le_add_left _ _ _ _ := le_of_eq (Subsingleton.elim _ _)
  smul_nonneg _ _ := le_of_eq (Subsingleton.elim _ _)
  unit := PUnit.unit
  exists_le_smul_unit _ := ⟨0, le_of_eq (Subsingleton.elim _ _)⟩

/-- The product of two order unit spaces, with the coordinatewise order
and the unit `(1, 1)`; this is the binary coproduct of `OUSᵒᵖ`. -/
instance Prod.orderUnitSpace (X Y : Type u) [AddCommGroup X] [Module ℝ X]
    [PartialOrder X] [OrderUnitSpace X] [AddCommGroup Y] [Module ℝ Y]
    [PartialOrder Y] [OrderUnitSpace Y] : OrderUnitSpace (X × Y) where
  add_le_add_left _ _ h z :=
    Prod.le_def.mpr ⟨ou_add_le_add_right (Prod.le_def.mp h).1 z.1,
      ou_add_le_add_right (Prod.le_def.mp h).2 z.2⟩
  smul_nonneg hr hx :=
    Prod.le_def.mpr ⟨ou_smul_nonneg hr (Prod.le_def.mp hx).1,
      ou_smul_nonneg hr (Prod.le_def.mp hx).2⟩
  unit := (ouUnit X, ouUnit Y)
  exists_le_smul_unit p := by
    obtain ⟨n, hn⟩ := ou_exists_le_smul_unit p.1
    obtain ⟨m, hm⟩ := ou_exists_le_smul_unit p.2
    refine ⟨max n m, Prod.le_def.mpr ⟨?_, ?_⟩⟩
    · exact hn.trans (ou_smul_unit_mono
        (by exact_mod_cast Nat.le_max_left n m))
    · exact hm.trans (ou_smul_unit_mono
        (by exact_mod_cast Nat.le_max_right n m))

/-! ### The category `OUS` -/

/-- A bundled order unit space: the object type of the category `OUS`. -/
structure OUS : Type (u + 1) where
  /-- the underlying type -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℝ carrier]
  [partialOrder : PartialOrder carrier]
  [orderUnitSpace : OrderUnitSpace carrier]

attribute [instance] OUS.addCommGroup OUS.module OUS.partialOrder
  OUS.orderUnitSpace

/-- An object of `OUS` may be used directly as its carrier type. -/
instance : CoeSort OUS.{u} (Type u) := ⟨OUS.carrier⟩

/-- Bundle an order unit space as an object of `OUS`. -/
abbrev OUS.of (X : Type u) [AddCommGroup X] [Module ℝ X] [PartialOrder X]
    [OrderUnitSpace X] : OUS.{u} := ⟨X⟩

/-- The order unit of a bundled order unit space. -/
abbrev OUS.unit (X : OUS.{u}) : X.carrier := ouUnit X.carrier

/-- The product of two bundled order unit spaces. -/
abbrev OUS.prod (X Y : OUS.{u}) : OUS.{u} := OUS.of (X.carrier × Y.carrier)

/-- The scalars `ℝᵤ`: the initial object of `OUS`, hence the final object
of `OUSᵒᵖ`. -/
abbrev ousScal : OUS.{u} := OUS.of (ULift.{u} ℝ)

/-- The zero space: the final object of `OUS`, hence the initial object of
`OUSᵒᵖ`. -/
abbrev ousTriv : OUS.{u} := OUS.of PUnit.{u + 1}

/-- The order unit of the scalars `ℝᵤ` is `1`. -/
@[simp] theorem ousScal_unit : ousScal.{u}.unit = (1 : ULift.{u} ℝ) := rfl

/-- The order unit of a product is the pair of the order units. -/
@[simp] theorem OUS.prod_unit (X Y : OUS.{u}) :
    (X.prod Y).unit = (X.unit, Y.unit) := rfl

/-- A **positive unit-preserving linear map** between order unit spaces:
the morphisms of `OUS` (and, read backwards, of `OUSᵒᵖ`). -/
structure OUSMap (X Y : OUS.{u}) : Type u where
  /-- the underlying real-linear map -/
  toLinearMap : X.carrier →ₗ[ℝ] Y.carrier
  /-- ... which is positive -/
  map_nonneg' : ∀ x : X.carrier, 0 ≤ x → 0 ≤ toLinearMap x
  /-- ... and unit-preserving -/
  map_unit' : toLinearMap X.unit = Y.unit

/-- Extensionality: a morphism of `OUS` is determined by its underlying
function. -/
theorem OUSMap.ext' {X Y : OUS.{u}} {f g : OUSMap X Y}
    (h : ∀ x, f.toLinearMap x = g.toLinearMap x) : f = g := by
  obtain ⟨f, hf₁, hf₂⟩ := f
  obtain ⟨g, hg₁, hg₂⟩ := g
  have hfg : f = g := LinearMap.ext h
  subst hfg
  rfl

/-- A positive linear map is monotone (apply positivity to `y - x`). -/
theorem OUSMap.mono {X Y : OUS.{u}} (f : OUSMap X Y) {x y : X.carrier}
    (h : x ≤ y) : f.toLinearMap x ≤ f.toLinearMap y := by
  have h1 := f.map_nonneg' (y - x) (sub_nonneg.mpr h)
  rw [map_sub] at h1
  exact sub_nonneg.mp h1

/-- The identity morphism of `OUS`. -/
def OUSMap.id (X : OUS.{u}) : OUSMap X X where
  toLinearMap := LinearMap.id
  map_nonneg' _ h := h
  map_unit' := rfl

/-- Composition in `OUS` (diagrammatic order: first `f`, then `g`). -/
def OUSMap.comp {X Y Z : OUS.{u}} (f : OUSMap X Y) (g : OUSMap Y Z) :
    OUSMap X Z where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_nonneg' x h := g.map_nonneg' _ (f.map_nonneg' x h)
  map_unit' := by
    show g.toLinearMap (f.toLinearMap X.unit) = Z.unit
    rw [f.map_unit', g.map_unit']

/-- **The category `OUS`** of order unit spaces with positive
unit-preserving linear maps.  All three category laws hold definitionally,
since composition is composition of the underlying linear maps. -/
instance : Category.{u} OUS.{u} where
  Hom X Y := OUSMap X Y
  id X := OUSMap.id X
  comp f g := OUSMap.comp f g
  id_comp _ := OUSMap.ext' fun _ => rfl
  comp_id _ := OUSMap.ext' fun _ => rfl
  assoc _ _ _ := OUSMap.ext' fun _ => rfl

/-- Extensionality in `OUS`, for morphisms written with `⟶`. -/
theorem ous_hom_ext {X Y : OUS.{u}} {f g : X ⟶ Y}
    (h : ∀ x, f.toLinearMap x = g.toLinearMap x) : f = g := OUSMap.ext' h

/-- Composition in `OUS` is composition of the underlying functions. -/
theorem ous_comp_apply {X Y Z : OUS.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X.carrier) :
    (f ≫ g).toLinearMap x = g.toLinearMap (f.toLinearMap x) := rfl

/-- The identity of `OUS` is the identity function. -/
theorem ous_id_apply {X : OUS.{u}} (x : X.carrier) :
    (𝟙 X : X ⟶ X).toLinearMap x = x := rfl

/-- Equal morphisms of `OUS` agree pointwise. -/
theorem ous_congr {X Y : OUS.{u}} {f g : X ⟶ Y} (h : f = g) (x : X.carrier) :
    f.toLinearMap x = g.toLinearMap x := by rw [h]

/-- Extensionality in `OUSᵒᵖ`. -/
theorem ousop_hom_ext {X Y : OUS.{u}ᵒᵖ} {f g : X ⟶ Y}
    (h : ∀ x, f.unop.toLinearMap x = g.unop.toLinearMap x) : f = g :=
  Quiver.Hom.unop_inj (ous_hom_ext h)

/-- Composition in `OUSᵒᵖ` applies the two underlying functions in the
opposite order. -/
theorem ousop_comp_apply {X Y Z : OUS.{u}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Z.unop.carrier) :
    (f ≫ g).unop.toLinearMap x
      = f.unop.toLinearMap (g.unop.toLinearMap x) :=
  ous_comp_apply g.unop f.unop x

/-- Equal morphisms of `OUSᵒᵖ` agree pointwise. -/
theorem ousop_congr {X Y : OUS.{u}ᵒᵖ} {f g : X ⟶ Y} (h : f = g)
    (x : Y.unop.carrier) : f.unop.toLinearMap x = g.unop.toLinearMap x := by
  rw [h]

/-- Postcomposition with a fixed map, pointwise. -/
theorem ousop_comp_congr {Z P X : OUS.{u}ᵒᵖ} {F : P ⟶ X} {a b : Z ⟶ P}
    (h : a ≫ F = b ≫ F) (x : X.unop.carrier) :
    a.unop.toLinearMap (F.unop.toLinearMap x)
      = b.unop.toLinearMap (F.unop.toLinearMap x) :=
  ((ousop_comp_apply a F x).symm.trans (ousop_congr h x)).trans
    (ousop_comp_apply b F x)

/-! ### The concrete final, initial and product objects of `OUS` -/

/-- The unique morphism `ℝᵤ ⟶ X` of `OUS`, namely `r ↦ r · 1`. -/
def ousUnitMap (X : OUS.{u}) : ousScal.{u} ⟶ X where
  toLinearMap :=
    { toFun := fun r => r.down • X.unit
      map_add' := fun a b => by
        show (a.down + b.down) • X.unit = a.down • X.unit + b.down • X.unit
        exact add_smul _ _ _
      map_smul' := fun r a => by
        show (r * a.down) • X.unit = r • (a.down • X.unit)
        exact mul_smul _ _ _ }
  map_nonneg' r hr := ou_smul_unit_nonneg hr
  map_unit' := one_smul _ _

/-- The defining equation of `ousUnitMap`. -/
@[simp] theorem ousUnitMap_apply (X : OUS.{u}) (r : ULift.{u} ℝ) :
    (ousUnitMap X).toLinearMap r = r.down • X.unit := rfl

/-- The unique morphism `X ⟶ 0` of `OUS`. -/
def ousTrivMap (X : OUS.{u}) : X ⟶ ousTriv.{u} where
  toLinearMap := 0
  map_nonneg' _ _ := le_of_eq (Subsingleton.elim _ _)
  map_unit' := Subsingleton.elim _ _

/-- The first projection `X × Y ⟶ X`, a coprojection of `OUSᵒᵖ`. -/
def ousFst (X Y : OUS.{u}) : X.prod Y ⟶ X where
  toLinearMap := LinearMap.fst ℝ X.carrier Y.carrier
  map_nonneg' _ h := (Prod.le_def.mp h).1
  map_unit' := rfl

/-- The second projection `X × Y ⟶ Y`. -/
def ousSnd (X Y : OUS.{u}) : X.prod Y ⟶ Y where
  toLinearMap := LinearMap.snd ℝ X.carrier Y.carrier
  map_nonneg' _ h := (Prod.le_def.mp h).2
  map_unit' := rfl

/-- The pairing `⟨f, g⟩ : Z ⟶ X × Y`, the cotupling of `OUSᵒᵖ`. -/
def ousPair {Z X Y : OUS.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) : Z ⟶ X.prod Y where
  toLinearMap := LinearMap.prod f.toLinearMap g.toLinearMap
  map_nonneg' z h := Prod.le_def.mpr ⟨f.map_nonneg' z h, g.map_nonneg' z h⟩
  map_unit' := Prod.ext f.map_unit' g.map_unit'

/-- The defining equation of `ousPair`. -/
@[simp] theorem ousPair_apply {Z X Y : OUS.{u}} (f : Z ⟶ X) (g : Z ⟶ Y)
    (z : Z.carrier) :
    (ousPair f g).toLinearMap z
      = (f.toLinearMap z, g.toLinearMap z) := rfl

/-- The product `f × g : X × Y ⟶ X' × Y'` of two morphisms. -/
def ousProdMap {X X' Y Y' : OUS.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    X.prod Y ⟶ X'.prod Y' where
  toLinearMap := LinearMap.prodMap f.toLinearMap g.toLinearMap
  map_nonneg' _ h :=
    Prod.le_def.mpr ⟨f.map_nonneg' _ (Prod.le_def.mp h).1,
      g.map_nonneg' _ (Prod.le_def.mp h).2⟩
  map_unit' := Prod.ext f.map_unit' g.map_unit'

/-- The defining equation of `ousProdMap`. -/
@[simp] theorem ousProdMap_apply {X X' Y Y' : OUS.{u}} (f : X ⟶ X')
    (g : Y ⟶ Y') (p : X.carrier × Y.carrier) :
    (ousProdMap f g).toLinearMap p
      = (f.toLinearMap p.1, g.toLinearMap p.2) := rfl

/-- Any morphism `ℝᵤ ⟶ X` is `r ↦ r · 1` (linearity and unitality). -/
theorem ousUnitMap_unique {X : OUS.{u}} (f : ousScal.{u} ⟶ X) :
    f = ousUnitMap X := by
  refine ous_hom_ext fun r => ?_
  have hr : r = r.down • (1 : ULift.{u} ℝ) := by
    apply ULift.down_injective
    simp
  rw [ousUnitMap_apply]
  conv_lhs => rw [hr]
  rw [map_smul]
  exact congrArg (fun z => r.down • z) f.map_unit'

/-- **`ℝᵤ` is the initial object of `OUS`**, hence the final object of
`OUSᵒᵖ`. -/
def ousScalIsInitial : IsInitial ousScal.{u} :=
  IsInitial.ofUniqueHom (fun X => ousUnitMap X) (fun _ f => ousUnitMap_unique f)

/-- **The zero space is the final object of `OUS`**, hence the initial
object of `OUSᵒᵖ`. -/
def ousTrivIsTerminal : IsTerminal ousTriv.{u} :=
  IsTerminal.ofUniqueHom (fun X => ousTrivMap X)
    (fun _ _ => ous_hom_ext fun _ =>
      Subsingleton.elim (α := PUnit.{u + 1}) _ _)

/-- The concrete presentation of `OUSᵒᵖ`: the final object is the scalars
`ℝᵤ` (initial in `OUS`), the binary coproducts are the products `X × Y`
with the coordinatewise order and unit `(1,1)`. -/
noncomputable def ousPres : CoprodPres (OUS.{u}ᵒᵖ) where
  T := Opposite.op ousScal.{u}
  hT := IsInitial.op (OUS.{u}) ousScalIsInitial
  P X Y := Opposite.op (X.unop.prod Y.unop)
  pinl X Y := Quiver.Hom.op (ousFst X.unop Y.unop)
  pinr X Y := Quiver.Hom.op (ousSnd X.unop Y.unop)
  hP X Y := BinaryCofan.IsColimit.mk _
    (fun {_} u v => Quiver.Hom.op (ousPair u.unop v.unop))
    (fun {_} _ _ => ousop_hom_ext fun x => ousop_comp_apply _ _ x)
    (fun {_} _ _ => ousop_hom_ext fun x => ousop_comp_apply _ _ x)
    (fun {_} _ _ m h₁ h₂ => ousop_hom_ext fun x => by
      refine Prod.ext ?_ ?_
      · exact (ousop_comp_apply _ m x).symm.trans (ousop_congr h₁ x)
      · exact (ousop_comp_apply _ m x).symm.trans (ousop_congr h₂ x))

/-- The unique morphism into the final object of `OUSᵒᵖ` is `r ↦ r · 1`. -/
theorem ousPres_from_apply (Y : OUS.{u}ᵒᵖ) (r : ULift.{u} ℝ) :
    (ousPres.hT.from Y).unop.toLinearMap r = r.down • Y.unop.unit := by
  have h : ousPres.hT.from Y = Quiver.Hom.op (ousUnitMap Y.unop) :=
    ousPres.hT.hom_ext _ _
  rw [h]
  rfl

/-- The coproduct of two morphisms of `OUSᵒᵖ` acts coordinatewise. -/
theorem ousPres_pmap_apply {X X' Y Y' : OUS.{u}ᵒᵖ} (f : X ⟶ X') (g : Y ⟶ Y')
    (p : (ousPres.P X' Y').unop.carrier) :
    (ousPres.pmap f g).unop.toLinearMap p
      = (f.unop.toLinearMap p.1, g.unop.toLinearMap p.2) := by
  refine Prod.ext ?_ ?_
  · exact ousop_comp_apply f _ p
  · exact ousop_comp_apply g _ p

/-! ### The left pushout square of 180I in `OUS` -/

section OUSMed1

variable {X Y Z : OUS.{u}}

/-- The mediating morphism `γ(x, y) = β(x, 0) + α(0, y)` of the first
pushout square of 180I. -/
def ousMed1 (α : ousScal.{u}.prod Y ⟶ Z) (β : X.prod ousScal.{u} ⟶ Z)
    (hc : ∀ z w : ULift.{u} ℝ,
      α.toLinearMap (z, w.down • Y.unit)
        = β.toLinearMap (z.down • X.unit, w)) :
    X.prod Y ⟶ Z where
  toLinearMap :=
    β.toLinearMap.comp ((LinearMap.inl ℝ X.carrier (ULift.{u} ℝ)).comp
        (LinearMap.fst ℝ X.carrier Y.carrier))
      + α.toLinearMap.comp ((LinearMap.inr ℝ (ULift.{u} ℝ) Y.carrier).comp
        (LinearMap.snd ℝ X.carrier Y.carrier))
  map_nonneg' p hp := by
    show (0 : Z.carrier)
      ≤ β.toLinearMap (p.1, 0) + α.toLinearMap (0, p.2)
    have h1 : (0 : X.carrier × ULift.{u} ℝ) ≤ (p.1, 0) :=
      Prod.le_def.mpr ⟨(Prod.le_def.mp hp).1, le_refl _⟩
    have h2 : (0 : ULift.{u} ℝ × Y.carrier) ≤ (0, p.2) :=
      Prod.le_def.mpr ⟨le_refl _, (Prod.le_def.mp hp).2⟩
    exact add_nonneg (β.map_nonneg' _ h1) (α.map_nonneg' _ h2)
  map_unit' := by
    show β.toLinearMap (X.unit, (0 : ULift.{u} ℝ))
      + α.toLinearMap ((0 : ULift.{u} ℝ), Y.unit) = Z.unit
    have h1 : α.toLinearMap ((1 : ULift.{u} ℝ), (0 : Y.carrier))
        = β.toLinearMap (X.unit, (0 : ULift.{u} ℝ)) := by
      have h := hc 1 0
      simpa using h
    have h2 : ((1 : ULift.{u} ℝ), (0 : Y.carrier))
        + ((0 : ULift.{u} ℝ), Y.unit) = ((1 : ULift.{u} ℝ), Y.unit) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [← h1, ← map_add, h2]
    exact α.map_unit'

/-- The defining equation of `ousMed1`. -/
@[simp] theorem ousMed1_apply (α : ousScal.{u}.prod Y ⟶ Z)
    (β : X.prod ousScal.{u} ⟶ Z) (hc) (p : X.carrier × Y.carrier) :
    (ousMed1 α β hc).toLinearMap p
      = β.toLinearMap (p.1, 0) + α.toLinearMap (0, p.2) := rfl

variable (α : ousScal.{u}.prod Y ⟶ Z) (β : X.prod ousScal.{u} ⟶ Z)
  (hc : ∀ z w : ULift.{u} ℝ,
    α.toLinearMap (z, w.down • Y.unit)
      = β.toLinearMap (z.down • X.unit, w))

/-- `γ ∘ (u × id) = α`. -/
theorem ousMed1_fac_left (y : ULift.{u} ℝ × Y.carrier) :
    (ousMed1 α β hc).toLinearMap (y.1.down • X.unit, y.2)
      = α.toLinearMap y := by
  show β.toLinearMap (y.1.down • X.unit, 0) + α.toLinearMap (0, y.2)
    = α.toLinearMap y
  have h1 : α.toLinearMap (y.1, (0 : Y.carrier))
      = β.toLinearMap (y.1.down • X.unit, (0 : ULift.{u} ℝ)) := by
    have h := hc y.1 0
    simpa using h
  have h3 : ((y.1, (0 : Y.carrier)) : ULift.{u} ℝ × Y.carrier)
      + (((0 : ULift.{u} ℝ), y.2) : ULift.{u} ℝ × Y.carrier) = y := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [← h1, ← map_add, h3]

/-- `γ ∘ (id × u) = β`. -/
theorem ousMed1_fac_right (y : X.carrier × ULift.{u} ℝ) :
    (ousMed1 α β hc).toLinearMap (y.1, y.2.down • Y.unit)
      = β.toLinearMap y := by
  show β.toLinearMap (y.1, 0) + α.toLinearMap (0, y.2.down • Y.unit)
    = β.toLinearMap y
  have h1 : α.toLinearMap ((0 : ULift.{u} ℝ), y.2.down • Y.unit)
      = β.toLinearMap ((0 : X.carrier), y.2) := by
    have h := hc 0 y.2
    simpa using h
  have h3 : ((y.1, (0 : ULift.{u} ℝ)) : X.carrier × ULift.{u} ℝ)
      + (((0 : X.carrier), y.2) : X.carrier × ULift.{u} ℝ) = y := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [h1, ← map_add, h3]

/-- `γ` is the *only* morphism with those two properties. -/
theorem ousMed1_uniq (m : X.prod Y ⟶ Z)
    (h₁ : ∀ y : ULift.{u} ℝ × Y.carrier,
      m.toLinearMap (y.1.down • X.unit, y.2) = α.toLinearMap y)
    (h₂ : ∀ y : X.carrier × ULift.{u} ℝ,
      m.toLinearMap (y.1, y.2.down • Y.unit) = β.toLinearMap y) :
    m = ousMed1 α β hc := by
  refine ous_hom_ext fun p => ?_
  show m.toLinearMap p = β.toLinearMap (p.1, 0) + α.toLinearMap (0, p.2)
  have e₁ : m.toLinearMap ((p.1, (0 : Y.carrier)) : X.carrier × Y.carrier)
      = β.toLinearMap (p.1, 0) := by
    have h := h₂ ((p.1, (0 : ULift.{u} ℝ)) : X.carrier × ULift.{u} ℝ)
    simpa using h
  have e₂ : m.toLinearMap (((0 : X.carrier), p.2) : X.carrier × Y.carrier)
      = α.toLinearMap (0, p.2) := by
    have h := h₁ (((0 : ULift.{u} ℝ), p.2) : ULift.{u} ℝ × Y.carrier)
    simpa using h
  have h3 : ((p.1, (0 : Y.carrier)) : X.carrier × Y.carrier)
      + (((0 : X.carrier), p.2) : X.carrier × Y.carrier) = p := by
    refine Prod.ext ?_ ?_ <;> simp
  have h4 : m.toLinearMap p
      = m.toLinearMap ((p.1, (0 : Y.carrier)) : X.carrier × Y.carrier)
        + m.toLinearMap (((0 : X.carrier), p.2) : X.carrier × Y.carrier) := by
    rw [← map_add, h3]
  rw [h4, e₁, e₂]

end OUSMed1

/-- `id × u : ℝ × ℝ ⟶ ℝ × Y`. -/
def ousSq1f (Y : OUS.{u}) : ousScal.{u}.prod ousScal.{u} ⟶ ousScal.{u}.prod Y :=
  ousProdMap (𝟙 ousScal.{u}) (ousUnitMap Y)

/-- `u × id : ℝ × ℝ ⟶ X × ℝ`. -/
def ousSq1g (X : OUS.{u}) : ousScal.{u}.prod ousScal.{u} ⟶ X.prod ousScal.{u} :=
  ousProdMap (ousUnitMap X) (𝟙 ousScal.{u})

/-- `u × id : ℝ × Y ⟶ X × Y`. -/
def ousSq1h (X Y : OUS.{u}) : ousScal.{u}.prod Y ⟶ X.prod Y :=
  ousProdMap (ousUnitMap X) (𝟙 Y)

/-- `id × u : X × ℝ ⟶ X × Y`. -/
def ousSq1i (X Y : OUS.{u}) : X.prod ousScal.{u} ⟶ X.prod Y :=
  ousProdMap (𝟙 X) (ousUnitMap Y)

/-- The defining equation of `ousSq1f`. -/
@[simp] theorem ousSq1f_apply (Y : OUS.{u}) (p : ULift.{u} ℝ × ULift.{u} ℝ) :
    (ousSq1f Y).toLinearMap p = (p.1, p.2.down • Y.unit) := rfl

/-- The defining equation of `ousSq1g`. -/
@[simp] theorem ousSq1g_apply (X : OUS.{u}) (p : ULift.{u} ℝ × ULift.{u} ℝ) :
    (ousSq1g X).toLinearMap p = (p.1.down • X.unit, p.2) := rfl

/-- The defining equation of `ousSq1h`. -/
@[simp] theorem ousSq1h_apply (X Y : OUS.{u}) (p : ULift.{u} ℝ × Y.carrier) :
    (ousSq1h X Y).toLinearMap p = (p.1.down • X.unit, p.2) := rfl

/-- The defining equation of `ousSq1i`. -/
@[simp] theorem ousSq1i_apply (X Y : OUS.{u}) (p : X.carrier × ULift.{u} ℝ) :
    (ousSq1i X Y).toLinearMap p = (p.1, p.2.down • Y.unit) := rfl

/-- **The left pullback square of 180I in `OUSᵒᵖ`**: the square
```
  ℝ × ℝ --id×u--> ℝ × Y
    |u×id           |u×id
    v               v
  X × ℝ --id×u--> X × Y
```
is a pushout in `OUS` — a positive unit-preserving map out of `X × Y` is
precisely a pair of such maps out of `ℝ × Y` and `X × ℝ` agreeing on
`ℝ × ℝ`, glued by `γ(x, y) = β(x, 0) + α(0, y)`. -/
theorem ous_isPushout1 (X Y : OUS.{u}) :
    IsPushout (ousSq1f Y) (ousSq1g X) (ousSq1h X Y) (ousSq1i X Y) := by
  have w : ousSq1f Y ≫ ousSq1h X Y = ousSq1g X ≫ ousSq1i X Y :=
    ous_hom_ext fun p =>
      (ous_comp_apply _ _ p).trans (ous_comp_apply _ _ p).symm
  have hcond : ∀ s : PushoutCocone (ousSq1f Y) (ousSq1g X),
      ∀ z w : ULift.{u} ℝ,
      s.inl.toLinearMap (z, w.down • Y.unit)
        = s.inr.toLinearMap (z.down • X.unit, w) := by
    intro s z w
    exact ((ous_comp_apply (ousSq1f Y) s.inl (z, w)).symm.trans
      (ous_congr s.condition (z, w))).trans
      (ous_comp_apply (ousSq1g X) s.inr (z, w))
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s => ousMed1 s.inl s.inr (hcond s)) ?_ ?_ ?_)
  · intro s
    exact ous_hom_ext fun y =>
      (ous_comp_apply (ousSq1h X Y) _ y).trans
        (ousMed1_fac_left _ _ (hcond s) y)
  · intro s
    exact ous_hom_ext fun y =>
      (ous_comp_apply (ousSq1i X Y) _ y).trans
        (ousMed1_fac_right _ _ (hcond s) y)
  · intro s m h₁ h₂
    refine ousMed1_uniq _ _ (hcond s) m (fun y => ?_) (fun y => ?_)
    · exact (ous_comp_apply (ousSq1h X Y) m y).symm.trans (ous_congr h₁ y)
    · exact (ous_comp_apply (ousSq1i X Y) m y).symm.trans (ous_congr h₂ y)

/-! ### The right pushout square of 180I in `OUS` -/

/-- **A positive map on a product killing `(0, 1)` kills `0 × Y`.**  For
`0 ≤ c` the order-unit axiom gives `(0, c) ≤ n · (0, 1)`, so `α(0, c)` is
squeezed between `0` and `0`; a general `c` is a difference of two
positive elements (`ou_eq_sub_of_nonneg`).  This is the order-unit
replacement of the norm estimate `c ≤ ‖c‖ · 1` used for von Neumann
algebras. -/
theorem ous_prod_apply_eq_zero {X Y Z : OUS.{u}} (α : X.prod Y ⟶ Z)
    (h1 : α.toLinearMap ((0 : X.carrier), Y.unit) = 0) (b : Y.carrier) :
    α.toLinearMap ((0 : X.carrier), b) = 0 := by
  have hnn : ∀ c : Y.carrier, 0 ≤ c →
      α.toLinearMap ((0 : X.carrier), c) = 0 := by
    intro c hc
    obtain ⟨n, hn⟩ := ou_exists_le_smul_unit c
    have hle : (((0 : X.carrier), c) : X.carrier × Y.carrier)
        ≤ ((0 : X.carrier), (n : ℝ) • Y.unit) :=
      Prod.le_def.mpr ⟨le_refl _, hn⟩
    have h0 : (0 : X.carrier × Y.carrier)
        ≤ (((0 : X.carrier), c) : X.carrier × Y.carrier) :=
      Prod.le_def.mpr ⟨le_refl _, hc⟩
    have hsm : (((0 : X.carrier), (n : ℝ) • Y.unit) : X.carrier × Y.carrier)
        = (n : ℝ) • (((0 : X.carrier), Y.unit) : X.carrier × Y.carrier) := by
      refine Prod.ext ?_ ?_ <;> simp
    have hz : α.toLinearMap ((0 : X.carrier), (n : ℝ) • Y.unit) = 0 := by
      rw [hsm, map_smul, h1, smul_zero]
    refine le_antisymm ?_ ?_
    · rw [← hz]; exact α.mono hle
    · have hp := α.mono h0
      rwa [map_zero] at hp
  obtain ⟨p, q, hp, hq, hb⟩ := ou_eq_sub_of_nonneg b
  have hsplit : (((0 : X.carrier), b) : X.carrier × Y.carrier)
      = (((0 : X.carrier), p) : X.carrier × Y.carrier)
        - (((0 : X.carrier), q) : X.carrier × Y.carrier) := by
    rw [hb]
    refine Prod.ext ?_ ?_ <;> simp
  rw [hsplit, map_sub, hnn p hp, hnn q hq, sub_zero]

section OUSMed2

variable {X Y Z : OUS.{u}}

/-- The mediating morphism `γ(x) = α(x, 0)` of the second pushout
square. -/
def ousMed2 (α : X.prod Y ⟶ Z) (β : ousScal.{u} ⟶ Z)
    (hc : ∀ z w : ULift.{u} ℝ,
      α.toLinearMap (z.down • X.unit, w.down • Y.unit)
        = β.toLinearMap z) : X ⟶ Z where
  toLinearMap := α.toLinearMap.comp (LinearMap.inl ℝ X.carrier Y.carrier)
  map_nonneg' x hx := α.map_nonneg' _ (Prod.le_def.mpr ⟨hx, le_refl _⟩)
  map_unit' := by
    show α.toLinearMap (X.unit, (0 : Y.carrier)) = Z.unit
    have h01 : α.toLinearMap ((0 : X.carrier), Y.unit) = 0 := by
      have h := hc 0 1
      rw [show β.toLinearMap (0 : ULift.{u} ℝ) = 0 from map_zero _] at h
      simpa using h
    have h3 : ((X.unit, (0 : Y.carrier)) : X.carrier × Y.carrier)
        + (((0 : X.carrier), Y.unit) : X.carrier × Y.carrier)
        = (X.prod Y).unit := by
      refine Prod.ext ?_ ?_ <;> simp
    have h4 : α.toLinearMap (X.unit, (0 : Y.carrier))
        + α.toLinearMap ((0 : X.carrier), Y.unit) = Z.unit := by
      rw [← map_add, h3]
      exact α.map_unit'
    rwa [h01, add_zero] at h4

/-- The defining equation of `ousMed2`. -/
@[simp] theorem ousMed2_apply (α : X.prod Y ⟶ Z) (β : ousScal.{u} ⟶ Z) (hc)
    (x : X.carrier) :
    (ousMed2 α β hc).toLinearMap x = α.toLinearMap (x, 0) := rfl

variable (α : X.prod Y ⟶ Z) (β : ousScal.{u} ⟶ Z)
  (hc : ∀ z w : ULift.{u} ℝ,
    α.toLinearMap (z.down • X.unit, w.down • Y.unit) = β.toLinearMap z)

/-- `γ ∘ π₁ = α`. -/
theorem ousMed2_fac_left (p : X.carrier × Y.carrier) :
    (ousMed2 α β hc).toLinearMap p.1 = α.toLinearMap p := by
  show α.toLinearMap (p.1, 0) = α.toLinearMap p
  have h01 : α.toLinearMap ((0 : X.carrier), Y.unit) = 0 := by
    have h := hc 0 1
    rw [show β.toLinearMap (0 : ULift.{u} ℝ) = 0 from map_zero _] at h
    simpa using h
  have h3 : ((p.1, (0 : Y.carrier)) : X.carrier × Y.carrier)
      + (((0 : X.carrier), p.2) : X.carrier × Y.carrier) = p := by
    refine Prod.ext ?_ ?_ <;> simp
  have h4 : α.toLinearMap p
      = α.toLinearMap (p.1, (0 : Y.carrier))
        + α.toLinearMap ((0 : X.carrier), p.2) := by
    rw [← map_add, h3]
  rw [h4, ous_prod_apply_eq_zero α h01 p.2, add_zero]

/-- `γ ∘ u = β`. -/
theorem ousMed2_fac_right (z : ULift.{u} ℝ) :
    (ousMed2 α β hc).toLinearMap (z.down • X.unit) = β.toLinearMap z := by
  show α.toLinearMap (z.down • X.unit, 0) = β.toLinearMap z
  have h := hc z 0
  simpa using h

/-- `γ` is the only morphism with that property. -/
theorem ousMed2_uniq (m : X ⟶ Z)
    (h₁ : ∀ p : X.carrier × Y.carrier,
      m.toLinearMap p.1 = α.toLinearMap p) : m = ousMed2 α β hc := by
  refine ous_hom_ext fun x => ?_
  show m.toLinearMap x = α.toLinearMap (x, 0)
  exact h₁ ((x, (0 : Y.carrier)) : X.carrier × Y.carrier)

end OUSMed2

/-- `u × u : ℝ × ℝ ⟶ X × Y`. -/
def ousSq2f (X Y : OUS.{u}) : ousScal.{u}.prod ousScal.{u} ⟶ X.prod Y :=
  ousProdMap (ousUnitMap X) (ousUnitMap Y)

/-- `π₁ : ℝ × ℝ ⟶ ℝ`. -/
def ousSq2g : ousScal.{u}.prod ousScal.{u} ⟶ ousScal.{u} :=
  ousFst ousScal.{u} ousScal.{u}

/-- `π₁ : X × Y ⟶ X`. -/
def ousSq2h (X Y : OUS.{u}) : X.prod Y ⟶ X := ousFst X Y

/-- `u : ℝ ⟶ X`. -/
def ousSq2i (X : OUS.{u}) : ousScal.{u} ⟶ X := ousUnitMap X

/-- **The right pullback square of 180I in `OUSᵒᵖ`**: the square
```
  ℝ × ℝ --u×u--> X × Y
    |π₁            |π₁
    v              v
    ℝ  ---u----->  X
```
is a pushout in `OUS`.  The mediating map is `γ(x) = α(x, 0)`; that it is
well defined uses `ous_prod_apply_eq_zero`. -/
theorem ous_isPushout2 (X Y : OUS.{u}) :
    IsPushout (ousSq2f X Y) ousSq2g.{u} (ousSq2h X Y) (ousSq2i X) := by
  have w : ousSq2f X Y ≫ ousSq2h X Y = ousSq2g.{u} ≫ ousSq2i X :=
    ous_hom_ext fun p =>
      (ous_comp_apply _ _ p).trans (ous_comp_apply _ _ p).symm
  have hcond : ∀ s : PushoutCocone (ousSq2f X Y) ousSq2g.{u},
      ∀ z w : ULift.{u} ℝ,
      s.inl.toLinearMap (z.down • X.unit, w.down • Y.unit)
        = s.inr.toLinearMap z := by
    intro s z w
    exact ((ous_comp_apply (ousSq2f X Y) s.inl (z, w)).symm.trans
      (ous_congr s.condition (z, w))).trans
      (ous_comp_apply ousSq2g.{u} s.inr (z, w))
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s => ousMed2 s.inl s.inr (hcond s)) ?_ ?_ ?_)
  · intro s
    exact ous_hom_ext fun p =>
      (ous_comp_apply (ousSq2h X Y) _ p).trans
        (ousMed2_fac_left _ _ (hcond s) p)
  · intro s
    exact ous_hom_ext fun z =>
      (ous_comp_apply (ousSq2i X) _ z).trans
        (ousMed2_fac_right _ _ (hcond s) z)
  · intro s m h₁ _
    exact ousMed2_uniq _ _ (hcond s) m
      (fun p => (ous_comp_apply (ousSq2h X Y) m p).symm.trans (ous_congr h₁ p))

/-! ### Joint monicity of the two cotuples in `OUSᵒᵖ` -/

/-- **The third axiom of 180I in `OUSᵒᵖ`**, elementwise: a positive
unit-preserving map out of `ℝ³` is determined by its restrictions along
`(x,y) ↦ (x,y,y)` and `(x,y) ↦ (y,x,y)`, because those recover the images
of the three coordinate units, and `ℝ³` is spanned by them. -/
theorem ous_jointlyMonic_aux {Z : OUS.{u}}
    (a b : (ousScal.{u}.prod ousScal.{u}).prod ousScal.{u} ⟶ Z)
    (h1 : ∀ x : ULift.{u} ℝ × ULift.{u} ℝ,
      a.toLinearMap ((x.1, x.2), x.2) = b.toLinearMap ((x.1, x.2), x.2))
    (h2 : ∀ x : ULift.{u} ℝ × ULift.{u} ℝ,
      a.toLinearMap ((x.2, x.1), x.2) = b.toLinearMap ((x.2, x.1), x.2)) :
    a = b := by
  set e₁ : (ULift.{u} ℝ × ULift.{u} ℝ) × ULift.{u} ℝ := ((1, 0), 0) with he₁
  set e₂ : (ULift.{u} ℝ × ULift.{u} ℝ) × ULift.{u} ℝ := ((0, 1), 0) with he₂
  set e₃ : (ULift.{u} ℝ × ULift.{u} ℝ) × ULift.{u} ℝ := ((0, 0), 1) with he₃
  have ha1 : a.toLinearMap e₁ = b.toLinearMap e₁ := h1 (1, 0)
  have ha2 : a.toLinearMap e₂ = b.toLinearMap e₂ := h2 (1, 0)
  have ha3 : a.toLinearMap e₃ = b.toLinearMap e₃ := by
    have h4 := h1 (0, 1)
    have hsum : (((0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ)), (1 : ULift.{u} ℝ))
        = e₂ + e₃ := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [he₂, he₃]
    rw [hsum, map_add, map_add, ha2] at h4
    exact add_left_cancel h4
  have key : ∀ (f : (ousScal.{u}.prod ousScal.{u}).prod ousScal.{u} ⟶ Z)
      (y : (ULift.{u} ℝ × ULift.{u} ℝ) × ULift.{u} ℝ),
      f.toLinearMap y = y.1.1.down • f.toLinearMap e₁
        + (y.1.2.down • f.toLinearMap e₂ + y.2.down • f.toLinearMap e₃) := by
    intro f y
    have hdec : y = y.1.1.down • e₁ + (y.1.2.down • e₂ + y.2.down • e₃) := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;>
        · apply ULift.down_injective
          simp [he₁, he₂, he₃]
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, map_add, map_smul, map_smul]
  refine ous_hom_ext fun y => ?_
  rw [key a y, key b y, ha1, ha2, ha3]

/-! ### `OUSᵒᵖ` is an effectus -/

/-- **189aII.1** (`effexamplesintro`, eff.tex:2032, Examples): the
category `OUSᵒᵖ` of order unit spaces with positive unit-preserving linear
maps in the opposite direction is an effectus in total form.

The point gives no proof.  Ours is the `vNᵒᵖ` argument of `effectus_vn`
with the C\*-algebra replaced by an ordered real vector space: `ℝ` is
initial in `OUS` and the products are the coproducts of `OUSᵒᵖ`
(`ousPres`), the two squares of 180I are the pushouts `ous_isPushout1`
and `ous_isPushout2`, and the two cotuples are jointly monic by
`ous_jointlyMonic_aux`. -/
theorem effectus_ous : Nonempty (EffectusTotalStructure OUS.{u}ᵒᵖ) := by
  have : HasTerminal (OUS.{u}ᵒᵖ) := ousPres.hT.hasTerminal
  have : HasInitial (OUS.{u}ᵒᵖ) :=
    (IsTerminal.op (OUS.{u}) ousTrivIsTerminal).hasInitial
  have : ∀ X Y : OUS.{u}ᵒᵖ, HasColimit (pair X Y) := fun X Y =>
    HasColimit.mk ⟨_, ousPres.hP X Y⟩
  have : HasBinaryCoproducts (OUS.{u}ᵒᵖ) :=
    hasBinaryCoproducts_of_hasColimit_pair _
  have : HasFiniteCoproducts (OUS.{u}ᵒᵖ) :=
    hasFiniteCoproducts_of_has_binary_and_initial
  refine ⟨{ hasFiniteCoproducts := inferInstance
            hasTerminal := inferInstance
            effectus := effectusTotalForm_of_pres ousPres ?_ ?_ ?_ }⟩
  · intro X Y
    have e₁ : ousPres.pmap (𝟙 X) (ousPres.hT.from Y)
        = Quiver.Hom.op (ousSq1i X.unop Y.unop) := by
      refine ousop_hom_ext fun p => (ousPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext rfl ?_
      exact ousPres_from_apply Y p.2
    have e₂ : ousPres.pmap (ousPres.hT.from X) (𝟙 Y)
        = Quiver.Hom.op (ousSq1h X.unop Y.unop) := by
      refine ousop_hom_ext fun p => (ousPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ rfl
      exact ousPres_from_apply X p.1
    have e₃ : ousPres.pmap (ousPres.hT.from X) (𝟙 ousPres.T)
        = Quiver.Hom.op (ousSq1g X.unop) := by
      refine ousop_hom_ext fun p => (ousPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ rfl
      exact ousPres_from_apply X p.1
    have e₄ : ousPres.pmap (𝟙 ousPres.T) (ousPres.hT.from Y)
        = Quiver.Hom.op (ousSq1f Y.unop) := by
      refine ousop_hom_ext fun p => (ousPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext rfl ?_
      exact ousPres_from_apply Y p.2
    rw [e₁, e₂, e₃, e₄]
    exact (ous_isPushout1 X.unop Y.unop).op
  · intro X Y
    have f₁ : ousPres.hT.from X = Quiver.Hom.op (ousSq2i X.unop) :=
      ousPres.hT.hom_ext _ _
    have f₄ : ousPres.pmap (ousPres.hT.from X) (ousPres.hT.from Y)
        = Quiver.Hom.op (ousSq2f X.unop Y.unop) := by
      refine ousop_hom_ext fun p => (ousPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ ?_
      · exact ousPres_from_apply X p.1
      · exact ousPres_from_apply Y p.2
    rw [f₄, f₁]
    exact (ous_isPushout2 X.unop Y.unop).op
  · intro Z a b hf hg
    apply Quiver.Hom.unop_inj
    refine ous_jointlyMonic_aux a.unop b.unop (fun x => ?_) (fun x => ?_)
    · exact ousop_comp_congr hf x
    · exact ousop_comp_congr hg x

/-! ## Order unit groups (189aII.2) -/

/-- **189aII.2** (`effexamplesintro`, eff.tex:2037, Examples): an **order
unit group** is a partially ordered abelian group with a distinguished
order unit.  Stated as a mixin over `AddCommGroup G` and `PartialOrder G`:
the order is translation-invariant and the distinguished element `unit` is
a positive element with `∀ g, ∃ n : ℕ, g ≤ n • unit`.

Unlike for order unit spaces, positivity of the unit must be required
here (this is the standard, Goodearl, definition): in `ℤ` with positive
cone `2ℕ` the element `1` satisfies the order-unit inequality for every
`g` but is not positive. -/
class OrderUnitGroup (G : Type u) [AddCommGroup G] [PartialOrder G] where
  /-- the order is translation-invariant -/
  protected add_le_add_left (x y : G) : x ≤ y → ∀ z, x + z ≤ y + z
  /-- the distinguished order unit -/
  unit : G
  /-- ... which is positive -/
  protected unit_nonneg : 0 ≤ unit
  /-- ... and an order unit -/
  protected exists_le_nsmul_unit (g : G) : ∃ n : ℕ, g ≤ n • unit

section OUGBasic

variable {G : Type u} [AddCommGroup G] [PartialOrder G] [OrderUnitGroup G]

/-- The distinguished order unit of an order unit group, with the group as
an explicit argument. -/
abbrev ougUnit (G : Type u) [AddCommGroup G] [PartialOrder G]
    [OrderUnitGroup G] : G := OrderUnitGroup.unit

/-- An order unit group is an ordered additive monoid. -/
instance OrderUnitGroup.toIsOrderedAddMonoid : IsOrderedAddMonoid G where
  add_le_add_left := OrderUnitGroup.add_le_add_left

/-- Translation-invariance of the order, as a lemma. -/
theorem oug_add_le_add_right {x y : G} (h : x ≤ y) (z : G) : x + z ≤ y + z :=
  OrderUnitGroup.add_le_add_left x y h z

/-- The order unit is positive (an axiom, see the class doc string). -/
theorem oug_unit_nonneg : (0 : G) ≤ ougUnit G := OrderUnitGroup.unit_nonneg

/-- The order-unit axiom. -/
theorem oug_exists_le_nsmul_unit (g : G) : ∃ n : ℕ, g ≤ n • ougUnit G :=
  OrderUnitGroup.exists_le_nsmul_unit g

/-- Natural multiples of a positive element are positive. -/
theorem oug_nsmul_nonneg {a : G} (ha : 0 ≤ a) : ∀ n : ℕ, 0 ≤ n • a := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      rw [succ_nsmul]
      exact add_nonneg ih ha

/-- Integer multiples of a positive element by a non-negative integer are
positive. -/
theorem oug_zsmul_nonneg {a : G} (ha : 0 ≤ a) {n : ℤ} (hn : 0 ≤ n) :
    0 ≤ n • a := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [natCast_zsmul]
  exact oug_nsmul_nonneg ha m

/-- The multiples of the order unit are monotone in the multiplier. -/
theorem oug_nsmul_unit_mono {n m : ℕ} (h : n ≤ m) :
    n • ougUnit G ≤ m • ougUnit G := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_nsmul]
  exact le_add_of_nonneg_right (oug_nsmul_nonneg oug_unit_nonneg k)

/-- **Every element of an order unit group is a difference of two positive
elements**: from `g ≤ n • 1` one gets `g = n•1 - (n•1 - g)`. -/
theorem oug_eq_sub_of_nonneg (g : G) :
    ∃ p q : G, 0 ≤ p ∧ 0 ≤ q ∧ g = p - q := by
  obtain ⟨n, hn⟩ := oug_exists_le_nsmul_unit g
  refine ⟨n • ougUnit G, n • ougUnit G - g,
    oug_nsmul_nonneg oug_unit_nonneg n, sub_nonneg.mpr hn, ?_⟩
  abel

end OUGBasic

/-! ### The basic examples of order unit groups -/

/-- `ℤ` is an order unit group with order unit `1`. -/
instance Int.orderUnitGroup : OrderUnitGroup ℤ where
  add_le_add_left x y h z := by
    rw [add_comm x z, add_comm y z]; exact add_le_add_right h z
  unit := 1
  unit_nonneg := zero_le_one
  exists_le_nsmul_unit g := ⟨g.toNat, by simp⟩

/-- An order unit group stays one after `ULift`ing. -/
instance ULift.orderUnitGroup (G : Type u) [AddCommGroup G] [PartialOrder G]
    [OrderUnitGroup G] : OrderUnitGroup (ULift.{v} G) where
  add_le_add_left x y h z := by
    show x.down + z.down ≤ y.down + z.down
    exact oug_add_le_add_right (show x.down ≤ y.down from h) z.down
  unit := ULift.up (ougUnit G)
  unit_nonneg := by
    show (0 : G) ≤ ougUnit G
    exact oug_unit_nonneg
  exists_le_nsmul_unit g := by
    obtain ⟨n, hn⟩ := oug_exists_le_nsmul_unit g.down
    exact ⟨n, hn⟩

/-- The one-point group is an order unit group; it is the final object of
`OUG`, hence the initial object of `OUGᵒᵖ`. -/
instance PUnit.orderUnitGroup : OrderUnitGroup PUnit.{u + 1} where
  add_le_add_left _ _ _ _ := le_of_eq (Subsingleton.elim _ _)
  unit := PUnit.unit
  unit_nonneg := le_of_eq (Subsingleton.elim _ _)
  exists_le_nsmul_unit _ := ⟨0, le_of_eq (Subsingleton.elim _ _)⟩

/-- The product of two order unit groups, with the coordinatewise order
and unit `(1, 1)`. -/
instance Prod.orderUnitGroup (G H : Type u) [AddCommGroup G] [PartialOrder G]
    [OrderUnitGroup G] [AddCommGroup H] [PartialOrder H] [OrderUnitGroup H] :
    OrderUnitGroup (G × H) where
  add_le_add_left _ _ h z :=
    Prod.le_def.mpr ⟨oug_add_le_add_right (Prod.le_def.mp h).1 z.1,
      oug_add_le_add_right (Prod.le_def.mp h).2 z.2⟩
  unit := (ougUnit G, ougUnit H)
  unit_nonneg := Prod.le_def.mpr ⟨oug_unit_nonneg, oug_unit_nonneg⟩
  exists_le_nsmul_unit p := by
    obtain ⟨n, hn⟩ := oug_exists_le_nsmul_unit p.1
    obtain ⟨m, hm⟩ := oug_exists_le_nsmul_unit p.2
    refine ⟨max n m, Prod.le_def.mpr ⟨?_, ?_⟩⟩
    · exact hn.trans (oug_nsmul_unit_mono (Nat.le_max_left n m))
    · exact hm.trans (oug_nsmul_unit_mono (Nat.le_max_right n m))

/-! ### The category `OUG` -/

/-- A bundled order unit group: the object type of the category `OUG`. -/
structure OUG : Type (u + 1) where
  /-- the underlying type -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [partialOrder : PartialOrder carrier]
  [orderUnitGroup : OrderUnitGroup carrier]

attribute [instance] OUG.addCommGroup OUG.partialOrder OUG.orderUnitGroup

/-- An object of `OUG` may be used directly as its carrier type. -/
instance : CoeSort OUG.{u} (Type u) := ⟨OUG.carrier⟩

/-- Bundle an order unit group as an object of `OUG`. -/
abbrev OUG.of (G : Type u) [AddCommGroup G] [PartialOrder G]
    [OrderUnitGroup G] : OUG.{u} := ⟨G⟩

/-- The order unit of a bundled order unit group. -/
abbrev OUG.unit (G : OUG.{u}) : G.carrier := ougUnit G.carrier

/-- The product of two bundled order unit groups. -/
abbrev OUG.prod (G H : OUG.{u}) : OUG.{u} := OUG.of (G.carrier × H.carrier)

/-- The scalars `ℤᵤ`: the initial object of `OUG`, hence the final object
of `OUGᵒᵖ`. -/
abbrev ougScal : OUG.{u} := OUG.of (ULift.{u} ℤ)

/-- The zero group: the final object of `OUG`, hence the initial object of
`OUGᵒᵖ`. -/
abbrev ougTriv : OUG.{u} := OUG.of PUnit.{u + 1}

/-- The order unit of the scalars `ℤᵤ` is `1`. -/
@[simp] theorem ougScal_unit : ougScal.{u}.unit = (1 : ULift.{u} ℤ) := rfl

/-- The order unit of a product is the pair of the order units. -/
@[simp] theorem OUG.prod_unit (G H : OUG.{u}) :
    (G.prod H).unit = (G.unit, H.unit) := rfl

/-- A **positive unit-preserving homomorphism** of order unit groups: the
morphisms of `OUG` (and, read backwards, of `OUGᵒᵖ`). -/
structure OUGMap (G H : OUG.{u}) : Type u where
  /-- the underlying additive homomorphism -/
  toAddHom : G.carrier →+ H.carrier
  /-- ... which is positive -/
  map_nonneg' : ∀ g : G.carrier, 0 ≤ g → 0 ≤ toAddHom g
  /-- ... and unit-preserving -/
  map_unit' : toAddHom G.unit = H.unit

/-- Extensionality for morphisms of `OUG`. -/
theorem OUGMap.ext' {G H : OUG.{u}} {f g : OUGMap G H}
    (h : ∀ x, f.toAddHom x = g.toAddHom x) : f = g := by
  obtain ⟨f, hf₁, hf₂⟩ := f
  obtain ⟨g, hg₁, hg₂⟩ := g
  have hfg : f = g := AddMonoidHom.ext h
  subst hfg
  rfl

/-- A positive homomorphism is monotone. -/
theorem OUGMap.mono {G H : OUG.{u}} (f : OUGMap G H) {x y : G.carrier}
    (h : x ≤ y) : f.toAddHom x ≤ f.toAddHom y := by
  have h1 := f.map_nonneg' (y - x) (sub_nonneg.mpr h)
  rw [map_sub] at h1
  exact sub_nonneg.mp h1

/-- The identity morphism of `OUG`. -/
def OUGMap.id (G : OUG.{u}) : OUGMap G G where
  toAddHom := AddMonoidHom.id _
  map_nonneg' _ h := h
  map_unit' := rfl

/-- Composition in `OUG` (diagrammatic order). -/
def OUGMap.comp {G H K : OUG.{u}} (f : OUGMap G H) (g : OUGMap H K) :
    OUGMap G K where
  toAddHom := g.toAddHom.comp f.toAddHom
  map_nonneg' x h := g.map_nonneg' _ (f.map_nonneg' x h)
  map_unit' := by
    show g.toAddHom (f.toAddHom G.unit) = K.unit
    rw [f.map_unit', g.map_unit']

/-- **The category `OUG`** of order unit groups with positive
unit-preserving homomorphisms. -/
instance : Category.{u} OUG.{u} where
  Hom G H := OUGMap G H
  id G := OUGMap.id G
  comp f g := OUGMap.comp f g
  id_comp _ := OUGMap.ext' fun _ => rfl
  comp_id _ := OUGMap.ext' fun _ => rfl
  assoc _ _ _ := OUGMap.ext' fun _ => rfl

/-- Extensionality in `OUG`, for morphisms written with `⟶`. -/
theorem oug_hom_ext {G H : OUG.{u}} {f g : G ⟶ H}
    (h : ∀ x, f.toAddHom x = g.toAddHom x) : f = g := OUGMap.ext' h

/-- Composition in `OUG` is composition of the underlying functions. -/
theorem oug_comp_apply {G H K : OUG.{u}} (f : G ⟶ H) (g : H ⟶ K)
    (x : G.carrier) : (f ≫ g).toAddHom x = g.toAddHom (f.toAddHom x) := rfl

/-- The identity of `OUG` is the identity function. -/
theorem oug_id_apply {G : OUG.{u}} (x : G.carrier) :
    (𝟙 G : G ⟶ G).toAddHom x = x := rfl

/-- Equal morphisms of `OUG` agree pointwise. -/
theorem oug_congr {G H : OUG.{u}} {f g : G ⟶ H} (h : f = g) (x : G.carrier) :
    f.toAddHom x = g.toAddHom x := by rw [h]

/-- Extensionality in `OUGᵒᵖ`. -/
theorem ougop_hom_ext {G H : OUG.{u}ᵒᵖ} {f g : G ⟶ H}
    (h : ∀ x, f.unop.toAddHom x = g.unop.toAddHom x) : f = g :=
  Quiver.Hom.unop_inj (oug_hom_ext h)

/-- Composition in `OUGᵒᵖ` applies the two underlying functions in the
opposite order. -/
theorem ougop_comp_apply {G H K : OUG.{u}ᵒᵖ} (f : G ⟶ H) (g : H ⟶ K)
    (x : K.unop.carrier) :
    (f ≫ g).unop.toAddHom x = f.unop.toAddHom (g.unop.toAddHom x) :=
  oug_comp_apply g.unop f.unop x

/-- Equal morphisms of `OUGᵒᵖ` agree pointwise. -/
theorem ougop_congr {G H : OUG.{u}ᵒᵖ} {f g : G ⟶ H} (h : f = g)
    (x : H.unop.carrier) : f.unop.toAddHom x = g.unop.toAddHom x := by rw [h]

/-- Postcomposition with a fixed map, pointwise. -/
theorem ougop_comp_congr {Z P G : OUG.{u}ᵒᵖ} {F : P ⟶ G} {a b : Z ⟶ P}
    (h : a ≫ F = b ≫ F) (x : G.unop.carrier) :
    a.unop.toAddHom (F.unop.toAddHom x) = b.unop.toAddHom (F.unop.toAddHom x) :=
  ((ougop_comp_apply a F x).symm.trans (ougop_congr h x)).trans
    (ougop_comp_apply b F x)

/-! ### The concrete final, initial and product objects of `OUG` -/

/-- The unique morphism `ℤᵤ ⟶ G` of `OUG`, namely `n ↦ n · 1`. -/
def ougUnitMap (G : OUG.{u}) : ougScal.{u} ⟶ G where
  toAddHom := AddMonoidHom.mk' (fun n => n.down • G.unit) (fun a b => by
    show (a.down + b.down) • G.unit = a.down • G.unit + b.down • G.unit
    exact add_zsmul _ _ _)
  map_nonneg' n hn := oug_zsmul_nonneg oug_unit_nonneg hn
  map_unit' := one_zsmul _

/-- The defining equation of `ougUnitMap`. -/
@[simp] theorem ougUnitMap_apply (G : OUG.{u}) (n : ULift.{u} ℤ) :
    (ougUnitMap G).toAddHom n = n.down • G.unit := rfl

/-- The unique morphism `G ⟶ 0` of `OUG`. -/
def ougTrivMap (G : OUG.{u}) : G ⟶ ougTriv.{u} where
  toAddHom := 0
  map_nonneg' _ _ := le_of_eq (Subsingleton.elim _ _)
  map_unit' := Subsingleton.elim _ _

/-- The first projection `G × H ⟶ G`. -/
def ougFst (G H : OUG.{u}) : G.prod H ⟶ G where
  toAddHom := AddMonoidHom.fst G.carrier H.carrier
  map_nonneg' _ h := (Prod.le_def.mp h).1
  map_unit' := rfl

/-- The second projection `G × H ⟶ H`. -/
def ougSnd (G H : OUG.{u}) : G.prod H ⟶ H where
  toAddHom := AddMonoidHom.snd G.carrier H.carrier
  map_nonneg' _ h := (Prod.le_def.mp h).2
  map_unit' := rfl

/-- The pairing `⟨f, g⟩ : K ⟶ G × H`. -/
def ougPair {K G H : OUG.{u}} (f : K ⟶ G) (g : K ⟶ H) : K ⟶ G.prod H where
  toAddHom := AddMonoidHom.prod f.toAddHom g.toAddHom
  map_nonneg' z h := Prod.le_def.mpr ⟨f.map_nonneg' z h, g.map_nonneg' z h⟩
  map_unit' := Prod.ext f.map_unit' g.map_unit'

/-- The defining equation of `ougPair`. -/
@[simp] theorem ougPair_apply {K G H : OUG.{u}} (f : K ⟶ G) (g : K ⟶ H)
    (z : K.carrier) :
    (ougPair f g).toAddHom z = (f.toAddHom z, g.toAddHom z) := rfl

/-- The product `f × g : G × H ⟶ G' × H'` of two morphisms. -/
def ougProdMap {G G' H H' : OUG.{u}} (f : G ⟶ G') (g : H ⟶ H') :
    G.prod H ⟶ G'.prod H' where
  toAddHom := f.toAddHom.prodMap g.toAddHom
  map_nonneg' _ h :=
    Prod.le_def.mpr ⟨f.map_nonneg' _ (Prod.le_def.mp h).1,
      g.map_nonneg' _ (Prod.le_def.mp h).2⟩
  map_unit' := Prod.ext f.map_unit' g.map_unit'

/-- The defining equation of `ougProdMap`. -/
@[simp] theorem ougProdMap_apply {G G' H H' : OUG.{u}} (f : G ⟶ G')
    (g : H ⟶ H') (p : G.carrier × H.carrier) :
    (ougProdMap f g).toAddHom p = (f.toAddHom p.1, g.toAddHom p.2) := rfl

/-- Any morphism `ℤᵤ ⟶ G` is `n ↦ n · 1`. -/
theorem ougUnitMap_unique {G : OUG.{u}} (f : ougScal.{u} ⟶ G) :
    f = ougUnitMap G := by
  refine oug_hom_ext fun n => ?_
  have hn : n = n.down • (1 : ULift.{u} ℤ) := by
    apply ULift.down_injective
    simp
  rw [ougUnitMap_apply]
  conv_lhs => rw [hn]
  rw [map_zsmul]
  exact congrArg (fun z => n.down • z) f.map_unit'

/-- **`ℤᵤ` is the initial object of `OUG`**, hence the final object of
`OUGᵒᵖ`. -/
def ougScalIsInitial : IsInitial ougScal.{u} :=
  IsInitial.ofUniqueHom (fun G => ougUnitMap G) (fun _ f => ougUnitMap_unique f)

/-- **The zero group is the final object of `OUG`**, hence the initial
object of `OUGᵒᵖ`. -/
def ougTrivIsTerminal : IsTerminal ougTriv.{u} :=
  IsTerminal.ofUniqueHom (fun G => ougTrivMap G)
    (fun _ _ => oug_hom_ext fun _ =>
      Subsingleton.elim (α := PUnit.{u + 1}) _ _)

/-- The concrete presentation of `OUGᵒᵖ`: the final object is the scalars
`ℤᵤ`, the binary coproducts are the products. -/
noncomputable def ougPres : CoprodPres (OUG.{u}ᵒᵖ) where
  T := Opposite.op ougScal.{u}
  hT := IsInitial.op (OUG.{u}) ougScalIsInitial
  P G H := Opposite.op (G.unop.prod H.unop)
  pinl G H := Quiver.Hom.op (ougFst G.unop H.unop)
  pinr G H := Quiver.Hom.op (ougSnd G.unop H.unop)
  hP G H := BinaryCofan.IsColimit.mk _
    (fun {_} u v => Quiver.Hom.op (ougPair u.unop v.unop))
    (fun {_} _ _ => ougop_hom_ext fun x => ougop_comp_apply _ _ x)
    (fun {_} _ _ => ougop_hom_ext fun x => ougop_comp_apply _ _ x)
    (fun {_} _ _ m h₁ h₂ => ougop_hom_ext fun x => by
      refine Prod.ext ?_ ?_
      · exact (ougop_comp_apply _ m x).symm.trans (ougop_congr h₁ x)
      · exact (ougop_comp_apply _ m x).symm.trans (ougop_congr h₂ x))

/-- The unique morphism into the final object of `OUGᵒᵖ` is `n ↦ n · 1`. -/
theorem ougPres_from_apply (H : OUG.{u}ᵒᵖ) (n : ULift.{u} ℤ) :
    (ougPres.hT.from H).unop.toAddHom n = n.down • H.unop.unit := by
  have h : ougPres.hT.from H = Quiver.Hom.op (ougUnitMap H.unop) :=
    ougPres.hT.hom_ext _ _
  rw [h]
  rfl

/-- The coproduct of two morphisms of `OUGᵒᵖ` acts coordinatewise. -/
theorem ougPres_pmap_apply {G G' H H' : OUG.{u}ᵒᵖ} (f : G ⟶ G') (g : H ⟶ H')
    (p : (ougPres.P G' H').unop.carrier) :
    (ougPres.pmap f g).unop.toAddHom p
      = (f.unop.toAddHom p.1, g.unop.toAddHom p.2) := by
  refine Prod.ext ?_ ?_
  · exact ougop_comp_apply f _ p
  · exact ougop_comp_apply g _ p

/-! ### The left pushout square of 180I in `OUG` -/

section OUGMed1

variable {G H K : OUG.{u}}

/-- The mediating morphism `γ(x, y) = β(x, 0) + α(0, y)` of the first
pushout square of 180I, for order unit groups. -/
def ougMed1 (α : ougScal.{u}.prod H ⟶ K) (β : G.prod ougScal.{u} ⟶ K)
    (hc : ∀ z w : ULift.{u} ℤ,
      α.toAddHom (z, w.down • H.unit) = β.toAddHom (z.down • G.unit, w)) :
    G.prod H ⟶ K where
  toAddHom :=
    (β.toAddHom.comp ((AddMonoidHom.inl G.carrier (ULift.{u} ℤ)).comp
        (AddMonoidHom.fst G.carrier H.carrier)))
      + (α.toAddHom.comp ((AddMonoidHom.inr (ULift.{u} ℤ) H.carrier).comp
        (AddMonoidHom.snd G.carrier H.carrier)))
  map_nonneg' p hp := by
    show (0 : K.carrier) ≤ β.toAddHom (p.1, 0) + α.toAddHom (0, p.2)
    have h1 : (0 : G.carrier × ULift.{u} ℤ) ≤ (p.1, 0) :=
      Prod.le_def.mpr ⟨(Prod.le_def.mp hp).1, le_refl _⟩
    have h2 : (0 : ULift.{u} ℤ × H.carrier) ≤ (0, p.2) :=
      Prod.le_def.mpr ⟨le_refl _, (Prod.le_def.mp hp).2⟩
    exact add_nonneg (β.map_nonneg' _ h1) (α.map_nonneg' _ h2)
  map_unit' := by
    show β.toAddHom (G.unit, (0 : ULift.{u} ℤ))
      + α.toAddHom ((0 : ULift.{u} ℤ), H.unit) = K.unit
    have h1 : α.toAddHom ((1 : ULift.{u} ℤ), (0 : H.carrier))
        = β.toAddHom (G.unit, (0 : ULift.{u} ℤ)) := by
      have h := hc 1 0
      simpa using h
    have h2 : ((1 : ULift.{u} ℤ), (0 : H.carrier))
        + ((0 : ULift.{u} ℤ), H.unit) = ((1 : ULift.{u} ℤ), H.unit) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [← h1, ← map_add, h2]
    exact α.map_unit'

/-- The defining equation of `ougMed1`. -/
@[simp] theorem ougMed1_apply (α : ougScal.{u}.prod H ⟶ K)
    (β : G.prod ougScal.{u} ⟶ K) (hc) (p : G.carrier × H.carrier) :
    (ougMed1 α β hc).toAddHom p
      = β.toAddHom (p.1, 0) + α.toAddHom (0, p.2) := rfl

variable (α : ougScal.{u}.prod H ⟶ K) (β : G.prod ougScal.{u} ⟶ K)
  (hc : ∀ z w : ULift.{u} ℤ,
    α.toAddHom (z, w.down • H.unit) = β.toAddHom (z.down • G.unit, w))

/-- `γ ∘ (u × id) = α`. -/
theorem ougMed1_fac_left (y : ULift.{u} ℤ × H.carrier) :
    (ougMed1 α β hc).toAddHom (y.1.down • G.unit, y.2) = α.toAddHom y := by
  show β.toAddHom (y.1.down • G.unit, 0) + α.toAddHom (0, y.2)
    = α.toAddHom y
  have h1 : α.toAddHom (y.1, (0 : H.carrier))
      = β.toAddHom (y.1.down • G.unit, (0 : ULift.{u} ℤ)) := by
    have h := hc y.1 0
    simpa using h
  have h3 : ((y.1, (0 : H.carrier)) : ULift.{u} ℤ × H.carrier)
      + (((0 : ULift.{u} ℤ), y.2) : ULift.{u} ℤ × H.carrier) = y := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [← h1, ← map_add, h3]

/-- `γ ∘ (id × u) = β`. -/
theorem ougMed1_fac_right (y : G.carrier × ULift.{u} ℤ) :
    (ougMed1 α β hc).toAddHom (y.1, y.2.down • H.unit) = β.toAddHom y := by
  show β.toAddHom (y.1, 0) + α.toAddHom (0, y.2.down • H.unit)
    = β.toAddHom y
  have h1 : α.toAddHom ((0 : ULift.{u} ℤ), y.2.down • H.unit)
      = β.toAddHom ((0 : G.carrier), y.2) := by
    have h := hc 0 y.2
    simpa using h
  have h3 : ((y.1, (0 : ULift.{u} ℤ)) : G.carrier × ULift.{u} ℤ)
      + (((0 : G.carrier), y.2) : G.carrier × ULift.{u} ℤ) = y := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [h1, ← map_add, h3]

/-- `γ` is the only morphism with those two properties. -/
theorem ougMed1_uniq (m : G.prod H ⟶ K)
    (h₁ : ∀ y : ULift.{u} ℤ × H.carrier,
      m.toAddHom (y.1.down • G.unit, y.2) = α.toAddHom y)
    (h₂ : ∀ y : G.carrier × ULift.{u} ℤ,
      m.toAddHom (y.1, y.2.down • H.unit) = β.toAddHom y) :
    m = ougMed1 α β hc := by
  refine oug_hom_ext fun p => ?_
  show m.toAddHom p = β.toAddHom (p.1, 0) + α.toAddHom (0, p.2)
  have e₁ : m.toAddHom ((p.1, (0 : H.carrier)) : G.carrier × H.carrier)
      = β.toAddHom (p.1, 0) := by
    have h := h₂ ((p.1, (0 : ULift.{u} ℤ)) : G.carrier × ULift.{u} ℤ)
    simpa using h
  have e₂ : m.toAddHom (((0 : G.carrier), p.2) : G.carrier × H.carrier)
      = α.toAddHom (0, p.2) := by
    have h := h₁ (((0 : ULift.{u} ℤ), p.2) : ULift.{u} ℤ × H.carrier)
    simpa using h
  have h3 : ((p.1, (0 : H.carrier)) : G.carrier × H.carrier)
      + (((0 : G.carrier), p.2) : G.carrier × H.carrier) = p := by
    refine Prod.ext ?_ ?_ <;> simp
  have h4 : m.toAddHom p
      = m.toAddHom ((p.1, (0 : H.carrier)) : G.carrier × H.carrier)
        + m.toAddHom (((0 : G.carrier), p.2) : G.carrier × H.carrier) := by
    rw [← map_add, h3]
  rw [h4, e₁, e₂]

end OUGMed1

/-- `id × u : ℤ × ℤ ⟶ ℤ × H`. -/
def ougSq1f (H : OUG.{u}) : ougScal.{u}.prod ougScal.{u} ⟶ ougScal.{u}.prod H :=
  ougProdMap (𝟙 ougScal.{u}) (ougUnitMap H)

/-- `u × id : ℤ × ℤ ⟶ G × ℤ`. -/
def ougSq1g (G : OUG.{u}) : ougScal.{u}.prod ougScal.{u} ⟶ G.prod ougScal.{u} :=
  ougProdMap (ougUnitMap G) (𝟙 ougScal.{u})

/-- `u × id : ℤ × H ⟶ G × H`. -/
def ougSq1h (G H : OUG.{u}) : ougScal.{u}.prod H ⟶ G.prod H :=
  ougProdMap (ougUnitMap G) (𝟙 H)

/-- `id × u : G × ℤ ⟶ G × H`. -/
def ougSq1i (G H : OUG.{u}) : G.prod ougScal.{u} ⟶ G.prod H :=
  ougProdMap (𝟙 G) (ougUnitMap H)

/-- The defining equation of `ougSq1f`. -/
@[simp] theorem ougSq1f_apply (H : OUG.{u}) (p : ULift.{u} ℤ × ULift.{u} ℤ) :
    (ougSq1f H).toAddHom p = (p.1, p.2.down • H.unit) := rfl

/-- The defining equation of `ougSq1g`. -/
@[simp] theorem ougSq1g_apply (G : OUG.{u}) (p : ULift.{u} ℤ × ULift.{u} ℤ) :
    (ougSq1g G).toAddHom p = (p.1.down • G.unit, p.2) := rfl

/-- The defining equation of `ougSq1h`. -/
@[simp] theorem ougSq1h_apply (G H : OUG.{u}) (p : ULift.{u} ℤ × H.carrier) :
    (ougSq1h G H).toAddHom p = (p.1.down • G.unit, p.2) := rfl

/-- The defining equation of `ougSq1i`. -/
@[simp] theorem ougSq1i_apply (G H : OUG.{u}) (p : G.carrier × ULift.{u} ℤ) :
    (ougSq1i G H).toAddHom p = (p.1, p.2.down • H.unit) := rfl

/-- **The left pullback square of 180I in `OUGᵒᵖ`** — the same square as
for `OUSᵒᵖ`, glued by `γ(x, y) = β(x, 0) + α(0, y)`. -/
theorem oug_isPushout1 (G H : OUG.{u}) :
    IsPushout (ougSq1f H) (ougSq1g G) (ougSq1h G H) (ougSq1i G H) := by
  have w : ougSq1f H ≫ ougSq1h G H = ougSq1g G ≫ ougSq1i G H :=
    oug_hom_ext fun p =>
      (oug_comp_apply _ _ p).trans (oug_comp_apply _ _ p).symm
  have hcond : ∀ s : PushoutCocone (ougSq1f H) (ougSq1g G),
      ∀ z w : ULift.{u} ℤ,
      s.inl.toAddHom (z, w.down • H.unit)
        = s.inr.toAddHom (z.down • G.unit, w) := by
    intro s z w
    exact ((oug_comp_apply (ougSq1f H) s.inl (z, w)).symm.trans
      (oug_congr s.condition (z, w))).trans
      (oug_comp_apply (ougSq1g G) s.inr (z, w))
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s => ougMed1 s.inl s.inr (hcond s)) ?_ ?_ ?_)
  · intro s
    exact oug_hom_ext fun y =>
      (oug_comp_apply (ougSq1h G H) _ y).trans
        (ougMed1_fac_left _ _ (hcond s) y)
  · intro s
    exact oug_hom_ext fun y =>
      (oug_comp_apply (ougSq1i G H) _ y).trans
        (ougMed1_fac_right _ _ (hcond s) y)
  · intro s m h₁ h₂
    refine ougMed1_uniq _ _ (hcond s) m (fun y => ?_) (fun y => ?_)
    · exact (oug_comp_apply (ougSq1h G H) m y).symm.trans (oug_congr h₁ y)
    · exact (oug_comp_apply (ougSq1i G H) m y).symm.trans (oug_congr h₂ y)

/-! ### The right pushout square of 180I in `OUG` -/

/-- **A positive homomorphism on a product killing `(0, 1)` kills
`0 × H`**, by the order-unit axiom `c ≤ n • 1` and
`oug_eq_sub_of_nonneg`. -/
theorem oug_prod_apply_eq_zero {G H K : OUG.{u}} (α : G.prod H ⟶ K)
    (h1 : α.toAddHom ((0 : G.carrier), H.unit) = 0) (b : H.carrier) :
    α.toAddHom ((0 : G.carrier), b) = 0 := by
  have hnn : ∀ c : H.carrier, 0 ≤ c → α.toAddHom ((0 : G.carrier), c) = 0 := by
    intro c hc
    obtain ⟨n, hn⟩ := oug_exists_le_nsmul_unit c
    have hle : (((0 : G.carrier), c) : G.carrier × H.carrier)
        ≤ ((0 : G.carrier), n • H.unit) := Prod.le_def.mpr ⟨le_refl _, hn⟩
    have h0 : (0 : G.carrier × H.carrier)
        ≤ (((0 : G.carrier), c) : G.carrier × H.carrier) :=
      Prod.le_def.mpr ⟨le_refl _, hc⟩
    have hsm : (((0 : G.carrier), n • H.unit) : G.carrier × H.carrier)
        = n • (((0 : G.carrier), H.unit) : G.carrier × H.carrier) := by
      refine Prod.ext ?_ ?_ <;> simp
    have hz : α.toAddHom ((0 : G.carrier), n • H.unit) = 0 := by
      rw [hsm, map_nsmul, h1, smul_zero]
    refine le_antisymm ?_ ?_
    · rw [← hz]; exact α.mono hle
    · have hp := α.mono h0
      rwa [map_zero] at hp
  obtain ⟨p, q, hp, hq, hb⟩ := oug_eq_sub_of_nonneg b
  have hsplit : (((0 : G.carrier), b) : G.carrier × H.carrier)
      = (((0 : G.carrier), p) : G.carrier × H.carrier)
        - (((0 : G.carrier), q) : G.carrier × H.carrier) := by
    rw [hb]
    refine Prod.ext ?_ ?_ <;> simp
  rw [hsplit, map_sub, hnn p hp, hnn q hq, sub_zero]

section OUGMed2

variable {G H K : OUG.{u}}

/-- The mediating morphism `γ(x) = α(x, 0)` of the second pushout
square. -/
def ougMed2 (α : G.prod H ⟶ K) (β : ougScal.{u} ⟶ K)
    (hc : ∀ z w : ULift.{u} ℤ,
      α.toAddHom (z.down • G.unit, w.down • H.unit) = β.toAddHom z) :
    G ⟶ K where
  toAddHom := α.toAddHom.comp (AddMonoidHom.inl G.carrier H.carrier)
  map_nonneg' x hx := α.map_nonneg' _ (Prod.le_def.mpr ⟨hx, le_refl _⟩)
  map_unit' := by
    show α.toAddHom (G.unit, (0 : H.carrier)) = K.unit
    have h01 : α.toAddHom ((0 : G.carrier), H.unit) = 0 := by
      have h := hc 0 1
      rw [show β.toAddHom (0 : ULift.{u} ℤ) = 0 from map_zero _] at h
      simpa using h
    have h3 : ((G.unit, (0 : H.carrier)) : G.carrier × H.carrier)
        + (((0 : G.carrier), H.unit) : G.carrier × H.carrier)
        = (G.prod H).unit := by
      refine Prod.ext ?_ ?_ <;> simp
    have h4 : α.toAddHom (G.unit, (0 : H.carrier))
        + α.toAddHom ((0 : G.carrier), H.unit) = K.unit := by
      rw [← map_add, h3]
      exact α.map_unit'
    rwa [h01, add_zero] at h4

/-- The defining equation of `ougMed2`. -/
@[simp] theorem ougMed2_apply (α : G.prod H ⟶ K) (β : ougScal.{u} ⟶ K) (hc)
    (x : G.carrier) :
    (ougMed2 α β hc).toAddHom x = α.toAddHom (x, 0) := rfl

variable (α : G.prod H ⟶ K) (β : ougScal.{u} ⟶ K)
  (hc : ∀ z w : ULift.{u} ℤ,
    α.toAddHom (z.down • G.unit, w.down • H.unit) = β.toAddHom z)

/-- `γ ∘ π₁ = α`. -/
theorem ougMed2_fac_left (p : G.carrier × H.carrier) :
    (ougMed2 α β hc).toAddHom p.1 = α.toAddHom p := by
  show α.toAddHom (p.1, 0) = α.toAddHom p
  have h01 : α.toAddHom ((0 : G.carrier), H.unit) = 0 := by
    have h := hc 0 1
    rw [show β.toAddHom (0 : ULift.{u} ℤ) = 0 from map_zero _] at h
    simpa using h
  have h3 : ((p.1, (0 : H.carrier)) : G.carrier × H.carrier)
      + (((0 : G.carrier), p.2) : G.carrier × H.carrier) = p := by
    refine Prod.ext ?_ ?_ <;> simp
  have h4 : α.toAddHom p
      = α.toAddHom (p.1, (0 : H.carrier))
        + α.toAddHom ((0 : G.carrier), p.2) := by
    rw [← map_add, h3]
  rw [h4, oug_prod_apply_eq_zero α h01 p.2, add_zero]

/-- `γ ∘ u = β`. -/
theorem ougMed2_fac_right (z : ULift.{u} ℤ) :
    (ougMed2 α β hc).toAddHom (z.down • G.unit) = β.toAddHom z := by
  show α.toAddHom (z.down • G.unit, 0) = β.toAddHom z
  have h := hc z 0
  simpa using h

/-- `γ` is the only morphism with that property. -/
theorem ougMed2_uniq (m : G ⟶ K)
    (h₁ : ∀ p : G.carrier × H.carrier, m.toAddHom p.1 = α.toAddHom p) :
    m = ougMed2 α β hc := by
  refine oug_hom_ext fun x => ?_
  show m.toAddHom x = α.toAddHom (x, 0)
  exact h₁ ((x, (0 : H.carrier)) : G.carrier × H.carrier)

end OUGMed2

/-- `u × u : ℤ × ℤ ⟶ G × H`. -/
def ougSq2f (G H : OUG.{u}) : ougScal.{u}.prod ougScal.{u} ⟶ G.prod H :=
  ougProdMap (ougUnitMap G) (ougUnitMap H)

/-- `π₁ : ℤ × ℤ ⟶ ℤ`. -/
def ougSq2g : ougScal.{u}.prod ougScal.{u} ⟶ ougScal.{u} :=
  ougFst ougScal.{u} ougScal.{u}

/-- `π₁ : G × H ⟶ G`. -/
def ougSq2h (G H : OUG.{u}) : G.prod H ⟶ G := ougFst G H

/-- `u : ℤ ⟶ G`. -/
def ougSq2i (G : OUG.{u}) : ougScal.{u} ⟶ G := ougUnitMap G

/-- **The right pullback square of 180I in `OUGᵒᵖ`**, with mediating map
`γ(x) = α(x, 0)`. -/
theorem oug_isPushout2 (G H : OUG.{u}) :
    IsPushout (ougSq2f G H) ougSq2g.{u} (ougSq2h G H) (ougSq2i G) := by
  have w : ougSq2f G H ≫ ougSq2h G H = ougSq2g.{u} ≫ ougSq2i G :=
    oug_hom_ext fun p =>
      (oug_comp_apply _ _ p).trans (oug_comp_apply _ _ p).symm
  have hcond : ∀ s : PushoutCocone (ougSq2f G H) ougSq2g.{u},
      ∀ z w : ULift.{u} ℤ,
      s.inl.toAddHom (z.down • G.unit, w.down • H.unit)
        = s.inr.toAddHom z := by
    intro s z w
    exact ((oug_comp_apply (ougSq2f G H) s.inl (z, w)).symm.trans
      (oug_congr s.condition (z, w))).trans
      (oug_comp_apply ougSq2g.{u} s.inr (z, w))
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s => ougMed2 s.inl s.inr (hcond s)) ?_ ?_ ?_)
  · intro s
    exact oug_hom_ext fun p =>
      (oug_comp_apply (ougSq2h G H) _ p).trans
        (ougMed2_fac_left _ _ (hcond s) p)
  · intro s
    exact oug_hom_ext fun z =>
      (oug_comp_apply (ougSq2i G) _ z).trans
        (ougMed2_fac_right _ _ (hcond s) z)
  · intro s m h₁ _
    exact ougMed2_uniq _ _ (hcond s) m
      (fun p => (oug_comp_apply (ougSq2h G H) m p).symm.trans (oug_congr h₁ p))

/-! ### Joint monicity of the two cotuples in `OUGᵒᵖ` -/

/-- **The third axiom of 180I in `OUGᵒᵖ`**: a positive unit-preserving
homomorphism out of `ℤ³` is determined by its restrictions along
`(x,y) ↦ (x,y,y)` and `(x,y) ↦ (y,x,y)`, because `ℤ³` is free abelian on
the three coordinate units. -/
theorem oug_jointlyMonic_aux {K : OUG.{u}}
    (a b : (ougScal.{u}.prod ougScal.{u}).prod ougScal.{u} ⟶ K)
    (h1 : ∀ x : ULift.{u} ℤ × ULift.{u} ℤ,
      a.toAddHom ((x.1, x.2), x.2) = b.toAddHom ((x.1, x.2), x.2))
    (h2 : ∀ x : ULift.{u} ℤ × ULift.{u} ℤ,
      a.toAddHom ((x.2, x.1), x.2) = b.toAddHom ((x.2, x.1), x.2)) :
    a = b := by
  set e₁ : (ULift.{u} ℤ × ULift.{u} ℤ) × ULift.{u} ℤ := ((1, 0), 0) with he₁
  set e₂ : (ULift.{u} ℤ × ULift.{u} ℤ) × ULift.{u} ℤ := ((0, 1), 0) with he₂
  set e₃ : (ULift.{u} ℤ × ULift.{u} ℤ) × ULift.{u} ℤ := ((0, 0), 1) with he₃
  have ha1 : a.toAddHom e₁ = b.toAddHom e₁ := h1 (1, 0)
  have ha2 : a.toAddHom e₂ = b.toAddHom e₂ := h2 (1, 0)
  have ha3 : a.toAddHom e₃ = b.toAddHom e₃ := by
    have h4 := h1 (0, 1)
    have hsum : (((0 : ULift.{u} ℤ), (1 : ULift.{u} ℤ)), (1 : ULift.{u} ℤ))
        = e₂ + e₃ := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [he₂, he₃]
    rw [hsum, map_add, map_add, ha2] at h4
    exact add_left_cancel h4
  have key : ∀ (f : (ougScal.{u}.prod ougScal.{u}).prod ougScal.{u} ⟶ K)
      (y : (ULift.{u} ℤ × ULift.{u} ℤ) × ULift.{u} ℤ),
      f.toAddHom y = y.1.1.down • f.toAddHom e₁
        + (y.1.2.down • f.toAddHom e₂ + y.2.down • f.toAddHom e₃) := by
    intro f y
    have hdec : y = y.1.1.down • e₁ + (y.1.2.down • e₂ + y.2.down • e₃) := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;>
        · apply ULift.down_injective
          simp [he₁, he₂, he₃]
    conv_lhs => rw [hdec]
    rw [map_add, map_zsmul, map_add, map_zsmul, map_zsmul]
  refine oug_hom_ext fun y => ?_
  rw [key a y, key b y, ha1, ha2, ha3]

/-! ### `OUGᵒᵖ` is an effectus -/

/-- **189aII.2** (`effexamplesintro`, eff.tex:2037, Examples): the
category `OUGᵒᵖ` of order unit groups with positive unit-preserving
homomorphisms in the opposite direction is an effectus in total form.

The point gives no proof.  Ours is the argument of `effectus_ous` with the
ordered real vector space replaced by a partially ordered abelian group:
`ℤ` is initial in `OUG`, the products are the coproducts of `OUGᵒᵖ`
(`ougPres`), and the three axioms of 180I are `oug_isPushout1`,
`oug_isPushout2` and `oug_jointlyMonic_aux`.  No scalar action is used
anywhere; the order-unit axiom does the work the norm did for von Neumann
algebras. -/
theorem effectus_oug : Nonempty (EffectusTotalStructure OUG.{u}ᵒᵖ) := by
  have : HasTerminal (OUG.{u}ᵒᵖ) := ougPres.hT.hasTerminal
  have : HasInitial (OUG.{u}ᵒᵖ) :=
    (IsTerminal.op (OUG.{u}) ougTrivIsTerminal).hasInitial
  have : ∀ G H : OUG.{u}ᵒᵖ, HasColimit (pair G H) := fun G H =>
    HasColimit.mk ⟨_, ougPres.hP G H⟩
  have : HasBinaryCoproducts (OUG.{u}ᵒᵖ) :=
    hasBinaryCoproducts_of_hasColimit_pair _
  have : HasFiniteCoproducts (OUG.{u}ᵒᵖ) :=
    hasFiniteCoproducts_of_has_binary_and_initial
  refine ⟨{ hasFiniteCoproducts := inferInstance
            hasTerminal := inferInstance
            effectus := effectusTotalForm_of_pres ougPres ?_ ?_ ?_ }⟩
  · intro G H
    have e₁ : ougPres.pmap (𝟙 G) (ougPres.hT.from H)
        = Quiver.Hom.op (ougSq1i G.unop H.unop) := by
      refine ougop_hom_ext fun p => (ougPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext rfl ?_
      exact ougPres_from_apply H p.2
    have e₂ : ougPres.pmap (ougPres.hT.from G) (𝟙 H)
        = Quiver.Hom.op (ougSq1h G.unop H.unop) := by
      refine ougop_hom_ext fun p => (ougPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ rfl
      exact ougPres_from_apply G p.1
    have e₃ : ougPres.pmap (ougPres.hT.from G) (𝟙 ougPres.T)
        = Quiver.Hom.op (ougSq1g G.unop) := by
      refine ougop_hom_ext fun p => (ougPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ rfl
      exact ougPres_from_apply G p.1
    have e₄ : ougPres.pmap (𝟙 ougPres.T) (ougPres.hT.from H)
        = Quiver.Hom.op (ougSq1f H.unop) := by
      refine ougop_hom_ext fun p => (ougPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext rfl ?_
      exact ougPres_from_apply H p.2
    rw [e₁, e₂, e₃, e₄]
    exact (oug_isPushout1 G.unop H.unop).op
  · intro G H
    have f₁ : ougPres.hT.from G = Quiver.Hom.op (ougSq2i G.unop) :=
      ougPres.hT.hom_ext _ _
    have f₄ : ougPres.pmap (ougPres.hT.from G) (ougPres.hT.from H)
        = Quiver.Hom.op (ougSq2f G.unop H.unop) := by
      refine ougop_hom_ext fun p => (ougPres_pmap_apply _ _ p).trans ?_
      refine Prod.ext ?_ ?_
      · exact ougPres_from_apply G p.1
      · exact ougPres_from_apply H p.2
    rw [f₄, f₁]
    exact (oug_isPushout2 G.unop H.unop).op
  · intro Z a b hf hg
    apply Quiver.Hom.unop_inj
    refine oug_jointlyMonic_aux a.unop b.unop (fun x => ?_) (fun x => ?_)
    · exact ougop_comp_congr hf x
    · exact ougop_comp_congr hg x

end

end Theses.B.Eff
