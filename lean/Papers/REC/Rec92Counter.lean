/-
Papers/REC/Rec92Counter.lean

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707 (2021): **REC 92** (`prop:predsep-splits`,
short.tex:1643) is false as printed for an effectus separated by *predicates*.

The counterexample `LinkedPts` ("linked points"), from
`docs/research/review-rec92.md`: objects are triples `X = (a, l, r)` of finite
sets, with `X₁ = a ⊔ l` and `X₂ = a ⊔ r`; a map `f : X → Y` is a pair of
partial functions `f₁ : X₁ ⇀ Y₁`, `f₂ : X₂ ⇀ Y₂` with `f₁⁻¹(y) = f₂⁻¹(y) ⊆ a_X`
for every linked point `y ∈ a_Y`.  It is a subcategory of `Pfn × Pfn`, an
effectus in partial form with unit `I = (∅, 1, 1)` and `Pred(X) = 2^{X₁} × 2^{X₂}`,
separated by predicates (not by states), with images, filters, comprehensions,
compatible filters and comprehensions, and scalars `{0,1}²`.  For the idempotent
scalar `s = (1, 0)` and the one-linked-point object `A = (1, ∅, ∅)` the predicate
`s ∘ 1_A = (1, ∅)` is not sharp, and `LinkedPts` is not equivalent — even as a
bare category — to a product of two non-trivial effectuses
(`linkedPts_not_equiv_prod`): `End(A) = {0, id}` forces `A` into one factor,
and `A` has a non-zero map to every object with a point.

Design: a map is stored as its two partial functions (`Option`-valued), with
the link condition as three `Prop` fields (`hl`, `hr`, `ha`); coproducts are
explicit (`ExplicitCoproducts.finPAC_of`, as for `BoolMat` in
`Papers/REC/Decompose.lean`).
-/
import Papers.REC.Decompose

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

open CategoryTheory
open CategoryTheory.Limits hiding HasImages
open Theses.B.Eff

namespace Papers.REC

universe u₁ u₂ v₁ v₂

/-! ## Option helpers -/

section OptionHelpers

variable {α β : Type*}

theorem opt_or_eq_some {o p : Option α} {a : α} (h : o = none ∨ p = none) :
    o.or p = some a ↔ o = some a ∨ p = some a := by
  rcases o with _ | o <;> rcases p with _ | p <;> simp_all

theorem opt_or_comm {o p : Option α} (h : o = none ∨ p = none) : o.or p = p.or o := by
  rcases o with _ | o <;> rcases p with _ | p <;> simp_all

theorem opt_or_assoc (o p q : Option α) : (o.or p).or q = o.or (p.or q) := by
  rcases o with _ | o <;> rfl

theorem opt_perp_of_or {o p q : Option α} (h : o.or p = none ∨ q = none) :
    p = none ∨ q = none := by
  rcases o with _ | o <;> rcases p with _ | p <;> simp_all

theorem opt_perp_or {o p q : Option α} (h₁ : o = none ∨ p = none)
    (h₂ : o.or p = none ∨ q = none) : o = none ∨ p.or q = none := by
  rcases o with _ | o <;> rcases p with _ | p <;> rcases q with _ | q <;> simp_all

theorem opt_or_bind {o p : Option α} (k : α → Option β) (h : o = none ∨ p = none) :
    (o.or p).bind k = (o.bind k).or (p.bind k) := by
  rcases o with _ | o <;> rcases p with _ | p <;> simp_all

theorem opt_bind_or (o : Option α) (k k' : α → Option β) :
    o.bind (fun x => (k x).or (k' x)) = (o.bind k).or (o.bind k') := by
  rcases o with _ | o <;> rfl

theorem opt_bind_perp {o p : Option α} (k : α → Option β) (h : o = none ∨ p = none) :
    o.bind k = none ∨ p.bind k = none := by
  rcases h with h | h <;> simp [h]

theorem opt_bind_some (o : Option α) : o.bind some = o := by
  rcases o with _ | o <;> rfl

theorem opt_bind_assoc (o : Option α) {γ : Type*} (k : α → Option β) (k' : β → Option γ) :
    (o.bind k).bind k' = o.bind (fun x => (k x).bind k') := by
  rcases o with _ | o <;> rfl

theorem opt_bind_const_eq_none {γ : Type*} (o : Option α) (c : γ) :
    o.bind (fun _ => some c) = none ↔ o = none := by
  rcases o with _ | o <;> simp

/-- Values in `Option (Empty ⊕ Unit)` are determined by whether they are `none`. -/
theorem eu_eq : ∀ v w : Option (Empty ⊕ Unit), (v = none ↔ w = none) → v = w := by
  rintro (_ | (e | ⟨⟩)) (_ | (e' | ⟨⟩)) h
  all_goals first | rfl | exact e.elim | exact e'.elim | simp at h

end OptionHelpers

/-! ## The category `LinkedPts` -/

/-- The objects: triples `(a, l, r)` of finite sets — the linked points `a`,
present in both components, the left points `l` and the right points `r`. -/
structure LinkedPts : Type 1 where
  a : Type
  l : Type
  r : Type
  [fa : Finite a]
  [fl : Finite l]
  [fr : Finite r]

attribute [instance] LinkedPts.fa LinkedPts.fl LinkedPts.fr

namespace LinkedPts

/-- The maps: pairs of partial functions `f₁ : a ⊔ l ⇀ a' ⊔ l'`,
`f₂ : a ⊔ r ⇀ a' ⊔ r'` with `f₁⁻¹(y) = f₂⁻¹(y) ⊆ a` for each linked `y ∈ a'`. -/
@[ext] structure Hom (X Y : LinkedPts) where
  f₁ : X.a ⊕ X.l → Option (Y.a ⊕ Y.l)
  f₂ : X.a ⊕ X.r → Option (Y.a ⊕ Y.r)
  hl : ∀ (x : X.l) (y : Y.a), f₁ (.inr x) ≠ some (.inl y)
  hr : ∀ (x : X.r) (y : Y.a), f₂ (.inr x) ≠ some (.inl y)
  ha : ∀ (x : X.a) (y : Y.a), f₁ (.inl x) = some (.inl y) ↔ f₂ (.inl x) = some (.inl y)

/-- Composition: componentwise composition of partial functions. -/
def Hom.comp {X Y Z : LinkedPts} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  f₁ x := (f.f₁ x).bind g.f₁
  f₂ x := (f.f₂ x).bind g.f₂
  hl x z h := by
    rcases hx : f.f₁ (.inr x) with _ | (y | y)
    · simp [hx] at h
    · exact f.hl x y hx
    · simp only [hx, Option.bind_some] at h
      exact g.hl y z h
  hr x z h := by
    rcases hx : f.f₂ (.inr x) with _ | (y | y)
    · simp [hx] at h
    · exact f.hr x y hx
    · simp only [hx, Option.bind_some] at h
      exact g.hr y z h
  ha x z := by
    constructor
    · intro h
      rcases hx : f.f₁ (.inl x) with _ | (y | y)
      · simp [hx] at h
      · simp only [hx, Option.bind_some] at h
        rw [(f.ha x y).1 hx, Option.bind_some]
        exact (g.ha y z).1 h
      · simp only [hx, Option.bind_some] at h
        exact absurd h (g.hl y z)
    · intro h
      rcases hx : f.f₂ (.inl x) with _ | (y | y)
      · simp [hx] at h
      · simp only [hx, Option.bind_some] at h
        rw [(f.ha x y).2 hx, Option.bind_some]
        exact (g.ha y z).2 h
      · simp only [hx, Option.bind_some] at h
        exact absurd h (g.hr y z)

/-- The identity: the pair of identities. -/
def Hom.id (X : LinkedPts) : Hom X X where
  f₁ := some
  f₂ := some
  hl _ _ h := by cases h
  hr _ _ h := by cases h
  ha _ _ := by simp

instance category : Category.{0} LinkedPts where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext rfl rfl
  comp_id f := Hom.ext (funext fun x => opt_bind_some (f.f₁ x))
    (funext fun x => opt_bind_some (f.f₂ x))
  assoc f g h := Hom.ext (funext fun x => opt_bind_assoc (f.f₁ x) g.f₁ h.f₁)
    (funext fun x => opt_bind_assoc (f.f₂ x) g.f₂ h.f₂)

@[simp] theorem comp_f₁ {X Y Z : LinkedPts} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.a ⊕ X.l) :
    Hom.f₁ (f ≫ g) x = (Hom.f₁ f x).bind (Hom.f₁ g) := rfl

@[simp] theorem comp_f₂ {X Y Z : LinkedPts} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.a ⊕ X.r) :
    Hom.f₂ (f ≫ g) x = (Hom.f₂ f x).bind (Hom.f₂ g) := rfl

@[simp] theorem id_f₁ (X : LinkedPts) (x : X.a ⊕ X.l) : Hom.f₁ (𝟙 X) x = some x := rfl

@[simp] theorem id_f₂ (X : LinkedPts) (x : X.a ⊕ X.r) : Hom.f₂ (𝟙 X) x = some x := rfl

theorem hom_ext {X Y : LinkedPts} {f g : X ⟶ Y} (h₁ : ∀ x, Hom.f₁ f x = Hom.f₁ g x)
    (h₂ : ∀ x, Hom.f₂ f x = Hom.f₂ g x) : f = g :=
  Hom.ext (funext h₁) (funext h₂)

/-! ### Explicit coproducts -/

/-- The coproduct `(a ⊔ a', l ⊔ l', r ⊔ r')`. -/
abbrev sumObj (X Y : LinkedPts) : LinkedPts := ⟨X.a ⊕ Y.a, X.l ⊕ Y.l, X.r ⊕ Y.r⟩

/-- The first coprojection. -/
def inl (X Y : LinkedPts) : X ⟶ sumObj X Y :=
  (⟨fun x => some (Sum.map .inl .inl x), fun x => some (Sum.map .inl .inl x),
    fun _ _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ => (by simp)⟩ :
    Hom X (sumObj X Y))

/-- The second coprojection. -/
def inr (X Y : LinkedPts) : Y ⟶ sumObj X Y :=
  (⟨fun x => some (Sum.map .inr .inr x), fun x => some (Sum.map .inr .inr x),
    fun _ _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ => (by simp)⟩ :
    Hom Y (sumObj X Y))

/-- The cotuple. -/
def desc {X Y T : LinkedPts} (f : X ⟶ T) (g : Y ⟶ T) : sumObj X Y ⟶ T :=
  (⟨fun
      | .inl (.inl a) => Hom.f₁ f (.inl a)
      | .inl (.inr a) => Hom.f₁ g (.inl a)
      | .inr (.inl x) => Hom.f₁ f (.inr x)
      | .inr (.inr x) => Hom.f₁ g (.inr x),
    fun
      | .inl (.inl a) => Hom.f₂ f (.inl a)
      | .inl (.inr a) => Hom.f₂ g (.inl a)
      | .inr (.inl x) => Hom.f₂ f (.inr x)
      | .inr (.inr x) => Hom.f₂ g (.inr x),
    (by rintro (x | x) y; exacts [f.hl x y, g.hl x y]),
    (by rintro (x | x) y; exacts [f.hr x y, g.hr x y]),
    (by rintro (x | x) y; exacts [f.ha x y, g.ha x y])⟩ : Hom (sumObj X Y) T)

/-- The empty object. -/
abbrev initObj : LinkedPts := ⟨Empty, Empty, Empty⟩

/-- The unique map out of the empty object. -/
def fromInit (T : LinkedPts) : initObj ⟶ T :=
  (⟨fun x => by rcases x with x | x <;> exact x.elim,
    fun x => by rcases x with x | x <;> exact x.elim,
    fun x => x.elim, fun x => x.elim, fun x => x.elim⟩ : Hom initObj T)

def explicit : ExplicitCoproducts LinkedPts where
  pt := sumObj
  inl := inl
  inr := inr
  desc := desc
  inl_desc _ _ := hom_ext (by rintro (x | x) <;> rfl) (by rintro (x | x) <;> rfl)
  inr_desc _ _ := hom_ext (by rintro (x | x) <;> rfl) (by rintro (x | x) <;> rfl)
  uniq _ := hom_ext (by rintro ((x | x) | (x | x)) <;> rfl)
    (by rintro ((x | x) | (x | x)) <;> rfl)
  init := initObj
  isInitial := IsInitial.ofUniqueHom fromInit
    (fun _ _ => hom_ext (by rintro (x | x) <;> exact x.elim)
      (by rintro (x | x) <;> exact x.elim))

instance hasFiniteCoproducts : HasFiniteCoproducts LinkedPts :=
  explicit.hasFiniteCoproducts

/-! ### The PCM enrichment: disjoint domains, union -/

/-- The zero map. -/
def zeroHom (X Y : LinkedPts) : X ⟶ Y :=
  (⟨fun _ => none, fun _ => none, fun _ _ h => (by cases h), fun _ _ h => (by cases h),
    fun _ _ => (by simp)⟩ : Hom X Y)

/-- Two maps are orthogonal when their domains are disjoint in each component. -/
def Orth {X Y : LinkedPts} (f g : X ⟶ Y) : Prop :=
  (∀ x, Hom.f₁ f x = none ∨ Hom.f₁ g x = none) ∧ (∀ x, Hom.f₂ f x = none ∨ Hom.f₂ g x = none)

/-- The sum of orthogonal maps: the union. -/
def oveeHom {X Y : LinkedPts} (f g : X ⟶ Y) (h : Orth f g) : X ⟶ Y :=
  (⟨fun x => (Hom.f₁ f x).or (Hom.f₁ g x), fun x => (Hom.f₂ f x).or (Hom.f₂ g x),
    fun x y hx => by
      rcases (opt_or_eq_some (h.1 _)).1 hx with hx | hx
      exacts [f.hl x y hx, g.hl x y hx],
    fun x y hx => by
      rcases (opt_or_eq_some (h.2 _)).1 hx with hx | hx
      exacts [f.hr x y hx, g.hr x y hx],
    fun x y => by
      rw [opt_or_eq_some (h.1 _), opt_or_eq_some (h.2 _), f.ha, g.ha]⟩ : Hom X Y)

instance homPCM (X Y : LinkedPts) : PCM (X ⟶ Y) where
  zero := zeroHom X Y
  Perp := Orth
  ovee := oveeHom
  perp_comm h := ⟨fun x => (h.1 x).symm, fun x => (h.2 x).symm⟩
  ovee_comm h := hom_ext (fun x => opt_or_comm (h.1 x)) (fun x => opt_or_comm (h.2 x))
  perp_of_ovee_perp _ h := ⟨fun x => opt_perp_of_or (h.1 x), fun x => opt_perp_of_or (h.2 x)⟩
  perp_ovee_of_ovee_perp hab h :=
    ⟨fun x => opt_perp_or (hab.1 x) (h.1 x), fun x => opt_perp_or (hab.2 x) (h.2 x)⟩
  ovee_assoc _ _ := hom_ext (fun _ => opt_or_assoc _ _ _) (fun _ => opt_or_assoc _ _ _)
  zero_perp _ := ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩
  zero_ovee _ := hom_ext (fun _ => rfl) (fun _ => rfl)

@[simp] theorem zero_f₁ {X Y : LinkedPts} (x : X.a ⊕ X.l) :
    Hom.f₁ (0 : X ⟶ Y) x = none := rfl

@[simp] theorem zero_f₂ {X Y : LinkedPts} (x : X.a ⊕ X.r) :
    Hom.f₂ (0 : X ⟶ Y) x = none := rfl

theorem perp_iff {X Y : LinkedPts} (f g : X ⟶ Y) : Perp f g ↔ Orth f g := Iff.rfl

@[simp] theorem ovee_f₁ {X Y : LinkedPts} {f g : X ⟶ Y} (h : Perp f g) (x : X.a ⊕ X.l) :
    Hom.f₁ (ovee f g h : X ⟶ Y) x = (Hom.f₁ f x).or (Hom.f₁ g x) := rfl

@[simp] theorem ovee_f₂ {X Y : LinkedPts} {f g : X ⟶ Y} (h : Perp f g) (x : X.a ⊕ X.r) :
    Hom.f₂ (ovee f g h : X ⟶ Y) x = (Hom.f₂ f x).or (Hom.f₂ g x) := rfl

instance finPAC : FinPAC LinkedPts :=
  explicit.finPAC_of
    (fun {_ _ _ f g} h k =>
      ⟨⟨fun x => opt_bind_perp _ (h.1 x), fun x => opt_bind_perp _ (h.2 x)⟩,
        hom_ext (fun x => opt_or_bind _ (h.1 x)) (fun x => opt_or_bind _ (h.2 x))⟩)
    (fun {_ _ _ f g} h k =>
      ⟨⟨fun w => by
          rcases hk : Hom.f₁ k w with _ | x
          · simp [hk]
          · simpa [hk] using h.1 x,
        fun w => by
          rcases hk : Hom.f₂ k w with _ | x
          · simp [hk]
          · simpa [hk] using h.2 x⟩,
        hom_ext (fun w => opt_bind_or _ _ _) (fun w => opt_bind_or _ _ _)⟩)
    (fun f => hom_ext
      (fun x => by
        show (Hom.f₁ f x).bind (fun _ => none) = none
        rcases Hom.f₁ f x with _ | y <;> rfl)
      (fun x => by
        show (Hom.f₂ f x).bind (fun _ => none) = none
        rcases Hom.f₂ f x with _ | y <;> rfl))
    (fun _ => hom_ext (fun _ => rfl) (fun _ => rfl))
    (fun {_ Y} b => ⟨fun x => by
        show (Hom.f₁ b x).bind (Hom.f₁ (desc (𝟙 Y) 0)) = none ∨
          (Hom.f₁ b x).bind (Hom.f₁ (desc 0 (𝟙 Y))) = none
        rcases Hom.f₁ b x with _ | ((y | y) | (y | y)) <;>
          first | exact Or.inl rfl | exact Or.inr rfl,
      fun x => by
        show (Hom.f₂ b x).bind (Hom.f₂ (desc (𝟙 Y) 0)) = none ∨
          (Hom.f₂ b x).bind (Hom.f₂ (desc 0 (𝟙 Y))) = none
        rcases Hom.f₂ b x with _ | ((y | y) | (y | y)) <;>
          first | exact Or.inl rfl | exact Or.inr rfl⟩)
    (fun h => ⟨fun x => by rcases h.1 x with h' | h' <;> simp [h'],
      fun x => by rcases h.2 x with h' | h' <;> simp [h']⟩)

/-! ### The effects: `I = (∅, 1, 1)`, `Pred(X) = 2^{X₁} × 2^{X₂}` -/

/-- The unit object `I = (∅, 1, 1)`: one left and one right point. -/
abbrev unitObj : LinkedPts := ⟨Empty, Unit, Unit⟩

/-- The value "true" of a predicate. -/
abbrev tt : Option (Empty ⊕ Unit) := some (.inr ())

/-- Complement of a predicate value. -/
def neg : Option (Empty ⊕ Unit) → Option (Empty ⊕ Unit)
  | none => tt
  | some _ => none

/-- A predicate from two subsets. -/
noncomputable def mkPred {X : LinkedPts} (P₁ : X.a ⊕ X.l → Prop) (P₂ : X.a ⊕ X.r → Prop) :
    X ⟶ unitObj := by
  classical
  exact (⟨fun x => if P₁ x then tt else none, fun x => if P₂ x then tt else none,
    fun _ y => y.elim, fun _ y => y.elim, fun _ y => y.elim⟩ : Hom X unitObj)

theorem mkPred_f₁ {X : LinkedPts} (P₁ : X.a ⊕ X.l → Prop) (P₂ : X.a ⊕ X.r → Prop)
    (x : X.a ⊕ X.l) : Hom.f₁ (mkPred P₁ P₂) x = none ↔ ¬ P₁ x := by
  classical
  unfold mkPred
  show (if P₁ x then tt else none) = none ↔ _
  split_ifs with h <;> simp [h]

theorem mkPred_f₂ {X : LinkedPts} (P₁ : X.a ⊕ X.l → Prop) (P₂ : X.a ⊕ X.r → Prop)
    (x : X.a ⊕ X.r) : Hom.f₂ (mkPred P₁ P₂) x = none ↔ ¬ P₂ x := by
  classical
  unfold mkPred
  show (if P₂ x then tt else none) = none ↔ _
  split_ifs with h <;> simp [h]

instance effectus : EffectusPartialForm LinkedPts where
  I := unitObj
  one X := (⟨fun _ => tt, fun _ => tt, fun _ y => y.elim, fun _ y => y.elim,
    fun _ y => y.elim⟩ : Hom X unitObj)
  orth {X} p := (⟨fun x => neg (Hom.f₁ p x), fun x => neg (Hom.f₂ p x), fun _ y => y.elim,
    fun _ y => y.elim, fun _ y => y.elim⟩ : Hom X unitObj)
  perp_orth p := ⟨fun x => by
      show Hom.f₁ p x = none ∨ neg (Hom.f₁ p x) = none
      rcases Hom.f₁ p x with _ | v <;> simp [neg],
    fun x => by
      show Hom.f₂ p x = none ∨ neg (Hom.f₂ p x) = none
      rcases Hom.f₂ p x with _ | v <;> simp [neg]⟩
  ovee_orth p := hom_ext
    (fun x => by
      show (Hom.f₁ p x).or (neg (Hom.f₁ p x)) = tt
      rcases Hom.f₁ p x with _ | (e | ⟨⟩)
      · rfl
      · exact e.elim
      · rfl)
    (fun x => by
      show (Hom.f₂ p x).or (neg (Hom.f₂ p x)) = tt
      rcases Hom.f₂ p x with _ | (e | ⟨⟩)
      · rfl
      · exact e.elim
      · rfl)
  orth_unique {X p q} h e := hom_ext
    (fun x => by
      have e1 : (Hom.f₁ p x).or (Hom.f₁ q x) = tt := congrFun (congrArg Hom.f₁ e) x
      have h1 := h.1 x
      show Hom.f₁ q x = neg (Hom.f₁ p x)
      revert e1 h1
      rcases Hom.f₁ p x with _ | (e | ⟨⟩) <;> rcases Hom.f₁ q x with _ | (e' | ⟨⟩) <;>
        simp [neg])
    (fun x => by
      have e1 : (Hom.f₂ p x).or (Hom.f₂ q x) = tt := congrFun (congrArg Hom.f₂ e) x
      have h1 := h.2 x
      show Hom.f₂ q x = neg (Hom.f₂ p x)
      revert e1 h1
      rcases Hom.f₂ p x with _ | (e | ⟨⟩) <;> rcases Hom.f₂ q x with _ | (e' | ⟨⟩) <;>
        simp [neg])
  eq_zero_of_perp_one {X p} h := hom_ext
    (fun x => by rcases h.1 x with h' | h'; exacts [h', absurd h' (by simp)])
    (fun x => by rcases h.2 x with h' | h'; exacts [h', absurd h' (by simp)])
  perp_of_one_perp {X Y f g} h :=
    ⟨fun x => by
      have := h.1 x
      simp only [comp_f₁] at this
      exact this.elim
        (fun h' => Or.inl ((opt_bind_const_eq_none _ (Sum.inr () : Empty ⊕ Unit)).1 h'))
        (fun h' => Or.inr ((opt_bind_const_eq_none _ (Sum.inr () : Empty ⊕ Unit)).1 h')),
      fun x => by
      have := h.2 x
      simp only [comp_f₂] at this
      exact this.elim
        (fun h' => Or.inl ((opt_bind_const_eq_none _ (Sum.inr () : Empty ⊕ Unit)).1 h'))
        (fun h' => Or.inr ((opt_bind_const_eq_none _ (Sum.inr () : Empty ⊕ Unit)).1 h'))⟩
  eq_zero_of_one_zero {X Y f} h := hom_ext
    (fun x => (opt_bind_const_eq_none _ (Sum.inr () : Empty ⊕ Unit)).1
      (congrFun (congrArg Hom.f₁ h) x))
    (fun x => (opt_bind_const_eq_none _ (Sum.inr () : Empty ⊕ Unit)).1
      (congrFun (congrArg Hom.f₂ h) x))

/-! ### Predicates -/

@[simp] theorem truth_f₁ (X : LinkedPts) (x : X.a ⊕ X.l) : Hom.f₁ (truth X) x = tt := rfl

@[simp] theorem truth_f₂ (X : LinkedPts) (x : X.a ⊕ X.r) : Hom.f₂ (truth X) x = tt := rfl

theorem opt_or_eq_none {α : Type*} (o p : Option α) : o.or p = none ↔ o = none ∧ p = none := by
  rcases o with _ | o <;> simp

theorem comp_truth_f₁ {X B : LinkedPts} (f : X ⟶ B) (x : X.a ⊕ X.l) :
    Hom.f₁ (f ≫ truth B) x = none ↔ Hom.f₁ f x = none := by
  show (Hom.f₁ f x).bind (fun _ => tt) = none ↔ _
  rcases Hom.f₁ f x with _ | y <;> simp

theorem comp_truth_f₂ {X B : LinkedPts} (f : X ⟶ B) (x : X.a ⊕ X.r) :
    Hom.f₂ (f ≫ truth B) x = none ↔ Hom.f₂ f x = none := by
  show (Hom.f₂ f x).bind (fun _ => tt) = none ↔ _
  rcases Hom.f₂ f x with _ | y <;> simp

/-- The order on `Pred(X) = 2^{X₁} × 2^{X₂}` is inclusion. -/
theorem pred_le_iff {X : LinkedPts} (p q : Pred X) :
    p ≼ q ↔ (∀ x, Hom.f₁ p x ≠ none → Hom.f₁ q x ≠ none) ∧
      (∀ x, Hom.f₂ p x ≠ none → Hom.f₂ q x ≠ none) := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun x hx h => hx ((opt_or_eq_none _ _).1 h).1,
      fun x hx h => hx ((opt_or_eq_none _ _).1 h).1⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨mkPred (fun x => Hom.f₁ q x ≠ none ∧ Hom.f₁ p x = none)
      (fun x => Hom.f₂ q x ≠ none ∧ Hom.f₂ p x = none), ⟨fun x => ?_, fun x => ?_⟩,
      hom_ext (fun x => ?_) (fun x => ?_)⟩
    · by_cases hp : Hom.f₁ p x = none
      · exact Or.inl hp
      · exact Or.inr ((mkPred_f₁ _ _ x).2 fun h => hp h.2)
    · by_cases hp : Hom.f₂ p x = none
      · exact Or.inl hp
      · exact Or.inr ((mkPred_f₂ _ _ x).2 fun h => hp h.2)
    · show (Hom.f₁ p x).or (Hom.f₁ (mkPred _ _) x) = Hom.f₁ q x
      refine eu_eq _ _ ?_
      rw [opt_or_eq_none, mkPred_f₁]
      constructor
      · rintro ⟨hp, hm⟩
        by_contra hq
        exact hm ⟨hq, hp⟩
      · intro hq
        exact ⟨by_contra fun hp => h₁ x hp hq, fun h => h.1 hq⟩
    · show (Hom.f₂ p x).or (Hom.f₂ (mkPred _ _) x) = Hom.f₂ q x
      refine eu_eq _ _ ?_
      rw [opt_or_eq_none, mkPred_f₂]
      constructor
      · rintro ⟨hp, hm⟩
        by_contra hq
        exact hm ⟨hq, hp⟩
      · intro hq
        exact ⟨by_contra fun hp => h₂ x hp hq, fun h => h.1 hq⟩

/-- `1 ∘ f ≤ p`, pointwise: the domain of `f` lies in `p`. -/
theorem supp_of_le {X B : LinkedPts} (f : X ⟶ B) (p : Pred X) (h : (f ≫ truth B) ≼ p) :
    (∀ x, Hom.f₁ f x ≠ none → Hom.f₁ p x ≠ none) ∧
      (∀ x, Hom.f₂ f x ≠ none → Hom.f₂ p x ≠ none) := by
  obtain ⟨k₁, k₂⟩ := (pred_le_iff _ _).1 h
  exact ⟨fun x hx => k₁ x fun h' => hx ((comp_truth_f₁ f x).1 h'),
    fun x hx => k₂ x fun h' => hx ((comp_truth_f₂ f x).1 h')⟩

/-- `p ∘ f = 1 ∘ f`, pointwise: the range of `f` lies in `p`. -/
theorem lands_iff {Y X : LinkedPts} (f : Y ⟶ X) (p : Pred X) :
    f ≫ p = f ≫ truth X ↔ (∀ y x, Hom.f₁ f y = some x → Hom.f₁ p x ≠ none) ∧
      (∀ y x, Hom.f₂ f y = some x → Hom.f₂ p x ≠ none) := by
  constructor
  · intro h
    refine ⟨fun y x hy hp => ?_, fun y x hy hp => ?_⟩
    · have e := congrFun (congrArg Hom.f₁ h) y
      rw [comp_f₁, comp_f₁, hy, Option.bind_some, Option.bind_some, hp] at e
      cases e
    · have e := congrFun (congrArg Hom.f₂ h) y
      rw [comp_f₂, comp_f₂, hy, Option.bind_some, Option.bind_some, hp] at e
      cases e
  · rintro ⟨h₁, h₂⟩
    refine hom_ext (fun y => eu_eq _ _ ?_) (fun y => eu_eq _ _ ?_)
    · rw [comp_f₁, comp_f₁]
      rcases hy : Hom.f₁ f y with _ | x
      · simp
      · simp only [Option.bind_some, truth_f₁]
        simpa using h₁ y x hy
    · rw [comp_f₂, comp_f₂]
      rcases hy : Hom.f₂ f y with _ | x
      · simp
      · simp only [Option.bind_some, truth_f₂]
        simpa using h₂ y x hy

/-- **Separated by predicates**: the singleton predicates recover both partial
functions. -/
theorem separatingPredicates : SeparatingPredicates LinkedPts := by
  intro Y X f g h
  refine hom_ext (fun y => Option.ext fun x => ?_) (fun y => Option.ext fun x => ?_)
  · have hk : ∀ o : Option (X.a ⊕ X.l),
        o.bind (Hom.f₁ (mkPred (fun z => z = x) (fun _ => False))) = none ↔ ¬ o = some x := by
      intro o
      rcases o with _ | z
      · simp
      · rw [Option.bind_some, mkPred_f₁]
        simp
    have e := congrFun (congrArg Hom.f₁ (h (mkPred (fun z => z = x) (fun _ => False)))) y
    rw [comp_f₁, comp_f₁] at e
    show Hom.f₁ f y = some x ↔ Hom.f₁ g y = some x
    rw [← not_iff_not, ← hk, ← hk, e]
  · have hk : ∀ o : Option (X.a ⊕ X.r),
        o.bind (Hom.f₂ (mkPred (fun _ => False) (fun z => z = x))) = none ↔ ¬ o = some x := by
      intro o
      rcases o with _ | z
      · simp
      · rw [Option.bind_some, mkPred_f₂]
        simp
    have e := congrFun (congrArg Hom.f₂ (h (mkPred (fun _ => False) (fun z => z = x)))) y
    rw [comp_f₂, comp_f₂] at e
    show Hom.f₂ f y = some x ↔ Hom.f₂ g y = some x
    rw [← not_iff_not, ← hk, ← hk, e]

/-! ### Images -/

/-- The image `im f = (ran f₁, ran f₂)`. -/
noncomputable def imP {Y X : LinkedPts} (f : Y ⟶ X) : Pred X :=
  mkPred (fun x => ∃ y, Hom.f₁ f y = some x) (fun x => ∃ y, Hom.f₂ f y = some x)

theorem isImage_imP {Y X : LinkedPts} (f : Y ⟶ X) : IsImage f (imP f) := by
  refine ⟨(lands_iff f _).2 ⟨fun y x hy => (mkPred_f₁ _ _ x).not.2 (not_not.2 ⟨y, hy⟩),
    fun y x hy => (mkPred_f₂ _ _ x).not.2 (not_not.2 ⟨y, hy⟩)⟩, fun q hq => ?_⟩
  obtain ⟨h₁, h₂⟩ := (lands_iff f q).1 hq
  refine (pred_le_iff _ _).2 ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := not_not.1 ((mkPred_f₁ _ _ x).not.1 hx)
    exact h₁ y x hy
  · obtain ⟨y, hy⟩ := not_not.1 ((mkPred_f₂ _ _ x).not.1 hx)
    exact h₂ y x hy

instance hasImages : HasImages LinkedPts := ⟨fun f => ⟨_, isImage_imP f⟩⟩

/-! ### Comprehension: `(a∩P₁∩P₂, l∩P₁, r∩P₂)` with the inclusion -/

section Corestrict

variable {A L : Type} (Pa : A → Prop) (Pl : L → Prop)

/-- Corestriction of a partial function to the subsets `Pa`, `Pl`. -/
noncomputable def corestr : Option (A ⊕ L) → Option ({a // Pa a} ⊕ {x // Pl x}) := by
  classical
  exact fun
    | none => none
    | some (.inl a) => if h : Pa a then some (.inl ⟨a, h⟩) else none
    | some (.inr x) => if h : Pl x then some (.inr ⟨x, h⟩) else none

theorem corestr_eq_inl (o : Option (A ⊕ L)) (w : {a // Pa a}) :
    corestr Pa Pl o = some (.inl w) ↔ o = some (.inl w.1) := by
  classical
  rcases o with _ | (a | x)
  · simp [corestr]
  · by_cases h : Pa a
    · have e : corestr Pa Pl (some (.inl a)) = some (.inl ⟨a, h⟩) := by simp [corestr, h]
      rw [e]
      constructor
      · intro h'
        cases h'
        rfl
      · intro h'
        cases h'
        rfl
    · have e : corestr Pa Pl (some (.inl a)) = none := by simp [corestr, h]
      rw [e]
      constructor
      · intro h'
        cases h'
      · intro h'
        cases h'
        exact absurd w.2 h
  · constructor
    · intro h
      by_cases hl : Pl x
      · have e : corestr Pa Pl (some (.inr x)) = some (.inr ⟨x, hl⟩) := by simp [corestr, hl]
        rw [e] at h
        cases h
      · have e : corestr Pa Pl (some (.inr x)) = none := by simp [corestr, hl]
        rw [e] at h
        cases h
    · intro h
      cases h

theorem corestr_bind (o : Option (A ⊕ L)) (h : ∀ z, o = some z → Sum.elim Pa Pl z) :
    (corestr Pa Pl o).bind (fun w => some (Sum.map Subtype.val Subtype.val w)) = o := by
  classical
  rcases o with _ | (a | x)
  · rfl
  · have ha : Pa a := h _ rfl
    simp [corestr, ha]
  · have hx : Pl x := h _ rfl
    simp [corestr, hx]

theorem val_map_inj (o o' : Option ({a // Pa a} ⊕ {x // Pl x}))
    (h : o.bind (fun w => some (Sum.map Subtype.val Subtype.val w)) =
      o'.bind (fun w => some (Sum.map Subtype.val Subtype.val w))) : o = o' := by
  rcases o with _ | w <;> rcases o' with _ | w'
  · rfl
  · cases h
  · cases h
  · have h' : some (Sum.map Subtype.val Subtype.val w) =
        some (Sum.map Subtype.val Subtype.val w') := h
    rw [(Sum.map_injective.2 ⟨Subtype.val_injective, Subtype.val_injective⟩)
      (Option.some.inj h')]

end Corestrict

/-- The linked part of the comprehension: `a ∩ P₁ ∩ P₂`. -/
abbrev cA {X : LinkedPts} (p : Pred X) (a : X.a) : Prop :=
  Hom.f₁ p (.inl a) ≠ none ∧ Hom.f₂ p (.inl a) ≠ none

/-- The left part of the comprehension: `l ∩ P₁`. -/
abbrev cL {X : LinkedPts} (p : Pred X) (x : X.l) : Prop := Hom.f₁ p (.inr x) ≠ none

/-- The right part of the comprehension: `r ∩ P₂`. -/
abbrev cR {X : LinkedPts} (p : Pred X) (x : X.r) : Prop := Hom.f₂ p (.inr x) ≠ none

/-- The comprehension object `(a∩P₁∩P₂, l∩P₁, r∩P₂)`. -/
abbrev cObj {X : LinkedPts} (p : Pred X) : LinkedPts :=
  ⟨{a // cA p a}, {x // cL p x}, {x // cR p x}⟩

/-- The comprehension map: the inclusion. -/
def cPi {X : LinkedPts} (p : Pred X) : cObj p ⟶ X :=
  (⟨fun w => some (Sum.map Subtype.val Subtype.val w),
    fun w => some (Sum.map Subtype.val Subtype.val w),
    fun _ _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ => (by simp)⟩ :
    Hom (cObj p) X)

theorem isComprehension_cPi {X : LinkedPts} (p : Pred X) : IsComprehension p (cPi p) := by
  refine ⟨(lands_iff _ _).2 ⟨?_, ?_⟩, fun Z g hg => ?_⟩
  · rintro (w | w) x ⟨⟩
    exacts [w.2.1, w.2]
  · rintro (w | w) x ⟨⟩
    exacts [w.2.2, w.2]
  obtain ⟨h₁, h₂⟩ := (lands_iff g p).1 hg
  let g' : Z ⟶ cObj p :=
    (⟨fun z => corestr (cA p) (cL p) (Hom.f₁ g z), fun z => corestr (cA p) (cR p) (Hom.f₂ g z),
      fun z w hw => g.hl z w.1 ((corestr_eq_inl _ _ _ w).1 hw),
      fun z w hw => g.hr z w.1 ((corestr_eq_inl _ _ _ w).1 hw),
      fun z w => by rw [corestr_eq_inl, corestr_eq_inl]; exact g.ha z w.1⟩ : Hom Z (cObj p))
  have hfac : g' ≫ cPi p = g := by
    refine hom_ext (fun z => corestr_bind _ _ _ ?_) (fun z => corestr_bind _ _ _ ?_)
    · rintro (a | x) hz
      · refine ⟨h₁ z _ hz, ?_⟩
        rcases z with z | z
        · exact h₂ _ _ ((g.ha z a).1 hz)
        · exact absurd hz (g.hl z a)
      · exact h₁ z _ hz
    · rintro (a | x) hz
      · refine ⟨?_, h₂ z _ hz⟩
        rcases z with z | z
        · exact h₁ _ _ ((g.ha z a).2 hz)
        · exact absurd hz (g.hr z a)
      · exact h₂ z _ hz
  refine ⟨g', hfac, fun h hh => ?_⟩
  have e := hh.trans hfac.symm
  exact hom_ext (fun z => val_map_inj _ _ _ _ (congrFun (congrArg Hom.f₁ e) z))
    (fun z => val_map_inj _ _ _ _ (congrFun (congrArg Hom.f₂ e) z))

instance hasComprehension : HasComprehension LinkedPts :=
  ⟨fun p => ⟨_, _, isComprehension_cPi p⟩⟩

/-! ### Filters: `(a∩P₁∩P₂, (l∩P₁) ⊔ (a∩P₁∖P₂), (r∩P₂) ⊔ (a∩P₂∖P₁))` -/

section Filt

variable {A L : Type} (S T : A → Prop) (R : L → Prop)

/-- The filter as a partial function: a linked point in `S` stays linked, one in
`T` becomes an unlinked point, the others are dropped. -/
noncomputable def filt : A ⊕ L → Option ({a // S a} ⊕ ({x // R x} ⊕ {a // T a})) := by
  classical
  exact fun
    | .inl a => if h : S a then some (.inl ⟨a, h⟩)
        else if h' : T a then some (.inr (.inr ⟨a, h'⟩)) else none
    | .inr x => if h : R x then some (.inr (.inl ⟨x, h⟩)) else none

/-- The factorisation through the filter. -/
def unfilt {B : Type} (f : A ⊕ L → Option B) :
    {a // S a} ⊕ ({x // R x} ⊕ {a // T a}) → Option B
  | .inl w => f (.inl w.1)
  | .inr (.inl w) => f (.inr w.1)
  | .inr (.inr w) => f (.inl w.1)

theorem filt_eq_inl (x : A ⊕ L) (w : {a // S a}) :
    filt S T R x = some (.inl w) ↔ x = .inl w.1 := by
  classical
  rcases x with a | x
  · by_cases hS : S a
    · have e : filt S T R (.inl a) = some (.inl ⟨a, hS⟩) := by simp [filt, hS]
      rw [e]
      constructor
      · intro h
        cases h
        rfl
      · intro h
        cases h
        rfl
    · constructor
      · intro h
        by_cases hT : T a
        · have e : filt S T R (.inl a) = some (.inr (.inr ⟨a, hT⟩)) := by simp [filt, hS, hT]
          rw [e] at h
          cases h
        · have e : filt S T R (.inl a) = none := by simp [filt, hS, hT]
          rw [e] at h
          cases h
      · intro h
        cases h
        exact absurd w.2 hS
  · constructor
    · intro h
      by_cases hR : R x
      · have e : filt S T R (.inr x) = some (.inr (.inl ⟨x, hR⟩)) := by simp [filt, hR]
        rw [e] at h
        cases h
      · have e : filt S T R (.inr x) = none := by simp [filt, hR]
        rw [e] at h
        cases h
    · intro h
      cases h

theorem filt_ne_none (x : A ⊕ L) (h : filt S T R x ≠ none) :
    Sum.elim (fun a => S a ∨ T a) R x := by
  classical
  rcases x with a | x
  · by_contra hc
    simp only [Sum.elim_inl, not_or] at hc
    exact h (by simp [filt, hc.1, hc.2])
  · by_contra hc
    simp only [Sum.elim_inr] at hc
    exact h (by simp [filt, hc])

theorem filt_bind {B : Type} (f : A ⊕ L → Option B)
    (hf : ∀ x, f x ≠ none → Sum.elim (fun a => S a ∨ T a) R x) (x : A ⊕ L) :
    (filt S T R x).bind (unfilt S T R f) = f x := by
  classical
  rcases x with a | x
  · by_cases hS : S a
    · simp [filt, hS, unfilt]
    · by_cases hT : T a
      · simp [filt, hS, hT, unfilt]
      · have : f (.inl a) = none := by
          by_contra hne
          rcases hf _ hne with h | h
          exacts [hS h, hT h]
        simp [filt, hS, hT, this]
  · by_cases hR : R x
    · simp [filt, hR, unfilt]
    · have : f (.inr x) = none := by
        by_contra hne
        exact hR (hf _ hne)
      simp [filt, hR, this]

theorem filt_surj (hST : ∀ a, S a → ¬ T a) (q : {a // S a} ⊕ ({x // R x} ⊕ {a // T a})) :
    ∃ x, filt S T R x = some q := by
  classical
  rcases q with w | w | w
  · exact ⟨.inl w.1, by simp [filt, w.2]⟩
  · exact ⟨.inr w.1, by simp [filt, w.2]⟩
  · have hS : ¬ S w.1 := fun h => hST _ h w.2
    exact ⟨.inl w.1, by simp [filt, hS, w.2]⟩

end Filt

/-- `a ∩ P₁ ∖ P₂`: linked points that become left points in the filter. -/
abbrev fT₁ {X : LinkedPts} (p : Pred X) (a : X.a) : Prop :=
  Hom.f₁ p (.inl a) ≠ none ∧ Hom.f₂ p (.inl a) = none

/-- `a ∩ P₂ ∖ P₁`: linked points that become right points in the filter. -/
abbrev fT₂ {X : LinkedPts} (p : Pred X) (a : X.a) : Prop :=
  Hom.f₂ p (.inl a) ≠ none ∧ Hom.f₁ p (.inl a) = none

/-- The filter object. -/
abbrev fObj {X : LinkedPts} (p : Pred X) : LinkedPts :=
  ⟨{a // cA p a}, {x // cL p x} ⊕ {a // fT₁ p a}, {x // cR p x} ⊕ {a // fT₂ p a}⟩

/-- The filter map: the partial identity onto `p`, unlinking where needed. -/
noncomputable def fXi {X : LinkedPts} (p : Pred X) : X ⟶ fObj p :=
  (⟨filt (cA p) (fT₁ p) (cL p), filt (cA p) (fT₂ p) (cR p),
    fun x w h => (by
      have := (filt_eq_inl _ _ _ _ w).1 h
      cases this),
    fun x w h => (by
      have := (filt_eq_inl _ _ _ _ w).1 h
      cases this),
    fun x w => (by
      rw [filt_eq_inl, filt_eq_inl]
      simp)⟩ : Hom X (fObj p))

theorem isFilter_fXi {X : LinkedPts} (p : Pred X) : IsFilter p (fXi p) := by
  refine ⟨(pred_le_iff _ _).2 ⟨fun x hx => ?_, fun x hx => ?_⟩, fun B f hf => ?_⟩
  · have hx' : filt (cA p) (fT₁ p) (cL p) x ≠ none := fun h => hx ((comp_truth_f₁ _ x).2 h)
    have := filt_ne_none _ _ _ x hx'
    rcases x with a | x
    · rcases this with h | h
      exacts [h.1, h.1]
    · exact this
  · have hx' : filt (cA p) (fT₂ p) (cR p) x ≠ none := fun h => hx ((comp_truth_f₂ _ x).2 h)
    have := filt_ne_none _ _ _ x hx'
    rcases x with a | x
    · rcases this with h | h
      exacts [h.2, h.1]
    · exact this
  obtain ⟨s₁, s₂⟩ := supp_of_le f p hf
  let f' : fObj p ⟶ B :=
    (⟨unfilt (cA p) (fT₁ p) (cL p) (Hom.f₁ f), unfilt (cA p) (fT₂ p) (cR p) (Hom.f₂ f),
      (by
        rintro (w | w) y h
        · exact f.hl w.1 y h
        · have h2 := (f.ha w.1 y).1 h
          exact s₂ _ (by rw [h2]; simp) w.2.2),
      (by
        rintro (w | w) y h
        · exact f.hr w.1 y h
        · have h1 := (f.ha w.1 y).2 h
          exact s₁ _ (by rw [h1]; simp) w.2.2),
      fun w y => f.ha w.1 y⟩ : Hom (fObj p) B)
  have hfac : fXi p ≫ f' = f := by
    refine hom_ext (fun x => filt_bind _ _ _ _ ?_ x) (fun x => filt_bind _ _ _ _ ?_ x)
    · rintro (a | x) hx
      · by_cases h2 : Hom.f₂ p (.inl a) = none
        · exact Or.inr ⟨s₁ _ hx, h2⟩
        · exact Or.inl ⟨s₁ _ hx, h2⟩
      · exact s₁ _ hx
    · rintro (a | x) hx
      · by_cases h1 : Hom.f₁ p (.inl a) = none
        · exact Or.inr ⟨s₂ _ hx, h1⟩
        · exact Or.inl ⟨h1, s₂ _ hx⟩
      · exact s₂ _ hx
  refine ⟨f', hfac, fun h hh => ?_⟩
  have e := hh.trans hfac.symm
  refine hom_ext (fun q => ?_) (fun q => ?_)
  · obtain ⟨x, hx⟩ := filt_surj (cA p) (fT₁ p) (cL p) (fun a h h' => h'.2 ▸ h.2 <| rfl) q
    have e1 := congrFun (congrArg Hom.f₁ e) x
    rw [comp_f₁, comp_f₁] at e1
    have hx' : Hom.f₁ (fXi p) x = some q := hx
    rw [hx', Option.bind_some, Option.bind_some] at e1
    exact e1
  · obtain ⟨x, hx⟩ := filt_surj (cA p) (fT₂ p) (cR p) (fun a h h' => h'.2 ▸ h.1 <| rfl) q
    have e1 := congrFun (congrArg Hom.f₂ e) x
    rw [comp_f₂, comp_f₂] at e1
    have hx' : Hom.f₂ (fXi p) x = some q := hx
    rw [hx', Option.bind_some, Option.bind_some] at e1
    exact e1

instance hasFilters : HasFilters LinkedPts := ⟨fun p => ⟨_, _, isFilter_fXi p⟩⟩

/-! ### Compatible filters and comprehensions -/

/-- A sharp predicate (an image) agrees on the linked points: `P₁ ∩ a = P₂ ∩ a`. -/
theorem sharp_linked {X : LinkedPts} {p : Pred X} (hp : IsSharp p) (a : X.a) :
    Hom.f₁ p (.inl a) ≠ none ↔ Hom.f₂ p (.inl a) ≠ none := by
  obtain ⟨Y, f, hf⟩ := hp
  obtain ⟨h₁, h₂⟩ := (lands_iff f p).1 hf.1
  obtain ⟨k₁, k₂⟩ := (pred_le_iff _ _).1 (hf.2 (imP f) (isImage_imP f).1)
  constructor
  · intro ha
    obtain ⟨y, hy⟩ := not_not.1 ((mkPred_f₁ _ _ _).not.1 (k₁ _ ha))
    rcases y with y | y
    · exact h₂ _ _ ((f.ha y a).1 hy)
    · exact absurd hy (f.hl y a)
  · intro ha
    obtain ⟨y, hy⟩ := not_not.1 ((mkPred_f₂ _ _ _).not.1 (k₂ _ ha))
    rcases y with y | y
    · exact h₁ _ _ ((f.ha y a).2 hy)
    · exact absurd hy (f.hr y a)

theorem opt_map_const_eq_some {α β : Type*} (o : Option α) (b c : β) :
    o.map (fun _ => b) = some c ↔ o ≠ none ∧ b = c := by
  rcases o with _ | o <;> simp

/-- The partial identity on a predicate agreeing on linked points (the assert map
of a sharp predicate). -/
def eAs {X : LinkedPts} (p : Pred X)
    (hp : ∀ a, Hom.f₁ p (.inl a) ≠ none ↔ Hom.f₂ p (.inl a) ≠ none) : X ⟶ X :=
  (⟨fun x => (Hom.f₁ p x).map (fun _ => x), fun x => (Hom.f₂ p x).map (fun _ => x),
    fun x y h => (by
      rw [opt_map_const_eq_some] at h
      cases h.2),
    fun x y h => (by
      rw [opt_map_const_eq_some] at h
      cases h.2),
    fun x y => (by
      rw [opt_map_const_eq_some, opt_map_const_eq_some, hp]
      simp)⟩ : Hom X X)

theorem eAs_lands {X : LinkedPts} (p : Pred X) hp : eAs p hp ≫ p = eAs p hp ≫ truth X := by
  refine (lands_iff _ _).2 ⟨fun y x h => ?_, fun y x h => ?_⟩
  · obtain ⟨h1, rfl⟩ := (opt_map_const_eq_some _ _ _).1 h
    exact h1
  · obtain ⟨h1, rfl⟩ := (opt_map_const_eq_some _ _ _).1 h
    exact h1

theorem eAs_left {X Z : LinkedPts} (p : Pred X) hp (g : Z ⟶ X) (hg : g ≫ p = g ≫ truth X) :
    g ≫ eAs p hp = g := by
  obtain ⟨h₁, h₂⟩ := (lands_iff g p).1 hg
  refine hom_ext (fun z => ?_) (fun z => ?_)
  · rw [comp_f₁]
    rcases hz : Hom.f₁ g z with _ | x
    · rfl
    · show (Hom.f₁ p x).map (fun _ => x) = some x
      rcases hp' : Hom.f₁ p x with _ | v
      · exact absurd hp' (h₁ z x hz)
      · rfl
  · rw [comp_f₂]
    rcases hz : Hom.f₂ g z with _ | x
    · rfl
    · show (Hom.f₂ p x).map (fun _ => x) = some x
      rcases hp' : Hom.f₂ p x with _ | v
      · exact absurd hp' (h₂ z x hz)
      · rfl

theorem eAs_right {X B : LinkedPts} (p : Pred X) hp (f : X ⟶ B)
    (s₁ : ∀ x, Hom.f₁ f x ≠ none → Hom.f₁ p x ≠ none)
    (s₂ : ∀ x, Hom.f₂ f x ≠ none → Hom.f₂ p x ≠ none) : eAs p hp ≫ f = f := by
  refine hom_ext (fun x => ?_) (fun x => ?_)
  · show ((Hom.f₁ p x).map (fun _ => x)).bind (Hom.f₁ f) = Hom.f₁ f x
    rcases hp' : Hom.f₁ p x with _ | v
    · show none = Hom.f₁ f x
      by_contra hne
      exact s₁ x (Ne.symm hne) hp'
    · rfl
  · show ((Hom.f₂ p x).map (fun _ => x)).bind (Hom.f₂ f) = Hom.f₂ f x
    rcases hp' : Hom.f₂ p x with _ | v
    · show none = Hom.f₂ f x
      by_contra hne
      exact s₂ x (Ne.symm hne) hp'
    · rfl

/-- **Compatible filters and comprehensions** (REC 74): for a sharp `p` and any
comprehension `π` of `p`, the factorisation `ξ` of the partial identity on `p`
through `π` is a filter with `ξ ∘ π = id`. -/
instance compatible : CompatibleFiltersComprehensions LinkedPts := by
  refine ⟨fun {W X p} π hsh hπ => ?_⟩
  have hp := sharp_linked hsh
  obtain ⟨ξ, hξ, -⟩ := hπ.2 (eAs p hp) (eAs_lands p hp)
  have hπξ : π ≫ ξ = 𝟙 W := (hπ.2 π hπ.1).unique
    (show (π ≫ ξ) ≫ π = π by rw [Category.assoc, hξ]; exact eAs_left p hp π hπ.1)
    (Category.id_comp π)
  refine ⟨ξ, ⟨(pred_le_iff _ _).2 ⟨fun x hx => ?_, fun x hx => ?_⟩, fun B f hf => ?_⟩, hπξ⟩
  · have htot : ∀ w, Hom.f₁ π w ≠ none := fun w h => by
      have e := congrFun (congrArg Hom.f₁ hπξ) w
      rw [comp_f₁, h] at e
      cases e
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 (fun h => hx ((comp_truth_f₁ ξ x).2 h))
    have e1 := congrFun (congrArg Hom.f₁ hξ) x
    rw [comp_f₁, hw, Option.bind_some] at e1
    intro hpx
    apply htot w
    rw [e1]
    show (Hom.f₁ p x).map _ = none
    rw [hpx]
    rfl
  · have htot : ∀ w, Hom.f₂ π w ≠ none := fun w h => by
      have e := congrFun (congrArg Hom.f₂ hπξ) w
      rw [comp_f₂, h] at e
      cases e
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 (fun h => hx ((comp_truth_f₂ ξ x).2 h))
    have e1 := congrFun (congrArg Hom.f₂ hξ) x
    rw [comp_f₂, hw, Option.bind_some] at e1
    intro hpx
    apply htot w
    rw [e1]
    show (Hom.f₂ p x).map _ = none
    rw [hpx]
    rfl
  · obtain ⟨s₁, s₂⟩ := supp_of_le f p hf
    refine ⟨π ≫ f, ?_, fun h hh => ?_⟩
    · show ξ ≫ π ≫ f = f
      rw [← Category.assoc, hξ]
      exact eAs_right p hp f s₁ s₂
    rw [← hh, ← Category.assoc, hπξ, Category.id_comp]

/-! ### The scalar `s = (1, 0)` and the object `A` with one linked point -/

/-- The idempotent scalar `s = (1, 0)` (identity on the left point of `I`, zero
on the right point). -/
def sS : Scal LinkedPts :=
  (⟨fun x => some x, fun _ => none, fun _ y => y.elim, fun _ _ h => (by cases h),
    fun y => y.elim⟩ : Hom unitObj unitObj)

theorem sS_idem : sS ≫ sS = sS := hom_ext (fun _ => rfl) (fun _ => rfl)

theorem sS_ne_zero : sS ≠ 0 := fun h => by
  have e := congrFun (congrArg Hom.f₁ h) (.inr ())
  cases e

theorem sS_ne_one : sS ≠ 𝟙 _ := fun h => by
  have e := congrFun (congrArg Hom.f₂ h) (.inr ())
  cases e

/-- The object `A = (1, ∅, ∅)`: one linked point. -/
abbrev objA : LinkedPts := ⟨Unit, Empty, Empty⟩

/-- `s ∘ 1_A = (1, ∅)` is **not sharp**: a map into `A` reaches the linked
point in both components or in neither, so its image is `(∅, ∅)` or `(1, 1)`. -/
theorem not_isSharp : ¬ IsSharp (truth objA ≫ sS) := by
  rintro ⟨Y, f, hf₁, hf₂⟩
  obtain ⟨h₁, h₂⟩ := (lands_iff f _).1 hf₁
  by_cases hex : ∃ y, Hom.f₁ f y = some (.inl ())
  · obtain ⟨y, hy⟩ := hex
    rcases y with y | y
    · exact h₂ _ _ ((f.ha y ()).1 hy) rfl
    · exact f.hl y () hy
  · push Not at hex
    have hz : f ≫ (0 : Pred objA) = f ≫ truth objA := by
      refine (lands_iff f 0).2 ⟨fun y x hy => ?_, fun y x hy => ?_⟩
      · rcases x with ⟨⟩ | e
        · exact absurd hy (hex y)
        · exact e.elim
      · rcases x with ⟨⟩ | e
        · rcases y with y | y
          · exact absurd ((f.ha y ()).2 hy) (hex _)
          · exact absurd hy (f.hr y ())
        · exact e.elim
    obtain ⟨k₁, -⟩ := (pred_le_iff _ _).1 (hf₂ 0 hz)
    exact k₁ (.inl ()) (fun h => by cases h) rfl

/-- `LinkedPts` is **not** separated by states: `A` has no states (the left and
right points of `I` cannot reach a linked point), yet `id_A ≠ 0`. -/
theorem not_separatingStates : ¬ SeparatingStates LinkedPts := by
  have nostate : ∀ ω : Stat objA, False := fun ω => by
    have e := congrFun (congrArg Hom.f₁ ω.2) (.inr ())
    rw [comp_f₁] at e
    rcases hω : Hom.f₁ ω.1 (.inr ()) with _ | (⟨⟩ | e')
    · rw [hω] at e
      cases e
    · exact ω.1.hl () () hω
    · exact e'.elim
  intro h
  have e := congrFun (congrArg Hom.f₁ (h (𝟙 objA) 0 (fun ω => (nostate ω).elim))) (.inl ())
  cases e

/-- `End(A) = {0, id}`: the linked point goes to itself in both components or
nowhere. -/
theorem endA (f : objA ⟶ objA) : f = 0 ∨ f = 𝟙 objA := by
  rcases h₁ : Hom.f₁ f (.inl ()) with _ | (⟨⟩ | e)
  · left
    refine hom_ext ?_ ?_
    · rintro (⟨⟩ | e)
      · exact h₁
      · exact e.elim
    · rintro (⟨⟩ | e)
      · rcases h₂ : Hom.f₂ f (.inl ()) with _ | (⟨⟩ | e)
        · rfl
        · rw [(f.ha () ()).2 h₂] at h₁
          cases h₁
        · exact e.elim
      · exact e.elim
  · right
    refine hom_ext ?_ ?_
    · rintro (⟨⟩ | e)
      · exact h₁
      · exact e.elim
    · rintro (⟨⟩ | e)
      · exact (f.ha () ()).1 h₁
      · exact e.elim
  · exact e.elim

/-- `A` has a non-zero map to every object with a point: send the linked point
there. -/
theorem exists_ne_zero (Q : LinkedPts) (hQ : 𝟙 Q ≠ 0) : ∃ m : objA ⟶ Q, m ≠ 0 := by
  rcases isEmpty_or_nonempty Q.a with ha | ⟨⟨q⟩⟩
  · rcases isEmpty_or_nonempty Q.l with hl | ⟨⟨q⟩⟩
    · rcases isEmpty_or_nonempty Q.r with hr | ⟨⟨q⟩⟩
      · exact (hQ (hom_ext (by rintro (x | x) <;> exact isEmptyElim x)
          (by rintro (x | x) <;> exact isEmptyElim x))).elim
      · refine ⟨(⟨fun _ => none, fun x => Sum.elim (fun _ => some (.inr q)) (fun e => e.elim) x,
          fun e => e.elim, fun e => e.elim, fun _ y => (by simp)⟩ : Hom objA Q), fun h => ?_⟩
        have e := congrFun (congrArg Hom.f₂ h) (.inl ())
        cases e
    · refine ⟨(⟨fun x => Sum.elim (fun _ => some (.inr q)) (fun e => e.elim) x, fun _ => none,
        fun e => e.elim, fun e => e.elim, fun _ y => (by simp)⟩ : Hom objA Q), fun h => ?_⟩
      have e := congrFun (congrArg Hom.f₁ h) (.inl ())
      cases e
  · refine ⟨(⟨fun x => Sum.elim (fun _ => some (.inl q)) (fun e => e.elim) x,
      fun x => Sum.elim (fun _ => some (.inl q)) (fun e => e.elim) x,
      fun e => e.elim, fun e => e.elim, fun _ y => (by simp)⟩ : Hom objA Q), fun h => ?_⟩
    have e := congrFun (congrArg Hom.f₁ h) (.inl ())
    cases e

end LinkedPts

/-! ## `LinkedPts` is not a product of two non-trivial effectuses -/

section NoProduct

open LinkedPts

variable {D : Type u₁} [Category.{v₁} D] [HasFiniteCoproducts D] [∀ X Y : D, PCM (X ⟶ Y)]
  [FinPAC D]

theorem eq_zero_of_id_src {X Y : D} (h : 𝟙 X = 0) (f : X ⟶ Y) : f = 0 := by
  rw [← Category.id_comp f, h, FinPAC.zero_comp]

theorem eq_zero_of_id_tgt {X Y : D} (h : 𝟙 Y = 0) (f : X ⟶ Y) : f = 0 := by
  rw [← Category.comp_id f, h, FinPAC.comp_zero]

/-- In a non-trivial effectus, `id_I ≠ 0`. -/
theorem id_effObj_ne_zero [EffectusPartialForm D] (h : (1 : Scal D) ≠ 0) :
    𝟙 (effObj D) ≠ 0 := by
  intro h'
  apply h
  show truth (effObj D) = 0
  exact eq_zero_of_id_src h' _

variable {D₁ : Type u₁} {D₂ : Type u₂} [Category.{v₁} D₁] [Category.{v₂} D₂]
  [HasFiniteCoproducts D₁] [HasFiniteCoproducts D₂]
  [∀ X Y : D₁, PCM (X ⟶ Y)] [∀ X Y : D₂, PCM (X ⟶ Y)] [FinPAC D₁] [FinPAC D₂]

/-- Under an equivalence `LinkedPts ≌ D₁ × D₂`, one component of the image of
`A` is a zero object: otherwise `End(A₁, A₂)` contains the three distinct maps
`(1,0)`, `(0,1)`, `(0,0)`, but `End(A) = {0, id}`. -/
theorem one_factor (e : LinkedPts ≌ D₁ × D₂) :
    𝟙 (e.functor.obj objA).1 = 0 ∨ 𝟙 (e.functor.obj objA).2 = 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨h₁, h₂⟩ := hc
  let F := e.fullyFaithfulFunctor
  let FA := e.functor.obj objA
  let u : FA ⟶ FA := ((𝟙 FA.1, 0) : (FA.1 ⟶ FA.1) × (FA.2 ⟶ FA.2))
  let v : FA ⟶ FA := ((0, 𝟙 FA.2) : (FA.1 ⟶ FA.1) × (FA.2 ⟶ FA.2))
  let w : FA ⟶ FA := ((0, 0) : (FA.1 ⟶ FA.1) × (FA.2 ⟶ FA.2))
  have back : ∀ {a b : FA ⟶ FA}, F.preimage a = F.preimage b → a = b := fun {a b} h => by
    have := congrArg e.functor.map h
    rwa [F.map_preimage, F.map_preimage] at this
  have huv : F.preimage u ≠ F.preimage v := fun h => h₁ (congrArg Prod.fst (back h))
  have huw : F.preimage u ≠ F.preimage w := fun h => h₁ (congrArg Prod.fst (back h))
  have hvw : F.preimage v ≠ F.preimage w := fun h => h₂ (congrArg Prod.snd (back h))
  rcases endA (F.preimage u) with hu | hu <;> rcases endA (F.preimage v) with hv | hv <;>
    rcases endA (F.preimage w) with hw | hw
  all_goals first
    | exact huv (hu.trans hv.symm)
    | exact huw (hu.trans hw.symm)
    | exact hvw (hv.trans hw.symm)

/-- If the second component of the image of `A` is a zero object and `D₂` is
non-trivial, contradiction: for `Q := e⁻¹(0, I₂)` every map `A → Q` is zero
(its image in `D₁ × D₂` has components into `0` and out of a zero object), but
`Q` has a point, so `A → Q` has a non-zero map. -/
theorem no_factor_aux [EffectusPartialForm D₂] (e : LinkedPts ≌ D₁ × D₂)
    (h₂ : (1 : Scal D₂) ≠ 0) (hA : 𝟙 (e.functor.obj objA).2 = 0) : False := by
  let T : D₁ × D₂ := (⊥_ D₁, effObj D₂)
  let Q := e.inverse.obj T
  have hT : 𝟙 T.1 = 0 := initialIsInitial.hom_ext _ _
  have hU := id_effObj_ne_zero h₂
  have hQ : 𝟙 Q ≠ 0 := by
    intro hQ
    let G := e.fullyFaithfulInverse
    have : (((𝟙 T.1, 𝟙 T.2) : (T.1 ⟶ T.1) × (T.2 ⟶ T.2)) : T ⟶ T) =
        (((𝟙 T.1, 0) : (T.1 ⟶ T.1) × (T.2 ⟶ T.2)) : T ⟶ T) :=
      G.map_injective ((eq_zero_of_id_src hQ _).trans (eq_zero_of_id_src hQ _).symm)
    exact hU (congrArg Prod.snd this)
  obtain ⟨m, hm⟩ := exists_ne_zero Q hQ
  apply hm
  apply e.functor.map_injective
  rw [← cancel_mono (e.counitIso.app T).hom]
  apply Prod.hom_ext
  · exact (eq_zero_of_id_tgt (Y := T.1) hT _).trans (eq_zero_of_id_tgt (Y := T.1) hT _).symm
  · exact (eq_zero_of_id_src hA _).trans (eq_zero_of_id_src hA _).symm

/-- **`LinkedPts` is not equivalent, even as a bare category, to a product of
two non-trivial effectuses.** -/
theorem linkedPts_not_equiv_prod [EffectusPartialForm D₁] [EffectusPartialForm D₂]
    (h₁ : (1 : Scal D₁) ≠ 0) (h₂ : (1 : Scal D₂) ≠ 0) : IsEmpty (LinkedPts ≌ D₁ × D₂) := by
  refine ⟨fun e => ?_⟩
  rcases one_factor e with h | h
  · exact no_factor_aux (e.trans (Prod.braiding D₁ D₂)) h₁ h
  · exact no_factor_aux e h₂ h

end NoProduct

/-- **REC 92** (`prop:predsep-splits`, short.tex:1643, Proposition): the
counterexample.  `LinkedPts` is an effectus (in partial form) with images and
compatible filters and comprehensions, separated by predicates but not by
states, with the non-trivial idempotent scalar `s = (1,0)`; the predicate
`s ∘ 1_A` is not sharp (so the printed proof's `asrt_{s∘1}` does not exist), and
`LinkedPts` is not equivalent to any product of two non-trivial effectuses. -/
theorem rec92_counterexample :
    SeparatingPredicates LinkedPts ∧ ¬ SeparatingStates LinkedPts ∧
      LinkedPts.sS ≫ LinkedPts.sS = LinkedPts.sS ∧ LinkedPts.sS ≠ 0 ∧
      LinkedPts.sS ≠ 𝟙 _ ∧ ¬ IsSharp (truth LinkedPts.objA ≫ LinkedPts.sS) ∧
      ∀ (D₁ : Type u₁) (D₂ : Type u₂) [Category.{v₁} D₁] [Category.{v₂} D₂]
        [HasFiniteCoproducts D₁] [HasFiniteCoproducts D₂]
        [∀ X Y : D₁, PCM (X ⟶ Y)] [∀ X Y : D₂, PCM (X ⟶ Y)] [FinPAC D₁] [FinPAC D₂]
        [EffectusPartialForm D₁] [EffectusPartialForm D₂],
        (1 : Scal D₁) ≠ 0 → (1 : Scal D₂) ≠ 0 → IsEmpty (LinkedPts ≌ D₁ × D₂) :=
  ⟨LinkedPts.separatingPredicates, LinkedPts.not_separatingStates, LinkedPts.sS_idem,
    LinkedPts.sS_ne_zero, LinkedPts.sS_ne_one, LinkedPts.not_isSharp,
    fun _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ => linkedPts_not_equiv_prod h₁ h₂⟩

/-- **REC 92** (`prop:predsep-splits`, short.tex:1643, Proposition) **is false as
printed** for separation by predicates: "an effectus separated by predicates
with images and compatible filters and comprehensions and a non-trivial
idempotent scalar `s` is equivalent to `C_s × C_{s^⊥}` for non-trivial
effectuses".  The negation is proved for the weakest reading of `≅` (an
equivalence of bare categories onto a product of *any* two non-trivial
effectuses); witness `LinkedPts` (`rec92_counterexample`).  The state-separated
case is true (`rec92_states`); the predicate case holds once `s ∘ 1_A` and
`s^⊥ ∘ 1_A` are sharp for all `A` (`rec92_predicates`). -/
theorem rec92_false_as_printed :
    ¬ ∀ (C : Type 1) [Category.{0} C] [HasFiniteCoproducts C] [∀ X Y : C, PCM (X ⟶ Y)]
        [FinPAC C] [EffectusPartialForm C] [HasImages C] [HasFilters C] [HasComprehension C]
        [CompatibleFiltersComprehensions C], SeparatingPredicates C →
        ∀ s : Scal C, s ≫ s = s → s ≠ 0 → s ≠ 𝟙 _ →
          ∃ (D₁ : Type u₁) (D₂ : Type u₂) (_ : Category.{v₁} D₁) (_ : Category.{v₂} D₂)
            (_ : HasFiniteCoproducts D₁) (_ : HasFiniteCoproducts D₂)
            (_ : ∀ X Y : D₁, PCM (X ⟶ Y)) (_ : ∀ X Y : D₂, PCM (X ⟶ Y))
            (_ : FinPAC D₁) (_ : FinPAC D₂)
            (_ : EffectusPartialForm D₁) (_ : EffectusPartialForm D₂),
            (1 : Scal D₁) ≠ 0 ∧ (1 : Scal D₂) ≠ 0 ∧ Nonempty (C ≌ D₁ × D₂) := by
  intro h
  obtain ⟨D₁, D₂, _, _, _, _, _, _, _, _, _, _, h₁, h₂, ⟨e⟩⟩ :=
    h LinkedPts LinkedPts.separatingPredicates LinkedPts.sS LinkedPts.sS_idem
      LinkedPts.sS_ne_zero LinkedPts.sS_ne_one
  exact (linkedPts_not_equiv_prod h₁ h₂).false e

end Papers.REC
