/-
Theses/B/Eff/StatesPredicates.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), lines
2070–3662: predicates, states and scalars of an effectus (parsec 190), the
effectus of effect modules and the representation theorem (191), the
distribution monad `𝒟_M`, abstract `M`-convex sets and their category
`AConv_M` (192–194), effect divisoids (195), and the theorem that `AConv_M`
is an effectus when `M` is an effect divisoid (196).

Design:
* The scalars `Scal C = C(1,1)` of an effectus in partial form carry an
  effect monoid structure (`λ ⊙ μ = λ ∘ μ`), and each `Pred X = C(X,1)` an
  effect module structure over it; both are instances whose data is genuine
  and whose proof obligations are `sorry`-ed (they are the claims of 190II).
* Formal `M`-convex combinations `MConvexComb M X` are functions `X → M`
  which sum to `1` over a finite support (via `PCM.IsSumOf`).  The
  functorial action `map`, and the monad multiplication `mu`, are obtained
  by choice from `sorry`-ed unique-existence lemmas (FIXME(choice)), since
  their values are partial sums.
* An abstract `M`-convex set is a *structure* `MConvex M X` (the pair
  `(X, h)` of the thesis), so that statements can quantify over convex
  structures; `AConvMCat M` is the bundled category.
* Not separately formalized: the example lists 190IV/190V and 192V.2
  (`OUS`, `OUG`, `CRng`, `CH`, `EJA`, and the non-cancellative triangle),
  the derivation-based description of the least congruence in 193IV and of
  coproduct elements in 193IX (only the resulting existence statements are
  stated), and 195V.4 (division effect monoids of Cho–Westerbaan).
-/
import Theses.B.Eff.Effectus

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

namespace Theses.B.Eff

universe u v w

/-! ## Predicates, states and scalars (parsec 190) -/

section Internal

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- **190II.1** (`dfn-mandso`, eff.tex:2075, Definition): a **predicate** on
an object `X` of an effectus in partial form is a map `X ⟶ 1` (here: to the
effect object `I`); the set `Pred X` of predicates is an effect algebra
(instance `predEffectAlgebra`). -/
abbrev Pred (X : C) : Type v := X ⟶ effObj C

/-- **190II.2** (`dfn-mandso`, eff.tex:2085, Definition): a **scalar** of an
effectus in partial form is a predicate on `1`, i.e. a map `1 ⟶ 1`.  The set
of scalars is written `Scal C ≡ M ≡ Pred 1`. -/
abbrev Scal (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Type v :=
  effObj C ⟶ effObj C

/-- **190II.2** (`dfn-mandso`, eff.tex:2090, Definition): the scalars `Scal C`
form an effect monoid with multiplication `λ ⊙ μ = λ ∘ μ` (composition; note
`1_M = id` by 181XIII).  Data genuine, proof obligations `sorry`-ed. -/
noncomputable instance scalEffectMonoid : EffectMonoid (Scal C) :=
  { predEffectAlgebra (effObj C) with
    mul := fun l m => m ≫ l
    one_mul := sorry
    mul_one := sorry
    mul_assoc := sorry
    distrib := sorry }

/-- **190II.3** (`dfn-mandso`, eff.tex:2097, Definition): a **real effectus**
is an effectus whose effect monoid of scalars is isomorphic to `[0,1]`. -/
def IsRealEffectus (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop :=
  ∃ φ : EffectMonoidHom (Scal C) I, Function.Bijective φ.toFun

/-- **190II.4** (`dfn-mandso`, eff.tex:2101, Definition): scalar
multiplication `λ · p = λ ∘ p` turns each `Pred X` into an effect module
over the scalars `Scal C`.  Data genuine, proof obligations `sorry`-ed. -/
noncomputable instance predEffectModule (X : C) :
    EffectModule (Scal C) (Pred X) where
  smul l p := p ≫ l
  mul_smul := sorry
  smul_perp := sorry
  perp_smul := sorry
  one_smul := sorry

/-- **190II.5** (`dfn-mandso`, eff.tex:2108, Definition): the substitution
map `Pred f : Pred Y → Pred X` of `f : X ⟶ Y`, given by
`Pred(f)(p) = p ∘ f`. -/
def predMap {X Y : C} (f : X ⟶ Y) : Pred Y → Pred X := fun p => f ≫ p

/-- **190II.5** (`dfn-mandso`, eff.tex:2112, Definition): for total `f` the
map `Pred f` is an effect module homomorphism, and `Pred` is in fact a
functor `Tot C → EMod_M^op` (the substitution functor). -/
theorem predMap_functor :
    ∃ F : Tot C ⥤ (EModCat.{v, v} (Scal C))ᵒᵖ,
      ∀ X : Tot C, (F.obj X).unop.carrier = Pred X.base := sorry

/-- **190II.6** (`dfn-mandso`, eff.tex:2118, Definition): a **substate** of
`X` is a map `ω : 1 ⟶ X`. -/
abbrev Substate (X : C) : Type v := effObj C ⟶ X

/-- **190II.6** (`dfn-mandso`, eff.tex:2119, Definition): a **state** is a
total substate; `Stat X` denotes the set of states of `X`. -/
def Stat (X : C) : Type v := { ω : effObj C ⟶ X // IsTotal ω }

/-- **190II.7** (`dfn-mandso`, eff.tex:2125, Definition): an effectus has
**separating predicates** if for every `X` the predicates on `X` are jointly
monic. -/
def SeparatingPredicates (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop :=
  ∀ ⦃Y X : C⦄ (f g : Y ⟶ X), (∀ p : Pred X, f ≫ p = g ≫ p) → f = g

/-- **190II.7** (`dfn-mandso`, eff.tex:2129, Definition): an effectus has
**separating states** if for every `X` the states of `X` are jointly
epic. -/
def SeparatingStates (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ ω : Stat X, ω.1 ≫ f = ω.1 ≫ g) → f = g

end Internal

/-- **190III** (eff.tex:2136, Examples): the effectus `vNᵒᵖ` (in partial
form: `(W*_ncpsu)ᵒᵖ`, cf. `effectus_vn_partial`) is a real effectus with
separating states and predicates.  (Its predicates on `𝒜` correspond to the
effects `[0,1]_𝒜` and its states to the normal states.) -/
theorem effectus_vn_real_separating
    (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    IsRealEffectus WStarCPSU.{u}ᵒᵖ ∧ SeparatingPredicates WStarCPSU.{u}ᵒᵖ ∧
      SeparatingStates WStarCPSU.{u}ᵒᵖ := sorry

/-! ## The effectus of effect modules (parsec 191) -/

/-- **191II** (`emod-effectus`, eff.tex:2206, Theorem), first half: for any
effect monoid `M` the category `EMod_M^op` is an effectus in total form
(with scalars `M` and separating predicates). -/
theorem emod_effectus (M : Type u) [EffectMonoid M] :
    Nonempty (EffectusTotalStructure (EModCat.{u, u} M)ᵒᵖ) := sorry

/-- **191II** (`emod-effectus`, eff.tex:2210, Theorem), second half
(*representation*, proved in 191VII): an effectus with separating predicates
embeds into `EMod_M^op` — the substitution functor `Pred` on the total maps
is faithful.  (Stated for an effectus in partial form with scalars
`M = Scal C`.) -/
theorem emod_effectus_representation {C : Type u} [Category.{v} C]
    [HasFiniteCoproducts C] [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C]
    [EffectusPartialForm C] (hsep : SeparatingPredicates C) :
    ∃ F : Tot C ⥤ (EModCat.{v, v} (Scal C))ᵒᵖ,
      (∀ X : Tot C, (F.obj X).unop.carrier = Pred X.base) ∧ F.Faithful :=
  sorry

/-- **191VIII** (`exc-rng-eff`, eff.tex:2337, Exercise): the category
`Rngᵒᵖ` of unital rings with unit-preserving homomorphisms, in the opposite
direction, is an effectus in total form.  (Its predicates on `R` correspond
to the idempotents of `R`; its scalars are `2`.) -/
theorem exc_rng_eff : Nonempty (EffectusTotalStructure RingCat.{u}ᵒᵖ) := sorry

/-- **191VIII.2** (`exc-rng-eff`, eff.tex:2351, Exercise): there is no
unit-preserving ring homomorphism `ℤ₂ → ℤ` (whence `Rngᵒᵖ` does not have
separating states). -/
theorem exc_rng_eff_no_hom : IsEmpty (ZMod 2 →+* ℤ) := sorry

/-! ## The distribution monad `𝒟_M` (parsec 192) -/

/-- **192II** (eff.tex:2364, Definition): a **formal `M`-convex
combination** over a set `X`, for an effect monoid `M`: a function
`p : X → M` with finite support whose values sum to `1` (the sum being the
iterated partial sum of the effect algebra `M`).  The set of all formal
`M`-convex combinations over `X` is the thesis's `𝒟_M X`, written
`λ₁|x₁⟩ ⋁ ⋯ ⋁ λₙ|xₙ⟩` for the combination supported on `x₁, …, xₙ`. -/
structure MConvexComb (M : Type u) [EffectMonoid M] (X : Type v) :
    Type (max u v) where
  toFun : X → M
  sum_one : ∃ l : List X, l.Nodup ∧ (∀ x, x ∈ l ↔ toFun x ≠ 0) ∧
    PCM.IsSumOf (l.map toFun) 1

namespace MConvexComb

variable {M : Type u} [EffectMonoid M]

instance {X : Type v} : CoeFun (MConvexComb M X) (fun _ => X → M) := ⟨toFun⟩

open Classical in
/-- The Dirac (point) distribution `1|x⟩ = η(x)` (192III.2). -/
noncomputable def eta {X : Type v} (x : X) : MConvexComb M X :=
  ⟨fun y => if y = x then 1 else 0, sorry⟩

/-- FIXME(choice): the pushforward `𝒟_M f` of a formal convex combination
along `f : X → Y` — `(𝒟_M f)(p)(y) = ⋁_{x : f(x) = y} p(x)` (192III.1) —
exists (the partial sums exist because subsums of `1` exist); stated as an
existence lemma from which `map` is obtained by choice. -/
theorem exists_map {X : Type v} {Y : Type w} (p : MConvexComb M X)
    (f : X → Y) :
    ∃ q : MConvexComb M Y, ∀ (y : Y) (l : List X), l.Nodup →
      (∀ x, x ∈ l ↔ (p.toFun x ≠ 0 ∧ f x = y)) →
      PCM.IsSumOf (l.map p.toFun) (q.toFun y) := sorry

/-- **192III.1** (`exc-dm-effectus`, eff.tex:2386): the functorial action
`𝒟_M f` of `𝒟_M` on `f : X → Y`. -/
noncomputable def map {X : Type v} {Y : Type w} (p : MConvexComb M X)
    (f : X → Y) : MConvexComb M Y :=
  (exists_map p f).choose

/-- FIXME(choice): the monad multiplication
`μ(Φ)(x) = ⋁_φ Φ(φ) ⊙ φ(x)` (192III.2) exists; stated as an existence
lemma from which `mu` is obtained by choice. -/
theorem exists_mu {X : Type v} (Φ : MConvexComb M (MConvexComb M X)) :
    ∃ q : MConvexComb M X, ∀ (x : X) (l : List (MConvexComb M X)),
      l.Nodup → (∀ φ, φ ∈ l ↔ Φ.toFun φ ≠ 0) →
      PCM.IsSumOf (l.map fun φ => Φ.toFun φ * φ.toFun x) (q.toFun x) := sorry

/-- **192III.2** (`exc-dm-effectus`, eff.tex:2397): the multiplication
`μ : 𝒟_M 𝒟_M X → 𝒟_M X`. -/
noncomputable def mu {X : Type v} (Φ : MConvexComb M (MConvexComb M X)) :
    MConvexComb M X :=
  (exists_mu Φ).choose

open Classical in
/-- The binary convex combination `λ|x⟩ ⋁ λᵖ|y⟩` (used for cancellativity,
192IV). -/
noncomputable def bin {X : Type v} (l : M) (x y : X) : MConvexComb M X :=
  ⟨fun z =>
    if x = y then (if z = x then 1 else 0)
    else if z = x then l else if z = y then orth l else 0, sorry⟩

end MConvexComb

section DMMonad

variable (M : Type u) [EffectMonoid M]

/-- **192III.1** (`exc-dm-effectus`, eff.tex:2380, Exercise\*): `𝒟_M` is a
functor `Set → Set` (with the action of `map`). -/
theorem exc_dm_effectus_functor :
    ∃ F : Type u ⥤ Type u, ∀ X : Type u, F.obj X = MConvexComb M X := sorry

/-- **192III.2** (`exc-dm-effectus`, eff.tex:2397, Exercise\*):
`(𝒟_M, η, μ)` is a monad on `Set`. -/
theorem exc_dm_effectus_monad :
    ∃ T : Monad (Type u), ∀ X : Type u,
      T.toFunctor.obj X = MConvexComb M X := sorry

/-- **192III.3** (`exc-dm-effectus`, eff.tex:2410, Exercise\*): the Kleisli
category of `𝒟_M` is an effectus (in total form) with scalars `M`. -/
theorem exc_dm_effectus_kleisli (T : Monad (Type u))
    (hT : ∀ X : Type u, T.toFunctor.obj X = MConvexComb M X) :
    Nonempty (EffectusTotalStructure (Kleisli T)) := sorry

end DMMonad

/-! ## Abstract `M`-convex sets (parsec 192, continued) -/

/-- **192IV** (eff.tex:2419, Definition): an **abstract `M`-convex set**: a
set `X` with a map `h : 𝒟_M X → X` such that `h(1|x⟩) = x` and
`h ∘ μ = h ∘ 𝒟_M h` (i.e. an Eilenberg–Moore algebra of the monad `𝒟_M`).
Formalized as a structure (the pair `(X, h)` of the thesis). -/
structure MConvex (M : Type u) [EffectMonoid M] (X : Type v) :
    Type (max u v) where
  h : MConvexComb M X → X
  h_eta : ∀ x : X, h (MConvexComb.eta x) = x
  h_mu : ∀ Φ : MConvexComb M (MConvexComb M X), h (MConvexComb.mu Φ) = h (Φ.map h)

/-- **192IV** (eff.tex:2438, Definition): a map `f : X → Y` between abstract
`M`-convex sets is **`M`-affine** if `f(h_X(⋁ᵢ λᵢ|xᵢ⟩)) = h_Y(⋁ᵢ λᵢ|f xᵢ⟩)`,
i.e. `f ∘ h_X = h_Y ∘ 𝒟_M f`. -/
def MConvex.IsAffine {M : Type u} [EffectMonoid M] {X : Type v} {Y : Type w}
    (sX : MConvex M X) (sY : MConvex M Y) (f : X → Y) : Prop :=
  ∀ p : MConvexComb M X, f (sX.h p) = sY.h (p.map f)

/-- **192IV** (eff.tex:2456, Definition): an abstract `M`-convex set `(X,h)`
is **cancellative** when `h(λ|y⟩ ⋁ λᵖ|x₁⟩) = h(λ|y⟩ ⋁ λᵖ|x₂⟩)` implies
`x₁ = x₂`, for `λ ≠ 1`. -/
def MConvex.Cancellative {M : Type u} [EffectMonoid M] {X : Type v}
    (st : MConvex M X) : Prop :=
  ∀ (y x₁ x₂ : X) (l : M), l ≠ 1 →
    st.h (MConvexComb.bin l y x₁) = st.h (MConvexComb.bin l y x₂) → x₁ = x₂

/-- **192IV** (eff.tex:2449, Definition): the category `AConv_M` of abstract
`M`-convex sets with `M`-affine maps (equivalently, the Eilenberg–Moore
category of `𝒟_M`). -/
structure AConvMCat (M : Type u) [EffectMonoid M] : Type (max u (v + 1)) where
  carrier : Type v
  str : MConvex M carrier

instance (M : Type u) [EffectMonoid M] : CoeSort (AConvMCat.{u, v} M) (Type v) :=
  ⟨AConvMCat.carrier⟩

/-- The category structure of `AConv_M` (192IV; that identities and
compositions are affine is `sorry`-ed). -/
noncomputable instance (M : Type u) [EffectMonoid M] :
    Category.{v} (AConvMCat.{u, v} M) where
  Hom X Y := { f : X.carrier → Y.carrier // MConvex.IsAffine X.str Y.str f }
  id X := ⟨_root_.id, sorry⟩
  comp f g := ⟨g.1 ∘ f.1, sorry⟩
  id_comp _ := Subtype.ext rfl
  comp_id _ := Subtype.ext rfl
  assoc _ _ _ := Subtype.ext rfl

/-- **192V.1** (eff.tex:2496, Examples): every convex subset `s` of a real
vector space is a cancellative abstract `[0,1]`-convex set, with
`h(⋁ᵢ λᵢ|xᵢ⟩) = Σᵢ λᵢ xᵢ`. -/
theorem convex_subset_mconvex {V : Type u} [AddCommGroup V] [Module ℝ V]
    (s : Set V) (hs : Convex ℝ s) :
    ∃ st : MConvex I s, st.Cancellative := sorry

/-- **192V.3** (eff.tex:2577, Examples): every (join-)semilattice is an
abstract `2`-convex set (in fact semilattices are *exactly* the abstract
`2`-convex sets). -/
theorem semilattice_two_convex (L : Type u) [SemilatticeSup L] :
    Nonempty (MConvex Bool L) := sorry

/-- **192V.3** (eff.tex:2581, Examples): every semilattice is also an
abstract `[0,1]`-convex set with `h(⋁ᵢ λᵢ|xᵢ⟩) = ⋁_{i : λᵢ ≠ 0} xᵢ`. -/
theorem semilattice_unitInterval_convex (L : Type u) [SemilatticeSup L] :
    Nonempty (MConvex I L) := sorry

/-- **192V.4** (eff.tex:2591, Examples): every cancellative abstract
`[0,1]`-convex set is isomorphic (by an affine bijection) to a convex subset
of a real vector space. -/
theorem cancellative_iso_convex {X : Type u} (st : MConvex I X)
    (hc : st.Cancellative) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℝ V) (s : Set V)
      (_ : Convex ℝ s) (st' : MConvex I s) (f : X → s),
        Function.Bijective f ∧ st.IsAffine st' f := sorry

/-! ### The opposite effect monoid, and states as a convex set (192VII) -/

section Opposite

variable (M : Type u) [EffectMonoid M]

/-- The effect algebra structure of `Mᵐᵒᵖ` — the same effect algebra as `M`
(needed for the opposite effect monoid; data genuine, proofs `sorry`-ed). -/
instance : PCM Mᵐᵒᵖ where
  zero := 0
  Perp a b := Perp a.unop b.unop
  ovee a b h := .op (ovee a.unop b.unop h)
  perp_comm := sorry
  ovee_comm := sorry
  perp_of_ovee_perp := sorry
  perp_ovee_of_ovee_perp := sorry
  ovee_assoc := sorry
  zero_perp := sorry
  zero_ovee := sorry

instance : EffectAlgebra Mᵐᵒᵖ :=
  { (inferInstance : PCM Mᵐᵒᵖ) with
    one := 1
    orth := fun a => .op (orth a.unop)
    perp_orth := sorry
    ovee_orth := sorry
    orth_unique := sorry
    eq_zero_of_perp_one := sorry }

/-- The **opposite effect monoid** `Mᵒᵖ`: same effect algebra, multiplication
reversed (used in 192VII for the convex structure on states). -/
instance : EffectMonoid Mᵐᵒᵖ :=
  { (inferInstance : EffectAlgebra Mᵐᵒᵖ) with
    mul := (· * ·)
    one_mul := sorry
    mul_one := sorry
    mul_assoc := sorry
    distrib := sorry }

end Opposite

section StatConvex

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- **192VII** (eff.tex:2613, Proposition), first half: for an effectus `C`
with scalars `M`, the states `Stat X` form an abstract `Mᵒᵖ`-convex set,
with `h(⋁ᵢ λᵢ|φᵢ⟩) = [φ₁, …, φₙ] ∘ ⟨λ₁, …, λₙ⟩`. -/
theorem stat_mconvex (X : C) :
    Nonempty (MConvex (Scal C)ᵐᵒᵖ (Stat X)) := sorry

/-- **192VII** (eff.tex:2622, Proposition), second half: `Stat f = f ∘ (–)`
is affine for total `f`, and `Stat : Tot C → AConv_{Mᵒᵖ}` is a functor. -/
theorem stat_functor :
    ∃ F : Tot C ⥤ AConvMCat.{v, v} (Scal C)ᵐᵒᵖ,
      ∀ X : Tot C, (F.obj X).carrier = Stat X.base := sorry

end StatConvex

/-! ## Congruences and coproducts of abstract `M`-convex sets (parsec 193) -/

section Congruence

variable {M : Type u} [EffectMonoid M] {X : Type v}

/-- **193II** (`aconv-cong`, eff.tex:2685, Exercise): an equivalence
relation `∼` on an abstract `M`-convex set `(X, h)` is a **congruence** when
`𝒟_M(q)(φ) = 𝒟_M(q)(ψ)` implies `q(h(φ)) = q(h(ψ))`, where `q : X → X/∼` is
the quotient map. -/
def MConvex.IsCongruence (st : MConvex M X) (r : Setoid X) : Prop :=
  ∀ φ ψ : MConvexComb M X,
    φ.map (Quotient.mk r) = ψ.map (Quotient.mk r) →
      Quotient.mk r (st.h φ) = Quotient.mk r (st.h ψ)

/-- **193II.1** (`aconv-cong`, eff.tex:2702, Exercise): the maps `𝒟_M q` and
`𝒟_M 𝒟_M q` are surjective (as is `q` itself). -/
theorem aconv_cong_surjective (r : Setoid X) :
    Function.Surjective
      (fun p : MConvexComb M X => p.map (Quotient.mk r)) ∧
    Function.Surjective
      (fun P : MConvexComb M (MConvexComb M X) =>
        P.map (fun p => p.map (Quotient.mk r))) := sorry

/-- **193II.2** (`aconv-cong`, eff.tex:2705, Exercise): `∼` is a congruence
iff the convex structure `h` descends to `X/∼` — there is (a necessarily
unique) `h_∼` with `h_∼ ∘ 𝒟_M q = q ∘ h`. -/
theorem aconv_cong_iff (st : MConvex M X) (r : Setoid X) :
    st.IsCongruence r ↔
      ∃ h' : MConvexComb M (Quotient r) → Quotient r,
        ∀ p : MConvexComb M X,
          h' (p.map (Quotient.mk r)) = Quotient.mk r (st.h p) := sorry

/-- **193II.3** (`aconv-cong`, eff.tex:2714, Exercise): for a congruence
`∼`, the quotient `(X/∼, h_∼)` is an abstract `M`-convex set and the
quotient map is `M`-affine. -/
theorem aconv_cong_quotient (st : MConvex M X) (r : Setoid X)
    (hc : st.IsCongruence r) :
    ∃ st' : MConvex M (Quotient r),
      st.IsAffine st' (Quotient.mk r) := sorry

/-- **193III** (`affine-kernel-cong`, eff.tex:2726, Exercise): the kernel
`{(x,y) : f(x) = f(y)}` of an affine map `f` between abstract `M`-convex
sets is a congruence. -/
theorem affine_kernel_cong {Y : Type v} (st : MConvex M X)
    (st' : MConvex M Y) (f : X → Y) (hf : st.IsAffine st' f) :
    st.IsCongruence (Setoid.ker f) := sorry

/-- **193IV** (`least-conv-cong`, eff.tex:2732, Exercise): every relation
`R ⊆ X²` on an abstract `M`-convex set is contained in a least congruence.
(The thesis moreover gives a syntactic description of this congruence by
derivations, which is not formalized here.) -/
theorem least_conv_cong (st : MConvex M X) (R : X → X → Prop) :
    ∃ r : Setoid X, st.IsCongruence r ∧ (∀ x y, R x y → r.r x y) ∧
      ∀ r' : Setoid X, st.IsCongruence r' → (∀ x y, R x y → r'.r x y) →
        ∀ x y, r.r x y → r'.r x y := sorry

end Congruence

/-- **193V** (`aconv-coprod`, eff.tex:2778, Proposition): `AConv_M` has
binary coproducts (constructed as a quotient of `𝒟_M(X + Y)` by the least
congruence making `η ∘ κ₁` and `η ∘ κ₂` affine). -/
theorem aconv_coprod (M : Type u) [EffectMonoid M] :
    HasBinaryCoproducts (AConvMCat.{u, v} M) := sorry

/-- The one-element abstract `M`-convex set `1` (193X). -/
def AConvMCat.punit (M : Type u) [EffectMonoid M] : AConvMCat.{u, v} M :=
  ⟨PUnit, ⟨fun _ => PUnit.unit, fun _ => rfl, fun _ => rfl⟩⟩

/-- The free abstract `M`-convex set `(𝒟_M X, μ)` on a set `X` (used in
193X; the algebra laws are the monad laws, `sorry`-ed). -/
noncomputable def AConvMCat.free (M : Type u) [EffectMonoid M] (X : Type v) :
    AConvMCat.{u, max u v} M :=
  ⟨MConvexComb M X, ⟨MConvexComb.mu, sorry, sorry⟩⟩

/-- **193X** (`n-times-one-aconvm`, eff.tex:2954, Exercise), first half: the
one-element convex set is the final object of `AConv_M`. -/
theorem n_times_one_aconvm_terminal (M : Type u) [EffectMonoid M] :
    Nonempty (IsTerminal (AConvMCat.punit.{u, v} M)) := sorry

/-- **193X** (`n-times-one-aconvm`, eff.tex:2954, Exercise), second half: in
`AConv_M` the `n`-fold coproduct `n · 1 = 1 + ⋯ + 1` is isomorphic to
`𝒟_M {1, …, n}`. -/
theorem n_times_one_aconvm (M : Type u) [EffectMonoid M] (n : ℕ)
    [HasFiniteCoproducts (AConvMCat.{u, u} M)] :
    Nonempty ((∐ fun _ : Fin n => AConvMCat.punit.{u, u} M) ≅
      AConvMCat.free M (ULift.{u} (Fin n))) := sorry

/-! ## `AConv_M` is almost an effectus (parsec 194) -/

section AlmostEffectus

variable (M : Type u) [EffectMonoid M]

/-- **194I** (`aconvalmosteffectus`, eff.tex:2968, Proposition), part 1:
`AConv_M` has finite coproducts (binary ones by 193V; the empty set is the
initial object). -/
theorem aconvalmosteffectus_coproducts :
    HasFiniteCoproducts (AConvMCat.{u, v} M) := sorry

/-- **194I** (`aconvalmosteffectus`, eff.tex:2968, Proposition), part 2:
`AConv_M` has a final object (the one-element convex set, 193X). -/
theorem aconvalmosteffectus_terminal :
    HasTerminal (AConvMCat.{u, v} M) := sorry

/-- **194I** (`aconvalmosteffectus`, eff.tex:2979, Proposition), part 3: the
cotuples `[κ₁,κ₂,κ₂], [κ₂,κ₁,κ₂] : 1+1+1 → 1+1` are jointly monic in
`AConv_M`. -/
theorem aconvalmosteffectus_jointlyMonic
    [HasFiniteCoproducts (AConvMCat.{u, v} M)]
    [HasTerminal (AConvMCat.{u, v} M)] :
    JointlyMonic
      (coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr :
        ((⊤_ AConvMCat.{u, v} M) ⨿ (⊤_ AConvMCat.{u, v} M)) ⨿
          (⊤_ AConvMCat.{u, v} M) ⟶
        (⊤_ AConvMCat.{u, v} M) ⨿ (⊤_ AConvMCat.{u, v} M))
      (coprod.desc (coprod.desc coprod.inr coprod.inl) coprod.inr) := sorry

/-- **194I** (`aconvalmosteffectus`, eff.tex:3008, Proposition), part 4: the
right pullback squares of the effectus axioms (`(κ₁; !)`-squares) hold in
`AConv_M`; only the left squares remain open (settled in 196II when `M` is
an effect divisoid). -/
theorem aconvalmosteffectus_kappaPullback
    [HasFiniteCoproducts (AConvMCat.{u, v} M)]
    [HasTerminal (AConvMCat.{u, v} M)] (X Y : AConvMCat.{u, v} M) :
    IsPullback (terminal.from X) (coprod.inl : X ⟶ X ⨿ Y)
      (coprod.inl : (⊤_ AConvMCat.{u, v} M) ⟶ _)
      (coprod.map (terminal.from X) (terminal.from Y)) := sorry

end AlmostEffectus

/-! ## Effect divisoids (parsec 195) -/

/-- **195II** (`dfn-effect-divisoid`, eff.tex:3187, Definition): an **effect
divisoid** is an effect monoid `M` with a partial division `a/b` (defined
for `a ≼ b`; formalized as a total operation whose axioms are guarded by
`a ≼ b`, cf. the *Beware* 195IIa) such that

1. `a/b` is the unique element with `a/b ≼ b/b` and `b ⊙ (a/b) = a`;
2. `a ≼ a/a`; and
3. `(a/a)/(a/a) = a/a`. -/
class EffectDivisoid (M : Type u) [EffectMonoid M] where
  /-- The partial division `a/b` (meaningful for `a ≼ b`). -/
  div : M → M → M
  div_le : ∀ {a b : M}, a ≼ b → div a b ≼ div b b
  mul_div : ∀ {a b : M}, a ≼ b → b * div a b = a
  div_unique : ∀ {a b c : M}, a ≼ b → c ≼ div b b → b * c = a → c = div a b
  le_div_self : ∀ a : M, a ≼ div a a
  div_div_self : ∀ a : M, div (div a a) (div a a) = div a a

export EffectDivisoid (div)

section DivisoidBasics

variable {M : Type u} [EffectMonoid M] [EffectDivisoid M]

/-- **195IV.1** (`exc-divisoid-basics`, eff.tex:3226, Exercise): `0/0 = 0`,
`1/1 = 1`, `a/1 = a`, `(a/a) ⊙ (a/a) = a/a` and `(a ⊙ b)/a = (a/a) ⊙ b`. -/
theorem exc_divisoid_basics_1 (a b : M) :
    div (0 : M) 0 = 0 ∧ div (1 : M) 1 = 1 ∧ div a 1 = a ∧
      div a a * div a a = div a a ∧ div (a * b) a = div a a * b := sorry

/-- **195IV.2** (`exc-divisoid-basics`, eff.tex:3233, Exercise): for
`a ≼ b ≼ c` we have `(b/c) ⊙ (a/b) = a/c`. -/
theorem exc_divisoid_basics_2 {a b c : M} (hab : a ≼ b) (hbc : b ≼ c) :
    div b c * div a b = div a c := sorry

end DivisoidBasics

/-- **195V.1** (eff.tex:3243, Examples): `[0,1]` is an effect divisoid with
`a/b` the ordinary quotient (and `0/0 = 0`). -/
noncomputable instance unitInterval.effectDivisoid : EffectDivisoid I where
  div a b := if (b : ℝ) = 0 then 0 else ⟨(a : ℝ) / b, sorry⟩
  div_le := sorry
  mul_div := sorry
  div_unique := sorry
  le_div_self := sorry
  div_div_self := sorry

/-- **195V.1** (eff.tex:3246, Examples): the two-element effect monoid `2`
is an effect divisoid (with `a/b = a`). -/
instance : EffectDivisoid Bool where
  div a _ := a
  div_le := sorry
  mul_div := sorry
  div_unique := sorry
  le_div_self := sorry
  div_div_self := sorry

/-- The product of two effect monoids, with componentwise multiplication
(needed for 195V.2; proof obligations `sorry`-ed). -/
instance prodEffectMonoid (M N : Type u) [EffectMonoid M] [EffectMonoid N] :
    EffectMonoid (M × N) :=
  { prodEffectAlgebra M N with
    mul := fun p q => (p.1 * q.1, p.2 * q.2)
    one_mul := sorry
    mul_one := sorry
    mul_assoc := sorry
    distrib := sorry }

/-- **195V.2** (eff.tex:3249, Examples): the product of two effect divisoids
is an effect divisoid, with componentwise division (in particular `[0,1]ⁿ`
is an effect divisoid). -/
instance prodEffectDivisoid (M N : Type u) [EffectMonoid M] [EffectMonoid N]
    [EffectDivisoid M] [EffectDivisoid N] : EffectDivisoid (M × N) where
  div p q := (div p.1 q.1, div p.2 q.2)
  div_le := sorry
  mul_div := sorry
  div_unique := sorry
  le_div_self := sorry
  div_div_self := sorry

/-- The effect monoid on the unit interval `[0,1]_{C(X)}` of the continuous
real functions on a topological space `X` (needed for 195VI; data genuine,
proof obligations `sorry`-ed). -/
noncomputable def continuousUnitIntervalEffectMonoid (X : Type u)
    [TopologicalSpace X] : EffectMonoid (Set.Icc (0 : C(X, ℝ)) 1) where
  zero := ⟨0, sorry⟩
  one := ⟨1, sorry⟩
  Perp f g := (f : C(X, ℝ)) + g ≤ 1
  ovee f g _ := ⟨(f : C(X, ℝ)) + g, sorry⟩
  orth f := ⟨1 - (f : C(X, ℝ)), sorry⟩
  mul f g := ⟨(f : C(X, ℝ)) * g, sorry⟩
  perp_comm := sorry
  ovee_comm := sorry
  perp_of_ovee_perp := sorry
  perp_ovee_of_ovee_perp := sorry
  ovee_assoc := sorry
  zero_perp := sorry
  zero_ovee := sorry
  perp_orth := sorry
  ovee_orth := sorry
  orth_unique := sorry
  eq_zero_of_perp_one := sorry
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  distrib := sorry

/-- A topological space is **basically disconnected** when the closure of
the support of every continuous real function is open (195VI). -/
def BasicallyDisconnected (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ f : C(X, ℝ), IsOpen (closure (Function.support f))

/-- **195VI** (`basic-divisoid-equiv`, eff.tex:3275, Exercise\*): for a
compact Hausdorff space `X`, the unit interval of `C(X)` is an effect
divisoid if and only if `X` is basically disconnected (equivalently, `C(X)`
is σ-Dedekind complete).  In particular the unit interval of `C[0,1]` is
*not* an effect divisoid, while that of `L^∞[0,1]` is. -/
theorem basic_divisoid_equiv (X : Type u) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] :
    letI := continuousUnitIntervalEffectMonoid X
    (Nonempty (EffectDivisoid (Set.Icc (0 : C(X, ℝ)) 1)) ↔
      BasicallyDisconnected X) := sorry

/-- **195VII** (eff.tex:3328, Proposition): if `a ⊥ b` and `a ⋁ b ≼ c` in an
effect divisoid, then `(a ⋁ b)/c = a/c ⋁ b/c`. -/
theorem divisoid_div_ovee {M : Type u} [EffectMonoid M] [EffectDivisoid M]
    {a b c : M} (hab : Perp a b) (hc : ovee a b hab ≼ c) :
    ∃ h' : Perp (div a c) (div b c),
      div (ovee a b hab) c = ovee (div a c) (div b c) h' := sorry

/-! ## `AConv_M` is an effectus for an effect divisoid `M` (parsec 196) -/

/-- **196II** (`aconvm-is-effectus`, eff.tex:3381, Theorem): if `M` is an
effect divisoid, then `AConv_M` is an effectus (in total form). -/
theorem aconvm_is_effectus (M : Type u) [EffectMonoid M] [EffectDivisoid M] :
    Nonempty (EffectusTotalStructure (AConvMCat.{u, v} M)) := sorry

end Theses.B.Eff
