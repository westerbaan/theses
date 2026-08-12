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
  effect module structure over it; both are instances (they are the claims
  of 190II) and both are fully proved.
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

/-! ### Helper lemmas on iterated partial sums in a PCM -/

/-- A one-element list sums to its only entry. -/
theorem isSumOf_singleton {M : Type u} [PCM M] (a : M) :
    PCM.IsSumOf [a] a := by
  have h := PCM.IsSumOf.cons (PCM.IsSumOf.nil (M := M)) (PCM.perp_zero a)
  rwa [PCM.ovee_zero] at h

/-- The sum of a one-element list is its only entry. -/
theorem eq_of_isSumOf_singleton {M : Type u} [PCM M] {a s : M}
    (h : PCM.IsSumOf [a] s) : s = a := by
  cases h with
  | cons hl hp =>
      cases hl
      exact PCM.ovee_zero a hp

/-- Sums of concatenated lists: if `l₁` sums to `s₁`, `l₂` to `s₂` and
`s₁ ⊥ s₂`, then `l₁ ++ l₂` sums to `s₁ ⋁ s₂`. -/
theorem isSumOf_append {M : Type u} [PCM M] {l₁ l₂ : List M} {s₁ s₂ : M}
    (h₁ : PCM.IsSumOf l₁ s₁) (h₂ : PCM.IsSumOf l₂ s₂) :
    ∀ h : Perp s₁ s₂, PCM.IsSumOf (l₁ ++ l₂) (ovee s₁ s₂ h) := by
  induction h₁ with
  | nil =>
      intro h
      have hz : ovee (0 : M) s₂ h = s₂ := PCM.zero_ovee s₂
      rw [List.nil_append, hz]
      exact h₂
  | @cons a l s hl hp ih =>
      intro h
      have hps : Perp s s₂ := PCM.perp_of_ovee_perp hp h
      have hcons := PCM.IsSumOf.cons (ih hps) (PCM.perp_ovee_of_ovee_perp hp h)
      rw [← PCM.ovee_assoc hp h] at hcons
      exact hcons

/-- A two-element list sums to the partial sum of its entries. -/
theorem isSumOf_pair {M : Type u} [PCM M] (a b : M) (h : Perp a b) :
    PCM.IsSumOf [a, b] (ovee a b h) :=
  isSumOf_append (isSumOf_singleton a) (isSumOf_singleton b) h

/-- Transport a sum along an equality of its value. -/
theorem isSumOf_congr {M : Type u} [PCM M] {l : List M} {s t : M}
    (h : PCM.IsSumOf l s) (e : s = t) : PCM.IsSumOf l t := e ▸ h

/-- A four-element list sums to `(a ⋁ b) ⋁ (c ⋁ d)`. -/
theorem isSumOf_four {M : Type u} [PCM M] (a b c d s : M)
    (hab : Perp a b) (hcd : Perp c d)
    (h : Perp (ovee a b hab) (ovee c d hcd))
    (e : ovee (ovee a b hab) (ovee c d hcd) h = s) :
    PCM.IsSumOf [a, b, c, d] s :=
  isSumOf_congr (isSumOf_append (isSumOf_pair a b hab) (isSumOf_pair c d hcd) h) e

/-- Sums in a product effect algebra are computed componentwise. -/
theorem isSumOf_prod {M N : Type u} [EffectAlgebra M] [EffectAlgebra N]
    {l : List (M × N)} {s₁ : M} {s₂ : N}
    (h₁ : PCM.IsSumOf (l.map Prod.fst) s₁)
    (h₂ : PCM.IsSumOf (l.map Prod.snd) s₂) :
    PCM.IsSumOf l (s₁, s₂) := by
  induction l generalizing s₁ s₂ with
  | nil => cases h₁; cases h₂; exact PCM.IsSumOf.nil
  | cons a l ih =>
      rw [List.map_cons] at h₁ h₂
      cases h₁ with
      | cons hl₁ hp₁ =>
        cases h₂ with
        | cons hl₂ hp₂ => exact PCM.IsSumOf.cons (ih hl₁ hl₂) ⟨hp₁, hp₂⟩

/-- Helper: multiplication in an effect monoid distributes over a partial
sum in its right argument (the special case `b = d = 0` of `distrib`). -/
theorem emon_mul_ovee {M : Type u} [EffectMonoid M] (x : M) {p q : M}
    (hpq : Perp p q) :
    ∃ h' : Perp (x * p) (x * q),
      x * ovee p q hpq = ovee (x * p) (x * q) h' := by
  have hd := EffectMonoid.distrib (PCM.perp_zero x) hpq
  rw [PCM.ovee_zero x (PCM.perp_zero x), (exc_emonzero p).2,
    (exc_emonzero q).2] at hd
  obtain ⟨t1, h1, hp1, e1⟩ := PCM.isSumOf_cons_iff.mp hd
  obtain ⟨t2, h2, hp2, e2⟩ := PCM.isSumOf_cons_iff.mp h1
  obtain ⟨t3, h3, hp3, e3⟩ := PCM.isSumOf_cons_iff.mp h2
  obtain ⟨t4, h4, hp4, e4⟩ := PCM.isSumOf_cons_iff.mp h3
  have ht4 : t4 = 0 := PCM.isSumOf_nil_iff.mp h4
  have ht3 : t3 = 0 := by rw [← e4, PCM.zero_ovee' t4 hp4]; exact ht4
  have ht2 : t2 = x * q := by
    rw [← e3, PCM.ovee_congr rfl ht3 hp3 (PCM.perp_zero (x * q))]
    exact PCM.ovee_zero _ _
  have ht1 : t1 = x * q := by
    rw [← e2, PCM.zero_ovee' t2 hp2]; exact ht2
  have hp' : Perp (x * p) (x * q) := by rw [← ht1]; exact hp1
  refine ⟨hp', ?_⟩
  rw [← e1]
  exact PCM.ovee_congr rfl ht1 hp1 hp'

/-- Helper: `0 ≼ a` in any PCM. -/
theorem pcm_zero_le {M : Type u} [PCM M] (a : M) : (0 : M) ≼ a :=
  ⟨a, PCM.zero_perp a, PCM.zero_ovee a⟩

/-- Helper: `a ≼ 1` in any effect algebra (witness `aᵖ`). -/
theorem ea_le_one {E : Type u} [EffectAlgebra E] (a : E) : a ≼ 1 :=
  ⟨orth a, EffectAlgebra.perp_orth a, EffectAlgebra.ovee_orth a⟩

/-- Helper: an effect algebra with `1 = 0` is trivial. -/
theorem eq_zero_of_one_eq_zero {E : Type u} [EffectAlgebra E] (h : (1 : E) = 0)
    (a : E) : a = 0 := by
  obtain ⟨c, hc, hac⟩ := ea_le_one a
  rw [h] at hac
  exact (eabasics_positivity hc hac).1

/-- Helper: multiplication in an effect monoid is monotone in its right
argument (a consequence of distributivity). -/
theorem emon_mul_le_mul_left {M : Type u} [EffectMonoid M] (x : M) {c d : M}
    (h : c ≼ d) : x * c ≼ x * d := by
  obtain ⟨e, he, rfl⟩ := h
  have hd := EffectMonoid.distrib (PCM.perp_zero x) he
  rw [PCM.ovee_zero x (PCM.perp_zero x)] at hd
  -- the first entry of a sum is below the sum
  have key : ∀ s : M, PCM.IsSumOf [x * c, 0 * c, x * e, 0 * e] s → x * c ≼ s := by
    intro s hs
    cases hs with
    | cons hl hp => exact ⟨_, hp, rfl⟩
  exact key _ hd

/-- Helper: `a ⊙ b ≼ a` in an effect monoid. -/
theorem emon_mul_le_left {M : Type u} [EffectMonoid M] (x y : M) : x * y ≼ x := by
  have h := emon_mul_le_mul_left x (ea_le_one y)
  rwa [EffectMonoid.mul_one] at h

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

/-- Helper (`one-m-is-id`, 181XIII, eff.tex:1181): the truth predicate on the
effect object `I` is the identity.  (Proof of the thesis: `1 = id ⋁ idᵖ` in
the effect algebra `C(I,I)`, so `1 ∘ 1 = 1 ⋁ (1 ∘ idᵖ)`; by the zero–one
axiom `1 ∘ idᵖ = 0`, whence `idᵖ = 0` and `id = 1`.) -/
theorem truth_effObj_eq_id : truth (effObj C) = 𝟙 (effObj C) := by
  set e : effObj C ⟶ effObj C := orth (𝟙 (effObj C)) with he
  have hperp : Perp (𝟙 (effObj C)) e := EffectAlgebra.perp_orth _
  have hovee : ovee (𝟙 (effObj C)) e hperp = truth (effObj C) :=
    EffectAlgebra.ovee_orth _
  obtain ⟨h', -⟩ := FinPAC.comp_ovee hperp (truth (effObj C))
  rw [Category.id_comp] at h'
  have hz : e ≫ truth (effObj C) = 0 :=
    EffectAlgebra.eq_zero_of_perp_one (PCM.perp_comm h')
  have he0 : e = 0 := EffectusPartialForm.eq_zero_of_one_zero hz
  have h2 := eabasics_orth_orth (𝟙 (effObj C))
  rw [← he, he0, eabasics_orth_zero] at h2
  exact h2

/-- **190II.2** (`dfn-mandso`, eff.tex:2090, Definition): the scalars `Scal C`
form an effect monoid with multiplication `λ ⊙ μ = λ ∘ μ` (composition; note
`1_M = id` by 181XIII). -/
noncomputable instance scalEffectMonoid : EffectMonoid (Scal C) :=
  { predEffectAlgebra (effObj C) with
    mul := fun l m => m ≫ l
    one_mul := fun a => by
      show a ≫ truth (effObj C) = a
      rw [truth_effObj_eq_id, Category.comp_id]
    mul_one := fun a => by
      show truth (effObj C) ≫ a = a
      rw [truth_effObj_eq_id, Category.id_comp]
    mul_assoc := fun a b c => (Category.assoc c b a).symm
    distrib := by
      intro a b c d hab hcd
      obtain ⟨h1, e1⟩ := FinPAC.comp_ovee hcd (ovee a b hab)
      obtain ⟨h2, e2⟩ := FinPAC.ovee_comp hab c
      obtain ⟨h3, e3⟩ := FinPAC.ovee_comp hab d
      have hp : Perp (ovee (c ≫ a) (c ≫ b) h2) (ovee (d ≫ a) (d ≫ b) h3) := by
        rw [← e2, ← e3]; exact h1
      have key : ovee c d hcd ≫ ovee a b hab
          = ovee (ovee (c ≫ a) (c ≫ b) h2) (ovee (d ≫ a) (d ≫ b) h3) hp :=
        e1.trans (PCM.ovee_congr e2 e3 h1 hp)
      show PCM.IsSumOf [c ≫ a, c ≫ b, d ≫ a, d ≫ b] (ovee c d hcd ≫ ovee a b hab)
      rw [key]
      exact isSumOf_append (isSumOf_pair _ _ h2) (isSumOf_pair _ _ h3) hp }

/-- **190II.3** (`dfn-mandso`, eff.tex:2097, Definition): a **real effectus**
is an effectus whose effect monoid of scalars is isomorphic to `[0,1]`. -/
def IsRealEffectus (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop :=
  ∃ φ : EffectMonoidHom (Scal C) I, Function.Bijective φ.toFun

/-- **190II.4** (`dfn-mandso`, eff.tex:2101, Definition): scalar
multiplication `λ · p = λ ∘ p` turns each `Pred X` into an effect module
over the scalars `Scal C`. -/
noncomputable instance predEffectModule (X : C) :
    EffectModule (Scal C) (Pred X) where
  smul l p := p ≫ l
  mul_smul l m a := (Category.assoc a m l).symm
  smul_perp := by
    intro l a b h
    exact Exists.imp (fun _ hh => hh.symm) (FinPAC.comp_ovee h l)
  perp_smul := by
    intro l m h a
    exact Exists.imp (fun _ hh => hh.symm) (FinPAC.ovee_comp h a)
  one_smul a := by
    show a ≫ truth (effObj C) = a
    rw [truth_effObj_eq_id, Category.comp_id]

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
theorem exc_rng_eff_no_hom : IsEmpty (ZMod 2 →+* ℤ) := by
  constructor
  intro f
  have h : ((1 : ZMod 2) + 1) = 0 := by decide
  have h2 := congrArg f h
  rw [map_add, map_one, map_zero] at h2
  norm_num at h2

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
  ⟨fun y => if y = x then 1 else 0, by
    by_cases h1 : (1 : M) = 0
    · refine ⟨[], List.nodup_nil, fun y => ?_, ?_⟩
      · have hy0 : (if y = x then (1 : M) else 0) = 0 := by
          by_cases hyx : y = x
          · rw [if_pos hyx, h1]
          · rw [if_neg hyx]
        simp [hy0]
      · rw [List.map_nil, h1]
        exact PCM.IsSumOf.nil
    · refine ⟨[x], List.nodup_singleton x, fun y => ?_, ?_⟩
      · rw [List.mem_singleton]
        refine ⟨fun hy => ?_, fun hy => ?_⟩
        · rw [if_pos hy]; exact h1
        · by_contra hyx; rw [if_neg hyx] at hy; exact hy rfl
      · have hl : (List.map (fun y => if y = x then (1 : M) else 0) [x]) = [1] := by
          simp
        rw [hl]
        exact isSumOf_singleton 1⟩

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

/-- Two formal convex combinations with the same values are equal. -/
theorem ext {X : Type v} {p q : MConvexComb M X} (h : p.toFun = q.toFun) :
    p = q := by
  cases p; cases q; cases h; rfl

/-- The pushforward along the identity is the identity (read off from the
specification of `map`). -/
theorem map_id {X : Type v} (p : MConvexComb M X) :
    p.map _root_.id = p := by
  have hspec := (exists_map p (_root_.id : X → X)).choose_spec
  refine MConvexComb.ext ?_
  funext y
  by_cases hy : p.toFun y = 0
  · have h := hspec y [] List.nodup_nil (by
      intro x
      constructor
      · intro hx; simp at hx
      · rintro ⟨hx0, rfl⟩; exact absurd hy hx0)
    rw [List.map_nil] at h
    show (exists_map p _root_.id).choose.toFun y = p.toFun y
    rw [PCM.isSumOf_nil_iff.mp h, hy]
  · have h := hspec y [y] (List.nodup_singleton y) (by
      intro x
      constructor
      · intro hx
        rw [List.mem_singleton] at hx
        subst hx
        exact ⟨hy, rfl⟩
      · intro hx
        exact List.mem_singleton.mpr hx.2)
    rw [List.map_cons, List.map_nil] at h
    show (exists_map p _root_.id).choose.toFun y = p.toFun y
    exact eq_of_isSumOf_singleton h

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
/-- Helper for `bin` (192II): the function which is `1` at `x` when `x = y`,
and otherwise `λ` at `x` and `λᵖ` at `y`, is a formal convex combination.
(Four cases: `x = y`, `λ = 0`, `λᵖ = 0`, and the generic one; the degenerate
effect monoid `1 = 0` is dealt with first.) -/
theorem bin_sum_one {X : Type v} (f : X → M) (l : M) (x y : X)
    (hf : ∀ z, f z = if x = y then (if z = x then 1 else 0)
      else if z = x then l else if z = y then orth l else 0) :
    ∃ s : List X, s.Nodup ∧ (∀ z, z ∈ s ↔ f z ≠ 0) ∧
      PCM.IsSumOf (s.map f) 1 := by
  by_cases h1 : (1 : M) = 0
  · refine ⟨[], List.nodup_nil, fun z => ?_, ?_⟩
    · simp only [List.not_mem_nil, false_iff, ne_eq, not_not]
      exact eq_zero_of_one_eq_zero h1 _
    · rw [List.map_nil, h1]
      exact PCM.IsSumOf.nil
  by_cases hxy : x = y
  · have hfx : f x = 1 := by rw [hf x, if_pos hxy, if_pos rfl]
    have hfz : ∀ z, z ≠ x → f z = 0 := by
      intro z hz; rw [hf z, if_pos hxy, if_neg hz]
    refine ⟨[x], List.nodup_singleton x, fun z => ?_, ?_⟩
    · rw [List.mem_singleton]
      refine ⟨?_, fun hz => ?_⟩
      · rintro rfl; rw [hfx]; exact h1
      · by_contra hzx; exact hz (hfz z hzx)
    · rw [List.map_cons, List.map_nil, hfx]
      exact isSumOf_singleton 1
  -- `x ≠ y` from here on
  have hfx : f x = l := by rw [hf x, if_neg hxy, if_pos rfl]
  have hfy : f y = orth l := by
    rw [hf y, if_neg hxy, if_neg (fun h : y = x => hxy h.symm), if_pos rfl]
  have hfz : ∀ z, z ≠ x → z ≠ y → f z = 0 := by
    intro z hzx hzy; rw [hf z, if_neg hxy, if_neg hzx, if_neg hzy]
  by_cases hl0 : l = 0
  · have hfy1 : f y = 1 := by rw [hfy, hl0, eabasics_orth_zero]
    refine ⟨[y], List.nodup_singleton y, fun z => ?_, ?_⟩
    · rw [List.mem_singleton]
      refine ⟨?_, fun hz => ?_⟩
      · rintro rfl; rw [hfy1]; exact h1
      · by_contra hzy
        by_cases hzx : z = x
        · exact hz (by rw [hzx, hfx, hl0])
        · exact hz (hfz z hzx hzy)
    · rw [List.map_cons, List.map_nil, hfy1]
      exact isSumOf_singleton 1
  by_cases hlo : orth l = 0
  · have hl1 : l = 1 := by
      have h := eabasics_orth_orth l
      rw [hlo, eabasics_orth_zero] at h
      exact h.symm
    refine ⟨[x], List.nodup_singleton x, fun z => ?_, ?_⟩
    · rw [List.mem_singleton]
      refine ⟨?_, fun hz => ?_⟩
      · rintro rfl; rw [hfx]; exact hl0
      · by_contra hzx
        by_cases hzy : z = y
        · exact hz (by rw [hzy, hfy, hlo])
        · exact hz (hfz z hzx hzy)
    · rw [List.map_cons, List.map_nil, hfx, hl1]
      exact isSumOf_singleton 1
  refine ⟨[x, y], ?_, fun z => ?_, ?_⟩
  · simp [hxy]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨?_, fun hz => ?_⟩
    · rintro (rfl | rfl)
      · rw [hfx]; exact hl0
      · rw [hfy]; exact hlo
    · by_contra hcon
      push_neg at hcon
      exact hz (hfz z hcon.1 hcon.2)
  · rw [List.map_cons, List.map_cons, List.map_nil, hfx, hfy]
    have h := isSumOf_pair l (orth l) (EffectAlgebra.perp_orth l)
    rwa [EffectAlgebra.ovee_orth l] at h

open Classical in
/-- The binary convex combination `λ|x⟩ ⋁ λᵖ|y⟩` (used for cancellativity,
192IV). -/
noncomputable def bin {X : Type v} (l : M) (x y : X) : MConvexComb M X :=
  ⟨fun z =>
    if x = y then (if z = x then 1 else 0)
    else if z = x then l else if z = y then orth l else 0,
   bin_sum_one _ l x y fun _ => rfl⟩

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
  id X := ⟨_root_.id, fun p => by rw [MConvexComb.map_id]; rfl⟩
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
(needed for the opposite effect monoid). -/
instance : PCM Mᵐᵒᵖ where
  zero := 0
  Perp a b := Perp a.unop b.unop
  ovee a b h := .op (ovee a.unop b.unop h)
  perp_comm h := PCM.perp_comm h
  ovee_comm h := congrArg MulOpposite.op (PCM.ovee_comm h)
  perp_of_ovee_perp hab h := PCM.perp_of_ovee_perp hab h
  perp_ovee_of_ovee_perp hab h := PCM.perp_ovee_of_ovee_perp hab h
  ovee_assoc hab h := congrArg MulOpposite.op (PCM.ovee_assoc hab h)
  zero_perp a := PCM.zero_perp a.unop
  zero_ovee a := congrArg MulOpposite.op (PCM.zero_ovee a.unop)

/-- Sums in `Mᵐᵒᵖ` are the sums of `M`, transported along `op`. -/
theorem isSumOf_op {l : List M} {s : M} (h : PCM.IsSumOf l s) :
    PCM.IsSumOf (l.map MulOpposite.op) (MulOpposite.op s) := by
  induction h with
  | nil => exact PCM.IsSumOf.nil
  | @cons a l s hl hp ih => exact PCM.IsSumOf.cons ih hp

instance : EffectAlgebra Mᵐᵒᵖ :=
  { (inferInstance : PCM Mᵐᵒᵖ) with
    one := 1
    orth := fun a => .op (orth a.unop)
    perp_orth := fun a => EffectAlgebra.perp_orth a.unop
    ovee_orth := fun a => congrArg MulOpposite.op (EffectAlgebra.ovee_orth a.unop)
    orth_unique := fun {a b} h h1 =>
      congrArg MulOpposite.op
        (EffectAlgebra.orth_unique (a := a.unop) (b := b.unop) h
          (congrArg MulOpposite.unop h1))
    eq_zero_of_perp_one := fun {a} h =>
      congrArg MulOpposite.op (EffectAlgebra.eq_zero_of_perp_one (a := a.unop) h) }

/-- The **opposite effect monoid** `Mᵒᵖ`: same effect algebra, multiplication
reversed (used in 192VII for the convex structure on states). -/
instance : EffectMonoid Mᵐᵒᵖ :=
  { (inferInstance : EffectAlgebra Mᵐᵒᵖ) with
    mul := (· * ·)
    one_mul := fun a => congrArg MulOpposite.op (EffectMonoid.mul_one a.unop)
    mul_one := fun a => congrArg MulOpposite.op (EffectMonoid.one_mul a.unop)
    mul_assoc := fun a b c =>
      congrArg MulOpposite.op
        (EffectMonoid.mul_assoc c.unop b.unop a.unop).symm
    distrib := by
      intro a b c d hab hcd
      have hperm :
          ([c.unop * a.unop, d.unop * a.unop, c.unop * b.unop, d.unop * b.unop] :
            List M).Perm
            [c.unop * a.unop, c.unop * b.unop, d.unop * a.unop, d.unop * b.unop] :=
        List.Perm.cons _ (List.Perm.swap _ _ _)
      exact isSumOf_op _ (PCM.isSumOf_perm hperm (EffectMonoid.distrib hcd hab)) }

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
      div a a * div a a = div a a ∧ div (a * b) a = div a a * b := by
  -- `a/1 = 1 ⊙ (a/1) = a`; the rest is uniqueness of the division.
  have hdiv_one : ∀ x : M, div x 1 = x := by
    intro x
    have h := EffectDivisoid.mul_div (ea_le_one x)
    rwa [EffectMonoid.one_mul] at h
  have hself : ∀ x : M, x * div x x = x := fun x =>
    EffectDivisoid.mul_div (pcm_preorder_refl x)
  refine ⟨?_, hdiv_one 1, hdiv_one a, ?_, ?_⟩
  · -- `0 ≼ 0/0` and `0 ⊙ 0 = 0`, so `0 = 0/0` by uniqueness.
    exact (EffectDivisoid.div_unique (pcm_preorder_refl (0 : M))
      (pcm_zero_le _) (exc_emonzero (0 : M)).1).symm
  · -- `(a/a) ⊙ (a/a) ≼ a/a` and `a ⊙ (a/a) ⊙ (a/a) = a ⊙ (a/a) = a`.
    refine EffectDivisoid.div_unique (pcm_preorder_refl a)
      (emon_mul_le_left _ _) ?_
    rw [← EffectMonoid.mul_assoc, hself a, hself a]
  · -- `(a/a) ⊙ b ≼ a/a` and `a ⊙ (a/a) ⊙ b = a ⊙ b`.
    refine (EffectDivisoid.div_unique (emon_mul_le_left a b)
      (emon_mul_le_left _ _) ?_).symm
    rw [← EffectMonoid.mul_assoc, hself a]

/-- **195IV.2** (`exc-divisoid-basics`, eff.tex:3233, Exercise): for
`a ≼ b ≼ c` we have `(b/c) ⊙ (a/b) = a/c`. -/
theorem exc_divisoid_basics_2 {a b c : M} (hab : a ≼ b) (hbc : b ≼ c) :
    div b c * div a b = div a c := by
  -- `(b/c) ⊙ (a/b) ≼ b/c ≼ c/c` and `c ⊙ (b/c) ⊙ (a/b) = b ⊙ (a/b) = a`.
  refine EffectDivisoid.div_unique (pcm_preorder_trans hab hbc)
    (pcm_preorder_trans (emon_mul_le_left _ _) (EffectDivisoid.div_le hbc)) ?_
  rw [← EffectMonoid.mul_assoc, EffectDivisoid.mul_div hbc,
    EffectDivisoid.mul_div hab]

end DivisoidBasics

/-- Helper: the algebraic order `≼` of the effect algebra `[0,1]` is the
usual order of the reals. -/
theorem unitInterval_le_iff {a b : I} : a ≼ b ↔ (a : ℝ) ≤ (b : ℝ) := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    show (a : ℝ) ≤ (a : ℝ) + (c : ℝ)
    linarith [c.2.1]
  · intro h
    refine ⟨⟨(b : ℝ) - (a : ℝ), by linarith [a.2.1], by linarith [b.2.2, a.2.1]⟩,
      ?_, ?_⟩
    · show (a : ℝ) + ((b : ℝ) - (a : ℝ)) ≤ 1
      linarith [b.2.2]
    · apply Subtype.ext
      show (a : ℝ) + ((b : ℝ) - (a : ℝ)) = (b : ℝ)
      ring

/-- **195V.1** (eff.tex:3243, Examples): `[0,1]` is an effect divisoid with
`a/b` the ordinary quotient (and `0/0 = 0`). -/
noncomputable instance unitInterval.effectDivisoid : EffectDivisoid I where
  -- `div` must be *total*, while the thesis's division is only meaningful for
  -- `a ≼ b`; we truncate at `1`, which changes nothing when `a ≤ b` (then
  -- `a/b ≤ 1`), so this really is "the ordinary quotient" where it matters.
  div a b := if (b : ℝ) = 0 then 0
    else ⟨min ((a : ℝ) / b) 1,
      le_min (div_nonneg a.2.1 b.2.1) zero_le_one, min_le_right _ _⟩
  div_le := by
    intro a b _
    refine unitInterval_le_iff.mpr ?_
    split_ifs with hb
    · exact le_rfl
    · show min ((a : ℝ) / (b : ℝ)) 1 ≤ min ((b : ℝ) / (b : ℝ)) 1
      rw [div_self hb, min_self]
      exact min_le_right _ _
  mul_div := by
    intro a b hab
    have hab' : (a : ℝ) ≤ (b : ℝ) := unitInterval_le_iff.mp hab
    apply Subtype.ext
    split_ifs with hb
    · have ha0 : (a : ℝ) = 0 := le_antisymm (by rw [← hb]; exact hab') a.2.1
      show (b : ℝ) * (0 : ℝ) = (a : ℝ)
      rw [ha0, mul_zero]
    · have hbne : (b : ℝ) ≠ 0 := hb
      have hb0 : (0 : ℝ) < (b : ℝ) := lt_of_le_of_ne b.2.1 (Ne.symm hb)
      have hmin : min ((a : ℝ) / (b : ℝ)) 1 = (a : ℝ) / (b : ℝ) :=
        min_eq_left ((div_le_one hb0).mpr hab')
      show (b : ℝ) * min ((a : ℝ) / (b : ℝ)) 1 = (a : ℝ)
      rw [hmin]
      field_simp
  div_unique := by
    intro a b c hab hc hbc
    have hab' : (a : ℝ) ≤ (b : ℝ) := unitInterval_le_iff.mp hab
    have hval : (b : ℝ) * (c : ℝ) = (a : ℝ) := congrArg Subtype.val hbc
    apply Subtype.ext
    split_ifs with hb
    · rw [if_pos hb] at hc
      have hc' : (c : ℝ) ≤ 0 := unitInterval_le_iff.mp hc
      show (c : ℝ) = (0 : ℝ)
      exact le_antisymm hc' c.2.1
    · have hbne : (b : ℝ) ≠ 0 := hb
      have hdiv : (a : ℝ) / (b : ℝ) = (c : ℝ) := by
        rw [← hval]; field_simp
      show (c : ℝ) = min ((a : ℝ) / (b : ℝ)) 1
      rw [hdiv]
      exact (min_eq_left c.2.2).symm
  le_div_self := by
    intro a
    refine unitInterval_le_iff.mpr ?_
    split_ifs with ha
    · show (a : ℝ) ≤ (0 : ℝ)
      exact le_of_eq ha
    · show (a : ℝ) ≤ min ((a : ℝ) / (a : ℝ)) 1
      rw [div_self ha, min_self]
      exact a.2.2
  div_div_self := by
    intro a
    split_ifs with ha h2 h3
    · rfl
    · exact absurd rfl h2
    · -- `a ≠ 0` makes `a/a = 1`, so the second condition cannot hold
      have h1 : min ((a : ℝ) / (a : ℝ)) 1 = 1 := by rw [div_self ha, min_self]
      have hone : (1 : ℝ) = 0 := by rw [← h1]; exact h3
      exact absurd hone one_ne_zero
    · have h1 : min ((a : ℝ) / (a : ℝ)) 1 = 1 := by rw [div_self ha, min_self]
      apply Subtype.ext
      show min (min ((a : ℝ) / (a : ℝ)) 1 / min ((a : ℝ) / (a : ℝ)) 1) 1
        = min ((a : ℝ) / (a : ℝ)) 1
      rw [h1, div_self one_ne_zero, min_self]

/-- **195V.1** (eff.tex:3246, Examples): the two-element effect monoid `2`
is an effect divisoid (with `a/b = a`). -/
instance : EffectDivisoid Bool where
  div a _ := a
  div_le h := h
  mul_div := by
    rintro a b ⟨c, hc, rfl⟩
    show (a ⊔ c) ⊓ a = a
    exact inf_eq_right.mpr le_sup_left
  div_unique := by
    rintro a b c _ ⟨e, he, rfl⟩ hmul
    rw [← hmul]
    exact (inf_eq_right.mpr le_sup_left).symm
  le_div_self a := pcm_preorder_refl a
  div_div_self _ := rfl

/-- Helper: the algebraic order of a product effect algebra is
componentwise. -/
theorem prod_le_iff {M N : Type u} [EffectAlgebra M] [EffectAlgebra N]
    {p q : M × N} : p ≼ q ↔ p.1 ≼ q.1 ∧ p.2 ≼ q.2 := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c.1, hc.1, rfl⟩, ⟨c.2, hc.2, rfl⟩⟩
  · rintro ⟨⟨c₁, h₁, e₁⟩, ⟨c₂, h₂, e₂⟩⟩
    exact ⟨(c₁, c₂), ⟨h₁, h₂⟩, Prod.ext_iff.mpr ⟨e₁, e₂⟩⟩

/-- The product of two effect monoids, with componentwise multiplication
(needed for 195V.2). -/
instance prodEffectMonoid (M N : Type u) [EffectMonoid M] [EffectMonoid N] :
    EffectMonoid (M × N) :=
  { prodEffectAlgebra M N with
    mul := fun p q => (p.1 * q.1, p.2 * q.2)
    one_mul := fun a => by
      show ((1 : M) * a.1, (1 : N) * a.2) = a
      rw [EffectMonoid.one_mul, EffectMonoid.one_mul]
    mul_one := fun a => by
      show (a.1 * (1 : M), a.2 * (1 : N)) = a
      rw [EffectMonoid.mul_one, EffectMonoid.mul_one]
    mul_assoc := fun a b c => by
      show (a.1 * b.1 * c.1, a.2 * b.2 * c.2) = (a.1 * (b.1 * c.1), a.2 * (b.2 * c.2))
      rw [EffectMonoid.mul_assoc, EffectMonoid.mul_assoc]
    distrib := by
      intro a b c d hab hcd
      exact isSumOf_prod (l := [(a.1 * c.1, a.2 * c.2), (b.1 * c.1, b.2 * c.2),
          (a.1 * d.1, a.2 * d.2), (b.1 * d.1, b.2 * d.2)])
        (EffectMonoid.distrib hab.1 hcd.1) (EffectMonoid.distrib hab.2 hcd.2) }

/-- **195V.2** (eff.tex:3249, Examples): the product of two effect divisoids
is an effect divisoid, with componentwise division (in particular `[0,1]ⁿ`
is an effect divisoid). -/
instance prodEffectDivisoid (M N : Type u) [EffectMonoid M] [EffectMonoid N]
    [EffectDivisoid M] [EffectDivisoid N] : EffectDivisoid (M × N) where
  div p q := (div p.1 q.1, div p.2 q.2)
  div_le h :=
    prod_le_iff.mpr ⟨EffectDivisoid.div_le (prod_le_iff.mp h).1,
      EffectDivisoid.div_le (prod_le_iff.mp h).2⟩
  mul_div := fun {p q} h => by
    show (q.1 * div p.1 q.1, q.2 * div p.2 q.2) = p
    rw [EffectDivisoid.mul_div (prod_le_iff.mp h).1,
      EffectDivisoid.mul_div (prod_le_iff.mp h).2]
  div_unique := fun {p q r} hpq hr hmul => by
    show r = (div p.1 q.1, div p.2 q.2)
    rw [← EffectDivisoid.div_unique (prod_le_iff.mp hpq).1 (prod_le_iff.mp hr).1
        (congrArg Prod.fst hmul),
      ← EffectDivisoid.div_unique (prod_le_iff.mp hpq).2 (prod_le_iff.mp hr).2
        (congrArg Prod.snd hmul)]
  le_div_self p :=
    prod_le_iff.mpr ⟨EffectDivisoid.le_div_self p.1, EffectDivisoid.le_div_self p.2⟩
  div_div_self p := by
    show (div (div p.1 p.1) (div p.1 p.1), div (div p.2 p.2) (div p.2 p.2))
        = (div p.1 p.1, div p.2 p.2)
    rw [EffectDivisoid.div_div_self, EffectDivisoid.div_div_self]

/-! ### Helpers for the unit interval of `C(X, ℝ)` (195VI) -/

section ContinuousIcc

variable {X : Type u} [TopologicalSpace X]

/-- The order of `C(X, ℝ)` is the pointwise one (introduction). -/
theorem cont_le_of_forall {f g : C(X, ℝ)} (h : ∀ x, f x ≤ g x) : f ≤ g := h

/-- The order of `C(X, ℝ)` is the pointwise one (elimination). -/
theorem cont_apply_le {f g : C(X, ℝ)} (h : f ≤ g) (x : X) : f x ≤ g x := h x

/-- Membership in `[0,1]_{C(X)}`, pointwise. -/
theorem cIcc_mem {g : C(X, ℝ)} (h0 : ∀ x, 0 ≤ g x) (h1 : ∀ x, g x ≤ 1) :
    g ∈ Set.Icc (0 : C(X, ℝ)) 1 :=
  ⟨cont_le_of_forall h0, cont_le_of_forall h1⟩

/-- An element of `[0,1]_{C(X)}` is pointwise nonnegative. -/
theorem cIcc_nonneg (f : Set.Icc (0 : C(X, ℝ)) 1) (x : X) : 0 ≤ (f : C(X, ℝ)) x :=
  cont_apply_le f.2.1 x

/-- An element of `[0,1]_{C(X)}` is pointwise at most `1`. -/
theorem cIcc_le_one (f : Set.Icc (0 : C(X, ℝ)) 1) (x : X) : (f : C(X, ℝ)) x ≤ 1 :=
  cont_apply_le f.2.2 x

/-- Pointwise introduction of the orthogonality relation of `[0,1]_{C(X)}`. -/
theorem cIcc_perp_of {f g : Set.Icc (0 : C(X, ℝ)) 1}
    (h : ∀ x, (f : C(X, ℝ)) x + (g : C(X, ℝ)) x ≤ 1) : (f : C(X, ℝ)) + g ≤ 1 :=
  cont_le_of_forall h

/-- Pointwise elimination of the orthogonality relation of `[0,1]_{C(X)}`. -/
theorem cIcc_perp_apply {f g : Set.Icc (0 : C(X, ℝ)) 1}
    (h : (f : C(X, ℝ)) + g ≤ 1) (x : X) :
    (f : C(X, ℝ)) x + (g : C(X, ℝ)) x ≤ 1 := cont_apply_le h x

end ContinuousIcc

/-- The effect monoid on the unit interval `[0,1]_{C(X)}` of the continuous
real functions on a topological space `X` (needed for 195VI). -/
noncomputable def continuousUnitIntervalEffectMonoid (X : Type u)
    [TopologicalSpace X] : EffectMonoid (Set.Icc (0 : C(X, ℝ)) 1) where
  zero := ⟨0, cIcc_mem (fun _ => le_refl 0) (fun _ => zero_le_one)⟩
  one := ⟨1, cIcc_mem (fun _ => zero_le_one) (fun _ => le_refl 1)⟩
  Perp f g := (f : C(X, ℝ)) + g ≤ 1
  ovee f g h := ⟨(f : C(X, ℝ)) + g,
    cIcc_mem (fun x => add_nonneg (cIcc_nonneg f x) (cIcc_nonneg g x))
      (fun x => cIcc_perp_apply h x)⟩
  orth f := ⟨1 - (f : C(X, ℝ)),
    cIcc_mem (fun x => by
        have := cIcc_le_one f x
        show (0 : ℝ) ≤ 1 - (f : C(X, ℝ)) x
        linarith)
      (fun x => by
        have := cIcc_nonneg f x
        show (1 : ℝ) - (f : C(X, ℝ)) x ≤ 1
        linarith)⟩
  mul f g := ⟨(f : C(X, ℝ)) * g,
    cIcc_mem (fun x => mul_nonneg (cIcc_nonneg f x) (cIcc_nonneg g x))
      (fun x => by
        show (f : C(X, ℝ)) x * (g : C(X, ℝ)) x ≤ 1
        nlinarith [cIcc_nonneg f x, cIcc_le_one f x, cIcc_nonneg g x,
          cIcc_le_one g x])⟩
  perp_comm := fun {a b} h => cIcc_perp_of fun x => by
    have h1 : (a : C(X, ℝ)) x + (b : C(X, ℝ)) x ≤ 1 := cIcc_perp_apply h x
    show (b : C(X, ℝ)) x + (a : C(X, ℝ)) x ≤ 1
    linarith
  ovee_comm := fun _ => Subtype.ext (add_comm _ _)
  perp_of_ovee_perp := fun {a b c} hab h => cIcc_perp_of fun x => by
    have h1 : (a : C(X, ℝ)) x + (b : C(X, ℝ)) x + (c : C(X, ℝ)) x ≤ 1 :=
      cIcc_perp_apply h x
    have h2 := cIcc_nonneg a x
    show (b : C(X, ℝ)) x + (c : C(X, ℝ)) x ≤ 1
    linarith
  perp_ovee_of_ovee_perp := fun {a b c} hab h => cIcc_perp_of fun x => by
    have h1 : (a : C(X, ℝ)) x + (b : C(X, ℝ)) x + (c : C(X, ℝ)) x ≤ 1 :=
      cIcc_perp_apply h x
    show (a : C(X, ℝ)) x + ((b : C(X, ℝ)) x + (c : C(X, ℝ)) x) ≤ 1
    linarith
  ovee_assoc := fun {a b c} hab h => Subtype.ext (by
    show (a : C(X, ℝ)) + (b : C(X, ℝ)) + (c : C(X, ℝ))
        = (a : C(X, ℝ)) + ((b : C(X, ℝ)) + (c : C(X, ℝ)))
    ring)
  zero_perp := fun a => cIcc_perp_of fun x => by
    have := cIcc_le_one a x
    show (0 : ℝ) + (a : C(X, ℝ)) x ≤ 1
    linarith
  zero_ovee := fun a => Subtype.ext (by
    show (0 : C(X, ℝ)) + (a : C(X, ℝ)) = (a : C(X, ℝ))
    ring)
  perp_orth := fun a => cIcc_perp_of fun x => by
    show (a : C(X, ℝ)) x + (1 - (a : C(X, ℝ)) x) ≤ 1
    linarith
  ovee_orth := fun a => Subtype.ext (by
    show (a : C(X, ℝ)) + (1 - (a : C(X, ℝ))) = (1 : C(X, ℝ))
    ring)
  orth_unique := fun {a b} h h1 => Subtype.ext (by
    have hv : (a : C(X, ℝ)) + (b : C(X, ℝ)) = (1 : C(X, ℝ)) :=
      congrArg Subtype.val h1
    show (b : C(X, ℝ)) = 1 - (a : C(X, ℝ))
    exact eq_sub_of_add_eq' hv)
  eq_zero_of_perp_one := fun {a} h => Subtype.ext (by
    have h1 : ∀ x, (a : C(X, ℝ)) x + 1 ≤ 1 := fun x => cIcc_perp_apply h x
    ext x
    have h2 := cIcc_nonneg a x
    have h3 := h1 x
    show (a : C(X, ℝ)) x = 0
    linarith)
  one_mul := fun a => Subtype.ext (by
    show (1 : C(X, ℝ)) * (a : C(X, ℝ)) = (a : C(X, ℝ))
    ring)
  mul_one := fun a => Subtype.ext (by
    show (a : C(X, ℝ)) * (1 : C(X, ℝ)) = (a : C(X, ℝ))
    ring)
  mul_assoc := fun a b c => Subtype.ext (by
    show (a : C(X, ℝ)) * (b : C(X, ℝ)) * (c : C(X, ℝ))
        = (a : C(X, ℝ)) * ((b : C(X, ℝ)) * (c : C(X, ℝ)))
    ring)
  distrib := by
    intro a b c d hab hcd
    refine @isSumOf_four _ ?inst _ _ _ _ _ ?_ ?_ ?_ ?_
    · refine cIcc_perp_of fun x => ?_
      show (a : C(X, ℝ)) x * (c : C(X, ℝ)) x + (b : C(X, ℝ)) x * (c : C(X, ℝ)) x ≤ 1
      nlinarith [cIcc_perp_apply hab x, cIcc_nonneg a x, cIcc_nonneg b x,
        cIcc_nonneg c x, cIcc_le_one c x]
    · refine cIcc_perp_of fun x => ?_
      show (a : C(X, ℝ)) x * (d : C(X, ℝ)) x + (b : C(X, ℝ)) x * (d : C(X, ℝ)) x ≤ 1
      nlinarith [cIcc_perp_apply hab x, cIcc_nonneg a x, cIcc_nonneg b x,
        cIcc_nonneg d x, cIcc_le_one d x]
    · refine cIcc_perp_of fun x => ?_
      show (a : C(X, ℝ)) x * (c : C(X, ℝ)) x + (b : C(X, ℝ)) x * (c : C(X, ℝ)) x
          + ((a : C(X, ℝ)) x * (d : C(X, ℝ)) x + (b : C(X, ℝ)) x * (d : C(X, ℝ)) x)
          ≤ 1
      nlinarith [cIcc_perp_apply hab x, cIcc_perp_apply hcd x, cIcc_nonneg a x,
        cIcc_nonneg b x, cIcc_nonneg c x, cIcc_nonneg d x]
    · refine Subtype.ext ?_
      show (a : C(X, ℝ)) * (c : C(X, ℝ)) + (b : C(X, ℝ)) * (c : C(X, ℝ))
          + ((a : C(X, ℝ)) * (d : C(X, ℝ)) + (b : C(X, ℝ)) * (d : C(X, ℝ)))
          = ((a : C(X, ℝ)) + (b : C(X, ℝ))) * ((c : C(X, ℝ)) + (d : C(X, ℝ)))
      ring

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
      div (ovee a b hab) c = ovee (div a c) (div b c) h' := by
  -- Write `s = a ⋁ b`.  The key step is that `a/s ⊥ b/s` with
  -- `a/s ⋁ b/s = s/s`: a complement `w` of `a/s` below `s/s` satisfies
  -- `s ⊙ w = b`, hence *is* `b/s` by uniqueness of the division.
  set s := ovee a b hab with hs
  have has : a ≼ s := ⟨b, hab, hs.symm⟩
  have hbs : b ≼ s := ⟨a, PCM.perp_comm hab, by
    rw [← PCM.ovee_comm hab]⟩
  have hss : s * div s s = s := EffectDivisoid.mul_div (pcm_preorder_refl s)
  obtain ⟨w, hw, hwe⟩ := EffectDivisoid.div_le has
  obtain ⟨h₂, e₂⟩ := emon_mul_ovee s hw
  rw [hwe, hss] at e₂
  have hsu : s * div a s = a := EffectDivisoid.mul_div has
  have hpa : Perp a (s * w) := by rw [← hsu]; exact h₂
  have e₂' : ovee a (s * w) hpa = ovee a b hab :=
    ((PCM.ovee_congr hsu rfl h₂ hpa).symm.trans e₂.symm).trans hs
  have e₂'' : ovee (s * w) a (PCM.perp_comm hpa)
      = ovee b a (PCM.perp_comm hab) := by
    rw [← PCM.ovee_comm hpa, ← PCM.ovee_comm hab]
    exact e₂'
  have hswb : s * w = b :=
    eabasics_cancellation (PCM.perp_comm hpa) (PCM.perp_comm hab) e₂''
  have hwle : w ≼ div s s := ⟨div a s, PCM.perp_comm hw, by
    rw [← PCM.ovee_comm hw]; exact hwe⟩
  have hwv : w = div b s := EffectDivisoid.div_unique hbs hwle hswb
  have hw' : Perp (div a s) (div b s) := by rw [← hwv]; exact hw
  have hovee_uv : ovee (div a s) (div b s) hw' = div s s := by
    rw [← PCM.ovee_congr rfl hwv hw hw']
    exact hwe
  -- now divide by `c`, using `(b/c) ⊙ (a/b) = a/c` three times
  have hEu : div s c * div a s = div a c := exc_divisoid_basics_2 has hc
  have hEv : div s c * div b s = div b c := exc_divisoid_basics_2 hbs hc
  have hEs : div s c * div s s = div s c :=
    exc_divisoid_basics_2 (pcm_preorder_refl s) hc
  obtain ⟨h₃, e₃⟩ := emon_mul_ovee (div s c) hw'
  rw [hovee_uv, hEs] at e₃
  have h' : Perp (div a c) (div b c) := by rw [← hEu, ← hEv]; exact h₃
  refine ⟨h', ?_⟩
  rw [e₃]
  exact PCM.ovee_congr hEu hEv h₃ h'

/-! ## `AConv_M` is an effectus for an effect divisoid `M` (parsec 196) -/

/-- **196II** (`aconvm-is-effectus`, eff.tex:3381, Theorem): if `M` is an
effect divisoid, then `AConv_M` is an effectus (in total form). -/
theorem aconvm_is_effectus (M : Type u) [EffectMonoid M] [EffectDivisoid M] :
    Nonempty (EffectusTotalStructure (AConvMCat.{u, v} M)) := sorry

end Theses.B.Eff
