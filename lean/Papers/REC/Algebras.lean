/-
Papers/REC/Algebras.lean

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707 (2021): §2.3 (orthoalgebras, convexity and
order unit spaces), §2.4 (Jordan operator algebras) and §2.5 (sequential
products) — points REC 37–61 of `../papers/REC-points.csv`.

Design:
* This file does not import `Papers/REC/Effectus.lean` (a new file cannot import
  another new file in the session that creates it: `scripts/lean1.sh` writes no
  olean).  Where a notion of `Effectus.lean` is needed — directed completeness
  of an effect algebra (REC 30) in the definition of a *normal* SEA — it is
  spelled out inline, with a note; nothing of `Effectus.lean` is redefined
  under the same name.
* A **convex effect algebra** (REC 39) is defined as printed; it is the same
  thing as thesis B's effect module over the effect monoid `[0,1]` (179II), and
  `ConvexEA.toEffectModule` / `ConvexEA.ofEffectModule` are the bridge.
* An **order unit space** (REC 41) is thesis B's `OrderUnitSpace` (an ordered
  vector space with a distinguished order unit, *not* assumed Archimedean)
  together with the two conditions the paper adds: the order-unit seminorm is a
  norm, and the positive cone is closed for it (`IsOUS`).
* JB-, JBW- and JW-algebras (REC 44, 48, 50) and purely exceptional algebras
  (REC 51) are defined; the theorems of Hanche-Olsen–Størmer and Shultz quoted
  in §2.4 (REC 52, 55) and the example REC 54 need the Albert algebra
  `M₃(𝕆)_sa` (Mathlib has no octonions) and are left to `Monoidal.lean`, where
  §6 uses them as named black-box hypotheses (`PLAN.md` §1).
-/
import Theses.B.Eff.ExtensiveExamples
import Theses.B.Eff.OrderUnit
import Theses.B.Eff.Comparisons

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

open CategoryTheory
open CategoryTheory.Limits hiding HasImages
open Theses.B.Eff
open scoped unitInterval

namespace Papers.REC

universe u v w

/-! ## §2.3 Orthoalgebras, convexity and order unit spaces -/

section Orthoalgebras

/-- **REC 37** (`def:orthoalgebra`, short.tex:787, Definition): an effect algebra
is an **orthoalgebra** when `0` is its only self-summable element: `a ⊥ a`
implies `a = 0`.  (`OA`, the full subcategory of `EA` on the orthoalgebras, is
built in `Decomposition.lean`, where the predicate functor into it lives.) -/
def IsOrthoalgebra (E : Type u) [EffectAlgebra E] : Prop :=
  ∀ a : E, Perp a a → a = 0

/-- **REC 37** (short.tex:795, the sentence after the definition): orthomodular
lattices, and in particular Boolean algebras, are orthoalgebras (with the effect
algebra structure of thesis B 175II.4). -/
theorem orthomodular_isOrthoalgebra (L : Type u) [OrthomodularLattice L] :
    @IsOrthoalgebra L (orthomodularEffectAlgebra L) := by
  intro a h
  have h' : a ≤ aᶜ := h
  have : a ⊓ aᶜ = a := inf_eq_left.2 h'
  rw [← this, Ortholattice.inf_compl]
  rfl

/-- Helper: an effect monoid homomorphism maps `0` to `0`. -/
theorem alg_emonHom_map_zero {M : Type u} {N : Type v} [EffectMonoid M] [EffectMonoid N]
    (f : EffectMonoidHom M N) : f.toFun 0 = 0 := by
  have h := f.perp_map (PCM.zero_perp (0 : M))
  have e := f.ovee_map (PCM.zero_perp (0 : M))
  rw [PCM.zero_ovee] at e
  have h0 : Perp (f.toFun 0) 0 := PCM.perp_zero _
  have e' : ovee (f.toFun 0) (f.toFun 0) h = ovee (f.toFun 0) 0 h0 := by
    rw [PCM.ovee_zero]; exact e.symm
  exact eabasics_cancellation (PCM.perp_comm h) (PCM.perp_comm h0)
    ((PCM.ovee_comm h).symm.trans (e'.trans (PCM.ovee_comm h0)))

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- **REC 38** (short.tex:797, Proposition): in an effectus separated by states
with `Pred(I) ≅ {0,1}` every predicate space is an orthoalgebra.  (Cited from
SIG, which proves a σ-version; the proof here is the argument the paper prints
for REC 93: if `p ⊥ p` then `p ∘ ω ⊥ p ∘ ω` in `{0,1}` for every state `ω`, so
`p ∘ ω = 0`, and state separation gives `p = 0`.) -/
theorem rec38 (hsep : SeparatingStates C) (h2 : ScalarsAreTwo C) (A : C) :
    IsOrthoalgebra (Pred A) := by
  obtain ⟨φ, ψ, hψφ, -⟩ := h2
  intro p hp
  refine hsep p 0 fun ω => ?_
  rw [FinPAC.comp_zero]
  obtain ⟨h', -⟩ := FinPAC.ovee_comp hp ω.1
  -- `ω ≫ p ⊥ ω ≫ p` among the scalars, so its image in `{0,1}` is `0`
  have hb : φ.toFun (ω.1 ≫ p) ⊓ φ.toFun (ω.1 ≫ p) = ⊥ := φ.perp_map h'
  rw [inf_idem] at hb
  have := hψφ (ω.1 ≫ p)
  rw [hb] at this
  rw [← this]
  exact alg_emonHom_map_zero ψ

end Orthoalgebras

section Convex

/-- **REC 39** (`def:convex`, short.tex:801, Definition): an effect algebra `E`
is **convex** when there is an action `· : [0,1] × E → E` of the real unit
interval with `λ·(μ·x) = (λμ)·x`; `λ·x ⊥ μ·x` and `λ·x ⊻ μ·x = (λ+μ)·x` when
`λ + μ ≤ 1`; `1·x = x`; and `λ·(x ⊻ y) = λ·x ⊻ λ·y`.  (The categories `EA_c`,
`DCEA_c` of the point are built in `Decomposition.lean`.) -/
class ConvexEA (E : Type u) [EffectAlgebra E] extends SMul I E where
  smul_smul : ∀ (l m : I) (x : E), l • m • x = (l * m) • x
  add_smul : ∀ (l m : I) (x : E) (h : (l : ℝ) + m ≤ 1),
    ∃ h' : Perp (l • x) (m • x),
      ovee (l • x) (m • x) h' = (⟨(l : ℝ) + m, add_nonneg l.2.1 m.2.1, h⟩ : I) • x
  one_smul : ∀ x : E, (1 : I) • x = x
  smul_ovee : ∀ (l : I) {x y : E} (h : Perp x y),
    ∃ h' : Perp (l • x) (l • y), l • ovee x y h = ovee (l • x) (l • y) h'

variable {E : Type u} [EffectAlgebra E]

/-- **REC 39**: a convex effect algebra is an effect module over the effect
monoid `[0,1]` in thesis B's sense (179II). -/
def ConvexEA.toEffectModule [c : ConvexEA E] : EffectModule I E where
  smul := c.smul
  mul_smul l m a := (ConvexEA.smul_smul l m a).symm
  smul_perp l _ _ h := by
    obtain ⟨h', e⟩ := ConvexEA.smul_ovee l h
    exact ⟨h', e.symm⟩
  perp_smul {l m} h a := by
    obtain ⟨h', e⟩ := ConvexEA.add_smul l m a h
    exact ⟨h', e⟩
  one_smul := ConvexEA.one_smul

/-- **REC 39**: conversely, an effect module over `[0,1]` (thesis B 179II) is a
convex effect algebra. -/
def ConvexEA.ofEffectModule [m : EffectModule I E] : ConvexEA E where
  smul := m.smul
  smul_smul l m a := (EffectModule.mul_smul l m a).symm
  add_smul l m x h := EffectModule.perp_smul (M := I) (show Perp l m from h) x
  one_smul := EffectModule.one_smul
  smul_ovee l _ _ h := by
    obtain ⟨h', e⟩ := EffectModule.smul_perp l h
    exact ⟨h', e.symm⟩

/-- **REC 40** (short.tex:823, Example), first sentence: for an ordered real
vector space `V` and `u ≥ 0`, the interval `[0,u]_V` is a convex effect algebra
with the obvious action.  Thin: thesis B's `orderIntervalEffectModule`
(179III.2) through the bridge of REC 39. -/
noncomputable def rec40_orderInterval (V : Type u) [AddCommGroup V] [Module ℝ V]
    [PartialOrder V] [IsOrderedAddMonoid V] [PosSMulMono ℝ V] [SMulPosMono ℝ V]
    (u : V) (hu : 0 ≤ u) :
    @ConvexEA (Set.Icc (0 : V) u) (orderIntervalEffectAlgebra V u hu) :=
  @ConvexEA.ofEffectModule _ (orderIntervalEffectAlgebra V u hu)
    (orderIntervalEffectModule V u hu)

/-- **REC 40** (short.tex:823, Example), second sentence (Gudder's
representation): every convex effect algebra `E` is isomorphic, as a convex
effect algebra, to `[0,u]_V` for an ordered vector space `V` with order unit
`u`.  Thin: thesis B's `effectModule_unitInterval_representation` (179III.2),
through the bridge of REC 39.  (The equivalence of categories of the point's
last sentence is not formalised here.) -/
theorem rec40_representation [c : ConvexEA E] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℝ V) (_ : PartialOrder V)
      (_ : IsOrderedAddMonoid V) (_ : PosSMulMono ℝ V) (_ : SMulPosMono ℝ V)
      (u : V) (_ : IsOrderUnit u) (_ : 0 ≤ u) (f : E → Set.Icc (0 : V) u),
        Function.Bijective f ∧
        (∀ (a b : E) (h : Perp a b), (f (ovee a b h) : V) = (f a : V) + (f b : V)) ∧
        (∀ (r : I) (a : E), (f (r • a) : V) = (r : ℝ) • (f a : V)) :=
  @effectModule_unitInterval_representation E _ c.toEffectModule

end Convex

section OUS

variable (V : Type u) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]

/-- **REC 41** (short.tex:837, Definition): the **order-unit seminorm**
`‖v‖ := inf {λ ∈ ℝ ; -λ1 ≤ v ≤ λ1}`. -/
noncomputable def ousNorm (v : V) : ℝ :=
  sInf {l : ℝ | -(l • ouUnit V) ≤ v ∧ v ≤ l • ouUnit V}

/-- **REC 41** (short.tex:837, Definition): an **order unit space** is an ordered
vector space with a designated order unit (thesis B's `OrderUnitSpace`) whose
seminorm `‖·‖` is a norm and whose positive cone is closed in the
`‖·‖`-topology. -/
class IsOUS : Prop where
  norm_eq_zero : ∀ v : V, ousNorm V v = 0 → v = 0
  cone_closed : ∀ v : V, (∀ ε : ℝ, 0 < ε → ∃ w : V, 0 ≤ w ∧ ousNorm V (v - w) < ε) → 0 ≤ v

/-- **REC 41** (short.tex:837, Definition): a **Banach** order unit space is
complete in its norm. -/
def IsBanachOUS : Prop :=
  ∀ s : ℕ → V, (∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, ousNorm V (s m - s n) < ε) →
    ∃ v : V, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, ousNorm V (s n - v) < ε

/-- **REC 41** (short.tex:837, Definition): an order unit space is **directed
complete** when its unit interval `[0,1]_V` is: every directed subset of
`[0,1]_V` has a least upper bound in `[0,1]_V`.  (`DCOUS`, with the positive
linear contractions, is built in `Decomposition.lean`.) -/
def IsDirectedCompleteOUS : Prop :=
  ∀ D : Set V, D ⊆ Set.Icc 0 (ouUnit V) → DirectedOn (· ≤ ·) D →
    ∃ s ∈ Set.Icc 0 (ouUnit V), (∀ d ∈ D, d ≤ s) ∧
      ∀ t ∈ Set.Icc 0 (ouUnit V), (∀ d ∈ D, d ≤ t) → s ≤ t

end OUS

section RealEffectus

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- **REC 43** (short.tex:848, Proposition): in an effectus with
`Pred(I) ≅ [0,1]` every predicate space is a convex effect algebra, with the
action `λ · p := λ ∘ p` for `λ ∈ Pred(I)` (here: the scalar `ψ(λ)` corresponding
to `λ ∈ [0,1]` under the isomorphism).  Proved from thesis B's effect-module
structure `predEffectModule` (190II.4), transported along the isomorphism
(cited from SIG, whose Example 27 is this observation). -/
noncomputable def rec43 (h : IsRealEffectus C) (A : C) : ConvexEA (Pred A) :=
  let ψ := h.choose_spec.choose
  { smul := fun l p => p ≫ ψ.toFun l
    smul_smul := fun l m x => by
      show (x ≫ ψ.toFun m) ≫ ψ.toFun l = x ≫ ψ.toFun (l * m)
      rw [ψ.map_mul, Category.assoc]
      rfl
    add_smul := fun l m x hlm => by
      have hperp : Perp l m := hlm
      obtain ⟨h1, e1⟩ := FinPAC.ovee_comp (ψ.perp_map hperp) x
      refine ⟨h1, ?_⟩
      show ovee (x ≫ ψ.toFun l) (x ≫ ψ.toFun m) h1 = x ≫ ψ.toFun (ovee l m hperp)
      rw [ψ.ovee_map hperp, e1]
    one_smul := fun x => by
      show x ≫ ψ.toFun 1 = x
      rw [ψ.map_one]
      exact (predEffectModule A).one_smul x
    smul_ovee := fun l _ _ hxy => by
      obtain ⟨h', e⟩ := FinPAC.comp_ovee hxy (ψ.toFun l)
      exact ⟨h', e⟩ }

/-- **REC 43**: the convex action of `rec43` is composition with the scalar
`ψ(λ) ∈ Pred(I)`. -/
theorem rec43_smul (h : IsRealEffectus C) {A : C} (l : I) (p : Pred A) :
    (rec43 h A).smul l p = p ≫ h.choose_spec.choose.toFun l :=
  rfl

end RealEffectus

/-! ## §2.4 Jordan operator algebras -/

section Jordan

variable (A : Type u) [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A]

/-- **REC 44** (`def:JB-algebra`, short.tex:861, Definition): a **JB-algebra**
`(A, *, 1, ≤)` is a Banach order unit space with a binary operation `*` that is
commutative, has `1` as unit, satisfies the Jordan identity
`(a*b)*(a*a) = a*(b*(a*a))`, and has `0 ≤ a*a ≤ 1` whenever `-1 ≤ a ≤ 1`.

⚠ The point asks only for a "binary operation"; a JB-algebra (Hanche-Olsen–
Størmer 3.1.6, which the point cites) is a *Jordan algebra*, so the product is
bilinear.  Bilinearity is added here (`add_mul`, `smul_mul`; the other side
follows by commutativity) and recorded in the audit. -/
class JBAlgebra [Mul A] : Prop extends IsOUS A where
  banach : IsBanachOUS A
  mul_comm : ∀ a b : A, a * b = b * a
  mul_one : ∀ a : A, a * ouUnit A = a
  one_mul : ∀ a : A, ouUnit A * a = a
  jordan : ∀ a b : A, (a * b) * (a * a) = a * (b * (a * a))
  sq_mem : ∀ a : A, -ouUnit A ≤ a → a ≤ ouUnit A → 0 ≤ a * a ∧ a * a ≤ ouUnit A
  add_mul : ∀ a b c : A, (a + b) * c = a * c + b * c
  smul_mul : ∀ (r : ℝ) (a b : A), (r • a) * b = r • (a * b)

/-- **REC 47** (`def:order-separating`, short.tex:897, Definition): a **state**
of an order unit space `A` is a positive unital linear map `ω : A → ℝ`. -/
structure OUSState where
  toLin : A →ₗ[ℝ] ℝ
  nonneg : ∀ a : A, 0 ≤ a → 0 ≤ toLin a
  unital : toLin (ouUnit A) = 1

variable {A}

/-- **REC 47** (`def:order-separating`, short.tex:897, Definition): a map between
partially ordered sets is **normal** when it preserves suprema of directed
sets: `f (⋁ S) = ⋁ f(S)`. -/
def IsNormalMap {P Q : Type*} [PartialOrder P] [PartialOrder Q] (f : P → Q) : Prop :=
  ∀ (S : Set P) (s : P), S.Nonempty → DirectedOn (· ≤ ·) S → IsLUB S s → IsLUB (f '' S) (f s)

variable (A)

/-- **REC 47** (`def:order-separating`, short.tex:897, Definition): `A` has a
**separating set of normal states** when any two distinct elements are told
apart by a normal state. -/
def HasSeparatingNormalStates : Prop :=
  ∀ a b : A, a ≠ b → ∃ ω : OUSState A, IsNormalMap ω.toLin ∧ ω.toLin a ≠ ω.toLin b

/-- **REC 48** (`def:JBW-algebra`, short.tex:901, Definition): a JB-algebra is a
**JBW-algebra** when it is directed complete (REC 41) and has a separating set
of normal states.  (The categories `JBW_pc`, `JBW_npc` are built in
`Reconstruction.lean`, where the predicate functor lands in them.) -/
class JBWAlgebra [Mul A] : Prop extends JBAlgebra A where
  directedComplete : IsDirectedCompleteOUS A
  separating : HasSeparatingNormalStates A

/-- **REC 50/51** (short.tex:913, 923): a real-linear map `φ : A → 𝔄` into a
C*-algebra is a **Jordan homomorphism into `𝔄_sa`** when it takes self-adjoint
values and `φ(a * b) = ½(φ(a)φ(b) + φ(b)φ(a))` (the special Jordan product of
REC 45). -/
def IsJordanHomInto [Mul A] (𝔄 : Type w) [CStarAlgebra 𝔄] (φ : A →ₗ[ℝ] 𝔄) : Prop :=
  (∀ a : A, IsSelfAdjoint (φ a)) ∧
    ∀ a b : A, φ (a * b) = (2⁻¹ : ℝ) • (φ a * φ b + φ b * φ a)

/-- **REC 50** (short.tex:913, Definition): a JBW-algebra is a **JW-algebra**
when it is Jordan-isomorphic to an ultraweakly closed Jordan subalgebra of the
self-adjoint part of a von Neumann algebra.

⚠ Rendered as: there is a von Neumann algebra `𝔄` (thesis A's Kadison
definition, `Theses.VonNeumannAlgebra`) and an *injective normal* Jordan
homomorphism `A → 𝔄_sa`.  For a JBW-algebra the two are equivalent (the image
of a normal injective Jordan homomorphism of a JBW-algebra is ultraweakly
closed, and conversely the inclusion of an ultraweakly closed Jordan subalgebra
is normal; Hanche-Olsen–Størmer §4.4–4.5); the tree has no ultraweak topology
on an abstract von Neumann algebra, and the injective-normal form is the one
REC 130 uses.  Recorded in the audit as a deviation. -/
def IsJWAlgebra [Mul A] : Prop :=
  ∃ (𝔄 : Type u) (_ : CStarAlgebra 𝔄) (_ : PartialOrder 𝔄) (_ : StarOrderedRing 𝔄)
    (_ : Theses.VonNeumannAlgebra 𝔄) (φ : A →ₗ[ℝ] 𝔄),
      IsJordanHomInto A 𝔄 φ ∧ Function.Injective φ ∧ IsNormalMap φ

/-- **REC 51** (short.tex:923, Definition): a JB-algebra is **purely
exceptional** when every Jordan homomorphism `A → 𝔄_sa` into a C*-algebra is
zero.  (The quantification is over C*-algebras in a fixed universe `w`.) -/
def IsPurelyExceptional [Mul A] : Prop :=
  ∀ (𝔄 : Type w) [CStarAlgebra 𝔄] (φ : A →ₗ[ℝ] 𝔄), IsJordanHomInto A 𝔄 φ → φ = 0

end Jordan

/-- **REC 53** (short.tex:934, Definition): a Stonean space `X` (compact
Hausdorff, extremally disconnected) is **hyperstonean** when `C(X,ℝ)` is
separated by normal states: positive unital linear functionals preserving
suprema of directed sets. -/
def IsHyperstonean (X : Type u) [TopologicalSpace X] : Prop :=
  CompactSpace X ∧ T2Space X ∧ ExtremallyDisconnected X ∧
    ∀ f g : C(X, ℝ), f ≠ g → ∃ ω : C(X, ℝ) →ₗ[ℝ] ℝ,
      (∀ h : C(X, ℝ), 0 ≤ h → 0 ≤ ω h) ∧ ω 1 = 1 ∧ IsNormalMap ω ∧ ω f ≠ ω g

/-! ## §2.5 Sequential products -/

section SEA

variable (E : Type u) [EffectAlgebra E]

/-- **REC 56** (`defn:sea`, short.tex:977, Definition): a **sequential effect
algebra** is an effect algebra with a total binary operation `&` such that
(writing `a | b` for `a & b = b & a`)

* a) `a & (b ⊻ c) = a & b ⊻ a & c` whenever `b ⊥ c`;
* b) `1 & a = a`;
* c) `a & b = 0` implies `b & a = 0`;
* d) if `a | b` then `a | b^⊥` and `a & (b & c) = (a & b) & c` for all `c`;
* e) if `c | a` and `c | b` then `c | a & b`, and if moreover `a ⊥ b` then
  `c | a ⊻ b`.

(Thesis B's 225IV, the tree's `SequentialEffectAlgebra`, asks `a ⊥ b` for *both*
conclusions of e); `SEA.toTree` is the comparison.) -/
class SEA where
  seq : E → E → E
  seq_ovee : ∀ (a : E) {b c : E} (h : Perp b c),
    ∃ h' : Perp (seq a b) (seq a c), seq a (ovee b c h) = ovee (seq a b) (seq a c) h'
  one_seq : ∀ a : E, seq 1 a = a
  seq_eq_zero : ∀ a b : E, seq a b = 0 → seq b a = 0
  comm_orth : ∀ {a b : E}, seq a b = seq b a → seq a (orth b) = seq (orth b) a
  comm_assoc : ∀ {a b : E}, seq a b = seq b a → ∀ c, seq a (seq b c) = seq (seq a b) c
  comm_seq : ∀ {a b c : E}, seq c a = seq a c → seq c b = seq b c →
    seq c (seq a b) = seq (seq a b) c
  comm_ovee : ∀ {a b c : E} (h : Perp a b), seq c a = seq a c → seq c b = seq b c →
    seq c (ovee a b h) = seq (ovee a b h) c

variable {E}

/-- Commutation `a | b` in a SEA (REC 56). -/
def SEA.Commute [SEA E] (a b : E) : Prop := SEA.seq a b = SEA.seq b a

/-- **REC 56**: a SEA in the paper's sense is a SEA in thesis B's sense (225IV). -/
def SEA.toTree [s : SEA E] : SequentialEffectAlgebra E where
  seq := s.seq
  seq_add c _ _ h := by
    obtain ⟨h', e⟩ := s.seq_ovee c h
    exact ⟨h', e.symm⟩
  one_seq := s.one_seq
  seq_zero_comm := s.seq_eq_zero
  seq_comm_orth := s.comm_orth
  seq_comm_assoc := fun h c => (s.comm_assoc h c).symm
  seq_comm_compat := fun h ha hb => ⟨s.comm_seq ha hb, s.comm_ovee h ha hb⟩

variable (E)

/-- **REC 56** (`defn:sea`, short.tex:977, Definition): a SEA is **normal** when
`E` is directed complete (REC 30: every upwards-directed subset has a supremum
for the effect-algebra order; spelled out here, see the file header) and

* f) for directed `S`, `a & ⋁S = ⋁_{s ∈ S} a & s`, and `a | ⋁S` whenever
  `a | s` for all `s ∈ S`. -/
def IsNormalSEA [SEA E] : Prop :=
  (∀ D : Set E, (∀ x ∈ D, ∀ y ∈ D, ∃ z ∈ D, x ≼ z ∧ y ≼ z) →
    ∃ s, (∀ x ∈ D, x ≼ s) ∧ ∀ t, (∀ x ∈ D, x ≼ t) → s ≼ t) ∧
  ∀ (D : Set E) (s : E), (∀ x ∈ D, ∀ y ∈ D, ∃ z ∈ D, x ≼ z ∧ y ≼ z) →
    ((∀ x ∈ D, x ≼ s) ∧ ∀ t, (∀ x ∈ D, x ≼ t) → s ≼ t) →
    ∀ a : E,
      ((∀ x ∈ SEA.seq a '' D, x ≼ SEA.seq a s) ∧
        ∀ t, (∀ x ∈ SEA.seq a '' D, x ≼ t) → SEA.seq a s ≼ t) ∧
      ((∀ x ∈ D, SEA.Commute a x) → SEA.Commute a s)

variable {E}

/-- An element `p` of a SEA is **idempotent** when `p & p = p` (REC 57). -/
def SEA.IsIdempotent [SEA E] (p : E) : Prop := SEA.seq p p = p

/-- **REC 57** (`lem:normal-SEA-properties`, short.tex:1021, Lemma), *the
statement*: in a normal SEA `E`, for every `a`

* a) there is a smallest idempotent `⌈a⌉` above `a`;
* b) there is a largest idempotent `⌊a⌋` below `a`;
* c) if `b & a = a` then `b ≥ ⌈a⌉`.

Cited from SEA (its §4: SEA 49–50 for the floor, SEA 71 for c)); recorded as a
`Prop` to enter §5 as a hypothesis until `Papers/SEA` can be imported. -/
def NormalSEACeilFloor : Prop :=
  ∀ (E : Type u) [EffectAlgebra E] [SEA E], IsNormalSEA E → ∀ a : E,
    (∃ c : E, SEA.IsIdempotent c ∧ a ≼ c ∧ (∀ p, SEA.IsIdempotent p → a ≼ p → c ≼ p) ∧
      ∀ b : E, SEA.seq b a = a → c ≼ b) ∧
    ∃ f : E, SEA.IsIdempotent f ∧ f ≼ a ∧ ∀ p, SEA.IsIdempotent p → p ≼ a → p ≼ f

/-- **REC 59** (`def:SEA-compressible`, short.tex:1046, Definition): a **state**
of a convex SEA `E` is a map `ω : E → [0,1]` that is additive, preserves the
scalar multiplication and has `ω(1) = 1`. -/
structure ConvexState (E : Type u) [EffectAlgebra E] [ConvexEA E] where
  toFun : E → I
  map_ovee : ∀ {a b : E} (h : Perp a b), ((toFun (ovee a b h) : I) : ℝ) = toFun a + toFun b
  map_smul : ∀ (l : I) (a : E), toFun (l • a) = l * toFun a
  map_one : toFun 1 = 1

/-- **REC 59** (`def:SEA-compressible`, short.tex:1046, Definition): the
sequential product of a convex SEA is **compressible** when for every idempotent
`p` and state `ω`, `ω(p) = 1` implies `ω(p & a) = ω(a)` for all `a`. -/
def IsCompressible [ConvexEA E] [SEA E] : Prop :=
  ∀ p : E, SEA.IsIdempotent p → ∀ ω : ConvexState E, ω.toFun p = 1 →
    ∀ a : E, ω.toFun (SEA.seq p a) = ω.toFun a

/-- **REC 60** (`def:SEA-quadratic`, short.tex:1059, Definition): the sequential
product is **quadratic** when `q & (p & q) = (q & p)²` for all idempotents
`p, q` (where `x² := x & x`). -/
def IsQuadratic [SEA E] : Prop :=
  ∀ p q : E, SEA.IsIdempotent p → SEA.IsIdempotent q →
    SEA.seq q (SEA.seq p q) = SEA.seq (SEA.seq q p) (SEA.seq q p)

/-- **REC 61** (`thm:normalSEAisJB`, short.tex:1064, Theorem), *the statement*:
a convex normal SEA whose sequential product is compressible and quadratic is
order-isomorphic to the unit interval of a directed-complete JB-algebra.  This
is van de Wetering, *Sequential measurement characterises quantum theory* (2018),
Theorem 4 — outside the papers being formalised; recorded as a named `Prop`
(a black box).  The paper does **not** use it in its proofs: §5 re-runs its
argument with the effectus's own states (REC 117–121). -/
def WeteringSequentialJB : Prop :=
  ∀ (E : Type u) [EffectAlgebra E] [ConvexEA E] [SEA E], IsNormalSEA E →
    IsCompressible (E := E) → IsQuadratic (E := E) →
    ∃ (A : Type u) (_ : AddCommGroup A) (_ : Module ℝ A) (_ : PartialOrder A)
      (_ : OrderUnitSpace A) (_ : Mul A), JBAlgebra A ∧ IsDirectedCompleteOUS A ∧
      ∃ f : E → Set.Icc (0 : A) (ouUnit A), Function.Bijective f ∧
        ∀ a b : E, a ≼ b ↔ (f a : A) ≤ f b

end SEA

end Papers.REC
