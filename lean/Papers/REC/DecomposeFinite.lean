/-
Papers/REC/DecomposeFinite.lean

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707 (2021), §4.4: a corrected form of REC 99.

REC 99 is false as printed (`rec99_false_as_printed` in
`Papers/REC/Decompose.lean`): finite tomography constrains nothing about the
scalars.  What the printed proof tries to show — that the Boolean part `B` and
the space `X` in `Pred(I) ≅ B ⊕ C(X,[0,1])` (REC 34/35) are finite — holds
exactly when the scalars have finitely many idempotents, and that is the
corrected statement proved here, in both directions.

This file does not import `Decompose.lean` (a new file cannot import another new
file in the session that creates it); it only needs `Effectus.lean`.
-/
import Papers.REC.Effectus

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

open CategoryTheory
open CategoryTheory.Limits hiding HasImages
open Theses.B.Eff

namespace Papers.REC

universe u v

/-! ## Isomorphisms of effect monoids -/

section EMIsoOps

variable {M N L K : Type v} [EffectMonoid M] [EffectMonoid N] [EffectMonoid L]
  [EffectMonoid K]

/-- The composite of effect monoid homomorphisms. -/
def EffectMonoidHom.comp' (g : EffectMonoidHom N L) (f : EffectMonoidHom M N) :
    EffectMonoidHom M L where
  toFun := g.toFun ∘ f.toFun
  perp_map h := g.perp_map (f.perp_map h)
  ovee_map h := by
    show g.toFun (f.toFun _) = _
    rw [f.ovee_map, g.ovee_map]
    rfl
  map_one := by show g.toFun (f.toFun 1) = 1; rw [f.map_one, g.map_one]
  map_mul a b := by show g.toFun (f.toFun (a * b)) = _; rw [f.map_mul, g.map_mul]; rfl

/-- The composite of isomorphisms of effect monoids. -/
def EMIso.trans (φ : EMIso M N) (ψ : EMIso N L) : EMIso M L where
  hom := EffectMonoidHom.comp' ψ.hom φ.hom
  inv := EffectMonoidHom.comp' φ.inv ψ.inv
  inv_hom a := by
    show φ.inv.toFun (ψ.inv.toFun (ψ.hom.toFun (φ.hom.toFun a))) = a
    rw [ψ.inv_hom, φ.inv_hom]
  hom_inv b := by
    show ψ.hom.toFun (φ.hom.toFun (φ.inv.toFun (ψ.inv.toFun b))) = b
    rw [φ.hom_inv, ψ.hom_inv]

/-- An isomorphism on the first factor of a direct sum. -/
def EffectMonoidHom.prodLeft (f : EffectMonoidHom M N) : EffectMonoidHom (M × K) (N × K) where
  toFun p := (f.toFun p.1, p.2)
  perp_map h := ⟨f.perp_map h.1, h.2⟩
  ovee_map h := Prod.ext (f.ovee_map h.1) rfl
  map_one := Prod.ext f.map_one rfl
  map_mul a b := Prod.ext (f.map_mul a.1 b.1) rfl

def EMIso.prodLeft (φ : EMIso M N) : EMIso (M × K) (N × K) where
  hom := EffectMonoidHom.prodLeft φ.hom
  inv := EffectMonoidHom.prodLeft φ.inv
  inv_hom a := Prod.ext (φ.inv_hom a.1) rfl
  hom_inv b := Prod.ext (φ.hom_inv b.1) rfl

end EMIsoOps

/-- An order isomorphism of Boolean algebras is a homomorphism of the effect
monoids of REC 16. -/
def boolOrderIsoHom {B B' : Type v} [BooleanAlgebra B] [BooleanAlgebra B'] (e : B ≃o B') :
    @EffectMonoidHom B B' (booleanEffectMonoid B) (booleanEffectMonoid B') :=
  letI := booleanEffectMonoid B
  letI := booleanEffectMonoid B'
  { toFun := e
    perp_map := fun {a b} h => by
      show e a ⊓ e b = ⊥
      have h' : a ⊓ b = ⊥ := h
      rw [← e.map_inf, h', e.map_bot]
    ovee_map := fun {a b} h => by
      show e (a ⊔ b) = e a ⊔ e b
      exact e.map_sup a b
    map_one := by show e ⊤ = ⊤; exact e.map_top
    map_mul := fun a b => by show e (a ⊓ b) = e a ⊓ e b; exact e.map_inf a b }

/-- An order isomorphism of Boolean algebras is an isomorphism of the effect
monoids of REC 16. -/
def boolOrderIsoEMIso {B B' : Type v} [BooleanAlgebra B] [BooleanAlgebra B'] (e : B ≃o B') :
    @EMIso B B' (booleanEffectMonoid B) (booleanEffectMonoid B') :=
  @EMIso.mk B B' (booleanEffectMonoid B) (booleanEffectMonoid B') (boolOrderIsoHom e)
    (boolOrderIsoHom e.symm) e.symm_apply_apply e.apply_symm_apply

/-! ## The corrected REC 99 -/

section Rec99

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- The indicator function of a clopen set, as an element of `[0,1]_{C(X)}`. -/
noncomputable def clopenIndicator {X : Type v} [TopologicalSpace X] (U : Set X)
    (hU : IsClopen U) : Set.Icc (0 : C(X, ℝ)) 1 :=
  ⟨⟨U.indicator 1, hU.continuous_indicator continuous_const⟩,
    cIcc_mem (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
      (fun x => Set.indicator_le_self' (fun _ _ => zero_le_one) x |>.trans (le_refl 1))⟩

/-- **REC 99**, corrected: a directed-complete effectus whose scalars have only
finitely many idempotents has `Pred(I) ≅ 𝒫(A) ⊕ [0,1]^Y` (as effect monoids) for
finite sets `A` and `Y` — `[0,1]^Y = C(Y,[0,1])` for the discrete finite space
`Y`, i.e. `[0,1]^n` with `n = |Y|`.  The printed proof's plan, with a hypothesis
that makes it work: in `Pred(I) ≅ B ⊕ C(X,[0,1])` (REC 35, from OAP 69 as the
hypothesis `h34`) the elements `(b, 0)` and `(0, 1_U)` for clopen `U` are
idempotent, so `B` is finite, hence `≅ 𝒫(atoms)`, and `X` has finitely many
clopens, hence (being totally separated) is finite and discrete.
`rec99_corrected_converse` shows the hypothesis is also necessary, so it is
the exact condition. -/
theorem rec99_corrected (h34 : EffectMonoidDCClassification.{v})
    (hdc : DirectedCompleteEffectus C) (hfin : Set.Finite {s : Scal C | s ≫ s = s}) :
    ∃ (A : Type v) (_ : Finite A) (Y : Type v) (_ : TopologicalSpace Y) (_ : Finite Y)
      (_ : DiscreteTopology Y),
      Nonempty (@EMIso (Scal C) (Set A × Set.Icc (0 : C(Y, ℝ)) 1) _
        (@prodEffectMonoid _ _ (booleanEffectMonoid (Set A))
          (continuousUnitIntervalEffectMonoid Y))) := by
  obtain ⟨B, iB, X, iX, -, hT2, hED, ⟨φ⟩⟩ := rec35_scalars h34 hdc
  letI : EffectMonoid B := booleanEffectMonoid B
  letI : EffectMonoid (Set.Icc (0 : C(X, ℝ)) 1) := continuousUnitIntervalEffectMonoid X
  haveI : Finite {s : Scal C // s ≫ s = s} := hfin.to_subtype
  let z : Set.Icc (0 : C(X, ℝ)) 1 := ⟨0, cIcc_mem (fun _ => le_refl 0) (fun _ => zero_le_one)⟩
  -- idempotents of `B ⊕ C(X,[0,1])` give idempotent scalars
  have hidem : ∀ u : B × Set.Icc (0 : C(X, ℝ)) 1, u * u = u →
      φ.inv.toFun u ≫ φ.inv.toFun u = φ.inv.toFun u := fun u hu => by
    show φ.inv.toFun u * φ.inv.toFun u = φ.inv.toFun u
    rw [← φ.inv.map_mul]
    exact congrArg φ.inv.toFun hu
  have hinj : Function.Injective φ.inv.toFun := fun a b h => by
    rw [← φ.hom_inv a, ← φ.hom_inv b, h]
  -- `B` is finite
  have hB : Finite B := by
    refine Finite.of_injective (β := {s : Scal C // s ≫ s = s})
      (fun b => ⟨φ.inv.toFun (b, z), hidem _ (Prod.ext (show b ⊓ b = b from inf_idem b)
        (Subtype.ext (show (0 : C(X, ℝ)) * 0 = 0 from mul_zero _)))⟩) ?_
    intro a b h
    exact congrArg Prod.fst (hinj (congrArg Subtype.val h))
  -- `X` has finitely many clopens
  have hclo : Finite {U : Set X // IsClopen U} := by
    refine Finite.of_injective (β := {s : Scal C // s ≫ s = s})
      (fun U => ⟨φ.inv.toFun (⊥, clopenIndicator U.1 U.2), hidem _ (Prod.ext
        (show (⊥ : B) ⊓ ⊥ = ⊥ from inf_idem _) (Subtype.ext (ContinuousMap.ext fun x => by
          change U.1.indicator (1 : X → ℝ) x * U.1.indicator (1 : X → ℝ) x =
            U.1.indicator (1 : X → ℝ) x
          by_cases hx : x ∈ U.1 <;> simp [hx])))⟩) ?_
    intro U V h
    have e := congrArg (fun u => ((u.2 : Set.Icc (0 : C(X, ℝ)) 1) : C(X, ℝ)))
      (hinj (congrArg Subtype.val h))
    apply Subtype.ext
    ext x
    have ex := congrArg (fun f : C(X, ℝ) => f x) e
    simp only at ex
    change U.1.indicator (1 : X → ℝ) x = V.1.indicator (1 : X → ℝ) x at ex
    by_cases hU : x ∈ U.1 <;> by_cases hV : x ∈ V.1 <;> simp_all
  -- hence `X` is finite (it is totally separated) and discrete
  have hX : Finite X := by
    refine Finite.of_injective (β := Set {U : Set X // IsClopen U})
      (fun x => {U | x ∈ U.1}) ?_
    intro x y hxy
    by_contra hne
    obtain ⟨U, hU, hxU, hyU⟩ := exists_isClopen_of_totally_separated hne
    have : (⟨U, hU⟩ : {U : Set X // IsClopen U}) ∈ {U : {U : Set X // IsClopen U} | x ∈ U.1} :=
      hxU
    have hxy' : {U : {U : Set X // IsClopen U} | x ∈ U.1} = {U | y ∈ U.1} := hxy
    rw [hxy'] at this
    exact hyU this
  haveI : DiscreteTopology X := Finite.instDiscreteTopology
  -- `B ≅ 𝒫(atoms B)`
  haveI : IsAtomic B := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  letI : CompleteAtomicBooleanAlgebra B := CompleteBooleanAlgebra.toCompleteAtomicBooleanAlgebra
  let ψ := @boolOrderIsoEMIso B (Set {a : B // IsAtom a}) _ _
    (CompleteAtomicBooleanAlgebra.toSetOfIsAtom (α := B))
  refine ⟨{a : B // IsAtom a}, inferInstance, X, iX, hX, inferInstance, ⟨?_⟩⟩
  letI := booleanEffectMonoid (Set {a : B // IsAtom a})
  exact φ.trans ψ.prodLeft

/-- **REC 99**, corrected, converse: if `Pred(I) ≅ 𝒫(A) ⊕ [0,1]^Y` with `A`, `Y`
finite, then `Pred(I)` has finitely many idempotents (an idempotent `(S, f)` has
`f` `{0,1}`-valued, so it is determined by `S` and `f⁻¹(1)`). -/
theorem rec99_corrected_converse (A Y : Type v) [Finite A] [Finite Y] [TopologicalSpace Y]
    (φ : @EMIso (Scal C) (Set A × Set.Icc (0 : C(Y, ℝ)) 1) _
      (@prodEffectMonoid _ _ (booleanEffectMonoid (Set A)) (continuousUnitIntervalEffectMonoid Y))) :
    Set.Finite {s : Scal C | s ≫ s = s} := by
  letI : EffectMonoid (Set A) := booleanEffectMonoid (Set A)
  letI : EffectMonoid (Set.Icc (0 : C(Y, ℝ)) 1) := continuousUnitIntervalEffectMonoid Y
  let g : {s : Scal C // s ≫ s = s} → Set A × Set Y :=
    fun s => ((φ.hom.toFun s.1).1, {y | ((φ.hom.toFun s.1).2 : C(Y, ℝ)) y = 1})
  have hidem : ∀ s : {s : Scal C // s ≫ s = s}, φ.hom.toFun s.1 * φ.hom.toFun s.1 =
      φ.hom.toFun s.1 := fun s =>
    (φ.hom.map_mul s.1 s.1).symm.trans (congrArg φ.hom.toFun s.2)
  have hval : ∀ (s : {s : Scal C // s ≫ s = s}) (y : Y),
      ((φ.hom.toFun s.1).2 : C(Y, ℝ)) y = 0 ∨ ((φ.hom.toFun s.1).2 : C(Y, ℝ)) y = 1 := by
    intro s y
    have e := congrArg (fun u : Set A × Set.Icc (0 : C(Y, ℝ)) 1 => ((u.2 : C(Y, ℝ)) y))
      (hidem s)
    change ((φ.hom.toFun s.1).2 : C(Y, ℝ)) y * ((φ.hom.toFun s.1).2 : C(Y, ℝ)) y =
      ((φ.hom.toFun s.1).2 : C(Y, ℝ)) y at e
    have : ((φ.hom.toFun s.1).2 : C(Y, ℝ)) y * (((φ.hom.toFun s.1).2 : C(Y, ℝ)) y - 1) = 0 := by
      linarith
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hg : Function.Injective g := by
    intro s t h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    apply Subtype.ext
    rw [← φ.inv_hom s.1, ← φ.inv_hom t.1]
    congr 1
    refine Prod.ext h1 (Subtype.ext (ContinuousMap.ext fun y => ?_))
    have hy := congrArg (fun S : Set Y => y ∈ S) h2
    simp only [g, Set.mem_setOf_eq, eq_iff_iff] at hy
    rcases hval s y with hs | hs <;> rcases hval t y with ht | ht
    · rw [hs, ht]
    · exact absurd (hy.2 ht) (by rw [hs]; norm_num)
    · exact absurd (hy.1 hs) (by rw [ht]; norm_num)
    · rw [hs, ht]
  haveI : Finite {s : Scal C // s ≫ s = s} := Finite.of_injective g hg
  haveI : Finite ↥{s : Scal C | s ≫ s = s} := this
  exact Set.toFinite _

end Rec99

end Papers.REC
