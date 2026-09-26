/-
Papers/SIG/Discharge.lean

The two results SIG cites from OAP, which `Papers/SIG/Classification.lean`
carries as the hypothesis `Prop`s `EffectMonoidEmbeddingTheorem` (SIG 41) and
`NoZeroDivisorsTheorem` (SIG 43), discharged by the OAP main theorems
(`Papers/OAP/Main.lean`): SIG 41 from `Papers.OAP.oap68` (OAP 68), SIG 43
from `Papers.OAP.oap71_iso` (OAP 71).  Then the SIG theorems that took them
as hypotheses, unconditionally: SIG 42 (`scalars_commutative_unconditional`)
and SIG 44 (`admitsNormalisation_iff_scalars_unconditional`).

Translations (SIG's notions against OAP's):
* SIG's `OmegaComplete` (sequences with `a n ≼ a (n+1)`, suprema `IsSupOf`
  for `≼`) gives OAP's class `OmegaComplete` (monotone sequences, `IsLUB` for
  OAP's `eaPartialOrder`, whose `≤` is `≼`): `sig_omegaComplete_toOAP`.
* OAP 68's clause "every countable subset of `B` has a supremum" gives SIG's
  `BooleanOmegaComplete` (the range of a sequence is countable).
* OAP's `BasicallyDisconnected` (`closure {x | f x ≠ 0}`) is the tree's
  (`closure (Function.support f)`): the same set, by `Iff.rfl`.
* OAP's `cxbEM X B` (OAP Basic's `unitIntervalEffectMonoid C(X, ℝ)` and
  `prodEffectMonoid`) and SIG's `cxbEffectMonoid X B` (the tree's
  `continuousUnitIntervalEffectMonoid X` and `prodEffectMonoid`) are two
  effect monoid structures on the same type with the same `⊥`, `⊕`, `1` and
  product; the identity is an isomorphism between them (`cxbIdHom`,
  `cxbIdHom_isIso`), composed onto OAP 68's embedding by
  `EMEmbedding.compIso`.
-/
import Papers.OAP.Main
import Papers.SIG.Classification
import Papers.SIG.EffectModules
import Papers.SIG.WeightModules

set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits Theses.B.Eff
open scoped Papers.OAP unitInterval

namespace Papers.SIG

universe u v

/-! ## Translations -/

/-- SIG's ω-completeness (SIG 17) is OAP's (OAP 13). -/
theorem sig_omegaComplete_toOAP {E : Type u} [EffectAlgebra E] (h : OmegaComplete E) :
    Papers.OAP.OmegaComplete E := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨s, hs1, hs2⟩ := h f (fun n => hf (Nat.le_succ n))
  exact ⟨s, fun t ht => hs1 t ht, fun c hc => hs2 c hc⟩

/-- The identity of `[0,1]_{C(X)} ⊕ B`, from OAP's structure `cxbEM X B` to
SIG's `cxbEffectMonoid X B`. -/
noncomputable def cxbIdHom (X : Type u) [TopologicalSpace X] (B : Type u) [BooleanAlgebra B] :
    @EffectMonoidHom (Set.Icc (0 : C(X, ℝ)) 1 × B) (Set.Icc (0 : C(X, ℝ)) 1 × B)
      (Papers.OAP.cxbEM X B) (cxbEffectMonoid X B) :=
  @EffectMonoidHom.mk _ _ (Papers.OAP.cxbEM X B) (cxbEffectMonoid X B)
    (@EAHom.mk _ _ (Papers.OAP.cxbEM X B).toEffectAlgebra (cxbEffectMonoid X B).toEffectAlgebra
      (@PCMHom.mk _ _ (Papers.OAP.cxbEM X B).toPCM (cxbEffectMonoid X B).toPCM id
        (fun h => h) (fun _ => rfl)) rfl)
    (fun _ _ => rfl)

/-- The identity of `[0,1]_{C(X)} ⊕ B`, from SIG's structure to OAP's. -/
noncomputable def cxbIdHom' (X : Type u) [TopologicalSpace X] (B : Type u) [BooleanAlgebra B] :
    @EffectMonoidHom (Set.Icc (0 : C(X, ℝ)) 1 × B) (Set.Icc (0 : C(X, ℝ)) 1 × B)
      (cxbEffectMonoid X B) (Papers.OAP.cxbEM X B) :=
  @EffectMonoidHom.mk _ _ (cxbEffectMonoid X B) (Papers.OAP.cxbEM X B)
    (@EAHom.mk _ _ (cxbEffectMonoid X B).toEffectAlgebra (Papers.OAP.cxbEM X B).toEffectAlgebra
      (@PCMHom.mk _ _ (cxbEffectMonoid X B).toPCM (Papers.OAP.cxbEM X B).toPCM id
        (fun h => h) (fun _ => rfl)) rfl)
    (fun _ _ => rfl)

theorem cxbIdHom_isIso (X : Type u) [TopologicalSpace X] (B : Type u) [BooleanAlgebra B] :
    @Papers.OAP.EMIsIso _ _ (Papers.OAP.cxbEM X B) (cxbEffectMonoid X B) (cxbIdHom X B) :=
  ⟨cxbIdHom' X B, fun _ => rfl, fun _ => rfl⟩

/-! ## SIG 41 and SIG 43, discharged -/

/-- **SIG 41** (`thm:effect-monoid-char`, main.tex:1159, Theorem, cited as
[OAP, Theorem 54]), proved: every ω-complete effect monoid embeds into
`[0,1]_{C(X)} ⊕ B` with `X` basically disconnected compact Hausdorff and `B`
an ω-complete Boolean algebra.  From **OAP 68** (`Papers.OAP.oap68`,
`thm:omega-complete-classification`) through the translations above. -/
theorem effectMonoidEmbeddingTheorem : EffectMonoidEmbeddingTheorem.{u} := by
  intro M _ hM
  have := sig_omegaComplete_toOAP hM
  obtain ⟨X, tX, cX, hX, B, bB, hbd, hsup, ⟨e⟩⟩ := Papers.OAP.oap68 (M := M)
  let e' := @Papers.OAP.EMEmbedding.compIso M _ _ _ (Papers.OAP.cxbEM X B)
    (cxbEffectMonoid X B) e (cxbIdHom X B) (cxbIdHom_isIso X B)
  let _ := cxbEffectMonoid X B
  refine ⟨X, tX, cX, hX, B, bB, fun f => hbd f, fun a _ => hsup _ (Set.countable_range a),
    e'.toEffectMonoidHom, fun a b h => e'.reflect h⟩

/-- **SIG 43** (`thm:no-zero-divisors`, main.tex:1186, Theorem, cited as
[OAP, Theorem 71]), proved: an ω-complete effect monoid without nontrivial
zero divisors is isomorphic to `{0}`, `{0,1}` or `[0,1]`.  From **OAP 71**
(`Papers.OAP.oap71_iso`, universe `v := 0`); OAP's `EMIsIso` unfolds to
SIG's `EMIso`. -/
theorem noZeroDivisorsTheorem : NoZeroDivisorsTheorem.{u} := by
  intro M _ hM hZ
  have := sig_omegaComplete_toOAP hM
  rcases Papers.OAP.oap71_iso.{u, 0} (M := M) hZ with ⟨f, g, h1, h2⟩ | ⟨f, g, h1, h2⟩ |
    ⟨f, g, h1, h2⟩
  · exact Or.inl ⟨f, g, h1, h2⟩
  · exact Or.inr (Or.inl ⟨f, g, h1, h2⟩)
  · exact Or.inr (Or.inr ⟨f, g, h1, h2⟩)

/-! ## The SIG theorems that took them as hypotheses -/

/-- **SIG 42** (main.tex:1172, Corollary), unconditionally: the scalars of a
σ-effectus are commutative.  `scalars_commutative` with its hypothesis SIG 41
discharged by **OAP 68** (`effectMonoidEmbeddingTheorem`). -/
theorem scalars_commutative_unconditional {C : Type u} [Category.{v} C]
    [HasCountableCoproducts C] [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C] :
    EffectMonoid.Commutative (Scal C) :=
  scalars_commutative effectMonoidEmbeddingTheorem

/-- **SIG 44** (main.tex:1196, Theorem), unconditionally: a σ-effectus admits
normalization iff its effect monoid of scalars is isomorphic to `{0}`,
`{0,1}` or `[0,1]`.  `admitsNormalisation_iff_scalars` with its hypothesis
SIG 43 discharged by **OAP 71** (`noZeroDivisorsTheorem`). -/
theorem admitsNormalisation_iff_scalars_unconditional {C : Type u} [Category.{v} C]
    [HasCountableCoproducts C] [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C] :
    AdmitsNormalisation C ↔
      EMIso (Scal C) PUnit.{1} ∨ EMIso (Scal C) Bool ∨ EMIso (Scal C) unitInterval :=
  admitsNormalisation_iff_scalars noZeroDivisorsTheorem

end Papers.SIG
