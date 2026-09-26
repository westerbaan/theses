/-
Papers/REC/Scalars.lean

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707 (2021): REC 34 and REC 35 discharged.

`Papers/REC/Effectus.lean` records REC 34 (`thm:effect-monoids`: a
directed-complete effect monoid is `≅ B ⊕ C(X,[0,1])`) as the `Prop`
`EffectMonoidDCClassification`, which REC 35, 93–97 and the corrected REC 99
take as the hypothesis `h34`.  It is OAP 69 (`mainthmdirectedcomplete`), now
proved in `Papers/OAP/Main.lean` (`Papers.OAP.oap69`); this file bridges the two
formalisations (OAP writes the sum as `[0,1]_{C(X)} ⊕ B`, uses its own
`DirectedComplete` class and unit interval effect monoid, and states the
isomorphism as a morphism with an inverse) and proves
`EffectMonoidDCClassification` outright (`rec34_holds`).  Later files pass
`rec34_holds` for `h34`.
-/
import Papers.REC.Effectus
import Papers.OAP.Main

set_option warn.classDefReducibility false

open Theses.B.Eff

namespace Papers.REC

universe u v

/-- REC's directed completeness gives OAP's (the order of OAP's scoped
instance `eaPartialOrder` is `≼`). -/
theorem oapDirectedComplete_of {M : Type u} [EffectAlgebra M] (h : DirectedCompleteEA M) :
    Papers.OAP.DirectedComplete M := by
  letI := Papers.OAP.eaPartialOrder M
  refine ⟨fun S hS => ?_⟩
  obtain ⟨s, hs1, hs2⟩ := h S (fun x hx y hy => hS.2 x hx y hy)
  exact ⟨s, hs1, hs2⟩

/-- **REC 34** (`thm:effect-monoids`, short.tex:761, Theorem) **holds**: it is
OAP 69 (`Papers.OAP.oap69`), with the summands swapped and OAP's unit interval
effect monoid `[0,1]_{C(X)}` identified with the tree's (the same operations). -/
theorem rec34_holds : EffectMonoidDCClassification.{u} := by
  intro M _ hdc
  haveI := oapDirectedComplete_of hdc
  obtain ⟨X, tX, cX, hX, B, iB, hED, f, g, hgf, hfg⟩ := Papers.OAP.oap69 (M := M)
  refine ⟨B, iB, X, tX, cX, hX, hED, ⟨?_⟩⟩
  letI : EffectMonoid (Set.Icc (0 : C(X, ℝ)) 1 × B) := Papers.OAP.cxbEM X B
  letI : EffectMonoid B := booleanEffectMonoid B
  letI : EffectMonoid (Set.Icc (0 : C(X, ℝ)) 1) := continuousUnitIntervalEffectMonoid X
  let hom : EffectMonoidHom M (B × Set.Icc (0 : C(X, ℝ)) 1) :=
    { toFun := fun a => ((f.toFun a).2, (f.toFun a).1)
      perp_map := fun {a b} h => ⟨(f.perp_map h).2, (f.perp_map h).1⟩
      ovee_map := fun {a b} h => by
        have e := f.ovee_map h
        exact Prod.ext (congrArg Prod.snd e) (congrArg Prod.fst e)
      map_one := by
        have e := f.map_one
        exact Prod.ext (congrArg Prod.snd e) (congrArg Prod.fst e)
      map_mul := fun a b => by
        have e := f.map_mul a b
        exact Prod.ext (congrArg Prod.snd e) (congrArg Prod.fst e) }
  let inv : EffectMonoidHom (B × Set.Icc (0 : C(X, ℝ)) 1) M :=
    { toFun := fun u => g.toFun (u.2, u.1)
      perp_map := fun {u v} h => g.perp_map (show Perp (u.2, u.1) (v.2, v.1) from ⟨h.2, h.1⟩)
      ovee_map := fun {u v} h => g.ovee_map (show Perp (u.2, u.1) (v.2, v.1) from ⟨h.2, h.1⟩)
      map_one := g.map_one
      map_mul := fun u v => g.map_mul (u.2, u.1) (v.2, v.1) }
  exact
    { hom := hom
      inv := inv
      inv_hom := fun a => hgf a
      hom_inv := fun u => by
        show ((f.toFun (g.toFun (u.2, u.1))).2, (f.toFun (g.toFun (u.2, u.1))).1) = u
        rw [hfg] }

/-- **REC 35** (`corscalars`, short.tex:768, Corollary), unconditionally: the
scalars of a directed-complete effectus are `≅ B ⊕ C(X,[0,1])`. -/
theorem rec35_scalars_holds {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Limits.HasFiniteCoproducts C] [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C]
    [EffectusPartialForm C] (hdc : DirectedCompleteEffectus C) :
    ∃ (B : Type v) (_ : CompleteBooleanAlgebra B) (X : Type v) (_ : TopologicalSpace X),
      CompactSpace X ∧ T2Space X ∧ ExtremallyDisconnected X ∧
        Nonempty (@EMIso (Scal C) (B × Set.Icc (0 : C(X, ℝ)) 1) _
          (@prodEffectMonoid _ _ (booleanEffectMonoid B) (continuousUnitIntervalEffectMonoid X))) :=
  rec35_scalars rec34_holds hdc

end Papers.REC
