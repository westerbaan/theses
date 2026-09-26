/-
Papers/SEA/Discharge.lean

The hypothesis `SEA35` of `Papers/SEA/Basic.lean` (SEA 35, cited from OAP 57
with OAP 69) discharged by the corner form of **OAP 69**
(`Papers.OAP.oap69_corner`, `Papers/OAP/Main.lean`), and the declarations
that took it restated without it: `dcem_structure` (the form of OAP 69),
SEA 36 (spectral theorem), `dcem_sqrt` and SEA 37 (unique square roots).  The
second hypothesis `OAP47` those declarations take is `oap47_holds`
(`Papers/SEA/Boolean.lean`).

Translations (SEA's notions against OAP's):
* SEA's `DirectedComplete` (`EDirected`, `EIsSup`, for `≼`) gives OAP's class
  `DirectedComplete` (`IsDirectedSet`, `IsLUB` for OAP's `eaPartialOrder`,
  whose `≤` is `≼`): `sea_directedComplete_toOAP`.
* OAP's corner `leftCorner p = {p·a}` with `cornerEffectMonoid p hp` against
  SEA's `Downset p = {a // a ≼ p}` with `cornerEM hp`: the identity on
  underlying elements is an effect monoid isomorphism (`downsetCornerIso`;
  `leftCorner p = [0,p]` is OAP's `leftCorner_eq_Iic`).
* OAP's `IsConvex` (its own `ConvexAction`) is, by OAP 49 (`oap49_iff`), an
  effect module over `[0,1]`, which is SEA's `ConvexAction`; convexity is
  carried across the corner isomorphism by `isConvex_of_emIso`.
* OAP's `EMIsIso f` (a morphism with an inverse morphism) gives SEA's
  bundled `EMIso` (`nonempty_emIso_of_OAP`).
* OAP's `[0,1]_{C(X)}` (Basic's `unitIntervalEffectMonoid C(X, ℝ)`) and SEA's
  `CXI X` (`intervalEffectMonoid`) are two structures on the same type with
  the same operations; the identity is an isomorphism (`cxiIso`).
-/
import Papers.OAP.Main
import Papers.SEA.Basic
import Papers.SEA.Boolean

namespace Papers.SEA

open Theses.B.Eff
open scoped Papers.OAP unitInterval

universe u v

/-! ## Translations -/

/-- SEA's directed completeness (SEA 11) is OAP's (OAP 13). -/
theorem sea_directedComplete_toOAP {E : Type u} [EffectAlgebra E] (h : DirectedComplete E) :
    Papers.OAP.DirectedComplete E := by
  refine ⟨fun S hS => ?_⟩
  obtain ⟨x, hx1, hx2⟩ := h S ⟨hS.1, fun a ha b hb => hS.2 a ha b hb⟩
  exact ⟨x, fun s hs => hx1 s hs, fun y hy => hx2 y hy⟩

/-- An OAP isomorphism of effect monoids (a morphism with an inverse
morphism, OAP 8) gives SEA's bundled `EMIso`. -/
theorem nonempty_emIso_of_OAP {M : Type u} {N : Type v} [EffectMonoid M] [EffectMonoid N]
    (f : EffectMonoidHom M N) (hf : Papers.OAP.EMIsIso f) : Nonempty (EMIso M N) := by
  obtain ⟨g, hgf, hfg⟩ := hf
  exact ⟨{
    toFun := f.toFun
    invFun := g.toFun
    left_inv := hgf
    right_inv := hfg
    map_one := f.map_one
    perp_iff := fun a b => ⟨fun h => by have := g.perp_map h; rwa [hgf, hgf] at this,
      fun h => f.perp_map h⟩
    map_ovee := fun _ _ h _ => f.ovee_map h
    map_mul := f.map_mul }⟩

/-- SEA's corner `[0,p]` (`cornerEM`, SEA 34) and OAP's corner `pM`
(`cornerEffectMonoid`, OAP 12) of an idempotent `p` are isomorphic by the
identity on underlying elements. -/
noncomputable def downsetCornerIso {M : Type u} [EffectMonoid M] {p : M} (hp : p * p = p) :
    @EMIso (Downset p) (Papers.OAP.leftCorner p) (cornerEM hp)
      (Papers.OAP.cornerEffectMonoid p hp) :=
  let _ := cornerEM hp
  let _ := Papers.OAP.cornerEffectMonoid p hp
  { toFun := fun a => ⟨a.1, Papers.OAP.mem_leftCorner_of_le hp a.2⟩
    invFun := fun x => ⟨x.1, Papers.OAP.le_of_mem_leftCorner hp x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_one := rfl
    perp_iff := fun a b => ⟨fun h => ⟨h, by
        have h' : Perp a.1 b.1 := h
        have h2 := Papers.OAP.oap23 hp (show a.1 ≤ p from a.2) (show b.1 ≤ p from b.2) h'
        rw [Papers.OAP.oplus_eq h'] at h2
        exact h2⟩, fun h => h.1⟩
    map_ovee := fun _ _ h _ => Subtype.ext (Papers.OAP.oplus_eq h.1).symm
    map_mul := fun _ _ => rfl }

/-- The identity of `[0,1]_{C(X)}`, from OAP's `unitIntervalEffectMonoid` to
SEA's `CXI X`. -/
noncomputable def cxiIso (X : Type u) [TopologicalSpace X] :
    @EMIso (Set.Icc (0 : C(X, ℝ)) 1) (CXI X) (Papers.OAP.unitIntervalEffectMonoid C(X, ℝ)) _ :=
  @EMIso.mk _ _ (Papers.OAP.unitIntervalEffectMonoid C(X, ℝ)) _
    (@EAIso.mk _ _ (Papers.OAP.unitIntervalEffectMonoid C(X, ℝ)).toEffectAlgebra _
      (Equiv.refl _) rfl (fun _ _ => Iff.rfl) (fun _ _ _ _ => rfl))
    (fun _ _ => rfl)

/-- Convexity (SEA 8: an effect module over `[0,1]`) is carried back along an
isomorphism: `λ·a := e⁻¹(λ·e a)`. -/
theorem isConvex_of_emIso {E : Type u} {F : Type v} [EffectMonoid E] [EffectMonoid F]
    (f : EMIso E F) (h : Nonempty (EffectModule I F)) : IsConvex E := by
  obtain ⟨m⟩ := h
  let g := f.symm
  have hfg : ∀ x, f.toFun (g.toFun x) = x := f.apply_symm
  have hgf : ∀ a, g.toFun (f.toFun a) = a := f.symm_apply
  refine ⟨{
    smul := fun l a => g.toFun (l • f.toFun a)
    mul_smul := ?_
    smul_perp := ?_
    perp_smul := ?_
    one_smul := ?_ }⟩
  · intro l k a
    show g.toFun ((l * k) • f.toFun a) = g.toFun (l • f.toFun (g.toFun (k • f.toFun a)))
    rw [hfg, EffectModule.mul_smul]
  · intro l a b hab
    have hF : Perp (f.toFun a) (f.toFun b) := (f.perp_iff a b).2 hab
    obtain ⟨h1, e1⟩ := EffectModule.smul_perp l hF
    have hE : Perp (g.toFun (l • f.toFun a)) (g.toFun (l • f.toFun b)) := (g.perp_iff _ _).2 h1
    refine ⟨hE, ?_⟩
    show ovee (g.toFun (l • f.toFun a)) (g.toFun (l • f.toFun b)) hE =
      g.toFun (l • f.toFun (ovee a b hab))
    rw [← g.map_ovee _ _ h1 hE, e1, f.map_ovee a b hab hF]
  · intro l k hlk a
    obtain ⟨h1, e1⟩ := EffectModule.perp_smul hlk (f.toFun a)
    have hE : Perp (g.toFun (l • f.toFun a)) (g.toFun (k • f.toFun a)) := (g.perp_iff _ _).2 h1
    refine ⟨hE, ?_⟩
    show ovee (g.toFun (l • f.toFun a)) (g.toFun (k • f.toFun a)) hE =
      g.toFun (ovee l k hlk • f.toFun a)
    rw [← g.map_ovee _ _ h1 hE, e1]
  · intro a
    show g.toFun ((1 : I) • f.toFun a) = a
    rw [EffectModule.one_smul, hgf]

/-! ## SEA 35, discharged -/

/-- **SEA 35** (`thm:first`, second.tex:907, Theorem, cited from OAP 57 and
69), proved: in a directed-complete effect monoid `M` there is an idempotent
`p` with `pM` convex and every element below `p⊥` idempotent, and
`pM ≅ [0,1]_{C(X)}` for an extremally disconnected compact Hausdorff `X`.
From **OAP 69** in its corner form (`Papers.OAP.oap69_corner`, OAP 57 with
OAP 66) through the translations above. -/
theorem sea35 : SEA35.{u} := by
  intro M _ hM
  have := sea_directedComplete_toOAP hM
  obtain ⟨p, hp, hconv, hB, X, tX, cX, hX, hED, f, hf⟩ := Papers.OAP.oap69_corner (M := M)
  let _ := cornerEM hp
  let _i := Papers.OAP.cornerEffectMonoid p hp
  let e := downsetCornerIso hp
  obtain ⟨φ⟩ := @nonempty_emIso_of_OAP _ _ _i (Papers.OAP.unitIntervalEffectMonoid C(X, ℝ)) f hf
  refine ⟨p, hp, ?_, fun a ha => hB a ha, X, tX, cX, hX, hED, ⟨e.trans (φ.trans (cxiIso X))⟩⟩
  exact isConvex_of_emIso e (Papers.OAP.oap49_iff.1 hconv)

/-! ## The SEA declarations that took `SEA35`, unconditionally -/

/-- `dcem_structure` (SEA 35 with SEA 34 and OAP 47; the form of **OAP 69**),
unconditionally: every directed-complete effect monoid is `[0,1]_{C(X)} ⊕ B`
for an extremally disconnected compact Hausdorff `X` and a complete Boolean
algebra `B`.  `SEA35` discharged by **OAP 69** (`sea35`), `OAP47` by
`oap47_holds`. -/
theorem dcem_structure_unconditional (M : Type u) [EffectMonoid M] (hM : DirectedComplete M) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X),
      ExtremallyDisconnected X ∧ ∃ (B : Type u) (_ : CompleteBooleanAlgebra B),
        Nonempty (@EMIso M (CXI X × B) _ (@prodEM _ _ _ (booleanEffectMonoid B))) :=
  dcem_structure sea35 oap47_holds M hM

/-- **SEA 36** (`seaspectral`, second.tex:917, Corollary; spectral theorem for
normal SEAs), unconditionally: `{a}'' ≅ [0,1]_{C(X)} ⊕ B` with `X`
extremally disconnected compact Hausdorff and `B` a complete Boolean algebra.
`sea36_spectral` with `SEA35` discharged by **OAP 69** (`sea35`) and `OAP47`
by `oap47_holds`. -/
theorem sea36_spectral_unconditional {E : Type u} [EffectAlgebra E] [NormalSEA E] (a : E) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X),
      ExtremallyDisconnected X ∧ ∃ (B : Type u) (_ : CompleteBooleanAlgebra B),
        Nonempty (@EMIso (bicommutantSub ({a} : Set E)).carrier (CXI X × B)
          (bicommEM {a} (singleton_commuting a)) (@prodEM _ _ _ (booleanEffectMonoid B))) :=
  sea36_spectral sea35 oap47_holds a

/-- `dcem_sqrt`, unconditionally: in a directed-complete effect monoid every
element has a unique square root.  `SEA35` discharged by **OAP 69**
(`sea35`), `OAP47` by `oap47_holds`. -/
theorem dcem_sqrt_unconditional (M : Type u) [EffectMonoid M] (hM : DirectedComplete M) :
    (∀ x : M, ∃ y : M, y * y = x) ∧ (∀ y z : M, y * y = z * z → y = z) :=
  dcem_sqrt sea35 oap47_holds M hM

/-- **SEA 37** (second.tex:933, Corollary), unconditionally: every element `a`
of a normal SEA has a unique square root, `∃! b, b ⊙ b = a`.  `sea37_sqrt`
with `SEA35` discharged by **OAP 69** (`sea35`) and `OAP47` by
`oap47_holds`. -/
theorem sea37_sqrt_unconditional {E : Type u} [EffectAlgebra E] [NormalSEA E] (a : E) :
    ∃! b : E, b ⊙ b = a :=
  sea37_sqrt sea35 oap47_holds a

end Papers.SEA
