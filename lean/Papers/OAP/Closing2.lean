/-
Papers/OAP/Closing2.lean

Cleanup pass (2026-09-26): OAP 66 without its waiting hypothesis.

* **OAP 66** (`thm:convexextremallydisconnected`): `oap66` in `OUS.lean`
  takes "M is a lattice" (OAP 37) as the hypothesis `oap37`, since
  `FloorCeiling.lean` was not importable there.  Here it is discharged by
  `isLUB_emSup` (`oap66_unconditional`), and the print's literal statement
  ("basically disconnected Hausdorff `X`", no "compact") is the corollary
  `oap66_as_printed`.
-/
import Papers.OAP.Main

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace Papers.OAP

open Theses.B.Eff
open scoped Papers.OAP unitInterval

universe u

section OAP66

attribute [local instance] unitIntervalEffectMonoid

variable {M : Type u} [EffectMonoid M] [EffectModule I M]

/-- **OAP 66** (`thm:convexextremallydisconnected`, first.tex:2489, Theorem),
unconditionally: a convex ω-complete effect monoid `M` is isomorphic (as an
effect monoid, compatibly with the convex structure) to `[0,1]_{C(X)}` for a
compact Hausdorff basically disconnected `X`, extremally disconnected when `M`
is directed complete.  `oap66` with its lattice hypothesis discharged by
OAP 37 (`isLUB_emSup`), as the printed proof does ("`M` is a lattice by
Theorem 37"). -/
theorem oap66_unconditional [OmegaComplete M] :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X)
      (f : EffectMonoidHom M (Set.Icc (0 : C(X, ℝ)) 1)), EMIsIso f ∧
      (∀ (l : I) (a : M), (f.toFun (l • a) : C(X, ℝ)) = (l : ℝ) • (f.toFun a : C(X, ℝ))) ∧
      BasicallyDisconnected X ∧ (DirectedComplete M → ExtremallyDisconnected X) :=
  oap66 fun a b => ⟨emSup a b, isLUB_emSup a b⟩

/-- **OAP 66** (`thm:convexextremallydisconnected`, first.tex:2489, Theorem),
as printed: a convex ω-complete effect monoid `M` is isomorphic to
`[0,1]_{C(X)}` for some basically disconnected Hausdorff space `X`; if `M` is
directed complete, `X` is extremally disconnected.  (The print omits
"compact"; `oap66_unconditional` also gives it.)  "Convex" is an
`EffectModule I M` (OAP 49). -/
theorem oap66_as_printed [OmegaComplete M] :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
      (f : EffectMonoidHom M (Set.Icc (0 : C(X, ℝ)) 1)), EMIsIso f ∧
      BasicallyDisconnected X ∧ (DirectedComplete M → ExtremallyDisconnected X) := by
  obtain ⟨X, tX, -, hX, f, hf, -, hbd, hed⟩ := oap66_unconditional (M := M)
  exact ⟨X, tX, hX, f, hf, hbd, hed⟩

end OAP66

end Papers.OAP
