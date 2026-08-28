/-
`scripts/UsesOf.lean` — who references a given constant, at the term level.

The textual dead-limb scan cannot answer this for a declaration whose short
name collides with a Mathlib one: `IsCommutingPair.symm` is written `.symm` at
every call site, and grepping for `symm` finds Mathlib's on every second line.
`docs/DEAD-LIMBS.md` §10f left it "Unresolved; needs a term-level check".

This is that check, and it is deliberately tiny: name the constants in
`targets`, and it prints every hand-written declaration of the two theses whose
type or value mentions one of them.  Nothing is written to disk; the answer is
the log output.

Run from `lean/`:

    lake env lean scripts/UsesOf.lean

or, if another agent holds the `lake` lock:

    LP=".lake/build/lib/lean"; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
    env LEAN_PATH="$LP" lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 \
      scripts/UsesOf.lean

Beware: this walks the whole environment, so it takes a few minutes.
-/
import Theses
import Lean.Elab.Command

open Lean Elab Command

namespace Theses.UsesOf

/-- The constants to look for.  Edit this list. -/
private def targets : List Name :=
  [`Theses.RvD.IsCommutingPair.symm]

private def mentions (e : Expr) (t : Name) : Bool :=
  (e.find? fun s => s.isConstOf t).isSome

elab "#uses_of" : command => do
  let env ← getEnv
  let names : Array Name := env.constants.fold (fun acc n _ => acc.push n) #[]
  for t in targets do
    let mut hits : Array Name := #[]
    for n in names.qsort Name.lt do
      if n == t then continue
      let mod := match env.getModuleFor? n with | some m => m.toString | none => ""
      if mod.startsWith "Theses.A" || mod.startsWith "Theses.B" then
        if (← findDeclarationRanges? n).isSome then
          if let some ci := env.find? n then
            let v := ci.value? (allowOpaque := true) |>.getD default
            if mentions ci.type t || mentions v t then
              hits := hits.push n
    if hits.isEmpty then
      logInfo s!"{t}: NO term-level reference in Theses/"
    else
      logInfo s!"{t}: {hits.size} term-level references — {hits.toList}"

#uses_of

end Theses.UsesOf
