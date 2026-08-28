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

Two questions have been put to it, both recorded in `docs/DEAD-LIMBS.md`:

* `IsCommutingPair.symm` — **no reference at all** (§10f, resolved).
* the `Δ^{1/2}` package — `modularSqrt` has eleven references and every one is
  inside the package, while `modularConj` has four and one of them leaves it.
  That is §13.7's cone finding, confirmed declaration by declaration, and it
  corrects §12b's stated reason for keeping `Tomita.lean`'s Part IV.

The `targets` list below is the second of those; edit it for the next question.

**Walk the constants once.**  The obvious loop puts the targets outermost and
re-runs `findDeclarationRanges?` over the whole environment for each one: eight
minutes per target, and still running after twenty-five for eight of them.
Testing every target on each constant instead brings it back to one walk.

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
  [`Theses.RvD.modularSqrt, `Theses.RvD.modularConj,
   `Theses.RvD.modularSqrt_hasCore, `Theses.RvD.orbit_mem_modularSqrt_domain,
   `Theses.RvD.mem_modularSqrt_domain, `Theses.RvD.exists_Ksub_repr,
   `Theses.RvD.modularConj_modularSqrt, `Theses.RvD.modularConj_modularSqrt_orbit]

private def mentions (e : Expr) (t : Name) : Bool :=
  (e.find? fun s => s.isConstOf t).isSome

elab "#uses_of" : command => do
  let env ← getEnv
  let names : Array Name := env.constants.fold (fun acc n _ => acc.push n) #[]
  -- Walk the constants ONCE and test every target on each.  The obvious loop
  -- (targets outermost) re-runs `findDeclarationRanges?` over the whole
  -- environment per target, which is eight minutes each and was still going
  -- after twenty-five for eight of them.
  let mut hits : Std.HashMap Name (Array Name) := {}
  for t in targets do
    hits := hits.insert t #[]
  for n in names.qsort Name.lt do
    let mod := match env.getModuleFor? n with | some m => m.toString | none => ""
    if !(mod.startsWith "Theses.A" || mod.startsWith "Theses.B") then continue
    if !(← findDeclarationRanges? n).isSome then continue
    let some ci := env.find? n | continue
    let v := ci.value? (allowOpaque := true) |>.getD default
    for t in targets do
      if n == t then continue
      if mentions ci.type t || mentions v t then
        hits := hits.insert t ((hits.getD t #[]).push n)
  for t in targets do
    let h := hits.getD t #[]
    if h.isEmpty then
      logInfo s!"{t}: NO term-level reference in Theses/"
    else
      logInfo s!"{t}: {h.size} term-level references — {h.toList}"

#uses_of

end Theses.UsesOf
