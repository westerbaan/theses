/-
`scripts/BinderDump.lean` — emit the algebra typeclasses each theorem's *type*
actually assumes.

Writes `docs/binders.txt`, one line per hand-written theorem:

    Theses.A.Proc.Tensor|Theses.A.Proc.mi_bilinear_cp|CStarAlgebra

The question it answers is one that cannot be answered by reading the source:
which classes govern a declaration, once `variable`, `omit … in`,
`instance`-implied superclasses and the section structure have all been
applied.  A doc comment that says "between von Neumann algebras" over a
signature the elaborator resolved to `CStarAlgebra` is claiming the thesis's
statement and proving a stronger one, and the audit row above it is then
graded against the wrong statement.  113II was found that way; this dumps the
data to look for the rest.

Only the classes that distinguish a *setting* are reported, not every instance
in the type: the interesting axis is C*-algebra against von Neumann algebra,
and Hilbert module against self-dual Hilbert module.

Run from `lean/`:

    lake env lean scripts/BinderDump.lean

or, if another agent holds the `lake` lock:

    LP=".lake/build/lib/lean"; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
    env LEAN_PATH="$LP" lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 \
      scripts/BinderDump.lean

⚠ Both `-D` flags matter: `lakefile.toml` sets them and a bare `lean` does not
read it.

Beware: this walks the whole environment, so it takes a few minutes.
-/
import Theses
import Lean.Elab.Command

open Lean Elab Command

namespace Theses.BinderDump

/-- The classes worth reporting.  Anything else in a type is plumbing. -/
private def watched : List Name :=
  [``CStarAlgebra, ``VonNeumannAlgebra, ``CStarModule, ``NormedAddCommGroup,
   ``InnerProductSpace, ``CompleteSpace]

/-- Which of `watched` occur in `e`. -/
private def classesIn (e : Expr) : List Name :=
  watched.filter fun c => (e.find? fun s => s.isConstOf c).isSome

elab "#dump_binders" : command => do
  let env ← getEnv
  let names : Array Name := env.constants.fold (fun acc n _ => acc.push n) #[]
  let mut out : Array String := #[]
  for n in names.qsort Name.lt do
    let mod := match env.getModuleFor? n with | some m => m.toString | none => ""
    if mod.startsWith "Theses.A" || mod.startsWith "Theses.B" then
      if (← findDeclarationRanges? n).isSome then
        if let some ci := env.find? n then
          if ci matches .thmInfo _ then
            let cs := (classesIn ci.type).map Name.toString
            let short := (n.toString.splitOn "0.").getLast!
            out := out.push s!"{mod}|{short}|{String.intercalate "," cs}"
  IO.FS.writeFile "docs/binders.txt" (String.intercalate "\n" out.toList)
  logInfo s!"wrote {out.size} rows to docs/binders.txt"

#dump_binders

end Theses.BinderDump
