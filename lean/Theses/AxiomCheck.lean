/-
Theses/AxiomCheck.lean

A diagnostic command, `#sorry_leaks`, that reports every declaration in the
`Theses` namespace whose proof depends on `sorryAx`.  It distinguishes

* **direct** leaks — the declaration is itself `sorry` (`sorryAx` occurs in
  its own type or value); these are the honest, counted `sorry`s; and
* **indirect** leaks — the declaration looks proved but *uses* a `sorry`ed
  result, typically through a `Prop`-valued class instance or a
  `Classical.choice` of a `sorry`ed existence statement.  These are the
  dangerous ones: `grep -c sorry` does not see them.

For each indirect leak the offending direct `sorry`s it rests on are listed.

Reading the output: auto-generated declarations (`.rec`, `.casesOn`, `.mk`,
`.injEq`, `.noConfusion`, `.sizeOf_spec`, projections) of a structure whose
*type* mentions a `sorry`ed definition show up as indirect leaks. They are
benign noise; the interesting indirect leaks are the hand-written ones.

This file is deliberately **NOT** imported by `Theses.lean`, so it has no
effect on the normal build.  Run it with

    lake env lean Theses/AxiomCheck.lean

Beware: `#sorry_leaks` walks the whole environment, so it takes a while.
-/
import Theses
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

namespace Theses.AxiomCheck

/-- Does `e` mention `sorryAx` itself? -/
private def exprHasSorry (e : Expr) : Bool :=
  (e.find? fun s => s.isConstOf ``sorryAx).isSome

/-- The body of a declaration.  NOTE: `ConstantInfo.value?` returns `none` for
theorems (and opaques) unless `allowOpaque := true` — without it every
`theorem foo : P := sorry` is silently misclassified as an *indirect* leak. -/
private def bodyOf (ci : ConstantInfo) : Option Expr :=
  ci.value? (allowOpaque := true)

/-- Is the declaration *itself* a `sorry` (as opposed to merely depending on
one)? -/
private def isDirectSorry (ci : ConstantInfo) : Bool :=
  exprHasSorry ci.type ||
    (match bodyOf ci with | some v => exprHasSorry v | none => false)

/-- The constants directly used by a declaration (type and value). -/
private def usedConstants (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++
    (match bodyOf ci with | some v => v.getUsedConstants | none => #[])

/-- For a declaration `n`, the set of *directly* `sorry`ed declarations (drawn
from `directs`) that `n` transitively depends on.  Memoised; the search is
pruned by `collectAxioms`, which is `O(1)` for imported declarations. -/
private partial def sorryRoots (directs : NameSet) (n : Name) :
    StateT (NameMap NameSet) CommandElabM NameSet := do
  if let some r := (← get).find? n then
    return r
  -- provisional entry, so that a dependency cycle terminates
  modify (·.insert n {})
  let axs ← Lean.collectAxioms n
  unless axs.contains ``sorryAx do
    return {}
  let mut acc : NameSet := if directs.contains n then ({} : NameSet).insert n else {}
  if let some ci := (← getEnv).find? n then
    for d in usedConstants ci do
      if d != n then
        let r ← sorryRoots directs d
        for x in r.toList do
          acc := acc.insert x
  modify (·.insert n acc)
  return acc

/-- Is `n` hand-written, i.e. does it come from a `theorem`/`def`/… in some
source file?  Auto-generated declarations (`.rec`, `.casesOn`, `.injEq`, the
structure eliminators, …) have no declaration range; they are noise in the
indirect-leak report, since they inherit `sorryAx` from the *type* of the
structure they belong to. -/
private def isHandWritten (n : Name) : CommandElabM Bool :=
  return (← findDeclarationRanges? n).isSome

/--
`#sorry_leaks` lists every declaration under the `Theses` namespace whose
axioms include `sorryAx`, split into declarations that are themselves `sorry`
and declarations that merely depend on one (with the `sorry`s they rest on).

It **fails** (non-zero exit code) if any *hand-written* declaration is an
indirect leak: a `sorry` of one's own is expected and fine, but a declaration
that looks proved and silently rests on one is the bug class this tool exists
to catch.  Suitable for CI as `lake env lean Theses/AxiomCheck.lean`.
-/
elab "#sorry_leaks" : command => do
  let env ← getEnv
  let names : Array Name :=
    env.constants.fold
      (fun (acc : Array Name) (n : Name) _ =>
        if (`Theses).isPrefixOf n && !n.isInternalDetail then acc.push n else acc)
      #[]
  let names := names.qsort Name.lt
  let mut direct : Array Name := #[]
  let mut indirect : Array Name := #[]
  for n in names do
    let axs ← Lean.collectAxioms n
    if axs.contains ``sorryAx then
      if let some ci := env.find? n then
        if isDirectSorry ci then direct := direct.push n else indirect := indirect.push n
  let directSet : NameSet := direct.foldl (init := {}) fun s n => s.insert n
  let mut msg := m!"checked {names.size} declarations under `Theses`\n"
  msg := msg ++
    m!"{direct.size} are themselves `sorry`; {indirect.size} depend on a `sorry`\n"
  msg := msg ++ m!"\n=== declarations that ARE `sorry` ({direct.size}) ===\n"
  for n in direct do
    msg := msg ++ m!"  {n}\n"
  let mut handWritten : Array Name := #[]
  msg := msg ++
    m!"\n=== declarations that DEPEND on a `sorry` ({indirect.size}) ===\n"
  for n in indirect do
    let roots ← (sorryRoots directSet n).run' {}
    let rs := roots.toList
    let hw ← isHandWritten n
    if hw then handWritten := handWritten.push n
    let tag := if hw then m!"  {n}" else m!"  {n}  (auto-generated)"
    if rs.isEmpty then
      msg := msg ++ tag ++ m!"\n"
    else
      msg := msg ++ tag ++ m!"\n      via: {rs}\n"
  msg := msg ++
    m!"\nof these, {handWritten.size} are hand-written (the rest are " ++
    m!"auto-generated declarations inheriting `sorryAx` from a type)\n"
  logInfo msg
  unless handWritten.isEmpty do
    logError m!"{handWritten.size} hand-written declaration(s) depend on a \
      `sorry` without being one:\n{handWritten.toList}"

end Theses.AxiomCheck

#sorry_leaks
