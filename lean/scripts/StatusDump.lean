/-
`scripts/StatusDump.lean` — emit the proof status of every theorem in the tree.

Writes `docs/status.txt`, one line per theorem:

    Theses.A.VN.Basic|Theses.A.VN.some_lemma|green

with status

* `green`  — axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only);
* `red`    — the declaration is itself `sorry`;
* `yellow` — it looks proved but depends on a `sorry` (an *indirect* leak).

This is the data behind the Sorry Map (`scripts/sorry_map.py`).  Unlike
`Theses/AxiomCheck.lean`, which reports only the leaks, this dumps *every*
theorem so the map can show proved ones too.

Two things it deliberately does:

* it filters by **module** (`Theses.A…`/`Theses.B…`) rather than by name
  prefix, because `private` declarations are mangled to `_private.…` and a
  name-prefix filter silently drops them — that once hid the four known-false
  `kaplansky_hilbmod_A*` estimates from the map entirely;
* it keeps only declarations with a declaration range, i.e. hand-written ones,
  so auto-generated `.rec`/`.casesOn`/projections do not appear.

Run from `lean/`:

    lake env lean scripts/StatusDump.lean

or, if another agent holds the `lake` lock:

    LP=".lake/build/lib/lean"; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
    env LEAN_PATH="$LP" lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 \
      scripts/StatusDump.lean

⚠ The two `-D` flags matter when invoking `lean` directly: `lakefile.toml` sets
them and a bare `lean` does not read it, which produces spurious errors.

Beware: this walks the whole environment, so it takes a few minutes.
-/
import Theses
import Lean.Elab.Command

open Lean Elab Command

namespace Theses.StatusDump

/-- Does `e` mention `sorryAx` itself? -/
private def exprHasSorry (e : Expr) : Bool :=
  (e.find? fun s => s.isConstOf ``sorryAx).isSome

/-- The body of a declaration.  `allowOpaque := true` is required: without it
`ConstantInfo.value?` returns `none` for theorems, and every `theorem foo := sorry`
is misclassified as an *indirect* leak. -/
private def bodyOf (ci : ConstantInfo) : Option Expr :=
  ci.value? (allowOpaque := true)

/-- Is the declaration *itself* a `sorry`, as opposed to merely depending on one? -/
private def isDirect (ci : ConstantInfo) : Bool :=
  exprHasSorry ci.type || (match bodyOf ci with | some v => exprHasSorry v | none => false)

/-- Write `docs/status.txt`: one line `module|name|status` per hand-written
theorem of the two theses. -/
elab "#dump_status" : command => do
  let env ← getEnv
  let names : Array Name := env.constants.fold (fun acc n _ => acc.push n) #[]
  let mut out : Array String := #[]
  for n in names.qsort Name.lt do
    let mod := match env.getModuleFor? n with | some m => m.toString | none => ""
    if mod.startsWith "Theses.A" || mod.startsWith "Theses.B" then
      if (← findDeclarationRanges? n).isSome then
        if let some ci := env.find? n then
          if ci matches .thmInfo _ then
            let axs ← Lean.collectAxioms n
            let st := if !axs.contains ``sorryAx then "green"
                      else if isDirect ci then "red" else "yellow"
            -- strip the `_private.<module>.0.` prefix that private names carry
            let short := (n.toString.splitOn "0.").getLast!
            out := out.push s!"{mod}|{short}|{st}"
  IO.FS.writeFile "docs/status.txt" (String.intercalate "\n" out.toList)
  logInfo s!"wrote {out.size} rows to docs/status.txt"

#dump_status

end Theses.StatusDump
