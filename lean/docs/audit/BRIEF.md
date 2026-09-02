# Worker brief — bring proofs onto the thesis's own argument

*The current pass (from 2026-09-03).  The briefs of the earlier passes — auditor, proof-route, repair, re-verification — are in git history before this file; their findings are in `docs/STATEMENT-AUDIT.md` and the CSV rows.*

Project: Lean 4 + Mathlib at `lean/` (Lean root). Theses: `../cstar.tex ../vn.tex ../proc.tex` (A, solutions `../asols.tex`), `../dils.tex ../eff.tex` (B, solutions `../bsols.tex`).

## Hard rules
- Compile ONLY via `scripts/lean1.sh <file.lean>` (one `lean` fits in memory; the script serialises through a lock, so you may wait for other workers — that is normal). Never `lake build`, never a language server, never bare `lean`. A compile takes 5-15 min.
- `lean1.sh` compiles one file against prebuilt oleans and writes none: nothing you add in file A is visible from file B this session, and `private` declarations of other files are invisible. Work file by file.
- NEVER change a theorem statement. NEVER add a `sorry`. Do not `git add` or commit; leave work in the tree.
- CSV fields are `|`-separated: NEVER write a literal `|` inside a field. Edit only the rows named in your assignment.
- Scratch files: put them in the session scratchpad with your own prefix (`<yourprefix>-*`); other workers share it.
- `export PATH="$HOME/.elan/bin:$PATH"`; Mathlib source under `.lake/packages/mathlib/`.

## The job
Your assignment names one audit CSV in `docs/audit/` and the Lean files it covers. Schema: `DISP|lean_name|module|stmt|proof|note|status`. Take every row with `proof` = `route` or `mild` whose declaration is in your files.

For each row, in this order:
1. **Re-derive from source, never from the note.** Read the thesis point (the DISP code decodes to a point; the doc comment gives the `.tex` line) and its printed proof or solution. Read our proof. Decide for yourself whether ours follows the printed argument. Recorded reasons in the status field have been wrong more often than right; do not brief yourself off them.
2. If ours already follows the printed argument, or the thesis prints no argument for that step: set `proof` to `faithful` (or `none`) and write a short dated status sentence saying what you checked.
3. If ours diverges and the printed route can be followed in **≤ 150 new lines** with tools already in the tree or in Mathlib: rewrite the proof onto the printed route, keeping the statement byte-identical. Compile until exit 0 with no new warnings. Set `proof` to `faithful` (or `mild` if a local shortcut remains, saying which), status `repaired <date>: <one sentence on what the printed route needed>`.
4. If it cannot be done under that bound: do not start it. Write a precise re-costing in the status field, opening with the existing verdict word (`left-cost` / `left-forced` / `left-mathlib` / `left-unavailable` / `left-encoding` / `left-by-choice` / `left-reasoned`), naming the missing lemma(s) by content and where you looked. Replace stale text rather than appending to it; keep it short.
5. Update the doc comment of a declaration only where it says something now false about its own proof.

Prefer many small faithful conversions over one heroic one. Stop and report when your rows are done or when you have spent about 3 hours.

## Report back (terse)
Per row: DISP, lean_name, old→new proof class, lines added, compile exit code. Then anything you changed outside the assignment and why. The orchestrator commits.
