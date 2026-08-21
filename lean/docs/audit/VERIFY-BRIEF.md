# Re-verification brief — closing the loop on the audit

The statement audit of 2026-08-20 flagged **253 rows** across
`lean/docs/audit/*.csv` as not matching their source.  Three repair waves
followed (commits `acde73c` … `e67f1e9`, all 30 modules).  **The CSVs were
never updated**, so the Sorry Map still draws a wedge on every one of those
rows and reports "statement ≠ source: 194" — which is now wrong, and wrong in
the direction that overstates the problem.

Your job is to establish, **row by row and against the current tree**, which
findings still hold.

## What you do

For every row in your assigned CSVs whose `stmt` is not `ok`, append a
**seventh field**, `status`:

* **`repaired`** — the finding no longer holds.  Either the flagged
  declaration now says what the point says, or the missing clause is stated
  elsewhere.  **Name where**, in the note: the repair waves deliberately added
  a *sibling* declaration in many cases rather than changing the flagged one,
  because several statements are destructured by consumers.  A sibling counts
  as repaired — the point is on record — but only if you have read it and it
  really is the clause.
* **`open`** — the finding still holds and nothing blocks repairing it.
* **`left-thesis`** — deliberately left: the thesis point is itself defective,
  so matching it would import a falsehood.
* **`left-ruling`** — governed by an open item in `QUESTIONS.md`.  Say which.
* **`left-benign`** — a `stronger` row that is a true generalisation the
  thesis's setting supplies.  Not a defect.
* **`left-cost`** — costed and declined.  Give the cost.

Keep the existing six fields **byte-for-byte unchanged**; you are appending
one field, not rewriting rows.  Rows whose `stmt` is `ok` are untouched and
keep six fields.

## How to decide

**Read the Lean, not the log.** `PROVING-LOG.md`'s session-94 entries record
what each repair worker believed it did, and they are a good index — but the
audit itself found that this project's records go stale, which is the whole
reason the map is now wrong.  Confirm against the source file.

Locate points in the LaTeX by number, not by line: DISP `NxR` is
`\begin{parsec}{N0}` (or `{N<k>}` for a lettered sub-parsec, `d` being the
4th), then `\begin{point}{R0}`.  The `.tex` sources have themselves been
edited since the audit, so check the current text.

**`unsure` is not a status.**  If you cannot settle a row, mark it `open` and
say in your report why — an overstated `repaired` is the exact failure this
pass exists to correct.

## Rules

* Edit **only your assigned CSVs**.  Do not touch any `.lean` file,
  `ERRATA.md`, `QUESTIONS.md`, `PROVING-LOG.md`, the surveys or the map.
* Do not run `git add`, `git commit`, `git stash` or any other state-changing
  git command.
* You should not need to compile.  If you want to inspect an elaborated
  statement: `export PATH="$HOME/.elan/bin:$PATH"`, then
  `LP=".lake/build/lib/lean"; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done`,
  then copy the file to the scratchpad, append `#check @Some.Name`, and run
  `env LEAN_PATH="$LP" lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 <copy>`.
  Never `lake build`, never `lake env lean`.
  Scratchpad: `/tmp/claude-1016/-home-claude-scm-theses-lean/3f45b388-372a-4e46-8b71-1dc777b2ea63/scratchpad`.

## Report

Lead with the tally: **how many rows `repaired`, `open`, and left under each
reason.**  Then anything that surprised you — a row the log claimed repaired
that is not, or one nobody claimed that turns out to be fine.
