# Sample brief — re-verify rows graded `ok` from the source

Project: Lean 4 + Mathlib at `lean/` (Lean root). Theses: `../cstar.tex ../vn.tex ../proc.tex` (A, solutions `../asols.tex`), `../dils.tex ../eff.tex` (B, solutions `../bsols.tex`).  Audit schema: `DISP|lean_name|module|stmt|proof|note|status` in `docs/audit/*.csv`; vocabulary in `docs/STATEMENT-AUDIT.md`.

## Purpose
Rows graded `ok`/`faithful` were never re-derived after being graded, and the flagged rows re-derived this week had notes that were wrong more often than right.  This pass measures the error rate of the `ok` grade on a random sample, so that the decision to re-audit everything or nothing rests on a number.

## Hard rules
- READ-ONLY on the tree: do not edit any `.lean` file or any CSV, do not compile, do not run Lean.  Your only output is your findings file.
- Scratch files: the session scratchpad with your own prefix.

## The job
`docs/audit/SAMPLE-2026-09-04.md` lists the sampled rows per audit file; your assignment names your files.  For each sampled row:
1. Locate the thesis point from the DISP (parsec = number, point = roman numeral; the doc comment gives the `.tex` line) and read the printed statement and, if any, its proof or solution.
2. Read the Lean statement and proof.
3. Decide, from the source and the Lean alone: does the Lean statement say what the printed point says (same hypotheses, conclusion, quantifiers, direction), and does the proof follow the printed argument (or is there none)?  Re-derive; do not accept the row's note.
4. Record in `docs/audit/SAMPLE-2026-09-04-findings/<your-assignment-name>.md` one line per row: `CONFIRMED` or `DEFECT` (or `UNSURE`), the DISP and name, and for a defect one sentence saying what differs and which column is wrong (stmt: should be weaker/stronger/differs; proof: should be route/mild).  A defect is a grade that is wrong, not a note that is imprecise.

Be exact and brief.  Report back the counts (confirmed / defect / unsure) and the defect lines.
