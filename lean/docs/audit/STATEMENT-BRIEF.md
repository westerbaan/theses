# Statement-alignment brief — bring a Lean statement up to the printed one

*Authorised by the author's ruling on `docs/DECISIONS.md` §2.1, 2026-09-04: option (a), with one condition.  A change that brings a Lean statement **closer to the printed statement of its own point** needs no ruling — but ONLY inside a pass whose assignment is exactly this.  In any other job a statement stays byte-identical, whatever the worker thinks of it.  Changes that go beyond the print, or weaken a statement, still need a ruling.*

Project: Lean 4 + Mathlib at `lean/` (Lean root). Theses: `../cstar.tex ../vn.tex ../proc.tex` (A, solutions `../asols.tex`), `../dils.tex ../eff.tex` (B, solutions `../bsols.tex`).  Audit schema `DISP|lean_name|module|stmt|proof|note|status`; vocabulary in `docs/STATEMENT-AUDIT.md`.

## Hard rules
- Compile ONLY via `scripts/lean1.sh <file.lean>` (serialised lock; scratch-file iteration allowed; one full compile per touched file at the end). Never `lake build`, never a language server. `lean1.sh` writes no olean: a downstream file cannot see what you add upstream this session.
- Never add a `sorry`. Do not `git add` or commit. Never write a literal `|` into a CSV field.
- Scratch files: the session scratchpad, your own prefix.

## The job
Your assignment names rows graded `weaker` or `differs` whose verdict is ours (`left-cost`, `open`, or an unverdicted field), not `left-thesis`, `left-ruling` or `left-benign`.  For each:
1. Re-derive the printed statement from the source (DISP → parsec/point; the doc comment gives the `.tex` line).  Identify exactly which clause, hypothesis, quantifier or object differs, and check that the difference is ours (a transcription gap) and not a defect of the print (then the row is `left-thesis` and stays) or a deliberate encoding the file documents (then `left-encoding`, and stays).
2. Change the statement to the printed one — adding the missing clause, dropping the extra hypothesis, naming the printed object — and repair the proof and every consumer (grep the tree; consumers in other files cannot be compiled this session, so keep the change conservative: prefer adding a clause to a conjunction, or a sibling declaration carrying the printed form, over changing a signature many files destructure).  Compile.
3. Regrade the row `ok` with status `repaired <date> under the §2.1 ruling: <what changed>`; if the change cannot be made without weakening something or going beyond the print, leave it and say why with the right `left-…` word.
4. Update the doc comment; record the statement change in the row (the old form, one line) so the history is recoverable; `PROVING-LOG.md` gets one entry from the orchestrator.

Report per row: old → new statement in one line each, consumers touched, lines, compile exit code.
