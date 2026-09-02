# Worker brief — doc comments state the current fact, not their history

*The cleanup pass of 2026-09-03.  Runs alongside `BRIEF.md` (the proof-route pass); a file is assigned to one pass at a time.*

Project: Lean 4 + Mathlib at `lean/` (Lean root). Theses: `../cstar.tex ../vn.tex ../proc.tex` (A), `../dils.tex ../eff.tex` (B).

## Hard rules
- Compile ONLY via `scripts/lean1.sh <file.lean>`, ONCE per file, after all edits to it (the script serialises through a lock shared with other workers; waiting is normal). Never `lake build`, never a language server, never bare `lean`.
- Change NOTHING but comments and doc comments: no statement, no proof, no name, no `private`, no import. A diff that touches a non-comment line is a failed job.
- Do not `git add` or commit. Never write a literal `|` into any CSV; do not edit CSVs at all.
- Scratch files: the session scratchpad, with your own prefix.

## What to change
A doc comment (or `/-! ... -/` section comment) should tell a reader of the Lean **what this declaration is and how it relates to the thesis point, as of now**. Many instead narrate their own history: "was `sorry` for six sessions", "re-derived 2026-08-29, with one thing this comment used to get wrong", "the earlier reading, struck", "until commit X this said …", session numbers, dated updates stacked on each other.  The history is already in `PROVING-LOG.md` (append-only) and in git.

For every doc comment in your files:
1. Keep: the DISP header line (`**34V** (label, file:line, tag)`), the paraphrased statement, the explanation of how the Lean rendering relates to the printed point (what is mirrored, what is generalised, which sibling carries which clause), the reason a proof takes a different route from the printed one, pointers to `ERRATA.md` rows, `QUESTIONS.md` keys and `docs/DECISIONS.md` sections that are still open, and any warning a reader needs ("false as printed", "the hint's convention is the mirror of ours").
2. Remove: narration of past states and past mistakes of the comment or the proof, dates that only date a narration, session numbers, "struck"/"used to say" passages, and repetition of what a neighbouring comment already says.  Where a date carries information (when a source was corrected, when a ruling landed) keep it in one clause.
3. Rewrite the survivor as plain present-tense prose, as short as it can be while keeping item 1.  A comment that already reads that way is left alone.
4. Verify every pointer you keep: a `QUESTIONS.md` key must exist in that file's headings (or the comment must say it is closed), an `ERRATA.md` row must exist, a `docs/DECISIONS.md §N` must exist, a `File.lean:N` must be within a few lines of the declaration it names.  Fix or drop what does not resolve.
5. Module-level `/-! -/` headers get the same treatment.

Do not shorten mathematics. Do not remove a caveat because it is old; remove it only if it is no longer true, and then say in your report which and why.

After editing, compile the file once; exit 0 with no new warnings.  Then run `python3 scripts/check_all.py` and make sure nothing you touched turned a check red (cite_check, lean_line_check, questions_check, errata_check, xref_check read comments).

## Report back (terse)
Per file: comments edited / total, lines removed, compile exit code, and a list of caveats you removed as no longer true, each with the reason.
