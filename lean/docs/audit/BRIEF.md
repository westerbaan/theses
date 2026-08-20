# Auditor brief — read this first

You are auditing the Lean formalization of Bram Westerbaan's and Abraham
Westerbaan's PhD theses in `/home/claude/scm/theses` (Lean root
`/home/claude/scm/theses/lean`, LaTeX sources one level up: `cstar.tex`,
`vn.tex`, `proc.tex`, `dils.tex`, `eff.tex`, `bsols.tex`, `asols.tex`).

Read `lean/docs/STATEMENT-AUDIT.md` before starting — it holds the schema,
the verdict vocabulary, and the rule for locating a statement in the LaTeX by
point number.  Your assignment message names your modules and your output
file.

## Your job, for every statement in your modules

For each Lean `theorem` whose doc comment carries a **DISP** number:

1. **Locate the statement in the thesis** by point number (the doc comment's
   `file.tex:NNNN` line reference has drifted and is a hint, not an address).
2. **Compare it, clause by clause, with our Lean statement.**  Hypotheses,
   conclusion, quantifier order and scope, direction of implications,
   variance, which objects are existentially bound, instance binders that
   carry real mathematical content (`[VonNeumannAlgebra …]`, `[CompleteSpace
   …]`, `[Fact …]`).  Ask the question that has found every defect so far:
   *does our rendering say what the source proves?*
3. **Then compare the proofs.**  Read the thesis's proof (normally the next
   point) and the Lean proof.  Does ours follow it, or does it reach the same
   conclusion another way?
4. **Write one row** to your CSV, in the schema of `STATEMENT-AUDIT.md`.

## Rules

* **Change nothing.**  Do not edit any `.lean` file, `ERRATA.md`,
  `QUESTIONS.md`, `PROVING-LOG.md`, `why-open.csv`, or any survey.  Your only
  write is your own CSV under `lean/docs/audit/`.  This pass *records*; the
  repairs come later and separately.
* **Do not run `git add`, `git commit`, `git stash`, or any other
  state-changing git command.**  Read-only git is fine.
* **`unsure` is a real verdict and it is respected.**  A wrong `ok` is worse
  than no row: it launders an unchecked statement as checked, and this project
  has been bitten repeatedly by exactly that.  If you cannot settle something
  in reasonable time, write `unsure` and say in the note what is in the way.
* **Do not audit by name.**  A Lean name that reads like the thesis's phrase
  is not evidence; read both texts.
* Statements that are `sorry` still get a statement verdict — the *statement*
  is auditable even when the proof is absent.  Use `proof` = `sorry`.
* Some points are Definitions, Examples, or bare citations with no proof.  Use
  `proof` = `none`, and still check the statement.
* Work in DISP order and **append rows as you go**, so partial work survives.
* Prior findings are context, not gospel.  `PROVING-LOG.md` records the
  divergence class claimed for many proofs when they were written; check it
  rather than copying it.  Several such records have turned out wrong.

## Useful

* Lean is not on `PATH` and you should not need to compile.  If you want to
  inspect an elaborated statement, use the `lean-lsp` MCP tools
  (`lean_hover_info`, `lean_declaration_file`, `lean_goal`), or:

  ```bash
  export PATH="$HOME/.elan/bin:$PATH"
  LP=".lake/build/lib/lean"; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
  cp <file> "$SCRATCH"/probe.lean && echo '#check @Some.Name' >> "$SCRATCH"/probe.lean
  env LEAN_PATH="$LP" lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 "$SCRATCH"/probe.lean
  ```

  Scratchpad: `/tmp/claude-1016/-home-claude-scm-theses-lean/3f45b388-372a-4e46-8b71-1dc777b2ea63/scratchpad`.
  Never run `lake build`, and never `lake env lean` (it blocks on another
  agent's build).
* The theses' own errata are in `berr.tex` and the `parsec-N.M` block at the
  top of `asols.tex`; a statement corrected there should be audited against
  the *corrected* form.
* `lean/ERRATA.md` already records ~30 known thesis defects and
  `lean/QUESTIONS.md` the open author questions.  If your statement is
  covered by one of those, say so in the note and give the row a verdict
  anyway.

## Final report

Lead with: **how many statements audited, how many `stmt` verdicts were not
`ok`, and how many `proof` verdicts were not `faithful`/`none`.**  Then list
the most serious findings — any `weaker`, `stronger` or `differs` — one line
each, most consequential first, naming the DISP and what differs.  Then say
what you left `unsure` and why.  Report plainly; do not round anything up.
