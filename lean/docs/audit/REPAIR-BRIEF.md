# Repair brief — read this first

The statement/proof audit is complete (`lean/docs/STATEMENT-AUDIT.md`, 2248
rows in `lean/docs/audit/*.csv`, 253 statements that do not match their
source).  Your job is the **first repair pass**: fix what we can fix *without
an author ruling*, in your assigned module.

## The one rule that decides everything

`ERRATA.md`'s scope note draws the line, and it is the line to follow:

> **Only defects in the theses** are errata.  **Our own mis-transcriptions are
> not — they need no author decision**, and are recorded in `PROVING-LOG.md`.

So:

* **REPAIR** — the thesis statement is correct and ours says less, or says it
  differently.  Restore the missing clause or the correct shape, **and prove
  it**.  This needs no ruling; it is what the 167I repair did three days ago
  (six `[VonNeumannAlgebra]` binders restored, logged, no ruling sought).
* **LEAVE, and list in your report** —
  1. the **thesis point is itself defective** (the audit note says false as
     printed, or wrong object, or does not typecheck).  Changing our statement
     to match a falsehood is wrong, and changing it any other way is the
     author's call;
  2. an **open question governs it** — `QUESTIONS.md` A6, A9, A10, B12, B13,
     B14, B15, D7.  Read the current `QUESTIONS.md`; some have been ruled on
     and deleted;
  3. the row is `stronger` and the note calls it a **benign generalisation**
     (a hypothesis the thesis's setting supplies, dropped because the proof
     does not need it).  That is not a defect.  Leave it;
  4. the statement is a **deliberate record of a falsehood**
     (`kaplansky_hilbmod_A*`, `surjective_nmiu_2`, `tensor_simple_facts_4`,
     `ea_modularity_prop`, the `centrally_similar_basic_*` counterexamples).

**Never weaken a statement, never delete one, and never add a `sorry`.**  If a
repair needs mathematics the tree does not have, leave the statement exactly as
it is and report the cost — that is a good outcome, not a failure.

## Cheap repairs to look for first

Some of the audit's findings are pure bookkeeping and cost almost nothing:

* **The statement already exists, untagged.**  `A/VN/Basic`'s 48V is rendered
  by a weak sibling while the thesis's actual statement sits beside it as
  `gnsRepFam_normal` with no doc comment; `B/Eff/Effectus`'s 181VII label sits
  on a private helper while `coprod_prod` carries none; `B/Dils`'s 142II
  content is in untagged private lemmas.  The repair is to move the DISP onto
  the right declaration (and make it public if it is private and now carries a
  numbered point).
* **A mislabelled DISP** — send the reader to the point actually rendered.
* **An unused hypothesis that makes the statement weaker than what we already
  prove** (90II.1's two self-adjointness binders, where the proof calls a lemma
  taking an arbitrary element).  Dropping it needs no new mathematics.

## Method

1. Read your module's rows in `lean/docs/audit/*.csv` — every row with `stmt`
   not `ok`, and every row whose note flags something even when the verdict is
   `ok`.
2. Sort them into repair / leave, by the rule above.
3. Repair, smallest first.  Each repair: restore the statement, extend the
   proof, keep the proof **faithful to the thesis's own argument** where the
   thesis gives one.
4. Recompile after each few repairs; the file must end with **no errors** and
   **no new `sorry`s**.
5. Verify every statement you touched is axiom-clean, in situ — copy the source
   to the scratchpad, append `#print axioms Fully.Qualified.Name`, compile the
   copy.  Oleans go stale and `#print axioms` against them lies.

## Build recipe

`lean` is not on `PATH`, and `lake env lean` blocks forever on another agent's
build.  From `/home/claude/scm/theses/lean`:

```bash
export PATH="$HOME/.elan/bin:$PATH"
LP=".lake/build/lib/lean"; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
env LEAN_PATH="$LP" lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 <file>
```

Both `-D` flags are load-bearing.  Never run `lake build`.  Lean writes
``declaration uses `sorry` `` with **backticks**; a straight-quote grep reports
zero.  And that warning fires only for the declaration *containing* the
`sorry`, never for its consumers — warning counts are not a taint check.
Scratchpad: `/tmp/claude-1016/-home-claude-scm-theses-lean/3f45b388-372a-4e46-8b71-1dc777b2ea63/scratchpad`.

## Rules of engagement

* Edit **only your assigned `.lean` file(s)**, plus append-only notes to
  `PROVING-LOG.md` at the end.  Do not touch `ERRATA.md`, `QUESTIONS.md`,
  `why-open.csv`, the surveys, or another module.
* Do not run `git add`, `git commit`, `git stash`, or any state-changing git
  command.  Leave your work in the working tree.
* Log every repair in `PROVING-LOG.md` under a `## Session 94 — <chapter>:`
  heading, with the divergence class where relevant: (1) faithful, (2)
  different route, (3) mild, (4) our mis-transcription, (5) Mathlib without
  reading the author.

## Final report

Lead with: **how many audit rows you repaired, how many you left and why, and
whether the module still compiles clean with no new `sorry`.**  Then the
repairs one line each, then the ones you left, grouped by which of the four
"leave" reasons applied.  Name anything that turned out to need a ruling you
did not expect.
