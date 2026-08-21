# Proof-route brief — proofs that do not follow the thesis

The audit recorded a `proof` verdict for every transcribed statement.  **502
are not `faithful` and not `none`**: 247 `route` (a different argument), 141
`mild` (the thesis's route with a local deviation), 114 `mathlib` (closed by a
Mathlib lemma without transcribing the author).

Your job is to put proofs back on the thesis's own argument **where that is
the right thing to do** — and to record, precisely, where it is not.

## The criterion, because this is not "convert everything"

A divergence is worth repairing when the thesis's argument **is the content**
and taking another route hides it.  It is *not* worth repairing when the
thesis's route is unavailable, false, or when transcribing it would duplicate
something Mathlib settles and the point is not about that step.

Repair, in descending order of value:

1. **Dependency inversions.**  Our proof derives X from Y where the *thesis*
   proves Y from X.  These are objectively wrong regardless of taste: they
   make the development circular as an exposition even when Lean accepts it.
   Four were found by the audit and three fixed — 11XIII was taken from
   Mathlib's "self-adjoint ⟹ real spectrum", which **is** the thesis's 11XV.1,
   itself proved *from* 11XIII; 27XVII went through maximal *ring* ideals,
   the route 16VIII explicitly rejects; 29II came from 29VII, which the thesis
   proves *using* 29II; 25II.3's part 4 used Mathlib's inverse-order fact that
   its own part 3 establishes.  **Hunt for more of these first.**
2. **Divergences resting on a premise that has expired.**  Nine were retired
   this session, every one justified in-file by a "still `sorry`" that was no
   longer true — and in each case the thesis's route turned out *shorter*:
   95II lost eight lines, 99XI went from a from-scratch universal-property
   proof to three lines, 130V lost about 150, 154III.2 took 60 lines of
   double-polarisation apparatus with it, 208III went from nine lines to
   three.  The sweep of "still `sorry`" claims is done, but a divergence may
   rest on any stale premise — check what the note actually claims.
3. **A substantive exercise or theorem whose argument we simply did not
   transcribe**, where the ingredients are now in the tree.
4. **`mathlib` rows where the point is *about* the step Mathlib supplies.**
   Closing "the operator norm is a norm" by the `NormedAddCommGroup` instance
   states nothing; closing a spectral-permanence theorem that way hides the
   thesis's argument.

**Do not repair** — record the reason instead:

* the thesis's proof is **false** or gapped (158V, 77VI, 106III.3's (E) clause,
  116III.4) — several are already `ERRATA.md` rows;
* it needs something the tree or Mathlib lacks (Fremlin 243I, the Borel
  functional calculus, Tomita–Takesaki);
* the point is a triviality and the thesis's "proof" is a sentence;
* re-proving would **weaken** a statement.  `B/Dils`'s 172VIII was left for
  exactly this reason and that was right.

**Never weaken a statement, never add a `sorry`, and never change a statement
at all in this pass** — statements were settled separately.  If a proof repair
seems to need a statement change, stop and report it.

## A fifth check, added 2026-08-21: **is the transcription used by anything?**

`A/CStar/Positive`'s 16II was closed by a Mathlib lemma — and 16II is the
*only* consumer of the complex-analysis run-up, so `goursat`, `cauchy_formula`,
`taylor`, `rigid_expansion`, `hadamard`, `invint_1/2/4` and
`powerSeries_hasDerivAt` had **zero uses anywhere in the tree**.  About a
thousand lines of faithfully transcribed thesis, hanging off nothing, because
one proof at the top took a shortcut.

`B/Dils` found the same shape twice more: 147II.7 was closed by
`Continuous.ext_on` where `dils.tex` says verbatim "conclude from part 4 and
part 6" — leaving **part 6 with no consumer at all**; and session 94's own
142II repair had zero uses while a hand-rolled 58-line Cauchy–Schwarz sat
beside it.

So: **for each `mathlib` or `route` row, ask what would become unreachable if
the thesis's route were restored — and, conversely, grep whether the results
the thesis's route would have used are used by anything at all.** An
unreferenced faithful transcription is the fingerprint of a shortcut taken
somewhere above it.  `grep -rn "\bname\b" Theses/ --include=*.lean` over a
suspect lemma is cheap and has now paid three times.

## Method

1. Read your rows in `lean/docs/audit/*.csv` — the `proof` column and the note.
   The note usually says what the thesis's route is and why it was not taken.
2. **Check the note's claim against the tree**, not against itself.  This
   project's records go stale; that is the finding that generated this whole
   audit.
3. Work by value, not by volume.  A module with forty `mathlib` rows does not
   need forty transcriptions — it needs the handful where the argument is the
   content.  **Report what you deliberately left and why**; that is as much
   the deliverable as the repairs.
4. Where you re-prove, the statement must stay **byte-identical**.  Verify
   axiom-cleanliness **in situ**: copy the source to the scratchpad, append
   `#print axioms Fully.Qualified.Name`, compile the copy.  Oleans go stale
   and `#print axioms` against them lies.
5. Update the `proof` column of any row you change — `faithful` if it now
   follows the thesis, or a corrected verdict — and say so in the note.

## Build

From `/home/claude/scm/theses/lean`:

```bash
export PATH="$HOME/.elan/bin:$PATH"
LP=".lake/build/lib/lean"; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
env LEAN_PATH="$LP" lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 <file>
```

Both `-D` flags are load-bearing.  Never `lake build`, never `lake env lean`.
Rebuild the olean of any file you change and compile its importers.  Do not
run any state-changing git command.  Log under `## Session 95` in
`PROVING-LOG.md`, with the divergence class of anything you leave.

## Report

Lead with: **how many proofs you put back on the thesis's route, how many you
deliberately left and under which reason, and whether every file still
compiles clean with no new `sorry`.**  Then the dependency inversions you
found, since those are the ones that matter most.
