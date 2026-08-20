# Statement & proof audit

A meticulous pass over **every** statement in the two theses that this tree
transcribes, asking two questions of each:

1. **Does our Lean statement say what the thesis statement says?**
2. **Does our Lean proof follow the proof the thesis gives?**

Started 2026-08-20 at commit `f6789a3` (1759 statements carrying a **DISP**
number across 30 modules).  This audit **records** divergences; it does not
repair them.  Nothing in the tree is changed on the strength of a row here —
a repair needs its own commit, and a change to a *statement* needs an author
ruling.

## Why a fresh pass

Fourteen statements have already been found, one at a time and by accident,
to be quietly weaker than or differently shaped from their sources — 30X
dropping `ϱ_Ω`, 51IX dropping ℂ-homogeneity, 28II.4 dropping the identification
with `f(a)`, 167I dropping `[VonNeumannAlgebra]` on all six algebras, 164II.2b
strengthened into a falsehood.  Each was found while working on something
else.  This is the systematic version of that check.

## Schema

One row per thesis statement, pipe-separated, in
`docs/audit/<module-slug>.csv`:

```
DISP|lean_name|module|stmt|proof|note
```

* **`stmt`** — does our statement match the thesis's?
  * `ok` — faithful: same hypotheses, same conclusion, same quantifiers, same
    direction and variance.
  * `weaker` — ours assumes more, or concludes less.
  * `stronger` — ours assumes less, or concludes more.  (Also false-as-ours
    if the extra strength is not actually true.)
  * `differs` — neither weaker nor stronger; a different shape.
  * `unsure` — could not settle it; the note says what is in the way.
* **`proof`** — does our proof follow the thesis's?
  * `faithful` — the thesis's argument, step for step (divergence class 1).
  * `route` — a different route (class 2).
  * `mild` — the thesis's route with a local deviation (class 3).
  * `mathlib` — closed by a Mathlib lemma without transcribing the author
    (class 5).
  * `none` — the thesis gives no proof (Definition, Example, or a bare
    citation), so there is nothing to match.
  * `sorry` — not proved here.
  * `unsure`.
* **`note`** — free text, **required** whenever `stmt` is not `ok` or `proof`
  is not `faithful`/`none`.  Say precisely what differs.  Empty otherwise.

Rows are in DISP order.  A statement transcribed by several Lean declarations
gets one row per declaration.

## Locating a statement in the sources

**Line references drift** — every doc comment carries one (`dils.tex:5024`)
and they are a starting point only.  Locate by point number instead.  A DISP
number `NxR` decodes as:

* `N` — the parsec: `\begin{parsec}{N0}`, e.g. `164` ↦ `{1640}`.
* `x` — an optional lowercase letter for a *sub*-parsec: `a` ↦ `{N1}`,
  `b` ↦ `{N2}`, …  So `125d` ↦ `\begin{parsec}{1254}` and `84b` ↦ `{842}`.
* `R` — a roman numeral giving the point *inside* that parsec:
  `\begin{point}{R0}`, e.g. `II` ↦ `{20}`, `XI` ↦ `{110}`.
* A trailing `.k` or `.2b` names a numbered clause within the point.

The proof, where there is one, is normally the *next* point (`Proof`), or the
following few.

## Roll-up

Filled in as fragments land.  `—` means not yet audited.

| chapter | statements | audited | stmt not `ok` | proof not `faithful`/`none` |
|---|---:|---:|---:|---:|
| A/CStar | 406 | — | — | — |
| A/VN | 422 | — | — | — |
| A/Proc | 403 | — | — | — |
| B/Dils | 307 | — | — | — |
| B/Eff | 221 | — | — | — |
| **total** | **1759** | — | — | — |

## What happens to a finding

Nothing, immediately.  When the audit is complete the rows are triaged:

* a defect in the **thesis** → `ERRATA.md`;
* a question for the **authors** → `QUESTIONS.md`;
* a defect in **our transcription** → repaired, and logged in
  `PROVING-LOG.md` (`ERRATA.md`'s scope note excludes it);
* a **proof** that diverges without needing to → re-proved, or the divergence
  recorded in `PROVING-LOG.md` with its class.
