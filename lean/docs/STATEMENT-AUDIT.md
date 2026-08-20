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

Filled in as fragments land.  Counts are of *rows*, which exceed the 1759
DISP-carrying `theorem`s because auditors also cover definitions and private
auxiliaries that transcribe a numbered point.

| fragment | modules | rows | stmt not `ok` | proof not `faithful`/`none` |
|---|---|---:|---:|---:|
| `acstar-basic` | `A/CStar/Basic` | 109 | **16** (11 weaker, 5 stronger) | 72 (43 mathlib, 26 route, 3 mild) |
| `avn-basic` | `A/VN/Basic` | 137 | **12** (all weaker) | 19 |
| `aproc-tensor` | `A/Proc/Tensor` | 148 | **8** (7 weaker, 1 stronger) | 19 (9 route, 8 mild, 1 mathlib, 1 sorry) |
| `bdils-paschke-stinespring` | `B/Dils/{Paschke, Stinespring}` | 70 | **18** (12 stronger, 5 weaker, 1 differs) | 21 |
| `beff-vnexamples` | `B/Eff/{VNExamples, Comparisons}` | 56 | **17** (6 weaker, 11 differs) | 11 |
| `acstar-matrices-representation` | `A/CStar/{Matrices, Representation}` | 118 | **28** (27 weaker, 1 stronger) | 56 (28 mathlib, 20 route, 8 mild) |

**705 rows in; 102 statements do not match their source** (69 weaker, 21
stronger, 12 differs, 0 unsure).

Not yet audited: `A/CStar/{Positive, TowardsVN}`,
`A/VN/{Projections, Division, NormalFunctionals, Completeness}`,
`A/Proc/{Measurement, Duplicators, QuantumLambda}`,
`B/Dils/{HilbertModules, SelfDualCompletion, SelfDual, Kaplansky, Pure}`,
`B/Eff/{Effectus, Quotients, Dagger, DiamondAmp, StatesPredicates,
EffectAlgebras}`.  (`A/VN/Projections` and `B/Dils/{SelfDual, Kaplansky}` are in flight.)  (`Positive.lean` and `Measurement.lean` are being edited by the
author and are held back deliberately.)

### Standing observations

* **Our doc comments can misrecord what is missing.**  `A/CStar/Matrices`'s
  33III says only "`M_n f` need not be positive", and its doc comment explains
  the omitted clause in the *pre-erratum* form ("need not be bounded") — but
  erratum `parsec-330.30` reverses that clause, asking one to show `M_n f`
  **is** bounded by `n²‖f‖`.  So the file records the wrong thing about its own
  gap.  When a point has an erratum, audit against the corrected form and
  check that our doc comment did too.
* **Dropping a clause can cost a downstream proof.**  34XII omits the Lemma's
  final "in particular, if `p = 0` or `q = 0` then `a = a* = 0`" — which is
  exactly what the thesis uses to finish Choi, so `choi_2` substitutes a
  private `col_eq_zero` for it.  A missing clause is not always inert.
* **Mathlib classes in hypothesis position assume what the thesis proves.**
  Where a statement takes `[CStarModule …]` or `[InnerProductSpace ℂ H]`, the
  class axioms are assumed rather than established: 32VI and 4XV state
  Cauchy–Schwarz only for *definite* inner products where the source allows
  any, and 32IX.1/4III.1 reduce "defines a norm" to the defining equation.
  Bundled Mathlib *objects* appearing in the statement (`gelfandTransform`,
  `gnsStarAlgHom`) are treated as content that is present; classes in binder
  position are not.

* **Seven thesis defects now, not four.**  `B/Dils` adds three: **155II**
  (KSGNS) prints the adjointable map as `T : Y → X`, which does not typecheck
  against the thesis's own `ad_T` of 153I — Kasparov's direction, and ours, is
  `T : X → Y`; **157VI** says "pick `T ∈ ϱ(𝒜)^□`" and then forms `√T`, so its
  claim that `φ_T` is ncp is false without `0 ≤ T`; and **140X.1** prints the
  triple as `(𝒜, ϱ, id)` where the dilating algebra must be `ℬ` (`bsols.tex`
  confirms `𝒫 = ℬ`).  `B/Eff` adds a likely eighth: eff.tex **227III.4** gives
  left-modularity as `f^□(f_⋄(IM k)) = IM k ∨ ⌈1∘f⌉` where `f^□(0) = ⌈1∘f⌉ᵖ`
  and 228II's condition (1) uses `⌈1∘b⌉ᵖ`; the two points are inconsistent and
  228II is right.  227III.4 is not formalized, so nothing in the tree is wrong.
* **One of our statements is false, not merely weaker.**  **139XI**
  `ess_uniq_pur` asserts the conclusion for *arbitrary* `V, W`, dropping all
  three alternative hypotheses the current `dils.tex` carries and `berr.tex`
  says are required.  Its proof is `sorry`, so nothing false is derived — but
  the statement must not be proved as it stands.  The author is revising this
  exercise now; audited against the text at `ea8cfa2`.
* **Doc-comment DISP labels are not reliable.**  `B/Eff/VNExamples` cites
  `31IV` where the rest of the tree writes `30IV`, and names 199II/197II/202I/
  203I.1/203IV for points that are actually 199V/197IV/202IV/203III/203III;
  `B/Dils` labels `nmiu_forall_mem` **138II** when its content is **138IV**,
  and cites **154IV**/**154II** for formulas that are in **154V**.  A wrong
  label sends the next reader to the wrong point.

* **Four thesis statements are false as printed, none of them previously
  recorded.**  Three share one shape — a monotonicity or positivity clause
  stated with no positivity hypothesis: **111IV** `mult-completely-monotone`
  (`(a)≤(ã)`, `(b)≤(b̃)` ⟹ `(ab)≤(ãb̃)`; at `N=1`, `a=b=−1≤0`), **116III.1**
  (`a₁⊗b₁ ≤ a₂⊗b₂` for all `a₁≤a₂`, `b₁≤b₂`; same counterexample at
  `𝒜=ℬ=ℂ`), and **116III.5** (`a ⊗ (·)` an ncp-map for *every* `a`).  The
  fourth is **42III**, which describes the ultrastrong opens with `‖a−b‖_ω ≤ ε`
  where it must be `< ε` — with `≤` a closed ball would be open.  In every
  case our Lean statement silently carries the repair, so it is our *statement*
  that is `weaker`, not our proof that is wrong.
* **A DISP-tagged declaration is not always the right one.**  `A/VN/Basic`'s
  **48V** is rendered by a statement strictly weaker than the point (it fixes
  the family `Ω` and then ignores it) — while the thesis's actual statement
  *is* in the file, as `gnsRepFam_normal`, carrying no doc comment and hence no
  DISP at all.  Auditors should check the neighbourhood, not just the tagged
  declaration.
* **Multi-part exercises rendered by one clause** are the commonest
  divergence by far, in every module audited so far.  Check every numbered
  part, including the "and conclude that …" tails.

* **Deliberate weakenings are mostly unmarked.**  `A/CStar/Basic` carries two
  doc comments saying in so many words that only a "sample claim" of a
  multi-part exercise is stated — and a grep shows those are the *only* two
  such admissions in the whole tree.  So the other weakenings this audit finds
  will not announce themselves.
* **The commonest shape is a multi-part exercise rendered by one clause.**
  9X.1 (whole cone property → the scalar clause), 4III.1 ("the operator norm
  is a norm" → definiteness), 4XV.1–.4 (indefinite inner products →
  `InnerProductSpace`), 7III.5 (ℝ-linear → additive).  None of these is false;
  each says less than the point it cites.
* **`proof = mathlib` is the norm, not the exception**, in the elementary
  chapters: 43 of 109 rows in `A/CStar/Basic`.  That is a legitimate choice
  for facts Mathlib already has, but it means the *thesis's* argument is
  unexhibited, and in a few places it inverts the thesis's own dependency
  order (11XIII from 11XV.1, which the thesis proves from 11XIII).

## What happens to a finding

Nothing, immediately.  When the audit is complete the rows are triaged:

* a defect in the **thesis** → `ERRATA.md`;
* a question for the **authors** → `QUESTIONS.md`;
* a defect in **our transcription** → repaired, and logged in
  `PROVING-LOG.md` (`ERRATA.md`'s scope note excludes it);
* a **proof** that diverges without needing to → re-proved, or the divergence
  recorded in `PROVING-LOG.md` with its class.
