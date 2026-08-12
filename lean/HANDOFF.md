# Handoff — state of the formalization

Written at the end of the first proving session.  Read this together with
[PROVING-LOG.md](PROVING-LOG.md) (errata + parked items) and
[CONVENTIONS.md](CONVENTIONS.md) (numbering + naming).

## What exists

A Lean 4 + Mathlib formalization of the **statements** of both theses, with
proofs being filled in incrementally.

* Statements: complete.  Every lemma/proposition/theorem/corollary/exercise
  of both theses (932 thesis points, ~1675 declarations, 30 files) is stated
  in Lean.  Definitions are real; only proofs are `sorry`.
* Proofs: in progress, see the table below.
* Everything compiles: `lake build` succeeds, `sorry` warnings only.

## Setting up on a fresh machine (Ubuntu)

The repository carries only sources: `.lake/` is git-ignored, so a clean
checkout needs the toolchain and the Mathlib build cache before anything
compiles.  Budget **~11 GB of disk** (7.4 GB `.lake/packages`, 2.7 GB
toolchains, 0.5 GB cache tarballs) and ≥8 GB RAM.

```sh
# 1. toolchain manager (installs to ~/.elan, adds to PATH via ~/.profile)
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
source ~/.profile          # or: export PATH="$HOME/.elan/bin:$PATH"

# 2. the project
git clone <this repo> && cd theses/lean
#    elan reads lean-toolchain (leanprover/lean4:v4.34.0-rc1) and fetches it

# 3. Mathlib sources + prebuilt oleans — do NOT skip, building Mathlib from
#    source takes hours; `cache get` takes a few minutes
lake exe cache get

# 4. verify
lake build                 # expect a wall of `sorry` warnings — that's the point
```

`apt` has no usable Lean packages; the elan script above is the supported
route on Linux.  If `cache get` reports corrupted files, re-run it — it is
idempotent and only re-fetches what's missing.

Everyday commands:

```sh
lake env lean Theses/B/Eff/EffectAlgebras.lean   # check one file, ~1-2 min
lake build Theses.A.CStar.Basic                  # rebuild one module + deps
lake build                                       # everything
```

**Rebuild oleans after adding helpers.** `lake env lean` reads *built* oleans
for imports, not sources, so a helper added to file X is invisible to file Y
until `lake build <X's module>` runs.  Several items in this session were
parked for this reason alone and turned out to be provable afterwards — if
you resume parked items, rebuild first.

History: `8d6f684` added the statements; the commit carrying this file adds
the first round of proofs.  Both are on `master`; push before switching
machines.

## Progress

**Session 1 result: 1401 → 947 code `sorry`s (454 proved, 32%).**

| chapter | file | start | now |
|---|---|---|---|
| **B/Eff** | **449** | | **129** |
| | WStarCat.lean | 15 | **0** |
| | Quotients.lean | 45 | **2** |
| | Effectus.lean | 41 | 10 |
| | EffectAlgebras.lean | 147 | 17 |
| | DiamondAmp.lean | 49 | 17 |
| | StatesPredicates.lean | 111 | 33 |
| | Dagger.lean | 42 | 35 |
| | Comparisons.lean | 20 | 16 |
| **A/CStar** | **304** | | **170** |
| | Basic.lean | 92 | **11** |
| | Representation.lean | 40 | 17 |
| | Positive.lean | 93 | 63 |
| | Matrices.lean | 55 | 55 — untouched |
| | TowardsVN.lean | 27 | 27 — untouched |
| **A/VN** | (5 files) | 276 | 276 — untouched |
| **A/Proc** | (4 files) | 233 | 233 — untouched |
| **B/Dils** | (7 files) | 139 | 139 — untouched |

Counts are of `sorry` **in code**, excluding backticked mentions in doc
comments.  Refresh with:

```sh
for d in B/Eff A/CStar A/VN A/Proc B/Dils; do
  echo -n "$d: "
  cat Theses/$d/*.lean | grep -E '(^|[^`])\bsorry\b' | grep -vc '`sorry`'
done
```

(Earlier progress rows in PROVING-LOG.md used raw `grep -c sorry`, which
counts doc-comment mentions too; the two sets of numbers differ by a few per
file.)

## Findings for the authors

The point of this exercise, beyond the Lean files, is
[PROVING-LOG.md](PROVING-LOG.md): **~14 errata** in the theses' own proofs,
found by trying to transcribe them.  The substantive ones:

* **195VII** (eff.tex:3331) rests on a step that is **false**: "if `c⊙a ⊥ c⊙b`
  then `(c/c)⊙a ⊥ (c/c)⊙b`" fails in `[0,1]` at `c = ½`, `a = b = 1`.  The
  statement is true; the Lean proof takes a different route.
* **16V** `spectrum-non-empty` is **false as stated** for the trivial
  C*-algebra `{0}`, which 8II explicitly admits: there every element is a
  unit, so `spec(a) = ∅`.  (Five more spectrum/norm statements need a
  `subsingleton_or_nontrivial` split for the same reason.)
* **Partial associativity is used backwards** in at least two places
  (eff.tex:414 and the `exc-dposet` solution): from `a ⊥ (c ⋁ d)` they
  conclude `a ⊥ c`, which the PCM axioms do not give.  Recoverable — the
  development now has an explicit `PCM.assoc_left`.
* **178IIIa** (bsols.tex:1645) uses one-sided distributivity, which is not an
  effect-monoid axiom; the four-fold law of 178II leaves exactly the terms
  being proved to vanish.
* **221IV.6** (eff.tex:6923) never checks that the induced map is *pure*,
  which 221II's definition of a dilation requires.
* **186VIII.2** uses a `κ₂` form of a pullback axiom stated only for `κ₁`.
* **189I.2** (bsols.tex:1822) swaps "total form" and "partial form".
* **30IV.2** — the suspicious extra `‖ω‖` factor is confirmed **spurious**:
  Mathlib's GNS construction proves `‖ab‖_ω ≤ ‖a‖‖b‖_ω` with no `‖ω‖`.
* **11VI.2** confirmed: the bound should be `‖a‖ < ‖b⁻¹‖⁻¹`.

## How to resume

Suggested order, easiest first:

1. **A/CStar** — finish it.  Mathlib has most of this chapter; see the
   "productive entry points" list below.  It is also the prerequisite for
   everything else in thesis A *and* for the `vNᵒᵖ` examples parked in B/Eff.
2. **A/VN** — von Neumann algebras.  Mathlib's `VonNeumannAlgebra`/
   `WStarAlgebra` are *different definitions* from the thesis's Kadison-style
   `Theses.VonNeumannAlgebra`, so expect less Mathlib reuse here.
3. **B/Dils** — dilations; depends on A/CStar + A/VN.
4. **A/Proc** — depends on A/VN.
5. The deep B/Eff remainder (Cho's theorem, parsecs 190–196, the †-effectus
   development) — mostly blocked on thesis A.

### The workflow that worked

Per `sorry`: **(a)** look for the Mathlib lemma first — many statements close
in one line; **(b)** otherwise read the thesis's own proof — in the `.tex`,
nearly every statement point is immediately followed by a `{Proof}` point,
and each Lean doc comment gives `file:LINE`; **(c)** exercise solutions are in
`../asols.tex` / `../bsols.tex`, keyed by the *same* LaTeX label the doc
comment carries: `grep -n 'solution}{exc-subbase}' ../bsols.tex`.

### Tooling to set up next time (recommended)

This session's workers proved *blind*: to see a goal they inserted a tactic
and recompiled the whole file; to find a Mathlib lemma they grepped the
source tree or wrote `exact?` and recompiled to read the suggestion.  With
warm oleans a small file re-checks in ~5 s, so compile time is not the
bottleneck — **not seeing goal states** is.

Worth setting up before the next push:

* **A Lean MCP server** — `lean-lsp-mcp` is the mature one (verify its
  current package name and tool list; the API may have moved).  It exposes
  goal state at a position, diagnostics, hover, completions, and lemma search
  by goal shape (`exact?`-style plus Loogle / LeanSearch).  Lemma discovery
  is the highest-value item: the A/CStar worker's own conclusion was that
  progress came from finding the right CFC lemma, and that search is
  currently manual guess-then-grep.
* **Cheaper first step**: this harness has a built-in LSP tool (hover,
  goToDefinition, workspaceSymbol).  If a Lean language server is configured
  it gives Mathlib symbol search and types-on-hover at zero setup cost — no
  goal state or tactic search, but part of the same win.

Two operational caveats:

* Each live Lean session holds all of Mathlib in memory (~4-6 GB).  One per
  parallel worker needs a well-sized box; otherwise serialize the
  MCP-using workers.
* Subagents do not see MCP tools automatically — they reach them via tool
  search.  Worker prompts must say explicitly to use them, or they fall back
  to grep-and-recompile.

### Parallelism

The work parallelises well because proofs don't affect statements: several
workers can prove different files at once, each owning a disjoint set of
files.  What to watch for (all of it bit us at least once):

* Give each worker **exclusive ownership** of its files; everything else is
  read-only to it.  Two workers editing one file will clobber each other.
* Workers see each other's *sources* but each other's **stale oleans** — so a
  helper added elsewhere during the run is not importable.  Either rebuild
  between waves, or accept some duplicated helpers and consolidate after.
* `PROVING-LOG.md` is shared mutable state: instruct workers to **append
  only**, re-read immediately before writing, and touch only their own rows
  in the progress table.
* Doc comments: workers are told never to edit them (they carry the thesis
  cross-references), so stale "`sorry`-ed" claims accumulate and need a
  separate sweep — that sweep is the one time editing them is correct.
* Lean respects `LEAN_NUM_THREADS`; on a many-core server cap it (e.g. 4-8)
  when running several workers, or the concurrent `lake env lean` invocations
  will thrash.

Rules given to every worker, worth keeping:
* **Never change a statement.**  Park instead: leave the `sorry`, add a line
  to PROVING-LOG.md saying why.  A wrong proof is far worse than a `sorry`.
* Log every thesis proof you had to repair (see PROVING-LOG.md) — that file
  is the most valuable output of this exercise for the authors.
* Compile after every small batch; never leave a file broken.
* No `axiom`s, no `native_decide`.

### Most productive Mathlib entry points (A/CStar)

* `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean` — the single
  most useful file (`IsSelfAdjoint.le_algebraMap_norm_self`,
  `CStarAlgebra.norm_or_neg_norm_mem_spectrum`, `norm_le_norm_of_nonneg_of_le`,
  `isClosed_nonneg`, `CFC.inv_nonneg`).
* `.../ContinuousFunctionalCalculus/Unital.lean` — `le_algebraMap_iff_spectrum_le`,
  `algebraMap_le_iff_le_spectrum`, `StarOrderedRing.nonneg_iff_spectrum_nonneg`:
  these turn order statements into real-spectrum statements and are the
  workhorses.
* `CStarAlgebra/Spectrum.lean`, `GelfandDuality.lean`,
  `GelfandNaimarkSegal.lean`, `CStarMatrix.lean`, `CompletelyPositiveMap.lean`,
  `Unitary/Span.lean` (Russo–Dye), `CStarAlgebra/Module/**`.
* `Algebra/Order/Star/Basic.lean` — `star_left_conjugate_nonneg`.  Note
  Mathlib has **no** `PosSMulMono ℝ A` instance for C*-algebras; conjugate by
  the scalar `√r` instead.
* Helpers added in `Theses/A/CStar/Basic.lean` and reusable downstream:
  `algebraMap_real_eq`, `isSelfAdjoint_algebraMap_ofReal`, `ofReal_smul_nonneg`,
  `algebraMap_ofReal_nonneg/_mono`, `norm_le_iff_neg_algebraMap_le`,
  `orderNorm_eq_norm`, `IsProjectionOn.norm_eq_iInf/.inner_eq_zero`,
  `norm_le_of_isAdjointTo`.

## Open decisions (need the author)

Three places where the honest fix is to change one of *our* statements — not
done, because the standing rule is never to change a statement without
approval:

1. **`orderIntervalEffectModule`** (B/Eff/EffectAlgebras.lean) — false as
   stated: the hypotheses relate the order of `V` to `+` but never to the
   scalar action, so even the data field `r • v ∈ [0,u]` fails (order `ℝ` by
   the cone of a ℚ-linear functional).  Needs `PosSMulMono ℝ V` added.
2. **221IV.1** (B/Eff/Dagger.lean) — our statement asks the mediating iso to
   be unique among all `α'` with `h₁ ∘ α' = h₂`, but the universal property
   (and dils.tex:1176) only gives uniqueness among those that also satisfy
   `ϱ₂ ∘ α' = ϱ₁`.  As stated it is too strong.  Not a thesis error.
3. **16V** `spectrum-non-empty` (A/CStar/Positive.lean) — false for the
   trivial C*-algebra `{0}`, which the thesis explicitly admits (8II); in it
   every element is a unit, so `spec(a) = ∅`.  Mathlib's `spectrum.nonempty`
   carries `[Nontrivial]`.  Either add that hypothesis or exclude the trivial
   algebra globally.  (Five further spectrum/norm statements need a
   `subsingleton_or_nontrivial` case split for the same reason.)

Also worth a decision: whether `Theses.VonNeumannAlgebra` (Kadison) should
eventually be proved *equivalent* to Mathlib's `WStarAlgebra` (Sakai) — that
bridge would unlock a lot of Mathlib reuse in A/VN.

## Known cleanups

* Some doc comments still say obligations are "`sorry`-ed" for declarations
  that are now proved (workers were forbidden to edit doc comments).
* A few helper lemmas exist in duplicate under `pcm_`, `dia_`, `dag_`
  prefixes, from workers compiling against each other's stale oleans.
  (A consolidation pass was running when this was written.)
* `grep -rn 'FIXME' Theses` — ~20 markers from the statement-writing phase,
  mostly missing carriers (`B^a(X)` as a type, `L^∞` algebra instances,
  Borel functional calculus).
