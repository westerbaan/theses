# Handoff — state of the formalization

Written at the end of the first proving session.  Read this together with
[QUESTIONS.md](QUESTIONS.md) (**everything awaiting an author decision**) and
[ERRATA.md](ERRATA.md) (**every defect found in the theses**, ordered by point
number for processing) — start with those two if you are an author — plus
[PROVING-LOG.md](PROVING-LOG.md) (the full record, including our own
mis-transcriptions) and [CONVENTIONS.md](CONVENTIONS.md) (numbering + naming).

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

# 5. the Lean MCP server (goal states + lemma search — see "Tooling" below)
curl -LsSf https://astral.sh/uv/install.sh | sh   # provides uvx
sudo apt install ripgrep                          # for lean_local_search
#    `.mcp.json` is committed, so Claude Code picks the server up on the next
#    start and asks once to approve it.  Run `lake build` first: the server
#    starts `lake serve`, which is slow against cold oleans.
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

**Session 3 result: 1402 → 458 code `sorry`s overall (944 proved, 67%).**
Four files are complete: `A/CStar/Basic`, `A/CStar/TowardsVN`,
`B/Eff/Quotients`, `B/Eff/WStarCat`.

| chapter | start | now | proved |
|---|---|---|---|
| **B/Eff** | 450 | **37** | 92% |
| **A/CStar** | 304 | **41** | 87% |
| **A/VN** | 276 | **128** | 54% |
| **B/Dils** | 139 | **75** | 46% |
| **A/Proc** | 233 | **177** | 24% |
| **total** | **1402** | **458** | **67%** |

Refresh with — **the only trustworthy recipe is to ask the compiler**:

```sh
lake build 2>&1 | grep -oE "Theses/[A-Za-z/]+\.lean:[0-9]+:[0-9]+: declaration uses" \
  | sort -u | sed 's|:[0-9]*:[0-9]*.*||' | uniq -c | sort -rn
```

This counts **declarations that still use `sorry`**, per file, from the compiler's
own warnings.  Warnings replay from cache, so it is cheap after the first build.

⚠️ **Pair it with an error count.**  A file with hard errors still emits its
`declaration uses 'sorry'` warnings, so the table can look right while a file
does not compile at all.  This happened for two sessions running:
`SelfDual.lean` was broken by a name clash introduced in
`SelfDualCompletion.lean` (session 59) and reported its usual 7 the whole time
(PROVING-LOG session 61).  So per file also run
`env LEAN_PATH="$LP" lean <file> 2>&1 | grep -c ': error'`, and **after adding
a public name to a file, re-check its dependents** — `private` does not protect
you: Lean refuses a private declaration whose name an imported public one
already holds.

Do **not** count with grep.  The old recipe was

```sh
n=$(grep -o '\bsorry\b' $f | wc -l); m=$(grep -o '`sorry`' $f | wc -l)   # WRONG
```

and it over-counts in two independent ways that between them inflated the
project total by about 5%:

* `\bsorry\b` matches prose in doc comments — "sorry-ed", "still sorry", file
  header summaries.  This produced wrong per-file counts four times in one week
  (`Stinespring` 7 vs 6, A/Proc 120 vs 115, `QuantumLambda` 20 vs 17,
  `Tensor` 45 vs 43), and three of those errors reached commit messages.
* It counts `sorry` **tokens**, while the compiler counts **declarations**.  One
  declaration with three `sorry`s is one open goal, not three (`Pure.lean`: 15
  tokens, 13 declarations).

Use the token count only when you specifically mean tokens, and say so.
(Excludes the two tooling `sorry`s in `AxiomCheck.lean`.  The baseline is the
statements-only commit `8d6f684`; earlier notes say 1401, counted slightly
differently — and on the grep basis, so the historical trend line is not exactly
comparable with compiler-counted figures.)

**A/Proc and most of B/Dils are cold because of sequencing, not difficulty** —
they sit at the end of the import chain `A/CStar → A/VN → {A/Proc, B/Dils}` and
no worker has been sent at them.  The real frontier is **A/VN**, where 72V is
the wall.

`lake build` succeeds; `sorry` + style-linter warnings only.

Session 3 ran two workers at a time, one per independent chain (the A chain,
and B/Eff which imports only `Theses.Common`).  See "Parallelism" below.

**A git trap worth knowing.** `git commit` commits the *index*, not the paths
you just named to `git add` — so when a worker has staged its own files,
`git add <my files> && git commit` silently sweeps the worker's staged work
into your commit under your message.  This happened in `bbe9ab6`, which
carries 798 lines of `B/Eff/StatesPredicates.lean` its message does not
mention (193X, 194I.3, 194I.4 — all verified clean afterwards).  Check
`git status` before committing, or use `git commit -- <paths>`.

<details>
<summary>Session 1 result: 1401 → 947 code `sorry`s (454 proved, 32%)</summary>

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

</details>

## Findings for the authors

The point of this exercise, beyond the Lean files, is the defects it turns up.
Two files hold them, so an author can work top to bottom without reading the
proving log:

* **[ERRATA.md](ERRATA.md)** — every defect in the theses, as tables grouped by
  source file and ordered by point number, each with a one-line fix and a
  status (`DONE` with its `parsec-N.M` erratum key, or `OPEN`).  Currently
  **38 thesis-A and 36 thesis-B** entries (a few cover several points each).
  Refresh the counts with
  `awk '/^## Thesis A/,/^## Thesis B/' ERRATA.md | grep -c '^| \*\*'`.
* **[QUESTIONS.md](QUESTIONS.md)** — the smaller set that needs a *decision*
  rather than a correction: a false claim whose intended repair is unclear, a
  definition that is too weak to prove what depends on it, results the theses
  only cite.  All thesis-B items are still open; thesis A was ruled on
  2026-08-13.

Our *own* mis-transcriptions are deliberately in neither — they need no author
attention and live in [PROVING-LOG.md](PROVING-LOG.md).

**How they were found is the part worth keeping.**  Proving a statement finds
nothing: a proof that closes is not evidence the source is right.  Every
erratum above came from *comparing* our proof with the author's, and two
dedicated audits — re-reading the authors' arguments for statements **already
proved** from Mathlib — produced 10 errata between them.  That is why the
workflow was inverted to "transcribe the thesis's proof first, Mathlib only as
fallback".

The single most productive check is reading a declaration against the
`file:LINE` its own doc comment carries; the second is reading it against its
own doc-comment *prose*, which has caught a false statement carrying no source
reference at all.  The recurring trap is the **"silent half-repair"** — a
clause quietly corrected in one statement and not carried to its siblings,
which has hidden two real errata (most recently `kaplansky_effects`, which
dropped a norm bound its three siblings kept).

## How to resume

Suggested order, easiest first:

1. **A/CStar** — 88 left of 170.  `Basic.lean` is **done**.  The highest-return
   items are not evenly spread; two bottlenecks each unblock a cluster:
   * the **⇐** direction of **33II.1** `cstar_matrix_positive_iff`
     (Matrices.lean) — `n_pos`, `cp_iff`, `cp_comp`, `cstar_positive_2x2matrix`
     and `cp_cs` are all downstream, and their other implications are already
     elementary;
   * the **cofinal-tail filter lemma** for **37IX** (TowardsVN.lean) — five
     statements (37IX.1–3, 37XI, 38II) wait only on it, and everything else they
     need is proved and in the file.

   What is left after those is genuinely hard and mostly needs infrastructure
   Mathlib lacks: the complex-analysis parsecs 120–150 (Goursat/Cauchy/Taylor,
   ~12 statements, needs Banach-valued contour integration), the order-ideal /
   Hahn–Banach development (~9), and the Riesz-ideal route of 27VIII–27XIII (8,
   though **27XV** is now proved independently, so that chain is no longer
   load-bearing).
2. **A/VN** — von Neumann algebras.  Mathlib's `VonNeumannAlgebra`/
   `WStarAlgebra` are *different definitions* from the thesis's Kadison-style
   `Theses.VonNeumannAlgebra`, so expect less Mathlib reuse here.
3. **B/Dils** — dilations; depends on A/CStar + A/VN.
4. **A/Proc** — depends on A/VN.
5. The deep B/Eff remainder (Cho's theorem, parsecs 190–196, the †-effectus
   development) — mostly blocked on thesis A.

### The workflow that worked

**The thesis's proof comes first — Mathlib is the fallback, not the default.**
Session 2 ran it the other way round ("try Mathlib first, it often closes in one
line") and that was wrong.  A one-line Mathlib closure proves the statement true
and cross-checks *nothing*; errata exist only where the two arguments are
compared.  When nine such proofs were later re-read against the authors'
arguments, that single pass produced **four new errata**.

Per `sorry`:

**(a)** **Read the author's proof.**  In the `.tex`, nearly every statement
point is immediately followed by a `{Proof}` point, and each Lean doc comment
gives `file:LINE`.  Exercise solutions are in `../asols.tex` / `../bsols.tex`
(mind the keying — see below).
**(b)** **Transcribe that argument**, using Mathlib for the mechanical steps
inside it.
**(c)** **Only if it cannot be transcribed** — needs infrastructure Mathlib
lacks, or is wrong — take a Mathlib route instead, and **log why**.

**Respect the thesis's dependency order.**  Where the author deliberately avoids
a big theorem because their development has not reached it, do not reach for
Mathlib's version: the resulting proof is sound but checks none of the
bootstrapping.  Two live examples, both flagged in PROVING-LOG.md: **9X.3**
closed via `a*a ≥ 0`, which the thesis cannot have until **25I** (9X.5 lists even
"`a²` is positive" as out of reach); and **11XV.3** closed via polynomial
spectral mapping, when the author's factorisation *is* the elementary substitute
for exactly that theorem.

This is slower per `sorry`, deliberately.  If the author's argument is long and
you cannot finish it, **park it with a note** saying how far you got — never
substitute a Mathlib proof silently.  A one-liner remains fine when it genuinely
*is* the author's argument, or when the doc comment says the item just records a
Mathlib result.

⚠️ **The two solution files are keyed differently, and getting this wrong is
silent.**  `bsols.tex` uses the LaTeX label the doc comment carries
(`grep -n 'solution}{exc-subbase}' ../bsols.tex`), but `asols.tex` uses
**parsec/point numbers**: `solution}{parsec-<parsec×10>.<point×10>}`, so `4IV`
is `parsec-40.40`, `9X` is `parsec-90.100`, `11XV` is `parsec-110.150`.  A
label search against `asols.tex` matches **none** of its 64 solutions and looks
exactly like "there is no published solution".  This cost session 2 a batch of
statements that were proved from Mathlib without ever consulting the author's
argument — see the divergence list at the top of PROVING-LOG.md.

**Ordering caveat:** step (a) before (b) is efficient, but if a Mathlib lemma
closes the goal it is tempting to stop there and never read the thesis proof.
That is fine for throughput and bad for the errata, which are the point of the
exercise — errata are only found by *comparing* the two. When you skip the
thesis proof, log that you skipped it (case 4 in PROVING-LOG's divergence list)
so the gap is visible rather than invisible.

### Tooling: the Lean MCP server (installed — on Linux; see the last caveat)

Session 1's workers proved *blind*: to see a goal they inserted a tactic and
recompiled the whole file; to find a Mathlib lemma they grepped the source
tree or wrote `exact?` and recompiled to read the suggestion.  With warm
oleans a small file re-checks in ~5 s, so compile time was never the
bottleneck — **not seeing goal states** was.

That is fixed.  `lean-lsp-mcp` (0.29.0, server reports "Lean LSP 1.28.1") is
configured in the committed `.mcp.json` and exposes 23 tools.  The ones that
matter here, each verified against this repo:

| tool | use |
|---|---|
| `lean_goal` | tactic state at a line — returns `goals_before`/`goals_after` |
| `lean_term_goal` | expected type at a position; **this is the one for our `sorry`s**, which are mostly term-mode `:= sorry` and give a null `lean_goal` |
| `lean_code_actions` | harvests `exact?` / `apply?` / `simp?` "Try this" edits without recompiling to read them |
| `lean_local_search` | ripgrep over Mathlib + project; no rate limit — make this the default |
| `lean_loogle`, `lean_leansearch`, `lean_leanfinder`, `lean_state_search`, `lean_hammer_premise` | lemma search by shape / natural language / goal |
| `lean_verify` | axioms a theorem actually uses — enforces the no-`axiom` rule and detects lingering `sorryAx` |
| `lean_multi_attempt` | screen several tactics at one position before committing |
| `lean_diagnostic_messages` | errors/warnings without a full `lake build` |

Worked examples, so the next session doesn't rediscover the calling
conventions:

* `lean_term_goal` at `Theses/A/CStar/Positive.lean:91` returns the full
  context and `⊢ Summable fun n ↦ ‖a n‖ * ‖z‖ ^ n`.
* `lean_goal` at `Theses/B/Eff/Dagger.lean:533` returns `⊢ IsPure h''` with
  all 17 hypotheses.
* `lean_verify` on `Theses.A.CStar.orderNorm_eq_norm` returns exactly
  `propext, Classical.choice, Quot.sound` (clean); on
  `Theses.A.CStar.hadamard_1` it additionally returns `sorryAx`.  Note the
  name must be fully qualified, and `section Positive` / `section Order` in
  `Basic.lean` are **sections, not namespaces** — they contribute nothing to
  the name.

Operational caveats:

* **The `bash -c` wrapper in `.mcp.json` is load-bearing — do not "simplify"
  it to `"command": "uvx"`.**  Claude Code spawns MCP servers in a minimal
  environment: `PATH` is the bare default
  (`/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin`, containing
  neither `~/.local/bin` for `uvx` nor `~/.elan/bin` for `lake`) **and `HOME`
  is not set**.  Two failures follow, in order:
    * `"command": "uvx"` → `ENOENT`, because `uvx` is not on that `PATH`.
    * `"command": "bash", "args": ["-lc", "exec uvx lean-lsp-mcp"]` →
      `-32000`.  `bash` *is* found, but with no `HOME` the login shell cannot
      read `~/.profile`, so `uvx` is still missing, the process exits, and the
      closed connection surfaces as a server error rather than a spawn error.

  `HOME` matters independently of `PATH`: elan resolves its toolchains under
  `$HOME/.elan`, so `lake serve` fails without it even once `uvx` is found.
  The wrapper therefore derives the home directory from the passwd database
  when `HOME` is absent (`getent passwd "$(id -un)"`), exports it, and puts
  both bin directories on `PATH` — no absolute paths, so the committed file
  still works for other users on other machines.

  To reproduce either failure without touching Claude Code, spawn the server
  under `env -i PATH=<default> …` and drive it over stdio; the config is a
  plain JSON object you can read and exec directly.  Note that a login shell
  is *not* used, so `~/.profile` is irrelevant now — but if you ever
  reintroduce one, check it stays silent on stdout, since any chatter there
  corrupts the MCP stdio stream.
* **Remote search rate limits differ sharply per tool** (the server reports
  these itself; the README's blanket "3 req / 30 s" is wrong):
  `lean_leansearch` 90/30 s, `lean_leanfinder` 10/30 s, `lean_state_search`
  6/30 s, `lean_loogle` **3/30 s**.  Only Loogle is genuinely scarce, so
  natural-language search via LeanSearch is nearly free and should be reached
  for early; save Loogle for type-shape queries nothing else answers.  The
  budget is shared across parallel workers.  `lean_local_search` (ripgrep) is
  unlimited and should still be the first move for "does this name exist".
* Each live Lean session holds all of Mathlib (~4-6 GB).  Claude Code runs
  **one** MCP server shared by all subagents, so this costs one `lake serve`,
  not one per worker — but it also means goal queries from parallel workers
  serialize through it.
* Subagents do not see MCP tools automatically — they reach them via tool
  search.  Worker prompts must say explicitly to use them, or they fall back
  to grep-and-recompile.
* Local Loogle (`LEAN_LOOGLE_LOCAL=true`) would remove the rate limit but
  needs ~13 GiB to index and ~7 GiB warm — **not viable on a 14 GB box**
  alongside `lake serve`.  Revisit only on a bigger machine.
* The fast REPL backend (`LEAN_REPL=true`) was deliberately **not** enabled:
  it only speeds up `lean_run_code` and column-less `lean_multi_attempt`,
  costs a second Mathlib-loaded process (~3-4 GB) that competes with the
  parallelism budget, requires a `repl` dependency in `lakefile.toml` pinned
  in lockstep with `lean-toolchain`, and *silently falls back* to LSP when
  that pin drifts.  A matching `v4.34.0-rc1` tag does exist if it is ever
  wanted.
* ⚠ **The committed config is Linux-only in practice** (checked 2026-08-17 on
  Bram's Mac, where the Lean side of the 81IX ruling was done).  Two
  independent blockers there: `uvx` is not installed, and the wrapper's `HOME`
  fallback calls `getent`, which is glibc-only — precisely the branch that
  fires, since the server is spawned without `HOME`.  A fallback that works on
  both systems is `H="${HOME:-$(eval echo ~"$(id -un)")}"`.  For the launcher,
  upstream's canonical route is `uvx lean-lsp-mcp`, but the package is an
  ordinary PyPI wheel exposing a `lean-lsp-mcp` console script, so a stdlib
  venv avoids installing `uv` at all
  (`python3 -m venv DIR; DIR/bin/pip install lean-lsp-mcp==0.29.0`) provided
  the launcher prefers a `lean-lsp-mcp` on `PATH` and falls back to `uvx`.
  Note also that on that machine the server was still "⏸ Pending approval"
  (`claude mcp list`), so **no `mcp__lean*` tools were exposed at all** — which
  is why 81XII was handed off rather than proved blind.  A separate trap on any
  fresh machine: `.lake/build` and the Mathlib cache are git-ignored, so
  `lake build` there compiles Mathlib from source (hours) unless
  `lake exe cache get` is run first — that cache is now warm on the Mac.

### Parallelism

The work parallelises well because proofs don't affect statements: several
workers can prove different files at once, each owning a disjoint set of
files.  What to watch for (all of it bit us at least once):

* Give each worker **exclusive ownership** of its files; everything else is
  read-only to it.  Two workers editing one file will clobber each other.
* Workers see each other's *sources* but each other's **stale oleans** — so a
  helper added elsewhere during the run is not importable.  Either rebuild
  between waves, or accept some duplicated helpers and consolidate after.
* `PROVING-LOG.md` is shared mutable state.  Session 2 solved this by telling
  each worker to write its log to its **own scratch file** and having the main
  session merge afterwards — no contention, and recommended over the session-1
  "append only, re-read first" rule.
* **A worker cannot compile-check a file whose imports another worker is
  editing.**  `lean_diagnostic_messages` and `lean_multi_attempt` both fail with
  "Imports are out of date" until the importee is rebuilt.  In session 2 this
  blocked `Representation.lean` (imports `Basic` and `Positive`) for the entire
  run.  The workaround that works is `lean_run_code` with `import Mathlib` and
  the statements copied into a scratch file; the real fix is to **partition work
  along the import graph**, giving one worker a file and everything it imports,
  or to rebuild between waves.
* Doc comments: workers are told never to edit them (they carry the thesis
  cross-references), so stale "`sorry`-ed" claims accumulate and need a
  separate sweep — that sweep is the one time editing them is correct.
* Lean respects `LEAN_NUM_THREADS`; on a many-core server cap it (e.g. 4-8)
  when running several workers, or the concurrent `lake env lean` invocations
  will thrash.

Rules given to every worker, worth keeping:
* **Never change a statement.**  Park instead: leave the `sorry`, add a line
  to PROVING-LOG.md saying why.  A wrong proof is far worse than a `sorry`.
* Log every place your proof **diverges from the thesis's**, not merely the
  ones you had to repair (see PROVING-LOG.md) — that file is the most valuable
  output of this exercise for the authors.  Four cases: thesis proof wrong;
  thesis proof fine but you used another route; different dependency order;
  and **you never read the thesis proof at all**.  The last is the easiest to
  omit and the most important to state, because it marks a statement that is
  proved but *not* cross-checked.
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

### Resolved in session 2

The **C\*-module inner-product convention** was approved and fixed.  Mathlib's
`CStarModule` is the mirror of the thesis's: the thesis has right 𝒜-modules
with `⟨x, y·b⟩ = ⟨x,y⟩ b`, Mathlib has `⟪x, a•y⟫ = a ⟪x,y⟫`, so
`⟪x,y⟫_Mathlib = ⟨y,x⟩_thesis`.  Two statements had been transcribed without
the swap and were false; both are corrected, with the convention now recorded
in their doc comments:

* **32VI** `chilb_cs` (Cauchy–Schwarz) — corrected *and proved*, one line from
  `CStarModule.inner_mul_inner_swap_le` once the arguments are swapped.
* **33II**.2 `cstar_matrix_gram_nonneg` — corrected to
  `fun i j => inner 𝒜 (x j) (x i)`; still `sorry`, downstream of 33II.1.

Everything else using an 𝒜-valued inner product was checked and is unaffected
(adjointness is star-symmetric; diagonal forms are star-invariant; the B/Dils
files are either already convention-aware or self-consistent).  **Anyone adding
new `CStarModule` statements — especially in B/Dils, which is untouched and
uses it in five files — must apply the swap.**

### Resolved by the author (2026-08-13) — thesis-A rulings, incorporated

Bram ruled on the thesis-A findings below.  Each is **fixed in the tex
sources** (cstar.tex / vn.tex / proc.tex), with the delta from the printed
edition recorded in the errata block at the top of `../asols.tex` (keyed
`parsec-N.M`); solution-text fixes were made in place with no record, since
the solutions were never printed.  **Check that errata block, not the printed
text, when transcribing.**  The Lean statements may be brought in line with
the corrected sources as *authorised* changes; `file:LINE` references in doc
comments may have shifted, so re-locate by point number.

* **23VII.3** — was already covered by the pre-existing erratum 230.70
  (formerly mis-keyed 230.50): point 3 assumes `0 ≤ a ≤ b`.  Fix the Lean
  statement accordingly.
* **72III.1b/1c** — likewise pre-existing erratum 720.30: the `‖ω‖` factors
  are deleted.  Both statements are now provable as sourced.
* **30IV.2** — the spurious `‖ω‖` was already covered by errata 300.40/300.60.
* **16V** `spectrum-non-empty` — now hypothesises `𝒜 ≠ {0}` (erratum 160.50).
* **16VI** — reworded: `spec(a) ⊆ {λ}` iff `a = λ` (erratum 160.60); true in
  `{0}` too, so this form needs no nontriviality split.
* **17VI.3** — the `inf` now runs over `λ ≥ 0`, not `λ ∈ ℝ` (erratum 170.60).
* **22III.5** — point 5 now assumes `𝒜 ≠ {0}` (erratum 220.30); its solution
  now cites 16V for non-emptiness of the spectrum.
* **22VIII** — the state-existence half now assumes `𝒜 ≠ {0}` (erratum
  220.80); the order-separating half is unchanged.
  **The trivial C*-algebra stays admitted globally** — 8II and the categorical
  chapters need it; only these five statements were touched.
* **34aVII** Russo–Dye — "for some natural number `N > 0`" (erratum 341.70).
* **37IX** — the statement gains "non-empty"; the proof now opens "wlog `𝒟`
  has a least element `T₀`", gets boundedness by squeezing, and proves
  self-adjointness of the limit via 25V(1) (errata 370.90, 370.100).
  **37VII is deliberately left unchanged.**
* **38VI.2** — the false "if" direction is **dropped**, with its hint
  (erratum 380.60); state only `x_α → x ⟹` operator-norm convergence.
* **61II** `ncp-ceill` — both displayed inequalities **reversed** (erratum
  610.20), likewise the proof's last line; its sole use site 99VII also had
  three `a`-for-`b` slips, now fixed (erratum 990.70 carries the corrected
  paragraph).
* **68IV.2** `cceil-basic` — positivity added to clauses 1 and 3 (erratum
  680.40); the Lean-side fix of 2026-08-13 is authorised as-is.
* Mechanical main-text fixes: **4VIII** (`V → ℂ`, erratum 40.80); **11XX.1**
  (`ℝ → ℂ`, *addendum* 110.200 — the printed statement was true, just less
  general); **12III**.3 (`z ∈ 𝒜` → `z ∈ ℂ`, folded into erratum 120.30);
  **17III** (`[0,∞]` → `[0,∞)`, erratum 170.30); **19Ia** (missing `⁻¹`,
  erratum 190.20); **23II** (cite `square-commuting-monotone`, erratum
  230.60).
* Solution texts fixed in place (no erratum blocks): 11XV.2, 11XX.2, 16V,
  16VI, 16VII (reference 160.60→160.50, the self-adjointness gap, the `{0}`
  branch), 17VI.6, 20aII, 22III.5, 26II.1 (plus a mis-citation
  `230.70(2)` → `(1)` found on site), 26II.4, 30IV.1.
* **62I** — its proof's citation of `inner-product-basic` for
  `f(a)² ≤ f(a²)` is corrected to `cp-cs` (erratum 620.20).
* Still open: a handful of minor solution nits listed in PROVING-LOG.

### Resolved by the author (2026-08-17) — thesis-A rulings, incorporated

Bram is working through the thesis-A rows of ERRATA.md.  Each ruling below is
already applied to the sources, and its row has been **deleted** from
ERRATA.md, per that file's own convention.

* **11XV.3** — the defect is in the *solution* (`asols.tex`, keyed
  `parsec-110.150`), not in the printed hint, so there is **no erratum
  block**.  Repaired by assuming `n > 1` ("For~$n=1$ this is trivial, so we
  may (and do) assume that~$n>1$"), under which the printed "`ζ^{2k+1} ∉ ℝ`
  when `k ≠ ½(n−1)`" is exactly right: over `k = 1,…,n` the only real value
  occurs at `2k+1 = n`, the next odd multiple `3n` exceeding `2n+1`.  Only
  `n = 1` broke it, where `2k+1 = 3 = 3n` does fit the range.  A line
  identifying that factor — `b − ζ^{2k+1} = b − ζⁿ = b + 1` — was added, which
  the closing sentence had been assuming tacitly.  **No Lean-side change is
  authorised or needed**: the statement of 11XV.3 is untouched.
* **79VI.4** `pseudoinverse-basic-2` — repaired by **compressing the
  conclusion**, not by adding a hypothesis: point 4 now reads
  `⌈b⌉c^∼1⌈b⌉ ≤ b^∼1` (erratum `parsec-790.60`).  ERRATA.md proposed the
  hypothesis `⌈b⌉ = ⌈c⌉` instead, which is the special case of this, and which
  would have cost the parenthetical.  The parenthetical **stands**: in this
  form the non-commuting case is the standard C\*-argument.  Write
  `c^∼½ := (c^∼1)^½`, `b^∼½ := (b^∼1)^½`, `p := ⌈b⌉`.  From `b ≤ c`,
  `‖c^∼½b^½‖² = ‖c^∼½ b c^∼½‖ ≤ ‖c^∼½ c c^∼½‖ = ‖⌈c⌉‖ ≤ 1`, so
  `b^½c^∼1b^½ = (c^∼½b^½)^*(c^∼½b^½)` is positive of norm `≤ 1` and equal to
  its own compression by `p`, hence `b^½c^∼1b^½ ≤ p`.  Conjugating by `b^∼½`
  — using `b^∼½b^½ = p` and `b^∼½b^∼½ = b^∼1`, both from 79VI.1 — gives
  `pc^∼1p ≤ b^∼1`.  Commutativity is used nowhere.
  * **Lean side, authorised**: restate `pseudoinverse_basic_2'_4`
    (`A/VN/Division.lean`) with conclusion `ceil b * pinv c * ceil b ≤ pinv b`
    and prove it by the argument above, closing its `sorry`.  `hcomm` is not
    needed by that argument; keep it only to match the printed statement.  The
    refutation `pseudoinverse_basic_2'_4_is_false` and
    `pseudoinverse_basic_2'_4_forces_eq_one` **stay** — they are what the
    erratum's delta records — but their doc comments should say they refute the
    *printed* conclusion, not the current one.
* **81IX** `div-usc` — the false half is **weakened, not dropped**.  The Lemma
  now states that `a ↦ a/b` is *both* ultrastrongly and ultraweakly continuous,
  and that `a ↦ c∖a/b` is **ultraweakly** continuous (erratum `parsec-810.90`).
  Note the first map's ultraweak continuity is not a consequence of its
  ultrastrong continuity — the two topologies are complementary (42IV) — but
  comes from the printed uniform-limit argument, the partial sums being
  ultraweakly continuous too and the uniformity transferring by 43I(1).
  The repaired proof is in the thesis's own idiom rather than the compactness
  route `div_uwc` takes: `c∖x = (x*/c*)*` (81II(5), now labelled
  `division-basic`) together with ultraweak — as against ultrastrong (43II.4) —
  continuity of `a ↦ a*`.  The counterexample to the printed second half is now
  **printed thesis content**, as the new sub-point **81XII**
  (`c = ∑ₙ n⁻¹|n⟩⟨n|`, `dₙ = |n⟩⟨0|`, `b = 1`).
  * **81VII** `div-approx` — its parenthetical "(and uniformly so)" is
    **deleted** (erratum `parsec-810.70`).  It was false for the two-sided map
    (uniformity would make 81IX's second map ultrastrongly continuous) and had
    exactly one consumer in either thesis, which did not need it.
  * **96VI** — its erratum is **withdrawn**, not applied: the thesis's own
    route survives the repair, so the bipositivity rewrite is not needed (the
    Lean proof of `canonical_filter` stays as it is, now one of two valid
    routes).  proc.tex instead reads "ultraweakly" in the normality paragraph
    and cites **44XV** `p-uwcont` for `f` in place of 45II `cp-uscont`, and
    "pointwise" for "uniform" in the complete-positivity step (erratum
    `parsec-960.60`).  Consequence worth keeping: normality of `g` now needs
    only that `f` is positive and normal, so complete positivity of `f` is used
    exactly once, in the last paragraph — and the standard filter therefore also
    satisfies the np-analogue of 96I's universal property.
  * **Lean side, done**: `div_uwc` (`A/VN/Division.lean`) now carries the 81IX
    identity, and `div_usc` — the printed statement, false in its second
    conjunct — is **retired**, its `sorry` with it (A/VN 128 → 127); its
    counterexample survives as the section note above `div_uwc`, and
    `div_usc_ball` is documented as the corrected first clause.  `div_approx`
    is untouched: it never claimed uniformity.  Verified with `lake build`
    (8718 jobs, no errors).

#### Handed to Bas: formalize 81XII

81XII is printed thesis content as of this ruling, so its counterexample should
be machine-checked; **this was scoped but deliberately not attempted** (see the
tooling note at the end).  Everything below was checked against the tree on
2026-08-17.

*Statement*, to sit beside `div_uwc` in `A/VN/Division.lean`, suggested name
`div_usc_2_is_false`: in `A = ℓ² →L[ℂ] ℓ²` with `b = 1` there are `c ≥ 0` and
`dₙ` with `c * dₙ → 0` in norm — hence ultrastrongly — while
`ldiv c (c * dₙ) = dₙ` does not converge ultrastrongly to `0 = ldiv c 0`;
conclude `¬ ContinuousOn` for `fun a => ldiv c (div a b)` on
`{a | ∃ d, ‖d‖ ≤ 1 ∧ a = c * d * b}` in the `ultrastrong` topology.

*Witness*: vn.tex prints `c = ∑_{n>0} n⁻¹|n⟩⟨n|`, but the constants are not
load-bearing — any positive injective diagonal with eigenvalues tending to `0`
refutes it.  In Lean prefer `c := ∑' n, ((1:ℝ)/2^n) • ketbraNat n n`, which is
norm-summable, so the series converges with no bespoke boundedness proof;
`dₙ := ketbraNat n 0`.

*What the tree already has* (all public): `ketbraNat` (`A/VN/Basic.lean` — note
its `ℓ²` notation is `local`), `vn_counterexamples_1` for the star and product
rules, which is what gives `star dₙ * dₙ = |0⟩⟨0|` **independently of `n`** —
the crux of the whole example; `ketbra_norm` (`A/CStar/Basic.lean`);
`vectorNP` for the vector state at `lp.single 2 0 1`; `usTendsto_iff`;
`ldiv`/`div`/`suppProj` with `ldiv_eq` and `division_basic_2`
(`b∖(b*a) = ⌈b⌋a`); and `ceil_mono`, `ceil_smul`, `ceil_of_isStarProjection`,
`ceil_basic_5` in `A/VN/Projections.lean`.

*The one real step* is `⌈c⌋ * dₙ = dₙ`, which is what turns `ldiv c (c * dₙ)`
into `dₙ`.  Route: `2⁻ⁿ|n⟩⟨n| ≤ c` (partial sums increase and the positive cone
is closed), then `ceil_mono` with `ceil_smul` and `ceil_of_isStarProjection`
gives `|n⟩⟨n| ≤ ⌈c⌋`, and `dₙ = |n⟩⟨n| * dₙ`.  Everything after that is
mechanical: continuity at `0` within the set would force
`omegaNorm ω dₙ → 0`, against `omegaNorm ω dₙ = 1`.

*Two frictions worth knowing before starting*: neither Mathlib nor the tree has
a diagonal operator on `lp` (hence the `tsum` of ketbras, and a `tsum`-apply
step for `c eₙ = 2⁻ⁿ eₙ`), and most of the `ℓ²` helpers in `A/VN/Basic.lean`
are `private` — so either re-derive the two or three needed facts locally, or
de-privatise them and accept the A/VN rebuild.

### Resolved by the author (2026-08-19) — thesis-A ruling, incorporated

* **104III** `centrally-similar-basic` — the false parts are repaired by
  **faithfulness**, not by equal central carriers.  Points 2a, 3 and 4 now
  assume `⌈p⌉ = ⌈q⌉ = 1`; point 5 assumes `⌈p⌉ = ⌈q⌉` (erratum
  `parsec-1040.30`).  The 2026-08-16 proposal `⌈⌈p⌉⌉ = ⌈⌈q⌉⌉` is **dropped**:
  it cannot repair .4, whose refuting witness `p = q = m = diag(1,0)` in
  `B(ℂ²)` satisfies every hypothesis reflexive in the pair.  Parts 1 and 2 are
  unchanged — both are true as printed, and part 2 is what forces `⌈p⌉ = ⌈q⌉`
  in the first place.  The repair costs the thesis nothing: 104VII, the only
  consumer, states `⌈p⌉ = ⌈q⌉ = 1` and cites 104III at proc.tex:1594 (part 5)
  and proc.tex:1624 (part 2a, first claim), both inside that setting.
  * **Lean side, authorised**: restate `centrally_similar_basic_{2a,3,4,5}`
    (`A/Proc/Measurement.lean`) with those hypotheses and prove them.  For .4
    the first two `iff`s are already proved as
    `centrally_similar_basic_4_faithful`.  For .2a the arguments are short:
    for the second claim take `c = 1`, `d = p`; for the first `c = 1`,
    `d = p/q`, whose carrier is `1` because `⌈p⌉ = ⌈(p/q)q⌉ ≤ ⌈p/q⌉`.  For .3
    see the argument in QUESTIONS A7 — it is on paper only.
  * The refutations of the printed forms — `centrally_similar_basic_*_counterexample`
    and the `_cceil_` ones — **stay**: they are what the erratum's delta
    records.  Their doc comments should say they refute the *printed*
    statements, not the current ones.
  * **The `p ∧ q` question is untouched by this ruling** and still open
    (QUESTIONS A7).  Restating the carrier hypotheses is authorised
    regardless; leave the `p ∧ q` clauses of .3, .4's third `iff` and .5's
    hint as they are until that is decided.

### Resolved by the author (2026-08-22) — thesis-A rulings, incorporated

* **26II** `commutative-cstar-basic` / `parsec-260.20` — the orphaned solution
  item.  The printed exercise has four points and a five-point solution, whose
  fifth proves an unasked bonus, `|a+b| ≤ |a|+|b|`.  That bonus is **promoted
  to point 5 of the exercise**, in the sharper form the solution's own
  computation already gives: `|a+b| ∨ |a−b| = |a|+|b|`.  The
  commuting-subalgebra point added on 2026-08-19 becomes **point 6** and gains
  a solution of its own (the least C\*-subalgebra containing `a` and `b` is the
  norm closure of the span of the `aⁿbᵐ`; it is commutative because what
  commutes with the elements of a sequence commutes with its limit).  No
  erratum for either: a reader of the printed edition loses nothing by not
  having them.  The solution to `parsec-270.100` still cites "item 5" and is
  correct as it stands; `proc.tex`'s 104III now cites
  `commutative-cstar-basic`(6).
  * **Lean side, authorised**: `commutative_cstar_basic_5`
    (`A/CStar/Positive.lean:6772`) is the thesis's **point 6** — rename it
    `_6` and re-tag its doc comment, which frees `26II.5` for the triangle
    inequality.  The sharper equality form is the one to state.

* **20II.1** — **not an erratum; row deleted from ERRATA.md.**  The row read
  "proof needs `f a` self-adjoint, never stated".  It *is* stated, ten parsecs
  earlier: **10V**, the proof of **10IV** `cstar-p-implies-i`
  (`cstar.tex:1344`), shows that a positive map sends self-adjoint elements to
  self-adjoint ones, by exactly the `f(a) = f(‖a‖) − f(‖a‖−a)` argument; and
  10IV's own conclusion gives it in one step, `f(a)* = f(a*) = f(a)`.  It is
  not even a gap in 20III's chain: `≤` is defined (**9IV**
  `cstar-positive-def`) as "the difference is positive", and positivity is
  defined only for self-adjoint elements, so `−‖a‖f(1) ≤ f(a)`, which the
  proof derives from positivity of `f`, already carries it.  The row's
  proposed fix `a = a⁺ − a⁻` is unusable here anyway: the positive and
  negative parts arrive at parsec 240, forty parsecs after 20II.
  * **Lean side** (a simplification, not required): `weak_russo_dye_1`'s
    eight-line `hfsa` block reconstructs 10V inline.  `cstar_p_implies_i`
    (`A/CStar/Basic.lean:1736`) is already in the tree and yields
    `IsSelfAdjoint (f a)` from `ha` in one line.
  * Found while checking this and **fixed in `cstar.tex`**: 10V's
    "`f(a) = f(‖a‖) − f(‖a‖−a)` being positive is self adjoint" said that
    `f(a)` is positive, which it need not be.  It now reads "… are positive,
    thus self adjoint, as is thus `f(a) = f(‖a‖) − f(‖a‖−a)`".  Ruled **not
    worth an erratum**: the printed intent is unmistakable.

* **32I** — **not an erratum; row deleted from ERRATA.md.**  The row asked the
  thesis to state definiteness in both arguments, because module-linearity of
  an adjointable `T` uses the first and uniqueness of its adjoint the second.
  Each is one line from the definiteness 32I already states (`cstar.tex:5088`):
  put the difference into both slots.  Both elements lie in the module whose
  definiteness is invoked, and `cstar.tex:5101` makes X and Y both pre-Hilbert,
  so both are available — this *is* the derivation 32I calls "not difficult to
  see", and it is what `eq_of_inner_left_eq`/`eq_of_inner_right_eq`
  (`A/CStar/Matrices.lean:60`, `:68`) do in three lines each.  The 2026-08-20
  audit rates all four 32I rows `ok`.
  * The row came from a **note**, `PROVING-LOG.md:2232` ("The thesis states
    definiteness once; both directions get used"), promoted to a defect with a
    "fix" it never claimed.  A note that one axiom serves two purposes is not
    a defect; ERRATA.md's scope line is "only defects in the theses".

* **33I.2** — **the redundancy is now in the printed statement's own text;
  row deleted from ERRATA.md.**  The row said the surjectivity half never uses
  the adjointability hypothesis.  True, and it uses no boundedness either:
  `A_mn := (Te_n)_m` and `v = ∑ₙ eₙvₙ` need only additivity and 𝒜-linearity.
  The printed *solution* already knew — `parsec-330.10` opens its surjectivity
  paragraph "let `T : 𝒜^N → 𝒜^M` be **a module map**".  So nothing was wrong;
  what the point lacked was the remark.  Point 2 now brackets the hypotheses
  and adds: "(Yes, all module maps from `𝒜^N` to `𝒜^M` are bounded and
  adjointable.)"  No addendum: the printed exercise is complete and correct as
  it stands, and a reader of it loses nothing.
  * **Lean side, authorised**: `cstar_matrices_2`'s third clause
    (`A/CStar/Matrices.lean:906`) may drop both the `→L[ℂ]` bundling and the
    `ModuleAdjointable` hypothesis — the latter is already discarded in the
    proof (`fun T hT _ => ?_`) — and take a plain additive 𝒜-linear map.  The
    new remark is worth a statement of its own: every module map
    `𝒜^N → 𝒜^M` is bounded and adjointable.  Note the contrast with **32IV**,
    where a bounded module map `J → C[0,1]` has no adjoint; freeness is what
    makes it automatic here.

* **32XV.3** — **the diagnosis is right and the repair was already there; row
  deleted from ERRATA.md.**  Part 3 indeed does not follow from order
  separation — **21VII** `order-separating-norm` is about *pu*-maps, and these
  functionals are only subunital.  But the printed solution `parsec-320.150`
  says so itself ("We cannot simply apply `parsec-210.70`, because the maps
  `⟨x,(·)x⟩` are not all unital") and then gives the direct argument the row
  asks for, in a stronger form than the row's: with `T_±^ε` (`ε > 0` dyadic)
  in place of `√(T_±)`, `T_∓T_±^ε = 0` gives
  `⟨T_±^ε y, T T_±^ε y⟩ = ±⟨√(T_±)T_±^ε y, √(T_±)T_±^ε y⟩`, whose supremum over
  the unit ball is `‖√(T_±)T_±^ε‖² = ‖T_±‖^{1+2ε} → ‖T_±‖`; then **24II**.4.
  Those vectors are not meant to exhaust the ball — they lie in it (whence the
  wlog `‖T‖ ≤ 1`), so their supremum is a lower bound for the one in question,
  and it already reaches `‖T_±‖` in the limit.  A single `ε` does *not* do:
  `‖T_±‖^{1+2ε} < ‖T_±‖`.  (Our `chilb_vector_states_3` instead fixes
  `ε = ½` and normalises by `(‖s‖‖x‖)⁻¹`, reaching `‖T_±‖² ≤ M‖T_±‖` with no
  limit — a legitimate variant, not a repair of anything.)
  * **Fixed in the exercise**: parts 1 and 2 keep the "Conclude that"; part 3
    now sits behind its own "Moreover, show that", so it no longer reads as a
    corollary of order separation.  No erratum, and no hint: the structural
    break is the whole of the delta.
  * A typo in the solution, fixed in place: "the maps `⟨x,(·)x⟩` not all
    unital" was missing its "are".

* **34VI.1 / QUESTIONS A2** — `parsec-340.60`'s `\TODO{}` is **a deliberate
  marker**, not a defect: it is how the author records that a solution is
  still to be written, and he will write it himself.  Row deleted from
  ERRATA.md.  Nothing is owed by the formalization here, and the missing
  solution is not a reason to treat `cstar_product_4` as suspect — it simply
  has no author's argument to cross-check against yet.  (The same goes for any
  other `\TODO{}` slot: do not read it as an erratum.)

* **34XVI** — **the row is factually wrong; deleted from ERRATA.md.**  It said
  the thesis derives `cp-russo-dye` from Russo–Dye (**34aVIII**), a later
  point.  The printed proof, 34XVII, cites **20II** `weak-russo-dye` and
  **34XIV** `cp-cs`, both earlier; `russo-dye` does not appear in it at all.
  `weak-russo-dye` was read as Russo–Dye.
  * **Lean side**: the consequence is the opposite of what
    `PROVING-LOG.md:2213` records — `cp_russo_dye` does not take a better
    dependency order than the thesis, it takes *the thesis's own*.  The log
    entry's "a genuine reduction that avoids Russo–Dye entirely, and arguably
    the better dependency order" should be struck.  (The audit had already
    softened the proof classification to `mild`; the residue is the
    `weaker` *statement*, `‖f(a)‖ ≤ ‖f(1)‖‖a‖` where 34XVI asserts the
    equality — that part of the audit row stands, and `cp_russo_dye_norm`
    addresses it.)

* **39VII** `bh-np-lemma` — **accepted; statement repaired, erratum
  `parsec-390.70`.**  The row is right that the displayed sum, read over the
  index set `ℰ×ℰ` — the sense the thesis uses elsewhere, and the sense a
  doubly-indexed `∑` asks for — need not converge.  The counterexample checks
  out: `A` block diagonal with `N_k×N_k` DFT blocks, `N_k = k⁸`, `x` constant
  `k^{-5}` on block `k`, `ω = ⟨x,(·)x⟩`; then `‖A‖ = 1`,
  `‖x‖² = ∑ₖ k^{-2} < ∞`, and block `k` contributes
  `N_k²·N_k^{-1/2}·k^{-10} = k²` to the sum of absolute values.
  * The statement now reads `ω(A) = lim_{ℱ ⊆ ℰ finite} ∑_{e,e'∈ℱ} …`, which is
    what 39VIII proves (`ω(A − PAP) → 0` with `P = ∑_{e∈ℱ}|e⟩⟨e|`) and all
    39X needs.  **The trap is that the squares `ℱ×ℱ` are cofinal among the
    finite subsets of `ℰ×ℰ`** — convergence along a cofinal subfamily is not
    convergence of the net, and the implication runs one way only.
  * A third reading, the *iterated* sum `∑_e(∑_{e'} …)`, does hold — but it is
    not what 39VIII gives, and deriving it in general goes through
    `ω = ∑ₙ⟨xₙ,(·)xₙ⟩`, i.e. through 39IX, which rests on 39VII.  So it is not
    available as a reading of this Lemma.
  * Also fixed while there: the display ended in a full stop with the sentence
    continuing "for every normal p-map …"; it is now a comma.

* **15I, the proof** — **the triangulation is the intended argument and is
  elementary; row deleted from ERRATA.md.**  Ruled by the author: that
  **14VIII** holds not only for a triangle but for a regular polygon is meant
  to be a trivial consequence of Goursat — inside the polygon there is a
  triangle `T` with `z₀ ∈ in(T)`, and `∫_T` is promoted to the integral over
  the polygon (same orientation) by adding integrals of *holomorphic*
  functions over the triangles filling the region between them, each zero by
  **14IV** `goursat`.  So 15IV's "in the obvious manner" stands as printed.
  * What was genuinely missing is that 15II cites `invint` for a sum over the
    N-gon's edges while **14VIII.4 is stated for a triangle**.  `invint` now
    has a **fifth item** carrying the polygon case (with the vertices numbered
    counterclockwise, so the value is `1`), the hint being the promotion
    above; 15II cites `\sref{invint}(5)`; and 14IX now reads "along a
    triangle~`T` (or regular polygon)".  No erratum — nothing printed becomes
    wrong.
  * **Lean side — please reword two doc comments.**  The `A/CStar/Positive`
    module header says 15I's winding number is one "which the thesis obtains
    from a triangulation it asserts without constructing", and
    `cauchy_formula`'s proof comment calls it "the thesis's route, with its
    asserted triangulation replaced".  Both read as *gap repaired*; the
    correct record is *route divergence*, and a larger one than
    `polygon_winding` alone.  `cauchy_formula` restructures the whole proof:
    `dslope f z₀` — differentiable on all of `U` — removes 15III's
    `δ`/`‖f'(z₀)‖+37` estimate and with it the small triangle `T` around `z₀`;
    Goursat is then applied to the **fan** `(w₀, wₙ, wₙ₊₁)`, where the interior
    edges cancel immediately, so the region between a triangle and the N-gon
    never arises; and the remaining scalar is `polygon_winding`, which proves
    the polygon case outright rather than promoting 14VIII.4 to it.  Two
    consequences worth recording: the tree uses neither **14VIII.4** nor the
    new **14VIII.5** here, and `polygon_winding` needs only *continuity* of
    `f` at `z₀`, not holomorphy.

* **14VIII.2** — accepted; erratum `parsec-140.80`.  The first line of the
  displayed computation had the dummy variable as its upper limit,
  `i∫₀^t (a−it)/(a²+t²)dt`; it now reads `∫₀^b`, as the next two lines already
  did.  Row deleted.

* **15I, the statement** — accepted; erratum `parsec-150.10`.  The vertices
  were printed `wₙ := c + r cos(2π/n) + i r sin(2π/n)`, with the dummy `n`
  where `2πn/N` is meant — so `N` did not occur in the formula at all and `w₀`
  was undefined.  Corrected to `c + r cos(2πn/N) + i r sin(2πn/N)`, which is
  what the proof uses and what `cauchy_formula` states.  Row deleted.

### Still open

**0. RESOLVED — the formalization validates the thesis's own bootstrapping.**
The author decided this should be the goal, and it has been implemented for
A/CStar.  **The bootstrapping now holds from parsec 110 upward**, with exactly
two imported facts at the base: `IsSelfAdjoint.spectralRadius_eq_nnnorm` (16III)
and `IsSelfAdjoint.mem_spectrum_eq_re` (11XV.1), both taken from Mathlib only
because the thesis's own route to them — the 𝒜-valued complex-analysis block at
parsecs **120–150** — is still `sorry`.  Both sit below the CFC in Mathlib's
import graph, so neither smuggles in later thesis content.

Above that line, **25I** is a theorem rather than an assumption, **19III** and
**24IV** are theorems rather than artefacts of Lean's star order, **23II** (the
thesis's hand-built square root) is proved, and the continuous functional
calculus appears nowhere below parsec 230.  See PROVING-LOG.md for the
`ThesisPos` development that achieved it.

**Closing parsecs 120–150 would remove the last two imports and make the chapter
self-supporting from the ground up — the single highest-value target in
A/CStar.**  It needs Banach-space-valued contour integration (Goursat, Cauchy,
Taylor, winding numbers) bridged to Mathlib.

Keep the rule that produced this, for every other chapter: *a proof of a
statement at parsec P may use only what the thesis has at or before P; the test
is mathematical content, not provenance.*  The original diagnosis, retained
because the failure modes recur:

* **What `0 ≤ a` means.**  In Lean it is Mathlib's star order (`a = b*b`); in
  the thesis before **25I** it is "`‖a − t‖ ≤ t` for some `t`", and their
  equivalence *is* 25I.  So statements before 25I phrased with `0 ≤ a` already
  presuppose 25I.
* **CFC before Gelfand.**  Everything from parsec 230 uses the continuous
  functional calculus, which the thesis obtains only at parsecs 270–280 — it
  hand-builds `√` at **23II** precisely to avoid this.  Sharpest instance:
  **23VII**.0'' is closed with `CFC.sqrt_le_sqrt`, i.e. thesis **28III**, five
  parsecs later and itself resting on 23VII.  Also **27XV**, closed via Gelfand
  through maximal ring ideals — the route **16VIII** explicitly rejects.

Nothing here is unsound: Mathlib proves all of it independently.  But if the
goal is to check that the *thesis's* development stands up, these proofs do not
do that, and several would need rewriting along the author's elementary routes
(the audit notes that for 17V, 17VI.6 and 23VII.0'' the author's route is
already available in the file).  If the goal is only that the statements are
true, they are fine as they are.  **This needs the author's call**, because it
determines a lot of rework.

Places where the honest fix is to change one of *our* statements, not done
because the standing rule is never to change a statement without approval:

1. ~~**`orderIntervalEffectModule`**~~ — **RESOLVED**, and like 221IV.1 it was a
   **transcription error on our side**, not a defect needing approval.  It is
   now fixed and fully proved (all five fields, axiom-clean).  The diagnosis was
   right — the order was related to `+` but never to the scalar action — but the
   conclusion "needs a hypothesis the thesis doesn't have" was wrong: the source
   (eff.tex:737) says "**if `V` is an ordered real vector space** with order unit
   `u`", and *ordered real vector space* already means the positive cone is
   closed under nonnegative scalars.  Our `[PartialOrder V] [IsOrderedAddMonoid V]`
   captured only the additive half.  Adding `[PosSMulMono ℝ V] [SMulPosMono ℝ V]`
   — the two monotonicity properties that the cone condition yields — makes all
   five fields go through directly.

   ⚠️ **Companion gap, still open**: `effectModule_unitInterval_representation`
   (the Gudder representation theorem in the same Examples point) *produces*
   `[PartialOrder V] [IsOrderedAddMonoid V]` and `0 ≤ u`, so it too omits the
   scalar compatibility, and it asks only for `0 ≤ u` where the source says `u`
   is an **order unit**.  As stated it therefore claims strictly *less* than the
   thesis does — easier to prove, but not the theorem.  Strengthening it needs an
   `OrderUnit` predicate that does not exist in the file yet, so it is left as a
   decision rather than a silent change.
2. ~~**221IV.1**~~ — **RESOLVED.**  This was a **transcription error on our
   side**, now fixed and proved.  Our uniqueness clause read
   `∀ α', h₁ ≫ α' = h₂ → α' = α`, dropping the second condition; the source
   (eff.tex:6837) says "there is a unique isomorphism `α` with `α ∘ h₁ = h₂`
   **and** `ϱ₂ ∘ α = ϱ₁`".  Adding the missing `α' ≫ ϱ₂ = ϱ₁` hypothesis makes
   it provable directly from the universal property, by the thesis's own
   argument (`σ₁ ≫ σ₂` and `𝟙` both mediate `(P,ϱ₁,h₁)` to itself).
   *Note for future reference*: HANDOFF previously cited `dils.tex:1176` for
   this, which is `paschke-unique-up-to-iso` — a lemma about **Paschke**
   dilations of ncp-maps between von Neumann algebras, a different setting from
   the abstract effectus proposition.  Checking the wrong text is what let the
   mis-transcription be recorded as a "statement too strong" decision instead of
   a bug.  Always confirm the doc comment's own `file:LINE`.
3. **[RESOLVED 2026-08-13 — see "Resolved by the author" above: five local
   fixes; `{0}` stays admitted globally.]**
   **The trivial C\*-algebra `{0}`** — the largest cluster, and the one worth
   deciding *globally* rather than statement by statement.  Mathlib's
   `CStarAlgebra` does not extend `Nontrivial`, but the thesis explicitly
   admits `{0}` (8II), where every element is a unit and `spec(a) = ∅`.  False
   as stated there: **16V** `spectrum_nonempty`, **16VI**
   `spectrum_eq_singleton_iff` (← direction), **22III**.5
   `order_ideal_basic_5`.  Surviving only by accident, with Lean proofs forced
   into a `subsingleton_or_nontrivial` split the thesis proofs do not have:
   **16VII** `gelfand_mazur`, **17VI**.3b.  Note the thesis's *own* solution to
   22III.5 (asols.tex:2112) extracts a convergent subsequence from `spec(a)`,
   silently assuming it non-empty — the same missing hypothesis.
   *Decide once*: add `[Nontrivial 𝒜]` where needed, or exclude the trivial
   algebra globally.
4. **[RESOLVED 2026-08-13 — erratum 230.70 was already this; incorporated.]**
   **23VII**.3 `sqrt_3` (A/CStar/Positive.lean, cstar.tex:3663) — "if
   `a,b ∈ sa(𝒜)` commute and `a ≤ b` then `a² ≤ b²`" is false: in `𝒜 = ℂ`,
   `a = -2 ≤ 1 = b` but `4 ≰ 1`.  Needs `0 ≤ a` — which the immediately
   following item 4 already assumes, so this looks like a slip rather than a
   real gap.  With it the proof is `b² − a² = b(b−a) + (b−a)a ≥ 0`.
5. **[RESOLVED 2026-08-13 — the thesis now says `N > 0`; erratum 341.70.]**
   **34aVII** `russo_dye` (A/CStar/Matrices.lean, cstar.tex:5842) — false at
   `N = 0` purely because Lean defines `2/(0:ℝ) = 0`, making the hypothesis
   read `‖a‖ < 1` and the conclusion `a = 0`.  The thesis says "for some
   natural number `N`" and means `N ≥ 1`.  Needs `N ≠ 0`; for `N ≥ 1` it is
   immediate from the proved `sum_of_unitaries_3`.
6. **[RESOLVED 2026-08-13 — erratum 720.30 was already this; incorporated.]**
   **72III**.1b and .1c (A/VN/Completeness.lean, vn.tex:3850) — **false as
   stated**: the `‖ω‖` factor in `|ω(a*bc)| ≤ ‖ω‖‖a‖_ω‖b‖‖c‖_ω` breaks
   homogeneity, since `‖a‖_ω = ω(a*a)^½` is unnormalised and `ω ↦ tω` scales the
   two sides by `t` and `t²`.  Counterexample `𝒜 = ℂ`, `ω = t·id`, `t ∈ (0,1)`,
   `a = b = c = 1`: `t ≤ t²`.  **Delete the `‖ω‖`** and both are provable as
   intended.  Note this is the same slip as **30IV**.2, where an extra `‖ω‖` was
   also spurious — worth sweeping every `‖·‖_ω` estimate in both theses.

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
