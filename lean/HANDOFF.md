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
  **47 thesis-A and 23 thesis-B** entries (a few cover several points each).
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

### Tooling: the Lean MCP server (installed)

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
