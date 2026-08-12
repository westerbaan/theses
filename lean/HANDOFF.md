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

**Session 2 result: 947 → 865 code `sorry`s (82 proved).  All of A/CStar was
worked; every other chapter is untouched.  `A/CStar/Basic.lean` is complete.**

| chapter | file | after s1 | now |
|---|---|---|---|
| **A/CStar** | | **170** | **88** |
| | Basic.lean | 11 | **0 — complete** |
| | Positive.lean | 63 | 40 |
| | Matrices.lean | 55 | 20 |
| | TowardsVN.lean | 27 | 15 |
| | Representation.lean | 17 | 13 |
| B/Eff | (8 files) | 129 | 129 — untouched |
| A/VN | (5 files) | 276 | 276 — untouched |
| A/Proc | (4 files) | 233 | 233 — untouched |
| B/Dils | (7 files) | 139 | 139 — untouched |

`lake build` succeeds (8738 jobs, exit 0); `sorry` + style-linter warnings only.

Session 2 was run as three parallel workers (Positive / Matrices /
TowardsVN+Representation) plus the main session on Basic.lean, all using the
Lean MCP for goal states.  That worked well; see "Parallelism" below for the
one thing that bit us (a worker could not compile-check `Representation.lean`
for the whole run because its imports were being edited concurrently, and had
to develop against Mathlib in a scratch file — its proofs were confirmed only
by the post-run rebuild).

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

The point of this exercise, beyond the Lean files, is
[PROVING-LOG.md](PROVING-LOG.md): **~25 errata** in the theses' own proofs,
found by trying to transcribe them.  Session 2 added, from A/CStar: **23VII.3**
false as stated (needs `0 ≤ a`); **34aVII** Russo–Dye false at `N = 0`;
**37IX** does not follow from **37VII** (bounded-above ≠ norm-bounded for a
directed set); **38VI.2** false in the `←` direction; three more statements
false for the trivial C\*-algebra; and independent confirmation that the `‖ω‖`
in **30IV.2** is spurious.  See "Open decisions" for the ones needing your
ruling.  The substantive session-1 findings:

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

Per `sorry`: **(a)** look for the Mathlib lemma first — many statements close
in one line; **(b)** otherwise read the thesis's own proof — in the `.tex`,
nearly every statement point is immediately followed by a `{Proof}` point,
and each Lean doc comment gives `file:LINE`; **(c)** exercise solutions are in
`../asols.tex` / `../bsols.tex`, keyed by the *same* LaTeX label the doc
comment carries: `grep -n 'solution}{exc-subbase}' ../bsols.tex`.

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

### Still open

Places where the honest fix is to change one of *our* statements, not done
because the standing rule is never to change a statement without approval:

1. **`orderIntervalEffectModule`** (B/Eff/EffectAlgebras.lean) — false as
   stated: the hypotheses relate the order of `V` to `+` but never to the
   scalar action, so even the data field `r • v ∈ [0,u]` fails (order `ℝ` by
   the cone of a ℚ-linear functional).  Needs `PosSMulMono ℝ V` added.
2. **221IV.1** (B/Eff/Dagger.lean) — our statement asks the mediating iso to
   be unique among all `α'` with `h₁ ∘ α' = h₂`, but the universal property
   (and dils.tex:1176) only gives uniqueness among those that also satisfy
   `ϱ₂ ∘ α' = ϱ₁`.  As stated it is too strong.  Not a thesis error.
3. **The trivial C\*-algebra `{0}`** — the largest cluster, and the one worth
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
4. **23VII**.3 `sqrt_3` (A/CStar/Positive.lean, cstar.tex:3663) — "if
   `a,b ∈ sa(𝒜)` commute and `a ≤ b` then `a² ≤ b²`" is false: in `𝒜 = ℂ`,
   `a = -2 ≤ 1 = b` but `4 ≰ 1`.  Needs `0 ≤ a` — which the immediately
   following item 4 already assumes, so this looks like a slip rather than a
   real gap.  With it the proof is `b² − a² = b(b−a) + (b−a)a ≥ 0`.
5. **34aVII** `russo_dye` (A/CStar/Matrices.lean, cstar.tex:5842) — false at
   `N = 0` purely because Lean defines `2/(0:ℝ) = 0`, making the hypothesis
   read `‖a‖ < 1` and the conclusion `a = 0`.  The thesis says "for some
   natural number `N`" and means `N ≥ 1`.  Needs `N ≠ 0`; for `N ≥ 1` it is
   immediate from the proved `sum_of_unitaries_3`.

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
