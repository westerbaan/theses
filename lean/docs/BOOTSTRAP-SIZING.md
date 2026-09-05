# Sizing: removing the last two Mathlib imports from `A/CStar`

Sizing only — no compiles were run, nothing was edited.  Sources re-read
2026-09-05: `Theses/A/CStar/{Basic,Positive,Representation}.lean`,
`docs/audit/acstar-{basic,positive}.csv`, `cstar.tex` 1714–2600,
`PROVING-LOG.md`, `HANDOFF.md`, `docs/DECISIONS.md`.

## 0. Headline: the target named in DECISIONS §2.2 is already built

`DECISIONS.md` §2.2, `HANDOFF.md` "Still open" item 0 and `PROVING-LOG.md`
"Where the bootstrapping now stands" all say the two Mathlib facts are imported
"because the thesis's own route to them — the 𝒜-valued complex-analysis block at
parsecs **120–150** — is still `sorry`".  **That is stale.**  Session 74
(`PROVING-LOG.md:17456`) closed 15I `cauchy_formula` and 15V `taylor`, and the
block is complete and `#print axioms`-clean:

| parsec | `Positive.lean` lines | count | content |
|---|---|---|---|
| 120 | 39–91 | 53 | 𝒜-valued holomorphic functions (12III) |
| 130 | 92–551 | 460 | power series, Hadamard, term-wise derivative, uniqueness |
| 140 | 552–1879 | 1328 | 𝒜-valued contour integral, Goursat, `invint` 1–4 |
| 150 | 1880–3468 | 1589 | winding number of the *N*-gon, Cauchy, Taylor, rigid expansion |
| | **total** | **3430** | |

16II `norm_spectrum` (`Positive.lean:3475`) is already proved on the printed
route off that block, and 11XV.1 `spectrum_self_adjoint_real_1`
(`Basic.lean:2966`) is already proved on the thesis's own 11XIII chain.  **Both
targets exist.**  What is left is not mathematics: it is ten call sites that
still name the Mathlib lemma instead of the tree's own theorem.

## 1. The use sites (item 1)

The brief names four.  There are **ten, in eight declarations, in two files** —
`grep -rn 'spectralRadius_eq_nnnorm\|mem_spectrum_eq_re' Theses/`.  (One further
hit, `Positive.lean:3479`, is a doc comment, not a use.)  No file outside
`A/CStar` uses either fact.

### `IsSelfAdjoint.spectralRadius_eq_nnnorm` — 6 uses

Thesis point: **16II** `norm-spectrum` (cstar.tex:2581), whose proof is **16III**
(cstar.tex:2575).  What the print cites instead of Mathlib: 11II `geometric`,
11VII `geometric_convergence`, 15VII `rigid-expansion` — all in the tree.
Replacement in every case: `norm_spectrum a ha`, a literal statement match
(`spectralRadius ℂ a = (‖a‖₊ : ℝ≥0∞)`), declared at `Positive.lean:3475` under
`variable {𝒜} [CStarAlgebra 𝒜]` only, so no instance obstruction anywhere.

| site | enclosing declaration | point |
|---|---|---|
| `Positive.lean:3627` | `spectrum_nonempty` | 16V |
| `Positive.lean:3667` | `spectrum_eq_singleton_iff` | 16VI |
| `Positive.lean:3733` | `norm_le_iff_spectrum_norm_le` | 16II aux |
| `Positive.lean:3742` | `norm_le_iff_spectrum_norm_le` | 16II aux |
| `Positive.lean:6586` | `norm_or_neg_norm_mem_spectrum'` | 22III.5 aux |
| `Representation.lean:2129` | `norm_le_norm_conjugate` | 28IV pt 60 |

All six are *downstream* of line 3475 in the import order, so no re-ordering is
needed.

### `IsSelfAdjoint.mem_spectrum_eq_re` — 4 uses

Thesis point: **11XXI**.1 (cstar.tex:1649), which the print reads off from
**11XV**.1 (cstar.tex:1570), itself proved from **11XIII**.  The tree already has
that whole chain, and `Basic.lean:3005` carries a wrapper
`mem_spectrum_eq_re_of_isSelfAdjoint` whose docstring says in so many words that
it exists so reality of the spectrum runs on the thesis chain "and not on
Mathlib's independent `IsSelfAdjoint.mem_spectrum_eq_re`".  **The wrapper is
`private`.**  That is the entire reason the four sites below reach for Mathlib:
they are in other files and cannot see it.

| site | enclosing declaration | point |
|---|---|---|
| `Positive.lean:3767` | `pos_spectrum` | 17III |
| `Positive.lean:4231` | `norm_le_of_thesisPos_pair` | 17VI.3a |
| `Positive.lean:6588` | `norm_or_neg_norm_mem_spectrum'` | 22III.5 aux |
| `Representation.lean:900` | `spectrum_miu` | 27XVII |

The public 11XXI.1 `spectrum_basic_1` (`Basic.lean:3434`) states the *subset*
form `spectrum ℂ a ⊆ Set.range ((↑) : ℝ → ℂ)`, so using it costs an `obtain` at
each site.  Dropping `private` from the pointwise wrapper is cheaper and keeps
the parsec-110 provenance visible.

## 2. Parsec 120–150, point by point, with audit state (item 2)

Every statement-bearing point of 120–150 has a Lean declaration; all rows are
`stmt = ok` except one, and **no proof in the block uses a Mathlib
complex-analysis theorem** — `grep` over `Positive.lean:39–3468` finds no
`circleIntegral`, no `hasFPowerSeriesOnBall`, no `isExactOn_ball`, no
`AnalyticOn`.  `DifferentiableOn ℂ` appears only as the *hypothesis* form.

| point | declaration | stmt | proof |
|---|---|---|---|
| 12III | `holomorphic_add/_mul/_id/_const/_polynomial` | ok | faithful ×5 |
| 13II | `radiusOfConvergence`, `fpsOfCoeffs` | ok | none |
| 13II | `hadamard_1` | ok | **mathlib** |
| 13II | `hadamard_2` | ok | faithful |
| 13IV | `summable_deriv_bound`, `powerSeries_hasDerivAt` | ok | none / faithful |
| 13VI | `powerseries_uniqueness_coeffients` | ok | faithful |
| 14II | `integral_scalar_smul` | **weaker** | **mathlib** |
| 14II | `integral_norm_le` | ok | **mathlib** |
| 14III | `segIntegral`, `triIntegral`, `measuredAngle`, `windingNumber`, +3 aux | ok | none |
| 14V | `triIntegral_affine` | ok | faithful |
| 14IV | `goursat` | ok | faithful |
| 14VIII | `invint_1/_2/_2'/_3/_4`, `inv_seg_ray`, `inv_seg_log`, `segment_inv_integral` | ok | faithful (2 none) |
| 15I | `cauchy_formula` | ok | **mild** |
| 15III | `polygon_slope_integral_zero` | ok | faithful |
| 15IV | `polygon_triangle`, `dir_lift`, `tri_zero_arc` | ok | **mild** / none |
| 15V | `taylor`, `edge_taylor` | ok | faithful |
| 15VII | `rigid_expansion`, `ball_subset_polygon` | ok | faithful / none |
| 16II | `norm_spectrum` | ok | faithful |
| 16V/VI/VII | `spectrum_nonempty`, `spectrum_eq_singleton_iff`, `gelfand_mazur` | ok | faithful |

Chain points outside 120–150 that the route needs, all `ok`/`faithful` in
`acstar-basic.csv`: 11II `geometric_1/_2`, 11VI `spectrum_bounded_1–3`,
11VII `geometric_convergence`, 11XIII `selfAdjoint_sub_I_isUnit`,
11XV `spectrum_self_adjoint_real_1–3`, 11XXI `spectrum_basic_1–6`.

Two points of the block are prose only and correctly carry no row: 14IX
(cstar.tex:2392, "not needed here") and 16IV (which 16II's own doc block
disowns).  Note a DISP mismatch in the prose: `HANDOFF` calls the target
"16III"; the audit row is **16II** (160.20 is the Proposition, 160.30 its Proof).

## 3. Line estimate (item 3)

**To make the bootstrapping claim true as written — ~25 lines of Lean.**

| item | file | lines |
|---|---|---|
| drop `private` from `mem_spectrum_eq_re_of_isSelfAdjoint`, promote its docstring to a public 11XXI.1 pointwise form | `Basic.lean:3005` | 4 |
| 5 `spectralRadius_eq_nnnorm` → `norm_spectrum` rewrites (3627, 3667, 3733, 3742, 6586) | `Positive.lean` | 8 |
| 3 `mem_spectrum_eq_re` → wrapper rewrites (3767, 4231, 6588) | `Positive.lean` | 5 |
| 2 rewrites (900, 2129) | `Representation.lean` | 4 |
| refresh the 8 audit `note`/`status` fields | 2 CSVs | 8 |
| rewrite `HANDOFF` item 0, `DECISIONS` §2.2, `PROVING-LOG` "Where the bootstrapping now stands", `Positive.lean` header | 4 docs | ~60 prose |

Each rewrite is a one-token substitution into an identical statement; no proof
restructuring, no new lemma.  Cost is dominated by the rebuild, not the edit.

**Optional, to make every 120–150 row `faithful` as well — ~680 further lines,
of which ~550 should probably not be spent.**

| item | lines | verdict |
|---|---|---|
| 13II `hadamard_1`: transcribe the printed ε-and-geometric-tail argument in place of `FormalMultilinearSeries.summable_norm_mul_pow` | ~50 | worth doing |
| 15I/15IV `mild`: the triangle *T* is traversed with `wn_T(z₀) = +1` where 15IV prints `−1`; also 14VIII.5's *N*-gon winding number is proved outright by `polygon_winding` rather than by the printed partition | ~80 | low value; a reader does not stumble (per the errata standard) |
| 14II parts 1–3: build the 𝒜-valued step functions `S_𝒜`, the unique linear `∫` with `∫ a·1_I = |I|a`, the disjoint-interval normal form, density in `C([0,1],𝒜)`, and re-base `segIntegral` on it | ~550 | **do not**: this replaces Mathlib's Bochner integral with a hand-rolled one, which is measure theory, not thesis content |

## 4. What gets replaced, what stays (item 4)

**Replaced — Mathlib results the thesis's own route now proves, and which no
longer appear anywhere in `A/CStar`:**
`DifferentiableOn.isExactOn_ball` (Morera for a disc) by 14IV `goursat`;
`DifferentiableOn.hasFPowerSeriesOnBall` and `eq_formalMultilinearSeries` by
15V `taylor` + 13VI `powerseries_uniqueness_coeffients` + 15VII
`rigid_expansion`; `IsSelfAdjoint.spectralRadius_eq_nnnorm` by 16II
`norm_spectrum`; `IsSelfAdjoint.mem_spectrum_eq_re` by 11XIII → 11XV.1 →
11XXI.1; `spectrum.nonempty` (Gelfand–Beurling, which 16IV disowns) by 16V
`spectrum_nonempty`; `CStarAlgebra.norm_or_neg_norm_mem_spectrum` (CFC) by
`norm_or_neg_norm_mem_spectrum'`; `WeakDual.CharacterSpace.mem_spectrum_iff_exists`
(maximal ring ideals, which 16VIII rejects) by 27XVII `spectrum_miu`;
`ContinuousMap.spectrum_eq_range` by 11XX `spectrum_continuousMap`;
`StarSubalgebra.spectrum_eq` by 11XXIII `spectral_permanence`.

**Stays, legitimately foundational:** the Bochner/`intervalIntegral` integral
itself (14II, above); `Real.cos/sin/pi/log/arctan` with the IVT;
`Complex.exp/log/arg`; `FormalMultilinearSeries` as the vehicle for
`radiusOfConvergence`; `Metric`, `Convex`, `convexHull`, completeness;
`HasDerivAt` calculus; Mathlib's `CStarAlgebra` class and the *definitions*
`spectrum`, `spectralRadius` with their algebra (`spectrum.mem_iff`,
`sub_singleton_eq`, `spectralRadius_le_nnnorm`).  After the ten rewrites the
claim "from the ground up" holds in the intended sense: real analysis and the
integral are imported, every C\*-algebraic and complex-analytic step is the
thesis's.

## 5. Rounds (item 5)

Rounds 1–3 are serial: `Basic → Positive → Representation` is the import chain,
and editing `Basic.lean` invalidates the whole `A/CStar` olean chain.  One
worker per file — parallel workers on `Positive.lean` would collide.  Serialise
every compile through `scripts/lean1.sh`.

1. **`Basic.lean`** — drop `private` from `mem_spectrum_eq_re_of_isSelfAdjoint`
   at :3005, restate its docstring as the pointwise form of 11XXI.1, keep it
   adjacent to `spectrum_basic_1`.  4 lines; forces a full `A/CStar` rebuild.
2. **`Positive.lean`** — the 8 rewrites at 3627, 3667, 3733, 3742, 3767, 4231,
   6586, 6588; drop the now-wrong "would close this in one line" aside at :3479
   and the `norm_or_neg_norm_mem_spectrum'` docstring's Mathlib caveat.  13 lines.
3. **`Representation.lean`** — the 2 rewrites at 900 and 2129.  4 lines.
4. **Docs and audit** — `HANDOFF` item 0, `DECISIONS` §2.2 (the recommendation
   paragraph is now moot: (a)'s "largest single item" is done), `PROVING-LOG`
   "Where the bootstrapping now stands", `Positive.lean` header block, and the
   `note`/`status` fields of the 8 affected audit rows.  No compile.
5. *(optional)* **13II `hadamard_1`** — transcribe the printed
   ε-and-geometric-tail argument; `Positive.lean:157`, ~50 lines, `mathlib` →
   `faithful`.
6. *(optional)* **15I/15IV orientation** — flip *T* to `wn_T(z₀) = −1` as
   printed, and route 14VIII.5 through the 15IV partition; ~80 lines, two
   `mild` rows → `faithful`.  Recommend deferring: no reader stumbles.

Rounds 1–4 are the whole of the claim: round 4 alone would be dishonest without
1–3, and 1–3 alone leave three documents asserting a `sorry` that is gone.
