# `Theses/A/CStar/` — full survey of the remaining `sorry`s (first survey of this chapter)

**Headline count at the time of the survey: A/CStar had 28 code `sorry`s.**
**Session 74 took it to 1.**  Session 73 closed the whole of parsec 140
(`goursat` and the four `invint` items); session 74 closed **15I
`cauchy_formula`**, **15V `taylor`**, **34VII `ccstar_pos_mat`** and **34IX.2
`cp_commutative_dom`**.  What remains is `functional_calculus_4` (**28II**.4),
the do-not-touch (d) item, which is awaiting an author decision — so **every
statement of `cstar.tex` except that one is proved**.

| file | at survey | after session 69 | after session 73 | after session 74 |
|---|---|---|---|---|
| `Basic.lean` | **0** | **0** | **0** | **0** |
| `Positive.lean` | 13 | 7 | 2 | **0** |
| `Representation.lean` | 11 | **1** | **1** | **1** |
| `Matrices.lean` | 4 | 2 | 2 | **0** |
| `TowardsVN.lean` | **0** | **0** | **0** | **0** |
| **total** | **28** | **10** | **5** | **1** |

All figures are compiler-counted and each is paired with an **error count
of 0** (session 74, recipe below).

Session 69 closed **18 of the 28**: the whole parsec 270 Riesz-ideal chain,
**30X**.2 and **30XIV** `gelfand_naimark` (the chapter's headline theorem) in
`Representation.lean` — leaving only the do-not-touch 28II.4; the whole parsec
130 power-series block plus 15VII and 24II.3 in `Positive.lean`; and both
**32XV** items in `Matrices.lean`.  What is left is **two clusters and nothing
else**: `goursat` with the six items behind it (parsecs 140–150), and `34VII`
with `34IX.2` behind it.

> **Do not count from the file headers.**  Four of the five used to open with
> "Statements only; every proof is `sorry`", which was false in all four.
> (`TowardsVN.lean` never carried that line — the first version of this survey
> said "all five", wrongly.)  `Basic.lean` and `Representation.lean` were fixed
> in session 69.

Refresh with (bypasses another agent's `lake build` lock):

```sh
export PATH="$HOME/.elan/bin:$PATH"
LP=".lake/build/lib/lean"; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
for f in Basic Positive Representation Matrices TowardsVN; do
  echo -n "$f: "
  env LEAN_PATH="$LP" lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 \
    Theses/A/CStar/$f.lean > /tmp/out-$f.txt 2>&1
  echo -n "$(grep -c 'declaration uses' /tmp/out-$f.txt) sorries, "
  echo "$(grep -c ': error' /tmp/out-$f.txt) errors"
done
```

⚠ **The two `-D` flags are load-bearing** (session 69).  `lakefile.toml` sets
`relaxedAutoImplicit = false` and `maxSynthPendingDepth = 3`, and a bare `lean`
does not read it: without `-DmaxSynthPendingDepth=3`, `Matrices.lean:1118`
(`ad_cp_3`) reports a spurious "typeclass instance problem is stuck", so the
recipe above claims **1 error** on a file that compiles cleanly.  The first
version of this survey omitted them.

Classification: **(a)** self-contained — a complete argument exists to
transcribe, or (for exercises) every ingredient is already in the tree;
**(b)** blocked on a *named* `sorry`; **(c)** cited to the literature, nothing
to transcribe; **(d)** suspicious — looks false or mis-transcribed.

**Counts at the time of the survey: (a) 17 · (b) 10 · (c) 0 · (d) 1.**
After session 69: (a) 2 (`goursat`, `34VII`) · (b) 7 · (c) 0 · (d) 1 (28II.4).
After session 73: (a) 2 (`15I`, `34VII`) · (b) 2 (`taylor`, `34IX.2`) · (c) 0 ·
(d) 1 (28II.4).  **After session 74: (a) 0 · (b) 0 · (c) 0 · (d) 1** — only the
28II.4 statement question is left.

**There are no (c) items in this chapter.**  Unlike A/VN (Artin–Wedderburn,
`L^∞`) and B/Dils, A/CStar cites nothing as a black box.  14IV `goursat`
credits Moore 1900 for the *idea* but reproduces the proof in full.

---

## `Positive.lean` — 13 (now 7)

| point | decl | class | session 69 |
|---|---|---|---|
| **13II**.1 | `hadamard_1` | (a) small | **proved** (4 lines) |
| **13II**.2 | `hadamard_2` | (a) small; hypothesis stronger than source | **proved** (6 lines) |
| **13IV** | `powerSeries_hasDerivAt` | (a) medium | **proved** (~40 lines) |
| **13VI** | `powerseries_uniqueness_coeffients` | (a) small | **proved** (~15 lines) |
| **14IV** | `goursat` | (a) **large — was the chapter's only gate** | **proved** (~340 lines, session 73) |
| **14VIII**.2 | `invint_2` | (a) small–medium | **proved** (~35 lines, from 14VIII.3) |
| **14VIII**.2′ | `invint_2'` | (a) small–medium | **proved** (~50 lines, from 14VIII.3) |
| **14VIII**.3 | `invint_3` | **(b)** on `goursat` — **wrongly**; it is (a) | **proved** (~75 lines, no Goursat) |
| **14VIII**.4 | `invint_4` | **(b)** on `invint_3` | **proved** (~25 lines) |
| **15I** | `cauchy_formula` | **(b)** on `goursat` + `invint_4` | **proved** (~420 lines, session 74) |
| **15V** | `taylor` | **(b)** on `cauchy_formula` | **proved** (~90 lines, session 74) |
| **15VII** | `rigid_expansion` | (a) — **not** blocked, see below | **proved** (~35 lines) |
| **24II**.3 | `cstar_pos_neg_part_3` | (a) small | **proved** (~105 lines) |

> **Session-69 costings.**  The survey's single best call was that the
> `radiusOfConvergence a = p.radius` bridge is the only real work in three of
> the four power-series items: factored out as the private
> `radiusOfConvergence_eq` + `fpsOfCoeffs_hasFPowerSeriesOnBall` (~55 lines),
> after which each dependent item cost 4–40 lines.  Two costings were badly
> off: **15VII** (~35 actual vs 80–120) and **13IV** (~40 vs 80–150) were
> over-costed — 13IV was the *second cheapest* of the four, not the dearest —
> while **24II**.3 was **under-costed roughly 2×** (~105 lines, not 40–60),
> because `|a+b| = (√2/2)·1` puts an irrational entry in the matrix and the
> neighbouring template's pure-`norm_num` endgame does not carry over.
> Mathlib drift to note: `HasSum.tendsto_atTop_zero` is gone (use
> `h.summable.tendsto_atTop_zero`); `EMetric.ball` / `Metric.emetric_ball*` are
> deprecated for `Metric.eball*`; `Matrix.dotProduct` is now root `dotProduct`.
> One trap: `rw [← map_mul]` on a goal containing a `!![…]` literal resolves
> against `Matrix.of`, not `Matrix.toEuclideanCLM`.

> **Session-73 costings and the two calls that were wrong.**  `goursat` came in
> at ~340 lines, inside this survey's ~250–400 — but the survey's reason was
> wrong twice over.  (i) "**Mathlib does not help here**" is false: Mathlib
> supplies the entire *endgame*.  `DifferentiableOn.isExactOn_ball`
> (`Mathlib/Analysis/Complex/HasPrimitives.lean`, Morera for a disc, stated for
> an arbitrary complete complex normed space so it applies to `𝒜`) gives a
> primitive on any disc, and the nested triangles eventually sit inside one; the
> thesis's `f(z*) + f'(z*)(z−z*) + o(·)` estimate is never needed.  What Mathlib
> does not help with is the *rectangle*-to-triangle transfer, which is a
> different claim — and that route is a **dead end**, because a triangle inside
> an open `U` need not lie inside any rectangle or disc inside `U`, so the only
> bridge is a primitive, and Mathlib's primitives are disc-only.  The bisection
> is unavoidable; transcribe the author.  (ii) **14VIII.3 was never (b) on
> `goursat`.**  Proved directly (see below) it becomes the *source* of 2, 2′ and
> 4, so the whole exercise costs ~200 lines with Goursat untouched, against this
> survey's ~80 + ~80 + rest — and the two ~80s were themselves over-costed once
> the order is reversed.

Twelve of these thirteen are the complex-analysis preamble of parsecs 120–150,
built only to reach **16II** `norm_spectrum` — which is *already proved*, from
Mathlib's `IsSelfAdjoint.spectralRadius_eq_nnnorm`.  Nothing in the tree uses
any of them.

**13II**.1 `hadamard_1` (`cstar.tex:1806`) — `∑ₙ‖aₙ‖‖z‖ⁿ` is summable for
`‖z‖ < R`.  The thesis proof is complete (ε below `R⁻¹`, geometric tail), but
Mathlib is shorter: build `p : FormalMultilinearSeries ℂ ℂ 𝒜` by
`p n = ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n)`, whose norm is `‖a n‖`
(`ContinuousMultilinearMap.norm_mkPiRing`), and identify our
`radiusOfConvergence a` with `p.radius` through
`FormalMultilinearSeries.radius_inv_eq_limsup`
(`Mathlib/Analysis/Analytic/RadiusLiminf.lean:66`) — it is literally our
definition.  Then `FormalMultilinearSeries.summable_norm_mul_pow`
(`Analytic/ConvergenceRadius.lean:241`) is the conclusion.  **Factor the
identification `radiusOfConvergence a = p.radius` out as its own lemma**: all
four power-series items reuse it, and it is the only real work in three of them.

**13II**.2 `hadamard_2` — converse.  `le_radius_of_tendsto` /
`le_radius_of_summable_norm` (`ConvergenceRadius.lean:229/233`) via the same
bridge.  ⚠ *Shape note:* our hypothesis is Mathlib `Summable (fun n => zⁿ • aₙ)`
— unconditional summability — where the thesis says only that the series
converges.  In an infinite-dimensional `𝒜` that is strictly stronger, so our
statement is slightly weaker than 13II.2.  Harmless for every intended use
(this direction is only ever applied to norm-convergent series), but recorded.

**13IV** `powerSeries_hasDerivAt` — holomorphy of a power series with the
term-wise derivative, at *any* `z` in the disc, not just the centre.  Mathlib's
`FormalMultilinearSeries.hasFPowerSeriesOnBall` plus
`HasFPowerSeriesAt.hasDerivAt` gives the centre for free; the general point
needs `HasFPowerSeriesOnBall.changeOrigin` / `p.derivSeries`.  The thesis's own
proof (uniform domination of the difference quotients by `2∑ₙ n‖aₙ‖rⁿ⁻¹`) is
equally transcribable.  ~80–150 lines either way.

**13VI** `powerseries_uniqueness_coeffients` — vanishing on a disc forces all
`aₙ = 0`.  The thesis hint differentiates repeatedly, which would make this
depend on 13IV; **in Lean it does not need to** —
`HasFPowerSeriesAt.eq_formalMultilinearSeries`
(`Analytic/Uniqueness.lean:113`) closes it against the zero series in ~40 lines.

**14IV** `goursat` (`cstar.tex:2177`) — **PROVED (session 73), ~340 lines,
axiom-clean.**  The bisection (segment reparametrisation, splitting, sign
reversal, the four sub-triangles, the quarter-of-the-integral choice, the nested
limit) is transcribed from the thesis in full; only the final estimate is
replaced, by Mathlib's Morera-on-a-disc.  Two devices made it cheap and are
worth reusing: the limit point comes from the *first vertices* forming a Cauchy
sequence (`cauchySeq_of_le_geometric_two` /
`dist_le_of_le_geometric_two_of_tendsto`, which also supply the quantitative
`dist (aₙ) z ≤ 2S₀/2ⁿ`), so no nested-compact intersection is needed; and
`triSideMax` — the longest side — replaces `Metric.diam` throughout, since every
side of every sub-triangle is *exactly half* a side of the parent (a `ring`
identity) and `convexHull {v₀,v₁,v₂} ⊆ closedBall v₀ (triSideMax …)` is one
`convexHull_min`.  All the machinery is `private` in `Positive.lean` and is
reusable: in particular `segIntegral_reparam` (hypothesis-free) and
`triIntegral_of_primitive`.

**14VIII**.2 / .2′ / .3 / .4 — **all four PROVED (session 73), and the thesis's
order is reversed.**  The thesis proves 2 by hand and reduces 3 to it *using
Goursat*; here **3 is proved directly and 2, 2′ and 4 are corollaries**.  The
observation: if `z₀ ∉ [w,w']` then the rescaled segment from `1` to
`ζ := (w'−z₀)/(w−z₀)` misses not merely `0` but **the whole branch cut
`(−∞,0]`**, so `Complex.log` is an honest antiderivative along it and
`Complex.hasDerivAt_log` + `intervalIntegral.integral_eq_sub_of_hasDerivAt` give
`∫_w^{w'} (z−z₀)⁻¹ dz = Log ζ` in one step.  That is the private
`segment_inv_integral`.  2 and 2′ are its case `z₀ = 0` (the segments miss `0`
because the real part is `a ≠ 0`, resp. the imaginary part is `b ≠ 0`), using
`arg x = arctan(x.im/x.re)` on the right half plane — not a Mathlib lemma, but
two lines from `Complex.abs_arg_lt_pi_div_two_iff`, `Complex.tan_arg` and
`Real.arctan_tan`.  4 is the thesis's own telescoping argument.

**15I** `cauchy_formula` — **PROVED (session 74), ~420 lines,
axiom-clean**, and *two* of the route sketched below turned out to be avoidable.
(1) **No primitive on a convex open set is needed.**  The fan triangulation from
the vertex `w₀` telescopes the spokes, so the closed-polygon integral is
`∑ₙ ∫_{T(w₀,wₙ,wₙ₊₁)}`, and each of those triangles already lies in
`convexHull(range w) ⊆ U`; `goursat` applies directly (`polygon_fan`,
`polygon_integral_eq_zero`, ~25 lines together).  So `Metric.thickening`,
convexity of `V` and `F(z) = ∫_c^z f` are all unnecessary.
(2) **The winding number needs only continuity, not holomorphy.**  By `invint_3`
the polygon integral is `i·∑ₙ arg ζₙ` with `ζₙ = (wₙ₊₁−z₀)/(wₙ−z₀)` (the
logarithms telescope, `w_N = w₀`).  Each edge spans a supporting line of the
`N`-gon, so an interior `z₀` satisfies
`Re((z₀−c)·conj e^{iπ(2n+1)/N}) < r cos(π/N)` **strictly**, which is exactly
`Im(conj(wₙ−z₀)(wₙ₊₁−z₀)) > 0`; hence every `ζₙ` is in the open upper half
plane, `arg` is continuous there, `exp(i ∑ arg ζₙ) = ∏ ζₙ = 1`, and the
intermediate value theorem along the segment from the centre makes the sum
constant `= N·(2π/N) = 2π`.  That is `polygon_winding`.  The fiddliest
ingredient is `cos(πm/N) ≤ cos(π/N)` for **odd** `m` (`cos_le_cos_of_odd`).
Mathlib's `Complex.differentiableOn_dslope` handles the removable singularity as
predicted.  (The thesis's vertex formula `wₙ = c + r cos(2π/n) + i r sin(2π/n)`
is a typo for `2πn/N`; our `hw` already writes the correct
`c + r·exp(2πi·n/N)`.  The "`‖f'(z₀)‖ + 37`" is the author's joke, and a valid
bound.)

**15V** `taylor` — **PROVED (session 74), ~90 lines.**  Per edge, the geometric
expansion of `(u−z)⁻¹` is integrated term by term with
`intervalIntegral.hasSum_integral_of_dominated_convergence`, dominated by
`(‖z−v‖/s)ⁿ·(M/s)`; the hypothesis `ball v s ⊆ interior(polygon)` gives
`s ≤ ‖u−v‖` on every edge **only through `polygon_notMem_edge`**, the same
lemma 15I needs.  Then `hasSum_sum` over the edges and `HasSum.const_smul`.

**15VII** `rigid_expansion` — ⚠ **classified (a), against the thesis's own
dependency graph.**  The thesis derives it from 15V + 13VI.  In Lean it needs
neither: `DifferentiableOn.hasFPowerSeriesOnBall`
(`Mathlib/Analysis/Complex/CauchyIntegral.lean:71`, stated for any complete
complex normed space, so it applies to `𝒜`) gives a power-series expansion of
`f` on the *whole* of `ball w R` directly from `hf`/`hball`, and
`HasFPowerSeriesAt.eq_formalMultilinearSeries` identifies its coefficients with
the given `a` using `hsmall` on the small ball.  ~80–120 lines, and **the only
item of parsecs 120–150 outside the power-series group that is reachable
without Goursat.**  A good early win that also demonstrates the
`radiusOfConvergence`/`FormalMultilinearSeries` bridge for the rest.

**24II**.3 `cstar_pos_neg_part_3` (`cstar.tex:3700`) — `|a+b| ≰ |a|+|b|` for
self-adjoint operators on `ℂ²`.  **(a), ~40–60 lines, the cheapest item in the
chapter.**  The thesis hint supplies the witnesses
(`a = ½[[1,1],[1,1]]`, `b = −[[1,0],[0,0]]`), and the *template is 50 lines
above it*: the `sqrt`-monotonicity counterexample at `Positive.lean:3630–3666`
does exactly this shape of argument in `EuclideanSpace ℂ (Fin 2)` —
`ContinuousLinearMap.nonneg_iff_isPositive`, then `isPositive_iff` evaluated at
an explicit vector, then `norm_num [Complex.le_def]`.  24II.1 and .2 on either
side are proved.

---

## `Representation.lean` — 11 (now 1)

| line | point | decl | class |
|---|---|---|---|
| ~776 | **28II**.4 | `functional_calculus_4` | **(d)** weaker than source |
| ~1290 | **30X**.2 | `proto_gelfand_naimark_2` | (a) large — see the ⚠ below |
| ~1302 | **30XIV** | `gelfand_naimark` | **(b)** on 30X.2 — but see the ⚠ below |

> **✅ The parsec 270 Riesz-ideal chain is CLOSED (session 69).**  All eight —
> `riesz_ideal_ring_ideal` (27VIII), `riesz_ideal_basic_1`/`_1b`/`_1c`/`_2`/`_3`
> (27X.1/.1b/.1c/.2/.3), `maximal_riesz_ideal_maximal_order_ideal` (27XI) and
> `riesz_ideal_miu_map` (27XIII) — are proved and axiom-clean, in the order this
> survey recommended, and **27XV `inv_mult_state` has been rewritten to use them**,
> so the maximal-ring-ideal detour that **16VIII** rejects is gone.  The section
> below is kept as the record of what the chain needed.

### The parsec 270 Riesz-ideal chain (8 sorries — all closed in session 69)

Dependency shape, all edges taken from the thesis's own citations:

```
        27VIII ──┐
27X.1 ───────────┼──> 27XI ──> 27XIII
27X.2 ───────────┘
27X.3   (isolated)
27X.1 ──> 27X.1b, 27X.1c
```

**Every external ingredient this chain needs is already proved**, in
`Positive.lean`: `maximal_ideal_state` (2746), `riesz_decomposition_lemma`
(4202), `order_ideal_basic_2` (2099, Zorn for order ideals),
`order_ideal_basic_3a/3b` (2275/2295, the least order ideal `(a)`),
`commutative_cstar_basic_1–4` (4009–4180, the Riesz-space structure of `𝒜_sa`),
and `IsOrderIdeal`/`IsMaximalOrderIdeal`.  This is the only multi-item chain in
the chapter with that property.

**27VIII** `riesz_ideal_ring_ideal` (`cstar.tex:3963`) — a Riesz ideal is a ring
ideal.  Complete proof at 270.90: reduce `x` to its real/imaginary parts, then
to `x⁺`/`x⁻` (using `|x| ∈ I`), then to `x ≥ 0` and `a` self-adjoint; conclude
from `−‖a‖x ≤ ax ≤ ‖a‖x` by 23VII `sqrt`.  ~100–150 lines.

**27X**.1 `riesz_ideal_basic_1` (`cstar.tex:3983`) — the least Riesz ideal on a
self-adjoint `a` is `(a)ₘ = {b : |ℜb|,|ℑb| ≤ n|a| for some n}`.  Exercise, no
written proof; the work is building the submodule and checking order-ideal +
`|·|`-closure + leastness.  ~200 lines, and the largest of the chain.  Its two
riders **27X**.1b (`(a)ₘ = 𝒜 ↔ a` invertible) and **27X**.1c (`(a)ₘ = (a)` for
`a ≥ 0`, against the proved `order_ideal_basic_3a/3b`) are each small once the
explicit description is available, and are (b) on it.

**27X**.2 `riesz_ideal_basic_2` — `I ⊔ J` is a Riesz ideal.  **Isolated** (no
other sorry depends on it except 27XI, and it depends on none).  The thesis's
hint is `riesz-decomposition-lemma`, which is proved at `Positive.lean:4202`.
A good self-contained target.

**27X**.3 `riesz_ideal_basic_3` — every proper Riesz ideal sits in a maximal
one.  **Fully isolated.**  This is Zorn on unions of chains, and
`order_ideal_basic_2` (`Positive.lean:2099`) is the same argument for order
ideals — copy its skeleton and add the `|·|`-closure clause, which passes to
unions trivially.  The cheapest item of the chain.

**27XI** `maximal_riesz_ideal_maximal_order_ideal` (`cstar.tex:4010`) —
**(b)** on 27VIII, 27X.1 and 27X.2, all three cited by name.
⚠ **Use `asols.tex`, not `cstar.tex`.**  The printed proof at 270.120 is
*wrong* — erratum `parsec-270.120` (`asols.tex:113`) opens "It's erroneously
assumed that `|a| ∈ J`" and supplies a corrected proof in full
(`asols.tex:115–171`).  Transcribe that one.

**27XIII** `riesz_ideal_miu_map` (`cstar.tex:4075`) — **(b)** on 27XI (and on
27VIII for the multiplicativity step).  This is the payoff: given 27XI, it is
`maximal_ideal_state` (proved) to get a pu-map with the right kernel, then four
lines — `b − f(b) ∈ ker f = I`, so `a(b − f(b)) ∈ I` by 27VIII, so
`f(ab) = f(a)f(b)`.

⚠ **What closing this chain actually bought.**  No `sorry` anywhere depended on
it.  What it bought is *honesty*: `inv_mult_state` (27XV) was proved, but its
own comment recorded that the hard direction went through Mathlib's Gelfand
theory, "which reaches the character space through maximal *ring* ideals —
exactly the route **16VIII** rejects", and that it "cannot be made honest
before that chain is proved."  **That repair is done.**

**Costings, measured.**  The chain came in at ~480 lines including helpers,
against this survey's ~150 (27VIII) + ~200 (27X.1) + rest — i.e. the estimates
were pessimistic, and the ordering was right.  Two things made it cheap, both
worth reusing:

* the private `orderIdealGen` skeleton of `Positive.lean:2170–2270` transfers
  almost verbatim to `rieszIdealGen` — same submodule fields, same `ℜ`/`ℑ`
  split, same `star_mem` computation; only the predicate changes;
* three helpers carry nearly everything: `abs_le_iff` (`|x| ≤ y ↔ -y ≤ x ≤ y`,
  one application of the proved **26II**.1), `abs_add_le` (the triangle
  inequality, immediate from it), and `mem_sup_of_le_add` (the
  Riesz-decomposition step).  All three are `private` in `Representation.lean`.

One erratum-of-the-erratum: `parsec-270.120`'s step `1 ≤ (|x|+na)(|y|+mb)` is
cited to `sqrt`(2) (**23VII**.2) but what it uses is **23VII**.1 — the product
of *commuting positives* is positive, via `uv − 1 = u(v−1) + (u−1)`.  Harmless;
both are proved.

### The rest

**28II**.4 `functional_calculus_4` (`cstar.tex:4299` — the doc comment says
4258; **drift 41 lines**).  **(d) — suspicious: weaker than the source.**
The exercise says: *show that `f(a)` is the unique element of `C*(a)` with
`φ(f(a)) = f(φ(a))` for all `φ ∈ spec(C*(a))`.*  Our statement is a bare
`∃! b : StarAlgebra.elemental ℂ a, ∀ φ, φ b = f (φ a)` — it asserts that *some*
unique element has the property and never says that element is `cfc f a`, which
is the entire usable content (the characterisation of the functional calculus by
characters).  As written it is true and (a)-sized, ~60 lines: existence from
`cfc`, uniqueness from Gelfand injectivity on the commutative
`StarAlgebra.elemental ℂ a` (commutative because `[IsStarNormal a]`).
**Recommended repair before proving:** state
`∀ b : StarAlgebra.elemental ℂ a, (∀ φ, φ b = f (φ a)) ↔ (b : 𝒜) = cfc f a`,
or at minimum add the conjunct that `cfc f a` satisfies the property.

> **Session 92: PROVED, and the flag stands.**  `functional_calculus_4` is
> closed and axiom-clean (25 lines, the thesis's own route: `j` from
> `characterSpaceToSpectrum`, then Gelfand on the commutative `C*(a)` via
> `gelfandStarTransform`), so `Representation.lean` — and with it the whole of
> A/CStar — has **no `sorry` left**.  The statement was *not* repaired: the
> recommended strengthening is filed as **QUESTIONS A10**, which carries a
> compiled 14-line proof of the missing clause `φ (cfc f a) = f (φ a)`, so the
> ruling is the only remaining cost.  It is that short because Mathlib's
> `continuousFunctionalCalculus a` is *defined* as part 3's `Φ`:
> `((characterSpaceHomeo a).compStarAlgEquiv' ℂ ℂ).trans (gelfandStarTransform _).symm`.

**30X**.2 `proto_gelfand_naimark_2` (`cstar.tex:4951` — doc says 4870; **drift
81 lines**) — if `Ω` is centre separating then `ϱ_Ω` is injective, so `𝒜`
embeds in `B(ℋ_Ω)`.  **(a), ~250–400 lines, and much closer than it looks:**

⚠ **Reclassify (session 69): our statement is weaker than the source, and it
is not a step towards 30XIV — it *is* 30XIV.**  The thesis's clause (1) is
"`ϱ_Ω` is injective"; ours is the bare `∃ H (ρ : 𝒜 →⋆ₐ[ℂ] B H), Injective ρ`,
which mentions neither `Ω` nor `ϱ_Ω`.  So (a) the converse (1) ⇒ (2) is
unstatable and only half the three-way equivalence is captured, and (b) 30X.2
and **30XIV** `gelfand_naimark` are the *same statement*, waiting on the *same*
missing construction.  Filed as **QUESTIONS A8**.  Whoever takes this on should
build `ϱ_Ω` properly and restate 30X, rather than prove the existential twice.

* the (2)⇔(3) half, `proto_gelfand_naimark_1`, is **proved** directly above
  (line 634), with four private helpers (`eq_zero_of_cube_eq_zero`,
  `conj_by_posPart`, `eq_zero_of_centreSeparating`, `nonneg_of_centreSeparating`);
* the single-`ω` GNS construction **exists in Mathlib** —
  `PositiveLinearMap.PreGNS`/`GNS`/`gnsStarAlgHom` in
  `Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean` — and this file
  already uses it (`omega_norm_basic_1/2`, `gns_starAlgHom_apply` at 527, and
  the 30VI note at 516–530);
* the Hilbert direct sum exists: `lp G 2` with its `InnerProductSpace` instance
  (`Mathlib/Analysis/InnerProductSpace/l2Space.lean:117`).

What is missing is exactly `ϱ_Ω` — the diagonal operator on
`lp (fun i => (ω i).GNS) 2`, bounded because each `‖ϱ_{ωᵢ}(a)‖ ≤ ‖a‖` — plus
the thesis's own four-line injectivity argument (270.120: `ϱ_Ω(a) = 0` forces
`‖ab‖_ω = 0` for all `b`, `ω`, and centre separation gives `a*a = 0`), and
`injective_miu_iso_on_image` (line 423, **proved**) for the final claim.
Universes are already named (`{ι : Type v}`, `𝒜 : Type u`, `H : Type (max u v)`)
— this is **not** an instance of the `∃ (ι : Type _)` auto-bound-universe bug.

⚠ **This retires a stale belief elsewhere.**  `AVN-survey.md` classes
**48III** `gns_normal` as **[L]**, "the GNS construction (cstar.tex 30VI) is not
formalized".  That was true when written; Mathlib's GNS file exists now and
`Representation.lean:516` already records it.  48III should be re-examined.

**30XIV** `gelfand_naimark` (`cstar.tex:5022`) — **(b)** on 30X.2, and on
nothing else: the thesis's proof is three lines given it, and its other input,
"the states are order separating", is `states_order_separating_1/2`
(`Positive.lean:2948/2979`, **proved**).  ~30 lines once 30X.2 lands.  The
universe here is correct too (`H : Type u` for `𝒜 : Type u` — the index set is
the states of `𝒜`, which lives in `Type u`).

---

## `Matrices.lean` — 4 (now 2)

| point | decl | class | session 69 |
|---|---|---|---|
| **32XV**.2 | `chilb_vector_states_2` | (a) medium | **proved** |
| **32XV**.3 | `chilb_vector_states_3` | (a) medium; source gives no argument | **proved** |
| **34VII** | `ccstar_pos_mat` | (a) **large — unblocks 34IX.2** | **proved** (~150 lines, session 74) |
| **34IX**.2 | `cp_commutative_dom` | **(b)** on 34VII | **proved** (~55 lines, session 74) |

> ⚠ **Both 32XV costings were wrong in the cheap direction, for the same
> reason: `Bᵃ(X)` as an actual `CStarAlgebra` *instance* did not exist** —
> neither here nor in Mathlib, whose `Analysis/CStarAlgebra/Module/` is
> `Defs` + `Constructions` + `Synonym` with **no adjointable-operator theory at
> all**.  `bax_cstar` (32XIII) supplies only the closedness half.  Session 69
> built it as a private `Subalgebra ℂ (X →L[ℂ] X)` — star = the chosen adjoint,
> `CStarRing` from 32XII, completeness from 32XIII, plus the spectral order —
> **~110 lines before either proof starts**, total insertion ~316 against the
> ~270 forecast.  Anyone touching parsec 320 again should reuse it.
> Also: `chilb_vector_states_3` needs `set_option maxHeartbeats 400000`
> (`rw` inside the `Bax` subtype is expensive; whole-file compile ~63 s), and
> `negPart_conj_aux`/`nonneg_of_negPart_cube` duplicate the two halves of
> `exists_negPart`, which sits *below* 32XV in the file — merge if reorganising.
>
> ⚠ **New erratum found here** (filed in ERRATA.md): after erratum
> `parsec-320.150` the exercise's own route to part 3 no longer works.  It asks
> the reader to "conclude" from order separation, imitating 250.30, which
> reduces to `T ≥ 0` via **21VII** `order-separating-norm` — stated for **pu**
> maps, while the erratum's point is that these functionals are only
> *subunital*.  Part 3's proof in Lean is therefore **ours**, not a
> transcription; so is part 2's, which the source also leaves as "conclude".
>
> **32XVI `chilb_adjoint_mul_self_nonneg` has been strengthened** to the
> thesis's Corollary 320.160 (`0 ≤ T*T` in `Bᵃ(X)`, not just pointwise), as
> this survey recommended once 32XV.2 landed.  It had no callers anywhere.

**32XV**.2 `chilb_vector_states_2` (`cstar.tex:5349` — doc says 5268; **drift
81**) — `0 ≤ T` in `Bᵃ(X)` iff `0 ≤ ⟨x,Tx⟩` for all `x`.  Part 1
`chilb_vector_states_1` (line 386) is **proved**, and its body (lines 396–440)
contains the reusable core: the polarisation argument `hQ`/`hB` showing that
`⟨x,Ux⟩ = 0` on the unit ball forces `U = 0`.  The remaining work is the
C*-algebra side — `bax_cstar` (line 328, proved) makes `Bᵃ(X)` a C*-algebra, and
`CStarAlgebra.nonneg_iff_eq_star_mul_self` turns `0 ≤ T` into `T = R*R`, which is
our existential.  ~150 lines.  ⚠ Check for circularity against
`cstar_matrix_positive_iff` (line 671), which is proved and lives in the same
orbit.

**32XV**.3 `chilb_vector_states_3` — `‖T‖ = sup_{‖x‖≤1}‖⟨x,Tx⟩‖` for
self-adjoint `T`.  ⚠ **The thesis gives no argument and its hint is retracted**:
erratum `parsec-320.150` (`asols.tex:255`) says "vector state" and `(X)₁` should
read "subunital vector functional" and `(X)_{≤1}`, and "Also, ignore the hint."
So provenance is (c)-like, but everything needed is in the file, hence (a):
`chilb_form_bounded` (line 250, proved) gives `‖Tx‖ ≤ B‖x‖ ↔ ‖⟨y,Tx⟩‖ ≤ B‖y‖‖x‖`
— one direction outright — and `module_maps_cstar_identity` (line 278, proved,
the C*-identity for adjointable operators) gives the other.  ~120 lines.
Note our statement **already incorporates the erratum** (`{x // ‖x‖ ≤ 1}`, and
functionals rather than states); part 2 quantifies over all `x` rather than the
unit ball, which is equivalent by scaling.

**34VII** `ccstar_pos_mat` (`cstar.tex:5584`; doc says 5504, **drift 80**) —
**PROVED (session 74), ~150 lines.**  ⚠ **Every costing of this item in this
survey was 3–5× too high, and for the same wrong reason.**  "The dominant cost
is the *transport* … moving `Mₙ(C(X))₊` to continuous `Mₙ(ℂ)`-valued functions
and back through `CStarMatrix`" is false: **no such bridge is needed**.  The
already-proved **33II**.1 `cstar_matrix_positive_iff`
(`0 ≤ A ↔ ∀ a, 0 ≤ ∑ᵢⱼ aᵢ* Aᵢⱼ aⱼ`) transports positivity across the character
space by itself, in *both* directions — `⇒` by taking `aᵢ = φ(vᵢ)·1` and
applying the (positive) character, `⇐` by feeding `vᵢ := φ(aᵢ)` to
`nonneg_of_forall_character` — and that 15-line lemma
(`matrix_nonneg_iff_character`) is the whole transport.  With it the thesis's
340.80 goes through verbatim: cover the character space by the opens where all
`N²` **entries** agree to within `δ`, `IsCompact.elim_finite_subcover`,
`PartitionOfUnity.exists_isSubordinate` (the character space is compact
Hausdorff, hence normal and paracompact), read off the estimate **entrywise**.
Two `CStarMatrix` frictions worth knowing: `‖M‖ ≤ ∑ⱼ∑ᵢ‖Mᵢⱼ‖` is proved in
Mathlib only inside a **`private`** lemma (`antilipschitzWith_toMatrixAux`) and
had to be repeated; and `(∑ₖ Mₖ) i j = ∑ₖ Mₖ i j` needs a hand-rolled induction,
since neither `Finset.sum_apply` nor `Matrix.sum_apply` fires through the
synonym.  Also: bare `isClosed_nonneg` resolves to the **Banach-lattice** lemma;
the one wanted is `CStarAlgebra.isClosed_nonneg`.

**34IX**.2 `cp_commutative_dom` (`cstar.tex:5643`) — **PROVED (session 74),
~55 lines**, by the thesis's one-sentence argument: `{M | 0 ≤ ∑ᵢⱼ bᵢ* f(Mᵢⱼ) bⱼ}`
is closed (`f` is bounded by the proved **20II**.2 `weak_russo_dye_2`, and entry
evaluation is 1-Lipschitz by `CStarMatrix.norm_entry_le_norm`) and contains the
generators, so 34VII applied to the Gram matrix `(aᵢ* aⱼ)` finishes it.  Its
sibling **34IX**.1 `cp_commutative_cod` (line 1260) was already proved.

⚠ **Nothing is waiting on 34IX.2**, contrary to what its two doc-comment
mentions might suggest.  `normal_russo_dye` (34aII, line 1559) is the only
would-be consumer, and it was **proved by a deliberate detour** — see the note
at lines 1546–1558: the one instance of `cp_commutative_dom` it needed is
`norm_sum_smul_le_aux` (line 1483), discharged by hand over the
finite-dimensional commutative `ι → ℂ`, with the partition of unity run directly
on `spec(a) ⊆ ℂ` through the continuous functional calculus.  No Gelfand
duality, no Urysohn.  So 34VII → 34IX.2 buys faithfulness, not reach.

---

## The three highest-value targets

> **Session 69: targets 1 and 2 are both DONE.**  The whole 270 chain, plus the
> 27XV repair; and **30X.2 and 30XIV `gelfand_naimark`** — the chapter's
> headline theorem — with `ϱ_Ω` built as the public `dsumRep`.  What remains of
> target 2 is a *statement* question (**QUESTIONS A8**), not a proof: our 30X.2
> drops `ϱ_Ω` from clause (1), so (1) ⇒ (2) is unstatable and 30X.2 is 30XIV
> rather than a step towards it.  Now that `dsumRep` exists, restating 30X
> faithfully is cheap — but it is an author decision.
>
> **Session 73: `goursat` is DONE, with the whole of 14VIII.**
>
> **Session 74: target 3 is DONE, and so are 15I, 15V and 34IX.2.  There are no
> targets left.**  The chapter's only open item is the *statement* question
> **28II**.4 (`functional_calculus_4`), which needs an author decision, not a
> proof.

**1. 27VIII `riesz_ideal_ring_ideal`** (`Representation.lean:81`) — **DONE**.
Chain-opening, and the chain is the biggest in the chapter: it is required by
27XI and 27XIII, and together with 27X.1/.2/.3 it accounts for **8 of the 28**
sorries.  It is the only chain here in which *every* external ingredient is
already proved (`maximal_ideal_state`, `riesz_decomposition_lemma`,
`order_ideal_basic_2/3a/3b`, `commutative_cstar_basic_1–4`), the thesis supplies
a complete proof, and the terminal item 27XIII is what lets `inv_mult_state` be
re-derived by the thesis's own route instead of the maximal-ring-ideal route it
explicitly rejects.  Order of attack within the chain: 27X.3 (isolated,
cheapest, copy `order_ideal_basic_2`) → 27VIII → 27X.2 → 27X.1 → 27XI (from
`asols.tex`) → 27XIII → 27X.1b/.1c.

**2. 30X.2 `proto_gelfand_naimark_2`** — **DONE**, together with 30XIV.
Chain-opening — it was the *sole* blocker of **30XIV `gelfand_naimark`**, the
headline theorem of the chapter, which is ~30 lines behind it.  Beats an
isolated item on two further counts: the (2)⇔(3) half is proved right above it,
and Mathlib now supplies both missing pieces of infrastructure (single-`ω` GNS,
`lp G 2` direct sum), so the residue is one construction (`ϱ_Ω` as a diagonal
operator) plus a four-line argument.  *All of that held.*  `ϱ_Ω` cost ~90 lines
and its template is `amp` (`A/VN/NormalFunctionals.lean:1716–1799`), the `ℕ`-fold
amplification built for 88V; 30X.2 and 30XIV together cost ~110 more.  Note
A/VN's public `lp_clm_ext` forces a primed name for the A/CStar copy.  Proving
it also settles whether A/VN's **48III `gns_normal`** is still correctly classed
[L] — it is not; Mathlib's GNS plus `dsumRep` should now cover it.

**3. 34VII `ccstar_pos_mat`** (`Matrices.lean`) — **DONE (session 74).**
Chain-opening (sole blocker of 34IX.2, closing the last CP-theory gap in the
chapter) with a complete thesis proof, but the payoff is faithfulness only —
`normal_russo_dye` already routed around it.  ⚠ **The "transport dominates" call was wrong**, and with it every costing of
this item (~350–500 here, 450–650 in session 69): the actual cost was ~150
lines, because `cstar_matrix_positive_iff` *is* the transport and neither
`(𝒜 ≃⋆ₐ ℬ) → (M_N 𝒜 ≃⋆ₐ M_N ℬ)` nor `M_N(C(X)) ≅ C(X, M_N ℂ)` has to be built.
See the 34VII entry above.

*Warm-ups:* none are left in this chapter — **nothing is left in this chapter**
except the 28II.4 statement question.

---

## What A/CStar gates downstream

**Nothing.  No declaration anywhere in `Theses/` is blocked, directly or
indirectly, on any of these 28 sorries.**  (Still true of the 1 that remains.)

Who imports it:

| importer | imports |
|---|---|
| `A/VN/Basic.lean:31–34` | `CStar.Basic`, `CStar.TowardsVN`, `CStar.Representation`, `CStar.Matrices` |
| `A/VN/NormalFunctionals.lean:21` | `CStar.Matrices` |
| `B/Dils/HilbertModules.lean:34` | `CStar.Matrices` |
| `B/Dils/Stinespring.lean:28` | `CStar.Matrices` |
| `A/Proc/*` | transitively, through `A/VN` |

So the surface is real — three other chapters sit on top of this one.  But
grepping the whole `Theses/` tree for each of the 28 declaration names returns
**no uses at all**, inside or outside A/CStar.  The complete set of
non-declaration hits is:

* `Positive.lean` — doc comments mentioning `goursat`/`taylor` (`goursat` is
  now proved and *is* used, by nothing yet, but see the 15I route above);
* `Matrices.lean:1483`, `:1546–1557` — the two notes explaining that
  `cp_commutative_dom` was *routed around*, not used;
* `A/VN/Basic.lean:2251` and `A/VN/Projections.lean:5473/5480` — these use
  `proto_gelfand_naimark_`**`1`**, the (2)⇔(3) equivalence, which is
  **proved**.  Not 30X.2.  This near-collision is the one place an audit could
  go wrong: the two names differ by a single character and only the second is
  `sorry`.

Two consequences.

**(i) A/CStar is faithfulness debt, not throughput debt.**  Closing any of these
28 will not unblock a single declaration outside the chapter, and will not
unblock anything inside it except along the four chains mapped above.  Weighed
against A/VN's 30 sorries — several of which *do* gate A/Proc and B/Dils — this
chapter should be scheduled for correctness-of-the-record reasons (the 270 chain
makes 27XV honest; 30X.2/30XIV give the chapter its headline theorem) rather
than to unstick anyone.

**(ii) The two indirect debts are worth carrying in the log**: `inv_mult_state`'s
honest-route comment (`Representation.lean:150–157`), and A/VN's now-doubtful
[L] on 48III `gns_normal`.  Neither is a `sorry`; neither shows up in a grep.
If an *indirect* leak is ever suspected, use `#sorry_leaks`
(`Theses/AxiomCheck.lean`, run with `lake env lean Theses/AxiomCheck.lean`) —
it distinguishes direct from indirect and lists the roots.  A plain grep will
not see one.

One related observation, not among the 28: **32XVI**
`chilb_adjoint_mul_self_nonneg` (`Matrices.lean:461`) is *proved*, but it
concludes `0 ≤ ⟨x, (S∘T)x⟩` for each `x`, whereas the thesis's Corollary 320.160
concludes `0 ≤ T*T` **in `Bᵃ(X)`**.  Ours is the hypothesis side of 32XV.2, not
its conclusion — deliberate (the doc comment says so, since 32XV.2 is `sorry`),
but it means the Corollary is not yet available in the form downstream code
would want.  When 32XV.2 lands, strengthen 32XVI to match.

---

## Housekeeping for the next worker

* **`cstar.tex:LINE` references in the doc comments have drifted, increasingly
  with depth.**  Confirm against the point number, never the line.  Measured
  drift: `Positive.lean` (parsecs 120–150, 240) **0–1 lines, still good**;
  27VIII/27X/27XI **+3** (3960→3963, 3980→3983, 4007→4010); 27XIII **+41**
  (4034→4075); 28II **+41** (4258→4299); and **+81 from parsec 300 onward** —
  30X 4870→4951, 30XIV 4941→5022, 32XV 5268→5349, 34VII 5504→5584, 34IX
  5563→5643.
* **`asols.tex` is errata-and-addenda, not solutions** — there are no worked
  exercise solutions for this chapter, and `parsec-340.60` (34VI.1) is an empty
  `\TODO{}`, which is why coverage appears to stop at parsec 340 (already noted
  as QUESTIONS A2).  Two entries matter here and are easy to miss:
  `parsec-270.120` (`asols.tex:113–171`) replaces a **wrong** proof of 27XI with
  a correct one, and `parsec-320.150` (`asols.tex:255–264`) corrects 32XV's
  statement and retracts its hint.  Our 32XV statements already follow the
  erratum.
* ~~**Update the five file headers.**~~  **Done for `Basic.lean` and
  `Representation.lean` (session 69).**  Note the survey was wrong to say all
  five carried the false line: **`TowardsVN.lean` never did** — its header
  already read "All statements of parsecs 350–400 are proved."  So it was four
  files, not five.
* **Do not edit a header of a file that nothing is waiting on while other
  agents are building.**  Touching `Basic.lean`'s header comment in session 69
  invalidated the whole `A/CStar → A/VN → {A/Proc, B/Dils}` olean chain and
  forced a full rebuild on a `B/Dils` worker mid-run.  Batch header fixes into
  the end of a session.
