# `Theses/A/CStar/` — full survey of the remaining `sorry`s (first survey of this chapter)

**Headline count: A/CStar has 28 code `sorry`s.**  Per file, counted by reading
every declaration body (each `sorry` is the whole proof of one `theorem`; no
declaration carries two):

| file | sorries |
|---|---|
| `Basic.lean` | **0** |
| `Positive.lean` | 13 |
| `Representation.lean` | 11 |
| `Matrices.lean` | 4 |
| `TowardsVN.lean` | **0** |
| **total** | **28** |

> **Do not count from the file headers.**  All five files still open with
> "Statements only; every proof is `sorry`."  That is false for every one of
> them, and flatly wrong for `Basic.lean` (1721 lines) and `TowardsVN.lean`
> (2033 lines), which are fully proved.

Refresh with (bypasses another agent's `lake build` lock):

```sh
LP=".lake/build/lib/lean"; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
for f in Basic Positive Representation Matrices TowardsVN; do
  echo -n "$f: "; env LEAN_PATH="$LP" lean Theses/A/CStar/$f.lean 2>&1 |
    grep -c "declaration uses"
done
```

Classification: **(a)** self-contained — a complete argument exists to
transcribe, or (for exercises) every ingredient is already in the tree;
**(b)** blocked on a *named* `sorry`; **(c)** cited to the literature, nothing
to transcribe; **(d)** suspicious — looks false or mis-transcribed.

**Counts: (a) 17 · (b) 10 · (c) 0 · (d) 1.**

**There are no (c) items in this chapter.**  Unlike A/VN (Artin–Wedderburn,
`L^∞`) and B/Dils, A/CStar cites nothing as a black box.  14IV `goursat`
credits Moore 1900 for the *idea* but reproduces the proof in full.

---

## `Positive.lean` — 13

| line | point | decl | class |
|---|---|---|---|
| 88 | **13II**.1 | `hadamard_1` | (a) small |
| 95 | **13II**.2 | `hadamard_2` | (a) small; hypothesis slightly stronger than source |
| 103 | **13IV** | `powerSeries_hasDerivAt` | (a) medium |
| 112 | **13VI** | `powerseries_uniqueness_coeffients` | (a) small |
| 159 | **14IV** | `goursat` | (a) **large — the file's gate** |
| 180 | **14VIII**.2 | `invint_2` | (a) small–medium |
| 190 | **14VIII**.2′ | `invint_2'` | (a) small–medium |
| 201 | **14VIII**.3 | `invint_3` | **(b)** on `goursat` |
| 210 | **14VIII**.4 | `invint_4` | **(b)** on `invint_3` |
| 223 | **15I** | `cauchy_formula` | **(b)** on `goursat` + `invint_4` |
| 239 | **15V** | `taylor` | **(b)** on `cauchy_formula` |
| 259 | **15VII** | `rigid_expansion` | (a) — **not** blocked, see below |
| 3710 | **24II**.3 | `cstar_pos_neg_part_3` | (a) small — **best cheap win in the chapter** |

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

**14IV** `goursat` (`cstar.tex:2177`) — **this is the gate of the whole
120–150 block**: 14VIII.3, and through it 14VIII.4, 15I and 15V, all cite it.
The thesis proof is complete (bisection, following Moore 1900) and is the
single largest transcription job in the chapter, ~250–400 lines.  **Mathlib
does not help here.**  Its complex-analysis development is stated for
*rectangle boundaries* (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`)
and *circles*, over an arbitrary complex Banach space `E`; our `triIntegral`
(built from `segIntegral`, `Positive.lean:134/140`) is a triangle, and there is
no bridge.  Anyone who takes this on should first decide whether to keep the
thesis's `segIntegral` vocabulary or to prove a rectangle↔triangle
transfer — the latter is probably the shorter road to 15I but abandons the
thesis's argument.

**14VIII**.2 / .2′ `invint_2` / `invint_2'` — the two explicit segment
integrals of `z⁻¹`.  Pure `intervalIntegral` computation; the thesis writes
both antiderivatives out (`arctan`, `log`).  Independent of Goursat, and of
each other up to mirroring.  ~80 lines apiece; do one, then the other is a
near-copy.

**14VIII**.3 `invint_3` — **(b)** on `goursat`: the thesis's hint is "using
Goursat's Theorem one may reduce the problem to horizontal and vertical line
segments", i.e. to .2/.2′.  A Goursat-free route exists (`Complex.log` is an
antiderivative of `z⁻¹` off the cut, `Complex.hasDerivAt_log`, plus the
fundamental theorem of calculus for the segment) and would *un*block this item
and 14VIII.4 without touching Goursat — worth considering, since Goursat is the
chapter's most expensive single item.

**14VIII**.4 `invint_4` — **(b)** on `invint_3`; then sum the three segments and
telescope the angles into `windingNumber`.  Small once .3 is in.

**15I** `cauchy_formula` — **(b)** on `goursat` *and* `invint_4`, both cited by
name in the proof (`cstar.tex:2396`).  ⚠ Note for whoever attempts it: the
thesis partitions the region between the small triangle `T` and the `N`-gon
"in the obvious manner into triangles `T₁,…,T_M`".  That triangulation is
asserted, not constructed, and is by some distance the hardest part to
formalize — treat it as an open gap in the source, not a transcription.  (The
"`‖f'(z₀)‖ + 37`" in the same proof is the author's joke, and a valid bound.)
Also: the thesis's vertex formula `wₙ = c + r cos(2π/n) + i r sin(2π/n)` is a
typo for `2πn/N`; our `hw` already writes the correct
`c + r·exp(2πi·n/N)`.

**15V** `taylor` — **(b)** on `cauchy_formula` (geometric-series expansion of
`1/(u−z)` under the integral, plus a uniform-convergence interchange).

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

## `Representation.lean` — 11

| line | point | decl | class |
|---|---|---|---|
| 81 | **27VIII** | `riesz_ideal_ring_ideal` | (a) medium — **root of the 270 chain** |
| 88 | **27X**.1 | `riesz_ideal_basic_1` | (a) medium–large |
| 99 | **27X**.1b | `riesz_ideal_basic_1b` | **(b)** on 27X.1 |
| 109 | **27X**.1c | `riesz_ideal_basic_1c` | **(b)** on 27X.1 |
| 120 | **27X**.2 | `riesz_ideal_basic_2` | (a) medium — isolated |
| 126 | **27X**.3 | `riesz_ideal_basic_3` | (a) small–medium — isolated |
| 133 | **27XI** | `maximal_riesz_ideal_maximal_order_ideal` | **(b)** on 27VIII, 27X.1, 27X.2 |
| 140 | **27XIII** | `riesz_ideal_miu_map` | **(b)** on 27XI |
| 322 | **28II**.4 | `functional_calculus_4` | **(d)** weaker than source |
| 690 | **30X**.2 | `proto_gelfand_naimark_2` | (a) large — **unblocks 30XIV** |
| 703 | **30XIV** | `gelfand_naimark` | **(b)** on 30X.2 |

### The parsec 270 Riesz-ideal chain (8 sorries)

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

⚠ **What closing this chain actually buys.**  No `sorry` anywhere depends on
it (see the downstream section).  What it buys is *honesty*: `inv_mult_state`
(27XV, line 147) **is proved**, but its own comment at lines 150–157 records
that the hard direction is routed through Mathlib's Gelfand theory, "which
reaches the character space through maximal *ring* ideals — exactly the route
**16VIII** rejects", and that it "cannot be made honest before that chain is
proved."  27VIII–27XIII is the price of that repair.

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

**30X**.2 `proto_gelfand_naimark_2` (`cstar.tex:4951` — doc says 4870; **drift
81 lines**) — if `Ω` is centre separating then `ϱ_Ω` is injective, so `𝒜`
embeds in `B(ℋ_Ω)`.  **(a), ~250–400 lines, and much closer than it looks:**

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

## `Matrices.lean` — 4

| line | point | decl | class |
|---|---|---|---|
| 445 | **32XV**.2 | `chilb_vector_states_2` | (a) medium |
| 453 | **32XV**.3 | `chilb_vector_states_3` | (a) medium; source gives no argument |
| 1221 | **34VII** | `ccstar_pos_mat` | (a) **large — unblocks 34IX.2** |
| 1286 | **34IX**.2 | `cp_commutative_dom` | **(b)** on 34VII |

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

**34VII** `ccstar_pos_mat` (`cstar.tex:5584` — doc says 5504; **drift 80**) —
for commutative `𝒜`, matrices `∑ₖ aₖBₖ` (`aₖ ∈ 𝒜₊`, `Bₖ ∈ Mₙ(ℂ)₊`) are dense in
`Mₙ(𝒜)₊`.  **(a) but the largest item in the chapter, ~350–500 lines.**  The
thesis proof (340.80) is complete: transport `𝒜 ≅ C(X)` by Gelfand — `gelfand`
is proved at `Representation.lean:220`, and Mathlib's `gelfandStarTransform` is
the bundled `≃⋆ₐ` — cover `X` by the open sets `{y : ‖A(x) − A(y)‖ < ε}`, take a
finite subcover, build a partition of unity by complete regularity, and read off
`‖A − ∑ₖ gₖ A(xₖ)‖ ≤ ε`.  The dominant cost is not the analysis but the
*transport*: moving `Mₙ(C(X))₊` to continuous `Mₙ(ℂ)`-valued functions and back
through `CStarMatrix`.  Budget accordingly.

**34IX**.2 `cp_commutative_dom` (`cstar.tex:5643`) — a positive map *out of* a
commutative C*-algebra is completely positive.  **(b)** on 34VII: the thesis's
proof is one sentence — "By `ccstar-pos-mat` the problem reduces to `A ≡ aB`,
and `(Mₙf)(aB) ≡ f(a)B` is clearly positive" — so ~40 lines on top of 34VII.
Its sibling **34IX**.1 `cp_commutative_cod` (line 1260) is proved.

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

**1. 27VIII `riesz_ideal_ring_ideal`** (`Representation.lean:81`).
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

**2. 30X.2 `proto_gelfand_naimark_2`** (`Representation.lean:690`).
Chain-opening — it is the *sole* blocker of **30XIV `gelfand_naimark`**, the
headline theorem of the chapter, which is ~30 lines behind it.  Beats an
isolated item on two further counts: the (2)⇔(3) half is proved right above it,
and Mathlib now supplies both missing pieces of infrastructure (single-`ω` GNS,
`lp G 2` direct sum), so the residue is one construction (`ϱ_Ω` as a diagonal
operator) plus a four-line argument.  Proving it also settles whether A/VN's
**48III `gns_normal`** is still correctly classed [L] — it probably is not.

**3. 34VII `ccstar_pos_mat`** (`Matrices.lean:1221`).
Chain-opening (sole blocker of 34IX.2, closing the last CP-theory gap in the
chapter) with a complete thesis proof, but ranked third because it is the
largest single item and the payoff is faithfulness only — `normal_russo_dye`
already routed around it.

*Warm-ups, if a short session is wanted:* **24II**.3 `cstar_pos_neg_part_3`
(~40 lines, template 50 lines above it) and **15VII** `rigid_expansion`
(~80–120 lines, and it turns out not to need Goursat).

---

## What A/CStar gates downstream

**Nothing.  No declaration anywhere in `Theses/` is blocked, directly or
indirectly, on any of these 28 sorries.**

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

* `Positive.lean:156` and `:234` — doc comments mentioning `goursat`/`taylor`;
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
* **Update the five file headers.**  "Statements only; every proof is `sorry`"
  is wrong in all five files and has already produced miscounts elsewhere in
  this project.
