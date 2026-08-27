# Dead limbs

*Sweep of **2026-08-27**, commit `9a69966`, over the **whole tree** — all 49
files of `Theses/A` and `Theses/B`, 163,848 lines, 7,493 hand-written named
declarations.*

*Counts were taken at `9a69966`. Two other workers were live in the tree during
the sweep and have since touched `A/CStar/Basic.lean`, `A/CStar/TowardsVN.lean`,
`A/VN/Basic.lean` and four audit CSVs; every declaration named individually
below was re-checked against the working tree afterwards and none of them
acquired a consumer. The aggregate counts of §2 and §3 are as at `9a69966`.*

*Supersedes the sweep of 2026-08-26 (commit `e0ef561`), which covered only the
twenty files of the commutation-theorem development. That sweep's findings are
not discarded: they are restated with their current status in §10, and the six
of its limbs that have since acquired a consumer are named with the commit that
closed them in §9.*

The standing check: enumerate every declaration with no consumer, and for each
ask whether it is genuinely terminal or **the fingerprint of a proof that went
around it**. A declaration the thesis cites, which nothing consumes, is the
shape a bypassed argument leaves behind. Three repairs in the week to
2026-08-27 were found exactly that way (§9).

**Read this first.** The single number to quote is **916 declarations with zero
uses out of 7,493 — 12.2%**; of those, **169 are accessors the method cannot
see** and **512 are thesis statements whose being terminal is the point**. The
band that wants a human is the remaining **235 untagged helpers, 3,549 lines**,
and inside it the **six case-1 fingerprints named in §5**. Nothing here is
broken, nothing is `sorry`-ed beyond the eleven deliberate ones, and no headline
result is at risk.

---

## 1. Method, and what each method is blind to

A declaration is **dead** when nothing anywhere in `Theses/` uses it. Uses are
counted over the comment-stripped source of all 49 files: **a mention inside a
doc comment is not a use**, and neither is a backtick-quoted name in prose. A
declaration's own body is excluded.

This round the count is **textual**, not a Lean meta-program walk of
`env.header.moduleData` as on 2026-08-26. Both are approximations and they are
blind to different things; the choice is recorded here so the next sweep can
reproduce it.

| | Lean term walk | textual walk |
|---|---|---|
| use inside a proof term | seen | seen (the name is in the source) |
| name in `simp only [f]`, `rw [f]`, `exact f` | seen | seen |
| `@[simp]` lemma fired by a **bare** `simp` | **blind** | **blind** |
| lemma reached by `rfl`/definitional unfolding | **blind** | **blind** |
| instance found by typeclass synthesis | seen | **blind** |
| dot-notation `hγ.gram_sum_re` | seen | seen (suffix-indexed) |
| cost | ≫ 1 h, ≫ 5 GB on the whole tree | 4 s |

Three implementation traps, all of which produced wrong numbers before they
were fixed, and all of which will recur:

* **`ConstantInfo.value?` returns `none` for theorems in Lean 4.34.** Call it
  with `(allowOpaque := true)`. With the default, proof bodies are invisible and
  the first run of the 2026-08-26 audit reported 77% of the development unused.
* **`Expr.getUsedConstants` has no DAG cache**, so it is exponential on shared
  proof terms. A term walk of the whole tree does not finish in ten minutes with
  it; a pointer-cached traversal is required. This is why the whole-tree pass is
  textual and the 2026-08-26 pass, over twenty files, was not.
* **A tokeniser that is not Unicode-aware is not a tokeniser for this tree.**
  `paschkeModule_h_ρ`, `kaplansky_hilbmod_A₂'` and `onb₁` all contain
  identifier characters outside ASCII; and `aconv_coprod.{u, v}` must not
  tokenise as `aconv_coprod.`. Both bugs reported live declarations as dead in
  the first pass of this sweep — `aconv_coprod` (193V) among them.

**The textual count is conservative in the direction that matters.** A name that
appears nowhere in 163,848 lines of source cannot be used except through bare
`simp`, `aesop`, or instance synthesis. Those three exits are quarantined: the
169 accessors of §8, and the **44 dead `instance` declarations**, are reported
separately and are *not* to be deleted on the strength of this scan.

**Agreement with the 2026-08-26 Lean pass.** On the twenty files that pass
covered, the two methods agree closely: `Tomita` 11 hard zero-use both ways,
`StandardSubspace` 4/4, `ModularTensor` 4/4, `TomitaAnalytic` 3/3,
`CommutationCyclic` 2/2, `CommutationReduction` 1/1, `Commutation` 5/5,
`TensorTransport` 7 then 8, `Modular` 9 then 7. Totals over the twenty files:
**111 hard zero-use then, 119 now**, against a tree that has grown.

**What this sweep does *not* reproduce is the cone.** The 2026-08-26 pass also
computed reverse reachability from the headline theorems, which finds a
*self-supporting block whose members all have consumers and whose block has
none* — `ModularGroup.lean`'s `jConj` layer, 1 hard zero-use but 26 outside the
cone (§10b). Direct zero-use cannot see that shape and this sweep does not
claim to. Those findings stand as recorded until someone re-runs a cone pass.

---

## 2. Headline numbers

| quantity | count |
|---|---|
| hand-written named declarations in `Theses/A` + `Theses/B` | 7,493 |
| **zero uses anywhere in `Theses/`** | **916 (12.2%)** |
| — accessor class (`@[simp]`, `rfl`-proved, or `_apply`/`_coe`/`_val`/`_def`-named) | 169 |
| **hard zero-use** | **747** (21,557 lines) |
| — carrying an opening DISP tag, i.e. a thesis statement | 512 (18,008 lines) |
| — untagged helpers | 235 (3,549 lines) |
| —— of those, named by an audit row | 45 |
| —— of those, named by no row at all (*the machinery pool*) | 190 (2,111 lines) |
| dead `instance` declarations (synthesis blind spot, not scored) | 44 |

And against the thesis points rather than the declarations:

| quantity | count |
|---|---|
| thesis points carried by at least one declaration | 889 |
| — points **every** declaration of which is dead | 145 |
| — points with a dead clause **and** a live sibling | 174 |

The second row of that table is the one to look at when hunting fingerprints.
A point all of whose clauses are dead is usually a leaf of the thesis. A point
with a dead clause *beside a live one* is where a route went round a part of its
own statement — which is exactly the shape of 123I, repaired this week (§9).

Of the 512 dead thesis statements: **276 are Exercises**, **105 are called
Theorem, Proposition or Lemma**, **35 are Examples**, and **35 are refutations
or counterexamples** (`*_counterexample`, `*_is_false`, `*_not_*`). The 105 are
the interesting band — a Lemma exists in order to be used — and §5 works through
the largest of them.

---

## 3. Per-file breakdown

Hard zero-use (excluding the accessor class), with the lines they occupy.
Files with none are omitted; `CommutationTheorem`, `CommutationTomita`,
`TomitaFourier`, `WStarCat` and `Common` are fully consumed.

| file | hard | dead | total | lines |
|---|---|---|---|---|
| `A/CStar/Basic.lean` | 59 | 59 | 139 | 1,126 |
| `A/Proc/Measurement.lean` | 59 | 61 | 402 | 2,638 |
| `A/CStar/Positive.lean` | 54 | 55 | 320 | 1,358 |
| `A/VN/Projections.lean` | 44 | 57 | 313 | 1,519 |
| `A/VN/Basic.lean` | 38 | 45 | 480 | 1,181 |
| `B/Eff/StatesPredicates.lean` | 38 | 51 | 397 | 1,049 |
| `A/Proc/Tensor.lean` | 32 | 40 | 481 | 948 |
| `B/Eff/EffectAlgebras.lean` | 30 | 34 | 248 | 612 |
| `A/CStar/Representation.lean` | 27 | 28 | 119 | 628 |
| `A/Proc/QuantumLambda.lean` | 27 | 37 | 384 | 1,000 |
| `B/Dils/HilbertModules.lean` | 21 | 23 | 161 | 431 |
| `B/Dils/Paschke.lean` | 21 | 37 | 250 | 456 |
| `B/Dils/SelfDual.lean` | 21 | 29 | 355 | 1,055 |
| `B/Eff/Effectus.lean` | 21 | 23 | 262 | 262 |
| `A/CStar/Matrices.lean` | 20 | 24 | 133 | 401 |
| `B/Eff/DiamondAmp.lean` | 20 | 22 | 138 | 331 |
| `B/Eff/VNExamples.lean` | 19 | 47 | 317 | 485 |
| `A/VN/Division.lean` | 17 | 17 | 163 | 798 |
| `A/Proc/Duplicators.lean` | 15 | 15 | 135 | 714 |
| `B/Dils/SelfDualCompletion.lean` | 13 | 22 | 219 | 157 |
| `B/Dils/Stinespring.lean` | 12 | 14 | 140 | 890 |
| `B/Eff/Dagger.lean` | 12 | 14 | 136 | 326 |
| `A/VN/Tomita.lean` | 11 | 16 | 69 | 52 |
| `B/Dils/Kaplansky.lean` | 10 | 13 | 124 | 226 |
| `B/Dils/Pure.lean` | 10 | 14 | 183 | 362 |
| `B/Eff/Comparisons.lean` | 10 | 10 | 74 | 797 |
| `B/Eff/Quotients.lean` | 10 | 10 | 92 | 243 |
| `A/CStar/TowardsVN.lean` | 9 | 11 | 73 | 225 |
| `A/Proc/TensorTransport.lean` | 8 | 11 | 70 | 108 |
| `A/VN/Completeness.lean` | 8 | 10 | 174 | 275 |
| `A/VN/Modular.lean` | 7 | 10 | 73 | 45 |
| `A/VN/NormalFunctionals.lean` | 7 | 8 | 105 | 423 |
| `A/Proc/Commutation.lean` | 5 | 6 | 44 | 100 |
| `A/Proc/CornerTensor.lean` | 4 | 5 | 62 | 51 |
| `A/VN/ModularTensor.lean` | 4 | 6 | 50 | 78 |
| `A/VN/StandardSubspace.lean` | 4 | 6 | 103 | 19 |
| `A/VN/TomitaTakesaki.lean` | 4 | 6 | 72 | 53 |
| `A/VN/BaX.lean` | 3 | 4 | 17 | 39 |
| `A/VN/ModularGroup.lean` | 3 | 3 | 84 | 15 |
| `A/VN/TomitaAnalytic.lean` | 3 | 4 | 70 | 16 |
| `A/Proc/CommutationCyclic.lean` | 2 | 2 | 8 | 17 |
| `A/Proc/Compression.lean` | 2 | 3 | 50 | 17 |
| `A/Proc/CommutationAmplify.lean` | 1 | 1 | 31 | 4 |
| `A/Proc/CommutationReduction.lean` | 1 | 1 | 9 | 24 |
| `A/VN/TomitaStrip.lean` | 1 | 2 | 61 | 3 |

The two `A/CStar` files at the top of the table are not a defect and should not
be read as one. `Basic.lean` is the opening chapter: 59 of its 139 declarations
are Exercises and Lemmas of parsecs 3–8 stated for the record, and almost every
one of them is Mathlib's own fact restated in the thesis's words. That is the
purest form of case 2 in the tree.

`A/VN/BaX.lean` is new since the previous sweep (17 declarations, 3 hard dead —
`bah_vn_sup`, `vecFunctional_normal`, `bah_vn`, all clauses of 49II). It is the
youngest file in the tree and its dead fraction is the ordinary one for a file
whose consumers have not been written yet.

---

## 4. Classification

| class | count | what it is | verdict |
|---|---|---|---|
| **4 — accessor noise** | 169 | `@[simp]`/`rfl` unfolders and `_apply`-shaped lemmas | not scored; do not delete (§8) |
| **2 — genuinely terminal** | ~490 | thesis statements whose being stated *is* the deliverable: Exercises, Examples, counterexamples, headline packagings | not a defect (§6) |
| **3 — superseded machinery** | ~190 | helpers whose consumer was rewritten (the machinery pool) | deletion candidates (§7) |
| **1 — the fingerprint** | **6 diagnosed** | the thesis cites it and our proof went round it | §5 — the valuable one |

The class boundaries are not sharp and the counts of classes 2 and 3 are
estimates from the DISP-tag and audit-row signals, not a per-declaration
reading of 747 items. The class-1 list is a per-declaration reading and is
complete only in the sense that it is what the two automatic signals (a `route`
or `mild` audit row naming a point that a dead declaration carries; a dead
Lemma/Proposition/Theorem beside a live sibling) turned up and a human then
confirmed against the source.

---

## 5. Class 1 — the fingerprints

Six. For each: the dead declaration, the point whose printed argument would
consume it, and what the repair would cost. **None of these was repaired in this
sweep**; they are reported.

### 5.1 `selfdual_compl_defining_dense` (163II) — the argument written three times

`B/Dils/SelfDual.lean:5246`, 78 lines, `green`, doc-comment class **"Divergence
class 1 (faithful)"** — i.e. it is the thesis's own argument, transcribed.
Zero consumers.

The argument it contains — the orthogonal projection `P` onto `D^⊥⊥` fixes the
image, so `P` and `id` both factor `η` through itself, so the uniqueness half
of the universal property gives `P = id` — is written out a **second** time
inside `ext_tensor_dense` (**164II**.1, `SelfDual.lean:7784`), whose own doc
comment says so in as many words:

> "its place is taken by the projection argument of **163II**
> (`selfdual_compl_defining_dense`)"

and a **third** time inside `paschke_tprod_dense` (`SelfDual.lean:9224`), whose
doc says "This is the Paschke-module analogue of `selfdual_compl_defining_dense`
(**163II**) and of `ext_tensor_dense` (**164II**.1), and it is the easiest of
the three". A fourth site, the `section TensorDense` header at `:6245`, says
"exactly as in `selfdual_compl_defining_dense` (**163II**)".

So the tree contains four prose citations of one declaration and no call of it.

**Point implicated:** 164II.1, and behind it the whole `SelfDual` density
layer.

**Cost.** Not small, and this is why it happened. 163II's universal property is
stated over *bounded module maps* `V → Y`; `ExtTensor`'s is stated over
*bilinear* maps. To call 163II from `ext_tensor_dense` one must first exhibit
`E.Z` as the self-dual completion of the algebraic tensor product `V = X ⊙ Y`
with its `BInner`, i.e. derive the linear universal property from the bilinear
one (`extTensor_map_ext` plus a `tSpan`-to-`V` transfer). Estimate **80–150
lines of new bridging**, against roughly **60 duplicated lines removed at each
of two sites**. Worth doing if the bridge is wanted for anything else; not
otherwise. Recommend: **leave, and record here** — which is what this entry is.

### 5.2 `injective_nmiu_iso_on_image_2'` (48VI part 2) — the exercise's own hint, half followed

`A/VN/Basic.lean:4781`, 74 lines, `green`. The *full* form of 48VI part 2: an
injective nmiu-map restricts to an nmiu-**isomorphism** onto its image. Its own
doc comment says the sibling `injective_nmiu_iso_on_image_2` (used four times)
is "the working form of" it. Zero consumers. Four of 48VI's five declarations
are live; this one is not.

The audit row for **69IVb** `nmiu_image` (`docs/audit/avn-projections.csv`,
proof class `route`) records:

> "its hint says to use 69IVa and injective-nmiu-iso-on-image, and ours does
> neither"

**Point implicated:** 69IVb, `A/VN/Projections.lean:7089`.

**Two corrections to that row, both verified here.** (i) The row is half stale:
`nmiu_image`'s proof *does* use 69IVa — it calls `nmiu_factors`
(`Projections.lean:6935`/`:7042`) three times. What it does not use is 48VI.2'.
(ii) The dead limb is therefore precisely the unfollowed half of the hint.

**Cost.** `nmiu_image` currently proves the image is a von Neumann subalgebra
by building the corner isometry by hand — the injective star-hom
`x ↦ (f x, (1−c)x)` into `B × A`, order reflection, then closedness and
directed-sup-closedness of the range: about 150 lines. The printed route is
69IVa's factorisation `f = (restriction to the corner) ∘ (compression)` followed
by 48VI.2' applied to the injective restriction, plus `injective_nmiu_iso_on_image_1`
(which is already `isVNSubalgebra_range`) to conclude. All three inputs are in
the tree and live. Estimate **40–80 lines replacing ~150**, with a real risk in
the middle: the `Type`-level identification of `↥f.range` with the corner
carries an induced order that 48VI.2' states over `↥f.toStarAlgHom.range` while
69IVb needs it over `f.range` inside `B`. **This is the strongest of the six**
— the inputs exist, the hint is printed, and the row already admits the
divergence. Recommend: **a fixing round should take this one first.**

### 5.3 `tensor_equalisers` (125VI) — the recorded reason has expired

`A/Proc/QuantumLambda.lean:7589`, 42 lines, `green`, doc comment: **"This is
proc.tex:4980 verbatim."** Zero consumers.

The audit row for **125VIIb** `tensor_preimage`
(`docs/audit/aproc-duplicators-quantumlambda.csv`, proof class `route`) says:

> "The thesis's hint (express rho^-1(S) as a pullback in W\*_miu) routes through
> 125VI, **which is itself blocked**."

**125VI is not blocked.** `tensor_equalisers` is `green` in `docs/status.txt` —
axiom-clean, no `sorry`, direct or indirect. It became so when 125IV
`equaliser_lemma` was discharged at commit `61d6f49` ("121II and 125IV
discharged in place: seven sorries become five"). The row's stated reason has
expired and the row should be re-costed against what is *actually* missing.

**Point implicated:** 125VIIb, `QuantumLambda.lean:7635`.

**Cost, honestly.** Re-costing the row is cheap and should be done. Restoring
the route is not: what the printed hint needs beyond 125VI is the expression of
`ρ⁻¹(𝒮)` as a **pullback in W\*_miu**, and the tree has no pullbacks in
W\*_miu as such. The current proof goes through the commutation theorem instead
(slice maps, `rSlice_natural`, `mem_tensorSub_of_image` = 121II) and is sound.
Estimate for the printed route: **pullbacks in W\*_miu, several hundred lines,
a statement-level decision** — not a repair. Recommend: **re-cost the row; leave
the proof.** I have not edited the row: re-costing it is a claim about the
thesis's hint, not about the tree, and belongs to whoever owns that CSV.

### 5.4 `powerSeries_hasDerivAt` (13IV) — a Proposition with no consumer, 48 lines above its consumer

`A/CStar/Positive.lean:198`, 47 lines, `green`, the **only** declaration
carrying 13IV. Zero consumers.

**13VI** `powerseries_uniqueness_coeffients` sits at `:246` — 48 lines below
it — and its in-proof comment says:

> "the solution differentiates the series repeatedly and reads `f⁽ⁿ⁾(0) = n aₙ`
> off **13IV** `powerSeries_hasDerivAt`. (That was once justified here by
> **13IV** being `sorry`; it is proved now, and this is *not* the reason any
> more.)"

**Point implicated:** 13VI.

**Cost.** The comment then costs the repair itself, correctly: the solution's
route needs, beyond 13IV, that the **term-wise derivative series is summable on
the same disc** — the radius of the derived series, which cstar.tex:1949 asserts
in passing — plus an induction producing the `n`-th derivative. 13IV delivers the
derivative only as a `tsum`. Estimate: a derived-radius lemma plus the
`n`-fold iteration, **120–200 lines**, against the 12-line
`HasFPowerSeriesAt.eq_zero` route in place. This is a genuine class-1
divergence with a fair reason already written down; the limb is the price.
Recommend: **leave**. It is here because a reader of the file should be told
that 13IV's only purpose in the thesis is a proof the tree does not run.

### 5.5 `selfDual_pi` (36III) — named as available by the row that leaves the divergence standing

`A/CStar/TowardsVN.lean:289`, 39 lines, `green`, the **only** declaration
carrying 36III. Zero consumers.

The audit row for **153IV** `hilbmod_adj_vector_ncp`
(`docs/audit/bdils-hilbertmodules-selfdualcompletion.csv`, `weaker`/`route`)
says:

> "of the three theorems it named as missing, one is NOT missing — cstar 36III
> `Theses.A.CStar.selfDual_pi` makes `A^n` a self-dual Hilbert A-module and is
> on the import path, modulo a short transfer between A/CStar's `SelfDual`
> (boundedness = `Continuous`) and 141IIa's (boundedness = `∃ C`). The other
> two, `Bᵃ(Aⁿ) ≅ Mₙ A` and `Bᵃ(A) ≅ Aᵒᵖ`, are genuinely absent."

**Point implicated:** 153IV.

**Cost.** The row costs it. The transfer between the two `SelfDual`
definitions is short — **20–40 lines** — but closing the limb needs all three
inputs, and two of them are genuinely absent (`Bᵃ(A) ≅ Aᵒᵖ` exists only
downstream as `rightMulEquiv` in `Paschke.lean`, which *imports* this file, so
it cannot be used here without moving it). Against a self-contained 140-line
computation, the row concludes "class 2, LEFT" and that is right.
Recommend: **leave**. Recorded so that nobody re-derives `selfDual_pi` a second
time under a different name.

### 5.6 `vanishing_effects` (44III) — the thesis's hint at two sites, followed at neither

`A/VN/Basic.lean:1890`, 55 lines, `green`. Zero consumers. Its shared estimate
`norm_apply_mul_le_of_nonneg` (`Basic.lean:170`, doc: "The estimate behind
**44III** and **44VII**") *is* consumed, so what is dead is the packaged Lemma.

**Two proofs declare in their own comments that they are going round it.**

**44VII** `vna_supremum_mult`, ninety lines below it in the same file
(`A/VN/Basic.lean:1982`):

> "The thesis's hint is to use `vanishing_effects`; concretely we use the
> estimate behind it, `|ω((⋁D−d)a)| ≤ ω(⋁D−d)^½ ω(a*(⋁D−d)a)^½`, whose second
> factor is *eventually* bounded because `a*(⋁D−d)a` decreases."

**166II** `ultranorm_continuity_ext_tensor` (`B/Dils/SelfDual.lean:8899`):

> "**166III** is the proof; transcribed below, with its appeal to **44III**
> `vanishing_effects` replaced by the order estimate `Ω(⟨d,d⟩ ⊗ ⟨yα,yα⟩) ≤ M² ·
> Ω(⟨d,d⟩ ⊗ 1)`"

**Points implicated:** 44VII and 166II. A Lemma cited as the route by two
proofs and called by neither is the cleanest instance of the pattern this check
exists for; it is listed sixth only because the verdict goes the other way.

**Cost, and why it should not be paid.** Both substitutions are deliberate and
both are *improvements*. 166II's comment explains that 44III's vanishing net
must consist of **effects**, which is why the thesis needs both norm bounds,
while the order estimate needs only one — so 166II's `hxb` is genuinely unused
and the lemma is true with either bound. 44VII's substitution replaces a
uniform bound with an eventual one. Restoring 44III's use at either site means
re-imposing a hypothesis and **weakening the tree's statement** to match the
printed route. Recommend: **leave; do not repair.** Recorded so that a future
sweep does not rediscover 44III as an open question, and so that nobody
"repairs" it into a weaker theorem.

### Shortlist — not yet read, same two signals

These are dead Lemma/Proposition/Theorem statements with a **live sibling** on
the same point, which is the 123I shape. Each is worth twenty minutes; none has
been checked against the printed argument.

| point | declaration | file:line | lines | live siblings |
|---|---|---|---|---|
| 118II | `cceil_tensor` | `A/Proc/Tensor.lean:9748` | 134 | 1/2 |
| 81IX | `div_usc_ball` | `A/VN/Division.lean:2975` | 114 | 4/5 |
| 106I | `uniqueness_sequential_product_exists` | `A/Proc/Measurement.lean:8611` | 79 | 1/3 |
| 4XIII | `positive_2x2matrix_2` | `A/CStar/Basic.lean:284` | 67 | 1/2 |
| 82I | `polar_decomposition_2` | `A/VN/Division.lean:3446` | 55 | 3/4 |
| 156II | `paschke_injective` | `B/Dils/Paschke.lean:3551` | 48 | 2/3 |
| 160IV | `hilbmod_projthm_3` | `B/Dils/SelfDual.lean:1387` | 45 | 2/3 |
| 96III | `ncp_uwlim_2` | `A/Proc/Measurement.lean:1797` | 39 | 2/3 |
| 23II | `sqrt_lemma_monotone` | `A/CStar/Positive.lean:5708` | 35 | 3/6 |
| 154III | `existence_paschke_2` | `B/Dils/Paschke.lean:1406` | 32 | 13/14 |

`existence_paschke_2` was read and is **not** a fingerprint: it is 154III part
2's uniqueness clause, and its content is already reachable structurally through
`M.univ` and `M.ρ_tprod`, both of which are used. It is a terminal repackaging.
`div_usc_ball` was read and is the sound first clause of 81IX, terminal by
intent (§6). The other eight are unread.

---

## 6. Class 2 — genuinely terminal

Roughly 490 of the 747, and the great bulk of the count. Not a defect. The four
recurring shapes:

* **The Exercise or Example stated for the record.** 276 dead statements have
  "Exercise" in their opening doc line and 35 have "Example". `A/CStar/Basic`'s
  `boundedOperators_basic_{1,2,3}`, `uniqueness_adjoint_{1,2}`,
  `isAdjointTo_{add,smul,comp}`, `inner_product_basic_{2,3,4}` are the type: the
  thesis's exercises of parsecs 4–5, each a Mathlib fact in the thesis's words,
  each complete in itself.
* **The refutation.** 35 dead statements are counterexamples or explicit
  falsity claims — `tensor_simple_facts_4_counterexample` (133 lines),
  `equivalent_examples_2_is_false`, `omega_norm_basic_2_counterexamples`,
  `vn_counterexamples_{3,6,11}`. Their whole purpose is to be stated. The four
  `kaplansky_hilbmod_A{₁,₁',₂,₂'}` in `B/Dils/Kaplansky.lean` are the sharpest
  case: they carry four of the tree's eleven deliberate `sorry`s and exist to
  record that 158V, the thesis's printed route, is **false**.
* **The headline packaging over a working `_aux`.** `stinespring` and
  `stinespring_unital` (135IV) are nine and twelve lines over `stinespring_aux`,
  which has three consumers. `continuous_measure_space` (129VIII) is a six-line
  specialisation of `continuous_measure_space_subset`, which has two.
  `cvn_linfty` (70III) is the existential packaging of the `cvn` /
  `cvn_direct_sum` / `exists_linftyPresentation` layer, all live — and its own
  doc says so ("`cvn` above is left as it stands — it is destructured at
  `A/Proc/Duplicators.lean:4038`"). The Theorem as the thesis states it is the
  deliverable; the aux is what proofs want.
* **The clause the tree cannot connect because the surrounding notion is
  absent.** All nine `vn_smc_*` declarations for **119V** (253 lines:
  `associator_natural`, `braiding_natural`, `leftUnitor_natural`,
  `rightUnitor_natural`, `pentagon`, `triangle`, `unitors_agree`, `hexagon`,
  `symmetry`) are dead as a block. The audit row for 132III explains it: "the
  isomorphism `Mon(W*_miu) = dW*_miu` is not stated (no categories in the
  tree)". The coherence conditions are stated and proved; nothing can consume
  them until W\*_miu is a `Category`. **Not a fingerprint** — this is the
  statement-level decision recorded at 132III, and it is 253 of the 18,008
  lines in the DISP-tagged band.

Two more, both named in the brief for this sweep and both confirmed terminal
here:

* **`emond_lemma_for_conv` (178V)**, `B/Eff/EffectAlgebras.lean:3232`, 18 lines.
  Dead. It is the `Fin n` form over the live `emond_lemma_for_conv_list`, and
  the one place the theses cite it — 194I.4 `AConvMCat.coprod_inl_injective` —
  is itself left under a costed machinery reason. Cannot be closed until that is.
* **`paschke_pure` (171VII)** is **no longer dead** — see §9.

---

## 7. Class 3 — superseded machinery, and what was deleted

**190 declarations, 2,111 lines**: untagged (no thesis point in the doc
comment), unrowed (no audit row names them), not accessors. This is the
deletion pool. Its largest members:

| lines | declaration | file:line |
|---|---|---|
| 119 | `paschkeModuleId` | `B/Dils/Paschke.lean:2190` |
| 112 | `PhiCompatible.mul_right` | `B/Dils/Paschke.lean:317` |
| 48 | `concreteTensor_top_cancel` | `A/Proc/Commutation.lean:565` |
| 46 | `conj_ncp_eq_of_le_proj` (private) | `A/Proc/Measurement.lean:3485` |
| 46 | `concreteTensor_top_top` | `A/Proc/TensorTransport.lean:661` |
| 38 | `paschke_rho_forces_cyclic` | `B/Dils/Paschke.lean:521` |
| 36 | `IsCompatExt.norm_ipVal_self_le` | `B/Dils/SelfDualCompletion.lean:1636` |
| 34 | `cyclic_and_separating_of_separating` | `A/Proc/Commutation.lean:475` |
| 34 | `op_smul_comm_complex'` | `B/Dils/SelfDualCompletion.lean:1057` |
| 33 | `modularSqrt_orbit` | `A/VN/ModularTensor.lean:1130` |
| 32 | `paschke_inner_conj_forces_zero` | `B/Dils/Paschke.lean:488` |
| 31 | `npFunctional_tendsto_of_isLUB` | `B/Dils/Paschke.lean:870` |

By file: `B/Dils/SelfDualCompletion` 28, `B/Dils/Paschke` 16,
`B/Eff/StatesPredicates` 15, `A/Proc/QuantumLambda` 13, `B/Eff/EffectAlgebras`
11, `A/VN/Tomita` 11, `A/Proc/TensorTransport` 10, `A/CStar/Positive` 10.

### Nothing was deleted in this sweep, and the reason is operational

1. **Two workers hold the same files.** One is adding declarations in
   `A/CStar` and `A/VN`; one is verifying `differs`/`stronger` audit rows. The
   pool is spread across exactly those files.
2. **Confirming a class-3 deletion requires a compile**, and compiling any of
   these files rebuilds oleans that both workers are reading. A bare `lake
   build` is forbidden here for the same reason.
3. **A deletion is not one edit.** `scripts/audit_check.py`'s phantom check
   reads 2,486 audit rows; each deletion has to take its row with it in the same
   edit, and thirteen phantom rows were found on 2026-08-26 left behind by
   exactly this omission.

So the pool is *recorded*, not spent. A fixing round with the tree to itself can
take it in one pass, file by file, deleting and re-running
`python3 scripts/audit_check.py` after each.

**Two items in the pool are not deletable and should be moved out of it by
hand:** `cyclic_and_separating_of_separating` and `CT_iff_vnComm` were
individually diagnosed on 2026-08-26 (§10) as retraction casualties with a
recorded reason; they carry no DISP tag, so the automatic filter puts them in
the pool, but the earlier reading stands.

**Two more dead declarations are class 3 by their own doc comment but carry a
DISP tag, so they stay:**

* `atomicTypeI_tensorBsurjectivity` (**125eIII**), `A/Proc/QuantumLambda.lean:5544`.
  Its doc now reads: the `←` half "was the one open at the time and **is now
  proved in general at the end of this file** (`tensorBsurjectivity`), from
  125VIIb `tensor_preimage`." Superseded by its own general form, exactly as the
  brief for this sweep reported. Both it and `atomicTypeI_tensor_preimage`
  (**125VIIb**) remain the tree's only record of the atomic-type-I case *as a
  case*. DISP-tagged, so not noise: **leave and report**, and retiring them
  stays a statement-level decision for the author (§10a).
* `ultranormcontstruct_add_unTendsto` (**148III** part 1, net form),
  `B/Dils/HilbertModules.lean:1842`. Its doc comment already withdraws its own
  justification: "The claim that used to stand here — 'kept because it is the
  form the net arguments of parsec 1490 use' — is **false**: parsec 1490's Lean
  proofs go through `unSeminorm_add_le` and `unSeminorm_inner_le` directly, and
  this form has no consumer." Confirmed dead here. DISP-tagged: **leave and
  report.** It is the cleanest deletion candidate in the tree the moment an
  author ruling permits removing a stated clause of 148III.

---

## 8. Class 4 — accessor noise

**169 declarations tree-wide** (40 of them in the twenty files the 2026-08-26
sweep covered, where it counted 45). These are `@[simp]`/`rfl` unfolders and
`_apply`/`_coe`/`_val`/`_def`-shaped lemmas: 128 carry `@[simp]`, 69 are proved
by `rfl` or `show …; rfl`, 112 are named in the accessor style.

**Neither method can see whether these are used.** A definitional rewrite leaves
no constant behind, and a bare `simp` names nothing for a textual scan to find.
The 2026-08-26 sweep compile-tested two of them — `extOut_apply` and
`htKetR_apply` — and found both load-bearing. `extOut_apply` now has an explicit
consumer (`A/Proc/Compression.lean:428`) and so has left the class; `htKetR_apply`
still shows zero textual uses and is still live through bare `simp`. That is the
whole argument for the quarantine, in one pair of declarations.

The style has a real cost, and it is not the dead lemmas: proofs that discharge
goals by `show …; rfl` against definitional unfolding break the moment a
definition becomes irreducible. The one place where this matters is recorded at
§10, `Defeq fragility`.

**Do not churn this class.** Reported; not counted as dead; not to be deleted on
the strength of any usage scan.

Add to it the **44 dead `instance` declarations**, which the textual method
cannot see at all because typeclass synthesis mentions no name in the source.
The Lean term walk *can* see those; a future cone pass should re-check them.

---

## 9. Previously recorded limbs that have since been closed

Six, all verified against the tree at `9a69966` and all named with the commit
that gave them a consumer. **These are recorded rather than dropped**: several
standing observations in this project have turned out to be stale claims about
our own work, and the record of a closure is worth as much as the record of a
limb.

| limb | point | closed by | consumer |
|---|---|---|---|
| `hilb_tensor_basic_2` | 109IV.2 | `49a49f0` | 110III's proof, `A/Proc/Tensor.lean:679` |
| `triple_tensor` | 119II | `49a49f0` | 119IV `isTensorProduct_assoc`, `Tensor.lean:10799` |
| `perp_sharp_is_orth` | 213III | `49a49f0` | `B/Eff/Comparisons.lean:600` |
| `ultranormcontstruct_smul` | 148III.3 | `027dc77` | `ext_tensor_dense` (164II.1), `B/Dils/SelfDual.lean:7828` |
| `dagger_of_iso_adjoint` | 216IX.1 | `0f036ad` | `B/Eff/Dagger.lean:528` |
| `paschke_pure` | 171VII | `7aa3dc0` | `pure_iff_stinespring_surjective`, `B/Dils/Pure.lean:4229` |

Three of these overturn a claim recorded in this file or in the brief for this
sweep, and each overturning is the point of the check:

* **`hilb_tensor_basic_2` (109IV.2)** was "the one transcription in
  `Tensor.lean` with no consumer" (PROVING-LOG, session 94), because 110III kept
  the density route. It is now consumed by 110III's own proof at
  `Tensor.lean:679` — the orthonormal-basis argument the thesis prints.
* **`triple_tensor` (119II)** was recorded as "the one left with its consumer
  missing" and as needing "a **trilinear** analogue of 114II … some 1300 lines".
  It is consumed at `Tensor.lean:10799`, where 119IV obtains `γ₃` from it
  directly. The 1,300-line estimate was not needed.
* **`ultranormcontstruct_smul` (148III.3)** was a long-standing dead limb, and
  the brief for this sweep expected it to be *genuinely unconsumable* — its
  natural consumer `unClosure_op_smul` closes under `x ↦ x·b` (148IV) rather
  than `b ↦ x₀·b` (148III.3). It has a consumer anyway, and not the expected
  one: `ext_tensor_dense` (164II.1) uses it for the `bSpan D ⊆ unClosure D`
  step, which its doc calls "the 'see `ultranormcontstruct`' of dils.tex:5165
  itself".

Also confirmed closed or absent, from the 2026-08-26 §7 list:

* `vnAdJ_one` — **deleted** at `e0ef561`, as §7 recorded. Absent from the tree.
* `extOut_apply` — has an explicit consumer at `A/Proc/Compression.lean:428`.
* `l2_tensor`, `orthonormal_basis_iff_l2_iso`, `hilb_tensor_unique`, `div_uwc`,
  `div_uwc_corner` — all consumed; the session-94 zero-consumer list for
  `Tensor.lean` and the `Measurement` neighbourhood is now empty except for the
  terminal `hilb_tensor_unique` (110V), which has four consumers.
* `IsHilbertTensorProduct.gram_sum_re` — five consumers, all by dot-notation
  (`hγ.gram_sum_re`). This is the one PROVING-LOG warned about; a scan that does
  not index dotted suffixes reports it dead, and the first pass of this sweep
  did exactly that before the tokeniser was fixed (§1).

And two from the brief that are **still dead**, as expected:

* `atomicTypeI_tensorBsurjectivity` and `atomicTypeI_tensor_preimage` — §7.
* `ultranormcontstruct_add_unTendsto` — §7.

---

## 10. The 2026-08-26 commutation-development findings, restated

Carried forward with their status at `9a69966`. Nothing below was re-derived by
this sweep's method except where a status is given.

### 10a. `QuantumLambda.lean` — the atomic-type-I island, 813 lines. **Unchanged.**

Commit `a992c23`. `atomicTypeI_tensor_preimage` and
`atomicTypeI_tensorBsurjectivity` are character-for-character the conclusions of
`tensor_preimage` (`:7635`) and `tensorBsurjectivity` (`:7694`) **with an extra
hypothesis**; both general statements were later proved outright through 121II
and go round the `atE` device entirely. **Both confirmed dead here.** Superseded,
not orphaned: it was the right thing to build when the commutation theorem was
still open. Of the 1,199-line commit, ~210 lines (`BKUnits`) and 147
(`uwTendsto_of_isLUB`, `uw_compress_tendsto`, since relocated to `Tensor.lean`)
are load-bearing; the other 68% is unreachable. *Largest single item in this
document.* Retiring it is a statement-level decision for the author.

### 10b. `ModularGroup.lean` — the `jConj` layer, ~300 lines. **Cone finding; not re-derivable here.**

Twenty-six declarations recorded as outside the cone of every headline theorem
while every member has a consumer inside the block. This sweep's method counts
direct uses only and therefore sees the block as live (`jConj` alone has 33
uses); it finds exactly **one** hard zero-use declaration in the file,
`jConj_modPow` (`:1057`) — which is the single hard zero-use the 2026-08-26
per-file table also reports. The two methods agree where they can and the cone
finding stands unverified until a cone pass is run again. The module docstring
still advertises `jConj_cpowOp`, `J_modPow` and `jConj_modPow` as **main
results**; `jConj_cpowOp` and `J_modPow` have one use each, `jConj_modPow` none.

### 10c. `TensorTransport.lean` — two clusters. **Partly closed.**

Cluster 1, the `CT_top_*` family: `CT_top_right` now has **2** consumers and
`tensorGen_vnComm_top` **1**; `CT_top_left`, `CT_top_top` and `mem_vnComm_top`
remain dead. Superseded and harmless to keep — readable special cases with short
proofs, now subsumed by `commutation_theorem`.

Cluster 2, `cornerTransfer` (`:811–922`, ~130 lines): **no longer an orphan by
direct count** — `cornerTransfer` has 4 consumers, `adjoint_cornerTransfer` and
`isUnitaryCLM_cornerTransfer` 3 each, `uconj_cornerAlg` and
`cext_cornerTransfer_cmpr` 2 each, `CT_cornerAlg_congr` 1. Only
`CT_of_CT_corner_any` (`:906`) is dead. The 2026-08-26 reading — that this is a
self-supporting island nothing outside consumes — is a cone claim and is not
contradicted; it is not confirmed either.

### 10d. `QuantumLambda.lean` — the one-sided `tensorSub_inf` chain, ~106 lines. **Unchanged.**

`tensorSub_inf` (`:6633`), `tensorSub₂_mono` (`:6229`) and
`tensorSub_inf_of_intersection_tensor` (`:6495`) all confirmed dead. Superseded
by the **two-sided** form: 125IV consumes
`tensorSub₂_inf_of_intersectionTensorStatement` (`:6714`, 1 use), because its
intersection `(𝒜̃ ⊗ B(ℋ)) ∩ (𝒜 ⊗ 𝒞)` varies in both factors.
**`tensorSub_inf`'s own docstring is still false** where it says "it is what
125IV `equaliser_lemma` consumes". It was orphaned inside its own commit.

### 10e. The `section Package` pattern — the structural finding. **Mostly unchanged.**

> A worker finishes a file, wraps a complete-looking API around it, and the next
> worker downstream works at the raw layer instead.

The `ModularTensor` `Δ^{1/2}` package: `opTensor_mem_modularSqrt_domain`
(`:1082`), `modularSqrt_orbit` (`:1130`), `modularSqrt_hasCore_orbitSpan`
(`:1209`) and `modularSqrt_htmul_pkg` (`:1223`) confirmed dead;
`modularSqrt_opTensor` (`:1096`) now has 1 use and `modularSqrt_htmul`
(`:1113`) 2, so the chain is no longer dead end to end. The diagnosis stands and
is sharper than "unused": `Tomita.lean`'s package ships its own
domain-membership dischargers and `ModularTensor.lean`'s ships none, so a
consumer of `modularSqrt_htmul_pkg` must drop out of the package vocabulary to
produce its hypothesis. **Had the package been used even once, that gap would
have closed.**

*Cost of this block: low.* `orbitSpan_hasCore_tensor` (`:748`, ~150 lines), the
expensive part, is consumed inside `tensor_factorisation`'s own proof.

The smaller instances of the same shape, all re-confirmed dead here:
`HasCyclicSeparating.hasCyclic`, `hasCyclicSeparating_of_dense_orbit`,
`hasFinCyclic_of_cyclic`, `mem_vnComm_of_forall`; the mirror pairs
`b_real_symm`/`b_b_apply`, `unitary_add_I_smul`/`unitary_sub_I_smul`,
`normFst_mul`/`normSnd_mul`; and `standardSubspace_toClosedSubmodule`
(`Tomita.lean:508`). Of the two `StandardSubspace` upstreaming wrappers,
`stdConj` now has 5 uses and `standardSubspace` 1; only the accessors
(`stdConj_apply`, `Jequiv_apply`) remain dead, i.e. class 4.

### 10f. Individually diagnosed items — status

| item | 2026-08-26 verdict | status at `9a69966` |
|---|---|---|
| `tomita_JM'J_unconditional` | terminal by intent; the general fact was proved locally | still dead, unchanged |
| `vnAdJ_one` | strictly redundant — **deleted** | absent from the tree |
| `sepSet_subset_Ksub` | orphan | still dead |
| `CT_iff_vnComm` | orphan, and the docs oversold it | still dead |
| `cyclic_and_separating_of_separating` | the sharpest retraction casualty | still dead |
| `IsCommutingPair.symm` | cannot be used as written | short name is `symm`; the textual method cannot separate it from Mathlib's. Unresolved; needs a term-level check |
| `concreteTensor_inf_le_inf`, `tensorSub₂_mono` | superseded | both still dead |
| Defeq fragility | the one place a reroute is advisable | unchanged; see §8 |

`101IV.2`, `101VIII.2` and `101IX` (`diamond_suprema_2`,
`diamond_composition_2`, `diamond_sum`) are all still dead, as recorded in
PROVING-LOG session 94: parts *1* of both are used heavily, these are numbered
exercise parts whose statement is the deliverable, and 118IV's note that the
printed route would use `diamond-suprema` and `diamond-composition` does not
make them the fingerprint the check is after. Left, recorded, re-confirmed.

---

## 11. If given a fixing round, in this order

1. **§5.2, `injective_nmiu_iso_on_image_2'` / 69IVb.** The only case-1 item all
   of whose inputs are in the tree and live, with the hint printed and the
   divergence already admitted in its own audit row. 40–80 lines replacing ~150.
   Fix the row's "does neither" in the same edit — it does use 69IVa.
2. **§5.3's row, not its proof.** Re-cost the 125VIIb row: 125VI is `green`
   since `61d6f49` and "which is itself blocked" is stale. Cheap, and it
   unblocks nothing but stops the next reader inheriting a false reason.
3. **§7's pool, file by file, with the tree to yourself.** 190 declarations,
   2,111 lines. Delete and re-run `scripts/audit_check.py` after each file. Do
   not start this while another worker holds `A/CStar` or `A/VN`.
4. **A cone pass**, to re-decide §10b and §10c cluster 2, and to check the 44
   dead instances that the textual method is blind to. Budget an hour of compute
   and use a pointer-cached constant walk (§1).
5. **§5.1, the three copies of 163II's projection argument.** Only if the
   linear-from-bilinear bridge is wanted for something else as well.
6. **Leave §5.4, §5.5, §5.6, §6 and §8 alone.** Each has a written reason, and
   in the case of §5.6 the repair would weaken the statement.

---

## 12. Changes applied in this sweep

**None to the tree.** No declaration was deleted, no statement changed, no
`sorry` added or removed (the count stands at eleven, all deliberate), and no
audit row edited. The two row corrections this sweep found — 69IVb's "ours does
neither" and 125VIIb's "125VI … is itself blocked" — are reported in §5.2 and
§5.3 and left for whoever re-costs those rows, because both are claims about the
theses' printed arguments rather than about the tree.

`scripts/audit_check.py`: all five checks at 0. `scripts/coverage.py`: 669/669
claims, 64/64 mixed.
