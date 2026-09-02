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
| dot-notation `hγ.gram_sum_re` | seen | seen (indexed over every dotted run — §7b) |
| cost | ≫ 1 h, ≫ 5 GB on the whole tree | 4 s |

Seven implementation traps, every one of which produced wrong numbers before
it was fixed, and all of which will recur.  The first three are about reading
the *source*; the next three (added by §7c) are about reading the *audit*, the
*tags* and the *extent of a declaration*; the last is the dotted-run rule §7a
and §7b arrived at:

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
* **A row filter that reads only `lean_name` does not know what the audit
  names.** An audit row names declarations in its free-text `note` and `status`
  fields as well as in `lean_name`, and one such note is a keep ruling in as
  many words ("removing them would be a statement change, so they are reported
  here rather than deleted", 228II). **Eight** declarations were held out of
  the §7c round by this alone, and no check in this repository would have
  reported the rows those deletions falsified. Index the whole row. See §7c.
* **The DISP-tag regex cannot read a parenthesised sub-clause.**
  `\d{1,3}[a-z]?[IVXL]+(?:\.[0-9a-z]+)?` matches `189aII.3` inside
  `**189aII.3(a)**` and then demands the closing `**`, so a tagged declaration
  reads as untagged. `scripts/audit_check.py` shares the defect, which is why
  its *unrowed* check passes on two declarations that open with a DISP tag no
  row names. See §7c.
* **The extent of a declaration begins before its doc comment.** A backward
  walk that skips attributes and `omit`/`open`/`variable … in` modifiers first
  and the doc block second stops at the doc block; the `omit … in` above it is
  left behind and attaches itself to whatever command comes next. That is how
  one of §7c's 40 deletions broke `A/Proc/CommutationReduction` at its
  `end Cyclic`, 259 lines further on. The walk must RESUME after the doc block.
* **A use is any contiguous run of dotted components, not a suffix of the
  token and not a prefix of it.** `hW.norm_ipVal_self_le` needs the suffix
  (§7a); `le_vnComm_comm.mpr` and `summable_diagTerm.hasSum` need the prefix,
  because a projection *out of* a theorem's conclusion puts the name it needs
  first; and `hΩ.centralProj.conj` and `h.isStarProjection.isIdempotentElem`
  need a run that is neither. Index `Foo.bar.baz` under all six of `Foo`,
  `Foo.bar`, `Foo.bar.baz`, `bar`, `bar.baz`, `baz`. Indexing suffixes alone
  reported **25 live declarations as dead** on 2026-08-27, `le_vnComm_comm`
  among them — the Galois connection the commutation theorem's proof runs on.
  A cone pass over compiled terms found the same 25 independently and agrees.
  See §7b.

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

*Snapshot of the sweep (2026-08-27) and not maintained since.*  85 declarations
were deleted by §12a–§12c and five more by §12d, and §5.7 and §13 correct
several of the classifications below; where this table and a later section
disagree, the later section is the one that was checked.

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

### 5.1 `selfdual_compl_defining_dense` (163II) — **the premise was wrong: the
projection argument is ours, and the thesis prints it at none of the three
points**

> **Corrected 2026-08-27, after acting on it.**  This was §11's item 5.  It
> does not survive reading `dils.tex`, and the correction runs the opposite
> way to §5.2's: there the *finding* was wrong, here the *diagnosis* is.
>
> **The four prose citations are ours, not the thesis's.**  `dils.tex` cites
> `selfdual-compl-defining` exactly once, at **164IX** (dils.tex:5300), and
> what it cites is the *uniqueness* half — "with the same reasoning as in
> `selfdual-compl-defining`".  The tree honours that: 163I
> `selfdual_compl_defining_unique` is live — `paschke_tensor_module` (167I)
> calls it (`SelfDual.lean:10537`).  The dead limb is the *moreover*-clause, and the
> argument the four citations name is printed at none of its three sites:
>
> * **163III** (dils.tex:4959-4990), 163II's own proof, runs no projection
>   argument.  It compares `X` with the **150II** completion, whose image is
>   dense by construction, obtains mutually inverse `U`, `W` from the two
>   universal properties, and transports the density along the surjective
>   ultranorm-continuous `U`.  No `D^⊥⊥`, no **160IV**.
> * **164II**.1's proof is one sentence (dils.tex:5311): "Property 1 … follows
>   immediately from the fact that the exterior tensor product is unique up to
>   an isomorphism which respects the embeddings" — the same transport, with
>   **164IX** as the comparison.
> * `paschke_tprod_dense` transcribes no thesis point at all; its own row has
>   said so since the 2026-08-26 route pass.
>
> So this is not the class-1 shape.  The thesis does not cite the dead
> declaration anywhere, and the two re-derivations are not re-derivations of
> what it does cite.
>
> **The recorded repair, re-costed.**  The duplicated block is **22** lines at
> 163II (`SelfDual.lean:5290-5311`), **29** at `ext_tensor_dense` and **20**
> at `paschke_tprod_dense` — **71** in all, not "roughly 60 removed at each of
> two sites".  The linear-from-bilinear bridge is about **100** lines: the
> linear `η̃ = extLift E.η` and its four module-map facts (~15), its
> `extBInner`-preservation (~20), and the transfer of the universal property
> (~60), which is not routine — `((a·x) ⊗ (b·y)) ⊗ 1` and `(x ⊗ y) ⊗ t a b`
> are equal only *modulo the degenerate inner product*, so the bilinear datum
> for `ExtTensor.univ` has to be extracted through the null-vector step
> `‖T v‖ ≤ C‖v‖_B = 0`.  **It has exactly one customer**: Paschke's universal
> property is over a different `BInner` (`ptensBInner φ` on `𝒜 ⊙ ℬ`) and would
> need a second bridge of its own, for a 20-line saving.  And it buys no
> faithfulness, because 163II is not what the thesis cites at either site.
> **Verdict: do not build it.**
>
> **What was done instead.**  `ext_tensor_dense` (**164II**.1) now runs the
> thesis's own proof, dils.tex:5311: `extTensorOfCompl` names the `ExtTensor`
> carried by the **150II** completion of `(X ⊙ Y) ⊙ 𝒞` — for which the density
> is the completion's own `dense` field, modulo 164VII's `bSpan`-to-`unClosure`
> step, extracted as `extTensor_bSpan_unClosure` — and **164IX**
> `ext_tensor_uniqueness` carries it to an arbitrary `ExtTensor`, exactly, the
> comparison map preserving the inner product and hence the ultranorm
> seminorms.  **Measured**: the 29-line projection block is gone and
> `ext_tensor_dense`'s own proof is 29 lines; the model costs four private
> declarations (`extTensorOfCompl`, `_eta`, `_dense`, `exists_extTensor_dense`)
> and the extracted `extTensor_bSpan_unClosure`, whose *new* text is about 60
> lines — the other 108 lines of them are moved, not written.  `SelfDual.lean`
> grows **10 755 → 10 871**, +116, of which about 60 lines are doc comment
> (this correction is written into three of them); the code delta is about
> **+56 against 29 removed**.  `hX`, `hY` are used at last, so the file's
> `set_option linter.unusedVariables false` suppression is gone.  The row moves
> `route` → `faithful`, and its recorded reason (that property 1 needs the
> unbuilt `ℓ²((pᵢⱼ))` construction) was false: 164VII proves property 1 for the
> thesis's *own* model only, and point 100 is what proves it for an arbitrary
> one.
>
> **The limb stays dead, and it moves to §6.**  163II's moreover-clause has no
> consumer left to gain: at the one site where the printed transport is
> available the tree now runs it *directly*, without 163II; and 163II itself
> cannot run it, for a reason that is neither a shortcut nor an omission but a
> universe restriction — `dils_completion B` yields a
> `SelfDualCompletion.{u, v, max u v}`, carrier in `Type (max u v)`, while
> 163II's `huniv` quantifies over codomains in `Type v` only, so the comparison
> map cannot be formed.  Its own doc comment and audit row, which both claimed
> "class 1 (faithful), the thesis's argument is exactly this one", are
> corrected.
>
> One erratum came out of the reading: **163III**'s last three sentences
> quantify over `X` where they mean `V`, and join the inner-product display to
> the density claim with an "As …, we know …" that is not an implication.
> Filed in `ERRATA.md` as a nit.

*Original section follows, retained because it is what the correction is
against:*

`B/Dils/SelfDual.lean:5246`, 78 lines, `green`, doc-comment class **"Divergence
class 1 (faithful)"** — i.e. it is the thesis's own argument, transcribed.
Zero consumers.

The argument it contains — the orthogonal projection `P` onto `D^⊥⊥` fixes the
image, so `P` and `id` both factor `η` through itself, so the uniqueness half
of the universal property gives `P = id` — is written out a **second** time
inside `ext_tensor_dense` (**164II**.1, `SelfDual.lean:7948`), whose own doc
comment says so in as many words:

> "its place is taken by the projection argument of **163II**
> (`selfdual_compl_defining_dense`)"

and a **third** time inside `paschke_tprod_dense` (`SelfDual.lean:9863`), whose
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

### 5.2 `injective_nmiu_iso_on_image_2'` (48VI part 2) — **NOT a fingerprint;
this section's premise was wrong**

> **Corrected 2026-08-27, after acting on it.**  This was §11's *first*
> recommendation and it does not survive reading the source.
>
> `injective-nmiu-iso-on-image` (`vn.tex:1119`) is one Lemma with **two**
> conclusions: (a) `f(𝒜)` is a von Neumann subalgebra, and (b) `f` restricts
> to an nmiu-isomorphism onto it.  **69IVb asks for (a) only** — `vn.tex:3637`
> reads "Use this, and `injective-nmiu-iso-on-image`, to show that `f(𝒜)` is a
> von Neumann subalgebra of `ℬ`".  That is `injective_nmiu_iso_on_image_1` /
> `isVNSubalgebra_range`, which the proof *does* use.  The dead limb is (b),
> the terminal second conclusion, which yields neither closedness of the range
> nor that its suprema are computed in `ℬ` — so **no proof of 69IVb can spend
> it**.  It belongs in §6 (genuinely terminal), not here.
>
> Two further corrections.  The row's staleness is smaller than claimed below:
> `nmiu_image` calls 69IVa `nmiu_factors` **once** (`Projections.lean:7013`);
> the "three times" counted the whole file, two of them inside
> `nmiu_factors_maps`.  And the universe obstacle binds **wider** than
> recorded: `isVNSubalgebra_range` and the three auxiliaries its proof calls
> (`starAlgHom_nonneg`, `starAlgHom_mono`, `starAlgHom_le_iff`) are all pinned
> to one universe — ~155 lines of *audited* statements, not 102 lines of one.
>
> **A live opportunity remained, and it is not this one — it was taken on
> 2026-08-27.**  The hint route replaces the **287**-line direct proof at
> `Projections.lean:7089–7375` with a **15-line declaration** (27 lines with its doc comment): `nmiu_factors_maps`
> (69IVa) gives `f = H ∘ G` with `G` onto the corner and `H` injective, so
> `f(𝒜) = H(⌈⌈f⌉⌉𝒜)`, and 48VI.1 applies to `H`.  §11's "40–80 lines replacing
> ~150" was wrong in both directions.
>
> **It needed no author ruling, and the earlier framing here — "left for an
> author ruling" — was wrong.**  The four pinned statements were restated
> universe-polymorphically under new names (`starAlgHom_nonneg_general`,
> `starAlgHom_mono_general`, `starAlgHom_le_iff_general`,
> `isVNSubalgebra_range_general`) and each audited statement was then
> **re-derived from its general form under its own name**.  A statement
> re-derived byte-identically is not a statement change: all four types were
> printed with `pp.explicit` + `pp.universes` + `pp.fullNames` against the old
> and the new olean and diffed to nothing, down to binder names.  No consumer
> moved; no row for those four changed; two rows were *added*, for the two
> general forms whose doc comments open with a DISP tag.  Measured deltas:
> `Basic.lean` **+33 net** (82 inserted, 49 deleted), `Projections.lean`
> **−263 net** — against the costed +20 / −273.  `nmiu_image` is axiom-clean
> in situ.  69IVb's proof class moves `route` → `faithful`.
>
> **It still does not give this limb a consumer.**  `injective_nmiu_iso_on_image_2'`
> is the Lemma's *second* conclusion, which 69IVb does not ask for; it stays
> terminal and belongs in §6.

*Original section follows, retained because the reasoning is what led to the
correction:*


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

### 5.3 `tensor_equalisers` (125VI) — the recorded reason has expired. **The row was re-costed the same day; §5.3 did not notice.**

*Status, added 2026-08-28.*  The recommendation below — "re-cost the row; leave
the proof", and "I have not edited the row" — **was carried out hours later, by
`4008ef8`, on 2026-08-27.**  The row now says "which is **NOT** blocked --
`tensor_equalisers` has been proved since `61d6f49` and is green; what the hint
still needs, and the tree still lacks, is pullbacks in W*_miu", and its status
field costs that: a category structure on W\*_miu with pullbacks plus a
limit-preservation theorem for `(·) ⊗ 𝒜`, several hundred lines and a
statement-level addition.  Both this section and §11's item 2 went on reading as
open for a day; checked and closed on 2026-08-28.  Nothing else about the
diagnosis changes — the limb stays dead and the proof stays as it is.


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

`A/CStar/TowardsVN.lean:527`, 39 lines, `green`, the **only** declaration
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

**166II** `ultranorm_continuity_ext_tensor` (`B/Dils/SelfDual.lean:9537`):

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

### Shortlist — **all read, 2026-08-28**; see §5.7 for what they turned out to be

These are dead Lemma/Proposition/Theorem statements with a **live sibling** on
the same point, which is the 123I shape.

| point | declaration | file:line | lines | live siblings |
|---|---|---|---|---|
| 118II | `cceil_tensor` | `A/Proc/Tensor.lean:9748` | 134 | 1/2 |
| 81IX | `div_usc_ball` | `A/VN/Division.lean:2975` | 114 | 4/5 |
| 106I | `uniqueness_sequential_product_exists` | `A/Proc/Measurement.lean:8928` | 79 | 1/3 |
| 4XIII | `positive_2x2matrix_2` | `A/CStar/Basic.lean:284` | 67 | 1/2 |
| 82I | `polar_decomposition_2` | `A/VN/Division.lean:3446` | 55 | 3/4 |
| 156II | `paschke_injective` | `B/Dils/Paschke.lean:3498` | 48 | 2/3 |
| 160IV | `hilbmod_projthm_3` | `B/Dils/SelfDual.lean:1387` | 45 | 2/3 |
| 96III | `ncp_uwlim_2` | `A/Proc/Measurement.lean:1797` | 39 | 2/3 |
| 23II | `sqrt_lemma_monotone` | `A/CStar/Positive.lean:6138` | 35 | 3/6 |
| 154III | `existence_paschke_2` | `B/Dils/Paschke.lean:1373` | 32 | 13/14 |

`existence_paschke_2` was read and is **not** a fingerprint: it is 154III part
2's uniqueness clause, and its content is already reachable structurally through
`M.univ` and `M.ρ_tprod`, both of which are used. It is a terminal repackaging.
`div_usc_ball` was read and is the sound first clause of 81IX, terminal by
intent (§6). **The other eight were read on 2026-08-28 — §5.7.**  One of them
is not a limb at all but a trap, and the "live siblings" column is wrong in two
rows: the sibling that keeps 96III's and 4XIII's counts above zero is in each
case *another dead declaration*.

### 5.7 The shortlist, read (2026-08-28)

Eight declarations, one verdict each.  The headline: **seven are terminal and
one is a trap**, and the check that found the trap is not the one the shortlist
was built on.

**`sqrt_lemma_monotone` (23II) — a trap, not a limb.**  The thesis's Lemma
states the approximating sequence is monotone, and the tree proves it — through
`mul_nonneg_of_commute`, the product of commuting positives.  That lemma is
proved from `sqrt_exists_core` → `sqrt_unit_exists` → `sqrt_lemma_exists`,
which is **the existence half of this same Lemma**.  The thesis rules the route
out in as many words at cstar.tex:3543 — "we have carefully avoided using the
fact here that the product of positive commuting elements is positive, which is
not available to us until `ineq-square-root`" — and proves monotonicity instead
from the positivity of the coefficients of `qₙ₊₁ − qₙ` as polynomials.  Nothing
breaks today: the declaration has no consumer, and the existence half gets
convergence the way the thesis does, from the Cauchy estimate
`‖bₙ − b_N‖ ≤ qₙ(1) − q_N(1)`.  Wiring this lemma into that chain closes a
cycle.  **Action taken:** the docstring now says so.  This is the one case where
being dead is what makes the tree correct, so the limb must not be "repaired"
and must not be deleted either.

**Superseded 2026-09-03.**  The trap is gone: `sqrt_lemma_monotone` is now
proved the thesis's own way, from a private cone `SqrtCone a` — the values at
`a` of the real polynomials with nonnegative coefficients and zero constant
term — closed under products by the exponent identity `aᵐ⁺¹·aⁿ⁺¹ = aᵐ⁺ⁿ⁺²`
alone.  It no longer touches `mul_nonneg_of_commute`, so there is no cycle to
close, and the "must not be repaired" warning above and the docstring it
refers to are both void.  The declaration is still consumerless; that part of
the row stands.

**`ncp_uwlim_2` (96III) — the row's own count was wrong, and the block is
closed.**  The table says 2 of 3 siblings live.  In fact `ncp_uwlim_1` is dead
too, and `ncp_uwlim`'s single consumer is `ncp_uwlim_2` — so all three
declarations in `A/Proc/Measurement.lean` are one block that nothing outside
reaches, ~110 lines.  The live rendering of 96III.1 is a *fourth* declaration
in a different file, `sfilter_cp_uwlim` (`B/Dils/Pure.lean`), whose own
docstring already says why: `ncp_uwlim_1` "asks for" a von Neumann structure on
the domain "and never uses it".  Rowed, so outside §7's pool by definition;
recorded, not deleted.

**`positive_2x2matrix_2` (4XIII) — a closed pair, same shape.**  Part 1's only
consumer is part 2, and part 2 has none.  Both halves of the Lemma, 76 lines,
reached from nothing.  Rowed; recorded.

**`cceil_tensor` (118II) — terminal, and the duplication is already declared.**
Its *argument* is re-run 400 lines below in the private `tensor_projSup_le`,
which says so in its own doc comment.  The two conclusions differ
(`⌈⌈a⊗b⌉⌉ = ⌈⌈a⌉⌉⊗⌈⌈b⌉⌉` against `⋁P ⊗ ⋁Q ≤ z`), so calling the Lemma would not
have served, and the shared machinery `ncp_union_2` is already factored out.
Nothing to do.

**`hilbmod_projthm_3` (160IV) — terminal, reason already written.**  The
docstring records the divergence: existence is `exists_orthogonal_decomp`, run
inside `V^⊥⊥` rather than extended to a basis of `X`, and uniqueness is the
sharper `V^⊥⊥ ∩ V^⊥ = {0}`.  `selfdual_compl_defining_dense` cites 160IV.3 in
prose and reaches for the machinery form, which is what a consumer needs.

**`polar_decomposition_2` (82I) — terminal.**  `[a*] = [a]*`; the live sibling
`polar_decomposition_1` has seven consumers across three files, and no proof in
the tree re-derives the starred identity inline.  A packaged clause of the
Proposition with no customer.

**`uniqueness_sequential_product_exists` (106I) and `paschke_injective`
(156II) — terminal by intent.**  Both are chapter endpoints: 106I's *uniqueness*
half is equally consumer-free, and `paschke_injective` is the headline the
`paschke_injective_carrier` machinery exists to state.  Class 2.

**What the eight say as a set.**  Three of them (23II's family, 96III's trio,
4XIII's pair) are **closed blocks whose internal traffic reads as life** — the
same thing §13.5 found in `TensorTransport`, arrived at from the other
direction.  A direct-use count cannot see them and the shortlist's "live
siblings" column inherits the blindness; it should be read as "siblings with a
mention", not as "siblings that are reached".  And the one real find came from
asking a question the shortlist does not ask — not *is this dead*, but *why is
the thesis's proof different from ours* — which is what turned up the ordering
constraint the thesis states and the tree quietly violates.

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
* **`injective_nmiu_iso_on_image_2'` (48VI part 2)**, `A/VN/Basic.lean:4902`,
  74 lines.  **Moved here from §5.2, 2026-08-27**, where it had been nominated
  as a fingerprint on a premise that does not survive reading `vn.tex:1119`.
  It is that Lemma's *second* conclusion — an injective nmiu-map restricts to
  an nmiu-**isomorphism** onto its image.  The one place the theses point at
  that Lemma is 69IVb (`vn.tex:3637`), which asks only for the *first*
  conclusion, and which took it on 2026-08-27 (§5.2).  The second conclusion
  yields neither closedness of the range nor that its suprema are computed in
  `ℬ`, so no proof of 69IVb can spend it.  Terminal.

---

## 7. Class 3 — superseded machinery, and what was deleted

**190 declarations, 2,111 lines**: untagged (no thesis point in the doc
comment), unrowed (no audit row names them), not accessors. This is the
deletion pool. Its largest members:

**Both halves have since been spent, and the count did not survive contact with
the tree — read §7a and §7b before quoting any number in this section.** The
pool re-derives to **130 declarations, not 190**; three of the twelve members
its table names below are live, rowed or ruled-kept; and of the 74 candidates
put in front of a compiler across the two rounds, 40 were deleted. Two of
the members named below are not dead (`IsCompatExt.norm_ipVal_self_le`) or not
unrowed (`PhiCompatible.mul_right`), and the deletable fraction measured on the
four `B/` files is about a quarter of the pool, not all of it.

| lines | declaration | file:line |
|---|---|---|
| 119 | `paschkeModuleId` | `B/Dils/Paschke.lean:2152` |
| 112 | `PhiCompatible.mul_right` | `B/Dils/Paschke.lean:317` |
| 48 | `concreteTensor_top_cancel` | `A/Proc/Commutation.lean:565` |
| 46 | `conj_ncp_eq_of_le_proj` (private) | `A/Proc/Measurement.lean:3485` |
| 46 | `concreteTensor_top_top` | `A/Proc/TensorTransport.lean:661` |
| 38 | `paschke_rho_forces_cyclic` | `B/Dils/Paschke.lean:521` |
| 36 | `IsCompatExt.norm_ipVal_self_le` | `B/Dils/SelfDualCompletion.lean:1560` |
| 34 | `cyclic_and_separating_of_separating` | `A/Proc/Commutation.lean:475` |
| 34 | `op_smul_comm_complex'` | `B/Dils/SelfDualCompletion.lean:1057` |
| 33 | `modularSqrt_orbit` | `A/VN/ModularTensor.lean:1130` |
| 32 | `paschke_inner_conj_forces_zero` | `B/Dils/Paschke.lean:488` |
| 31 | `npFunctional_tendsto_of_isLUB` | `B/Dils/Paschke.lean:870` |

By file: `B/Dils/SelfDualCompletion` 28, `B/Dils/Paschke` 16,
`B/Eff/StatesPredicates` 15, `A/Proc/QuantumLambda` 13, `B/Eff/EffectAlgebras`
11, `A/VN/Tomita` 11, `A/Proc/TensorTransport` 10, `A/CStar/Positive` 10.

### Nothing was deleted in this sweep, and the reason is operational

*(Superseded for the four `B/` files by §7a, 2026-08-27: they were spent in a
round with the tree to itself. The reasoning below stands for the `A/` half.)*

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

### 7a. The B half of the pool, spent (2026-08-27, tree to itself)

**19 declarations, 114 lines deleted** from the four `B/` files the pool names
(`B/Dils/SelfDualCompletion` 9, `B/Dils/Paschke` 6, `B/Eff/StatesPredicates` 4,
`B/Eff/EffectAlgebras` 0). Every deletion was made and then *compiled*: each
edited file and every file downstream of it — `Kaplansky`, `Paschke`,
`SelfDual`, `Pure`, `Quotients`, `DiamondAmp`, `Dagger`, `Comparisons`,
`VNExamples` — rebuilt at exit 0. None of the 19 carried an audit row, so no
row was deleted; `audit_check.py` stays at 0 on all six checks and
`coverage.py` at 669/669, 64/64. The `sorry` count is untouched at 11.

Deleted:

* `SelfDualCompletion`: `semC_neg`, `op_smul_add'`, `mul_op_smul'`,
  `op_smul_comm_complex'`, `ipf_add_left`, `ipf_smul_left`, `ipf_zero_left`,
  `ipf_sub_left`, `hasIP_zero_right` — 61 lines. The `'`-suffixed module
  axioms on `V̄` and the left-argument halves of the `ipf` family: the
  instances were built from the *other* halves and these were never consumed.
* `Paschke`: `ptens_smul_sum`, `pTheta_mono`, `rightMul_one`, `nc_norm`,
  `ncInner_smul_left`, `denseRange_ksEta` — 28 lines. The last three are
  `private`, so the compile is a *proof* of their deadness: no external use is
  possible and a bare `simp` inside the file would have failed.
* `StatesPredicates`: `emon_mul_le_mul_left`, `CoprodPres.desc_self`,
  `AConvMCat.mix_one`, `AConvMCat.mix_zero` — 25 lines.

**Two of the seven B members this section names by name were not dead at all,
and the method is why.**

* **`IsCompatExt.norm_ipVal_self_le`** (listed above at 36 lines) has **three
  consumers**: `SelfDualCompletion.lean:1733` and `:1734`
  (`hW.norm_ipVal_self_le`) and `:2038` (`E.isCompat.norm_ipVal_self_le`).
  All three are dot-notation, which §1's table claims the textual walk sees
  "suffix-indexed". For a name qualified by a *structure* namespace
  (`IsCompatExt.`) it evidently did not. **Add to §1: index every declaration
  under its bare last component as well as its qualified name, and test the
  index on a `Foo.bar` reached as `h.bar`.**
* **`PhiCompatible.mul_right`** (112 lines, the second-largest member) **is
  rowed**: `docs/audit/bdils-paschke-stinespring.csv` row 9, DISP **154III**,
  `stronger`/`faithful`. The pool is defined as *unrowed*, so its presence
  here is a defect in the pool, not a finding about the declaration. Its doc
  does not *open* with a DISP tag (it opens "Shifting a φ-compatible map on
  the right"), which is why the tag filter missed it; the row filter should
  have caught it and did not. **Left untouched.**

**A third trap for §1, found while reconstructing the pool.** A scanner must
end a declaration's own body at the next **top-level command**, not at the next
**named** declaration. Anonymous `instance : …` blocks have no name, so a
scanner that stops at the next name swallows the anonymous instance's body and
loses every use inside it. This reports as dead:
`CompatExt.ipVal_neg_neg` (used at `SelfDualCompletion.lean:1962`, inside
`noncomputable instance : NormedAddCommGroup E.Car`) and `isSumOf_op` (38
lines, used at `StatesPredicates.lean:5404`, inside an anonymous instance).
Both would have been deleted by a scan that did not fix this.

**Kept, each with its reason** (all zero-use, all untagged, all unrowed — the
pool's filter has no signal for any of these):

* `paschkeModuleId` (93 lines, the pool's largest member): its own doc says
  "**Non-vacuity check** … Kept in the tree deliberately: two separate
  mirroring defects left `PaschkeModule` *uninhabited* and nine theorems of
  this file vacuous". Class 2, not class 3.
* `paschke_inner_conj_forces_zero`, `paschke_rho_forces_cyclic`: both docs
  open "**Negative result** (kept in the tree; `PROVING-LOG.md` session 15)",
  and the head of `Paschke.lean` cites both as the record of two renderings
  that left `PaschkeModule` uninhabited.
* `msc_cor14_1_sup`, `msc_cor14_2_sup_below`: `PROVING-LOG.md` (the 177Ia
  repair) rules that they "stay unreferenced *by design*: like the
  `WrightTriangle` refutations they are the record of the false first
  printing", and the 177Ia row's note says so too.
* `npFunctional_tendsto_of_isLUB`: **class 1 shaped, not class 3.**
  `Pure.lean:2893` names it in prose as the justification of the step "`∑ᵢ qᵢ
  ↑ ⌈⌈p⌉⌉` ultrastrongly", and the Lean proof of that step does not use it.
  Worth a look in the next cone pass.
* `two_convex_nonempty` / `two_convex_unique` (together "`AConv₂ ≅ Set`"),
  `tuple_desc` (the binary instance of the thesis's tuple identity),
  `emon_mul_orth_comm` (`a ⊙ aᵖ = aᵖ ⊙ a` in any effect monoid): each is a
  terminal record cited by name in the tree's own prose.
* `isDiff_ominus`, `MConvexComb.coeFinsupp_support`, `DMKleisli.fn_id`:
  accessors (`isDiff_ominus` is the defining property of the choice-defined
  `ominus`), so §8, so out of the pool by its own definition.

**The pool's B-half count is too high by roughly a factor of two.** This round
re-derived it per file with the same filters plus a Unicode tokeniser, correct
declaration ends, and `@[simp]`/`instance` quarantined: 9 / 10 / 9 / 4
candidates against this section's 28 / 16 / 15 / 11. The difference is
`@[simp]` lemmas and `_apply`/`_val`-shaped accessors that §8 already
quarantines. **Do not re-quote 190 as a deletable count**; on the B evidence
the deletable fraction of the pool is nearer a quarter of it.

**One deletion round creates the next.** Removing the 19 orphaned five more
declarations, 53 lines, whose only consumer was one of them: `ipf_sub_right`
(5), `pTheta_add` (11) and `pTheta_nonneg` (13) in `Paschke`,
`MConvexComb.bin_one` (14) and `bin_zero` (11) in `StatesPredicates`. They
were **live at `a4df27b`** and so outside the pool this round was given; they
are left in place, and they are the cone effect §11.4 predicts, now measured:
one round at 19 deletions produced five new limbs.

### 7b. The A half of the pool, spent (2026-08-27, tree to itself)

**26 declarations, 225 lines deleted** — 21 from the `A/` half of the pool
(173 lines) and the 5 declarations the `B/` round of §7a orphaned (52 lines),
which were live when the pool was drawn and so were outside its scope then.
`git` reports 250 lines removed, the difference being the blank separators the
deletions left behind.  Every edited file and every file downstream of one was
rebuilt individually at exit 0, and the tree was then rebuilt whole.
`scripts/audit_check.py` stays at 0 on all six checks and `scripts/coverage.py`
at 669/669, 64/64.  The `sorry` count is untouched at eleven.  None of the 26
carried an audit row, so no row was deleted; one *doc comment* was edited, and
it is named below.

Deleted:

* `A/CStar/Positive` — `arg_eq_arctan`, `thesisPos_one`, `mul_le_meet_mul_add`,
  15 lines.  The whole of that file's pool.  Two are `private`, so the compile
  is a proof of their deadness.
* `A/Proc/QuantumLambda` — `sum_haU_diag`, `gZ_sa`, `gZSsa`, `coe_wstar_image`,
  `vtmul_mem_tensorSub₂`, `isVNSubalgebra_tensorSub₂`, `tensorSub₂_mono`,
  `concreteTensorEquiv_unique`, `tensorSub_inf_of_intersection_tensor`,
  58 lines.  Two of them — `tensorSub₂_mono` and
  `tensorSub_inf_of_intersection_tensor` — are §10d's one-sided `tensorSub_inf`
  chain, dead in two consecutive sweeps; the chain's third member
  `tensorSub_inf` is kept, for the reason below.
  **This is the one deletion that took prose with it**:
  the `WstarTransport` section overview at `:6092` listed
  `tensorSub_inf_of_intersection_tensor` beside its two-sided companion, and
  that bullet was rewritten in the same edit to name only the companion — which
  is the form 125IV `equaliser_lemma` actually consumes — and to record where
  the one-sided form went.
* `A/Proc/TensorTransport` — `htmul_zero_left`, `ucext_surjective`, `ucmpr_one`,
  `CT_top_left`, `CT_top_top`, `CT_of_CT_corner_any`, 36 lines.  The three
  `CT_*` are §10c's cluster 1 and cluster 2 remnant, "superseded and harmless
  to keep"; superseded is the definition of class 3, and this round spent them.
* `A/Proc/Commutation` — `concreteTensor_top_cancel`, 37 lines: §7's
  third-largest member.
* `A/VN/ModularTensor` — `modularSqrt_orbit`, 22 lines: §7's table names it,
  §10e confirmed it dead, and its content survives in `modularSqrt_htmul`
  (2 uses), of which it was a three-line transport.
* `A/VN/Tomita` — `b_real_symm`, 5 lines: the dead half of the
  `a_real_symm`/`b_real_symm` mirror pair §10e names.  `a_real_symm` has a
  consumer; this one never did.
* The five orphans of §7a — `ipf_sub_right` (`SelfDualCompletion`), `pTheta_add`
  and `pTheta_nonneg` (`Paschke`), `MConvexComb.bin_one` and `bin_zero`
  (`StatesPredicates`), 52 lines.  All five were re-checked as still zero-use
  before deletion.

**The fourth mechanism by which a textual zero-use lies, and it is the largest
one yet: the dotted PREFIX.**  §7a fixed the *suffix* — `h.bar` as a use of
`Foo.bar` — by indexing every declaration under the last component of its
qualified name.  That fix does not see the other side of the dot.  A use of the
form `f.mp`, `f.mpr`, `f.hasSum`, `f.comp`, `f.isComplete`, `f.symm`,
`f.induction_on`, `f.opTensor` — a *projection out of* the declaration's own
conclusion — tokenises as a single dotted identifier whose **first** component
is the declaration.  An index built from suffixes alone never contains it, and
the declaration reads as having zero uses.

Indexing every contiguous dotted run `parts[i:j]` rather than only the suffixes
`parts[i:]` removes **25 declarations from the pool tree-wide, 13 in `A/` and 12
in `B/`** — the whole pool falls from 155 to 130 and the `A/` half from 96 to
83.  Every one of the 25 is live and would have compiled as an error if
deleted:

| declaration | the use the suffix index could not see |
|---|---|
| `mem_vnComm_top` | `TensorTransport.lean:735`, `mem_vnComm_top.mp hb` |
| `le_vnComm_comm` | `Commutation.lean:189`, `le_vnComm_comm.mpr …` (and 2 more) |
| `summable_diagTerm` | `Tensor.lean:7194`, `summable_diagTerm.hasSum` |
| `continuous_diagChi` | `Tensor.lean:7208`, `continuous_diagChi.comp hcont` |
| `Corner.isClosed_cornerSet` | `Measurement.lean:597`, `isClosed_cornerSet.isComplete` |
| `IsCorner.isStarProjection` | `CornerTensor.lean:106`, `h.isStarProjection.isIdempotentElem` — **suffix and prefix at once** |
| `isUnitaryCLM_one` | `CommutationAmplify.lean:374`, `isUnitaryCLM_one.opTensor …` |
| `le_iff_matForm` | `Basic.lean:5349`, `le_iff_matForm.mpr` (and 2 more) |
| `suppProj_eq_zero_iff` | `Projections.lean:2993`, `suppProj_eq_zero_iff.mp` |
| `IsPowBase.denseRange_mul_self` | `ModularGroup.lean:380`, `h.denseRange_mul_self.induction_on` |

and three more in `A/` (`CentrePositiveSeparating.centralProj`,
`IsPowBase.lipschitzWith_cpowOp`, `differentiable_sinq`) with twelve in `B/`
(`rf_continuous`, `lipschitz_lk_fst`, `lipschitz_lk_snd`,
`SPred.isSup_iff_isSupSet`, `SPred.isInf_iff_isInfSet`, `pcm_isSumOf_pair_iff`,
`CoprodPres.eTTT`, `op_le_iff`, `unitInterval_le_iff`, `prod_le_iff`,
`saDown_le_iff`, `cuUpLin`).  Note that **`mem_vnComm_top` is named as dead by
both §7 and §10c**, and it is not: the older Lean term walk saw the use and the
textual walk of this sweep did not.  `IsCorner.isStarProjection` needs both
halves of the fix at once, so a scanner that has one and not the other still
loses it.

**A cone pass over compiled terms, run independently and finishing while this
round was in progress, found the same mechanism and the same 25 declarations**,
and reported that it accounts for 33 of the 36 non-instance declarations the
textual method calls dead and the terms call live.  Two methods that are blind
in different places (§1) agreeing on the identity of a defect is the strongest
evidence this document has for any of its numbers.  Where they disagree the
cone is right: it walks terms, not text.

**Added to §1** by this round, completing the entry §7a opened: a use is any
*contiguous dotted run* of the token, not a suffix of it and not a prefix of it.
Index `Foo.bar.baz` under all six of `Foo`, `Foo.bar`, `Foo.bar.baz`, `bar`,
`bar.baz`, `baz`, and test the index on a `Foo.bar` reached as `h.bar`, on one
reached as `bar.mp`, and on one reached as `h.bar.mp`.  §1's dot-notation row
now reads **"seen (indexed over every dotted run)"** in place of
"suffix-indexed", and §1 carries the rule as its fourth implementation trap.

**A fifth thing the pool's filters miss, cheaper than the others.** §8's
accessor class is matched by name *suffix* — `_apply`, `_coe`, `_val`, `_def`.
It does not catch the same shapes written the other way round: `coe_orbitSub`
(`A/VN/Tomita.lean`, proved `rfl`) and `mem_saOrbit_iff` (same file, proved
`Iff.rfl`) are accessors by §8's own description — "`rfl`-proved" — and are
therefore out of the pool by the pool's own definition, but the name filter put
them in it.  Both were kept.  A `rfl`/`Iff.rfl` body is the reliable signal
here; the name is not.

**Kept, each with its reason** (all zero-use, all untagged, all unrowed):

* **The whole of `A/VN/Tomita.lean`'s Part IV, `section Package`** — eight
  declarations, and this is the largest keep in either half.  §10e reads the
  package pattern as waste; the reason to keep *this* package is in §10e's own
  diagnosis.  Its two definitions `modularSqrt` and `modularConj` are **not**
  dead — `A/VN/ModularTensor.lean` uses them at `:1193`, `:1197`, `:1210`,
  `:1225` and `:1229` — so the block is reached, and what §10e names as the
  difference between this package and `ModularTensor`'s is precisely that
  "`Tomita.lean`'s package ships its own domain-membership dischargers and
  `ModularTensor.lean`'s ships none".  The dischargers are
  `orbit_mem_modularSqrt_domain`, `exists_Ksub_repr` and
  `mem_modularSqrt_domain`.  Deleting them deletes the thing §10e names as the
  repair.
  **Half of that reason is false, and the term-level walk of 2026-08-28 says
  which half.**  `modularConj` is live: four references, one of them
  `modularConj_htmul`, which `A/VN/CommutationTomita.lean` consumes.
  `modularSqrt` is not: **eleven references and every one inside the package**,
  its own siblings plus `ModularTensor.lean`'s `Δ^{1/2}` chain — and
  `ModularTensor` is the block, so it cannot be the evidence that the block is
  reached.  The three dischargers named above have **no reference at all**, nor
  do `modularSqrt_hasCore`, `modularConj_modularSqrt`,
  `modularConj_modularSqrt_orbit`, `modularSqrt_isSelfAdjoint` and
  `modularSqrt_inner_nonneg`.  The keep stands, on §10e's ground and not on
  this one.
* `bicommutant_eq_of_uwClosed` (`Tomita.lean:482`): named in that file's own
  header under **"Main results"**, as are `modularSqrt_hasCore`,
  `modularConj_modularSqrt_orbit` and `modularConj_modularSqrt`.  Prose-cited
  terminal record, the §7a criterion.
* `concreteTensor_top_top` (`TensorTransport.lean`, §7's table, 46 lines): its
  own file's header cites it at `:32`, and `A/Proc/CommutationAmplify.lean:61`
  rests a **recorded refutation** on it — "amplification never manufactures a
  separating vector", because `𝒜 ⊗̄ B(ℒ) = B(ℋ ⊗ ℒ)` has a separating vector
  only when `dim (ℋ ⊗ ℒ) ≤ 1`.  Class 2, not class 3.
* `tensorSub_inf` (`QuantumLambda.lean`): its docstring carries a ⚠ note added
  on 2026-08-26 saying in as many words that nothing consumes it and that it is
  "kept on the record as the unconditional statement of the abstract 121II".
  The tree's own written ruling; left standing while §10d's other two members
  went.
* `modularSqrt_hasCore_orbitSpan`, `modularSqrt_htmul_pkg`
  (`ModularTensor.lean`, Part 6): the package block whose third member
  `modularConj_htmul` is live.  Same argument as Tomita's Part IV, one step
  weaker.  *(This bullet named a third declaration,
  `opTensor_mem_modularSqrt_domain`, as the zero-use domain discharger for the
  live `modularSqrt_opTensor`.  Hours later on 2026-08-28, §10e's ruling added
  `htmul_mem_modularSqrt_domain`, which consumes it; it is live by direct count
  now and outside the pool for the ordinary reason.
  `scripts/limb_check.py` caught the stale line, and it was the first thing
  that script found.)*
* `CT_iff_vnComm` and `cyclic_and_separating_of_separating`: §7 already moves
  these out of the pool by hand and the 2026-08-26 reading stands.
* `coe_orbitSub`, `mem_saOrbit_iff`: §8, per the accessor note above.

**A third member of §7's own table is not in the pool.** §7a found two —
`IsCompatExt.norm_ipVal_self_le` not dead, `PhiCompatible.mul_right` not
unrowed.  The third is **`conj_ncp_eq_of_le_proj`** (`A/Proc/Measurement.lean`,
46 lines, §7's fourth-largest member).  The section doc seven lines above it
says: "The elementary route is kept below as
`conj_ncp_eq_of_le_proj`/`exists_ncpCorestrict`, which the corestriction
arguments of 100III and 102VII use in their own right."  It is a written keep
ruling, in the tree, in the same doc comment block.  The pool's filters read
only the declaration's *own* doc comment for a DISP tag and never the section
prose above it, so a keep ruling written one paragraph up is invisible to them.
Left untouched.  **Three of the twelve members §7 names by name are wrong** —
one live, one rowed, one ruled kept — which is the measurement to quote about
that table, not its line counts.

**The A-half count, re-derived.** Per file, at `5a0bd16`, with the prefix fix,
correct declaration ends and `@[simp]`/`instance` quarantined:
`A/VN/Tomita` **12** (§7: 11), `A/Proc/QuantumLambda` **10** (§7: 13),
`A/Proc/TensorTransport` **7** (§7: 10), `A/CStar/Positive` **3** (§7: 10).
The whole `A/` half is **83** and the whole pool **130**, against §7's 190.
`A/CStar/Positive` is the sharpest correction, and unlike the `B/` half's it is
**not** explained by `@[simp]` and accessor noise.  That file has 54 zero-use
declarations; **51 of them carry an opening DISP tag or an audit row** — it is
the opening chapter, and §3 already says so — and two more are `instance`s,
which leaves exactly three.  §7's ten is not reproducible under §7's own stated
filters: widening the DISP-tag regex (§7's `\d{1,3}[a-z]?[IVXL]+` rejects a
label with a trailing lowercase letter, e.g. `**125VIIb**`) and matching audit
rows at the bare last component as well as the qualified name together move
exactly **one** declaration tree-wide, and restoring §7a's declaration-end bug
moves Positive not at all.  Whatever produced the 10 is not recorded, which is
the argument for re-deriving rather than quoting.

Of the 83, this round worked the four files §7 names by file and the five `A/`
declarations its table names by line — 42 candidates in seven files — and
deleted 21 of them.  **41 candidates in fourteen other `A/` files are
untouched**, the largest being `A/VN/Modular` 8, `A/Proc/Tensor` 6,
`A/Proc/CornerTensor` 4, `A/VN/StandardSubspace` 4, `A/VN/TomitaTakesaki` 4.

**Two rounds, one measured deletable fraction.** 19 of the `B/` half's 32
worked candidates and 21 of the `A/` half's 42: **40 of 74, a little over half
of what is put in front of a compiler, and 40 of the pool's 130.** §7a's "nearer
a quarter" holds tree-wide; the per-file rate, once the pool is re-derived
honestly, is about one in two.

**One deletion round creates the next, again, and the effect is compounding.**
The 21 `A/` deletions orphaned **three** more declarations, 51 lines, whose only
consumer was one of them: `CT_top_right` (30 lines, `TensorTransport`) — §10c
recorded it as having two consumers and both were `CT_top_left` and
`CT_top_top`; `CT_cornerAlg_congr` (9 lines, same file) — §10c recorded one
consumer and it was `CT_of_CT_corner_any`; and `sum_matU_diag` (12 lines,
`QuantumLambda`), whose only consumer was `sum_haU_diag`.  They were live at
`5a0bd16` and are left in place.  Note that all three were named in §10c/§10e as
*evidence that a block was not dead*; the evidence was one deletion deep.

### 7c. The pool's remainder, spent (2026-08-28, tree to itself)

**40 declarations, 295 lines deleted** across twenty files — 28 in `A/` (203
lines) and 12 in `B/` (92).  **75 candidates were put in front of a compiler
and 35 survived**, so the one-in-two rate §7b measured held almost exactly
(40/75 = 53%, against §7a+§7b's 40/74 = 54%).  Every edited file and every file
downstream of one was rebuilt — which, because `A/VN/Basic` and `A/Proc/Tensor`
are near the head of the import chain, is the whole tree — and a full `lake
build` finished at exit 0.  `scripts/audit_check.py` stays at 0 on all six
checks and `scripts/coverage.py` at 669/669, 64/64.  The `sorry` count is
untouched at eleven.  None of the 40 carried an audit row, so no row was
deleted, and **no doc comment was edited**: every prose citation this round
found is a citation of something it kept.

The 75 are the whole of what §7b left: the **41** in the fourteen `A/` files
§7b names, the **2** in `A/Proc/Commutation` its per-line pass did not reach,
the **3** limbs §7b's own deletions orphaned (`CT_top_right`,
`CT_cornerAlg_congr`, `sum_matU_diag`), and the **29** that remain of §7a/§7b's
34 unexamined `B/` members once the five §7b deleted as §7a's orphans are taken
out.  With this round the pool defined by §7 is **exhausted**: the re-derived scan
now reports **71** declarations, and they are the **67** examined and ruled
kept across §7a, §7b and this section (32 + 35) plus four of the five limbs
this round itself created.  Nothing in the pool is unexamined.

Deleted:

* `A/Proc/Tensor` — `htKet_comp_adjoint`, `ncpMap_ortho_eq_zero` (private),
  `concreteTensor_le_iff`, `spatialSpan_le_concreteTensor`,
  `concreteTensor_eq_closure_spatialSpan`, `concreteTensor_inf_le_inf`, 55
  lines.  The last is §10f's "superseded" verdict spent: 121II's rowed carrier
  is `intersection_tensor'`, which proves the whole Proposition, and the "easy
  half" helper never fired.  The four `concreteTensor_*`/`spatialSpan_*` are
  the unconsumed remainder of the `concreteTensor` API that
  `docs/COMMUTATION-THEOREM.md` records as built in one go.
* `A/Proc/Commutation` — `mem_vnComm_of_forall`, `reduced_commutant_eq`, 21
  lines.  The first is §10e's `section Package` shape at its smallest (an
  `.mpr` wrapper on a live `mem_vnComm`); the second is the reduction theorem
  in a set-comprehension form nothing asks for — `mem_vnComm_iff_comm_reduced`,
  which it wraps, has consumers.
* `A/Proc/CommutationCyclic` — `HasCyclicSeparating.hasCyclic`,
  `hasCyclicSeparating_of_dense_orbit`, 15 lines; `A/Proc/CommutationReduction`
  — `hasFinCyclic_of_cyclic`, 16 lines.  §10e names all three as the small
  instances of the package pattern and re-confirmed them dead; this round spent
  them.
* `A/Proc/Compression` — `commutant_cmpr_image`, 15 lines: the set-level
  restatement of `vnComm_cornerAlgVN`, which is live.
* `A/Proc/CornerTensor` — `cmpr_surjective`, 4 lines.  Its own doc calls it
  the "second half" of `e B(ℋ) e ≅ B(eℋ)`, but the content is `cmpr_cext`,
  which has consumers in this file and two more downstream; the *first* half
  `range_cext` is kept (below).
* `A/Proc/TensorTransport` — `CT_cornerAlg_congr`, 11 lines, and
  `A/Proc/QuantumLambda` — `sum_matU_diag` (private), 12 lines: two of the
  three limbs §7b's own round created.  The third, `CT_top_right`, is kept.
* `A/VN/Basic` — `gnsElemVecs_separating`, `chi_le_one`, 10 lines;
  `A/VN/NormalFunctionals` — `gnsElemVecsOn_separating`, 4 lines.  The two
  `gns*_separating` are the `gnsHilb`/`gnsHilbOn` specialisations of
  `gnsElemVecsFam_separating`, which is used at the family level directly.
* `A/VN/Modular` — `unitary_add_I_smul`, `unitary_sub_I_smul` (§10e's mirror
  pair, both halves dead), `isSelfAdjoint_sqrtSumSq`, 13 lines.
* `A/VN/StandardSubspace` — `stdConj_stdConj`, `stdConj_R`, `stdIsModularPair`,
  12 lines: three more of §10e's upstreaming wrappers, each a one-line
  restatement of a live `J_J`/`J_R`/`isModularPair_a_b` at
  `S.toClosedSubmodule`.
* `A/VN/TomitaAnalytic` — `powExt_zero`, `kMass_nonneg`, 8 lines;
  `A/VN/TomitaTakesaki` — `sepSet_subset_Ksub` (§10f's "orphan, still dead"),
  `absOp_isSelfAdjoint`, 7 lines.
* `B/Eff/Effectus` — `isTotal_map`, `par_map_hat`, `par_ovee_eq'`, 26 lines.
* `B/Eff/VNExamples` — `ncpsu_scal_nonneg`, `wUnitSU_one`, `vn_isTotal_iff`, 24
  lines.  `vn_isTotal_iff` is the sharpest of the three: PROVING-LOG session 85
  calls it "the form the eight will use", and the eight hypothetical von
  Neumann examples all reach past it to `su_isTotal_iff` after destructuring
  `s` themselves.  Its companion `vn_effObj_iso` **is** used that way in prose
  and is kept.
* `B/Dils/HilbertModules` — `mul_smul'`, `sum_smul'`, 17 lines: two of the five
  private module laws forced out of `CStarModule`'s bare `SMul`.  PROVING-LOG
  parsec 7487 rules on them itself — "the polar construction is arranged to
  avoid them … 149IX needs `sub_smul'` only".
* `B/Dils/SelfDual` — `vnTensor_legRight_nonneg`, `ext_smul_sum` (private), 9
  lines; `B/Eff/Dagger` — `standard_form_isPure`, 11 lines (its sibling
  `standard_form_truth` has a consumer at `:2661`; this one never did);
  `B/Eff/DiamondAmp` — `pcm_sup_unique`, 5 lines.

**The seventh mechanism by which a textual zero-use lies — and this one is not
about the text at all.  A declaration can be named by an audit row in the row's
`note` or `status` field instead of its `lean_name` field.**  The pool is
defined as *unrowed*, and every row filter written for it — and every one of
`scripts/audit_check.py`'s row checks — reads `lean_name` and nothing else.
(The script has seven checks as of 2026-08-28; the seventh reads
`docs/status.txt`, not the rows, and is described at the end of §12d.)
Eight of this round's 75 candidates are named in a note, and one of those notes
is a keep ruling in as many words:

| declaration | the row, and what its note says |
|---|---|
| `spred_sup_of_quot`, `spred_isSup_unique`, `boxPull_one` | **228II** (`beff-vnexamples.csv:74`): "All three are public statements of the toolbox the block announces itself as collecting, and **removing them would be a statement change, so they are reported here rather than deleted**." |
| `purelyAtomic_not_discrete_of_measure_zero` | **129II** (`aproc-duplicators-quantumlambda.csv:26`): "the exception is exhibited by `purelyAtomic_not_discrete_of_measure_zero`" — the machine-checked counterexample the row's `differs` verdict rests on |
| `spred_isInf_orth` | **207V.4**: "helpers `spred_isSup_orth`, `spred_isInf_orth`" |
| `ovee_le_of_le` | **208III**: "`ovee_le_of_le` survives, still used by the orthomodular law" |
| `extensive_effectus_set`, `extensive_effectus_compHaus` | **189aII.3**: "(a) Set and (c) CH are now formalized, as `extensive_effectus_set` and `extensive_effectus_compHaus`" — the two clauses that hold the row's `weaker` verdict to clause (b) alone |

Deleting any of the eight leaves an audit row asserting something false about
the tree, **and no check in this repository would report it.**  Note also that
two of the eight notes are already half-stale — `spred_isInf_orth` was
superseded by `spred_isInfSet_orth` in the 207V.4 repair, and 208III's
"still used by the orthomodular law" was overtaken on 2026-08-22 by
`ovee_le_of_le`'s own docstring ("Scaffolding of the route 208III used to take
… nothing appeals to it any more") — so the mechanism protects stale prose as
readily as live prose.  **Add to §1: index the whole of every audit row, not
its `lean_name` field, when deciding whether a declaration is rowed.**

**An eighth, cheap and mechanical: the DISP-tag regex cannot read a
parenthesised sub-clause label.**  `extensive_effectus_set` and
`extensive_effectus_compHaus` open `/-- **189aII.3(a)** …` and `/-- **189aII.3(c)**
…`.  Both the pool scanner's tag regex and `scripts/audit_check.py`'s
`TAG_OPENS` (`\d{1,3}[a-z]?[IVXL]+(?:\.[0-9a-z]+)?`) match `189aII.3` and then
demand a closing `**`, which `(a)` is in the way of.  So the two read as
untagged, which is what put them in the pool.  The same blind spot means
`audit_check.py`'s *unrowed* check (check 3) does not see them either: they
open with a DISP tag, no row names them in `lean_name`, and the checker
reports 0 unrowed.  **Widening the regex by one optional group would make
`audit_check.py` report two unrowed declarations**, whose repair is to add both
names to row 189aII.3's `lean_name`.  Not done here — it is an audit edit, not
a deletion — but it is the one concrete defect this round found in a checker
rather than in a scanner.

**Mechanism 6 — the keep ruling written above the declaration rather than in
it — was the single largest cause of a keep this round, and it fired eight
times in one specific place: the file's own module docstring under "Main
results".**  §7b kept `bicommutant_eq_of_uwClosed` for exactly this reason and
recorded it as a one-off; it is not.  A module header that lists its
deliverables by name is a keep ruling for every name on the list, and three
files' headers between them saved eight candidates:

* `A/VN/Modular.lean` names `.dense_range` as part of **Lemma A**,
  `eq_one_of_eq_compPMap` as half of **Lemma D**, and states Lemma B's
  deliverable as "`c̃ h = c`, `d̃ h = d`" — which is `normFst_mul` and
  `normSnd_mul` and nothing else in the tree.  Four keeps from one header.
* `A/VN/TomitaTakesaki.lean` names `tomita_JM'J` as half of **RvD Theorem
  4.2(1)** and `isClosed_image_of_uwCompact` as the compactness transfer;
  `A/VN/TomitaAnalytic.lean` names `tomita_JM'J_unconditional`, confirming
  §10f's "terminal by intent".
* `A/Proc/TensorTransport.lean`'s header cites `CT_top_right` by name at `:28`
  — in the *same bullet* that cites `concreteTensor_top_top`, which is why
  §7b kept that one.  So `CT_top_right`, which §7b's own deletions orphaned
  and `docs/COMMUTATION-THEOREM.md` calls a "consumer-free special case",
  **stays**: the header is a citation and the two siblings §7b deleted
  (`CT_top_left`, `CT_top_top`) were not cited there.

**Kept, each with its reason** (35 declarations; all zero-use, all untagged by
the filters, all unrowed by `lean_name`):

* **§8, by the `rfl` signal §7b added** — 7: `mem_cornerAlg` and
  `CentralProj.mem_sub_iff` and `mem_lkSub` and `par_perp_iff` (`Iff.rfl`),
  `IsModularPair.D_domain` and `par_zero_eq'` and `saDown_saUp` (`rfl`).  None
  is named in the accessor style, and the name filter is why they were in the
  pool at all.
* **Named in an audit row's note** — 8, tabled above.  Seven are in `B/`; the
  eighth, `purelyAtomic_not_discrete_of_measure_zero`, is the counterexample
  129II's `differs` verdict rests on.
* **Named by a written ruling in `PROVING-LOG.md` or `ERRATA.md`** — 3:
  `linfty_ae_le` and `pairLp_one` (PROVING-LOG parsec 28085 rules on both by
  name: "Neither is worth removing"); `isPure_of_comp_isComprehension`
  (`ERRATA.md`'s 221IV.5/.6/.7 row: "proved in plain effectus generality,
  alongside `isPure_of_comp_isComprehension`").
* **Named in the file's own prose — mechanism 6** — 13: the eight from module
  headers above, plus `range_cext` (`CornerTensor.lean`'s header: "`cext` is an
  injective ∗-homomorphism **onto the corner `e B(ℋ) e`**", and that is the
  only statement of it), `cornerAlg_one` (its section prose: "### The trivial
  corner — a sanity anchor for the definitions", i.e. class 2, a non-vacuity
  check), `isPureMap_of_isFilter` (`Pure.lean:2388` names it beside
  `isPureMap_of_isCorner`, and it is the filter half of **170I**'s "filters and
  corners are pure"), `vn_effObj_iso` (`VNExamples.lean:6216`, "what the eight
  examples downstream actually use is … the *uniqueness* statement
  `vn_effObj_iso`, which is proved" — and again at `:2127`), and
  `modularPair_data` (`StandardSubspace.lean:650`).
* **`inv1p_nonneg`, `inv1p_comm`** (`B/Dils/Kaplansky`)
  — 2, and PROVING-LOG parsec 6167 calls `inv1p_comm` and `inv1p_conj_le_one`
  "the two facts the thesis lists at dils.tex:4213":
  the doc comment of the *definition* `inv1p`, four declarations above them,
  states "`0 ≤ inv1p b ≤ 1` as well as `0 ≤ b * inv1p b ≤ 1` (dils.tex:4213)"
  — the four facts these two, `inv1p_conj_le_one` and the live `inv1p_le_one`
  render.  They are the toolbox of the `kaplansky_hilbmod_A*` statements, three
  of which are among the tree's deliberate `sorry`s; deleting them removes the
  tree's only rendering of a sentence the thesis prints.
  **`inv1p_conj_le_one` left this list on 2026-08-29**: it is now consumed, and it
  is not dead.  `kaplansky_hilbmod_A₂` — the one of the four estimates that turned
  out to be *true* — is now proved, and `inv1p_conj_le_one` is what bounds
  `⟨(1+⟨y_α,y_α⟩)⁻¹·y_α, (1+⟨y_α,y_α⟩)⁻¹·y_α⟩ ≤ 1` in that proof, which is the
  step the whole estimate turns on.
* **`jConj_modPow`** (`A/VN/ModularGroup`): §13.4 of this document already
  ruled on it — the `jConj` layer "is a class-2 record — kept, not deleted,
  because it is the tree's only statement of `J Δ^{it} J = Δ^{it}`" — and the
  module docstring advertises it under **main results**.  It is the single hard
  zero-use of that file and it stays.

**One deletion failed to compile, and the cause was the deletion tool, not the
declaration.**  `A/Proc/CommutationReduction` broke on
`hasFinCyclic_of_cyclic`: the declaration is preceded by a doc comment which is
itself preceded by `omit [CompleteSpace H] in`, and a backward walk that skips
attributes and `… in` modifiers *first* and the doc block *second* stops at the
doc block and leaves the `omit` behind.  The orphaned `omit … in` then attached
itself to the next command, `end Cyclic`, and Lean reported "Unexpected name
`Cyclic` after `end`" 259 lines further on.  **Add to §1's implementation
traps: a declaration's extent runs from the first of its modifier lines, and
the walk backwards over attributes, bare modifiers and `omit`/`open`/`variable
… in` must RESUME after the doc comment, not stop at it.**  The whole tree was
scanned for the same residue after the repair and this was the only instance.
No other deletion of the 40 failed: the remaining 39 compiled at the first
attempt, and the five `private` ones among them —
`ncpMap_ortho_eq_zero`, `sum_matU_diag`, `mul_smul'`, `sum_smul'`,
`ext_smul_sum` — are compile-*proved* dead, since no external use of a
`private` declaration is possible and a bare `simp` inside its own file would
have failed.

**One deletion round creates the next, a third time, and the effect is
shrinking.**  The 40 deletions orphaned **five** declarations, 43 lines, whose
only consumer was one of them: `CT_uconj_iff` (16 lines) and `uconj_cornerAlg`
(14 lines) in `TensorTransport`, both consumed only by `CT_cornerAlg_congr`;
`zero_smul'` (7 lines, `HilbertModules`), consumed only by `sum_smul'`; and the
two definitions `gnsElemVecs` (`A/VN/Basic`) and `gnsElemVecsOn`
(`A/VN/NormalFunctionals`), 3 lines each, whose only consumers were the two
`*_separating` wrappers deleted above — `gnsElemVecsOn` is **rowed**, so it is
outside the pool by definition and should not be chased.  All five were live at
`0e9f7ff` and are left in place.  Three rounds, thirteen new limbs: 5, then 3,
then 5.

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
| `triple_tensor` | 119II | `49a49f0` | 119IV `isTensorProduct_assoc`, `Tensor.lean:10681` |
| `perp_sharp_is_orth` | 213III | `49a49f0` | `B/Eff/Comparisons.lean:600` |
| `ultranormcontstruct_smul` | 148III.3 | `027dc77` | `ext_tensor_dense` (164II.1), `B/Dils/SelfDual.lean:7948` |
| `dagger_of_iso_adjoint` | 216IX.1 | `0f036ad` | `B/Eff/Dagger.lean:528` |
| `paschke_pure` | 171VII | `7aa3dc0` | `pure_iff_stinespring_surjective`, `B/Dils/Pure.lean:4553` |

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

### 10a. `QuantumLambda.lean` — the atomic-type-I island, 813 lines. **Still the author's call, but the call is on two rows, not on 43 declarations (measured 2026-08-28).**

*The paragraph below is the 2026-08-26 reading and stands.  What it does not
give is the shape of the decision, and that is what an author needs.*

**Measured as the island stands today**, from the "atomic type I slice device"
header to `end AtomicTypeI`: **586 lines, 43 declarations, of which 39 are
`private`.**  (§10a's 813 is a count over commit `a992c23`, which also carries
`BKUnits` and `GenSum`, part of them load-bearing.)  Four are public —
`AtomicTypeIRep`, `AtomicTypeI`, `atomicTypeI_tensor_preimage`,
`atomicTypeI_tensorBsurjectivity` — and **nothing outside `QuantumLambda.lean`
names any of the four**; inside the file the only mentions of the two theorems
are prose in a doc comment at `:4522`.

**Only two of the 43 are rowed thesis statements**: 125VIIb
`atomicTypeI_tensor_preimage` and 125eIII `atomicTypeI_tensorBsurjectivity`.
(The first was *unrowed* until 2026-08-28 — its tag has a sub-point letter and
nothing matched that shape; see `docs/STATEMENT-AUDIT.md`.)  The other 41,
definitions included, are untagged and unrowed: ordinary §7 pool material the
moment the two statements go.  So the ruling is on two rows and the rest
follows.

**And retiring them costs no coverage.**  Both rows are `stmt=ok` on the
schema's sibling clause: 125VIIb is carried by `tensorSub` and `tensor_preimage`
and 125eIII by `surj_of_haTensorBSurj`, `haTensorBSurj` and
`tensorBsurjectivity` — all green, all in the same file.  `coverage.py` stays at
669/669 either way.  What is lost is not a point of either thesis but the
*widening*: the atomic type I forms are the only place the tree proves 125VIIb
and 125eIII for infinite-dimensional atomic blocks, `haTensorPreimage` and
`haTensorBSurj` asking for hereditarily atomic.  That is the thing to weigh, and
it is a smaller and more definite question than "813 lines".

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

### 10b. `ModularGroup.lean` — the `jConj` layer, ~300 lines. **DECIDED at §13.4: kept.**

*The paragraph below is the state of the question before the cone pass, kept
because it records what the direct count could and could not see.  §13.4 ran
the cone on 2026-08-27 and settled it: the 26 declarations are one connected
component that nothing outside reaches, the layer is a class-2 record, and it
**stays**, because `J Δ^{it} J = Δ^{it}` is stated nowhere else in the tree.
§13.4 also moves the block's first member: `Jisometry` is in the cone.*

Twenty-six declarations recorded as outside the cone of every headline theorem
while every member has a consumer inside the block. This sweep's method counts
direct uses only and therefore sees the block as live (`jConj` alone has 33
uses); it finds exactly **one** hard zero-use declaration in the file,
`jConj_modPow` (`:1057`) — which is the single hard zero-use the 2026-08-26
per-file table also reports. The two methods agree where they can and the cone
finding stands unverified until a cone pass is run again. The module docstring
still advertises `jConj_cpowOp`, `J_modPow` and `jConj_modPow` as **main
results**; `jConj_cpowOp` and `J_modPow` have one use each, `jConj_modPow` none.

### 10c. `TensorTransport.lean` — two clusters. **Superseded by §13.5; cluster 2 is now deleted.**

*The paragraph below reads the two clusters by direct count and is left as
written, because the direct count is exactly what §13.5 overturns.  §13.5
found both clusters wholly outside the cone and re-described them as one
finding — "`TensorTransport.lean` stops carrying weight at line 710".  Cluster
2 was afterwards emptied not by that verdict but by §7's pool: once §12c
deleted `CT_cornerAlg_congr` and `CT_of_CT_corner_any`, the rest of the block
fell to zero uses by direct count and went in the fourth pool round, §12d.
Cluster 1 stands; `CT_top_right` is kept, for the reason §12c gives: the
module header cites it by name at `:28`.*

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
It was orphaned inside its own commit.

*Corrected 2026-08-28:* this section said "**`tensorSub_inf`'s own docstring is
still false** where it says 'it is what 125IV `equaliser_lemma` consumes'".  The
docstring had in fact been repaired on 2026-08-26 — it now carries a ⚠ note
saying 125IV goes through the two-sided form and recording the old claim as
withdrawn — and the same repair is on
`tensorSub_inf_of_intersectionTensorStatement` above it.  What *was* still
wrong is that both repairs pointed the reader at a section of this document
numbered **5d**, which it has never had under its present numbering — 5a and 5d
were what §10a and §10d are called now.  They point at §10d today, and
`scripts/xref_check.py` is what found them.  (The pointer is spelled out here
without its `docs/` prefix on purpose: that script cannot tell a reference from
a quotation of one, and quoting it in full would leave the check reporting this
sentence forever.)

### 10e. The `section Package` pattern — the structural finding. **DECIDED 2026-08-28: kept, and the gap is closed.**

*Ruling, ahead of the paragraph that framed the question.*  The `Δ^{1/2}` half
of `ModularTensor.lean` **stays**, and the reason is the asymmetry the block
sits in rather than its use count.  The file's own header displays two
conclusions — `J_ξ = J_ω ⊗ J_{ω'}` **and**
`Δ_ξ^{1/2} = closure (Δ_ω^{1/2} ⊙ Δ_{ω'}^{1/2})` — and they are not consumed
alike:

| | consumers outside the file |
|---|---|
| `isCyclicVector_vnTensor` | 1 (`CommutationTomita`) |
| `isSeparatingVector_vnTensor` | 1 (`CommutationTomita`) |
| `isStandard_vnTensor` | 1 (`CommutationTomita`) |
| `modularConj_htmul` | 1 (`CommutationTomita`) |
| `opTensor_mem_modularSqrt_domain` | 0 |
| `modularSqrt_opTensor` | 0 (one use, `modularSqrt_htmul`) |
| `modularSqrt_htmul` | 0 (one use, `modularSqrt_htmul_pkg`) |
| `modularSqrt_hasCore_orbitSpan` | 0 |
| `modularSqrt_htmul_pkg` | 0 |

Five declarations, one closed chain.  Deleting them would delete the second
displayed conclusion of a file written for both, and the tree states it
nowhere else — the same ground on which §13.4 kept the `jConj` layer.

**The block is larger than this file, and §13.7 said so before this ruling
did.**  A term-level walk of the whole environment (`scripts/UsesOf.lean`,
2026-08-28) confirms §13.7's cone finding declaration by declaration:
`modularSqrt` has **11 references and every one is inside the package**, and
`modularSqrt_hasCore`, `orbit_mem_modularSqrt_domain`, `mem_modularSqrt_domain`,
`exists_Ksub_repr`, `modularConj_modularSqrt`, `modularConj_modularSqrt_orbit`,
`modularSqrt_isSelfAdjoint` and `modularSqrt_inner_nonneg` have **none**.  With
this file's six — the five above plus the new `htmul_mem_modularSqrt_domain` —
that is **fifteen declarations across two files, entered from nowhere**.  The
ruling covers all fifteen; the first version of this section covered five and
was measuring one file.  `modularConj` is *not* among them: it has four
references and one, `modularConj_htmul`, is consumed by `CommutationTomita`, so
the `J` half is live and the two halves of the same package differ.

**One correction to the paragraph below, and it is the eighth mechanism
again.**  `modularSqrt_hasCore_orbitSpan` reads as having one use.  It has
none: the single occurrence is inside `modularSqrt_htmul_pkg`'s *doc comment*
("Together with `modularSqrt_hasCore_orbitSpan` …"), prose in a `/-- … -/`
block.  §10e's own text called it dead and was right; the count was not.

**And the diagnosis was actionable after all.**  §10e said the package ships no
domain-membership discharger, so a consumer of `modularSqrt_htmul_pkg` must
leave the package vocabulary to produce its hypothesis, and that "had the
package been used even once, that gap would have closed."  It is closed now, by
`htmul_mem_modularSqrt_domain` (`ModularTensor.lean`, Package section), and
**it was one lemma wide**: `modularSqrt` unfolds to `(mp … ).D` and `mp`'s two
arguments are `Prop`s, so proof irrelevance makes the two operators defeq and
`opTensor_mem_modularSqrt_domain` transports with a single `rwa
[opTensor_apply]`.  Compiled at exit 0 on the first attempt.

Stated plainly, because it is the honest reading: **the block is now complete
and still unused.**  Those are two different facts and only the first was ours
to change.  The new discharger is itself unconsumed, which is one more
declaration in a dead block — accepted, because what it buys is that the next
reader who wants the `Δ^{1/2}` half can state it without dropping a layer, and
that was the whole content of the finding.

(§12b's keep of `Tomita.lean`'s own `section Package` rests on the same
sentence, and cites `ModularTensor.lean:1193, 1197, 1210, 1225, 1229` as the
uses that keep `modularSqrt` and `modularConj` alive.  Two edits moved them: the
module header gained 20 lines and `htmul_mem_modularSqrt_domain` 24 more, so the
citations above the new lemma are +20 and those below it +44.  The uses are the
same ones; `modularSqrt_hasCore_orbitSpan` is now at `:1206` and
`modularSqrt_htmul_pkg` at `:1244`.)

*What follows is the state of the question before this ruling, kept because it
is where the diagnosis was made.*

**10e, as written on 2026-08-27 — the `section Package` pattern, "mostly
unchanged".**

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
| `IsCommutingPair.symm` | cannot be used as written | **RESOLVED 2026-08-28: dead, and the 2026-08-26 verdict was right about why.** `scripts/UsesOf.lean` walks the environment for term-level references and finds **none** in `Theses/` — the check §10f asked for. The cause is in the file: `sqrtSumSq c d` and `sqrtSumSq d c` are propositionally but not definitionally equal and no `sqrtSumSq_comm` is proved, so `p.symm` returns a pair whose derived operators no downstream lemma is stated about. Written into the declaration's own doc comment; the three-lemma repair is named there and deliberately not built |
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

1. ~~**§5.2, `injective_nmiu_iso_on_image_2'` / 69IVb.**~~ **DONE 2026-08-27,
   and the recommendation was wrong** — see the correction at the head of §5.2.
   69IVb asks only for the Lemma's *first* conclusion; the dead limb is the
   second, and no proof of 69IVb can consume it.  The row was fixed; the limb
   stays dead and moves to §6.  The separate item the attempt turned up — the
   thesis's hint route, **15 lines against our 287**, blocked by
   universe-pinned audited statements — was **also taken, 2026-08-27**, and it
   needed **no author ruling**: the four pinned statements were generalized
   under new names and the audited ones re-derived from them byte-identically,
   which is a proof change, not a statement change.  Measured: `Basic` +33 net,
   `Projections` −263 net; 69IVb moves `route` → `faithful`.
2. ~~**§5.3's row, not its proof.** Re-cost the 125VIIb row: 125VI is `green`
   since `61d6f49` and "which is itself blocked" is stale.~~ **DONE 2026-08-27
   by `4008ef8`, hours after this list was written, and neither this item nor
   §5.3 was updated to say so.** Verified 2026-08-28: the row reads "which is
   NOT blocked" and its status field carries the re-cost (pullbacks in W\*_miu
   plus limit-preservation for `(·) ⊗ 𝒜`; several hundred lines and a
   statement-level addition). The proof is unchanged, as recommended.
3. ~~**§7's pool, file by file, with the tree to yourself.**~~ **DONE, and the
   pool is now EXHAUSTED** — §7a (`B/`) and §7b (`A/`) on 2026-08-27, §7c (the
   remainder, 75 candidates in twenty-seven files) on 2026-08-28. **85
   declarations, 634 lines deleted** — 80 of them pool members put in front of
   a compiler, five of them limbs an earlier round created — out of a pool that
   re-derives to 130, not 190. What is left is **71 declarations, every one of
   them examined and ruled kept with a written reason**: 67 across the three
   sections, plus four of the five limbs §7c itself created. Nothing in the
   pool is unexamined. The deletable fraction, measured three times
   independently, is **one in two** (19/32, 21/42, 40/75).
4. ~~**A cone pass**, to re-decide §10b and §10c cluster 2, and to check the 44
   dead instances that the textual method is blind to.~~ **DONE 2026-08-27,
   §13.** It cost 8m22s and 5.4 GB with the pointer-cached walk, and it
   answered all three questions: §10b's layer is real and is kept (§13.4);
   §10c's two clusters are one finding and both are outside the cone (§13.5);
   of the 44 "dead" instances **38 are live** and 6 are not (§13.2). The
   fourth answer was the one not asked for — the two methods disagree on 810
   declarations, and where they disagree the cone is right (§13.6).
5. ~~**§5.1, the three copies of 163II's projection argument.**~~ **DONE
   2026-08-27, and the recommendation's premise was wrong** — see the
   correction at the head of §5.1.  The thesis cites the *uniqueness* half of
   163II, which is live; the projection argument is ours, printed at none of
   the three sites.  The bridge was costed at ~100 lines against 71
   duplicated (the *measured* duplication, not the recorded "60 at each of two
   sites"), with **one** customer, and was **not built**.  What was built
   is the thesis's own proof of **164II**.1 (dils.tex:5311), which removed one
   of the three copies; the limb keeps no consumer and moves to §6.
6. **Leave §5.4, §5.5, §5.6, §6 and §8 alone.** Each has a written reason, and
   in the case of §5.6 the repair would weaken the statement.
   **Re-checked 2026-08-28, and unlike §5.1 and §5.2 they hold.**  That check
   was owed: §5.1 and §5.2 came out of the same sweep, in the same voice, and
   both premises dissolved on contact with the source.  These three do not.
   Every factual claim underneath them was put back to the tree and the .tex:
   all three limbs are still at zero consumers; 13VI's in-proof comment is
   where §5.4 quotes it, and cstar.tex:1949 does assert the derived series'
   radius in passing, in those words ("because the radius of convergence of
   `∑ₙ aₙ n z^{n−1}` is `R>r`"); §5.6's two quoted comments are both still
   there, and the shared estimate `norm_apply_mul_le_of_nonneg` is still
   consumed, so what is dead really is only the packaged Lemma.  The one claim
   worth singling out is §5.5's, because its *form* is the one that was wrong
   about `ModularGroup`/`TomitaTakesaki`: "`rightMulEquiv` … in `Paschke.lean`,
   which **imports** this file, so it cannot be used here".  The import graph
   was walked: `Theses.B.Dils.Paschke` does reach
   `Theses.A.CStar.TowardsVN`, and `TowardsVN` does not reach `Paschke`.  The
   direction is right and the reason stands.
7. ~~**The §5 shortlist, eight declarations unread.**~~ **DONE 2026-08-28,
   §5.7.** Seven terminal, one a *trap* — `sqrt_lemma_monotone` proves a clause
   of 23II through a lemma that rests on 23II's own existence half, which the
   thesis rules out in as many words. It is annotated, and it must not be
   deleted: being dead is what keeps the tree acyclic. The pass also corrected
   two rows of the shortlist's own table.

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

### 12a. The fixing round of 2026-08-27 (§11 item 3, `B/` half)

**19 declarations, 114 lines deleted** — the first thing this document has ever
removed from the tree. Full account, including the six kept with reasons and
the two members of §7's own table that turned out to be live or rowed, in §7a.

* `B/Dils/SelfDualCompletion.lean` — 9 declarations, 61 lines.
* `B/Dils/Paschke.lean` — 6 declarations, 28 lines.
* `B/Eff/StatesPredicates.lean` — 4 declarations, 25 lines.
* `B/Eff/EffectAlgebras.lean` — nothing: all four of its candidates are kept
  with a reason (two "unreferenced by design", one prose-cited, one accessor).

No statement was changed, no `sorry` added or removed (eleven, all deliberate),
and no audit row was edited or deleted — none of the 19 was rowed. Every edited
file and every file downstream of one was rebuilt individually at exit 0:
`SelfDualCompletion`, `Kaplansky`, `Paschke`, `SelfDual`, `Pure`,
`StatesPredicates`, `Quotients`, `DiamondAmp`, `Dagger`, `Comparisons`,
`VNExamples`. `scripts/audit_check.py`: 0 orphaned, 0 unrecorded, 0 phantom,
0 schema, 0 unrowed, 0 misplaced. `scripts/coverage.py`: 669/669 claims, 64/64
mixed.

`docs/status.txt` is now stale by 19 rows: it is written by
`scripts/StatusDump.lean` and names every declaration, so the deleted ones are
still listed there until it is regenerated. Nothing reads it except
`scripts/sorry_map.py`, and it was not regenerated here because doing so
rebuilds the whole tree, which the `A/` worker held.

The `A/` half of the pool was spent the same day; see §12b.

### 12b. The fixing round of 2026-08-27 (§11 item 3, `A/` half)

**26 declarations, 225 lines deleted** — 21 from the `A/` half of §7's pool and
the five that §7a's own deletions orphaned.  Full account, including the
eight-declaration package kept whole, the fourth mechanism by which a textual
zero-use lies, and the third member of §7's own table that turns out to be ruled
kept, in §7b.

* `A/Proc/QuantumLambda.lean` — 9 declarations, 58 lines.
* `A/Proc/TensorTransport.lean` — 6 declarations, 36 lines.
* `A/Proc/Commutation.lean` — 1 declaration, 37 lines.
* `A/VN/ModularTensor.lean` — 1 declaration, 22 lines.
* `A/CStar/Positive.lean` — 3 declarations, 15 lines: the whole of that file's
  re-derived pool.
* `A/VN/Tomita.lean` — 1 declaration, 5 lines.  The other eleven candidates are
  kept, eight of them as one block.
* `B/Dils/SelfDualCompletion.lean`, `B/Dils/Paschke.lean`,
  `B/Eff/StatesPredicates.lean` — the five orphans of §7a, 52 lines.

No statement was changed, no `sorry` added or removed (eleven, all deliberate),
and no audit row was edited or deleted — none of the 26 was rowed.  **One doc
comment was changed**, and it is the only prose edit in either half of this
round: the `WstarTransport` section overview in `A/Proc/QuantumLambda.lean`
listed `tensorSub_inf_of_intersection_tensor` in a bullet beside its two-sided
companion, so that bullet was rewritten in the same edit to name only the
companion and to record where the one-sided form went.

Every edited file and every file downstream of one was rebuilt individually at
exit 0 — which, because `A/CStar/Positive` sits at the head of the import chain,
is the whole tree in import order from `A/CStar/Basic` to `B/Eff/VNExamples` —
and a full `lake build` then confirmed it.  `scripts/audit_check.py`: 0
orphaned, 0 unrecorded, 0 phantom, 0 schema, 0 unrowed, 0 misplaced.
`scripts/coverage.py`: 669/669 claims, 64/64 mixed.

`docs/status.txt` is now stale by 45 rows — §12a's 19 and these 26.  It is
written by `scripts/StatusDump.lean` and names every declaration, so the deleted
ones are still listed there until it is regenerated; nothing reads it except
`scripts/sorry_map.py`.

**Where the pool stands.**  Re-derived at `5a0bd16` — that is, after §7a — it
is **130 declarations, 83 in `A/` and 47 in `B/`**, not §7's 190.  Across the
two halves **74 candidates were put in front of a compiler and 40 were deleted**,
a little over one in two; §7a's 19 came out of 32 `B/` candidates and this
round's 21 out of 42 `A/` ones.  What is left after this round is **109**: 62 in
`A/` (41 never examined, 21 examined and kept) and 47 in `B/` (34 never
examined, 13 examined and kept).  §7b names the fourteen `A/` files that hold
the untouched 41.

The three declarations this round orphaned, and the five that §7a orphaned and
this round deleted, are the cone effect of §11.4 measured twice: **two rounds,
eight new limbs, and the second round's three were all cited in §10 as evidence
that a block was not dead.**

### 12c. The fixing round of 2026-08-28 (§11 item 3, the pool's remainder)

**40 declarations, 295 lines deleted** — the whole of what §7a and §7b left
unexamined, and two of the three limbs §7b's own deletions created.  Full
account, including the **seventh** mechanism by which a textual zero-use lies
(a declaration named in an audit row's `note` field, not its `lean_name`), an
eighth in the DISP-tag regex, and the eight keeps that came out of module
docstrings' "Main results", in §7c.

* `A/Proc/Tensor.lean` — 6 declarations, 55 lines.
* `A/Proc/Commutation.lean` — 2 declarations, 21 lines.
* `A/Proc/CommutationCyclic.lean` — 2 declarations, 15 lines.
* `A/Proc/CommutationReduction.lean` — 1 declaration, 16 lines.
* `A/Proc/Compression.lean` — 1 declaration, 15 lines.
* `A/Proc/QuantumLambda.lean` — 1 declaration, 12 lines.
* `A/Proc/TensorTransport.lean` — 1 declaration, 11 lines.
* `A/Proc/CornerTensor.lean` — 1 declaration, 4 lines.
* `A/VN/Modular.lean` — 3 declarations, 13 lines.
* `A/VN/StandardSubspace.lean` — 3 declarations, 12 lines.
* `A/VN/Basic.lean` — 2 declarations, 10 lines.
* `A/VN/TomitaAnalytic.lean` — 2 declarations, 8 lines.
* `A/VN/TomitaTakesaki.lean` — 2 declarations, 7 lines.
* `A/VN/NormalFunctionals.lean` — 1 declaration, 4 lines.
* `B/Eff/Effectus.lean` — 3 declarations, 26 lines.
* `B/Eff/VNExamples.lean` — 3 declarations, 24 lines.
* `B/Dils/HilbertModules.lean` — 2 declarations, 17 lines.
* `B/Eff/Dagger.lean` — 1 declaration, 11 lines.
* `B/Dils/SelfDual.lean` — 2 declarations, 9 lines.
* `B/Eff/DiamondAmp.lean` — 1 declaration, 5 lines.

No statement was changed, no `sorry` added or removed (eleven, all deliberate),
no audit row was edited or deleted — none of the 40 was rowed in `lean_name` —
and, unlike §12b, **no doc comment was changed either**: every prose citation
this round turned up is a citation of something it kept, which is why it kept
it.  A full `lake build` finished at exit 0 after the whole tree had been
rebuilt in import order from `A/CStar/Basic` to `B/Eff/VNExamples`.
`scripts/audit_check.py`: 0 orphaned, 0 unrecorded, 0 phantom, 0 schema,
0 unrowed, 0 misplaced.  `scripts/coverage.py`: 669/669 claims, 64/64 mixed.

**Where the pool stands: it is spent.**  The re-derived scan reports **71**
declarations, and every one of them has a written reason — 67 examined and
ruled kept across §7a (13), §7b (19) and §7c (35), and four of the five limbs
this round created.  Across the three rounds **149 pool candidates were put in
front of a compiler and 80 were deleted** — 19 of §7a's 32, 21 of §7b's 42, 40
of §7c's 75, a hair over one in two every time — and with §7b's five orphans
that is **85 declarations and 634 lines** (114 + 225 + 295), against a pool §7
recorded as 190 declarations and 2,111 lines.

The five declarations this round orphaned — `CT_uconj_iff` and
`uconj_cornerAlg` (`TensorTransport`), `zero_smul'` (`HilbertModules`),
`gnsElemVecs` (`A/VN/Basic`) and the rowed `gnsElemVecsOn`
(`A/VN/NormalFunctionals`) — are the cone effect of §11.4 measured a third
time: **three rounds, thirteen new limbs (5, 3, 5), and each round's are
outside the pool the next one is handed.**

### 12d. The fourth pool round (2026-08-28, `A/Proc/TensorTransport.lean`)

§12c's forty deletions left five limbs behind and said they were "left in
place".  Two of them were in `TensorTransport`, and taking them meant taking
the block they belonged to, because the block's remaining members consumed
only each other.  So the fourth round is a *block* deletion rather than a list
of independent ones, and the criterion has to be stated at the block level:
**no declaration outside the block used any member of it.**  That was checked
against `e612c93` for each of the five, not against the working tree, and it
held for all five.

| deleted | line at `e612c93` | direct uses, all inside the block |
|---|---|---|
| `cornerTransfer` | `:789` | 4 |
| `adjoint_cornerTransfer` | `:792` | 3 |
| `isUnitaryCLM_cornerTransfer` | `:801` | 1 |
| `cext_cornerTransfer_cmpr` | `:823` | 2 |
| `uconj_cornerAlg` | `:845` | 0 |

**104 lines, 5 declarations** (56 → 51), together with the `section
CornerChoice` header, its `variable` block, the section prose *"Independence of
the choice of corner"* — whose subject `CT_of_CT_corner_any` §12c had already
deleted — and the `section CornerPayoff` that §12b had emptied and left
standing.  None of the five is named by an audit row: `scripts/audit_check.py`
reports 0 phantom rows after the deletion.

**This is the pool, not the cone.**  §13.5 put ten declarations of this file
outside the cone and re-described clusters 1 and 2 as one finding; that verdict
is a record and not a deletion order, and it is not what was executed here.
What made these five deletable is the ordinary pool test — zero direct use,
unrowed, untagged — which they failed at `0e9f7ff` and passed only after §12c
removed their last two external consumers.  Cluster 1 is equally outside the
cone and is **untouched**, because `CT_top_right` is cited by name in the
module header (§12c) and its siblings were already gone.

**And the round created three more limbs, in the same file.**  `coe_uconj`
(`:191`) and `CT_uconj_iff` (`:545`) are now at zero uses; `uconj_concreteTensor`
(`:527`) has two, both inside `CT_uconj_iff`.  §12c had already named
`CT_uconj_iff` as one of its five and left it; it is left again, with the other
two.  Four rounds now, and the tail is not shrinking as fast as §12c hoped: 5,
3, 5, 3.

**A seventh check, and the deletions are what needed it.**  `docs/status.txt`
is generated by `scripts/StatusDump.lean` and is the data behind the Sorry Map
and behind every "it is `green`" in these pages — §5.3's argument that 125VI is
not blocked is exactly such a lookup.  It is regenerated by hand, so a deletion
round leaves it naming declarations that are gone, and a reader checking a name
against it gets a `green` for something that no longer exists.  §12d's four
deleted theorems sat in it for a day.  `scripts/audit_check.py` now reports
them as **STALE**, and status.txt has been regenerated: 6432 rows, the four
gone and `htmul_mem_modularSqrt_domain` added.

Only that direction is checked — the file holds theorems only, so a `def`
missing from it is not an error — and two classes of name have to be excluded
because Lean synthesises them and they appear in no source: `instFooBar` from an
anonymous `instance`, and `toParentClass` from an `extends`.  Without those
exclusions the check reports 305 names; with them it reported exactly the four.

---

## 13. The cone pass (2026-08-27, commit `5a0bd16`)

*§11 item 4, run.  **The walk finished**: 8 min 22 s wall, 5.4 GB peak RSS,
exit 0, over the compiled `.olean`s.  No Lean was written into `Theses/`,
nothing was deleted, and no audit row was touched.*

**As-of.** The environment walked is the tree's oleans at `5a0bd16`, with one
known drift: the `A/` worker had already rebuilt `A/CStar/Positive.olean` when
the walk started, so three declarations present in `5a0bd16`'s source
(`arg_eq_arctan`, `thesisPos_one`, `mul_le_meet_mul_add`) are absent from the
environment.  Nothing else in the tree had drifted — every other one of the
7,471 source declarations at `5a0bd16` paired with an environment constant.

### 13.1 The method that worked, and its cost

`Expr.getUsedConstants` was **not** used; §1 is right that it has no DAG cache.
What worked is a walk memoised on `ExprStructEq` — `Expr`'s hash is cached
inside the node, so a repeat visit to a shared subterm is an O(1) hash hit:

```lean
structure St where
  seen : Std.HashSet ExprStructEq := {}
  out  : Std.HashSet Name := {}

partial def visit (e : Expr) : StateM St Unit := do
  match e with
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => return
  | .const n _ => modify fun s => { s with out := s.out.insert n }
  | _ =>
    if (← get).seen.contains ⟨e⟩ then return      -- the cache §1 says is required
    modify fun s => { s with seen := s.seen.insert ⟨e⟩ }
    match e with
    | .app f a       => do visit f; visit a
    | .lam _ t b _   => do visit t; visit b
    | .forallE _ t b _ => do visit t; visit b
    | .letE _ t v b _  => do visit t; visit v; visit b
    | .mdata _ b     => visit b
    | .proj n _ b    => do modify (fun s => { s with out := s.out.insert n }); visit b
    | _ => return
```

driven over `ci.type` **and** `ci.value? (allowOpaque := true)` (§1's first
trap) for every constant whose module is `Theses.A*`/`Theses.B*`, with a fresh
cache per declaration so memory stays flat.  Edges are kept only where the
target is also a `Theses` constant — Mathlib compiles before `Theses`, so no
`Theses` fact can be reached through a Mathlib one, and the internal graph is
complete.

* **13,702** environment constants in `Theses` modules (7,471 of them
  hand-written source declarations; the rest are projections, `.rec`, `.mk`,
  `_proof_*`, `match_*`, which are collapsed onto the source declaration they
  belong to before any count is taken).
* **95,882** `Theses` → `Theses` edges.
* **8 min 22 s / 5.4 GB / exit 0**, of which ~10 s is `import Theses`.  No
  declaration stalled; the walk is linear in the size of the term DAG, which is
  exactly what §1 predicted a cached traversal would be.
* Run as a single `elab` command in a scratch file under the §1 invocation
  (`LEAN_PATH=…` plus both `-D` flags); it never recompiles anything, so it is
  safe to run while another worker holds the tree.  Stream the output to a file
  handle and flush every 500 declarations — a version that accumulated the rows
  in an `Array` and wrote at the end gave no way to tell a slow run from a hung
  one.

The **textual** side was re-derived here too, from a checkout of `5a0bd16`, so
that the two methods could be compared declaration by declaration.  That
re-derivation reproduces this document's published numbers closely enough to
stand in for the original scan: the per-file *total* declaration count matches
§3 exactly on all 44 files (bar the two files §7a has since shrunk), the
per-file *dead* count matches on 39 of them, and it finds **exactly the 44 dead
named `instance`s** of §2 and §8.

### 13.2 Question 1 — the 44 dead instances: **38 are live, 6 are not**

The Lean walk sees typeclass synthesis, so this is decidable and now decided.
**38 of the 44 have consumers**, several of them heavy ones —
`UnUnif.instUniformSpace` 123, `vonNeumannAlgebra_lp_infty` 58, `ksSMul` 37,
`factIsStarProjectionCeil` 34, `ncUniformSMul` 34, `scalEffectMonoid` 26,
`instVonNeumannAlgebraCU` 23.  §8's quarantine was right and the instances
should not be counted as dead.

The six with **no consumer anywhere in the compiled tree**:

| declaration | file:line (`5a0bd16`) | DISP | could anything downstream want it? |
|---|---|---|---|
| `Theses.A.Proc.factIsStarProjectionSuppProj` | `A/Proc/Measurement.lean:334` | — | **The only one that is noise.** One of four sibling `Fact (IsStarProjection …)` registrations; the other three have 34, 15 and 10 consumers. Costs two lines; any future lemma about `suppProj` that wants a `Fact` would find it. **Keep, do not count.** |
| `Theses.A.Proc.linfCoreflective` | `A/Proc/QuantumLambda.lean:659` | 122VI.3 | No. It *is* the Exercise's second half (`Set` is coreflective in `(W*_miu)^op`). Nothing can consume it until W\*_miu is a `Category` — the same statement-level block §6 records for the nine `vn_smc_*` of 119V. Class 2. |
| `Theses.B.Eff.effectus_has_all_kernels` | `B/Eff/Quotients.lean:786` | 200III | No. It is 200III's first sentence, packaged as a `HasAllKernels` instance; the form proofs use is its sibling `isKernel_comprMap` eight lines below. Class 2. |
| `Theses.B.Eff.effectus_has_all_cokernels` | `B/Eff/Quotients.lean:1450` | 205II | No. Same shape as the row above, for 205II. Class 2. |
| `Theses.B.Eff.unitInterval.effectDivisoid` | `B/Eff/StatesPredicates.lean:6936` | 195V.1 | No — it is an Example (`[0,1]` is an effect divisoid). Class 2. |
| `Theses.B.Eff.prodEffectDivisoid` | `B/Eff/StatesPredicates.lean:7056` | 195V.2 | No — the Example that the product of two effect divisoids is one. Class 2. |

So **five of the six are DISP-tagged thesis statements, terminal by intent**,
and the sixth is a two-line `Fact`.  There is nothing to delete here, and §8's
sentence "the Lean term walk *can* see those; a future cone pass should
re-check them" is now discharged: **the instance census yields no deletion.**

One hazard the census exposes: `prodEffectMonoid`
(`B/Eff/StatesPredicates.lean:7034`, untagged, unrowed) has exactly **one**
consumer, `prodEffectDivisoid`, which has none.  It is a dead two-block whose
head carries 195V.2, so `prodEffectMonoid` must not be deleted on its own.  It
is inside §8's instance quarantine, which is what protects it.

### 13.3 The cone, and what it is measured against

Roots: every declaration whose doc comment **opens** with a DISP tag (1,959) or
which an audit row names (2,322) — union **2,574**.  Forward closure over the
dependency graph:

| | count |
|---|---|
| source declarations at `5a0bd16` | 7,471 |
| **in the cone of something the theses claim** | **6,981** |
| **outside it** | **490 (6.6%)** |
| — of those, with at least one term-level consumer | **100** |
| — of those, textually *live* | 208 |

Those **100** are the shape direct zero-use cannot see: every member has a
consumer, and the block has none.  Grouped into weakly connected components,
the components of three or more are:

| size | where | what |
|---|---|---|
| 26 | `A/VN/ModularGroup.lean` | **the `jConj` layer — §10b, confirmed below** |
| 17 | `B/Eff/EffectAlgebras.lean` | the `WrightTriangle` refutation, kept unreferenced by design (§6, §7a) |
| 15 | `A/VN/Tomita.lean` 9, `A/VN/ModularTensor.lean` 5, `A/VN/Modular.lean` 1 | the `modularSqrt` (Δ^{1/2}) package — **§10e, and see below** |
| 14 | `B/Dils/Kaplansky.lean` | the `inv1p`/`rf` resolvent layer under the known-false 158V |
| 10 | `A/Proc/TensorTransport.lean` | **§10c cluster 2, plus three more — confirmed below** |
| 9 | `A/Proc/TensorTransport.lean` 7, `A/Proc/Tensor.lean` 2 | **§10c cluster 1**, plus `amplification`, `amplification'` |
| 8 | `B/Dils/Paschke.lean` | the `paschkeModuleId` non-vacuity check, kept by ruling (§7a) |
| 5 | `A/Proc/QuantumLambda.lean` | the one-sided `tensorSub_inf` chain — §10d, confirmed |
| 5 | `A/VN/Projections.lean` | `saIncl_isLUB`, `compress_surjective`, `restrictNMIU`, `restrictNMIU_apply`, `nmiu_factors_maps` |
| 4 | `B/Eff/StatesPredicates.lean` | the "`AConv₂ ≅ Set`" record, kept by prose citation (§7a) |
| 4 | `A/VN/StandardSubspace.lean` | the `stdConj` wrappers (§10e's smaller instances) |

Five of the eleven are already recorded in this document with a reason, which
is itself a result: **the cone re-derives the previous sweep's hand findings
without being told them.**

### 13.4 Question 2 — §10b, the `jConj` layer: **the 2026-08-26 cone finding is confirmed, exactly**

The cone finds **26** declarations in `A/VN/ModularGroup.lean` outside the cone
of every DISP-tagged and every audit-rowed declaration in the tree — the same
26 the 2026-08-26 pass reported — and they form a *single* connected component,
i.e. a genuine block and not 26 unrelated limbs:

`real_inner_J_map_map` (`:590`), `inner_J_map_map` (`:593`), `jConjRe`
(`:612`), `jConjRe_smul_I` (`:616`), `jConj` (`:621`), `jConj_apply` (`:629`),
`J_apply_eq_jConj` (`:632`), `jConj_one` (`:636`), `jConj_mul` (`:639`),
`jConj_add` (`:646`), `jConj_zero` (`:653`), `jConj_smul` (`:656`),
`jConj_star` (`:664`), `norm_jConj_le` (`:685`), `jConjHom` (`:691`),
`jConjHom_apply` (`:708`), `continuous_jConjHom` (`:711`), `jConj_R` (`:723`),
`jConj_two_sub_R` (`:729`), `jConj_cfc_real` (`:735`), `cpow_conj_ofReal`
(`:756`), `IsPowBase.cpowOp_eq_re_add_im` (`:772`), `jConj_cpowOp` (`:810`),
`J_opPow` (`:1011`), `J_modPow` (`:1029`), `jConj_modPow` (`:1056`).

`jConj` alone has **18** consumers and every one of them is inside this block;
that is why §10b's direct count saw only one hard zero-use (`jConj_modPow`) and
concluded nothing.  **The direct count was not wrong, it was blind, and the
cone is right.**

Two refinements to §10b:

* **The block does not start where the module docstring says.**  `Jisometry`
  (`:586`), which the docstring groups with the layer, is **in** the cone: it
  has two external consumers, `commute_modPow_T` and `modPow_neg_eq_prod` in
  `A/VN/TomitaAnalytic.lean`.  The dead block begins one declaration later.
* Two further members of the file are dead as a *pair* rather than as part of
  the layer: `IsPowBase.denseRange_mul_self` (`:371`, one consumer,
  `opPow_mul`) and `IsPowBase.lipschitzWith_cpowOp` (`:535`, one consumer,
  `continuous_cpowOp`) are inside the cone — they are named here only because
  they are in §7's deletion pool by the textual filters (see §13.6).

The rest of `ModularGroup.lean` — `IsPowBase`, `cpowOp`, `opPow`, `modPow` and
their 60-odd lemmas — is squarely in the cone, reached through
`A/VN/TomitaAnalytic.lean` and `A/VN/TomitaFourier.lean`.  So the file is not
a dead file with a live island; it is a live file with **one dead limb of ~300
lines**, exactly as its own docstring says ("On the record only — nothing
consumes these").  **Verdict: the docstring is accurate, §10b stands as
written, and the layer is a class-2 record — kept, not deleted, because it is
the tree's only statement of `J Δ^{it} J = Δ^{it}`.**

### 13.5 Question 3 — §10c cluster 2: **confirmed, and larger than recorded**

§10c called cluster 2 "no longer an orphan by direct count" and left the cone
claim "not contradicted; not confirmed either".  It is now **confirmed**.  All
seven members of the `cornerTransfer` block are outside the cone, together with
three declarations upstream of them that §10c did not name:

| declaration | line | term-level consumers | all inside the block? |
|---|---|---|---|
| `coe_uconj` | `:201` | 1 | yes |
| `uconj_concreteTensor` | `:536` | 1 | yes |
| `CT_uconj_iff` | `:551` | 1 | yes |
| `cornerTransfer` | `:809` | 5 | yes |
| `adjoint_cornerTransfer` | `:814` | 2 | yes |
| `isUnitaryCLM_cornerTransfer` | `:822` | 2 | yes |
| `cext_cornerTransfer_cmpr` | `:843` | 1 | yes |
| `uconj_cornerAlg` | `:865` | 1 | yes |
| `CT_cornerAlg_congr` | `:884` | 1 | yes |
| `CT_of_CT_corner_any` | `:903` | 0 | — |

`cornerTransfer`'s four-to-five consumers are real and they are all its own
siblings.  **Where the two methods disagree, the cone is right**: §10c's
"no longer an orphan" reads the block's internal traffic as life.

The same holds for **cluster 1**, which §10c called "partly closed" on the
strength of `CT_top_right` acquiring two consumers and `tensorGen_vnComm_top`
one.  Both are outside the cone, and so are their consumers:
`exists_smul_one_of_central` (`:621`), `concreteTensor_top_top` (`:650`),
`mem_vnComm_top` (`:716`), `tensorGen_vnComm_top` (`:725`), `CT_top_right`
(`:743`), `CT_top_left` (`:776`), `CT_top_top` (`:783`), together with
`amplification` and `amplification'` in `A/Proc/Tensor.lean`.  **Cluster 1 is
not partly closed; it is closed nowhere.**

The file's live part ends at `isVNSubalgebra_top` (`:710`).  Everything from
`:621` to the end of the file — 24 of its 70 declarations, roughly 300 of its
925 lines — supports nothing either thesis claims.  **Re-decision: §10c
clusters 1 and 2 are one finding, not two, and the honest description is
"`TensorTransport.lean` stops carrying weight at line 710."**  Whether to
retire it is the same kind of author ruling as §10a's atomic-type-I island:
these are readable special cases of `commutation_theorem`, harmless to keep,
and the cone's verdict is a record, not a deletion order.

### 13.6 The fourth disagreement — and it is the expensive one

Comparing the two methods declaration by declaration over the 7,471 paired
source declarations:

| | count |
|---|---|
| dead by both methods | 810 |
| **textually dead, but the compiled terms use it** | **74** |
| — of those, `instance` (the §8 blind spot, expected) | 38 |
| — of those, **not** an instance | **36** |
| **textually live, but nothing in the tree uses it** | **121** |

**(a) `f.mpr` — the mirror of the trap §7a fixed, and it is still open.**

§7a taught the scanner to index a declaration under its bare last component, so
that `IsCompatExt.norm_ipVal_self_le` reached as `hW.norm_ipVal_self_le` is
seen.  That fix covers the *suffix* case.  The **prefix** case was never fixed:
a use written `le_vnComm_comm.mpr` tokenises as the single identifier
`le_vnComm_comm.mpr`, whose suffixes are `le_vnComm_comm.mpr` and `mpr` —
**never `le_vnComm_comm`**.  Every `foo.mp`, `foo.mpr`, `foo.symm`, `foo.1`,
`foo.le`, `foo.choose` use of a named lemma is therefore invisible.

That is the mechanism behind **33 of the 36**: for each of them the textual
scan finds no bare occurrence anywhere in 163,848 lines, and the source does
contain the name in a `name.something` form.  **Where the two disagree here, the
cone is right and the textual scan is wrong**, and the cost is not theoretical:
**25 of these declarations are inside §7's class-3 deletion pool** — untagged,
unrowed, not accessors, no `@[simp]` — i.e. they are on the list a fixing round
is told it may delete.

| declaration | file:line (`5a0bd16`) | term consumers | consuming files |
|---|---|---|---|
| `A.Proc.le_vnComm_comm` | `A/Proc/Commutation.lean:210` | 4 | `A/Proc/Commutation.lean`, `A/Proc/CommutationTheorem.lean`, `A/Proc/Compression.lean` |
| `A.VN.le_iff_matForm` | `A/VN/Basic.lean:5218` | 4 | `A/VN/Basic.lean`, `A/VN/Completeness.lean` |
| `B.Eff.saDown_le_iff` | `B/Eff/VNExamples.lean:490` | 3 | `B/Eff/VNExamples.lean` |
| `A.Proc.IsCorner.isStarProjection` | `A/Proc/CornerTensor.lean:97` | 2 | `A/Proc/CornerTensor.lean` |
| `A.VN.suppProj_eq_zero_iff` | `A/VN/Projections.lean:2922` | 2 | `A/VN/Projections.lean` |
| `RvD.differentiable_sinq` | `A/VN/TomitaStrip.lean:424` | 2 | `A/VN/TomitaStrip.lean` |
| `B.Dils.rf_continuous` | `B/Dils/Kaplansky.lean:190` | 2 | `B/Dils/Kaplansky.lean` |
| `B.Eff.SPred.isSup_iff_isSupSet` | `B/Eff/DiamondAmp.lean:236` | 2 | `B/Eff/DiamondAmp.lean` |
| `B.Eff.CoprodPres.eTTT` | `B/Eff/StatesPredicates.lean:820` | 2 | `B/Eff/StatesPredicates.lean` |
| `A.Proc.isUnitaryCLM_one` | `A/Proc/CommutationAmplify.lean:361` | 1 | `A/Proc/CommutationAmplify.lean` |
| `A.Proc.Corner.isClosed_cornerSet` | `A/Proc/Measurement.lean:587` | 1 | `A/Proc/Measurement.lean` |
| `A.Proc.continuous_diagChi` | `A/Proc/Tensor.lean:7204` | 1 | `A/Proc/Tensor.lean` |
| `A.Proc.summable_diagTerm` | `A/Proc/Tensor.lean:7184` | 1 | `A/Proc/Tensor.lean` |
| `A.Proc.mem_vnComm_top` | `A/Proc/TensorTransport.lean:717` | 1 | `A/Proc/TensorTransport.lean` |
| `RvD.IsPowBase.denseRange_mul_self` | `A/VN/ModularGroup.lean:371` | 1 | `A/VN/ModularGroup.lean` |
| `RvD.IsPowBase.lipschitzWith_cpowOp` | `A/VN/ModularGroup.lean:535` | 1 | `A/VN/ModularGroup.lean` |
| `A.VN.CentrePositiveSeparating.centralProj` | `A/VN/Projections.lean:7633` | 1 | `A/VN/Projections.lean` |
| `B.Dils.lipschitz_lk_fst` | `B/Dils/Kaplansky.lean:1565` | 1 | `B/Dils/Kaplansky.lean` |
| `B.Dils.lipschitz_lk_snd` | `B/Dils/Kaplansky.lean:1571` | 1 | `B/Dils/Kaplansky.lean` |
| `B.Eff.SPred.isInf_iff_isInfSet` | `B/Eff/DiamondAmp.lean:252` | 1 | `B/Eff/DiamondAmp.lean` |
| `B.Eff.pcm_isSumOf_pair_iff` | `B/Eff/Effectus.lean:378` | 1 | `B/Eff/Effectus.lean` |
| `B.Eff.op_le_iff` | `B/Eff/StatesPredicates.lean:5391` | 1 | `B/Eff/DiamondAmp.lean` |
| `B.Eff.prod_le_iff` | `B/Eff/StatesPredicates.lean:7024` | 1 | `B/Eff/StatesPredicates.lean` |
| `B.Eff.unitInterval_le_iff` | `B/Eff/StatesPredicates.lean:6920` | 1 | `B/Eff/StatesPredicates.lean` |
| `B.Eff.cuUpLin` | `B/Eff/VNExamples.lean:2171` | 1 | `B/Eff/VNExamples.lean` |

**All twenty-five survive — checked 2026-08-28, and this is the check the
warning was for.**  §7's pool was spent in four rounds after this table was
written (§12a–§12d, 90 declarations deleted), and every one of the twenty-five
is still defined in the tree: `SPred.isSup_iff_isSupSet`,
`SPred.isInf_iff_isInfSet` and `CentrePositiveSeparating.centralProj` are
declared with their namespace in the name, the other twenty-two plainly.  The
warning was heeded, or the rounds were lucky; either way nothing was lost.

**And the rule now has one implementation in the repository.**  The scanner
this table indicts is not checked in — it was a worker's script — but
`scripts/limb_check.py` counts uses for the same purpose, and it had the trap
half-fixed: its bound allowed a dot *after* the name, so `le_vnComm_comm.mpr`
counted, and forbade one *before* it, so `hW.norm_ipVal_self_le` and
`hΩ.centralProj.conj` did not.  Bounding on identifier characters alone fixes
both directions; measured on this table's own names, `centralProj` goes 0 → 2,
`SPred.isSup_iff_isSupSet` 0 → 5, and `norm_ipVal_self_le` 0 → 4, while
`le_vnComm_comm` was already right at 7.  It over-counts a short name against
Mathlib's, which is the safe direction: over-counting reports a limb alive and a
person looks, under-counting confirms a stale dead-claim in silence.

The first row is the sharpest.  `le_vnComm_comm` is the Galois connection for
the bundled commutant; three of its four consumers are in
`A/Proc/CommutationTheorem.lean` and `A/Proc/Compression.lean` — and §3's table
calls `CommutationTheorem` "fully consumed".  **Deleting it on this document's
own pool list would break the proof of the commutation theorem.**  It was in
the pool at `9a69966` too; the `B/` half of §7a happened to contain none of
these 25, which is why the deletion round of 2026-08-27 got away with it.

**Add to §1, as the fourth implementation trap:** *index a use token under
**every contiguous run of its dotted components**, not only its suffixes.*  A
scanner that indexes `le_vnComm_comm.mpr` under `mpr` but not under
`le_vnComm_comm` will delete live lemmas, and every `_iff` lemma in the tree is
exposed to it.  Suffixes alone are not enough and prefixes alone are not
either: `CentrePositiveSeparating.centralProj` is used at
`A/VN/Projections.lean:7719` as `hΩ.centralProj.conj`, where the name it needs
to be found under is neither the first component nor the last.

The other eleven of the 36 are already quarantined by §8 or by a DISP tag and
are **not** at risk: `eabasics_le_iff_orth_le` (175V.6, **36** consumers),
`PartialMap` (180I, 12 — an `abbrev`, so it can be consumed with no constant
left behind at all), `bax_le_iff` (32XV, 4), `open_almost_clopen` (54IX, 2),
`totIsInitial` (181XII, 2), `spectrum_bounded_3` (11VI, 1),
`bax_isSelfAdjoint_iff` and `mem_bax_iff` (both rowed), and the three `@[simp]`
lemmas `mem_cstarEqualiser`, `freeMap_comp`, `freeMap_id`.

**(b) The other direction: 121 declarations the textual scan calls live are
term-dead.**  These are suffix collisions — the price of §7a's fix.  The worst
is `RvD.IsCommutingPair.symm` (`A/VN/Modular.lean:570`) with **1,777** textual
"uses", every one of them somebody else's `symm`; then `PCMCat.of` (424),
`CommCmpr.one` (178), `CommCmpr.mul` (169), `CommCmpr.smul` (108), and a long
tail of `.val_one` / `.val_zero` / `.norm_def` / `.le_def` accessors whose last
component is shared across four or five namespaces.  **This resolves the one
item §10f left open**: `IsCommutingPair.symm` was recorded as "cannot be used
as written… the textual method cannot separate it from Mathlib's.  Unresolved;
needs a term-level check."  The check has been run: **zero consumers.  The
2026-08-26 verdict was right.**

Netting the two directions, the tree's true zero-consumer count at `5a0bd16` is
**931 of 7,471 source declarations (12.5%)** — close to §2's 916, but not the
same 916: 74 of §2's are live and 121 declarations it counts as live are not.

### 13.7 Two corrections to §10 that the cone forces

* **§10e is too generous to itself.**  It records that
  `modularSqrt_opTensor` "now has 1 use" and `modularSqrt_htmul` "2, so the
  chain is no longer dead end to end".  Both are outside the cone.
  `modularSqrt_opTensor`'s one consumer is `modularSqrt_htmul`;
  `modularSqrt_htmul`'s two are `modularSqrt_htmul_pkg` and
  `modularSqrt_orbit`, which have none.  The whole Δ^{1/2} package —
  `A/VN/Tomita.lean:658–708` (`modularSqrt`, which has **10** consumers, all
  its own siblings) together with `A/VN/ModularTensor.lean:1081–1230` — is
  dead **as a block**, 15 declarations across three files.  §10e's structural
  diagnosis ("the package ships no domain-membership dischargers, so a consumer
  must drop out of the package vocabulary") is exactly right and is now
  measured: the package has never once been entered from outside.
* **§10c's cluster 1 / cluster 2 split does not survive.**  See §13.5.

### 13.8 What a next pass should not repeat

* The whole-tree term walk is **tractable** and the 2026-08-26 failure was the
  missing cache, nothing else.  It need not be attempted textually again.
  Budget ten minutes and 6 GB, not an hour and 5 GB.
* Do **not** accumulate the output in memory and write at the end.  The first
  attempt here did, ran for six minutes with nothing on disk, and could not be
  distinguished from a hang; it was killed on suspicion and the run wasted.
  Stream and flush.
* `Lean.Meta.isInstance` is `CoreM`, so it needs `liftCoreM` inside a
  `CommandElabM` `elab`; and `meta` is a reserved token, so it cannot be a
  `let mut` name.  Both cost a five-minute reload of Mathlib to discover.
* Two concurrent `lean` processes each holding the `Theses` environment is
  ~10 GB and will be killed on this box.  Check for an already-running walk
  before launching one.

### 13.9 Changes applied

**None to the tree.**  No declaration deleted, no statement changed, no `sorry`
added or removed, no audit row edited.  This section is the whole of the
output.  The one action item it creates for someone else is §13.6's prefix-
indexing fix to the textual scanner, and the 25 declarations it names must come
off §7's deletion pool before the `A/` half of that pool is spent.

*Closed 2026-08-28.*  Both halves of that item are discharged: the twenty-five
were checked one by one after the pool was spent and **all twenty-five are still
in the tree**, and the indexing rule is implemented in the one use-counter the
repository actually contains, `scripts/limb_check.py` — see §13.6.  What is
*not* discharged, and cannot be from here, is the scanner itself: it was never
checked in, so the next person to write one inherits §1's trap list and nothing
more.

---

## 14. Re-checking this document (`scripts/limb_check.py`, 2026-08-28)

Every "confirmed dead", every "zero consumers", every "still dead" in the
pages above was true when it was written, and nothing rechecks any of them.
That is how §5.1 and §5.2 both came to rest on premises that had expired, and
how §10c's "no longer an orphan by direct count" survived until a cone pass
contradicted it.  `scripts/limb_check.py` re-counts them: it pulls the names
out of the dead-claims, counts their *code* uses in `Theses/` with comments
blanked and the defining occurrence not counted, and reports the ones that are
alive.  A name the tree no longer has is reported apart — that is a deletion
this document records, not a stale claim.

**What it reads, and why so little.**  Prose is not read at all.  The first
version read sentences and was wrong eleven times out of twelve, always the
same way: the document was saying a name is *alive* in the very sentence that
carried a dead-claim about something else — "parsec 1490's proofs go through
`unSeminorm_add_le` directly", "**`mem_vnComm_top` is named as dead by both §7
and §10c**, and it is not".  A sentence cannot be read for its subject with a
regex.  So only two structured positions are used: the names a **bullet opens
with**, and the **first cell of a table row**, which is where this document
puts the declaration a claim is about.  Parenthesised annotations are dropped,
because the convention here is `` `ipf_sub_right` (`SelfDualCompletion`) `` and
some file names are also declaration names.

That buys precision at the cost of recall: **28 names re-counted** out of a
document that mentions hundreds.  It is a check on the claims that are stated
in the form the sweep states them, not a liveness audit of the tree.  It
inherits §1's eight ways a textual zero-use lies, so a name it reports as alive
really does occur, and a name it passes may still be reached through a dotted
projection.

**The first thing it found was a line eight hours old.**  §12c's kept-list
opened a bullet with `opTensor_mem_modularSqrt_domain` among the zero-use
declarations; §10e's ruling, taken the same day, added
`htmul_mem_modularSqrt_domain`, which consumes it.  The bullet was rewritten and
the check reads zero.  The lesson is not about that declaration: a document
this size grows stale claims faster than a sweep can reread it, and the only
claims worth stating in the sweep's structured form are the ones a script can
keep honest.
