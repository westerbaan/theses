# Dead limbs in the commutation-theorem development

*Audit of 2026-08-26, over the ~20,000 lines added in eighteen rounds by
eighteen workers on 2026-08-25/26: `A/VN/{Modular, StandardSubspace,
ModularGroup, Tomita, ModularTensor, TomitaTakesaki, TomitaStrip, TomitaFourier,
TomitaAnalytic, CommutationTomita}.lean`, `A/Proc/{Commutation, CornerTensor,
TensorTransport, CommutationReduction, CommutationAmplify, Compression,
CommutationCyclic, CommutationTheorem}.lean`, and the additions to
`A/Proc/{Tensor, QuantumLambda}.lean`.*

The standing check: enumerate every declaration with no consumer, and for each
ask whether it is genuinely terminal or the fingerprint of a proof that went
around something. Read with `docs/COMMUTATION-THEOREM.md`.

**Read this first.** The single number to quote is **≈ 1,456 lines in 129
declarations that lie outside the dependency cone of every headline theorem**,
plus two further blocks of **813** and **~130** lines, for **≈ 2,270 lines with
no consumer out of ~20,000 — about 11%.** Nothing here is broken, nothing is
`sorry`-ed, and no headline result is at risk. Most of it is over-generated API,
not abandoned mathematics. The parts that cost something are named in §7.

---

## 1. Method, and a tooling trap worth an hour

A Lean meta-program walked `env.header.moduleData` and computed, for every
declaration in the twenty files, the set of declarations anywhere in `Theses/`
whose **type or proof term** mentions it. Two corrections were needed before the
numbers meant anything.

**`ConstantInfo.value?` returns `none` for theorems in Lean 4.34.** You must
either match `.thmInfo v => v.value` explicitly or call
`ConstantInfo.value? (allowOpaque := true)`. With the default, proof bodies are
invisible and only *statements* contribute edges; the first run of this audit
reported 77% of the development unused. If a future pass produces an
implausible number, this is why.

**`@[simp]`/`rfl` lemmas cannot be detected by this method at all.** A
definitional rewrite leaves no constant behind, so a live `@[simp] … := rfl`
lemma is indistinguishable from a dead one — and a *textual* grep does not help
either, because a bare `simp` names nothing. Two such lemmas were compile-tested
during this audit (`extOut_apply`, `htKetR_apply`) and both turned out to be
load-bearing. **45 of the 156 candidate hits are in this class and are presumed
live.** See §4.

A second, stronger pass computed reverse reachability from a root set consisting
of every declaration outside the eighteen new files together with the nine
headline theorems. **This cone computation is the fixpoint** — it already
subsumes the cascade of declarations that become dead once the first layer goes
— so its figure, not the raw zero-use count, is the one to quote.

Scripts were scratch-only and are not committed; the whole analysis is about
forty lines of `CoreM` over `moduleData` and is cheaper to rewrite than to
maintain.

---

## 2. Headline numbers

| quantity | count |
|---|---|
| public declarations in the twenty files | 1,593 |
| zero uses anywhere in `Theses/` | 209 |
| — of those, compiler-generated (`.congr_simp`, `.ctorIdx`, notation) | 53 |
| real source declarations with zero uses | 156 |
| — of those, `@[simp]`/`rfl` accessors (undecidable, presumed live) | 45 |
| **hard zero-use** | **111** |
| — in the eighteen new files | 57 |
| — new additions to `Tensor.lean` / `QuantumLambda.lean` | 12 |
| — pre-existing declarations (thesis statements: `vn_smc_*`, `tensor_simple_facts_*`) | 42 |
| **outside the dependency cone of every headline theorem** (the fixpoint) | **129 decls ≈ 1,456 lines** |

Add the `QuantumLambda` atomic-type-I island (813 lines, §5a) and the
`cornerTransfer` island (~130 lines, §5c), neither of which the cone figure
covers because both sit in files whose *other* contents are load-bearing:
**≈ 2,270 lines total.**

---

## 3. Per-file breakdown

Hard zero-use (excluding compiler-generated and `simp`/`rfl`), and lines outside
the headline cone.

| file | hard zero-use | outside cone |
|---|---|---|
| `A/Proc/Tensor.lean` | 31 | *(pre-existing; not scored)* |
| `A/Proc/QuantumLambda.lean` | 23 | *(pre-existing; see §5a)* |
| `A/VN/Tomita.lean` | 11 | 19 decls / ~105 lines |
| `A/VN/Modular.lean` | 9 | 13 / ~92 |
| `A/Proc/TensorTransport.lean` | 7 | 24 / ~389 |
| `A/Proc/Commutation.lean` | 5 | 7 / ~156 |
| `A/VN/StandardSubspace.lean` | 4 | 7 / ~41 |
| `A/VN/ModularTensor.lean` | 4 | 8 / ~131 |
| `A/Proc/Compression.lean` | 4 | 6 / ~39 |
| `A/VN/TomitaTakesaki.lean` | 3 | 7 / ~72 |
| `A/VN/TomitaAnalytic.lean` | 3 | 4 / ~24 |
| `A/Proc/CornerTensor.lean` | 3 | 5 / ~63 |
| `A/Proc/CommutationCyclic.lean` | 2 | 2 / ~13 |
| `A/VN/ModularGroup.lean` | 1 | **26 / ~301** |
| `A/Proc/CommutationReduction.lean` | 1 | 1 / ~30 |
| `A/VN/TomitaStrip.lean` | 0 | 0 |
| `A/Proc/CommutationAmplify.lean` | 0 | 0 |
| `A/Proc/CommutationTheorem.lean` | 0 | 0 |
| `A/VN/CommutationTomita.lean` | 0 | 0 |

Note `ModularGroup.lean`: one hard zero-use declaration, but 26 outside the
cone. That gap *is* the finding of §5b — a self-supporting block in which every
member has a consumer and the block as a whole has none. It is the reason the
cone pass exists.

Four files are fully consumed: `TomitaStrip`, `CommutationAmplify`,
`CommutationTheorem`, `CommutationTomita`.

---

## 4. Classification

| class | count | what it is |
|---|---|---|
| **dead-on-arrival accessor** | 45 | `@[simp]`/`rfl` unfolders. Not scored as dead; see below. |
| **genuinely terminal** | ~35 | Headline statements, dual restatements, deliberately exposed interfaces. |
| **superseded** | ~30 | A later round proved the general form and the earlier one is now unreachable. |
| **orphan** | ~25 | Machinery for a route that was then not taken. The interesting class. |
| **duplicate** | ~20 | A second copy of something the tree already had. §6. |

**The 45 dead-on-arrival accessors are a fact about how this development was
written, not a defect.** These files discharge goals by `show …; rfl` against
definitional unfolding rather than by rewriting with the accessor, so lemmas
like `htmulL_apply`, `htmulR_apply`, `adJre_apply`, `mem_powStrip`,
`Jequiv_apply`, `stdConj_apply`, `modularConj_apply`, `Phire_apply`,
`opRatio_domain` never fire. Written to the same template as the ones that do
fire, they are simply dead on arrival. Two consequences:

* Do not delete them on the strength of a usage scan. The scan cannot see them,
  and at least two (`extOut_apply`, `htKetR_apply`) are load-bearing through
  bare `simp`.
* The style has a real cost elsewhere: proofs that unfold with `show …; rfl`
  break the moment the definition becomes irreducible. §7 names the one place
  this matters.

---

## 5. The blocks

### 5a. `QuantumLambda.lean:4730–5542` — 813 lines, superseded

The atomic-type-I widening (commit `a992c23`). Verified to be a closed island:
*every* reference into the range from outside it is compiler-generated
(projections, `.eq_1`, `recOn`). The apparent exceptions, `EqL.vtmulR_*`, are a
separate later copy at `:6957`.

`atomicTypeI_tensor_preimage` and `atomicTypeI_tensorBsurjectivity` are
character-for-character the conclusions of `tensor_preimage` (`:7593`) and
`tensorBsurjectivity` (`:7652`) **with an extra hypothesis**. Both general
statements were later proved outright through 121II and go around the `atE`
device entirely. This is superseded, not orphaned: it was the right thing to
build when the commutation theorem was still open.

Of the 1,199-line commit, roughly 210 lines (`BKUnits`) and 147
(`uwTendsto_of_isLUB`, `uw_compress_tendsto`, since relocated to `Tensor.lean`)
were salvaged by later rounds and are load-bearing for `equaliser_lemma` and for
the reduction. The other 68% is unreachable. The pre-existing `haE` layer is
untouched and still live.

*Largest single item in this document.* Retiring it is a statement-level
decision for the author: the two theorems are true, proved, and are the only
record of the atomic-type-I case as a case.

### 5b. `ModularGroup.lean` — the `jConj` layer, ~300 lines, orphan

Twenty-six declarations: `jConjRe`, `jConj`, `jConj_{apply,one,mul,add,zero,
smul,star,R,two_sub_R,cfc_real,cpowOp,modPow}`, `jConjHom`,
`continuous_jConjHom`, `norm_jConj_le`, `J_apply_eq_jConj`, `J_opPow`,
`J_modPow`, `cpow_conj_ofReal`, `IsPowBase.cpowOp_eq_re_add_im`,
`inner_J_map_map`, `real_inner_J_map_map`. Verified to be a closed island: only
compiler-generated references enter it.

The module docstring advertises `jConj_cpowOp`, `J_modPow` and `jConj_modPow`
as **main results**. Nothing consumes them. `TomitaFourier` defines
`modFlow x' t := Δ^{it}(Jx'J)Δ^{-it}` directly and never performs the
rearrangement of RvD Lemma 4.8's `g(t)` that would have needed
`J Δ^{it} = Δ^{it} J`.

This block also duplicates `adJ` (§6).

### 5c. `TensorTransport.lean` — two clusters

`CT_top_right` / `CT_top_left` / `CT_top_top` / `mem_vnComm_top` /
`tensorGen_vnComm_top`, ~70 lines. `CT_top_right`'s only users are the other
two, which are themselves zero-use. When `COMMUTATION-THEOREM.md` §5a called
`CT_top_right` "the first instance of the theorem itself", that was a status
report on an open problem, not a dependency. `commutation_theorem` now subsumes
all three. **Superseded, and harmless to keep** — they are readable special
cases with short proofs.

`CT_of_CT_corner_any`, `CT_cornerAlg_congr`, `uconj_cornerAlg`,
`cext_cornerTransfer_cmpr`, `isUnitaryCLM_cornerTransfer`,
`adjoint_cornerTransfer`, `cornerTransfer` (`:790–922`), ~130 lines. **Orphan.**
The docstring says this is what `CT_of_CT_corner` was missing, but
`CT_of_CT_finCyclic` quantifies its hypothesis over *all* Hilbert spaces, so the
corner realisation is supplied by the caller and the choice never varies. The
transport was never needed.

### 5d. `QuantumLambda.lean` — the one-sided `tensorSub_inf` chain, ~106 lines

`:6468–6488`, `:6511–6579`, `:6588–6603`. Superseded not by unconditionality but
by the **two-sided** form: 125IV consumes
`tensorSub₂_inf_of_intersectionTensorStatement` (`:6678`), because its
intersection `(𝒜̃ ⊗ B(ℋ)) ∩ (𝒜 ⊗ 𝒞)` varies in both factors.
**`tensorSub_inf`'s own docstring is false** where it says "it is what 125IV
`equaliser_lemma` consumes". It was orphaned inside its own commit.

---

## 6. The `section Package` pattern — the structural finding

`Tomita.lean:645–716` bundles `modularSqrt`/`modularConj` with nine lemmas.
**The two definitions are used downstream; all nine lemmas are dead.**
`ModularTensor.lean`, the only consumer, reaches past them to the raw layer
(`mp`, `orbit_hasCore`, `J_D_orbit`, `orbit_mem_domain`, `Jli`, `J_inner_real`)
and then builds *its own* parallel package at `:1195–1240`. And
`CommutationTomita.lean:93` is literally `J_htmul`, "restated for the bare
conjugation `J`" — the only real consumer's first move is to unwrap.

This is the dominant failure mode of the development. It is not abandoned
mathematics: **a worker finishes a file, wraps a complete-looking API around it,
and the next worker downstream works at the raw layer instead.**

### The `ModularTensor` `Δ^{1/2}` package — six declarations, ~105 lines

`MT:1082–1151` and `MT:1206–1240`, entirely unreachable:

```
tensor_factorisation.2.1 / .2.2
  ├─ opTensor_mem_modularSqrt_domain (1082)   DEAD
  └─ modularSqrt_opTensor (1096)              DEAD
       └─ modularSqrt_htmul (1113)            DEAD
            ├─ modularSqrt_orbit (1130)       DEAD
            └─ modularSqrt_htmul_pkg (1220)   DEAD
  modularSqrt_hasCore_orbitSpan (1206)        DEAD
```

The file's docstring states two goals: `J_ξ = J_ω ⊗ J_{ω'}` **and**
`Δ_ξ^{1/2} = closure(Δ_ω^{1/2} ⊙ Δ_{ω'}^{1/2})`. `tensor_factorisation`
(`MT:921`) returns a triple; the `J`-half feeds the live `modularConj_htmul`,
which `CommutationTomita` uses. The `Δ^{1/2}` components `hfa`/`hfb` are
consumed only inside the dead block.

**Diagnosis — and it is sharper than "unused".** `Tomita.lean`'s package ships
its own domain-membership dischargers (`orbit_mem_modularSqrt_domain`,
`mem_modularSqrt_domain`). **`ModularTensor.lean`'s package ships none.**
`opTensor_mem_modularSqrt_domain` stayed behind in the `Full` section, phrased
over `mp … .D` with the six raw standardness hypotheses
`hsM hcM hsN hcN hsT hcT`. So a consumer of `modularSqrt_htmul_pkg` must drop
out of the package vocabulary and re-derive `isStandard` / `isStandard_vnTensor`
by hand to produce its hypothesis `h`. **Had the package been used even once,
that gap would have closed.** The `J`-half of the same section has no such gap —
because it was used.

Commit order agrees. `ModularTensor.lean` is one commit, `5d816fc`; its consumer
`CommutationTomita.lean` is the later `d179cda`, and took only
`modularConj_htmul`, `isCyclicVector_vnTensor`, `isSeparatingVector_vnTensor`,
`isStandard_vnTensor`.

*Mitigating.* The expensive part is not dead: `orbitSpan_hasCore_tensor`
(`MT:748`, ~150 lines) is consumed inside `tensor_factorisation`'s own proof at
`MT:943`. And `hfa`/`hfb` fall out of the same `IsModularPair.eq_one_of_comp`
application as the `J`-half, so almost nothing was built *for* the dead
statements. **Cost of this block: low. Keep it, or delete it, freely.**

### The same shape, smaller

* **Speculative direction-guessing at class boundaries.**
  `HasCyclicSeparating.hasCyclic`, `hasCyclicSeparating_of_dense_orbit`,
  `hasFinCyclic_of_cyclic`, `mem_vnComm_of_forall`, `CommCmpr.{one,mul,smul}` —
  each the mirror of the one the next round actually needed.
* **Mirror-pair over-generation.** `b_real_symm`/`b_b_apply`,
  `unitary_add_I_smul`/`unitary_sub_I_smul`, `normFst_mul`/`normSnd_mul`.
* **Two `StandardSubspace` upstreaming wrappers, both 100% dead**:
  `StandardSubspace.lean`'s `section Std` (`stdConj` + 3 lemmas, `:654–682`) and
  `Tomita.lean`'s `standardSubspace` + `standardSubspace_toClosedSubmodule`
  (`:503–512`). Same idea, two rounds, ~40 lines. Defensible as the natural
  Mathlib-upstreaming interface; as they stand, decoration.

---

## 7. Individually diagnosed items

### `tomita_JM'J_unconditional` — terminal, but was redundant. **Fixed.**

`TomitaAnalytic:1165`. Terminal by intent: `COMMUTATION-THEOREM.md` §4 scopes
the project to "only the *conjugation* half `JMJ = M'`", and this is the dual,
exposed for the record.

It is *not* an overlooked-lemma case. `CommutationTomita.lean` needed
`J S□ J = (J S J)□` for an **arbitrary set** `S` (`adJ_image_commutant`),
applied to a bicommutant in the generators `elemOps M N` — a shape a statement
about `M` itself cannot serve, so the general algebraic fact was proved locally
and subsumes this one.

But it was **a three-line corollary of its own sibling that was not proved as
one**: `adJ` is an involution (`adJ_adJ`), so applying `adJ ''` to
`J M J = M'` gives `J M' J = M`. Instead it re-derived from `tomita_JM'J` +
`adJ_commutant_subset`, a parallel path whose only purpose was this theorem.

**Applied 2026-08-26** (§12): reproved as

```lean
  rw [← tomita_JMJ_unconditional M ω hsep hcyc hMdense hM'dense hM,
    Set.image_image]
  simp only [vnAdJ_vnAdJ, Set.image_id']
```

Statement byte-identical, axiom-clean. **Consequence: `tomita_JM'J`
(`TomitaTakesaki:534`, ~12 lines) is now zero-use.** Deleting it retires a
public name in another file and is left for the author. `adJ_commutant_subset`
remains live via `TomitaFourier:680`.

### `vnAdJ_one` — strictly redundant. **Deleted.**

`vnAdJ` is a `noncomputable abbrev`, hence reducible, so the already-`@[simp]`
`adJ_one` applies verbatim. Verified by probe: both `simp [-vnAdJ_one]` and
`simp only [adJ_one]` close `vnAdJ M ω hsep hcyc 1 = 1`. It was the one member
of the eight-lemma `vnAdJ_*` wrapper block that nobody needed. See §12.

### `sepSet_subset_Ksub` — orphan

`TomitaTakesaki:669`. `sepSet ⊆ 𝒦`, three lines. Orphan of a "run the
nearest-point projection inside the real Hilbert space `𝒦`" framing. The proof
that shipped (`exists_separating_of_notMem`, `:785`) separates in `ℋ` and
projects only at the very end via `P_apply_mem` at `:835`, and never needs the
containment. The module docstring already records the departure as deliberate.

### `CT_iff_vnComm` — orphan, and the docs oversold it

`Commutation:270`, with its only feeder `CT_vnComm` (`:257`), dead as a block,
and advertised in the module docstring as a main result.
`COMMUTATION-THEOREM.md`'s "dualising via `CT_iff_vnComm` swaps the two
examples" describes a **prose** argument that was never formalized. What the
proof needed were `CT_comm` and `CT_iff_bicommutant`, both live. And now that
`commutation_theorem` is unconditional, both sides of the iff are theorems.

### `cyclic_and_separating_of_separating` — the sharpest retraction casualty

`Commutation:468`, ~28 lines, and it drags `reducedSet` (`:373`) with it. It
produces a cut `f ∈ vnComm M` — in the **commutant** — whereas the transport
that closed the reduction (`CT_of_CT_compression_of_dense`) needs a cut
`e ∈ SA`, **inside the algebra**. `CommutationAmplify.lean:54` names it in the
retraction by name.

### `Modular.lean`'s advertised "Lemma A" is transitively dead

`IsModularPair.injective_apply` and `dense_range` are zero-use;
`inner_nonneg`'s only consumer is the dead `modularSqrt_inner_nonneg`. Only
`isSelfAdjoint` is load-bearing, via `isClosed`. **Positivity, injectivity and
dense range of `Δ^{1/2}` are used nowhere in the commutation theorem** —
precisely the machinery the bounded resolvent argument (Lemmas C/D) replaced.

### `IsCommutingPair.symm` cannot be used as written

`Modular:570`. Built to derive ~8 mirrored `_snd` lemmas from their `_fst`
twins, and it cannot: `sqrtSumSq c d` and `sqrtSumSq d c` are not syntactically
equal. Either add `sqrtSumSq_comm` and route through it, or delete.

### `concreteTensor_inf_le_inf`, `tensorSub₂_mono` — superseded

`Tensor:11479`, `QL:6206`. Built for "easy half by monotonicity, hard half by
the real theorem". `intersection_tensor'` proves the equality outright by a
rewrite chain; `le_antisymm` never appears.

### Defeq fragility — the one place a reroute is advisable

`ModularTensor.modularConj_htmul` and `CommutationTomita.J_htmul` close
`modularConj`-shaped goals with bare `J`-shaped terms. Those proofs break the
moment `modularConj`/`Jequiv` become irreducible. They should go through the
(currently unused, §4) `modularConj_apply` / `Jequiv_apply`. **This is the item
where the `show …; rfl` style has a real cost.**

---

## 8. Duplication, with a verdict on each

| duplicate | which copy survives, and why |
|---|---|
| `jConjRe`/`jConj`/`jConjHom` (`ModularGroup:597–737`) vs `adJre`/`adJ` (`TomitaTakesaki:154–223`) | **Identical definitions.** `adJ` survives — it is live, consumed by `CommutationTomita`; `jConj*` is entirely dead (§5b). Both need only `StandardSubspace.lean`'s `J`, `J_norm`, `J_J`, `J_smul_I`, `smul_complex_of_smul_I`; **that is where the single copy belongs.** If `J X^w J = (J X J)^{w̄}` is wanted on the record, restate it on `adJ` and keep `jConjHom` as `adJHom`. **`ModularGroup:560–562`'s claim that `TomitaTakesaki` is "downstream of this file" is false** — `TomitaTakesaki` imports only `Tomita`; the two meet at `TomitaFourier`, where both are in scope and only one is used. |
| `Jli`+`J_inner_real` (`Tomita:131,135`) vs `Jisometry`+`real_inner_J_map_map` (`ModularGroup:571,574`) | Same definition, and **both are live** — `Jli` → `ModularTensor`, `TomitaTakesaki`; `Jisometry` → `TomitaFourier`, `TomitaAnalytic`. One copy, in `StandardSubspace.lean`. Of the two lemmas keep `J_inner_real` (used); `real_inner_J_map_map` is dead. |
| `J_inner_map_map` (`TomitaTakesaki:148`) vs `inner_J_map_map` (`ModularGroup:578`) | Exact type match. Keep `J_inner_map_map`: five lines via `J_inner_swap`, versus twenty, and the twenty-line one is dead. |
| `real_inner_le_of_le` (`TomitaTakesaki:949`) vs `real_inner_le_of_le'` (`ModularGroup:210`) | **Character-for-character identical proofs.** The *primed* one is live (`IsPowBase.norm_cpowOp_apply_le`); the unprimed one is dead. Keep the live one, drop the prime, move to a common ancestor. Mathlib-level; check `ContinuousLinearMap.reApplyInnerSelf` first. |
| `opTensor_comp` / `opTensor_adjoint'` (`CornerTensor:572,582`) vs `opTensor_mul` / `opTensor_adjoint` (`Tensor:1012,1067`) | The primed forms are the general (different Hilbert spaces) versions, and `opTensor_adjoint'`'s proof is character-identical to `opTensor_adjoint`. **`Tensor.lean` already states `opTensor_add_left` across different spaces**, so the general forms belong there under the unprimed names, with the endomorphism cases as one-line corollaries (`opTensor_mul` has 4 external users, `opTensor_adjoint` 1). |
| **The ket operator — four copies** | `htKet e : x ↦ x ⊗ e` (`Tensor:1117`) is canonical, 4 external users. `htmulL y` (`ModularTensor:212`) is the *same map* under another name. And `y ↦ x ⊗ y` exists three times: `htmulR` (`ModularTensor:220`), `htKetL` (`TensorTransport:77`), `htKetR` (`Compression:753`) — `Compression` and `TensorTransport` are siblings, hence the third copy, **and they pick opposite names for the same map** ("left ket" vs "ket in the second variable"). One copy, in `Tensor.lean`, and settle the name. (`B/Dils`'s `hilbTensorKet*` is a different tensor product; leave it.) |
| `htmul_add_right` (`ModularTensor:397` and `TensorTransport:65`) | Character-identical, two namespaces. Belongs in `Tensor.lean` beside `htmul_add_left`. Likewise `htmul_zero_left` (`TensorTransport:71`, dead) beside `htmul_zero_right`. |
| `vnTensor` (`ModularTensor:540`) vs `concreteTensor` (`Tensor:11394`); `commutantSA` (`Tomita:290`) vs `vnComm` (`Commutation:59`) | **The same objects under two names each**, bridged at `CommutationTomita:247,253`. This is the `A/VN`↔`A/Proc` seam; it is documented, but it means new code in `A/VN` uses names nothing else in the tree uses. Retire `vnTensor`/`commutantSA` in favour of the `A/Proc` names, or at least stop growing the `A/VN` copies. |
| `isClosed_image_of_uwCompact` (`TomitaTakesaki:588`) vs `..._real` (`:614`) | Same 25-line filter/cluster-point proof twice, `inner ℂ` versus `inner ℝ`. Only the real one is used — its own docstring says so, because `P` is only ℝ-linear. The ℂ version was written first and never adapted. **The one place a deletion would also remove genuinely duplicated proof text.** |
| `bicommutant_eq_of_uwClosed` (`Tomita:482`) vs `isClosed_uw_of_bicommutant` (`TomitaTakesaki:640`) | Two directions of one iff, same one-line proof from `(double_commutant M).2.1`, written by two rounds. Collapse; the `Tomita` direction is dead. |
| `isVNSubalgebra_top` (`TensorTransport:710`) vs `isVNSubalgebra_top'` (`QuantumLambda:7075`) | Identical proofs; the `QuantumLambda` one is more general (arbitrary C\*-algebra) and should absorb the special case. |
| `opRatio_domain` (`Modular:136`) vs `IsModularPair.D_domain` (`:178`); `modularPair_data` (`StandardSubspace:640`) vs `isModularPair_a_b` (`:650`); `isCyclicVector_htmul` vs `isCyclicVector_vnTensor` (`ModularTensor:599,1169`) | Same statement twice, tens of lines apart; in each case one is dead. **`modularPair_data`'s stated justification — "no dependency on `Modular.lean`" — is contradicted by the file's own `import Theses.A.VN.Modular` on line 53.** |

Deliberate and documented, leave alone: `intersection_tensor'` vs
`intersection_tensor` (import-graph driven), `tomita_JMJ` vs
`tomita_JMJ_unconditional`, `Jequiv`/`modularConj`/`stdConj`.

---

## 9. Headline theorems: all reachable, all clean

Axiom-checked, all `[propext, Classical.choice, Quot.sound]`:
`commutation_theorem`, `intersection_tensor`, `equaliser_lemma`,
`tensor_equalisers`, `tensor_preimage`, `tensor_closed`,
`tensor_map_factorisation`, `tensorBsurjectivity`, `tomita_JMJ_unconditional`,
`tomita_JM'J_unconditional`, `CT_of_cyclicSeparating`,
`CT_of_CT_cyclicSeparating`. The only `sorry` in any of these files is the
deliberate `tensor_simple_facts_4` (`Tensor.lean:6833`), documented false in
`ERRATA.md`.

The chain, verified transitively:

```
lemma_4_7 (TomitaAnalytic:1074)
  → tomita_JMJ_unconditional (TomitaAnalytic:1155)
      ├→ adJ_image_elemOps (CommutationTomita:175)            [M, and N]
      └→ commutant_vnTensor_eq_vnTensor_commutant (:210)      [M ⊗̄ N]
  → CT_of_cyclicSeparating_bicommutant (CommutationTomita:267)
  → CT_of_cyclicSeparating (:284)
  → cyclicSeparatingCTStatement (Proc/CommutationTheorem:102)
  → CT_of_isVNSubalgebra (:135)     [via CT_of_CT_cyclicSeparating, the reduction]
  → commutation_theorem (:143)
  → intersection_tensor' (:244)
  → Proc.intersection_tensor (QuantumLambda:309, 121II)
```

`modularConj_htmul`, `lemma_4_6`, `modPow`, `adJ`, `CT_of_CT_corner`,
`CT_of_CT_compression_of_dense` are all inside the cone of
`commutation_theorem`. `intersection_tensor` is inside the cone of
`tensor_preimage`, `tensor_closed` and `tensor_map_factorisation`. Nothing is
stranded. The five Kornell statements and `commutation_theorem` are themselves
consumer-free, which is correct: they are the thesis statements.

---

## 10. Stale documentation found in passing — **all six fixed 2026-08-26** (§12)

* `Commutation.lean:12–16` advertises `CT_iff_vnComm` as a main result; dead and
  now vacuous. ✔ removed from the header; the declaration now carries an "on
  the record only" note.
* `ModularGroup.lean`'s "Main results" advertises `jConj_cpowOp`, `J_modPow`,
  `jConj_modPow`; all dead. ✔ moved into a new "On the record only — nothing
  consumes these" section of the module docstring.
* `ModularGroup.lean:560–562` says `TomitaTakesaki` is "downstream of this
  file"; it is not. ✔ replaced by the true import-graph statement: siblings,
  meeting at `TomitaFourier`.
* `tensorSub_inf`'s docstring claims 125IV consumes it; 125IV consumes the
  two-sided form. ✔ corrected — on `tensorSub_inf` **and** on
  `tensorSub_inf_of_intersectionTensorStatement`, which carried the same claim
  and which this list had missed.
* `StandardSubspace.lean:637` says `modularPair_data` has "no dependency on
  `Modular.lean`"; the file imports it. ✔ corrected.
* `EqL.rSlice_mem` (`QuantumLambda:6801`) cross-references "the argument of
  `atE_mem`" — inside the 813-line dead block, i.e. the later round reproved the
  argument rather than reusing it. ✔ the cross-reference is gone; the docstring
  now says the argument is self-contained.

---

## 11. If given a fixing round, in this order

1. **Move the J-conjugation layer into `StandardSubspace.lean` and keep one
   copy.** This is the only item that removes real duplicated *proof text*
   (~300 lines in `ModularGroup`, plus `real_inner_le_of_le`,
   `inner_J_map_map`, `Jisometry`, and the 25-line `isClosed_image_of_uwCompact`
   twin in `TomitaTakesaki`). Everything needed lives in `StandardSubspace.lean`
   already; the duplication exists purely because `ModularGroup` and
   `Tomita`/`TomitaTakesaki` are siblings in the import graph. **Highest value,
   lowest risk, and it prevents recurrence.**
2. **Settle the ket operator and the `htmul_*` lemmas in `Tensor.lean`**, and
   move `opTensor_comp`/`opTensor_adjoint'` there under the unprimed names.
   Four copies of one operator, with two files calling the same map "left" and
   "right", is a live naming hazard, not just clutter.
3. ~~**Fix the six stale docstrings in §10.** Ten minutes, and they are actively
   misleading — two of them assert dependency facts that are false.~~
   **Done 2026-08-26** — seven of them in the end; see §10 and §12.
4. ~~**Route `modularConj_htmul` and `J_htmul` through `modularConj_apply` /
   `Jequiv_apply`** (§7). The only place the `show …; rfl` style is load-bearing
   in a way that will break.~~ **Done 2026-08-26.** Both now go through
   `modularConj_apply`; `Jequiv_apply` turned out not to be needed, because
   `modularConj_apply` unfolds all the way to the bare `J` in one step and
   `Jequiv` never appears in either goal.
5. **Decide on the atomic-type-I block (§5a).** 813 lines, superseded, and a
   statement-level call the author should make — not a cleanup.
6. **Leave the packages and the accessors alone**, or delete them wholesale;
   either is fine. They cost nothing and re-deriving them is cheap. Do not spend
   a round on them.

Items 1–4 are mechanical and total maybe a day; **3 and 4 are done** (§12).
Items 1 and 2 are not, deliberately: both move declarations between files and
retire public names, which is the author's call. Item 5 needs the author.
Item 6 is the 45 accessors plus the `section Package` blocks — the bulk of the
raw count and none of the cost.

---

## 12. Changes applied

Four now: two by the audit itself (1 and 2 below), and two by the bookkeeping
round of 2026-08-26 that applied §11 items 3 and 4 (3 and 4 below). All
statement-preserving. Everything else in this document is left for a
later round with the author's eye on it — anything that moves a declaration
between files, retires a public name, or changes a proof route stays here as
text.

**1. `TomitaAnalytic.lean` — `tomita_JM'J_unconditional` reproved from its
sibling** (§7). Was:

```lean
  tomita_JM'J M ω hsep hcyc hMdense hM'dense
    (adJ_commutant_subset M ω hsep hcyc hM
      (fun _ hx' _ hφ => lemma_4_7 M ω hsep hcyc hM hM'dense hx' hφ))
```

now:

```lean
  rw [← tomita_JMJ_unconditional M ω hsep hcyc hMdense hM'dense hM,
    Set.image_image]
  simp only [vnAdJ_vnAdJ, Set.image_id']
```

Statement byte-identical; docstring extended to name the route.
**`tomita_JM'J` (`TomitaTakesaki:534`, ~12 lines) is now zero-use** — deleting
it retires a public name in another file and was not done.
`adJ_commutant_subset` remains live via `TomitaFourier:680`.

**2. `TomitaTakesaki.lean` — `vnAdJ_one` deleted** (§7). Two lines. Zero-use in
the constant closure, and `adJ_one` covers the same goals through the reducible
`abbrev`, verified by probe before deleting.

**Verification.** Both edits were checked by rebuilding the whole downstream
chain against a shadow olean tree, so that the `@[simp]` removal was tested
against *recompiled* consumers rather than stale oleans:

| file | result |
|---|---|
| `A/VN/TomitaTakesaki.lean` | exit 0, no output |
| `A/VN/TomitaStrip.lean` | exit 0, no output |
| `A/VN/TomitaFourier.lean` | exit 0, no output |
| `A/VN/TomitaAnalytic.lean` | exit 0, no output |
| `A/VN/CommutationTomita.lean` | exit 0, no output |
| `A/Proc/CommutationTheorem.lean` | exit 0, no output |
| `A/Proc/QuantumLambda.lean` | exit 0, **0 errors, 0 `sorry` warnings**, only its own pre-existing linter noise |

Identical to the pre-edit baseline in every case.
`tomita_JM'J_unconditional` and `tomita_JMJ_unconditional` axiom-checked in situ:
`[propext, Classical.choice, Quot.sound]`.

*Not rebuilt:* `.lake/build` still holds the pre-edit oleans for the two touched
files. A `lake build` will recompile them and their dependents; nothing else is
needed.

**3. The seven stale docstrings of §10 — corrected 2026-08-26.** Comment-only;
no statement, proof term or `import` changed.

| file | what was false | now |
|---|---|---|
| `A/VN/StandardSubspace.lean` | `modularPair_data`'s "no dependency on `Theses/A/VN/Modular.lean`" | says the *statement* names nothing from `Modular.lean` but the file imports it on line 53; also records that it is the unbundled twin of `isModularPair_a_b` and has no consumer |
| `A/VN/ModularGroup.lean` | "`TomitaTakesaki` … downstream of this file; the two are deliberately independent" | siblings — `TomitaTakesaki` ← `Tomita` ← `StandardSubspace`, this file ← `StandardSubspace` — meeting at `TomitaFourier`, where only `adJ` is used |
| `A/VN/ModularGroup.lean` | "Main results" listing `jConj_cpowOp`, `J_modPow`, `jConj_modPow` | those three moved to a new "On the record only — nothing consumes these" section naming the whole `jConj` layer |
| `A/Proc/Commutation.lean` | header advertising `CT_iff_vnComm` as a main result | header clause deleted; the declaration carries an "on the record only" note pointing at §7 |
| `A/Proc/QuantumLambda.lean` | `tensorSub_inf`: "it is what 125IV `equaliser_lemma` consumes" | says nothing consumes it, and names the two-sided form 125IV does consume |
| `A/Proc/QuantumLambda.lean` | `tensorSub_inf_of_intersectionTensorStatement`: "i.e. what 125IV `equaliser_lemma` actually needs" — **the same false claim, one declaration earlier, which §10 had missed** | corrected the same way |
| `A/Proc/QuantumLambda.lean` | `EqL.rSlice_mem` citing "the argument of `atE_mem`", inside the dead `:4730–5542` block | cross-reference removed; the argument is stated as self-contained |

**4. `modularConj_htmul` and `J_htmul` rerouted 2026-08-26** (§11 item 4).
`ModularTensor.lean:1192` and `CommutationTomita.lean:93` were term-mode proofs
that typechecked a `J`-shaped term against a `modularConj`-shaped goal (and the
reverse) purely by definitional unfolding. Both now go through the `@[simp]`
unfolder `modularConj_apply`:

```lean
  -- modularConj_htmul
  simp only [modularConj_apply]
  exact (tensor_factorisation …).1 ζ ζ'

  -- J_htmul
  simpa only [modularConj_apply] using modularConj_htmul …
```

`Jequiv_apply` was not needed after all: `modularConj_apply` rewrites straight
to the bare `J`, so `Jequiv` never appears in either goal. Statements
byte-identical.

**Verification of 3 and 4.** Every touched file recompiled with
`lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3` against the same
`LEAN_PATH`, and its output diffed against a pre-edit baseline taken the same
session:

| file | result |
|---|---|
| `A/VN/StandardSubspace.lean` | exit 0, no output — byte-identical to baseline |
| `A/VN/ModularGroup.lean` | exit 0, no output — byte-identical |
| `A/VN/ModularTensor.lean` | exit 0, no output — byte-identical |
| `A/VN/CommutationTomita.lean` | exit 0, no output — byte-identical |
| `A/Proc/Commutation.lean` | exit 0, no output — byte-identical |
| `A/Proc/QuantumLambda.lean` | exit 0, 0 errors, 0 `sorry` warnings — its own pre-existing linter noise only, identical to baseline modulo shifted line numbers |

**Considered and not applied.** Deleting `tomita_JM'J`, §11 items 1 and 2, and
every item in §8 — all of them either retire a public name, move a declaration
between files, or change a route, which is exactly the class this audit was
told to describe rather than perform.
