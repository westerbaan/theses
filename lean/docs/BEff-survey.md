# `Theses/B/Eff/` — full survey of the remaining `sorry`s (worker, session 82, 2026-08-17; **updated session 83, 2026-08-18**)

> **Session 83 update.**  The root, **180V**, is CLOSED — *both*
> `effectus_vn` and `effectus_vn_partial` are proved in `VNExamples.lean` and
> are `#print axioms`-clean.  B/Eff is now at **13** `sorry`s (`VNExamples`
> **9**, `StatesPredicates` 2, `EffectAlgebras` 2), 0 errors.  Three further
> corrections to what is below: `WStar.trivial` was stated one universe too
> high (`WStar.{u+1}`) and so could never be an object of `WStarNCPU.{u}` —
> fixed; the costing overlooked that **`ℂ` also has to be lifted** to
> `ULift.{u} ℂ` and given a `Theses.VonNeumannAlgebra` instance; and the real
> cost of the file is not the mathematics but that `WStarCat.lean`'s `id` and
> `comp` come from `Classical.choice`, so every categorical step needs a
> propositional apply-lemma where `emod_effectus` uses `rfl`.  The eight
> hypothetical examples are *still* gated on a transport of the new concrete
> structure to the arbitrary `s` of their statements.  See PROVING-LOG,
> session 83.
>
> **Session 83, second worker.**  `exc_dm_effectus_kleisli` (192III.3) is also
> CLOSED, from the author's solution at `bsols.tex:1991–2170`, which is
> complete and usable as written.  With both closures B/Eff is at **12**
> `sorry`s (`VNExamples` 9, `StatesPredicates` **1**, `EffectAlgebras` 2), 0
> errors.  See the `StatesPredicates.lean` section below.

**Headline count (session 82): B/Eff had 15 code `sorry`s.**  Per file, each source run
through `lean` individually with `LEAN_PATH` set (never `lake env lean`), and
each checked for **errors** as well as `sorry`s.  (`VNExamples.lean` was
re-verified against freshly built `B/Dils` oleans; while the `B/Dils` worker
is mid-rebuild it reports a transient `object file … does not exist` at its
import line, which is not a defect in this directory — retry, do not debug.)

| file | lines | `sorry` | errors |
|---|---|---|---|
| `VNExamples.lean` | 408 (now 2167) | **11** (now **9**) | 0 |
| `StatesPredicates.lean` | 7216 (now 7723) | **2** (now **1**) | 0 |
| `EffectAlgebras.lean` | 3088 | **2** | 0 |
| `Comparisons.lean` | 1903 | 0 | 0 |
| `Dagger.lean` | 2572 | 0 | 0 |
| `DiamondAmp.lean` | 1855 | 0 | 0 |
| `Quotients.lean` | 1427 | 0 | 0 |
| `Effectus.lean` | 2783 | 0 | 0 |
| `WStarCat.lean` | 292 | 0 | 0 |
| **total** | | **12** | **0** |

The import chain is linear:
`EffectAlgebras + WStarCat → Effectus → StatesPredicates → Quotients →
DiamondAmp → Dagger → Comparisons → VNExamples`.  Only `VNExamples.lean`
imports thesis A (via `Theses.B.Dils.Pure`); the other eight import
`Theses.Common` alone.  **Preserve that**: it is an author ruling of
2026-08-17, and it is why `B/Eff` builds in seconds and cannot be broken by
work upstream.

---

## Headline findings of this session

1. **Neither recorded blocker is real.**
   * *"Mathlib lacks a `CStarAlgebra` instance for the trivial algebra."*
     **Refuted, and fixed.**  Mathlib's `CStarAlgebra` extends `NormedRing`,
     **not** `NormOneClass`, so `‖1‖ = 0` is no obstacle; only four instances
     (`StarRing`, `CStarRing`, `StarModule ℂ`, and then `CStarAlgebra` itself
     as `{}`) were missing for `PUnit`, plus `StarOrderedRing` and
     `Theses.VonNeumannAlgebra`.  All six are now in `VNExamples.lean`, with
     `WStar.trivial` as the object.  ~25 lines.  (Mathlib in fact *already*
     has a trivial C\*-algebra by accident: `CStarAlgebra (Π _ : Empty, ℂ)`
     synthesises from the finite-`Pi` instance.)
   * *"An `EffectusPartialStructure` uniqueness lemma is missing."*  **Half
     real, and the hard half is now proved.**  The PCM-enrichment of a finPAC
     is **not extra data**: it is uniquely determined by the category and its
     finite coproducts (`finPAC_pcm_unique`, `Comparisons.lean`, axiom-clean),
     hence so is the enrichment carried by any `EffectusPartialStructure`
     (`effectusPartialStructure_homPCM_unique`).  What is *not* determined is
     the effect object `I` of `EffectusPartialForm` together with its truth
     map: those are unique only up to isomorphism, and the nine hypothetical
     statements will additionally need an invariance-under-`I`-iso lemma
     (small, but not written).

   The argument, for the record, uses only the finPAC axioms:
   `𝟙` on the initial object is `0` (both are maps `0 ⟶ 0`), so `f = f ≫ 𝟙 =
   f ≫ 0 = 0` for every `f : X ⟶ 0` and `C(X, 0)` is a **singleton**; hence
   `0 = 0_{X,0} ≫ !` is the same morphism for any two enrichments.  With `0`
   fixed the partial projections `▷₁, ▷₂` are fixed, and `f ⊥ g` iff `f, g`
   are the two components of one `b : X ⟶ Y + Y` (`⇐` is *compatible sum*,
   `⇒` takes `b = κ₁f ⋁ κ₂g`, which exists by *untying*).  Finally
   `f ⋁ g = ∇ ∘ b` for any such `b`, because `▷₁ ⋁ ▷₂ = ∇` and `⋁` commutes
   with precomposition.

2. **`effectus_vn` / `effectus_vn_partial` (180V) is the root**, as previously
   recorded, and it is now genuinely open work rather than gated: the trivial
   algebra exists, and the uniqueness lemma removes the second gate for its
   eight dependants.  See the entry below for what remains.

3. **`vn_is_andthen_eff` (211IV) needs `A/Proc`, which is not on the import
   path** — a correction to `VNExamples.lean`'s own header, which says "`A/Proc`
   … nothing here has been shown to need it".  eff.tex:4859 proves the two
   &-effectus axioms by citing **105V** `positive-map-uniqueness` and **100III**
   `pure-fundamental`, and both live in `Theses/A/Proc/Measurement.lean`.
   Worse: **105V is itself `sorry` there** (`Measurement.lean:6610`).  So 211IV
   is blocked on an A/Proc item *and* on an import that must first be added.

4. **Three of the four non-`VNExamples` items are literature parks, not
   targets** (QUESTIONS **A3**); only `exc_dm_effectus_kleisli` is a live
   target, and it has a complete author solution.

5. **QUESTIONS A3 is stale in two places**: it lists
   `finite_effectMonoid_commutative` and `exists_noncommutative_effectMonoid`
   as parked, but both are **proved** (`EffectAlgebras.lean:2763`, `:2299`).
   Only `finite_effectMonoid_boolean` of that trio is still open.

---

## Classification at a glance

| classification | statements |
|---|---|
| **proved (session 83)** | `exc_dm_effectus_kleisli`; `effectus_vn` + `effectus_vn_partial` |
| **reachable, live target** | `finite_effectMonoid_boolean`; `effects_sea` (225V) |
| **blocked on the root 180V** | the eight hypothetical vN examples below |
| **blocked outside B/Eff** | `vn_is_andthen_eff` (A/Proc 105V + missing import); `vn_is_dagger_category` (via 211IV) |
| **awaiting a ruling / literature park** | `effectModule_unitInterval_representation`, `cancellative_iso_convex` (both QUESTIONS **A3**) |
| **known false** | none in this directory |

Nothing in `B/Eff` is known false, and nothing is waiting on a thesis-B
ruling: the open thesis-B rulings (B10, B12, D6, D7) all bite in `B/Dils`.

---

## `VNExamples.lean` — the eleven von Neumann examples

All eleven are **Examples/Corollaries** of eff.tex, and this matters for
costing: nine of them are asserted with **no proof in the text**, or with a
one-line pointer.  There is very little to transcribe here; almost all of the
mathematics has to be supplied.

### The root: `effectus_vn` (180V) and `effectus_vn_partial` (180V)

*Route.* eff.tex:832 says only "**To see `vNᵒᵖ` is an effectus in total form,
adapt the proof of `emod-effectus`**" — QUESTIONS **A3** already records that
there is no proof to transcribe.  `emod_effectus` (191II) *is* proved, in
`StatesPredicates.lean:1480`, and the bridge it goes through,
**`effectusTotalForm_of_pres`** (`StatesPredicates.lean:819`), is exactly what
`effectus_vn` should use: it reduces `EffectusTotalForm D` to the three axioms
of 180I verified against *any* concrete presentation of the final object and
the binary coproducts.  Two further worked instances of that bridge are in the
same file (`emod_effectus_aux:1492`, `exc_rng_eff:1881`).

*What has to be built.*

1. `HasTerminal (WStarNCPU.{u}ᵒᵖ)`, i.e. `ℂ` is **initial** in `vN`: existence
   is `algebraMap`, uniqueness is unitality + `ℂ`-linearity.  Normality of
   `z ↦ z • 1` needs closedness of the positive cone (Mathlib
   `isClosed_nonneg`).  ~60 lines.
2. `HasFiniteCoproducts (WStarNCPU.{u}ᵒᵖ)`, i.e. finite **products** in `vN`.
   Terminal object: **`WStar.trivial`** — now available; what is left is
   `IsTerminal (WStarNCPU.of WStar.trivial)`, whose every obligation is a
   `Subsingleton.elim`, ~30 lines.  Binary products: `A × B`, and Mathlib
   already has `CStarAlgebra (A × B)`; `PartialOrder`, `StarOrderedRing` and
   `Theses.VonNeumannAlgebra` on the product are componentwise.  ~120 lines.
   **Do not route this through thesis A's `⊕ᵢ𝒜ᵢ = lp 𝒜 ∞`** — that carries
   `[∀ i, Nontrivial (𝒜 i)]`, which is precisely what the coproduct with the
   initial object violates.  Mathlib's `Prod`/finite-`Pi` C\*-instances have no
   such hypothesis, and that is the fix for the second half of the recorded
   blocker.
3. The three axioms of 180I at that presentation.  In `vN` they are statements
   about `A × ℂ`, `A × B` and `ℂ × ℂ × ℂ`; the *proofs* are the ones
   `emod_effectus` gives for effect modules, run in a different concrete
   category.

*Costing.* **~500–800 lines, one to two sessions**, with step 3 the bulk.
`effectus_vn_partial` is then the partial-form counterpart; the thesis notes
(eff.tex:835) that the partial maps are the ncpsu-maps, i.e. exactly
`WStarCPSU`, so most of the work is shared, but the PCM structure
(`f ⊥ g` iff `f + g` is again subunital, `f ⋁ g = f + g`) and the effects data
(`I = ℂ`, `truth = ` the unit map) have to be built explicitly.  Add ~300
lines.  **This is the highest-value target in the directory**: eight of the
remaining ten sit behind it.

*Classification:* **reachable, long.**

### The eight hypothetical examples

`effectus_vn_real_separating` (190III), `diamond_effectus_vn` (206III),
`vn_is_andthen_eff` (211IV), `vn_is_dagger_category` (215VI),
`vn_has_dilations` (221III), `vn_dilation_order_correspondence` (223VI),
`exc_purec_no_biproduct` (224VI), `exc_purec_equal` (224VII).

Each takes an **arbitrary** `s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ` and
must produce its conclusion for *that* `s`.  Since this session, the
enrichment part of `s` is known to be canonical
(`effectusPartialStructure_homPCM_unique`), so a proof may compute with the
concrete `⋁`; what still has to be supplied is the transport along
`s.effectus.I ≅ ℂ`.  Nobody should attack any of these before 180V exists —
without a concrete `s` in hand there is nothing to compute with.

Individually:

* **`effectus_vn_real_separating` (190III)** — eff.tex:2136 asserts it and
  cites `[effintro]`; no proof.  The content is concrete and elementary once
  the effectus exists: predicates on `𝒜` are `[0,1]_𝒜`, states are the normal
  states, `M ≅ [0,1]`, separation of states is `np_faithful` (the second axiom
  of `Theses.VonNeumannAlgebra`), separation of predicates is order separation.
  **~250 lines after 180V.**  *Reachable, blocked on the root.*
* **`diamond_effectus_vn` (206III)** — eff.tex:4460 is a bare Examples list
  ("`vNᵒᵖ`, `CvNᵒᵖ`, `EJAᵒᵖ` and `Set` are all ⋄-effectuses"), no proof.
  `f_⋄` is `p ↦ ⌈f(p)⌉`; the ceiling calculus is fully developed in
  `A/VN/Projections.lean` and on the import path.  **~250 lines after 180V.**
  *Reachable, blocked on the root.*
* **`vn_is_andthen_eff` (211IV)** — the one example whose text gives a real
  route, and the only one **blocked outside `B/Eff`**: eff.tex:4861 proves
  axiom 1 by **105V** `positive-map-uniqueness` and axiom 2 by **100III**
  `pure-fundamental`, both in `Theses/A/Proc/Measurement.lean`.  100III is
  proved; **105V is `sorry`** (`Measurement.lean:6610`).  And `A/Proc` is not
  imported by `VNExamples.lean` — adding `import Theses.A.Proc.Measurement`
  is a small change but a real one, and the file header's claim that nothing
  here needs `A/Proc` is wrong.  *Blocked: A/Proc 105V, plus the root.*
* **`vn_is_dagger_category` (215VI)** — eff.tex:5338 is a **Corollary** of
  211IV together with the †'-effectus theorem of 215V, so it inherits 211IV's
  blocker.  Whether 215V's sufficiency direction is available in the tree
  should be checked before costing.  *Blocked, via 211IV.*
* **`vn_has_dilations` (221III)** — eff.tex:6806 says "as shown in
  `existence-paschke`", and **`existence_paschke` is proved**
  (`B/Dils/Paschke.lean:1376`), on the import path.  This is therefore the
  cheapest of the eight once 180V exists: the work is fitting the Paschke
  dilation into the abstract `IsDilation` shape.  **~200 lines after 180V.**
  *Reachable, blocked on the root.*
* **`vn_dilation_order_correspondence` (223VI)** — eff.tex:7095, "By
  `paschke-correspondence`".  `paschke_correspondence_mem`, `_embedding` and
  `_surjective` are all **proved** (`Paschke.lean:2861, 2893, 2973`).  Same
  shape as 221III.  **~200 lines after 180V.**  *Reachable, blocked on the
  root.*
* **`exc_purec_no_biproduct` (224VI)** and **`exc_purec_equal` (224VII)** —
  Exercises\* with **full author solutions** (`bsols.tex:3358–3479` and
  `3480–3540`).  These are the only two vN examples with a transcribable
  proof, but they are also the heaviest: 224VI classifies the non-zero pure
  maps `𝒜 → ℂ` through a GNS representation, `paschke-pure`, minimality of a
  projection and factoriality of `⌈⌈p⌉⌉𝒜`; 224VII works inside `M₄` with
  filters, `⌈ξ(1)⌉` and pseudoinverses.  **~600 and ~400 lines**, each after
  180V *and* after the †-effectus development of parsecs 215–220 that
  `PureCat` and `AndThenEffectus` presuppose.  *Blocked on the root and on
  215–220.*

### `effects_sea` (225V) — the one that does **not** need 180V

*Route.* eff.tex:7381 asserts that `[0,1]_𝒜` is a sequential effect algebra
with `a & b = √a b √a`, without proof.  Note the neighbouring **225VI**
proves only (S1), (S2), (S3) for a †-effectus, so it is not a route to the
whole statement; ours is `SequentialEffectAlgebra` with six fields, and
`seq_comm_orth`, `seq_comm_assoc`, `seq_comm_compat` are the Gudder–Greechie
content.  Everything needed is Mathlib's continuous functional calculus —
**always available, so the old "needs the import" note in `why-open.csv` was
wrong**; the statement is an isolated one with no dependence on the effectus
structure at all.

*Costing.* **~400–600 lines**, dominated by the commutation axioms
(`√a b √a = √b a √b` forces `ab = ba`, and then the identities are C\*-algebra
computations).  *Reachable and independent — the best target in this file
for anyone who does not want to build 180V.*

---

## `StatesPredicates.lean` — one

* **`exc_dm_effectus_kleisli` (192III.3, `exc-dm-effectus`, eff.tex:2410,
  Exercise\*)** — **PROVED, session 83**, by transcribing the author's
  solution (`bsols.tex:1991–2170`), which is complete and usable exactly as
  the survey described it, and the costing of ~500–700 lines was right at its
  low end: **~480 added lines**, of which ~190 are the `MConvexComb` glue and
  ~290 the Kleisli plumbing and the three axioms.  Notes for anyone building on it:
  * The new section `DMKleisli` gives `Kl(𝒟_M)` a concrete `CoprodPres`
    (`one M = PUnit`, `P X Y = X ⊕ Y`, `pinl/pinr = kpure κᵢ`) together with
    `HasTerminal`/`HasFiniteCoproducts`, and the three axioms go through
    `effectusTotalForm_of_pres`, its third worked instance.
  * The only real content is `MConvexComb.exists_glue`: given `α ∈ 𝒟_M(X+1)`
    and `β ∈ 𝒟_M(1+Y)` agreeing in `𝒟_M(1+1)`, the glued `δ` sums to `1`
    because `α(κ₂*) = ⋁_y β(κ₂y)`.  That is the author's own computation.
  * Six `MConvexComb`/`PCM` helpers (`eq_eta_punit`,
    `map_apply_of_unique_fiber`, `PCM.le_of_mem_isSumOf`,
    `eq_zero_of_map_eq_zero`, `exists_map_inl`, `jointly_injective_of_three`)
    were **moved up** in the file, from the `AConv_M` block (parsecs 193–194)
    to just before the `𝒟_M` monad, because 192III.3 needs them earlier.  No
    statement changed; the `AConv_M` uses are unaffected.
  * `Kleisli.Adjunction.adj` is in Mathlib but was **not** used: the coproduct
    is quicker to give by hand than to extract from the adjunction, because
    Mathlib's `BinaryCofan.mk` does not reduce reducibly to the given
    coprojections.  Related trap: `DMKleisli.pres` must be `@[reducible]`, or
    `(pres M).T.of` does not unfold and every `rw` against a `kpure` lemma
    fails with a type mismatch that the error message reports as "did not find
    an occurrence of the pattern".
* **`cancellative_iso_convex` (192V.4, eff.tex:2588)** — cited to
  \[statesofconvexsets, thm. 8\] and **not proved in the thesis**.  QUESTIONS
  **A3**.  *Awaiting a ruling* (confirm that parking is right); if revived it
  is an independent project (the Stone–Kakutani/Gudder embedding of a
  cancellative convex set into a vector space), **~500–600 lines**.  Nothing
  in the tree helps beyond `MConvex.ofConvex` and the `rsum` API.

## `EffectAlgebras.lean` — two

* **`finite_effectMonoid_boolean` (178III.2, eff.tex:640)** — cited to
  \[basmsc, prop. 40\], no proof in the thesis, but **it should not be treated
  as a literature park**: most of `basmsc` prop. 40's ingredients are already
  in the file.  `emon_finite_idem` (`:2731`) proves every element of a finite
  effect monoid idempotent; the proof of `finite_effectMonoid_commutative`
  (`:2763`) shows `a ⊙ b` *is* the meet; and the MSc sup/inf calculus
  (`msc_prop13_*`, `msc_cor14_*`, `msc_prop15*`, `msc_cor16_*`,
  `:1224`–`:1400`) is formalized.  What is missing is the lattice
  (`a ⊔ b := (aᵖ ⊙ bᵖ)ᵖ`), distributivity — for which `EffectMonoid.distrib`
  plus `b ⊔ c = b ⋁ (c ⊙ bᵖ)` is the route — and then the *structure* equality
  `@booleanEffectMonoid M ba = em`, which needs `Perp a b ↔ a ⊙ b = 0` (itself
  a consequence of distributivity).  **~250–400 lines; the best next target in
  this file.**  QUESTIONS **A3** already records the two siblings as proved.
* **`effectModule_unitInterval_representation` (179III.2, eff.tex:739)** —
  Gudder–Pulmannová, cited only.  QUESTIONS **A3**, and additionally
  **our statement is weaker than the cited result** (HANDOFF, "Companion gap"):
  it produces `[PartialOrder V] [IsOrderedAddMonoid V]` and `0 ≤ u` where the
  source needs an *ordered real vector space* with `u` an **order unit**.  As
  written it would be provable without being the theorem.  *Awaiting a ruling:
  strengthen first, or drop.*

---

## Suggested order for the next worker

1. **`effects_sea` (225V)** if you want a self-contained item — it needs
   nothing but the CFC and touches no other statement.
2. **`finite_effectMonoid_boolean` (178III.2)** — no author proof, but the
   ingredients are in `EffectAlgebras.lean` already; see above.
3. **`effectus_vn` + `effectus_vn_partial`**, the root.  Start with
   `IsTerminal (WStarNCPU.of WStar.trivial)` and the binary product `A × B`;
   both are mechanical and neither existed before this session.  Everything
   else in `VNExamples.lean` except `effects_sea` waits on it.

Do **not** start on 211IV/215VI until A/Proc's 105V is closed, and do not add
`import Theses.A.Proc.*` to any file other than `VNExamples.lean`.

---

## New infrastructure added this session

In `Comparisons.lean`, section `FinPACUnique` (general effectus theory; it
**belongs in `Effectus.lean`** and is parked here only because moving it there
would invalidate the whole `B/Eff` olean chain — move it at the next full
rebuild):

* `pcm_eq_of_data` — two `PCM`s agree if their zero, `Perp` and `ovee` do;
* `finPAC_eq_zero_of_hom_to_initial` — every map into the initial object is
  `0`, from the **finPAC axioms alone** (`Quotients.lean` has the same
  statement for an effectus in *partial form*, via `eq_zero_of_one_zero`);
* `perp_pproj`, `ovee_pproj` — `▷₁ ⊥ ▷₂` and `▷₁ ⋁ ▷₂ = ∇`;
* `perp_iff_exists_bound`, `ovee_eq_bound` — the bound characterisation;
* `finPAC_pcm_unique`, `effectusPartialStructure_homPCM_unique`.

In `VNExamples.lean`, section `TrivialAlgebra`: the six missing instances for
`PUnit` and the object `WStar.trivial`.

All are `#print axioms`-clean (`propext, Classical.choice, Quot.sound`), and
both files compile with 0 errors.
