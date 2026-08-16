# `Theses/A/Proc/` — full survey of the remaining `sorry`s (worker 71, 2026-08-16; revised workers 72–78, sessions 47–54)

**Headline count: A/Proc has 78 code `sorry`s** after session 54.
Per file: `Tensor` 39, `Measurement` **11**, `QuantumLambda` 17,
`Duplicators` **11** (was 17).  (`grep -c sorry` over-counts, because the file
docstrings mention `sorry` in prose; the code counts are the ones above.
Note `\bsorry\b` also matches "sorry-ed" in prose — count the compiler's
`declaration uses \`sorry\`` warnings instead.)

> **Session 54 correction — 112XI IS NOT UNBLOCKED BY 77V, and the whole
> `Tensor.lean` upper half is still shut.**
> The row "112XI | blocked on **77V** `vn_extension`" below was wrong, and so
> was the session-53 A/VN note that inherited it.  77V is now proved, and
> 112XI is still out of reach: proc.tex:2998 reads "since `β_⊙` is ultraweakly
> continuous and bounded, and `𝒜⊙ℬ` can **by `tensor-basic`** be considered an
> ultraweakly dense ∗-subalgebra of `𝒯` via `γ_⊙`, the theorem follows from
> `vn-extension`" — it cites **112X as well as 77V**, and all five parts of
> 112X are `sorry`.  Concretely, `vn_extension` wants a map `f : S → 𝒞` on a
> ∗-subalgebra `S ⊆ 𝒯` that is continuous for the topology **induced from
> `𝒯`** plus a bound `‖f s‖ ≤ C‖s‖_𝒯`, and building `f` from `β_⊙` needs
> (i) injectivity of `γ_⊙` (well-definedness; available from 112X.2, or by a
> separate product-functional separation argument);
> (ii) `uwTensorTopology ≤ induced(γ_⊙, ultraweak 𝒯)` — equivalently, every
> norm-limit-of-simple functional on `𝒜⊙ℬ` is the restriction of a normal
> functional on `𝒯`, which is exactly **112X.5**'s first half, whose own hint
> is **87III** `predual_complete` (`A/VN/NormalFunctionals.lean:889`,
> `sorry`).  This is not a Lean artefact: continuity for an *induced* topology
> is equivalent to extendability of the testing functionals, so no amount of
> `BilinNormal β` (continuity for the *finer* `uwTensorTopology`) substitutes
> for it;
> (iii) the norm bound, which converts `hb`'s tensorNorm bound through
> **112X.2** `‖γ_⊙ s‖ = ‖s‖`, resting on **90II.2**
> (`NormalFunctionals.lean:3336`, `sorry`).
> **So A/Proc's external frontier is now three `sorry`s in one A/VN file,
> `NormalFunctionals.lean`: 87III `predual_complete`, 90II.2
> `vn_center_separating_fundamental_2`, and 86IX
> `polar_decomposition_of_functional` (needed by 112X.4).**  Everything above
> them — 112X, 112XI, 114I, 114II, 115II, 116VII and the whole
> functoriality/monoidal block — stays shut.
> **Closed instead this session, all in `Duplicators.lean` and all following
> the thesis's own proofs:** **127VI** `unit_duplicator`, **128VIII**
> `uniqueness_duplicator` (a duplicable von Neumann algebra is commutative and
> its duplicator is multiplication), **128XI** `duplicability_multiplication`,
> **127III**-uniqueness `duplicable_unique`, **132III**.1
> `dup_vna_is_monoid_1` and **132III**.3 `dup_vna_is_monoid_3`.  128VIII cost
> ~90 lines: **128VI** `sef_instrument` and **128II** `tomiyama` were already
> proved in the file, and the only new machinery is that the effects span `𝒜`
> linearly (`mem_span_effects`, `effects_induction`), which is what the
> thesis's "by the usual reasoning" appeals to.
> **128XIII** `duplicable_product` is *not* reachable: the thesis builds
> `π₁ ∘ δ ∘ (κ₁ ⊗ κ₁)`, and `κ₁ ⊗ κ₁` needs `tmap`/`tmapM`, i.e. **115II**.

> **Session 52 update — THE VACUOUS BAND IS OPEN: 111VII and 111XII are
> proved and axiom-clean.**
> `special_tensor` (**111VII**), `vnTensorProduct_exists` and
> `vnTensorProduct_nonempty` (**111XII**, unbundled and bundled) are proved,
> so `vnTensor`, `VNT` and `⊗ᵥ` are now axiom-clean *definitions*.
> **What that buys, measured rather than estimated: exactly 12 previously
> `sorryAx`-tainted declarations became clean — the 3 theorems above plus
> the 9 definitions built from them** (`vnTensor`, `VNT`, `vtmul` in
> `Tensor`; `tensorSub`, `TensorBSurjective` in `QuantumLambda`;
> `Duplicator`, `Duplicable`, `MonoidInWcpsu`, `MonoidInWmiu` in
> `Duplicators`).  **None of the 54 band members flips to clean by itself**
> — every one of them is still a `sorry`; what changed is that their
> statements are no longer vacuous, so proving one now *yields* an
> axiom-clean theorem.  First one done: **116III.1**
> `tensor_simple_facts_1` (+ the reusable `vtmul_nonneg`), which is three
> lines of `a ⊗ b = (√a ⊗ √b)*(√a ⊗ √b)` off miu-bilinearity.
> Session-51's analysis of 111VII was right in every detail; the one thing
> it did not foresee is that the *bundled* 111XII has its two algebras in
> **different universes** while the spatial construction needs both Hilbert
> spaces in one, which cost a `ULift` Hilbert-space instance and
> universe-polymorphic re-proofs of four `A/VN` lemmas (see PROVING-LOG
> session 52 §3).
> **The next gate for `Tensor.lean` is now 112XI `tensor_universal_property`
> (blocked on A/VN 77V `vn_extension`)**, which gates 114I, 114II and — with
> 112X — 116VII; and **115II `exists_tmap`**, which gates all of the
> functoriality/monoidal block (115IV, 115V, 118IV, 119II–119V).

> **Session 51 update — parsec 1020 is closed, and the next gate is 111VII,
> which is in *this* chapter.**
> **102VII** `canonical_quotient_rigid` and **102IX** `pure_is_rigid` are
> **proved and axiom-clean**, together with the index-free `ad_rigid` (any
> `d*(·)d : ⌈d⌉ᵣ𝒜⌈d⌉ᵣ → 𝒜` is rigid) and `stdFilter_rigid`.  102VII cost
> ~210 lines and needed nothing the tree lacked; the only real step is the
> compression `x ↦ eₙ h(x) eₙ` being the identity by **102V** `nmiu-rigid`
> (private `compress_eq_of_ceil`).  Three corrections to what follows:
> (i) **81V `douglas` is proved** — `A/VN/Division.lean`'s seven `sorry`s do
> not include `douglas_1/2` or `sequential_quotient_1`; only **81VIII.2**
> `sequential_quotient_2` and **81IX.2** `div_usc` remain of that block, so
> the "104III.3/.4/.5 → 81V/81VIII" row below is half stale (those three are
> unsolved *exercises* about `div`/`pinv`/infima, not blocked items).
> (ii) **111VII `special_tensor` is NOT in the vacuous band** — its statement
> mentions no `VNT`; it is what *gates* the band, and the table under "(c)"
> should not list it.
> (iii) **111VII is now A/Proc-local.**  Session 50 supplied the last A/VN
> input to `tensor-2` (89IX + `exists_sumVectorNP`); `tensor-1` is **88VI**
> `double_commutant` (proved: `W*(S)` = the ultraweak closure of a unital
> ∗-subalgebra, and the span of the range of `⊗` is one, since
> `(A⊗B)(C⊗D) = AC⊗BD`); `tensor-3` is the thesis's `√T·x⊗y = 0` argument
> plus `(hilbTensor H K).isTensor.dense`.  Only miu-bilinearity of `opTensor`
> ("left to the reader") is genuinely unwritten.  **111VII → 111XII
> un-vacuums 54 of the 88 remaining statements and is the highest-leverage
> target in the chapter.**

> **Session 49 update — 100III is proved, and the parsec-1000 gate is open.**
> **100III** `pure_fundamental`, **100VII**.1/.2/.3 `special_pure_maps_*`,
> **105III**.4 `chevron_f_basic_4` and **105IV**.1/.3
> `chevron_f_purely_positive_1/3` are **proved and axiom-clean**.
> Two corrections to what follows:
> (i) **98XI `ad-pure` was not needed** — (1)⟹(2) reduces to "`π_s ∘ c_p` is
> properly pure", and that factors directly as (filter)∘(corner) with
> `a := √p·s`: `x ↦ ⌊a⌉x⌊a⌉` is a corner `⌈p⌉𝒜⌈p⌉ → ⌊a⌉𝒜⌊a⌉` and `a*(·)a` a
> filter `⌊a⌉𝒜⌊a⌉ → s𝒜s`, so no polar decomposition and no iterated corners.
> 98XI is still **not transcribed**, and reading it produced ERRATA **98XI**
> (its `[f] = [a](·)[a]*` has the brackets swapped).
> (ii) **our `IsPure` (100I) was mis-transcribed** — no von Neumann hypothesis
> on the algebra in the middle of a composition, which makes (1)⟹(2)
> unprovable; `[VonNeumannAlgebra B]` was added to the `comp` constructor
> (PROVING-LOG session 49 §1).
> **The chain above 100III is now blocked only by A/VN**: 104III.3/.4/.5 wait
> on 81V `douglas` / 81VIII `sequential-quotient`, and 104VII → 104IX →
> 105V-uniqueness → 105VII / 106I-uniqueness behind them.  The one big
> *reachable* item left in `Measurement.lean` is **102VII**
> `canonical_quotient_rigid` (and 102IX behind it).

> **Session 48 update — both parsec-980 blockers are gone.**
> **98III** `filters_composition` and **98VI** `corners_composition` are
> **proved and axiom-clean**, and neither needed the machinery the previous
> two surveys expected: 98III needs no `⌊√p'√q⌉ = ⌈p'⌉` (see below), and 98VI
> needs neither the printed hint nor its converse.  Also closed: **103II**.1/.2
> (`purely_positive_examples_1/2`), **105III**.1-2 (`chevron_f_basic_12`),
> **105V** existence (`positive_map_uniqueness_exists`) and **106I** existence
> (`uniqueness_sequential_product_exists`).  **The single blocker of the whole
> parsec 1000–1060 chain is now 100III `pure_fundamental`**, and inside it the
> one hard implication (1)⟹(2), which needs **98XI `ad-pure`** — the statement
> that `[a*(·)a] = [a](·)[a]*` is an ncpu-isomorphism.  `ad-pure` is an
> *Example* in proc.tex and **is not transcribed in the Lean file at all**; it
> needs 82I `polar-decomposition` (proved, A/VN) plus corner bookkeeping.
> Everything else in 100III is short: (2)⟹(3) is the uniqueness clause of
> 98IX, and (3)⟹(1) is `f = c_{f(1)} ∘ [f] ∘ π_{⌈f⌉}` with an iso in the
> middle (an ncp-isomorphism is a filter — see `isPure_of_iso`).

> **Session 47 update — 96V is proved, and the Measurement chain is open.**
> `canonical_filter` (**96V**) is closed and axiom-clean, and does **not**
> need the false conjunct of 81IX: only 81VI.1/.2 and 81VII (all proved) are
> used, and the thesis's `div-usc` step for *normality* is replaced by an
> elementary bipositivity argument (ERRATA row **96VI**).  Two corrections to
> the map below follow: (i) our Lean statement of 96V used `suppProj d` where
> the thesis has `\ceilr{d} = rangeProj d`, which made it **false** — fixed;
> (ii) with `isFilter_stdFilter` in place, the parsec-980 block is no longer
> one undifferentiated block behind 96V.  **Closed in session 47:** 96V,
> 98II.1, 98II.2, 98II.3, 98VII, 98VII-formula, 98IX `exists_sqBracket`,
> 98IX `square_f`, 100II.3.  **Still blocking the rest of parsec 980–1000:**
> **98III** `filters_composition` and **98VI** `corners_composition`, which
> together gate 100III `pure_fundamental` and everything above it.

## Classification summary

| class | count | share |
|---|---|---|
| (c) **vacuous band** — statement mentions `VNT`/`⊗ᵥ`/`Duplicator`, hence depends on `sorryAx` through **111XII**; can never be closed axiom-cleanly until 111XII is | **56** | 64% |
| (b) blocked on a *named* `sorry` outside A/Proc, or on another A/Proc `sorry` | **~24** | 27% |
| (a) self-contained / reachable now | **4** (124I, 125II, 125cIII, 130IV) | 5% |
| (c′) cited to literature, no thesis argument at all | **1** (121II) | 1% |
| (d) suspicious | **0 new** (3 already-known false statements are recorded and realigned) | |

*(Recomputed in session 51 against the current 88.  `QuantumLambda` and
`Duplicators` were surveyed per-declaration for the first time; the earlier
band figures for those two files were both wrong, in opposite directions.
`Measurement`'s and `Tensor`'s rows have not been re-derived — the per-item
tables below are the current record.)*

The two blockers that gate almost everything:

* **89IX `normal_functional`** (`A/VN/NormalFunctionals.lean:1727`, `sorry`) —
  gates **111VII** `special_tensor`, hence **111XII**, hence the whole
  54-statement vacuous band.  48VIII `ngns` (the other input to 111XII) **is
  proved**, so 89IX is the *only* thing between A/Proc and un-vacuuming 47% of
  the chapter.  **This is by a wide margin the highest-leverage item for
  A/Proc, and it is in A/VN, not here.**
* ~~**81VI / 81VII / 81IX** gate **96V**~~ — **resolved.** 81VI.1/.2, 81VII,
  81V.1/.2 and 81VIII.1 are proved (session 46), and 96V is proved from them
  (session 47).  81IX's false second half is **not** needed.

## (a) Reachable now

| DISP | decl | file:line | note |
|---|---|---|---|
| **99XI** | `filter_of_projection_multiplicative` | Measurement 2601 | **CLOSED this session** |
| **106III**.1 | `sequential_product_counterexample_1` | Measurement ~4281 | **CLOSED this session** — was unblocked by the new `isFilter_cornerIncl`: axiom (B) needs `⌈p⌉(·)⌈p⌉` to be *pure*, which is `corner ; filter` with the filter being the corner inclusion of a projection.  (C) collapses to `⌈p⌉q⌈p⌉ = ⌈p⌉q⌈p⌉`, (D) is `q := p`, (E) reduces to `e₁⌈p⌉e₂ = 0` being star-symmetric (no contraposition theory needed), and ¬(A) needs `⌈½·1⌉ = 1 ≠ ½·1`. |
| **98II**.2 | `filter_basic_2` | Measurement 2018 | **two of the three conjuncts are directly provable** — see "the near miss" below |
| **124I** | `vn_generation_bound` | QuantumLambda 678 | pure cardinal arithmetic on `wstar S`; no thesis proof, no dependency on anything sorried |
| **125II** | `vn_gns_bound` | QuantumLambda 729 | `ngns` + a cardinality count of the GNS direct sum; `ngns` is proved |
| ~~**129X**~~ | `continuous_finite_measure_space_not_duplicable` | Duplicators 725 | **REMOVED (session 51)** — `hd : Duplicable 𝒜` is in the *type*, so it is tainted after all; and proc.tex:6367 really does use the product functional `ω⊗ω` and `carrier-tensor` faithfulness |
| **130IV** | `measure_space_partition` | Duplicators 1019 | (a) — its recorded obstruction has been discharged; see the `Duplicators` table |
| **125cIII** | `Fha_concrete` | QuantumLambda 894 | (a) but long — nothing it needs is `sorry` |

### The near miss: 98II.2 `filter_basic_2` — **superseded (session 47)**

*Kept for the record; 98II.2 was closed the thesis's own way, through 98II.1,
once 96V made `c_p` a filter.  The ℂ-gadget below is still the cheapest new
infrastructure in the chapter, but nothing in parsec 980 needs it any more.*


Worth writing down because it is a genuinely short route the thesis does not
take, and because it stops one gadget short.

* **mono in `W*_cp`** is immediate from `IsFilter.universal`'s *uniqueness*
  clause once `g`, `h` are rescaled into the unit ball by `s⁻¹` with
  `s = ‖g 1‖ + ‖h 1‖ + 1` (the universal property demands `f 1 ≤ c 1`, which
  an arbitrary ncp-map does not satisfy).  `exists_ncpSmul` +
  `Theses.A.CStar.ofReal_smul_nonneg` + `algebraMap_ofReal_mono` do it in
  ~20 lines.  Written and type-checked during the session.
* **`c z = 0 ⟹ z = 0` for positive `z`** then follows from mono applied to
  `√z(·)√z` and the zero map: for positive `x`, `√z x √z ≤ ‖x‖·z`, so
  `c(√z x √z) = 0`; extend to all `x` by `x = ℜx + i·ℑx`, `y = y⁺ − y⁻`.
  Hence **faithfulness `⌈c⌉ = 1` is reachable**.
* **Injectivity is not**, and the obstruction is precise: it needs mono at
  `B = ℂ`, i.e. the ncp-map `ℂ → C`, `ζ ↦ ζ·a` for positive `a`.  **The tree
  has no ncp-map out of `ℂ`** — no `algebraMap` as an `NCPMap`/`NMIUMap`, and
  `cp_commutative_dom` (34IX.2) is itself `sorry`.  Building it needs
  (i) `M ≥ 0` in `M_k(ℂ)` implies `M.map (algebraMap ℂ C) ≥ 0` (route:
  `M = star X * X`, and `CStarMatrix.map` of a ∗-hom is multiplicative), and
  (ii) `algebraMap ℂ C` preserves directed suprema (route: a LUB of reals is
  in the closure of the set, and the positive cone of `C` is norm-closed).
  **That gadget is reusable and would close 98II.2 outright**; it is the
  single cheapest piece of new infrastructure in this chapter.

Since the statement is one conjunction, the two provable clauses cannot be
banked separately, so the `sorry` stands.

## (c) The vacuous band — 56 statements behind 111XII

*(Recounted per-declaration in session 51: `QuantumLambda` is 10, not 13, and
`Duplicators` is 14, not 9.  **111VII `special_tensor` is not in the band** —
its statement mentions no `VNT`; it is what gates the band, and it has been
removed from the `Tensor.lean` list below, which is therefore 31.)*

**Session 52: this band is no longer vacuous.**  `vnTensorProduct_nonempty`
is proved, so `vnTensor`/`VNT`/`⊗ᵥ` are axiom-clean and every statement below
is now a real (provable, and once proved axiom-clean) obligation rather than a
vacuous one.  The list is kept because it is still the list of open `sorry`s;
strike 111XII ×2 (proved) and 116III.1 (proved, session 52).  Historical note:
their *types* mention `VNT 𝒜 ℬ = (vnTensor 𝒜 ℬ).carrier`, and `vnTensor` used
to be `Nonempty.some` of the sorried `vnTensorProduct_nonempty`.

* `Tensor.lean` (31, of which 111XII ×2 and 116III.1 are now closed): 115II ×2
  (`exists_tmap`, `tensor_functorial`), 115IV ×2, 115V, 116I ×2, 116III.1/.2/.4/.5,
  116IV.1/.2, 117III, 118II ×2, 118IV.1/.4/.5/.6, 119II, 119IV, 119IVb, 119IVc,
  `exists_tmapM`, 119V ×5.  (`tensor_simple_facts_3` and `product_functional_norm`
  are tainted too — via `predualTensor`, itself chosen from a sorried existence.)
* `QuantumLambda.lean` (10): 123II.1/.2, 125IV, 125VI, 125VIIb, 125VIII,
  125dII, 125eIIa, 125eIII, 125eVII.  **Not** tainted (corrections, session 51):
  **121II** (it is about the *concrete* Hilbert-space tensor product, whose
  `hilbTensor` comes from the **proved** `hilbertTensor_nonempty`), **125bII**
  and **125cIII** (`HaFreeMIU` / `MatAlg` / `lp` contain no `VNT`, and the
  `VonNeumannAlgebra (MatAlg n)` instance `Theses.A.VN.mn_vna_1` is proved).
* `Duplicators.lean` (14, of which six are now closed — session 54: 127III
  uniqueness, 127VI, 128VIII, 128XI, 132III.1, 132III.3): 127III (main
  equivalence ~~and uniqueness~~), ~~127VI~~,
  ~~128VIII~~, ~~128XI~~, **128XIII**, **129X**, ~~**132III.1**~~, 132III.2/~~.3~~/.4,
  **132III.5**, 132IV, **132VI** `free_monoid_in_Wcpsu`.  The five in bold were
  previously classified (b) or (a); each carries `Duplicable`/`Duplicator`/`⊗ᵥ`
  in its *type*, hypothesis side included, so none can be axiom-clean before
  111XII.  Only **130IV**, **130V** and the unit `exists_freeMonoidUnitCpsu`
  are untainted.

## (b) Blocked, with the named blocker

### `Measurement.lean` (parsecs 960–1060) — 11 left, 2 closed in session 51 (7 in session 49, 7 in session 48, 9 in session 47)

| DISP | decl | blocked on |
|---|---|---|
| 96V | `canonical_filter` | **CLOSED (session 47)** — also `isFilter_ad`, `isFilter_stdFilter`, `ldiv_div_ad`, `ad_injective`, `ad_bipositive` |
| 98II.1 | `filter_basic_1` | **CLOSED** |
| 98II.2 | `filter_basic_2` | **CLOSED** — via 98II.1, so the ℂ-gadget of the "near miss" below was **not** needed |
| 98II.3 | `filter_basic_3` (bipositivity) | **CLOSED** |
| 98III | `filters_composition` | **CLOSED (session 48)** — and the "route that should work" recorded in session 47 (reduce to `c_q ∘ c_{p'}` and prove `⌊√p'√q⌉ = ⌈p'⌉`) is **not needed**.  The obstruction (`f(1) ≤ d(c(1))` does not give `f(1) ≤ d(1)`) is removed by *rescaling*: `c(1) ≤ l·1` with `l = ‖c(1)‖+1`, so `f(1) ≤ l·d(1)`, and `l⁻¹f` factors through `d`; rescaling the factor back by `l` gives `h'` with `d(h'(1)) = f(1) ≤ d(c(1))`, hence `h'(1) ≤ c(1)` by bipositivity of `d` (98II.3), hence a factorisation through `c`.  Uniqueness is injectivity of both (98II.2).  Total: ~45 lines, using `exists_ncpSmul` |
| 98VI | `corners_composition` | **CLOSED (session 48)** — using neither the printed hint nor its converse.  Take the composite's effect to be `s := β'(r)`, the transport of `τ`'s effect along the 98IV.1 isomorphism `β : ⌊p⌋𝒜⌊p⌋ ≅ ℬ`; then `s ≤ ⌊p⌋ ≤ p` and `π(1−s) = 1−r`, and the universal property falls out of `π`'s and `τ`'s.  Uniqueness is surjectivity of `τ∘π` (98IV.2).  ERRATA row 98VI and QUESTIONS A1 updated |
| 98VII, 98VII-formula | `filter_corner`, `filter_corner_formula` | **CLOSED** (the thesis's proof verbatim) |
| 98IX | `exists_sqBracket`, `square_f` | **CLOSED** |
| 100II.3 | `isPure_adSelf` | **CLOSED** (`a*(·)a = canonicalFilter a ∘ π_{⌊a⌉}`) |
| 100III | `pure_fundamental` | **CLOSED (session 49)** — and **without 98XI**: `π_s ∘ c_p` factors directly as (corner into `⌊a⌉𝒜⌊a⌉`) then (filter `a*(·)a`), `a = √p·s`.  Needed one repair to our own `IsPure` (see the session-49 note above) |
| 100VII.1/.2/.3 | `special_pure_maps_*` | **CLOSED (session 49)** — a unital filter and a corner of `1` are isomorphisms |
| 102VII | `canonical_quotient_rigid` | **CLOSED (session 51)** — the thesis's proof, ~210 lines; `approximate_pseudoinverse` (80IV), `IsApproxPseudoinverse.mul_eq_suppProj`, `partialSums_of_isLUB`, `ceil_fundamental_1` (60VII.1) and `nmiu_rigid` were all already in the tree.  The final limit is taken **ultraweakly** on the truncations `eₘ x eₘ`, not ultrastrongly on `eₙ h(eₙ a eₙ) eₙ`, so `cp-uscont` and the corner-topology transfer are not needed (ERRATA **102VIII**) |
| 102IX | `pure_is_rigid` | **CLOSED (session 51)** — 60 lines from `ad_rigid` at `d = √f(1)` (`stdFilter_rigid`), the 98IX square, and 100III's inverse for `[f]`; the thesis's `⋄`-computation is replaced by the pointwise identity `π_{⌈f⌉}(q.val) = q` |
| 103II.1/.2 | `purely_positive_examples_*` | **CLOSED (session 48)** — .1 is `isPure_adSelf` (100II.3) plus 101VII.1 at `a* = a`; .2 is `a(·)a = g∘g` for `g = √a(·)√a` |
| 104III.2a | `centrally_similar_basic_2a` | **parked: false as printed**, ERRATA row exists |
| 104III.3/.4/.5 | `centrally_similar_basic_*` | **not blocked** — 81V `douglas` and 81VIII.1 are proved (correction, session 51).  These are unsolved exercises about `div`, `pinv` and infima of positive elements, with no published solution (asols stops at parsec 340) |
| 104VII | `positive_quotients_centrally_similar` | 104III.4/.5 (80IV is now proved — correction to w46 §7) |
| 104IX | `faithful_positive_map_uniqueness` | 100VII + 104VII |
| 105III.1-2 | `chevron_f_basic_12` | **CLOSED (session 48)** — part 1 is the defining formula, part 2 is the 98IX square at `a ∈ ⌈f⌉𝒜⌈f⌉` plus `ceilOne_conj` |
| 105III.4 | `chevron_f_basic_4` | **CLOSED (session 49)** |
| 105IV.1/.3 | `chevron_f_purely_positive_*` | **CLOSED (session 49)** — and neither needed 105III.4: the map `u f(·) u` is pure directly (corner ∘ `f` ∘ `cornerIncl`), and its ⋄-self-adjointness transports from `f`'s via the new `corner_ceil_val` (ceilings in a corner are ambient ceilings) and `le_sub_iff_le_one_sub` |
| 105V uniqueness, 105VII | `positive_map_uniqueness`, `sqrt_axiom` | 104IX (105IV is now proved; the thesis's proof cites `faithful-positive-map-uniqueness` = 104IX explicitly).  **105V existence is CLOSED (session 48)**: it is `adSelf √p`, ⋄-positive by 103II.2 — it never needed 104IX |
| 106I uniqueness | `uniqueness_sequential_product` | 105V uniqueness.  **106I existence is CLOSED (session 48)**: (A)/(C)/(D) are `√p√p = p` computations, (B) is `adSelf √p` with 100II.3, and (E) is 101VII.1 transported from ceilings to the order by the new private helper `effect_le_isStarProjection_iff` (`b ≤ q ↔ ⌈b⌉ ≤ q` for an *effect* `b` and a projection `q`) |
| 106III.1 | `sequential_product_counterexample_1` | **CLOSED this session** |
| 106III.2/.3 | `sequential_product_counterexample_2/3` | purity-free? .2's axioms (A)(C)(D)(E) are computations; (E) needs contraposition.  Worth a look after 106III.1 |

### `Tensor.lean` — the 11 untainted ones

| DISP | decl | blocked on |
|---|---|---|
| 112X.1 | `tensor_basic_1` | **90II.2** `vn_center_separating_fundamental_2` (A/VN, `sorry`).  *Correction to earlier notes:* 90II**.1** is now **proved** and is exactly this statement's first conjunct; only the norm-approximation conjunct is left, and the two sit in one theorem. |
| 112X.2 | `tensor_basic_2` | 90II.2 (21VII `order_separating_norm` is now **proved**) |
| 112X.3 | `tensor_basic_3` | 112X.2 |
| 112X.4 | `tensor_basic_4` | 74IV/74VI now **proved**; still needs **86IX** `polar_decomposition_of_functional` (A/VN, `sorry`) |
| 112X.5 | `tensor_basic_5` | **87III** `predual_complete` (A/VN, `sorry`) |
| 112XI | `tensor_universal_property` | ~~77V~~ — **77V is proved (session 53); 112XI is blocked on 112X.2 and 112X.5**, hence on **87III** and **90II.2**.  See the session-54 note at the top |
| 114I | `tensor_universal_property_extra` | 112XI |
| 114II | `tensor_uniqueness` | 112XI |
| 116VII | `tensor_characterization` | 112X + 116IV |

### `QuantumLambda.lean` — the 7 untainted ones (recounted, session 51)

| DISP | decl | file:line | class | note |
|---|---|---|---|---|
| 121II | `intersection_tensor` | :326 | (c′) | proc.tex:4473 gives no argument, only "See Corollary IV.5.10 of Takesaki I".  **Not** in the vacuous band |
| 123I.3 | `linf_tensor` | :650 | (b) | **116VII** `tensor_characterization` (`Tensor.lean:2407`, `sorry`), which proc.tex:4645 cites explicitly; parts 1/2 of the exercise are proved just above it |
| 124I | `vn_generation_bound` | :678 | (a) | proc.tex:4696 needs `#(∗-algebra generated by S) ≤ #ℂ + #S` **and** that every element of `wstar S` is an ultraweak limit of a filter on it — the tree has **no** characterisation of `wstar` as a closure (only `isVNSubalgebra_wstar`), so a transfinite-closure construction has to be written |
| 124III | `second_adjunction` | :707 | (b) | Freyd's AFT: needs products and equalisers in `W*_miu` preserved into `W*_cpsu`.  47V `vn_equalisers` is **proved**; **47IV.3 `vn_products_ncpsu` (`A/VN/Basic.lean:2905`, `sorry`) is the real external blocker** — the earlier note ("124I + 125II + Zorn") missed it |
| 125II | `vn_gns_bound` | :729 | (a) | `ngns` is proved and `gnsHilb`/`exists_faithful_normal_rep` give the representation concretely; only the cardinal count `#H ≤ 2^#A` is left (the thesis's `#H = Σ_ω #H_ω` is correct only via countable support of `ℓ²`-families) |
| 125bII | `ha_second_adjunction` | :852 | (b) | AFT again: `ha_equalisers` (84bV, `A/VN/Division.lean:3084`), `hereditarilyAtomic_subalgebra` (84bIII, `Division.lean:3074`) and `vn_products_ncpsu`, all `sorry` |
| 125cIII | `Fha_concrete` | :894 | (a), long | nothing it needs is `sorry`: `HereditarilyAtomic` *is* the direct-sum decomposition by definition, and `mn_vna_1` is proved.  The work is the representatives/re-indexing bijection |

### `Duplicators.lean` — the 3 untainted ones (recounted, session 51)

| DISP | decl | file:line | class | note |
|---|---|---|---|---|
| 130IV | `measure_space_partition` | :1019 | (a) | **the recorded obstruction is gone**: `lp_infty_nonneg_iff` / `lp_infty_le_iff` (`A/VN/Basic.lean:765 ff.`) and 47IV.1/.2 supply the componentwise order on `lp ℬ ∞`.  proc.tex:6518 is a bare Exercise — build `𝒜 ≅ ⊕ₙ ℬₙ` from `IsLinftyOf` by restriction maps; ordinary measure theory |
| 130V | `discrete_ell_x` | :1034 | (b) | 130IV alone; `atomic_measure_space` (same file, :892, **proved**) already turns each atom into `ℂ` |
| 132VI unit | `exists_freeMonoidUnitCpsu` | :1206 | (b) | **47IV.3 `vn_products_ncpsu` (`A/VN/Basic.lean:2905`, `sorry`)** — it is exactly the `W*_cpsu` product of the family `(ω)_{ω ∈ W*_cpsu(𝒜,ℂ)}`.  The earlier note ("missing componentwise positivity of `CStarMatrix n (lp …)`") named the symptom, not the blocker |

Everything else in the file is in the vacuous band (see above).  Note that
128VIII's main input, **Tomiyama 128II**, is proved in this file (`tomiyama`).

## (c′) Cited to literature

* **121II** `intersection_tensor` — proc.tex:4473 cites Takesaki IV.5.10 and gives
  no argument.  (**Not** in the vacuous band — correction, session 51: it is about
  the concrete Hilbert-space tensor product.)

## (d) Suspicious

Nothing new found this session.  The three already-known false statements of
this chapter are all recorded and the Lean statements realigned:
104III.2a (parked), 104IV (repaired, ERRATA), 101VII.2 (repaired, ERRATA),
117II.1 (repaired and since **proved**).

## Corrections to earlier reports

1. **A/Proc is 115 (now 114), not ~120.**
2. **48VIII `ngns` is proved.**  111XII therefore hangs on 111VII alone, and
   111VII on 89IX alone.  Earlier notes named "89IX" as *a* blocker; it is
   *the* blocker, and it now gates 54 statements — nearly half the chapter.
3. **21VII `order_separating_norm` and 90II.1 are now proved**; only 90II.2
   blocks 112X.1/.2.  w42's table listed 90II wholesale.
4. **80IV `approximate_pseudoinverse` is proved** (session 36), so w46 §7's
   "104VII is blocked on 80IV" is stale; 104III.4/.5 are what is left there.
5. **74IV/74VI are proved** (sessions 23/25), so w42's entry for 112X.4 is
   down to 86IX alone.
6. The standard filter `c_p` of a *projection* does **not** need 96V: the
   corner inclusion is a filter by an elementary argument (now in the tree as
   `isFilter_cornerIncl`).  Earlier maps treated all of parsec 980 as one
   block behind 96V.
