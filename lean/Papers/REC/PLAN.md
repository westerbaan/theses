# REC — plan of the formalisation

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707 (2021).  Source `../papers/2109.10707/short.tex`
(macros `preamble.tex`), index `../papers/REC-points.csv` (136 points, one
global counter over definitions, examples, remarks, lemmas, propositions,
theorems, corollaries).  Doc comments open `**REC n**`; audit rows go in
`docs/audit/papers-rec.csv`.

Written 2026-09-26 (phase 1).  Status column = state at the end of phase 1 (§2 and §3 formalised in `Effectus.lean` and `Algebras.lean`).

## 1. The main theorems, precisely

The paper's goal (§5, §6) is three theorems about a **sequential effectus**
(REC 100): a *normal* (REC 30) effectus *separated by states* (REC 14) with

1. filters (REC 23) and comprehensions (REC 22);
2. images of comprehensions (REC 62);
3. the pure maps (REC 78) form a dagger category;
4. every pure `f` is ⋄-adjoint (REC 70) to `f†`;
5. for every predicate `p` a *unique* †-positive pure `asrt_p : A → A` with `1 ∘ asrt_p = p`;
6. `p & q := q ∘ asrt_p` makes every `Pred(A)` a *normal SEA* (REC 56).

* **REC 102** (`thm:JB-embedding`).  A sequential effectus is equivalent to a
  product `C₁ × C₂` of effectuses, where the predicate spaces of `C₁` are complete
  Boolean algebras and those of `C₂` are (unit intervals of) directed-complete
  JB-algebras; the predicate functors `C₁ → CBAᵒᵖ`, `C₂ → JB_npcᵒᵖ` are faithful
  iff `C` is separated by predicates.
* **REC 103** (`thm:JBW-CBA`).  If moreover the scalars are irreducible (REC 20),
  either all predicate spaces are complete Boolean algebras or all are unit
  intervals of JBW-algebras (REC 48), with a predicate functor into `CBAᵒᵖ`
  resp. `JBW_npcᵒᵖ`, faithful iff separated by predicates.
* **REC 136** (`thm:JW-algebra`).  For a *monoidal* sequential effectus (REC 122)
  with irreducible scalars `≠ {0,1}` there is a functor `F : C → JW_npcᵒᵖ` with
  `Pred(A) ≅ [0,1]_{F(A)}` (printed `F(Pred(A))`, ill-typed — see §4), faithful
  iff separated by predicates.

### What they rest on

| used for | result | where from | treatment in Lean |
|---|---|---|---|
| 35, 93, 95, 97, 99c, 102 | dc effect monoid `≅ B ⊕ C(X,[0,1])` (REC 34) | OAP 69 (`mainthmdirectedcomplete`) | Prop `EffectMonoidDCClassification`; **discharged**: `rec34_holds` (`Scalars.lean`, from `Papers.OAP.oap69`) — pass it for `h34` |
| 103 | irreducible dc effect monoid `∈ {0},{0,1},[0,1]` (REC 36) | OAP 71 (or REC 34 + "connected Stonean = point") | Prop, hypothesis until OAP importable |
| 92 | idempotents of an effect monoid are central | OAP 20 | **in-house** (4 lines: `p·a·p^⊥ ≤ p·p^⊥ = 0`) |
| 96 | orthoalgebra SEA with all elements idempotent is Boolean | SEA 44 (`prop:SEAsharpisBoolean`, cited as "Prop. 45") | **discharged**: `sea44_holds` (`Decompose.lean`, from `Papers.SEA.sea44_booleanAlgebra`) |
| 105, 106, 109 | normal SEA: `⌈a⌉`, `⌊a⌋` exist; `b&a=a ⇒ b ≥ ⌈a⌉`; idempotents a complete lattice (REC 57) | SEA 49–50, 71, … | from SEA |
| 119, 120, 125 | spectral theorem for convex normal SEAs, sharp elements norm-dense (REC 58) | SEA 36 (`seaspectral`) and §6 of SEA | from SEA |
| 38 | `{0,1}` scalars + state separation ⇒ orthoalgebras | cited SIG; SIG only has a σ-version (SIG 48/50) | **in-house** (the Prop 93 argument, 5 lines) |
| 43 | `[0,1]` scalars ⇒ convex predicate spaces | SIG 25/27 | **in-house** (tree `predEffectModule`) |
| 42, 94, 95 | `DCOUS ≃ DCEA_c` | cited "cf. SIG Prop 55"; SIG proves only the σ-version (SIG 56) | in-house on top of the tree's cone/`Vec` construction (thesis B 179) + black box `WrightMonotoneCompleteBanach` (Wright 1972, Lemma 1.1: a dc OUS is Banach) |
| 119 | `ω(a)=0 ⇒ ω(p&a) = ω(p^⊥&a)` | "exactly as" van de Wetering 2018 (*Sequential measurement characterises…*) Prop 46 — **not printed** | reconstruct in-house (preferred) or black box `WeteringStateOrderLemma` |
| 120 | `(1-λδ)^{-1} ≥ 0` iff `1-λδ` maps non-positives to non-positives | Alfsen–Shultz, *State spaces* (1.82) | black box `AlfsenShultzResolventPositivity` (likely provable) |
| 121 | order derivations `D_p` ⇒ JB-algebra | Alfsen–Shultz, *Geometry*, Thm 9.48 (via 9.43) | **black box** `AlfsenShultzJordanFromDerivations` — the load-bearing external result of 102/103 |
| 118 | order-derivation criterion | Alfsen–Shultz, *State spaces*, Prop 1.108 | stated as black box; *not* used by the proof (120 reworks A–S 1.106 instead) |
| 61 | convex normal compressible quadratic SEA ⇒ JB | van de Wetering 2018, Thm 4 | stated as black box; not used by the main proofs |
| 123–128 | `Q_{√a}` is the unique ⋄-positive map with `Q 1 = a` | van de Wetering PhD thesis 2021, Thm 4.6.17 | black box `WeteringQuadraticUnique` |
| 135 | JBW = JW ⊕ purely exceptional (REC 52) | Hanche-Olsen–Størmer Thm 7.2.7 | black box `HancheOlsenStormerDecomposition` |
| 133 | purely exceptional JBW `≅ C(X, M₃(𝕆)_sa)` (REC 55) + `M₃(𝕆)_sa` is type I₃ (H-O–S 2.8.3) | Shultz 1979; Hanche-Olsen–Størmer 2.8.3 | Mathlib has **no octonions**: black box the *combination*, i.e. REC 133's conclusion, as `ShultzExceptionalIdempotents` (records a deviation: the Albert algebra is never constructed) |
| 130, 135 | universal von Neumann algebra `W*(V)` (REC 129) | Hanche-Olsen–Størmer Thm 7.1.9 | black box `HancheOlsenStormerUniversalEnvelope` |
| 135 | ≥ 4 mutually exchangeable idempotents summing to 1 ⇒ JW (REC 132) | Alfsen–Shultz, *Geometry*, Lemma 4.4 | black box `AlfsenShultzFourExchangeable` |
| 46 only | EJA classification | Jordan–von Neumann–Wigner | **not used** by any main theorem; Example 46 left as a remark |

Every black box enters as a named `Prop` (e.g. `def AlfsenShultzJordanFromDerivations : Prop := …`)
and appears as an explicit hypothesis of 102/103/136 — never an `axiom`, never a `sorry`.
The OAP/SEA/SIG items are the same kind of hypothesis *until* those libraries have
oleans; then they are discharged by the corresponding theorem and the hypothesis disappears.

## 2. Files

`lean1.sh` writes no olean, so a new file cannot import another new file in the
session that creates it.  Hence §3 lives with §2.1–2.2 (it needs REC 23, 28, 30).

| file | sections | points | est. lines |
|---|---|---|---|
| `Papers/REC/Effectus.lean` | §2.1, §2.2, §3 | 1–36, 62–86 | ~2,400 |
| `Papers/REC/Algebras.lean` | §2.3–§2.5 | 37–61 | ~1,500 |
| `Papers/REC/Decompose.lean` | §4 | 87–99 | 2,750 (done 2026-09-26): explicit coproducts, generic Karoubi effectus `KCat`, splitting theorem, 87–98, `BoolMat`, 99 refuted |
| `Papers/REC/DecomposeFinite.lean` | §4.4 | 99 (corrected) | 260 (done 2026-09-26) |
| `Papers/REC/Scalars.lean` | §2.2 | 34, 35 discharged | 90 (done 2026-09-26): `rec34_holds` from OAP 69 |
| `Papers/REC/Reconstruction.lean` | §5 | 100–121 | ~2,500 |
| `Papers/REC/Monoidal.lean` | §6 | 122–136 | ~1,800 |

## 3. Point table

Kinds: D definition, E example, R remark, L lemma, P proposition, T theorem, C corollary.
"tree" = the statement is already a theorem/definition of `Theses/` (thin restatement:
our proof cites it).  Status: **done** (compiled, audit row), **stated** (statement
compiled, proof is an external result taken as hypothesis/Prop), **deferred** (not
started; reason), **n/f** (not formalised: no mathematical claim, or a claim about
external literature).

### §2.1 Effectus theory (Effectus.lean)

| # | k | content | deps | tree / external | status |
|---|---|---|---|---|---|
| 1 | D | effectus in total form; partial maps, states, predicates; `Par(C)` | – | tree 180I `EffectusTotalForm`, `Par` | done (thin) |
| 2 | E | Set; Kl(finite distributions); (fd) C*ᵒᵖ with PU maps | 1 | tree `extensive_effectus_set`, `set_pred_subset`, `exc_dm_effectus_kleisli`; C*/PU: not in tree | done 1–2; 3 deferred (tree has vNᵒᵖ with NCPU maps and OUSᵒᵖ, neither is C*/PU) |
| 3 | R | Schrödinger vs Heisenberg picture | – | – | n/f |
| 4 | D | PCM, additive, biadditive, PCM-enriched | – | tree 174II `PCM`, `PCMHom` | done |
| 5 | D | partial projections, compatible families, finPAC | 4 | tree 180VII `FinPAC`, `pproj₁/₂` (binary; paper: finite J) | done |
| 6 | D | effect algebra; order, `⊥`, additive ⇒ monotone | 4 | tree 175I, 176 `eabasics_*` | done |
| 7 | E | orthomodular lattice as EA with `x⊥y ⟺ x∧y=0` | 6 | tree 175II.4 uses `x ≤ y^⊥` | **FALSE as printed**; refuted in Lean (MO2); corrected form done |
| 8 | E | `[0,1]_𝔄` is an EA | 6 | tree `orderIntervalEffectAlgebra` | done |
| 9 | D | effectus in partial form; total maps | 5, 6 | tree 180VII `EffectusPartialForm`, `IsTotal` | done (thin) |
| 10 | R | `Par`/`Tot` equivalence | 1, 9 | tree 180X Cho (`cho_thm_1`, …); "2-categorical" part not in tree | done (1-categorical halves only) |
| 11 | E | Pfn, Kl(subdistr.), C*ᵒᵖ contractive positive, EAᵒᵖ in partial form | 9 | tree: `Par (Type u)` instances | done for Pfn; rest deferred |
| 12 | D | `Pred(A)`, `Pred(f)`; functor to EAᵒᵖ | 9 | tree 190II `Pred`, `predMap` | done (functor laws, additivity) |
| 13 | D | separated by predicates | 12 | tree 190II.7 `SeparatingPredicates` | done (thin) |
| 14 | D | separated by states | 12 | tree 190II.7 `SeparatingStates` | done (thin) |
| 15 | D | effect monoid (bi-additive axioms); idempotents | 6 | tree 178II `EffectMonoid` (four-fold law) | done: both directions of the axiom translation |
| 16 | E | Boolean algebra effect monoid, commutative | 7, 15 | tree `booleanEffectMonoid` | done |
| 17 | E | scalars form an effect monoid, `s·t = s∘t` | 9, 15 | tree `scalEffectMonoid` | done (thin) |
| 18 | E | `C(X,[0,1])` commutative effect monoid | 15 | tree `continuousUnitIntervalEffectMonoid` | done |
| 19 | R | spatial interpretation | – | – | n/f |
| 20 | E | direct sum of EAs/EMs; irreducible | 6, 15 | tree `prodEffectAlgebra` | done |
| 21 | E | corner `pM`, `M ≅ pM ⊕ p^⊥M`, irreducible ⟺ no non-trivial idempotents | 15, 20 | OAP 12, 20, 21 | done in-house |
| 22 | D | comprehension | 9 | tree 199II `IsComprehension` | done (thin) |
| 23 | D | filter (= quotient for `p^⊥`) | 9 | tree 197II `IsQuotient` | done (new def + bridge) |
| 24 | E | standard comprehension/filter on `B(H)` | 22, 23 | not in tree | deferred (needs `B(H)` corners in `vNᵒᵖ` partial form) |
| 25 | R | comprehensions ⟺ kernels; cokernels ⟺ images + sharp filters | 22, 23 | tree 200III, 205II | done (thin, the halves the tree has) |
| 26 | R | `Pred_□`, chain of adjunctions `ξ ⊣ 0 ⊣ U ⊣ 1 ⊣ π` | 22, 23 | tree 198II, 198III, 199VI | done (thin) |
| 27 | P | filters epic, comprehensions monic, `1∘ξ = a`, comprehensions total | 22, 23 | tree 197V, 199VII, 202VIII | done (thin) |
| 28 | D | monoidal effectus | 9 | – | done |
| 29 | L | scalar multiplication facts | 28 | – | done (new proof) |

### §2.2 Directed completeness (Effectus.lean)

| # | k | content | deps | tree / external | status |
|---|---|---|---|---|---|
| 30 | D | directed-complete, normal effectus | 12 | – | done |
| 31 | E | Set normal; fd C* normal; vN dc | 30 | tree `Par (Type u)` | deferred (needs order transport along `set_pred_subset`; C*/vN parts need concrete partial-form effectuses) |
| 32 | E | complete Boolean algebra is a dc effect monoid | 16, 30 | – | done |
| 33 | E | `C(X,[0,1])` dc for extremally disconnected `X` | 18, 30 | Stone–Nakano; OAP | deferred (classical, not proved in the paper) |
| 34 | T | dc effect monoid `≅ B ⊕ C(X,[0,1])` | 20, 30 | **OAP 69** | done: `rec34_holds` (`Scalars.lean`, from OAP 69) |
| 35 | C | scalars of a dc effectus | 34 | – | done from 34 |
| 36 | T | irreducible dc effect monoid ∈ `{0}, {0,1}, [0,1]` | 34 | **OAP 71** | stated (Prop) |

### §2.3–2.5 Order unit spaces, Jordan algebras, SEAs (Algebras.lean)

| # | k | content | deps | tree / external | status |
|---|---|---|---|---|---|
| 37 | D | orthoalgebra, `OA` | 6 | – | done |
| 38 | P | `Pred(I)≅{0,1}` + state separation ⇒ orthoalgebras | 14, 37 | SIG (σ-version); in-house | done (in-house proof) |
| 39 | D | convex EA; `EA_c`, `DCEA_c` | 6 | tree 179II `EffectModule` over `I` | done (+ bridge to tree effect modules) |
| 40 | E | `[0,u]_V` convex; Gudder representation; Jacobs equivalence | 39 | tree cone/`Vec` construction; Gudder, Jacobs–Westerbaan–Westerbaan | done (Gudder part thin; categorical equivalence n/f) |
| 41 | D | OUS (norm, closed cone), Banach, dc; `DCOUS` | – | tree `OrderUnitSpace`, `ouGauge` (weaker: no Archimedean axiom) | done (`ousNorm`, `IsOUS`, `IsBanachOUS`, `IsDirectedCompleteOUS`) |
| 42 | P | `DCOUS ≃ DCEA_c` | 39, 41 | SIG 56 (σ-version only) + Wright | deferred (needs categories + Wright; SIG only has the σ-version) |
| 43 | P | `Pred(I)≅[0,1]` ⇒ predicate spaces convex | 17, 39 | SIG 25/27; tree `predEffectModule` | done |
| 44 | D | JB-algebra | 41 | – | done — **bilinearity added** (flag 15) |
| 45 | E | `𝔄_sa` is JB | 44 | Mathlib C*-algebras | deferred (C*-norm = order-unit norm, completeness) |
| 46 | E | EJA ⟺ fd JB; JvNW classification | 44 | tree `EuclideanJordanAlgebra`; JvNW | n/f (classification not used) |
| 47 | D | states of an OUS; normal; separating | 41 | – | done |
| 48 | D | JBW-algebra; `JBW_pc`, `JBW_npc` | 44, 47 | – | done |
| 49 | E | vN algebra sa part is JBW | 48 | tree `VonNeumannAlgebra` | deferred |
| 50 | D | JW-algebra | 48 | tree vN (ultraweak topology?) | done as injective normal Jordan hom (deviation, flag 16) |
| 51 | D | purely exceptional | 44 | – | done |
| 52 | T | JBW = JW ⊕ purely exceptional | 50, 51 | **Hanche-Olsen–Størmer 7.2.7** | deferred to Monoidal.lean (black box phrased at its use in 135) |
| 53 | D | hyperstonean | 47 | – | done |
| 54 | E | `C(X, M₃(𝕆)_sa)` purely exceptional | 51, 53 | Shultz; **no octonions in Mathlib** | n/f |
| 55 | T | purely exceptional ≅ `C(X, M₃(𝕆)_sa)` | 54 | **Shultz 1979** | deferred to Monoidal.lean (black box, see §1) |
| 56 | D | SEA, normal SEA | 6 | tree 225IV `SequentialEffectAlgebra` has a *weaker* axiom (e) | done (own class + `SEA.toTree`) |
| 57 | L | normal SEA: `⌈a⌉`, `⌊a⌋`, `b&a=a ⇒ b≥⌈a⌉` | 56 | **SEA** | stated (Prop, from SEA) |
| 58 | R | spectral theorem for normal SEAs | 56 | **SEA** | deferred (SEA spectral theorem; used from REC 119 on) |
| 59 | D | compressible | 39, 56 | – | done |
| 60 | D | quadratic | 56 | – | done |
| 61 | T | convex normal compressible quadratic SEA is JB | 59, 60, 44 | **van de Wetering 2018 Thm 4** | stated (black box `WeteringSequentialJB`) |

### §3 Pure maps and ⋄-adjointness (Effectus.lean)

| # | k | content | deps | tree / external | status |
|---|---|---|---|---|---|
| 62 | D | image | 9 | tree 202I `IsImage` | done (thin) |
| 63 | L | `im(f∘g) ≤ im f`, `=` for iso `g` | 62 | tree 202V `im_ineq` | done (paper's proof, typo noted) |
| 64 | D | sharp, `SPred` | 62 | tree 203I | done (thin) |
| 65 | D | floor, ceiling (well-defined) | 22, 62 | tree 203I.2 | done + well-definedness |
| 66 | P | floor/ceiling a)–f) | 63, 65 | tree 203IV, 203XII, 203XIII | done |
| 67 | D | ⋄-effectus | 23, 64 | tree 206II `DiamondEffectus` | done (+ bridge) |
| 68 | D | `f^⋄`, `f_⋄`, `f^□` (well-defined) | 66, 67 | tree `diaPull`, `diaPush`, `boxPull` | done + independence of the comprehension |
| 69 | P | Galois properties a)–h) | 66, 68 | tree 207II–207VI | done |
| 70 | D | ⋄-adjoint, ⋄-self-adjoint | 68 | tree 206II.1–2 | done (thin) |
| 71 | L | ⋄-adjointness symmetric | 69 | tree 209II.1 | done (paper's proof) |
| 72 | R | ⋄-adjoints not unique; rigidity | 70 | – | done (definition of rigid only) |
| 73 | E | vN conjugations ⋄-adjoint | 70 | not in tree | deferred |
| 74 | D | compatible filters and comprehensions | 22, 23, 64 | – | done |
| 75 | D | assert map of a sharp predicate; well-defined; idempotent; `1∘asrt_p = im asrt_p = p` | 74 | – | done |
| 76 | E | `asrt_P(A) = PAP` on `B(H)` | 75 | – | deferred (with 24) |
| 77 | L | `im f ≤ p ⟺ asrt_p∘f = f`; `1∘g ≤ p ⟺ g∘asrt_p = g` | 62, 75 | tree 211XV (in an &-effectus only) | done (paper's proof, weaker setting) |
| 78 | D | pure map | 22, 23 | tree 201II `IsPure` | done (+ bridge) |
| 79 | E | pure ⟺ Kraus rank 1 in vN | 78 | tree Dils (Paschke) partially | deferred |
| 80 | L | filters compose; comprehensions compose | 23, 22, 74 | tree 197IX; 211XI (&-effectus only) | done (part 2 needs the floor trick, see §4) |
| 81 | R | finite-dimensional reconstruction of vdW 2018 | – | external | n/f |
| 82 | L | sharp ⇒ ortho-sharp | 66, 67 | tree 208I | done |
| 83 | L | `p ∨ q` exists and is sharp; `SPred` ortholattice | 69, 82 | tree 204V, 208III, 208IX | done |
| 84 | P | `SPred` sub-EA and OML | 83 | tree 208III | done (thin) |
| 85 | D | `OMLatGal` | – | tree `OMLatGalCat` | done (thin) |
| 86 | P | functor `C → OMLatGal` | 69, 84 | tree 208VII | done (thin) |

### §4 Decomposing into sharp and convex systems (Decompose.lean, DecomposeFinite.lean)

| # | k | content | deps | external | status |
|---|---|---|---|---|---|
| 87 | P | non-trivial idempotent scalar ⇒ `Pred(C)` embeds into a product | 12, 15 | – | done (`rec87`): under-specified, rendered as `Pred(A) ≅ s·Pred(A) ⊕ s^⊥·Pred(A)` + faithfulness + non-triviality |
| 88 | D | idempotent; Karoubi envelope `Split(C)` | – | Mathlib `Karoubi` | done: `Split C` ≅ Mathlib `Karoubi C` (`splitEquivKaroubi`) |
| 89 | P | `Split(C)` is an effectus; preserves separation, monoidality | 88, 9, 13, 14, 28 | – | effectus + predicate bullet done; **state bullet FALSE** (refuted in Lean); monoidal bullet deferred (unused: REC 90 proved without it) |
| 90 | P | monoidal + non-trivial idempotent scalar ⇒ `Split(C) ≃ C_s × C_{s^⊥}` | 29, 89 | – | done (`rec90`, via `CentralSplitting.equivalence`) |
| 91 | P | ditto without splitting, given images + compatible filters/comprehensions | 77, 90 | – | done (`rec91`) |
| 92 | P | ditto from state/predicate separation | 77, 90 | OAP 20 (in-house) | done for states (`rec92_states`); predicates case with sharpness of `s∘1` as hypothesis (`rec92_predicates`; proof gap, flag 18) |
| 93 | P | dc + state separation ⇒ `Pred(A) ≅ OA ⊕ convex` | 35, 37, 39 | OAP 69 | done (`rec93`, `h34` = `rec34_holds`) |
| 94 | P | `Pred : C → OAᵒᵖ × DCOUSᵒᵖ` | 42, 93 | – | done into `OA × DCEA_c` (`rec94_functor`); `≅ DCOUS` = REC 42, deferred |
| 95 | P | `C ≃ C₁ × C₂` with `Pred` into `OAᵒᵖ` resp. `DCOUSᵒᵖ` | 92, 93, 42 | – | done into `OA`, `DCEA_c` (`rec95`, `rec95_oaFunctor`, `rec95_dcFunctor`); DCOUS part = REC 42 |
| 96 | L | orthoalgebra SEA is Boolean with `a&b = a∧b` | 37, 56 | SEA 44 | done (`rec96`; SEA 44 discharged) |
| 97 | P | normal-SEA predicate space `≅` complete BA ⊕ convex | 93, 96 | – | done (`rec97`; two omitted steps supplied, flag 19; normality unused) |
| 98 | D | finite tomography | 12 | – | done (`FiniteTomography`) |
| 99 | P | dc + finite tomography ⇒ `Pred(I) ≅ 𝒫(A) ⊕ [0,1]^n` | 34, 98 | – | **FALSE**: refuted (`rec99_false_as_printed`, `BoolMat`); corrected with "finitely many idempotent scalars", an iff (`rec99_corrected`, `rec99_corrected_converse`) |

### §5 The reconstruction (Reconstruction.lean)

| # | k | content | deps | external | status |
|---|---|---|---|---|---|
| 100 | D | sequential effectus | 14, 22, 23, 30, 56, 62, 70, 78 | – | deferred |
| 101 | R | remark on axiom 5 (CPM-like reformulation) | 100 | – | deferred (the reformulation is a claim: formalise as an iff) |
| 102 | T | **main**: `C ≃ C₁ × C₂`, CBA / dc JB | 95, 97, 106, 109, 121 | all of §1 except §6 items | deferred |
| 103 | T | **main**: irreducible scalars ⇒ CBA or JBW | 36, 102 | OAP 71 | deferred |
| 104 | R | JB vs JBW remark | – | – | n/f |
| 105 | P | `im asrt_p = ⌈p⌉`; sharp ⟺ idempotent; `p` sharp ⟺ `p^⊥` sharp | 57, 66, 100 | SEA | deferred |
| 106 | P | all maps have images | 57, 66, 105 | SEA (complete lattice of idempotents) | deferred |
| 107 | C | sequential ⇒ ⋄-effectus | 105, 106 | – | deferred |
| 108 | L | `asrt_p² = asrt_{p²}` | 100 | – | deferred |
| 109 | L | filters and comprehensions compatible; `π_p∘ξ^p = asrt_p` | 57, 108 | SEA | deferred |
| 110 | P | `π_p† = ξ^p` | 109 | – | deferred |
| 111 | C | `Θ† = Θ⁻¹` | 110 | – | deferred |
| 112 | P | sequential product compressible | 77, 109 | – | deferred |
| 113 | L | pure `f = π_{im f}∘Θ∘ξ^{⌈1∘f⌉}∘asrt_{1∘f}` | 69, 109 | – | deferred |
| 114 | P | `asrt_{p&q}² = asrt_p∘asrt_q²∘asrt_p` | 110, 111, 113 | – | deferred |
| 115 | C | quadratic | 114 | – | deferred |
| 116 | R | uniqueness of the dagger (unfinished in the source: `\TODO`) | – | – | n/f |
| 117 | D | order derivation | 41 | Mathlib `NormedSpace.exp` | deferred |
| 118 | P | A–S criterion | 117 | **Alfsen–Shultz, State spaces 1.108** | deferred (black box, unused) |
| 119 | L | `ω(a)=0 ⇒ ω(p&a)=ω(p^⊥&a)` | 112, 115, 58 | **vdW 2018 Prop 46 (unprinted)** | deferred |
| 120 | P | `D_p` is an order derivation | 119, 58 | **A–S (1.82)** | deferred; proof under-specified (see §4) |
| 121 | P | `V_A` is a JB-algebra | 120 | **A–S Geometry 9.48/9.43** | deferred (black box) |

### §6 Monoidal (Monoidal.lean)

| # | k | content | deps | external | status |
|---|---|---|---|---|---|
| 122 | D | monoidal sequential effectus | 28, 100 | – | deferred |
| 123 | P | `asrt_{a⊗b} = asrt_a ⊗ asrt_b` | 122 | vdW thesis 4.6.17 | deferred |
| 124 | C | `p⊗q` sharp | 123 | – | deferred |
| 125 | P | `T_{a⊗1} = T_a ⊗ id` | 123, 58 | SEA spectral | deferred |
| 126 | C | `a⊗1`, `1⊗b` operator commute | 125 | – | deferred |
| 127 | P | `a ↦ a⊗1` normal injective Jordan hom | 126 | – | deferred |
| 128 | P | `Q_{a⊗b} = Q_a ⊗ Q_b` | 123 | – | deferred |
| 129 | T | universal von Neumann algebra `W*(V)` | 48 | **H-O–S 7.1.9** | deferred (black box) |
| 130 | C | JW ⟺ `ψ` injective | 129 | – | deferred |
| 131 | D | symmetry; exchangeable | 48 | – | deferred |
| 132 | L | ≥4 exchangeable idempotents ⇒ JW | 131 | **A–S Geometry 4.4** | deferred (black box) |
| 133 | L | purely exceptional ⇒ 3 exchangeable idempotents | 55 | **Shultz + H-O–S 2.8.3** | deferred (black box, §1) |
| 134 | L | tensor of exchangeable pairs | 124, 128 | – | deferred |
| 135 | P | `V_A` is JW | 52, 127, 130, 132–134 | – | deferred |
| 136 | T | **main**: functor `C → JW_npcᵒᵖ` | 103, 135 | – | deferred |

## 4. Flags: false or under-specified as printed

1. **REC 7 is false as printed** (the same slip as OAP 2, from which it is copied).  With `x ⊥ y :⟺ x ∧ y = 0` and `x ⊻ y := x ∨ y` an
   orthomodular lattice is an effect algebra only if it is Boolean: in `MO2`
   (`0 < a, a^⊥, b, b^⊥ < 1`) both `a ⊻ a^⊥ = 1` and `a ⊻ b = 1`, so the
   orthosupplement of `a` is not unique.  The cited source (and thesis B 175II.4,
   and SEA 3) use `x ⊥ y :⟺ x ≤ y^⊥`.  The Boolean case (REC 16) is unaffected.
   Refuted in Lean: `rec7_as_printed_false`.
2. **REC 99 is false as printed** — refuted in Lean (`rec99_false_as_printed`):
   `BoolMat 𝒫(ℕ)` (`Kl(D_M)` on finite sets, `M = 𝒫(ℕ)`, built from scratch as an
   effectus in partial form) is directed complete with finite tomography (point
   predicates), but `Pred(I) = 𝒫(ℕ)` is not even order-isomorphic to
   `𝒫(A) × [0,1]^n`, `A` finite.  In fact finite tomography constrains nothing:
   every complete Boolean algebra is the scalars of such an effectus
   (`rec99_any_boolean_scalars`).  The proof's error: at `I` tomography is
   witnessed by `id_I` alone.  Corrected statement (`DecomposeFinite.lean`): the
   conclusion holds iff `Pred(I)` has finitely many idempotents.  ERRATA REC 99.
3. **REC 80, part 2**: stated for any comprehensions, proved only for comprehensions
   of *sharp* predicates (compatibility is only assumed for those).  Gap closes: a
   comprehension for `p` is a comprehension for `⌊p⌋` (proof of 66 b), which is sharp.
4. **REC 120**, proof (independent review `docs/research/review-rec120.md`, ERRATA
   "REC 120"): Theorem 102 is **true**; REC 120's printed step is broken for *all*
   scalars, not only `C(X,[0,1])`-valued ones — "take `ω' := asrt_p ∘ ω`" applies
   Lemma 119 to a *sub*state.  Local repair, covering both 102 and 103: use the total
   state `ω := π_q ∘ σ` for a state `σ` of `{A|q}`, then evaluate at a point of `X`.
   (Also `λ < ½‖δ‖` vs `λ < ½‖δ‖^{-1}`, and `p` is reused for a second idempotent.)
   Do **not** reorder to do 103 first.  Remaining risks for 102: Lemma 119 for
   `C(X)`-valued states (citation-only in the paper), and the exact hypotheses of the
   REC 121 Alfsen–Shultz black box — state it for Banach order unit spaces with a
   norm-dense set of sharp combinations, with no spectral duality / dual space assumed.
5. **REC 136**: `F(Pred(A)) ≅ [0,1]_{F(A)}` is ill-typed (`F` is a functor on `C`);
   meant `Pred(A) ≅ [0,1]_{F(A)}`.
6. **REC 87**: "embeds non-trivially into a product of categories" is under-specified.
7. **REC 69**: `SEff` is undefined (means `SPred`); in g) `f : A → B, g : B → C` but the
   composite written is `f ∘ g`; the proof of c) swaps `p` and `q`.
8. **REC 63**: the proof concludes `im f ≤ im(f∘g)`; the argument shows (and the
   statement says) `im(f∘g) ≤ im f`.
9. **REC 66**: "effectus with images and compressions" — meant comprehensions (also in
   the proof).
10. **REC 93**: `s₁` undefined (the idempotent is called `s`, and the convex action
    should use `s^⊥`).
11. **REC 102/103**: `JB_npc` is never defined (only `JBW_npc`); "CBA *of* JBW" typo;
    102 calls the predicate spaces JB-algebras (they are unit intervals of them).
12. **REC 29**: `s·p = s∘p` silently identifies `I ⊗ I` with `I` (a unitor); REC 28
    only asks biadditivity in the first variable (the second follows by symmetry).
13. **REC 38, 42** are cited to SIG, which proves only σ-versions; 38 is a 5-line
    in-house argument, 42 needs Wright's lemma.
14. **REC 56** vs the tree: thesis B's 225IV (tree `SequentialEffectAlgebra`) demands
    `a ⊥ b` for *both* conclusions of axiom (e); REC's (e) demands it only for
    `c | a ⊻ b`.  Not an erratum; REC needs its own class.
15. **REC 44** asks only for a "binary operation"; a JB-algebra is a Jordan
    *algebra*, so bilinearity is added in Lean (ERRATA REC 44).
16. **REC 50** (JW-algebra) is rendered as "injective normal Jordan homomorphism into
    the self-adjoint part of a (Kadison) von Neumann algebra" — equivalent to the
    printed "Jordan-isomorphic to an ultraweakly closed subset" for JBW-algebras
    (Hanche-Olsen–Størmer §4.4–4.5, not proved here); the tree has no ultraweak
    topology on an abstract von Neumann algebra.

17. **REC 89**, second bullet, **is false as printed** (refuted in Lean,
    `rec89_states_not_preserved`, `rec89_states_false_as_printed`): with an
    idempotent scalar `s ∉ {0,1}` the object `(I, s)` of `Split(C)` has no states but
    `id ≠ 0`, so `Split(C)` is never separated by states.  The printed "analogously"
    fails: the analogue of `p ∘ s` is the substate `t ∘ ω`.  Unused later.
18. **REC 92**, proof: takes `asrt_{s∘1}` without showing `s ∘ 1` sharp.  Proved
    under state separation (`isSharp_of_states`); from predicate separation alone no
    argument (gap, not refuted) — `rec92_predicates` assumes it.  REC 91's
    sharpness argument (image of `s · id`) needs the monoidal structure.
19. **REC 97**, proof: "`A_b` is a principal downset, so a SEA" needs `s ∘ 1`
    idempotent in the SEA of `Pred(A)` (true: REC 96's argument inside `Pred(A)`,
    `part_idem`), and completeness of the Boolean algebra is not argued (true: `A_b`
    is directed complete, `boolean_complete_of_dc`).  Normality of the SEA is not
    needed.  Not filed (a careful reader repairs both).
20. **REC 87** (flag 6): formalised as `Pred(A) ≅ s·Pred(A) ⊕ s^⊥·Pred(A)` (natural in
    `A`), faithfulness of `Pred(C) → C₁ × C₂`, non-triviality at `I` (`rec87`).

Items 1, 2 and 17 are the only ones that change what is true; 3, 4, 18, 19 are gaps
in proofs; the rest are typos/notation a careful reader repairs, or deviations of
the Lean.  Filed in `../papers/ERRATA.md`: REC 7, 44, 63, 69, 80, 89, 92, 99 (and
120, by the review).

## 5. Cost estimate

| file | new Lean lines | notes |
|---|---|---|
| Effectus.lean | ~2,000 (this phase) | mostly thin restatements + monoidal lemma + REC 7, 21, 75–80 |
| Algebras.lean | ~1,500 | definitions; 38, 43 short; 42 is the only real proof (~600) |
| Decompose.lean (+ DecomposeFinite, Scalars) | 3,100 (done) | as planned, plus the counterexample `BoolMat` (~450) and the REC 34 bridge |
| Reconstruction.lean | ~2,500 | 105–115 reuse tree &-/†-effectus patterns but in the paper's setting (~1,200); 117–121 functional analysis (~1,000) + black boxes; main theorems 102/103 (~300) |
| Monoidal.lean | ~1,800 | JBW tensor calculus; five black boxes |

Total ≈ 11,000 lines; §2–§4 done (≈ 8,000 with this session's 3,100); the critical
path is now Reconstruction (§5) → Monoidal (§6).  Main risks for 102 (flag 4): Lemma 119
for `C(X)`-valued states, and the exact hypotheses of the REC 121 black box.

## 6. Handover to §5 (written at the end of the §4 session, 2026-09-26)

What §5 (`Reconstruction.lean`, REC 100–121) can use from §4 — import
`Papers.REC.Decompose` and `Papers.REC.Scalars` once their oleans exist:

* **REC 34/35 are theorems now**: `rec34_holds : EffectMonoidDCClassification`
  (`Scalars.lean`, from `Papers.OAP.oap69`).  Pass it wherever a statement takes
  `h34`.  REC 36 (`IrreducibleDCClassification`, used by 103) is still a Prop;
  OAP 71 is in `Papers.OAP.Main` (`oap71_iso`) but stated for "no zero divisors",
  so a bridge irreducible → no zero divisors is needed (or: REC 34 + a connected
  extremally disconnected space is a point).
* **SEA 44 is a theorem**: `sea44_holds` (REC-SEA → `Papers.SEA.SEAlgebra` bridge:
  `SEA.toTree` plus `comm_seq`).  The same bridge gives access to the rest of
  `Papers.SEA` (REC 57's floor/ceiling, SEA 49–50/71, the spectral theorem) for
  REC 105–109, 119, 120 — check `Papers/SEA/*.lean` for built points before stating
  them as Props.
* **Splitting 102's `C ≃ C₁ × C₂`**: `rec95` gives `C ≌ (dcSplitting σs hsep).ε.Part ×
  (dcSplitting σs hsep).ε'.Part` (REC 92 at the Boolean idempotent of REC 93).  The
  parts are effectuses (`KCat` instances).  For 102 one needs the predicate spaces of
  `C₁` to be complete Boolean algebras: `rec97` proves it for `s · Pred(A)` inside
  `C`, and `partPredIso` identifies `Pred` of an object `(A, asrt)` of `C₁` with
  `s · Pred(A)`; transporting the Boolean algebra (and the SEA of REC 100 axiom 6)
  along `partPredIso` is *not* done yet.
* **Assert maps of `s ∘ 1`**: `asrtT`, `asrtT_pred` (`p ∘ asrt = s ∘ p`),
  `asrtT_substate` (`asrt ∘ ω = ω ∘ s`), `isSharp_of_states`, `asrtT_effObj`.
* **Instance pitfall** (cost an hour): for a part given by a *composite* term
  (`(dcSplitting σs hsep).ε.Part`), `Pred P` elaborates but instance search for
  `EffectAlgebra (Pred P)` inside generic lemmas (e.g. `EAIso.isOrthoalgebra`) can
  wander into `Karoubi C` and fail.  Work around by proving the needed consequence
  in a section where the part's data are variables (`partPred_isOrthoalgebra`,
  `partPred_directedComplete`, `partPredMap_id`) and applying it with explicit
  arguments.  `KCat`'s `Hom` is `Karoubi.Hom` (not Karoubi's `⟶`) for the same
  reason.
* **Generic tools**: `ExplicitCoproducts.finPAC_of` (build `FinPAC` from an explicit
  coproduct — reuse for any new concrete effectus); `KCat` (full subcategories of
  the Karoubi envelope with effect object `(I, e)`); `CentralSplitting.equivalence`;
  `EAIso` with transport of orthoalgebra / directed completeness / convexity.
* **Still open in §2–§4**: REC 89's monoidal bullet (monoidal structure on
  `Split C`; needs `MonoidalCategory` coherence on `KCat`, ~400 lines, not used by
  REC 90–136 as far as the plan shows), REC 42 (`DCEA_c ≅ DCOUS`, needs Wright's
  lemma) and hence the DCOUS halves of 94/95/97, REC 36 (see above), and the
  predicate-separated case of REC 92 without the sharpness hypothesis.
* **REC 100's "normal effectus separated by states"** is exactly the setting of
  `rec93`–`rec97` (dc + state separation), so 102's first steps are `rec95` +
  `rec97`; REC 103 adds irreducibility, where `s ∈ {0, 1}` and one factor of
  `rec95` is trivial.

