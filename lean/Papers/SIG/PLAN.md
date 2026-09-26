# SIG — formalisation plan

K. Cho, B. Westerbaan, J. van de Wetering, *Dichotomy between deterministic
and probabilistic models in countably additive effectus theory*, QPL 2020
(arXiv:2003.10245).  Source `../papers/2003.10245/main.tex`, index
`../papers/SIG-points.csv` (76 points).  Namespace `Papers.SIG`.

## Numbering caveat (flag for the indexer)

`index.py` counts every theorem-like environment, but three of them sit inside
`\begin{Auxproof}`, which `settings.tex` gobbles (`\hideauxproof`): **51**
(`ex:notBoolean`), **63** (`lem:pam-equiv`) and **64**
(`lem:charact-eff-sigma`) are **not printed**, and do not advance the printed
counter.  So index number *n* is printed as *n* for n ≤ 50, *n − 1* for
52 ≤ n ≤ 62, and *n − 3* for n ≥ 65 (e.g. index 65 `lem:charact-sigma-effectus`
is the printed "Lemma 62"; index 40 `thm:normalisation-equiv` is printed
Theorem 40).  We cite index numbers (the project convention); the audit note
of a row ≥ 52 gives the printed number too.  The hidden proofs inside
`Auxproof` are author-written but unprinted: we may use them as guidance, and
say so.

## Design

* **PCMs** are the tree's `Theses.B.Eff.PCM` (174II, Perp-relation style);
  SIG 1 is the same definition (Kleene associativity; the tree has one
  direction as an axiom and `PCM.assoc_left` for the other).  *Additive* maps
  (SIG 1: `f 0 = 0` and preservation of `⊕`) are a new predicate, since the
  tree's `PCMHom` omits `f 0 = 0`.
* **σ-PAMs** (SIG 2) are a new class `SigmaPAM`: a partial sum on families
  `J → M` indexed by countable `J : Type` (universe 0 — every countable index
  set is in bijection with one there); partition-associativity is stated for
  the fibres of an arbitrary map `p : J → K` (so blocks may be empty — this is
  what makes the empty sum `0` exist, and it is Arbib–Manes' reading);
  the unary axiom for every one-element index type.  The note after SIG 2
  ("every σ-PAM is a PCM") is `SigmaPAM.toPCM`, a def, with the PCM axioms
  proved from the three σ-PAM axioms.
* **σ-PACs / σ-effectuses** (SIG 5, 12): a σ-effectus is a new class
  `SigmaEffectus C` over `[HasCountableCoproducts C] [∀ X Y, SigmaPAM (X ⟶ Y)]`
  whose fields are the printed axioms (σ-biadditive composition, countable
  compatible-sum, binary untying, the effect-algebra structure of `C(A, I)`
  and effectus conditions (ii), (iii)), with `C(A,B)`'s PCM the one derived
  from its σ-PAM (instance `homPCM`).  From it we *derive* the tree's
  `FinPAC C` and `EffectusPartialForm C` instances, so every σ-effectus is a
  tree effectus in partial form and `Pred`, `Scal`, `Substate`, `Stat`,
  `IsTotal`, `effPair`, `scalEffectMonoid`, … apply unchanged.  (The paper's
  finPAC and effectus in partial form, SIG 5 and 12, are literally the tree's
  `FinPAC` and `EffectusPartialForm`, 180VII.)
* **σ-effect algebras** (SIG 17) are effect algebras whose `≼`-order is
  ω-complete (`OmegaComplete`), with the canonical countable sum
  `IsCSum x s` ("`s` is the supremum of the finite partial sums") as a
  relation, not as a second σ-PAM instance (which would clash with the
  derived PCM).
* **Effect monoids** are the tree's `EffectMonoid` (178II), whose
  distributivity axiom is the four-term expansion; SIG 21 phrases it as
  biadditivity; the two are proved equivalent.
* **OAP**: SIG 41 and 43 are OAP's Theorems 54 and 71, not importable this
  session.  They enter as explicit hypotheses (`Prop`-valued statements
  `OAP54`, `OAP71` in our file), recorded "waits on OAP 54/71".

## Status (2026-09-26, end of phase 1)

Rows in `docs/audit/papers-sig.csv` for 48 of the 76 points: 1–13, 16–31,
33–45, 65–70; axiom-clean, no `sorry`.  Of these, 6, 11, 16, 27, 35 are
remarks/pointers (module docs, no declaration), 41 and 43 are OAP's theorems
stated as `Prop`s and used as hypotheses (waits on OAP 68/71), and 65 is not
formalised (66 and 68 are proved without it) — so **42 points carry proved
declarations**,
plus the unnumbered claim after SIG 17 (the canonical σ-PAM of a σ-effect
algebra, `canonicalSigmaPAM`).  Partial: 23 (the "ω-complete iff basically
disconnected" clause cited), 26 (σ-version unstated), 28, 29, 33, 34 (σ-case
only — the finite effectus `EMod[M]ᵒᵖ`, `WMod[M]` not built).  Open: 14, 15,
32, 46–64 except 65, 71–76.

Files written (each compiles; files importing a new file were checked by
compiling the concatenation, since `lean1.sh` writes no olean):
`Prelim` (737 lines), `SigmaEffectus` (1146), `Normalisation` (428),
`Classification` (197), `EffectModules` (1205), `WeightModules` (930).
The plan below had `Modules.lean`; it became `EffectModules.lean` +
`WeightModules.lean`.

Next (phase 2), in order of value:
* `Pfn.lean` (14, 22-Pfn, 32, 47, 49): Pfn = Mathlib `PartialFun`; hom sums
  via `pointwiseSigmaPAM` over a disjoint-support σ-PAM on `Part Y`
  (summable iff domains pairwise disjoint); coproducts `Σ j, X j`;
  `I = PUnit`.  47: `X ↦ {x // x ≠ 0}` is full, faithful, essentially surjective
  (preimage `Part S` with the same σ-PAM).  48 directly: `F A = {ω ≠ 0}`.
* `Convex.lean` (52–62, 71–76): the tree has `OrderUnit` mixins and the GP
  representation `effectModule_unitInterval_representation`.
* finite halves of 28/29/33/34.

## Files (in import order)

| file | points | est. lines |
|---|---|---|
| `Prelim.lean` | 1–11 (§2) | 900 |
| `SigmaEffectus.lean` | 12, 13, 16–23 (§3.0–3.1) | 1,600 |
| `Normalisation.lean` | 36, 38–40 (§4) | 900 |
| `Modules.lean` | 24–35, 63–70 (§3.2, App. A) | 2,500 (may split `Modules/Effect`, `Modules/Weight`) |
| `Pfn.lean` | 14, 22 (`Pfn` part), 32, 47, 49 | 1,200 |
| `Classification.lean` | 41–46, 48, 50, 51 (§5.0–5.1) | 700 |
| `Convex.lean` | 52–62, 71–76 (§5.2, App. C) | 2,500 |
| `WStar.lean` | 15, 23 (`W*` part) | XL, last |

## Points

Cost: S ≤ 50 lines, M ≤ 250, L ≤ 800, XL more or needing a large external
theory.  "tree" = `Theses/B/Eff/*`.

| # | kind | content | file | deps | cost | notes |
|---|---|---|---|---|---|---|
| 1 | Def | PCM; additive, biadditive maps | Prelim | tree 174II `PCM` | S | tree's `PCMHom` lacks `f 0 = 0`: new `IsAdditive` |
| 2 | Def | σ-PAM; σ-additive, σ-biadditive; note: σ-PAM ⇒ PCM | Prelim | 1 | M | new `SigmaPAM`; `SigmaPAM.toPCM` |
| 3 | Def | category enriched over PCMs / σ-PAMs | Prelim | 1, 2 | S | |
| 4 | Def | partial projections of a coproduct; compatible family | Prelim | 3 | S | zero maps = a family `Zero (X ⟶ Y)` |
| 5 | Def | finPAC; σ-PAC | Prelim | 3, 4 | M | finPAC = tree `FinPAC` (180VII); σ-PAC new |
| 6 | Remark | PACs characterised by coproducts + zero maps | Prelim | — | — | cites [Cho19 §3.8.1], [AM80 §5]; no Lean content (its countable case is SIG 62) |
| 7 | Def | effect algebra; category `EA` of additive maps | Prelim | 1 | S | tree `EffectAlgebra` (175I); `EA` with *additive* (subunital) maps is new |
| 8 | Example | Boolean algebra is an EA | Prelim | 7 | S | tree `booleanEffectAlgebra`; state the printed `⊥`/`⊕` |
| 9 | Example | effects of `B(H)` form an EA | Prelim | 7 | S | tree `effectsEffectAlgebra` at `H →L[ℂ] H` |
| 10 | Remark | EA morphisms subunital | Prelim | 7 | S | `f 1 ≼ 1` for additive `f` |
| 11 | Remark | EA ≅ Eilenberg–Moore of OMP/bounded posets | — | — | XL | cites Harding, Jenča; not formalised (row says so) |
| 12 | Def | effectus (partial form); σ-effectus; morphism of (σ-)effectuses; predicates, substates, total maps, states, scalars | SigmaEffectus | 5, 7 | M | effectus = tree 180VII; `SigmaEffectus` new; derived tree instances |
| 13 | Remark | operational reading; tests | SigmaEffectus | 12 | S | `IsTest` def |
| 14 | Example | `Pfn` is a σ-effectus; `St X ≅ X`, `Pred X ≅ 𝒫 X`, `Tot Pfn ≅ Set` | Pfn | 12 | L | build coproducts (Σ-types) and disjoint-domain sums by hand |
| 15 | Example | `W*ᵒᵖ` is a σ-effectus | WStar | 12, tree `VNExamples` | XL | ultraweak sums; last |
| 16 | Remark | partial vs total form | SigmaEffectus | tree Cho's theorem | S | pointer to tree `eff_partial_to_total`; σ-total form open (no claim) |
| 17 | Def | σ-effect algebra (ω-complete EA); canonical countable sums | SigmaEffectus | 7 | M | `OmegaComplete`, `IsCSum`, existence of canonical sums |
| 18 | Prop | EA + σ-PAM extending its PCM ⇒ ω-complete, sums canonical | SigmaEffectus | 2, 17 | L | printed proof; "extends" = binary sums agree |
| 19 | Cor | `Pred A` of a σ-effectus is a σ-EA | SigmaEffectus | 12, 18 | S | |
| 20 | Lemma | additive map between σ-EAs: σ-additive ⇔ ω-continuous | SigmaEffectus | 17 | M | no printed proof ("straightforwardly verifiable") |
| 21 | Def | (σ-)effect monoid (biadditive product); opposite monoid | SigmaEffectus | 17, tree 178II | M | equivalence with tree's four-term distributivity; unnumbered claim after it = OAP 43 |
| 22 | Example | `{0,1}`, Boolean algebras, ω-complete BAs are (σ-)effect monoids; scalars of `Pfn` | SigmaEffectus (+Pfn) | 21, 14 | M | |
| 23 | Example | `[0,1]` σ-effect monoid; `[0,1]_{C(X)}` effect monoid; ω-complete iff basically disconnected | SigmaEffectus (+WStar) | 21 | M / XL | the "iff" cites Gillman–Jerison 1H, 3N.5: XL, not attempted in phase 1 |
| 24 | Def | (σ-)effect `M`-module; categories `EMod[M]`, `sEMod[M]` (subunital maps) | Modules | 21, tree 179II | M | tree `EModCat` has *unital* maps: new category |
| 25 | Example | `Pred A` is a (σ-)effect module over the scalars | Modules | 12, 24 | S | tree `predEffectModule` + σ part |
| 26 | Example | effect `{0,1}`-module = effect algebra | Modules | 24 | S | tree `effectModuleBool` + uniqueness |
| 27 | Example | effect `[0,1]`-module = convex EA = interval of an ordered vector space | Modules | 24 | M | tree `orderIntervalEffectModule`, `Vec` construction |
| 28 | Prop | `EMod[M]ᵒᵖ` effectus, `sEMod[M]ᵒᵖ` σ-effectus | Modules | 24, 65, 66 | L | finite case cites [Cho19 3.4.10]: prove both |
| 29 | Prop | `Pred : C → (s)EMod[M]ᵒᵖ` morphism of (σ-)effectuses | Modules | 28, 67 | L | |
| 30 | Def | (σ-)weight `M`-module; `WMod[M]`, `sWMod[M]` | Modules | 21 | M | |
| 31 | Example | substates form a (σ-)weight `Mᵒᵖ`-module | Modules | 12, 30 | M | |
| 32 | Example | weight `{0,1}`-modules = pointed sets; `WMod ≅ sWMod ≅ pSet` | Pfn | 30 | M | |
| 33 | Prop | `WMod[M]` effectus, `sWMod[M]` σ-effectus | Modules | 30, 65, 68 | L | |
| 34 | Prop | `sSt : C → (s)WMod[Mᵒᵖ]` morphism of (σ-)effectuses | Modules | 33, 69, 70 | L | |
| 35 | Remark | convex-set analogues open | — | — | — | open question; no claim |
| 36 | Def | predicate-/substate-separated | Normalisation | 12 | S | predicate-separated = tree `SeparatingPredicates` |
| 37 | Prop | separated ⇔ `Pred` / `sSt` faithful | Modules | 29, 34, 36 | S | "immediate"; needs the functors |
| 38 | Def | normalisation; (state-separated, in text) | Normalisation | 12 | S | |
| 39 | Prop | with normalisation: state-sep ⇔ substate-sep | Normalisation | 36, 38 | S | printed proof |
| 40 | Thm | σ-effectus: normalisation ⇔ division ⇔ no zero divisors ⇔ nonzero scalars epi | Normalisation | 12, 38, 69-free | L | (i)⇒(ii) cites [Cho15 6.4]: our own proof via `effPair`; (iii)⇒(i) cites [MA86 3.2.24] for summability of `ω ∘ sⁿ`: we reformulate (finite partial sums + limit axiom) |
| 41 | Thm | ω-complete effect monoid ↪ BA ⊕ `[0,1]_{C(X)}` | Classification | OAP 54 | — | statement only, as hypothesis `OAP54`; waits on OAP 54 |
| 42 | Cor | scalars of a σ-effectus commute | Classification | 19, 41 | M | from hypothesis 41; needs `C(X)` effect monoid, direct sum |
| 43 | Thm | ω-complete, no zero divisors ⇒ `{0}`, `{0,1}` or `[0,1]` | Classification | OAP 71 | — | hypothesis `OAP71`; waits on OAP 71 |
| 44 | Thm | normalisation ⇔ scalars ≅ `{0}`, `{0,1}`, `[0,1]` | Classification | 19, 40, 43 | M | |
| 45 | Prop | scalars `{0}` ⇒ trivial category | Classification | 12 | S | printed proof |
| 46 | Example | `sEA ≅ sEMod[{0,1}]`; Kochen–Specker makes `St(P(H)) = ∅` | Classification | 24, 28 | XL | KS not in Mathlib: the isomorphism part only (M); KS part cited |
| 47 | Prop | `sWMod[{0,1}] ≃ Pfn`, morphism of σ-effectuses | Pfn | 14, 32, 33 | L | |
| 48 | Thm | substate-sep. σ-effectus with scalars `{0,1}` embeds faithfully in `Pfn`; `St A ≅ F A` | Classification | 34, 37, 47 | M | |
| 49 | Prop | contravariant powerset `Pfn → ωBAᵒᵖ` faithful σ-morphism | Pfn | 14 | L | needs `ωBAᵒᵖ` σ-effectus (unnumbered claim) |
| 50 | Thm | … embeds in `ωBAᵒᵖ`; `Pred A` orthoalgebra (text) | Classification | 48, 49 | M | |
| 51 | Example | 6-element non-Boolean sub-EA of `𝒫{1,2,3,4}` | Classification | 7 | S | **hidden (Auxproof)**; cheap by `decide` |
| 52 | Def | order unit; `OVSu` (subunital positive maps) | Convex | — | S | tree `OrderUnit` has mixins; printed no. 51 |
| 53 | Prop | `OVSu ≃ EMod[[0,1]]` | Convex | 24, 52 | L | cites JacobsMF Thm 14; tree has `Vec` representation (EffectAlgebras 3827ff.) |
| 54 | Def | order-unit space, order-unit norm, Banach OUS | Convex | 52 | S | |
| 55 | Def | monotone σ-complete; σ-normal; `sBOUS` | Convex | 54 | S | |
| 56 | Prop | `sBOUS ≃ sEMod[[0,1]]` | Convex | 53, 72–75 | L | printed proof in App. C |
| 57 | Thm | predicate-sep. σ-effectus with scalars `[0,1]` ↪ `sBOUSᵒᵖ` | Convex | 29, 37, 56 | M | |
| 58 | Def | ordered vector space with trace; `OVSt`; subbase; cancellative; `CWMod`; base norm; (Banach) pre-base-norm space; σ-closed subbase; `sBBNS`, `sCWMod` | Convex | 30 | M | defs in text after 58 too |
| 59 | Prop | `sBase : OVSt ≃ CWMod[[0,1]]` | Convex | 58 | L | proof sketched (refers to [Cho19 §7.2.1]) |
| 60 | Prop | `sBBNS ≃ sCWMod[[0,1]]` | Convex | 59, 76 | L | |
| 61 | Thm | state-sep. σ-effectus, scalars `[0,1]`, cancellative substates ↪ `sBBNS` | Convex | 34, 37, 39, 60 | M | |
| 62 | Remark | predicate-separation ⇒ cancellative substates | Convex | 36 | S | no printed proof; easy |
| 63 | Lemma | weak partition-associativity suffices | Prelim | 2 | M | **hidden (Auxproof)** |
| 64 | Lemma | effectus + (countable coproducts, jointly monic projections, finite⇒countable compatibility) ⇔ σ-effectus | Modules | 12, 63 | L | **hidden (Auxproof)** |
| 65 | Lemma | characterisation of σ-effectuses by (i)–(viii) | Modules | 12 | L | printed 62; proof cites [Cho19 3.8.6, 7.3.38] "not hard to verify": we prove |
| 66 | Prop | `sEMod[M]ᵒᵖ` σ-effectus | Modules | 65 | L | printed 63 |
| 67 | Prop | `Pred` morphism of σ-effectuses | Modules | 66 | M | printed 64 |
| 68 | Prop | `sWMod[M]` σ-effectus | Modules | 65 | L | printed 65 |
| 69 | Lemma | maps into `∐ B_λ` ↔ families with summable truths | Modules | 12 | M | printed 66; "same manner as finite case"; needs countable version of effectus axiom (iii), derivable from binary (iii) + limit axiom |
| 70 | Prop | `sSt` morphism of σ-effectuses | Modules | 68, 69 | M | printed 67 |
| 71 | Lemma | `⋁ 2^{-N} aₙ = 2^{-N} ⋁ aₙ` in ω-complete effect `[0,1]`-modules | Convex | 24 | S | printed 68 |
| 72 | Lemma | OVS with order unit monotone σ-complete ⇔ `[0,u]` ω-complete | Convex | 71 | M | printed 69 |
| 73 | Lemma | σ-normal ⇔ restriction ω-continuous | Convex | 72 | M | printed 70; proof hidden (Auxproof) |
| 74 | Lemma | monotone σ-complete OVS with unit is Banach OUS | Convex | 54 | L | printed 71; cites Wright 1972 Lemmas 1.1–1.2 |
| 75 | Lemma | ω-complete effect `[0,1]`-module is a σ-effect module | Convex | 20, 53, 72, 74 | M | printed 72 |
| 76 | Lemma | subbase a σ-weight module ⇒ Banach pre-base-norm space, sums = series | Convex | 58 | L | printed 73; uses Furber Cor 2.2.5 (`τ x = ‖x‖` on the cone): prove |

## Flags (possible defects, under-specification)

* **Numbering**: see the caveat above (index ≠ print from 52 on).
* **SIG 2** does not say whether partition blocks may be empty.  With
  non-empty blocks only, nothing forces the empty family to be summable, so
  "`0 = ⋁∅`" (the note after SIG 2) would not follow; we allow empty blocks.
* **SIG 4**: "category with zero morphisms" — we use a family of chosen zeros
  (`Zero (X ⟶ Y)`), which in every use is the PCM zero.
* **SIG 12**: condition (iii) is binary even for σ-effectuses; SIG 66 (and
  the iteration in SIG 40) need its countable form, which follows from the
  binary one, PCM associativity and the limit axiom — the paper does not say so.
* **SIG 18**: "a σ-PAM structure that extends the PCM structure": we read
  "the PCM derived from the σ-PAM is `E`'s", i.e. binary sums agree.
* **SIG 23**: "`[0,1]_{C(X)}` is ω-complete iff `X` is basically
  disconnected": cited (Gillman–Jerison), not proved in the paper.
* **SIG 40 (iii)⇒(i)** relies on Manes–Arbib's iteration theorem for the
  existence of `⋁ ω ∘ sⁿ`; direct argument available (above).
* **SIG 46**: Kochen–Specker; out of reach, cited.
