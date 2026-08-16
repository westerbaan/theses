# `Theses/A/Proc/` — full survey of the remaining `sorry`s (worker 71, 2026-08-16)

**Headline count correction: A/Proc has 113 code `sorry`s, not ~120.**
Per file after this session: `Tensor` 43, `Measurement` **36** (was 38),
`QuantumLambda` 17, `Duplicators` 17.  (`grep -c sorry` gives 45/38/20/17
because the file docstrings mention `sorry` in prose; the code counts are the
ones above.  Session 41 already reported 115.)

## Classification summary

| class | count | share |
|---|---|---|
| (c) **vacuous band** — statement mentions `VNT`/`⊗ᵥ`/`Duplicator`, hence depends on `sorryAx` through **111XII**; can never be closed axiom-cleanly until 111XII is | **54** | 47% |
| (b) blocked on a *named* `sorry` outside A/Proc | **50** | 44% |
| (a) self-contained / reachable now | **5** | 4% |
| (c′) cited to literature, no thesis argument at all | **1** | 1% |
| (d) suspicious | **0 new** (3 already-known false statements are recorded and realigned) | |
| closed this session | **2** (99XI, 106III.1) | |

The two blockers that gate almost everything:

* **89IX `normal_functional`** (`A/VN/NormalFunctionals.lean:1727`, `sorry`) —
  gates **111VII** `special_tensor`, hence **111XII**, hence the whole
  54-statement vacuous band.  48VIII `ngns` (the other input to 111XII) **is
  proved**, so 89IX is the *only* thing between A/Proc and un-vacuuming 47% of
  the chapter.  **This is by a wide margin the highest-leverage item for
  A/Proc, and it is in A/VN, not here.**
* **81VI `sequential-douglas` / 81VII `div-approx` / 81IX `div-usc`**
  (`A/VN/Division.lean`, all three `sorry`) — gate **96V `canonical_filter`**,
  which gates essentially all of `Measurement.lean` (parsecs 960–1060).

## (a) Reachable now

| DISP | decl | file:line | note |
|---|---|---|---|
| **99XI** | `filter_of_projection_multiplicative` | Measurement 2601 | **CLOSED this session** |
| **106III**.1 | `sequential_product_counterexample_1` | Measurement ~4281 | **CLOSED this session** — was unblocked by the new `isFilter_cornerIncl`: axiom (B) needs `⌈p⌉(·)⌈p⌉` to be *pure*, which is `corner ; filter` with the filter being the corner inclusion of a projection.  (C) collapses to `⌈p⌉q⌈p⌉ = ⌈p⌉q⌈p⌉`, (D) is `q := p`, (E) reduces to `e₁⌈p⌉e₂ = 0` being star-symmetric (no contraposition theory needed), and ¬(A) needs `⌈½·1⌉ = 1 ≠ ½·1`. |
| **98II**.2 | `filter_basic_2` | Measurement 2018 | **two of the three conjuncts are directly provable** — see "the near miss" below |
| **124I** | `vn_generation_bound` | QuantumLambda 678 | pure cardinal arithmetic on `wstar S`; no thesis proof, no dependency on anything sorried |
| **125II** | `vn_gns_bound` | QuantumLambda 729 | `ngns` + a cardinality count of the GNS direct sum; `ngns` is proved |
| **129X** | `continuous_finite_measure_space_not_duplicable` | Duplicators 725 | `Duplicable A` is the hypothesis (not the conclusion) so the statement is *not* `VNT`-tainted in a way that blocks a proof by contradiction; but its proof (proc.tex:6363) does use the duplicator's `δ`, so treat as (b) until checked |

### The near miss: 98II.2 `filter_basic_2`

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

## (c) The vacuous band — 54 statements behind 111XII

Their *types* mention `VNT 𝒜 ℬ = (vnTensor 𝒜 ℬ).carrier`, and `vnTensor` is
`Nonempty.some` of the sorried `vnTensorProduct_nonempty`.  Nothing in this
band can be `#print axioms`-clean until 111XII is.

* `Tensor.lean` (32): 111VII `special_tensor`, 111XII ×2, 115II ×2
  (`exists_tmap`, `tensor_functorial`), 115IV ×2, 115V, 116I ×2, 116III.1/.2/.4/.5,
  116IV.1/.2, 117III, 118II ×2, 118IV.1/.4/.5/.6, 119II, 119IV, 119IVb, 119IVc,
  `exists_tmapM`, 119V ×5.  (`tensor_simple_facts_3` and `product_functional_norm`
  are tainted too — via `predualTensor`, itself chosen from a sorried existence.)
* `QuantumLambda.lean` (13): 121II, 123II.1/.2, 125IV, 125VI, 125VIIb, 125VIII,
  125bII, 125cIII, 125dII, 125eIIa, 125eIII, 125eVII.
* `Duplicators.lean` (9): 127III (uniqueness), 127VI, 128VIII, 128XI, 132III.2/.3/.4,
  132IV, 132VI.

## (b) Blocked, with the named blocker

### `Measurement.lean` (parsecs 960–1060) — all 36 rooted at 96V

`96V canonical_filter` (proc.tex:414) needs `sequential-douglas` (81VI),
`div-usc` (81IX) and `div-approx` (81VII), all `sorry` in
`A/VN/Division.lean`.  Everything below then follows the thesis's own
dependency chain:

| DISP | decl | blocked on |
|---|---|---|
| 96V | `canonical_filter` | **81VI, 81VII, 81IX** (A/VN) |
| 98II.1 | `filter_basic_1` | 96V (needs `c_p` to *be* a filter) |
| 98II.2 | `filter_basic_2` | see "near miss" above — only the ℂ-gadget |
| 98II.3 | `filter_basic_3` (bipositivity) | 96V / 81VI |
| 98III | `filters_composition` | 98II.3 (to get `g 1 ≤ c 1` back through `d`) |
| 98VI | `corners_composition` | the exercise's own hint inequality; 98IV/98V are proved, so this one is *closer* than the rest — worth a second look |
| 98VII, 98VII-formula | `filter_corner`, `filter_corner_formula` | 98II.1 + 96V |
| 98IX | `exists_sqBracket`, `square_f` | 98VII |
| 100II.3 | `isPure_adSelf` | 96V (`a*(·)a = canonicalFilter a ∘ π_{⌈a⌉ᵣ}`) |
| 100III | `pure_fundamental` | 98II, 98III, 98VI, 98IX |
| 100VII.1/.2/.3 | `special_pure_maps_*` | 100III |
| 102VII | `canonical_quotient_rigid` | 96V (80IV and 45VI, its other inputs, **are** proved) |
| 102IX | `pure_is_rigid` | 98IX + 102VII + 100III |
| 103II.1/.2 | `purely_positive_examples_*` | 100II.3 (purity half); 101VII.1 half is proved |
| 104III.2a | `centrally_similar_basic_2a` | **parked: false as printed**, ERRATA row exists |
| 104III.3/.4/.5 | `centrally_similar_basic_*` | 81V `douglas` / 81VIII `sequential-quotient` (A/VN, `sorry`) |
| 104VII | `positive_quotients_centrally_similar` | 104III.4/.5 (80IV is now proved — correction to w46 §7) |
| 104IX | `faithful_positive_map_uniqueness` | 100VII + 104VII |
| 105III.1-2/.4 | `chevron_f_basic_*` | 98IX (`chevron` is defined from `[f]`) |
| 105IV.1/.3 | `chevron_f_purely_positive_*` | 103II + 105III |
| 105V ×2, 105VII | `positive_map_uniqueness*`, `sqrt_axiom` | 104IX + 105IV |
| 106I ×2 | `uniqueness_sequential_product*` | 105V (and purity for axiom B) |
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
| 112XI | `tensor_universal_property` | **77V** `vn_extension` (A/VN, `sorry`) |
| 114I | `tensor_universal_property_extra` | 112XI |
| 114II | `tensor_uniqueness` | 112XI |
| 116VII | `tensor_characterization` | 112X + 116IV |

### `QuantumLambda.lean` — the 4 untainted ones

| DISP | decl | note |
|---|---|---|
| 123I.3 | `linf_tensor` | reachable in principle (checking `IsTensorProduct` for `ℓ^∞(X) × ℓ^∞(Y) → ℓ^∞(X×Y)`); needs the centre-separating clause, i.e. 116VII-style work.  Exercise, no author argument. |
| 124I | `vn_generation_bound` | (a) — cardinal count |
| 124III | `second_adjunction` | needs 124I + 125II + a Zorn/limit construction; Theorem with a full proof at proc.tex:4718 |
| 125II | `vn_gns_bound` | (a) — `ngns` is proved |

### `Duplicators.lean` — the 8 untainted ones

| DISP | decl | blocked on |
|---|---|---|
| 127III | `duplicable` (main equivalence) | 128VIII/128XI (tainted) |
| 128XIII | `duplicable_product` | `Duplicable` hypothesis ⇒ 111XII |
| 129X | `continuous_finite_measure_space_not_duplicable` | uses the duplicator's `δ` ⇒ 111XII |
| 130IV | `measure_space_partition` | the missing componentwise description of `spectralOrder` on `lp ℬ ∞` (same mathematics as `vonNeumannAlgebra_lp_infty`, now discharged — **recheck**, this may have opened) |
| 130V | `discrete_ell_x` | 130IV |
| 132III.1 | `dup_vna_is_monoid_1` | `Duplicator` ⇒ 111XII |
| 132III.5 | `dup_vna_is_monoid_5` | 132III.2–.4 |
| 132VI | `exists_freeMonoidUnitCpsu` | the missing componentwise positivity of `CStarMatrix n (lp …)` (w66 §132VI) |

## (c′) Cited to literature

* **121II** `intersection_tensor` — proc.tex:4450 cites Takesaki IV.5.10 and gives
  no argument.  (Also in the vacuous band.)

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
