# `B/Dils` survey — `SelfDual.lean` and `Pure.lean` (session 48)

Counts verified by `grep -cE '(^|[^`])\bsorry\b'` **and** by the compiler's
`declaration uses 'sorry'` warnings (they agree).

At session start: `SelfDual.lean` 21, `Pure.lean` 15, `Paschke.lean` 8,
`Kaplansky.lean` 5, `Stinespring.lean` 2, `SelfDualCompletion.lean` 2,
`HilbertModules.lean` 0 — **53**, exactly as the brief said.

At session end: `SelfDual.lean` **19**, `Pure.lean` **13**, rest unchanged —
**49**.

Classification key: **(a)** self-contained, **(b)** blocked on a named
`sorry` elsewhere, **(c)** cited to the literature / another chapter,
**(d)** suspicious/false.

---

## `SelfDual.lean` — 21 items

| DISP | name | class | note |
|---|---|---|---|
| 159IX | `ketbra_ultranorm_continuous` | **(a)** | thesis proof is 159X–159XI, present but "not converted"; self-contained, medium-large |
| 160IV.2 | `hilbmod_projthm_2` | **(a)** | proof 160V–160VIII; needs `V^⊥⊥` = un-closure of `bSpan V`.  160IV.1 is *proved* in file |
| 160IV.3 | `hilbmod_projthm_3` | **(a)** | same proof block; the orthogonal decomposition.  **This is the keystone of the 1600 parsec** — 160IX(⇐) and 160X wait only on it |
| 160IX | `selfdual_orthn_basis` | **(b)** | ⇐ half needs 160IV.3; ⇒ half needs ℓ²-sum convergence for a non-basis orthonormal family, which the tree does not yet have separately |
| 160X | `selfdual_gramschmidt` | **(b)** | needs 160IX + polar decomposition in a self-dual module |
| **161II.1** | `hilbmod_el2_inner` | **(a)** | **CLOSED this session** (polarization, see log) |
| 161II.2 | `hilbmod_el2` | **(a)** | large: `ℓ²((pᵢ))` self dual + coordinate map is a bijection.  Now that 161II.1 is closed the inner product exists, so this is the natural next target in this parsec |
| **161IV.2** | `onb1_el2` | **(a)** | **CLOSED this session** (direct bijection, see log); the brief's assumption that it needs 161II was wrong |
| 162II | `total_mv_order` | **(a)/(c)** | comparison of projections in a factor; proof 162III not converted.  Genuinely hard (Zorn + halving) |
| 162IV | `selfdual_normalish_form` | **(b)** | needs 162II and 161II.2 |
| 163II uniq | `selfdual_compl_defining_unique` | **(b)** | needs **151Ia** `selfdual_completion_univ` (`SelfDualCompletion.lean`, `sorry`) |
| 163II dense | `selfdual_compl_defining_dense` | **(b)** | same, plus 160IV.3 |
| 164II ex. | `univprop_ext_tensor` | **(a)** | the construction 164III–164VIII via `ℓ²((pᵢⱼ))`; the single biggest item in the file, and 161II.2 is a prerequisite in practice |
| 164II.1 | `ext_tensor_dense` | **(b)** | density is **not** a field of `ExtTensor`, so it must come from `univ`; that route needs 160IV.3.  Checked: nothing in file derives it |
| 164II.2a | `ext_tensor_basis` | **(b)** | needs 164II.1 and 161II.2 |
| 164II.2b | `ext_tensor_ketbra_dense` | **(b)** | needs 164II.2a |
| 165VI | `ba_ext_tensor_pres` | **(b)** | proof 165VII–165X; needs 164II.2b.  165III (its companion) *is* proved |
| 166IV | `exttensor_dense_subsets` | **(b)** | needs 164II.1; 166II (the other half of the parsec) is proved |
| 166VI | `dilationspace_dense_subset` | **(b)** | needs 166IV |
| 167I | `paschke_tensor` | **(b)** | needs 165VI + `existence_paschke` |
| 167I furth. | `paschke_tensor_module` | **(b)** | needs 167I |

**Bottom line for `SelfDual.lean`.**  Only *five* of the 21 were (a) at
session start: 159IX, 160IV.2, 160IV.3, 161II.1, 161IV.2 (plus 161II.2 and
164II existence, which are (a) but very large).  Two of those five are now
closed.  **160IV.3 is the highest-value remaining target**: it is the direct
blocker of 160IX, 160X, 163II-dense and 164II.1, and 164II.1 in turn gates
165VI → 166IV → 166VI → 167I — i.e. *eleven* of the file's remaining
nineteen sorries sit downstream of the 1600-parsec projection theorem.

---

## `Pure.lean` — 15 items

| DISP | name | class | note |
|---|---|---|---|
| 169IV | `standard_corner_dils` | **(c)** | cited to proc.tex 98I/95II; the universal property of `b ↦ ⌊a⌋b⌊a⌋` has to be built from scratch (`A/Proc` is off this import path) |
| 169V | `h_is_corner_for_unital_map` | **(b)** | the author's proof works with the *standard* dilation of `existence_paschke` (`Paschke.lean`, `sorry`) |
| 169X | `dils_stand_filter` | **(c)** | cited to proc.tex 96V — which **is** now proved in `A/Proc/Measurement.lean` (session 47) but is not importable here.  Proving it locally means redoing 96V |
| **169XI.1** | `dils_filter_basics_1` | **(a)** | **CLOSED this session** |
| 169XI.2a | `dils_filter_basics_2a` | **(d)** | false under the transcribed `c 1 ≤ b`; QUESTIONS **B11**, left `sorry` per the brief |
| **169XI.2b** | `dils_filter_basics_2b` | **(a)** | **CLOSED this session**, from 169XI.1.  Note it does **not** depend on 2a, and so is not affected by B11 |
| 170II.1 | `dils_examples_pure_1` | **(b)** | `ad_T` classification of pure maps `B(H) → B(K)`; needs 171VII and the Stinespring block |
| 170II.2 | `dils_examples_pure_2` | **(b)** | the thesis derives it from 169V + 169XI.2; 169V is `sorry` and 169XI.2**a** is the false half |
| 170IV.1 | `surjective_nmiu_1` | **(a)**, newly | see "New lead" below |
| 170IV.2 | `surjective_nmiu_2` | **(b)** | converse; needs 169IV (the standard corner `h_z`) |
| 171II | `paschke_corner` | **(b)** | three-step proof through `existence_paschke` |
| 171VII | `paschke_pure` | **(b)** | needs 171II |
| 172III | `ncp_extreme_paschke` | **(b)** | needs `paschke_correspondence_*` (three `sorry`s in `Paschke.lean`) and 170II.2 |
| 172X | `pure_ncp_extreme` | **(b)** | needs 172III + 171II + 169XI |
| 172XII | `ncp_extreme_comp` | **(b)** | the thesis gives **no proof at all** (a Corollary with no proof point); the intended one is φ = h ∘ ϱ from `existence_paschke`, ϱ ncp-extreme by 172VIII (proved) and h ncp-extreme by 172X |

**Bottom line for `Pure.lean`.**  This file is *not* volume: 13 of its 15
were blocked, essentially all on three roots — `existence_paschke`
(`Paschke.lean`), 169IV `standard_corner_dils`, and 169X `dils_stand_filter`.
The two genuinely reachable items were 169XI.1 and 169XI.2b, and both are now
closed.  **A worker sent at `Pure.lean` for volume will find nothing**; the
return is in `Paschke.lean`'s `existence_paschke` and in re-deriving proc.tex
96V/98I locally (or putting `A/Proc` on the import path — QUESTIONS **D3**).

### New lead: 170IV.1 `surjective_nmiu_1` is now unblocked

The author's solution routes the kernel of a surjective nmiu-map through
`kernel-ultraweak-twosided-ideal-dils` and **69II**
`prop:weakly-closed-ideal` — and 69II is still `sorry`
(`A/VN/Projections.lean:4384`).  But **69IV `carrier_miu` is proved**
(`A/VN/Projections.lean:4399`) and delivers exactly what is needed without
69II: for an nmiu-map `f`, the carrier `z := ⌈f⌉` is **central**, and
`f a = 0 ↔ z·a = 0`.  So the central projection with `ker ϱ = (1−z)A` is
available directly.

What remains is real but routine: for `f : A → C` ncp with `f(z) = f(1)`,
show `f((1−z)x) = 0` — Kadison–Schwarz (`ncp_cp_cs`, proved) gives
`f(w)f(w)* ≤ ‖f 1‖·f(ww*)` with `w = (1−z)x = x(1−z)` by centrality, and
`ww* = (1−z)xx*(1−z) ≤ ‖x‖²(1−z)`, whose image is `0` — and then build the
factorisation `f'` as an `NCPMap` on `B` along the bijection `A/ker ϱ ≅ B`.
Estimated 200–250 lines, most of it the `NCPMap` bundle.  Note 170IV.**2**
stays blocked on 169IV regardless.
