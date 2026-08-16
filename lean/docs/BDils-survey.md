# `B/Dils` survey — `SelfDual.lean` and `Pure.lean` (sessions 48–50)

Counts verified by `grep -cE '(^|[^`])\bsorry\b'` **and** by the compiler's
`declaration uses 'sorry'` warnings (they agree).

At session start: `SelfDual.lean` 21, `Pure.lean` 15, `Paschke.lean` 8,
`Kaplansky.lean` 5, `Stinespring.lean` 2, `SelfDualCompletion.lean` 2,
`HilbertModules.lean` 0 — **53**, exactly as the brief said.

At the end of session 48: `SelfDual.lean` **19**, `Pure.lean` **13**, rest
unchanged — **49**.

At the end of **session 49** (parsec 1600, see PROVING-LOG): `SelfDual.lean`
**14**, `Pure.lean` 13, `Paschke.lean` 8, `Kaplansky.lean` 5,
`Stinespring.lean` 2, `SelfDualCompletion.lean` 2, `HilbertModules.lean` 0 —
**44**, compiler-counted per file.

At the end of **session 50** (164II.1 and the 1660 parsec): `SelfDual.lean`
**11**, `Pure.lean` 13, `Paschke.lean` 8, `Kaplansky.lean` 5,
`Stinespring.lean` 2, `SelfDualCompletion.lean` 2, `HilbertModules.lean` 0 —
**41**, compiler-counted per file.

At the end of **session 51** (161II.2 and 164II.2a): `SelfDual.lean` **9**,
`Pure.lean` 13, `Paschke.lean` 8, `Kaplansky.lean` 5, `Stinespring.lean` 2,
`SelfDualCompletion.lean` 2, `HilbertModules.lean` 0 — **39**,
compiler-counted per file.

At the end of **session 52** (the `ExtTensor` witness): unchanged at
**39** — `SelfDual.lean` 9, `Pure.lean` 13, `Paschke.lean` 8,
`Kaplansky.lean` 5, `Stinespring.lean` 2, `SelfDualCompletion.lean` 2,
`HilbertModules.lean` 0, compiler-counted per file.  The session's output
is a new `def`, not a closed `sorry`.

Classification key: **(a)** self-contained, **(b)** blocked on a named
`sorry` elsewhere, **(c)** cited to the literature / another chapter,
**(d)** suspicious/false.

---

## `SelfDual.lean` — 21 items (9 open after session 51)

| DISP | name | class | note |
|---|---|---|---|
| 159IX | `ketbra_ultranorm_continuous` | **(b)** | **Reclassified session 50, was (a).**  Thesis proof 159X–159XI needs the operator-norm density of `span Ω` among np-functionals on `ℬᵃ(X)`, i.e. **90II**.2 `vn_center_separating_fundamental_2`, which is `sorry` at `A/VN/NormalFunctionals.lean:3343` (90II.1, line 3299, *is* proved).  Everything else in the proof is elementary |
| **160IV.2** | `hilbmod_projthm_2` | **(a)** | **CLOSED session 49** |
| **160IV.3** | `hilbmod_projthm_3` | **(a)** | **CLOSED session 49** — the keystone; done by running 149VIII's Zorn argument inside the submodule instead of extending a basis of `X` |
| **160IX** | `selfdual_orthn_basis` | **(a)** | **CLOSED session 49**; needed no Zorn, and the "ℓ²-sum convergence for a non-basis orthonormal family" is now `exists_unTendsto_of_l2Summable` in `HilbertModules.lean` |
| **160X** | `selfdual_gramschmidt` | **(a)** | **CLOSED session 49**, by induction on `n` with the polar decomposition as the orthonormalization step |
| **161II.1** | `hilbmod_el2_inner` | **(a)** | **CLOSED this session** (polarization, see log) |
| **161II.2** | `hilbmod_el2` | **(a)** | **CLOSED session 51**, and it cost ~90 lines, not "large": the statement never mentions the module `ℓ²((pᵢ))` (only the coordinate map), so nothing had to be constructed and `hX : SelfDual ℬ X` is not even used — the two convergence clauses of `IsONBasis` carry all three parts.  ⚠️ Our statement is therefore **weaker than the exercise**, which also asks for the right-ℬ-module structure on `ℓ²((pᵢ))` and its self-duality; neither is formalized anywhere |
| **161IV.2** | `onb1_el2` | **(a)** | **CLOSED this session** (direct bijection, see log); the brief's assumption that it needs 161II was wrong |
| 162II | `total_mv_order` | **(a)/(c)** | comparison of projections in a factor; proof 162III not converted.  Genuinely hard (Zorn + halving) |
| 162IV | `selfdual_normalish_form` | **(b)** | needs 162II and 161II.2 |
| 163II uniq | `selfdual_compl_defining_unique` | **(b)** | needs **151Ia** `selfdual_completion_univ` (`SelfDualCompletion.lean`, `sorry`) |
| **163II dense** | `selfdual_compl_defining_dense` | **(a)** | **CLOSED session 49**.  The survey's "needs 151Ia" was **wrong**: the statement takes the universal property as a hypothesis |
| 164II ex. | `univprop_ext_tensor` | **(a)/(b)** | the construction 164III–164VIII via `ℓ²((pᵢⱼ))`; the single biggest item in the file.  **Session 52**: the case `X = 𝒜`, `Y = ℬ` *is* proved, as `extTensorSelf` (see below); the general case still needs `ℓ²((pᵢⱼ))` as an actual Hilbert `𝒞`-module (our `L2Set` is a bare `Set (ι → ℬ)`), and the shortcut through the self-dual completion is blocked on **151I** `dils_completion` (`SelfDualCompletion.lean:81`, `sorry`).  Multi-session |
| **164II.1** | `ext_tensor_dense` | **(a)** | **CLOSED session 50.**  `P = id` from `exists_orthoProj` + `ExtTensor.univ` as in 163II-dense; the `bSpan D ⊆ unClosure D` gap is the thesis's own 164VII, and needs only *unbounded* ultrastrong density of `𝒜 ⊙ ℬ` (`IsVNTensor.generates` + `isVNSubalgebra_usClosureSubalgebra`) — **not** Kaplansky density, contrary to this row's earlier text |
| **164II.2a** | `ext_tensor_basis` | **(a)** | **CLOSED session 51** (~170 lines).  It needed 164II.1 but **not** 161II.2, contrary to this row's earlier text: the thesis's 164X reduces to a Parseval identity checked against product np-functionals only because its `X ⊗ Y` *is* `ℓ²((pᵢⱼ))`; for an abstract `E : ExtTensor` the cheaper route is 164II.1 + the 166III estimates with `s` chosen before `u` |
| 164II.2b | `ext_tensor_ketbra_dense` | **(b)/(d?)** | needs **159IX** `ketbra_ultranorm_continuous`, hence 90II.2 in `A/VN` — see below.  164II.2a is *not* the blocker any more |
| 165VI | `ba_ext_tensor_pres` | **(b)** | proof 165VII–165X; needs 164II.2b for the `generates` clause of `IsVNTensor`, plus 165IX/165X for `exists_productFunctional`/`separating`.  165III (its companion) *is* proved |
| **166IV** | `exttensor_dense_subsets` | **(a)** | **CLOSED session 50.**  The thesis's route through 158II `kaplansky_hilbmod` (open, printed proof false) is avoided: `u ∈ U` is chosen before `v ∈ V`, so no norm-bounded net is required |
| **166VI** | `dilationspace_dense_subset` | **(a)** | **CLOSED session 50**, together with the new public `paschke_tprod_dense` (the elementary tensors of `𝒜 ⊗_φ ℬ` are ultranorm dense — easier than 164II.1, since `{∑ aᵢ ⊗ bᵢ}` is already a ℬ-submodule) |
| 167I | `paschke_tensor` | **(b)** | needs 165VI + `existence_paschke` |
| 167I furth. | `paschke_tensor_module` | **(b)** | needs 167I |

**Bottom line for `B/Dils` after session 52.**  The non-vacuity question is
settled and no field is defective, so nothing that was proved has to be
revisited.  What is left in the directory is now dominated by **three
construction-sized roots**, none session-sized: **151I** `dils_completion`
(the self-dual completion, `SelfDualCompletion.lean:81`), on which both
`existence_paschke` and the general `univprop_ext_tensor` depend;
**90II**.2 in `A/VN`, on which 159IX and hence 164II.2b depend; and **158II**
`kaplansky_hilbmod`, open with a dead printed proof (QUESTIONS B10).  The
**next gate is 151I `dils_completion`** — it is the only one of the three
inside `B/Dils` and it unblocks the two largest remaining items at once.
A smaller, genuinely reachable target is **157IV.1**
`paschke_correspondence_mem` (`Paschke.lean:1099`): the thesis's argument is
"`√T ∈ ϱ(𝒜)^□`, so `φ_T(a) = h(√T ϱ(a) √T)` is ncp", and the pieces exist
(`ad_normal`/44VIII in `A/VN`, complete positivity of conjugation), but
conjugation as a bundled `NCPMap` on a von Neumann algebra has to be built
locally — `A/Proc`'s `adNCP` is off the import path (QUESTIONS **D3**).

**Bottom line for `SelfDual.lean` after session 51.**  The 1600 and 1610
parsecs are closed except 162II/162IV/163II-uniq, and the 1640 parsec is
down to the **existence** construction `univprop_ext_tensor` and
**164II.2b**.  The next gate is **164II.2b `ext_tensor_ketbra_dense`**, and
it is *not* self-contained: the thesis's 164XI replaces a general
`t ∈ 𝒜 ⊗ ℬ` in `|(eᵢ⊗dⱼ)t⟩⟨e_k⊗d_l|` by an ultrastrong limit from
`𝒜 ⊙ ℬ` and appeals to **159IX** `ketbra_ultranorm_continuous`, which is
`sorry` and blocked on **90II**.2 (`A/VN/NormalFunctionals.lean:3343`).
Two extra obstacles specific to our transcription: the approximating net is
forced to be indexed by `Finset (ι × κ)` (the thesis only claims "the span
is ultraweakly dense", with no net), and the ultraweak topology is not
metrizable, so a diagonal choice is not available either.  Everything else
of 164XI — `ketbra_ultraweakly_dense` (**159IV**, proved) applied to the
basis now supplied by 164II.2a, and `unDense_tSpan` — is already in the
file.

~~⚠️ **Non-vacuity gap.**~~ — **CLOSED session 52.**  `ExtTensor` **is
inhabited**, by the new `extTensorSelf` (`SelfDual.lean`, just below
`univprop_ext_tensor`): for *any* `ht : IsVNTensor t`, the algebra `𝒞`
itself — as a Hilbert `𝒞`-module over itself, with `η = t` — is an
`ExtTensor t ht 𝒜 ℬ`.  That is stronger than the `ℂ`-only check suggested
here, and it is literally the case `X = 𝒜`, `Y = ℬ` of
`univprop_ext_tensor`; it needs no von Neumann hypotheses.  Axiom-clean
(`propext, Classical.choice, Quot.sound`, checked from inside the module),
and `extTensorSelf _ vnTensor_mul_complex` gives the fully concrete
`ExtTensor (·*·) _ ℂ ℂ`, against which **164II.1 was checked to
elaborate**.  So 164II.1, 164II.2a/2b, 165III, 165VI, 166IV, 166VI and
167I are non-vacuous.

**Constructing it exposed no defect.**  Unlike `PaschkeModule` (session
14/43), every field of `ExtTensor` is mirrored correctly: `η_inner` reduces
to `IsVNTensor.star` then `.mul` over *non-commutative* `𝒜`, `ℬ`, so a star
in the wrong slot would not have typechecked.  The `univ` field needs no
density argument — `T' z := z · T(1,1)` is forced by `t 1 1 = 1` — and the
Gram-bound hypothesis on `T` is never used.

**Bottom line for `SelfDual.lean` after session 50.**  The 1600 parsec is
closed (160IV.1/.2/.3, 160IX, 160X) and so is the 1660 parsec (166II, 166IV,
166VI), together with 163II-dense and **164II.1**.  Of the remaining **11**,
the self-contained ones are **161II.2** `hilbmod_el2`, the **164II
existence** construction (both large) and **162II** `total_mv_order` (Zorn +
halving, genuinely hard); **159IX** is *not* self-contained — see its row.

~~**The next gate is 161II.2 `hilbmod_el2`**~~ — closed session 51.  For the
record, the costing above was wrong in two places: 164II.2a does **not**
need 161II.2, and the "polarisation of 160IX.2" for the inner-product clause
is unnecessary (148V `innerprod_ultraweak` on the two basis expansions gives
it directly).  The `ceil` lemma prediction was right: it is
`ceil_star_mul_self_le_iff`, which already existed in the file (private,
written for 161IV.2) and only had to be moved above 161II.2.

Reusable output of sessions 49–50 (all `private` in `SelfDual.lean` unless
noted): `exists_orthogonal_decomp` / `exists_orthoProj` (the projection
theorem for *any* ultranorm-closed ℬ-submodule, and the projection as a
bounded module map); `tSpan` / `tSpanSubalg` / `unDense_tSpan` (`𝒜 ⊙ ℬ` as a
`*`-subalgebra of `𝒜 ⊗ ℬ`, ultrastrongly dense);
`unSeminorm_op_smul_le` (`‖c·z‖_ω ≤ ‖z‖‖c‖_ω`);
`unSeminorm_eta_le_left/_right` (the 166III estimates);
`unSeminorm_tprod_left/_right` and `exists_conj_comp_np` for the Paschke
module; and the **public** `paschke_tprod_dense`.

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
| 170IV.1 | `surjective_nmiu_1` | **(d)** | **Reclassified session 52.**  Our statement omits the thesis's "between von Neumann algebras" (dils.tex:6223); `section Pure` binds only `[CStarAlgebra A]`.  So the 69IV route below — and the author's own 69II route — is unavailable, both needing `[VonNeumannAlgebra A]`.  QUESTIONS **D5** |
| 170IV.2 | `surjective_nmiu_2` | **(b)/(d)** | converse; needs 169IV (the standard corner `h_z`), *and* has the same missing von Neumann hypothesis — QUESTIONS **D5** |
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

### ~~New lead: 170IV.1 `surjective_nmiu_1` is now unblocked~~ — WITHDRAWN (session 52)

**The lead below is dead as our statement stands.**  `surjective_nmiu_1`
carries no `[VonNeumannAlgebra A]`, and `carrier_miu` (69IV) — like 69II —
needs it.  See QUESTIONS **D5**; if the hypothesis is restored, the costing
below applies unchanged.

### The (withdrawn) lead, kept for after D5 is ruled on

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
