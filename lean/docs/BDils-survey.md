# `B/Dils` survey — `SelfDual.lean` and `Pure.lean` (sessions 48–53)

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

At the end of **session 53** (D5 implemented; 170IV.1 and 157IV.1):
`SelfDual.lean` 9, `Pure.lean` **12**, `Paschke.lean` **7**,
`Kaplansky.lean` 5, `Stinespring.lean` 2, `SelfDualCompletion.lean` 2,
`HilbertModules.lean` 0 — **37**, compiler-counted per file.

At the end of **session 54** (159IX, and 164II.2b refuted):
`SelfDual.lean` **8**, `Pure.lean` 12, `Paschke.lean` 7,
`Kaplansky.lean` 5, `Stinespring.lean` 2, `SelfDualCompletion.lean` 2,
`HilbertModules.lean` 0 — **36**, compiler-counted per file.

At the end of **session 55** (151Ia, and 163II-uniq with it):
`SelfDual.lean` **7**, `Pure.lean` 12, `Paschke.lean` 7,
`Kaplansky.lean` 5, `Stinespring.lean` 2, `SelfDualCompletion.lean` **1**,
`HilbertModules.lean` 0 — **34**, compiler-counted per file.

At the end of **session 57** (158II `kaplansky_hilbmod`, through the linking
algebra): `Kaplansky.lean` **4**, rest unchanged — **33**.

At the end of **session 58** (138VIII-findim; 150II costed, not closed):
`SelfDual.lean` 7, `Pure.lean` 12, `Paschke.lean` 7, `Kaplansky.lean` 4,
`Stinespring.lean` **1**, `SelfDualCompletion.lean` 1,
`HilbertModules.lean` 0 — **32**, compiler-counted per file (each source run
through `lean` individually).

At the end of **session 59** (150II phase 1: the ultranorm uniformity and
`V̄`; no `sorry` closed by design): `SelfDual.lean` 7, `Pure.lean` 12,
`Paschke.lean` 7, `Kaplansky.lean` 4, `Stinespring.lean` 1,
`SelfDualCompletion.lean` 1, `HilbertModules.lean` 0 — **32**,
compiler-counted per file (each source run through `lean` individually).

At the end of **session 60** (150II phase 2: the σ-closure and its inner
product; again no `sorry` closed by design): `SelfDual.lean` 7, `Pure.lean`
12, `Paschke.lean` 7, `Kaplansky.lean` 4, `Stinespring.lean` 1,
`SelfDualCompletion.lean` 1, `HilbertModules.lean` 0 — **32**,
compiler-counted per file (each source run through `lean` individually).

At the end of **session 61** (**150II `dils_completion` is proved**;
`SelfDualCompletion.lean` is finished): `SelfDual.lean` 7, `Pure.lean` 12,
`Paschke.lean` 7, `Kaplansky.lean` 4, `Stinespring.lean` 1,
`SelfDualCompletion.lean` **0**, `HilbertModules.lean` 0 — **31**,
compiler-counted per file (each source run through `lean` individually, and
each checked for *errors* as well as `sorry`s — see the regression noted in
the session-61 section below).

Classification key: **(a)** self-contained, **(b)** blocked on a named
`sorry` elsewhere, **(c)** cited to the literature / another chapter,
**(d)** suspicious/false.

---

## `SelfDual.lean` — 21 items (9 open after session 51)

| DISP | name | class | note |
|---|---|---|---|
| **159IX** | `ketbra_ultranorm_continuous` | **(a)** | **CLOSED session 54**, ~110 lines, once A/VN's **90II**.2 landed.  `Ω = {f⟨x,(·)x⟩}` is `baVecNP`, already in `SelfDualCompletion.lean`; centre-separation of `Ω` is `ba_nonneg_iff` + `np_faithful` at `b = 1`; 90II.2 is fed `S = 𝒷ᵃ(X)` and its `ωₖ(sₖ*(·)sₖ)` read back as the vector functional of `sₖxₖ`.  ⚠️ The thesis's preparatory estimate `‖\|z⟩⟨y\|‖ ≤ ‖z‖‖y‖` (159X, proved there from order separation) is **not needed**: it is already the bound with which `mketbra` is defined |
| **160IV.2** | `hilbmod_projthm_2` | **(a)** | **CLOSED session 49** |
| **160IV.3** | `hilbmod_projthm_3` | **(a)** | **CLOSED session 49** — the keystone; done by running 149VIII's Zorn argument inside the submodule instead of extending a basis of `X` |
| **160IX** | `selfdual_orthn_basis` | **(a)** | **CLOSED session 49**; needed no Zorn, and the "ℓ²-sum convergence for a non-basis orthonormal family" is now `exists_unTendsto_of_l2Summable` in `HilbertModules.lean` |
| **160X** | `selfdual_gramschmidt` | **(a)** | **CLOSED session 49**, by induction on `n` with the polar decomposition as the orthonormalization step |
| **161II.1** | `hilbmod_el2_inner` | **(a)** | **CLOSED this session** (polarization, see log) |
| **161II.2** | `hilbmod_el2` | **(a)** | **CLOSED session 51**, and it cost ~90 lines, not "large": the statement never mentions the module `ℓ²((pᵢ))` (only the coordinate map), so nothing had to be constructed and `hX : SelfDual ℬ X` is not even used — the two convergence clauses of `IsONBasis` carry all three parts.  ⚠️ Our statement is therefore **weaker than the exercise**, which also asks for the right-ℬ-module structure on `ℓ²((pᵢ))` and its self-duality; neither is formalized anywhere |
| **161IV.2** | `onb1_el2` | **(a)** | **CLOSED this session** (direct bijection, see log); the brief's assumption that it needs 161II was wrong |
| 162II | `total_mv_order` | **(a)/(c)** | comparison of projections in a factor; proof 162III not converted.  Genuinely hard (Zorn + halving) |
| 162IV | `selfdual_normalish_form` | **(b)** | needs 162II and 161II.2 |
| **163II uniq** | `selfdual_compl_defining_unique` | **(a)** | **CLOSED session 55**, ~110 lines, immediately after 151Ia: apply 151Ia four times (`E₁→E₂`, `E₂→E₁`, and once on each `Eᵢ` for the uniqueness clause, which identifies `W∘U` and `U∘W` with the identity).  ⚠️ For the inner-product clause we do **not** re-run the thesis's density argument: `U` is bundled as a CLM, **152VIII** gives `U*`, and `U*U` and `id` have equal vector states on `η₁V`, so **152IX**.2 `hilmod_fixed_on_V_eq` closes it |
| **163II dense** | `selfdual_compl_defining_dense` | **(a)** | **CLOSED session 49**.  The survey's "needs 151Ia" was **wrong**: the statement takes the universal property as a hypothesis |
| 164II ex. | `univprop_ext_tensor` | **(a)/(b)** | the construction 164III–164VIII via `ℓ²((pᵢⱼ))`; the single biggest item in the file.  **Session 52**: the case `X = 𝒜`, `Y = ℬ` *is* proved, as `extTensorSelf` (see below); the general case still needs `ℓ²((pᵢⱼ))` as an actual Hilbert `𝒞`-module (our `L2Set` is a bare `Set (ι → ℬ)`), and the shortcut through the self-dual completion is blocked on **151I** `dils_completion` (`SelfDualCompletion.lean:81`, `sorry`).  Multi-session |
| **164II.1** | `ext_tensor_dense` | **(a)** | **CLOSED session 50.**  `P = id` from `exists_orthoProj` + `ExtTensor.univ` as in 163II-dense; the `bSpan D ⊆ unClosure D` gap is the thesis's own 164VII, and needs only *unbounded* ultrastrong density of `𝒜 ⊙ ℬ` (`IsVNTensor.generates` + `isVNSubalgebra_usClosureSubalgebra`) — **not** Kaplansky density, contrary to this row's earlier text |
| **164II.2a** | `ext_tensor_basis` | **(a)** | **CLOSED session 51** (~170 lines).  It needed 164II.1 but **not** 161II.2, contrary to this row's earlier text: the thesis's 164X reduces to a Parseval identity checked against product np-functionals only because its `X ⊗ Y` *is* `ℓ²((pᵢⱼ))`; for an abstract `E : ExtTensor` the cheaper route is 164II.1 + the 166III estimates with `s` chosen before `u` |
| 164II.2b | `ext_tensor_ketbra_dense` | **(d)** | **FALSE as transcribed** (session 54, QUESTIONS **D6**): our statement forces a `Finset (ι × κ)`-indexed net along `atTop`, and at `ι = κ = PUnit` (`X = 𝒜`, `Y = ℬ`, `E = extTensorSelf`) `atTop` is principal at the top element, so the net's value there would have to *equal* `T` — forcing `𝒜 ⊗ ℬ = 𝒜 ⊙ ℬ`.  The thesis claims only ultraweak **density** of `span D`, and *that* **is proved**, as the new public `ext_tensor_ketbra_uwDense` (entourage form), by the thesis's own 164XI: 159IV + 164II.2a + Kaplansky 74IV + 159IX.  Left `sorry` per the never-change-a-statement rule |
| 165VI | `ba_ext_tensor_pres` | **(b)** | proof 165VII–165X.  `generates` is supplied by `ext_tensor_ketbra_uwDense`, and the miu-clauses by 165III (proved).  ⚠️ **This row previously said "what is left is 165IX/165X" — that is wrong** (session 55): 165IX/165X give product functionals only for the *vector states* `Ω_X`, `Ω_Y` and then appeal to **116VII** `tensor-characterization`, whereas our `IsVNTensor.exists_productFunctional` transcribes proc.tex's `tensor` literally and demands one for **every** pair of np-functionals.  `tensor_characterization` (`A/Proc/Tensor.lean:3848`) is itself `sorry` **and** off this import path, so 165VI is blocked *outside* `B/Dils` |
| **166IV** | `exttensor_dense_subsets` | **(a)** | **CLOSED session 50.**  The thesis's route through 158II `kaplansky_hilbmod` (open, printed proof false) is avoided: `u ∈ U` is chosen before `v ∈ V`, so no norm-bounded net is required |
| **166VI** | `dilationspace_dense_subset` | **(a)** | **CLOSED session 50**, together with the new public `paschke_tprod_dense` (the elementary tensors of `𝒜 ⊗_φ ℬ` are ultranorm dense — easier than 164II.1, since `{∑ aᵢ ⊗ bᵢ}` is already a ℬ-submodule) |
| 167I | `paschke_tensor` | **(b)** | needs 165VI + `existence_paschke` |
| 167I furth. | `paschke_tensor_module` | **(b)** | needs 167I |

**Bottom line for `B/Dils` after session 54.**  159IX is closed and 164II.2b
is **dead as transcribed** (D6), so the 1640 parsec is finished apart from the
`univprop_ext_tensor` construction.  `existence_paschke` was inspected once
more against dils.tex:3600 (**154IV**–**154V**) and is blocked on **two**
roots, not one: it builds `𝒜 ⊙ ℬ` with the φ-inner product, completes it with
**150II** `dils_completion`, and gets its universal property from **151Ia**
`selfdual_completion_univ` — *both* `sorry` in `SelfDualCompletion.lean`.
Costed:

* the `𝒜 ⊙ ℬ` inner-product space (Mathlib `TensorProduct` + positivity of the
  Gram form `∑ᵢⱼ bᵢ* φ(aᵢ* αⱼ) βⱼ` from complete positivity of `φ` — the
  conjugated-sum manipulations in `PhiCompatible.mul_right` are the model):
  ~250 lines;
* **151Ia** `selfdual_completion_univ` (`SelfDualCompletion.lean:94`) — extend
  a bounded module map along an ultranorm-dense inner-product-preserving `η`,
  by ultranorm limits.  **Not blocked**: it takes the completion as a
  hypothesis, and ultranorm completeness of a self-dual module is already in
  the tree (`unComplete_of_isONBasis`, the TFAE at `HilbertModules.lean:3492`).
  ~300–400 lines, and it is the *reachable* piece of the plan;
* **150II** `dils_completion` (`SelfDualCompletion.lean:79`) — the type
  construction, 150III–150XV, fast nets + transfinite induction.  Multi-session;
* `ϱ`, `h` and their nmiu/ncp clauses on top: ~300 lines.

**So the next gate is 151Ia `selfdual_completion_univ`**, not
`existence_paschke`: it is the only unblocked link in that chain, it also
unblocks 163II-uniq `selfdual_compl_defining_unique`, and the thesis uses it
for `univprop_ext_tensor` too.

**Bottom line for `B/Dils` after session 53.**  The non-vacuity question is
settled and no field is defective, so nothing that was proved has to be
revisited.  What is left in the directory is dominated by **three
construction-sized roots**, none session-sized: **150II** `dils_completion`
(the self-dual completion, `SelfDualCompletion.lean:81` — sessions 52 and
the brief for 53 both called this "151I", which is wrong: 151Ia is
`selfdual_completion_univ`, the *universal property*, on the next screen),
on which both **154III** `existence_paschke` and the general
`univprop_ext_tensor` depend; **90II**.2 in `A/VN`, on which 159IX and hence
164II.2b depend; and **158II** `kaplansky_hilbmod`, open with a dead printed
proof (QUESTIONS B10).  150II is the only one of the three inside `B/Dils`,
but it is a *type-construction* — a completion carrying `NormedAddCommGroup`,
`CStarModule`, `CompleteSpace` and self-duality, built in the thesis
(150III–150XV) from fast nets and a transfinite induction on compatible
extensions.  It is not a session-sized item and was not attempted.

The **next gate is therefore `existence_paschke`** (**154III**,
`Paschke.lean:425`), which sits between 150II and everything else: 157IV.2
and 157IV.3, 171II `paschke_corner`, and — through 171II — most of
`Pure.lean`.

~~A smaller, genuinely reachable target is **157IV.1**~~ — **CLOSED session
53** (`Paschke.lean`).  The costing was right: the thesis's 157VI argument
("`√T ∈ ϱ(𝒜)^□`, so `φ_T(a) = h(√T ϱ(a) √T)` is ncp") transcribes directly,
and conjugation as a bundled `NCPMap` had to be built locally, from
`ad_cp_1`/**34V**.1 and `ad_normal`/**44VIII**, together with a local copy of
the ncp-composition helper (`Stinespring.lean` and `Pure.lean` both have one,
both `private`).  ⚠️ Note the *thesis* proves 157IV only for the concrete
dilation `𝒜 ⊗_φ ℬ` and transfers to an arbitrary one at 157IX through
`paschke-unique-up-to-iso`; **part 1 needs none of that** — the Set-up
argument is model-independent, and our proof uses only `hD.1` (`φ = h ∘ ϱ`).
Parts 2 (⇒) and 3 are *not* model-independent: 157VII/157VIII compute inside
`𝒜 ⊗_φ ℬ` with `hilmod-fixed-on-V`, so both stay blocked on
`existence_paschke`.

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
| **170IV.1** | `surjective_nmiu_1` | **(a)** | **CLOSED session 53**, once D5 was ruled on and `[VonNeumannAlgebra A] [VonNeumannAlgebra B]` restored (the fix really was local to the two signatures).  ~150 lines by the costing below, and the estimate held |
| 170IV.2 | `surjective_nmiu_2` | **(b)** | converse; the von Neumann binders are restored (D5 done), but it still needs **169IV** — the standard corner `h_z` — *and* the thesis's `iso` (an ncp-isomorphism of von Neumann algebras is nmiu), which the tree does not have either |
| 171II | `paschke_corner` | **(b)** | three-step proof through `existence_paschke` |
| 171VII | `paschke_pure` | **(b)** | needs 171II |
| 172III | `ncp_extreme_paschke` | **(b)** | needs `paschke_correspondence_*` (three `sorry`s in `Paschke.lean`) and 170II.2 |
| 172X | `pure_ncp_extreme` | **(b)** | needs 172III + 171II + 169XI |
| 172XII | `ncp_extreme_comp` | **(b)** | the thesis gives **no proof at all** (a Corollary with no proof point); the intended one is φ = h ∘ ϱ from `existence_paschke`, ϱ ncp-extreme by 172VIII (proved) and h ncp-extreme by 172X |

**Bottom line for `Pure.lean` after session 53.**  This file is *not* volume:
12 of its 15 are blocked, essentially all on three roots — `existence_paschke`
(`Paschke.lean`), 169IV `standard_corner_dils`, and 169X `dils_stand_filter`.
The genuinely reachable items were 169XI.1, 169XI.2b and (after D5) 170IV.1,
and all three are now closed.  **A worker sent at `Pure.lean` for volume will
find nothing**; the return is in `Paschke.lean`'s `existence_paschke` and in
re-deriving proc.tex 96V/98I locally (or putting `A/Proc` on the import path
— QUESTIONS **D3**).

### 170IV.1 `surjective_nmiu_1` — CLOSED session 53

D5 was ruled on ("fix transcription"), `[VonNeumannAlgebra A]
[VonNeumannAlgebra B]` were added to both halves of 170IV, and the change
really was local to the two signatures: nothing consumes them, and the only
other edit was the doc comments.

The route costed in session 52 is the one that worked, and the ~200-line
estimate was right (~150 lines).  For the record, since it is reusable:

* The author's solution routes `ker ϱ` through
  `kernel-ultraweak-twosided-ideal-dils` and **69II**
  `prop:weakly-closed-ideal`, which is still `sorry`
  (`A/VN/Projections.lean:4504`).  **69IV `carrier_miu` is proved** and
  delivers what is needed without 69II: for an nmiu-map `f`, `z := ⌈f⌉` is
  **central** and `f a = 0 ↔ z·a = 0` (we use it in the equivalent
  `nmiu_factors` form, `f a = f b ↔ z·a = z·b`).  **Divergence from the
  thesis, logged**: the author's 69II route is not taken.
* The section `σ : B → A` of `ϱ` (the inverse of `ϱ' : zA → B`, which the
  solution builds as a subtype) is built here as a *function* `B → A`,
  `σ(ϱ a) = z·a`, well defined by 69IV.  This avoids the corner algebra
  entirely: `σ` is a non-unital ∗-homomorphism, so **34IV**.3 `cp_of_mi`
  gives complete positivity for free, and no "bijective miu-map has an miu
  inverse" argument is needed.
* Normality of `σ` is the one step the solution does not mention (it says
  only "consequently it is an nmiu-isomorphism").  It is four lines of
  algebra: if `u` bounds `σ(D)` then `(1−z)u = (1−z)(u − σd₀)(1−z) ≥ 0`, so
  `σ(⋁D) ≤ σ(ϱ u) = zu ≤ u`.  The same computation reappears below.
* `f(z·x) = f(x)` for ncp `f` with `f(z) = f(1)` is Kadison–Schwarz, but
  **34XIV** `cp_cs` with `a := x`, `b := 1−z` is sharper than the session-52
  costing suggested: it gives `f(x*(1−z))·f((1−z)x) ≤ ‖f(1−z)‖·f(x*x) = 0`
  directly, so no `ww* ≤ ‖x‖²(1−z)` norm estimate is needed at all.

Note 170IV.**2** stays blocked, and on *two* things, not one: 169IV, and the
thesis's `iso` (a bijective ncp-map of von Neumann algebras is nmiu), which
the tree does not have.


---

## Session 55: 151Ia is closed, and what that does and does not unblock

**151Ia** `selfdual_completion_univ` cost **~360 lines** of proof plus ~110
lines of reusable helpers — the 300–400 line estimate held.  It is the
thesis's own proof (151II): the approximating net is built explicitly over
`Finset (NPFunctional 𝒷 × ℕ)` (functionals × precision, `atTop`), pushed
forward along `T`, and the limit comes from ultranorm completeness of the
self-dual `Y` (**149V** `dils_selfdual`, `1 ⇒ 2`).  Everything after that
runs off one estimate, `‖T̂x − Tv‖_ω ≤ C‖x − ηv‖_ω`, which settles
`T̂∘η = T`, additivity, both homogeneities, boundedness (at `v = 0`) and
uniqueness one np-functional at a time.  See PROVING-LOG session 55 for the
two divergences and for why the ℬ-homogeneity step needs the *two*-functional
entourage `{ω, conjNP (star b) ω}`.

**163II-uniq fell with it**, as predicted.  Nothing else did:

* **154III `existence_paschke`** is now blocked on a *single* root, **150II**
  `dils_completion` — 151Ia is no longer part of its blocker set.  The
  remaining costing of session 54 stands: the `𝒜 ⊙ ℬ` inner-product space
  ~250 lines, `ϱ`/`h` and their nmiu/ncp clauses ~300 lines, both on top of
  150II.
* **164II ex.** `univprop_ext_tensor` likewise still needs 150II (or
  `ℓ²((pᵢⱼ))` as an actual Hilbert `𝒞`-module).
* **165VI** is blocked outside the directory — see its row above.

**So the next gate inside `B/Dils` is 150II `dils_completion`**
(`SelfDualCompletion.lean:79`), and it is the *only* remaining root: every
open item of `Paschke.lean` and `Pure.lean` is downstream of it or of
proc.tex's 96V/98I.  It is a type construction (150III–150XV: fast nets, the
uniformity on `V̄`, the module structure, extending the seminorms, a
transfinite induction on compatible extensions, self-duality) carrying
`NormedAddCommGroup`/`CStarModule`/`CompleteSpace`/`SelfDual`, and it is not
session-sized.

The only item in the directory that is neither blocked nor known-false and
has never been attempted is **138VIII-findim** `kraus_decomposition_findim`
(`Stinespring.lean:2037`).

---

## Session 58: 150II is costed, 138VIII-findim is closed

**138VIII-findim** `kraus_decomposition_findim` (`Stinespring.lean`) — the
one item that was unblocked, never attempted and not known false — is
**closed**, ~200 lines, axiom-clean, and the 200–300 line estimate held.  It
does **not** use `kraus_decomposition` (the general 138VIII) and needs no
ultraweak convergence: cutting `𝒦'` down to `Nᗮ` for
`N = ker(ξ ↦ V₀* ∘ (· ⊗ ξ))` and extending an orthonormal basis of `Nᗮ` to a
Hilbert basis of `𝒦'` makes the Kraus sum *finite*, so the net of partial
sums is eventually constant.  Divergence from the author's solution (which
bounds the dilation space inside the GNS construction) and a nit erratum
(the solution divides by `dim ℋ`) are logged.

`Stinespring.lean`'s remaining `sorry` is **139XI** `ess_uniq_pur`, which is
false as stated (ERRATA / QUESTIONS **B12**).  **The file is therefore
finished**, up to that ruling.

### 150II `dils_completion` — still the only root, now costed

Not closed, and not session-sized; `SelfDualCompletion.lean` is untouched.
The three questions the session was sent to answer, with the working in
PROVING-LOG session 58:

1. **Mathlib's completion applies** and replaces **150V–150IX** outright.
   The ultranorm uniformity is the uniformity of the seminorm family
   `(unSeminorm ω B)_ω`, whose two seminorm laws are already proved; then
   `WithSeminorms` + `UniformSpace.Completion` give the additive group, the
   ℂ-module *and* the 𝒷-action (via `un_op_smul`), and the possible
   **indefiniteness of `B` is handled for free** by the separated completion.
   In-tree precedent: **136II** does exactly this for the ℂ-valued case.
   What Mathlib does not give is the inner product (not uniformly
   continuous), the norm (not continuous) and the σ-iteration.
2. **`kaplansky_hilbmod_of_selfDual` does *not* collapse the iteration.**  It
   hypothesises `SelfDual ℬ X` and goes through the linking algebra, i.e.
   needs `ℬᵃ(X ⊕ ℬ)` to be a von Neumann algebra (**152X**) — so applying it
   to `V₁ = σ(V₀)` assumes the goal.  The ordinal induction *is* avoidable,
   but by an **inductive predicate** over the fixed index type `Φ` of
   entourages (legal because every Cauchy net is equivalent to a fast one),
   which also removes the thesis's Zorn reformulation.
3. **149V does more than this survey claimed**: as a TFAE it means the only
   property to prove on the carrier is `BddUnComplete`; self-duality and
   ultranorm completeness follow.  ⚠ But `SelfDualCompletion` also demands
   `[CompleteSpace X]` (**norm** completeness), which 149V does **not** give
   and which no lemma in the tree provides — an extra ~100-line item that the
   session-54/55 costing omitted.

**Superseded by session 59 — see the updated table below.**  Total costing:
**≈ 2100–2600 lines, 3–4 sessions**, of which steps 1–4
(seminorm family → `UniformSpace` → `Completion` → extended seminorms and
norm, ~900 lines) form a self-contained first session that leaves the file
compiling and are independently useful to the whole directory.  Step 5 (the
σ-closure and the inner product on it, 600–900 lines) is the only genuinely
new mathematics.  See the table in PROVING-LOG session 58.

**The next gate inside `B/Dils` is still 150II** — every open item of
`Paschke.lean` and `Pure.lean` is downstream of it or of proc.tex's
96V/98I.  With 138VIII-findim closed, **the only self-contained item left in
the directory is 162II `total_mv_order`** (comparison of projections in a
factor; Zorn + halving, genuinely hard).  Everything else is 150II, an item
downstream of it, known-false, or blocked outside `B/Dils`:

* `Kaplansky.lean`'s remaining **4** are exactly the known-false
  `kaplansky_hilbmod_A₁/_A₁'/_A₂/_A₂'` — **the file is finished** (158II
  itself was proved in session 57).
* `Stinespring.lean`'s remaining **1** is the known-false 139XI.
* `HilbertModules.lean` is 0.

So three of the seven files are done, and the directory's whole remaining
mass — `Pure` 12, `SelfDual` 7, `Paschke` 7 — sits behind 150II, proc.tex's
96V/98I, `tensor_characterization`, and the false 169XI.2a / 164II.2b.

---

## Session 59: 150II phase 1 is built — the nine-item table, marked off and re-costed

Nothing was closed (by design), and `B/Dils` stays at **32**.  What landed is
**495 lines** in `SelfDualCompletion.lean`, after `end Completion`, under
*"Parsec 1500 continued: the ultranorm uniformity and `V̄`"* — all compiling
and axiom-clean (`propext, Classical.choice, Quot.sound`).  See PROVING-LOG
session 59 for the two divergences and the three findings.

**Confirmed, and more sharply than session 58 put it:** the ultranorm
uniformity *is* the seminorm-family uniformity, and
`UnUnif.withSeminorms : WithSeminorms (UnUnif.sem B)` closes by **`rfl`**.
**150IV–150X are not transcribed at all.**

| # | piece | costed (s58) | status after s59 | remaining |
|---|---|---|---|---|
| 1 | seminorm family → `UniformSpace`, + `UnTendsto`/`UnCauchy`/`UnDense` bridge | 250 | **DONE** (~200 lines): `unSem`, `UnUnif`, `instUniformSpace`, `withSeminorms`, `hasBasis_uniformity`, `tendsto_iff`, `cauchy_iff`, `dense_iff`, `uniformContinuous_of_bound` | 0 |
| 2 | `V̄`, its `AddCommGroup` / `Module ℂ` / `SMul 𝒷` and the module axioms | 200 | **DONE** (~150 lines): `UnCompl`, `unEta` + its five algebra lemmas, `coe_eq_coe_of_inner_zero`, `op_smul_add'`, `add_op_smul'`, `mul_op_smul'`, `one_op_smul'`, `op_smul_comm_complex'` | 0 |
| 3 | extended seminorms on `V̄`, their laws and transformation rules | 250 | **MOSTLY DONE** (~130 lines): `semC`, `semC_coe`, `semC_unEta`, `continuous_semC`, `semC_nonneg/_zero/_add_le/_smul_complex/_neg/_op_smul` | separation (`∀ω, semC B ω x = 0 → x = 0`) and the reverse triangle inequality — ~60 |
| 4 | the "norm" on `V̄` | 200 | **RE-COSTED to ~80 and reshaped** — no `⨆` over np states and no new A/VN lemma: use `∀ ω, (semC B ω x)² ≤ M²(ω 1).re` and `np_orderSeparating` | ~80 |
| 5 | **the heart**: σ-closure as an inductive predicate over `Φ`, the inner product on it by `∃!`-induction, the `BInner` axioms | 600–900 | untouched | 600–900 |
| 6 | the carrier `X` as a subtype + `NormedAddCommGroup`/`NormedSpace ℂ`/`SMul 𝒷`/`CStarModule` | 250 | untouched | 250 |
| 7 | `BddUnComplete 𝒷 X`, then `SelfDual` + `UnComplete` from **149V** | 150 | untouched | 150 |
| 8 | `CompleteSpace X` (**not** supplied by 149V; *not* a transcription defect — 141II defines "Hilbert module" as norm-complete) | 100 | untouched | 100 |
| 9 | `η`, `η_inner`, ultranorm density of its range | 150 | **PART DONE**: `unEta` and `denseRange_unEta` are in; `η_inner` and `DenseRange → UnDense` need the inner product from step 5 | ~40 |
| **10** | **new**: universes.  `dils_completion` wants `X : Type (max u v)`, `Completion (UnUnif B) : Type v` — run the construction on `ULift.{u} V` with `B` transported | — | new | ~50 |

**Remaining after session 59 was ≈ 1300–1700 lines, 2–3 sessions.**  Session
60 did steps 3-tail, 4 and 5; see the next section for the state now.

---

## Session 61 (i.e. after session 60): 150II is one session from done

Session 60 added **747 lines** (section `SigmaClosure`), all axiom-clean, and
closed costing items **3**, **4** and **5** — including "the heart".  The
structural finding that made step 5 cheap is in PROVING-LOG session 60: the
inner product of a compatible extension is **determined by its underlying
set** (condition 4 of 150XI fixes the quadratic form, polarization fixes the
sesquilinear form, and **44XI** fixes the element of `𝒷`), so the thesis's
poset of *pairs* becomes a poset of `Submodule ℂ V̄`s under `⊆`, its limit
step becomes `sSup` of a chain, and both of 150XIII's estimates are replaced
by *joint continuity* of the polarization form `ipf`.

| # | piece | status after s60 | remaining |
|---|---|---|---|
| 1 | seminorm family → `UniformSpace`, `Un*` bridge | **DONE** (s59) | 0 |
| 2 | `V̄`, its module structure | **DONE** (s59) | 0 |
| 3 | extended seminorms `semC` and their laws | **DONE** — separation is `eq_zero_of_semC_eq_zero` (~15 lines, not 60); the reverse triangle inequality is **not needed** | 0 |
| 4 | the "norm" on `V̄` | **DONE** as `SemBddBy B M x := ∀ ω, semC B ω x ≤ M·((ω 1).re)^½`, with both directions of "on a compatible extension this is `‖x‖ ≤ M`" | 0 |
| 5 | **the heart**: the σ-closure and the inner product on it | **DONE**, ~490 lines: `ipf`, `HasIP`/`ipVal`, `IsCompatExt` (+ its `BInner`), `SigmaCl`, `IsCompatExt.sigma`, `exists_maximal_compatExt` | 0 |
| 6 | the carrier `X := ↥W` with `NormedAddCommGroup`/`NormedSpace ℂ`/`CStarModule` | untouched (`hW.smulInst`, `hW.binner` are in) | 250 |
| 6b | **new**: `unSeminorm ω (inner 𝒷) = semC B ω` on `X` (clause 4 of 150XI) — the bridge steps 7–9 all run through | new | 40 |
| 7 | `BddUnComplete 𝒷 X` from σ-closedness, then **149V** | untouched | 150 |
| 8 | `CompleteSpace X` | untouched | 100 |
| 9 | `η`, `η_inner`, `UnDense (range η)` | `η_inner` is `ipVal_unEta`; density needs 6b | 60 |
| 10 | universes (`ULift.{u} V`) | untouched | 50 |

**Remaining ≈ 600 lines — one session.**  It is packaging: no new
mathematics, and the two facts everything rests on (`σ(W) ⊆ W` for the
maximal `W`, and `ω[x,x] = ‖x‖_ω²` on it) are proved.

**Carry-forward.**  In our setting `[SMul 𝒷 V]` carries **no axioms**, so the
only inner-product rule that survives to `V̄` is the *conjugated* one
`[b·x,b·y] = b[x,y]b*`; 𝒷-homogeneity is recovered by polarizing in the
algebra variable (`IsCompatExt.ipVal_op_smul_right`), which also needed a
sixth module law `smul_op_smul' : (c • b) • x = c • (b • x)`.

---

## Session 61 (result): **150II `dils_completion` is proved**; the next gate is 154III

`SelfDualCompletion.lean` is **finished** (1 → 0), `B/Dils` is **32 → 31**,
and every declaration of the new material is axiom-clean
(`propext, Classical.choice, Quot.sound`), checked both inside the module and
from an importing file against a rebuilt olean.  **432 lines** were added
(after `end SigmaClosure`, under *"Parsec 1500 concluded"*); the statement of
`dils_completion` is unchanged, only its *proof* moved down the file, to
after the construction it consumes.

Costing items 6–10 and 6b, costed at ≈600 lines, cost **432**:

| # | piece | costed (s60) | actual | how |
|---|---|---|---|---|
| 6 | carrier + `NormedAddCommGroup`/`NormedSpace ℂ`/`CStarModule` | 250 | **~110** | `CompatExt` (see below); `AddGroupNorm.toNormedAddCommGroup`; every axiom is one application of `module_seminorm_2` or of the `ipVal` API |
| 6b | `unSeminorm ω (inner 𝒷) = semC B ω` on `X` | 40 | **6** | `ipVal_spec` + `ipf_self` + `Real.sqrt_sq` |
| 7 | `BddUnComplete 𝒷 X`, then **149V** | 150 | **~80** | plus a **new general lemma**, `exists_semC_entourage_subset` (~45), that was not in the costing |
| 8 | `CompleteSpace X` | 100 | **~75** | exactly session 58's route |
| 9 | `η`, its clauses, `UnDense (range η)` | 60 | **~35** | density needs no uniformity basis: the `semC`-ball is *open*, so `DenseRange.exists_mem_open` suffices |
| 10 | universes (`ULift.{u} V`) | 50 | **~15** | `BInner.ulift`; every field is the corresponding field of `B` |

**Two things the costing did not name.**

1. **`exists_semC_entourage_subset` — the extended seminorms *generate* the
   uniformity of `V̄`.**  Item 7 needs to turn `UnCauchy` (a `semC` statement)
   into Mathlib's `Cauchy` (an entourage statement), and nothing in phases 1–2
   does that: `semC` was built by `Completion.extension`, which gives
   continuity but not a basis.  The proof is four lines of mathematics —
   closed entourages are a basis (`uniformity_hasBasis_closed`); pull one back
   along the uniform inducing `coe` and apply `UnUnif.hasBasis_uniformity`; the
   `semC`-entourage is *open* and the image of `V × V` is dense, so
   `Dense.open_subset_closure_inter` puts it inside the closed entourage.  It
   is independently useful and belongs to the `UnCompl` API rather than to
   150II.
2. **Bundling.**  Every structure on the carrier depends on the *proof*
   `hW : IsCompatExt B W`, so none of them can be an `instance` — and `letI`
   in the type of a `def` (the shape `IsCompatExt.binner` already had) makes
   `isDefEq` time out.  Bundling `W` with its proof into a one-field structure
   `CompatExt B` fixes this: `CompatExt.Car E` is a type *synonym* of `↥E.carrier`
   (load-bearing — the subtype of a uniform space carries the subspace
   uniformity, which would clash with the norm one), and everything on it is a
   genuine instance.

**A regression from session 59, found here and fixed.**  Session 59 added a
**public** `unSeminorm_op_smul` to `SelfDualCompletion.lean`; `SelfDual.lean`
(which imports it transitively) already had a `private` lemma of that name, and
Lean rejects a private declaration whose name is already taken by an imported
public one.  So **`SelfDual.lean` has not compiled since session 59** — two
errors, invisible to a `grep -c "declaration uses"` count, and invisible to
sessions 59 and 60 because they only ran `lean` on the file they were editing.
Renaming the private lemma to `unSeminorm_op_smul_inner` restores it.
**Lesson: after adding a public name to a file, re-check its dependents, and
count errors as well as `sorry`s.**

**What 150II unblocks.**  **158II** `kaplansky_hilbmod` (Kaplansky density for
Hilbert C*-modules, general case) was proved *modulo* 150II in session 57; it
is now **unconditional** — `#print axioms` is clean.  The doc comments in
`Kaplansky.lean` that said otherwise are corrected.

**The next gate is 154III `existence_paschke`** (`Paschke.lean:425`), now the
single root of `B/Dils`: 157IV.2/.3, most of `Pure.lean` (12), 171II and the
shortcut for 164II ex. all sit behind it.  It is no longer blocked on anything
— 150II and 151Ia are both proved, and the ℬ-valued Gram positivity
`0 ≤ ∑ᵢⱼ bᵢ* φ(aᵢ*aⱼ) bⱼ` it needs is available (`cp_iff … |>.out 1 0`, used
in `Stinespring.lean:3187`), so 33II.1 is *not* in its blocker set.  What it
costs, in the same units as the table above:

| # | piece | cost |
|---|---|---|
| 1 | `BInner ℬ (𝒜 ⊗[ℂ] ℬ)` with `⟨a⊗b, a'⊗b'⟩ = b' φ(a' a*) b*`: two `TensorProduct.lift`s, and positivity from `cp_iff` after writing a tensor as a finite sum (`Stinespring.exists_fin_rep` is the model, currently `private`) | 200 |
| 2 | `X` and `tprod` from **150II**, `inner_tprod`, `PhiCompatible` | 100 |
| 3 | `univ` from **151Ia** `selfdual_completion_univ` (bilinear → linear on the tensor product, then the universal property) | 150 |
| 4 | `ρ : NMIUMap 𝒜 (Ba ℬ X)ᵐᵒᵖ` — each `ρ a₀` from `univ`, then unitality/multiplicativity/involutivity by uniqueness on elementary tensors; **normality is the hard field** | 250–400 |
| 5 | `h : NCPMap (Ba ℬ X)ᵐᵒᵖ ℬ` from `hilbmod_adj_vector_ncp` (**153IV**, proved) | 100 |

≈**800–950 lines, one long session or two.**  `existence_paschke_5` stays
structurally blocked (unchanged).
