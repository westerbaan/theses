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
| 169V | `h_is_corner_for_unital_map` | **(b)** | ⚠️ row corrected session 66: `existence_paschke` **is** proved, and `exists_paschke_iso_paschkeModule` supplies the transfer, so the author's `ϑ : ℬ ≅ p𝒫p`, `p = \|e⟩⟨e\|` is now writable.  The remaining gap is the *last* sentence of 169VI — "so `h` is a corner (of `p`)" — which is **169IV**, the universal property of the standard corner, still `sorry` and cited to proc.tex |
| 169X | `dils_stand_filter` | **(c)** | cited to proc.tex 96V — which **is** now proved in `A/Proc/Measurement.lean` (session 47) but is not importable here.  Proving it locally means redoing 96V |
| **169XI.1** | `dils_filter_basics_1` | **(a)** | **CLOSED this session** |
| **169XI.2a** | `dils_filter_basics_2a` | **(a)** | was **(d)**, false under the transcribed `c 1 ≤ b`.  **CLOSED session 63**, after Bas ruled on B11 (2026-08-16): the repair is that `IsFilterFor`'s *mediating* map is **subunital**, not that `c 1 = b`.  ~25 lines, the thesis's own argument; needs only monotonicity of `c'` plus **169XII**, not faithfulness |
| **169XI.2b** | `dils_filter_basics_2b` | **(a)** | **CLOSED session 53**, from 169XI.1.  Note it does **not** depend on 2a, and was unaffected by the B11 repair |
| 170II.1 | `dils_examples_pure_1` | **(b)** | `ad_T` classification of pure maps `B(H) → B(K)`; needs 171VII and the Stinespring block |
| 170II.2 | `dils_examples_pure_2` | **(b)** | the thesis derives it from 169V + 169XI.2.  ⚠️ row corrected session 66: **169XI.2a is no longer false or open** (B11 was ruled on; closed session 63) and 169XI.2b closed session 53, so the only blocker left is **169V**, i.e. **169IV** |
| **170IV.1** | `surjective_nmiu_1` | **(a)** | **CLOSED session 53**, once D5 was ruled on and `[VonNeumannAlgebra A] [VonNeumannAlgebra B]` restored (the fix really was local to the two signatures).  ~150 lines by the costing below, and the estimate held |
| 170IV.2 | `surjective_nmiu_2` | **(b)** | converse; the von Neumann binders are restored (D5 done), but it still needs **169IV** — the standard corner `h_z` — *and* the thesis's `iso` (an ncp-isomorphism of von Neumann algebras is nmiu), which the tree does not have either |
| 171II | `paschke_corner` | **(b)** | three-step proof through `existence_paschke`, which **is** proved now, as are the two `A/VN` inputs of its third step (**83V** `cceil_sum`, axiom-clean, and **170IV**.1 `surjective_nmiu_1`).  What is *not* in the tree is the first two steps: `𝒜p` as a self-dual Hilbert `p𝒜p`-module and the isomorphism `𝒜 ⊗_{h_p} p𝒜p ≅ 𝒜p`.  Still multi-session |
| 171VII | `paschke_pure` | **(b)** | needs 171II, 170II.2 **and** proc.tex's `square-f` and `weakly-closed-ideal` |
| **172III** | `ncp_extreme_paschke` | **(a)** | **CLOSED session 66.**  This row (and session 64's) said it needs 170II.2 — **wrong**: only the *thesis's* proof of 3 ⇒ 1 does, to get `0 < λ < 1` out of purity of `h`.  Choosing `t = μa + ½` with `μ = (4(‖a‖+1))⁻¹` gives `φ_t(1) = ½φ(1)` directly, so 3 ⇒ 1 needs nothing beyond **157IV**.2/.3 (now proved).  ~200 lines + two helpers (`ncpSMul`, `isLUB_ofReal_smul`) |
| 172X | `pure_ncp_extreme` | **(b)** | needs 171II + 169XI (172III is no longer a blocker) |
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

---

## Session 62 (result): **154III `existence_paschke` is proved**; the next gate is 154III.5

`Paschke.lean` goes **7 → 6** and `B/Dils` **31 → 30**:
`HilbertModules` 0, `SelfDualCompletion` 0, `Stinespring` 1, `Kaplansky` 4,
`Paschke` **6**, `SelfDual` 7, `Pure` 12 — each source run through `lean`
individually and **paired with an error count (all 0)**, including the two
dependents `SelfDual.lean` and `Pure.lean`, rebuilt against the new
`Paschke.olean`.  `existence_paschke` and every new declaration are
axiom-clean (`propext, Classical.choice, Quot.sound`), checked from an
importing file against the rebuilt olean.

**≈830 lines** were added to `Paschke.lean`, immediately before
`existence_paschke`, under *"The construction of `𝒜 ⊗_φ ℬ`
(**154IV**–**154VI**)"*.  The ≈800–950 estimate held, and so did four of the
five line items:

| # | piece | costed | actual | how |
|---|---|---|---|---|
| 1 | `BInner ℬ (𝒜 ⊗[ℂ] ℬ)` | 200 | **~150** | `ptensPair` by two `TensorProduct.lift`s; `star` on the tensor product is Mathlib's (`TensorProduct.star_tmul`), so the conjugate-linear slot is `x ↦ pair (star x)`; positivity is `phi_gram_nonneg` = `cp_iff … .out 1 0` after `TensorProduct.exists_finset` |
| 2 | `X`, `tprod`, `inner_tprod`, `PhiCompatible` | 100 | **~90** | `dils_completion` at `𝒷 = ℬ`, `V = 𝒜 ⊗[ℂ] ℬ`, both `Type u`, so `SelfDualCompletion.{u,u,u}` — no `ULift`.  The bound holds with `r = 1`, *as an equality* |
| 3 | `univ` from **151Ia** | 150 | **~110** | `TensorProduct.lift` of `T`, then `selfdual_completion_univ`.  The one gap the statement of `PhiCompatible` leaves is ℂ-linearity in `b`, recovered from `smul_action` + `op_smul_complex_smul`/`op_one_smul` |
| 4 | `ρ : NMIUMap 𝒜 (Ba ℬ X)ᵐᵒᵖ`, **normality the hard field** | 250–400 | **~330** | see below |
| 5 | `h` from a vector state | 100 | **~90** | **not** `hilbmod_adj_vector_ncp` (153IV) but **145I** `hilbmod_vectstates_cp` for complete positivity and **152XIII** `baVecNP` (through `npFunctionalOp`, already in the file) for normality |

### What `ρ`'s normality actually cost — and a blocker the costing missed

The thesis (154VI) proves normality of `ϱ` from **48II** `normal_faithful`
and **152IX** `hilmod-fixed-on-V`, reducing it to normality of the vector
forms `d ↦ ⟨x̂, ϱ(d) x̂⟩ = ∑ᵢⱼ bᵢ* φ(aᵢ* d aⱼ) bⱼ`, and then cites **153I**
`hilbmod-ad-ncp` **and 49IV `mn-vna`** for that.  ⚠️ **Both halves of 49IV it
needs are `sorry` in `A/VN/Basic.lean`**: `mn_vna_2`'s third clause
(`M ↦ ∑ᵢⱼ aᵢ* Mᵢⱼ aⱼ` preserves suprema — although *this* one is in fact
available, as `exists_isLUB_matForm`, which is proved) and `mn_vna_3`
(`Mₙφ` is normal, genuinely open).  So the thesis's route to the *only*
hard field of `existence_paschke` is blocked outside `B/Dils`, which neither
the brief nor the survey knew.

The route taken instead needs nothing from `A/VN` that is not already
proved, and is ~150 of the ~330 lines:

* **`gram_polarization`** — *double* polarisation, i.e. **44II**
  `mult_polarization` applied twice, once in the `aᵢ` and once in the `bᵢ`:
  `b φ(u d u'*) b* = (1/16) ∑ₖ ∑ₗ iᵏ⁺ˡ · w_k* φ(v_l* d v_l) w_k`
  with `w_k = iᵏ b* + b'*`, `v_l = iˡ u* + u'*`.  Every diagonal term
  `d ↦ ω(w* φ(v* d v) w)` is `conjNP v (compNP φ (conjNP w ω))`, an
  np-functional.  This terminates where the single polarisation of the
  *module* variable does not: `Θ_{a⊗b}(d) = b φ(a d a*) b*`, so the double
  polarisation is exactly the reduction of a general `Θ_x` to elementary
  tensors, whereas polarising in `x ∈ 𝒜 ⊙ ℬ` only ever reduces `n` terms to
  two.
* **`preservesDirSups_of_np_combination`** — a monotone `g : 𝒜 → ℂ` that is
  a ℂ-*combination* of np-functionals is normal.  A combination does not
  preserve suprema, so normality is read off **convergence**: each
  np-functional converges along the net of the directed set to its value at
  the supremum (`npFunctional_tendsto_of_isLUB`, the **44VI**
  `vna_supremum_uwlimit` idiom isolated), the combination therefore
  converges, and the limit is squeezed between monotonicity and any upper
  bound.  This is the reusable half of the argument.

The remaining ~180 lines of item 4 are ordinary: `exists_prho` (through
`ptprod_univ` and **152VIII** `hilbmod_adjoint_exists`, which turns a bounded
module map on a self-dual module into an element of `𝒷ᵃ(X)`),
`ba_ext_ptprod` (**152IX**.2 on the elementary tensors), the ring/star
structure by that extensionality — `prho_star` needs the `BInner`-level
identity `[x·a₀, y] = [x, y·a₀*]` rather than a density argument — and the
`ᵐᵒᵖ` bookkeeping.

### The next gate: **154III.5 `existence_paschke_5`, which is *not* blocked**

⚠️ **The standing claim that `existence_paschke_5` is "structurally blocked"
is wrong**, and it was wrong for a reason that this session removed.  The
argument was that 154X builds `σ` by re-running the construction for `h'`,
"which needs `existence_paschke` applied to a triple the statement does not
hand you".  But 154X applies the construction to the **ncp-map
`h' : 𝒫' → ℬ`**, and `𝒫'` is a von Neumann algebra by `PaschkeTriple.vn` —
so `existence_paschke h'` now delivers exactly the `PaschkeModule h'` that
154X asks for.  The route, entirely inside `B/Dils`:

1. `M' : PaschkeModule h'` from `existence_paschke h'`; put
   `ϱ'' := M'.ρ ∘ D'.ρ : NMIUMap 𝒜 (Ba ℬ M'.X)ᵐᵒᵖ` and `e := M'.tprod 1 1`.
   `paschkeModule_h_ρ` gives `φ a = ⟨e, ϱ''(a) e⟩`, which is the hypothesis
   `hφ` of **154III.4** `existence_paschke_4` **on the nose** (that theorem is
   proved and takes an arbitrary `M`).  ~60 lines.
2. `existence_paschke_4` yields the inner-product-preserving intertwiner
   `S : M.X → M'.X`; `hilbmod_adjoint_exists` gives `S*`, and **153I**
   `hilbmod_ad_ncp` (proved) gives `ad_S : NCPMap (Ba ℬ M'.X) (Ba ℬ M.X)`.
   ~80 lines.
3. Transport `ad_S` to the opposite algebras.  This is the one genuinely new
   obligation: `f ↦ fᵐᵒᵖ` does **not** preserve complete positivity in
   general (the transpose is the counterexample the file header already
   records), but it does for `ad_S`, because the ᵐᵒᵖ-Gram sum collapses to
   `(∑ⱼ Cⱼ S* Tⱼ)(∑ᵢ Cᵢ S* Tᵢ)*`.  Normality transports along
   `selfAdjointUnop` as in `npFunctionalOp`.  ~120 lines.
4. `σ := ad_S^ᵐᵒᵖ ∘ M'.ρ`, and the two equations `σ ∘ ϱ' = ϱ`,
   `h ∘ σ = h'` by unwinding.  ~60 lines.
5. **Uniqueness** of `σ` — 154VIII, which the thesis proves *before* part 4:
   by `hilmod_fixed_on_V` it is enough to compare `⟨x̂, σₖ(c) x̂⟩`, and
   `a ⊗ b = ϱ(a)(1 ⊗ 1)b` turns both into
   `∑ᵢⱼ bᵢ* h'(ϱ'(aᵢ*) c ϱ'(aⱼ)) bⱼ`.  Needs `dils-univlemma`
   (`σ(ϱ'(a) c ϱ'(a')) = ϱ(a) σ(c) ϱ(a')` for a mediating `σ`) — check
   whether the tree has it before writing it.  ~150 lines.

**≈450–550 lines, one session.**  It is the single highest-return item left
in the directory: `IsPaschkeDilationOf` carries the universal property, so
**156II, 157IV.2/.3 and 171II are all downstream of 154III.5, not of
`existence_paschke`** — every one of them is stated for an arbitrary
`PaschkeTriple`, and there is no way to transfer a computation from
`𝒜 ⊗_φ ℬ` to it without the mediating `σ`.  The earlier reading of this
survey ("`existence_paschke` gates 157IV.2/.3, most of `Pure.lean`, 171II")
was therefore one step short: `existence_paschke` gates 154III.5, and
154III.5 gates them.

Also still true after this session: **162II `total_mv_order` is the only
self-contained item in the directory**, `165VI` is blocked outside it on
`tensor_characterization`, and the five known-false items
(`Kaplansky`'s four, `Stinespring`'s 139XI) plus 169XI.2a and 164II.2b stand.

### Reusable output

All public in `Paschke.lean`: `ptensPair` / `ptensBInner` (the φ-inner
product on `𝒜 ⊙ ℬ`), `exists_fin_tmul`, `phi_gram_nonneg`, `ptprod`,
`ptprod_univ` (part 1 as a standalone theorem), `phiLift`,
`exists_ba_of_boundedModuleMap`, `ba_ext_ptprod`, `prho` and its ring/star
lemmas, `prhoHom`, `prhoHom_normal`, `pTheta`, `gram_polarization`,
`npFunctional_tendsto_of_isLUB`, `preservesDirSups_of_np_combination`,
`pVecLin` / `pVecLin_cp` / `pVecLin_normal` / `pVecNCP` (the vector state on
`𝒷ᵃ(X)ᵐᵒᵖ` as an ncp-map, for **any** self-dual `X` — this is what 154III.3
is, and it is stated independently of the Paschke construction).

⚠️ The name `gram_nonneg` was **not** available: `SelfDual.lean` (which
imports `Paschke.lean`) has a `private` lemma of that name, and a public one
here would have reproduced the session-59 regression exactly.  Ours is
`phi_gram_nonneg`.  `exists_rho` likewise collides with a `private` lemma in
`A/CStar/TowardsVN.lean` (different namespace, so harmless, but renamed to
`exists_prho` anyway).


---

## Session 63 (result): **154III.5 `existence_paschke_5` is proved**, and the B11 ruling closes 169XI.2a

`Paschke.lean` goes **6 → 5**, `Pure.lean` **12 → 11**, `B/Dils` **30 → 28**:
`HilbertModules` 0, `SelfDualCompletion` 0, `Stinespring` 1, `Kaplansky` 4,
`Paschke` **5**, `SelfDual` 7, `Pure` **11** — **all seven** run through `lean`
individually against rebuilt oleans and each **paired with an error count,
0 everywhere** (an `A/VN` rebuild by a sibling worker was in flight during the
session, so the upstream four were re-checked as well rather than assumed).  Every new or changed
declaration is axiom-clean (`propext, Classical.choice, Quot.sound`), checked
from an importing file.

**399 lines** in `Paschke.lean` (the ≈450–550 estimate held), ~40 changed lines
in `Pure.lean`.

### `existence_paschke_5`: what the costing got right and wrong

The route was **exactly** the five steps costed in the session-62 section
above, and the "not structurally blocked" correction is confirmed: 154X
re-runs the construction on `h' : 𝒫' → ℬ`, whose domain is a von Neumann
algebra by `PaschkeTriple.vn`, so `existence_paschke h'` supplies the missing
input, and `paschkeModule_h_ρ` at `h'` is the hypothesis of
`existence_paschke_4` on the nose.

Two line items were mis-costed, in opposite directions:

| # | piece | costed | actual | note |
|---|---|---|---|---|
| 3 | `ad_S` cp on the **opposite** algebras | 120 | **~15** | the survey's "`f ↦ fᵐᵒᵖ` does not preserve complete positivity in general" is **wrong**.  It does, for every `f`: the Gram sum of `fᵐᵒᵖ` unops to the Gram sum of `f` at the starred families with the two summation indices exchanged.  The counterexample in the file header is `op : A → Aᵐᵒᵖ` (a ∗-*anti*-isomorphism, = transpose on `M₂`), a different map.  Now public and general as `ncpMop` |
| 5 | uniqueness of `σ` (**154VIII**) | 150 | **~230** | the thesis's route is via `hilmod-fixed-on-V`, i.e. ultranorm density of `η`'s image — unavailable, because `existence_paschke_5` quantifies over an **abstract** `PaschkeModule`, which carries no `η`.  Replaced by two lemmas extracted from the *uniqueness* half of the universal property of part 1 (below).  `dils_univlemma` **is** in the tree (**139III**, `Stinespring.lean`), and `stinespring_is_paschke` (140III) is a complete worked template for the whole shape |

### The two reusable lemmas that replace the density argument

* **`paschkeModule_inner_tprod_separating`** — `⟨a ⊗ b, w⟩ = 0` for all
  `a, b` forces `w = 0`.  Run part 1 against **`ℬ` itself** (`selfDual_self`)
  and the **zero** bilinear map: `x ↦ ⟨w, x⟩` and `0` are then two bounded
  module maps `𝒜 ⊗_φ ℬ → ℬ` lifting it, so they are equal, and evaluating at
  `w` gives `⟨w,w⟩ = 0`.
* **`paschkeModule_ba_ext`** — adjointable operators agreeing on the
  elementary tensors are equal, by the same uniqueness at `Y = 𝒜 ⊗_φ ℬ` (on
  top of `phiCompatible_comp`).

They make **no polarization step necessary**: the same computation run at two
*different* elementary tensors gives the whole sesquilinear form,
`⟨a ⊗ b, σ(c)(a' ⊗ b')⟩ = b' h'(ϱ'(a') c ϱ'(a*)) b*` (`paschke_sigma_matrix`),
where the thesis determines only the diagonal.

### The next gate

**`exists_paschke_iso_paschkeModule`** is in `Paschke.lean`, public, proved
(three lines): `existence_paschke_5` composed with **140VIII**
`paschke_unique_up_to_iso` says *every* Paschke dilation of `φ` is
nmiu-isomorphic to the constructed one, compatibly with `ϱ` and `h`.  That is
the "by `paschke-unique-up-to-iso` it suffices to prove it for the dilation of
`existence-paschke`" step with which the thesis opens **156II**
(dils.tex:3886) *and* **157IV**.2/.3 (dils.tex:4042).  It typechecks, which is
the machine-check that the two settings line up.

**So the next gate is 157IV.2/.3 `paschke_correspondence_embedding` /
`_surjective`** (`Paschke.lean`), now genuinely unblocked and the largest
remaining cluster inside the directory.  Costing, from dils.tex 157VII–157IX:

* **.2 (order embedding)**: for `T ∈ ϱ(𝒜)^□` with `φ_T` ncp, show `T ≥ 0` by
  `⟨x̂, T x̂⟩ = ∑ᵢⱼ bᵢ* φ_T(aᵢ*aⱼ) bⱼ ≥ 0` on `x ∈ 𝒜 ⊙ ℬ`.  Needs positivity
  from the elementary tensors, i.e. **`hilbmod_ordersep` plus ultranorm
  density** — so it must be run on the *concrete* module (`E.dense`), not on
  an abstract `PaschkeModule`, and then transported.  ~250 lines.
* **.3 (surjectivity)**: for `ψ ≤_ncp φ`, the identity `a ⊗ b ↦ a ⊗ b` is
  φ-compatible into `𝒜 ⊗_ψ ℬ` (this is where `ψ ≤_ncp φ` enters, via the two
  Gram forms), giving `W`; then `T = W*W ∈ ϱ(𝒜)^□`, `0 ≤ T ≤ 1` and
  `φ_T = ψ`.  Every ingredient is now in the file
  (`ptprod_univ`, `hilbmod_adjoint_exists`, `hilmod_fixed_on_V`).  ~300 lines.
* **transport to an arbitrary triple** (157IX): `exists_paschke_iso_paschkeModule`,
  then check that `ϑ` restricts to `[0,1]_{ϱ'(𝒜)^□} → [0,1]_{ϱ(𝒜)^□}` and
  that `φ_t^{𝒫'} = φ_{ϑ(t)}^{𝒫}`.  ~150 lines.

**156II `paschke_injective`** is unblocked by the same corollary but is
*also* an A/VN question (`cceil-fundamental`, `ad-contraposed`, `ceil` of a
map), so it is the less attractive of the two.

Unchanged after this session: **162II `total_mv_order`** is still the only
self-contained item outside the Paschke chain; **165VI** is still blocked
outside the directory on `tensor_characterization`; the five known-false items
stand; **164II.2b** stands (QUESTIONS D6).  **169XI.2a is no longer among the
false ones** — see the row above.

---

## Session 64 (result): **157IV.2 and 157IV.3 are proved**; the next gate is 156II

`Paschke.lean` goes **5 → 3** and `B/Dils` **28 → 26**:
`HilbertModules` 0, `SelfDualCompletion` 0, `Stinespring` 1, `Kaplansky` 4,
`Paschke` **3**, `SelfDual` 7, `Pure` 11 — each source run through `lean`
individually and **paired with an error count (0 everywhere)**, including the
two dependents `SelfDual.lean` and `Pure.lean` rebuilt against the new
`Paschke.olean`.  Every new declaration is axiom-clean
(`propext, Classical.choice, Quot.sound`), checked from an importing file.

**≈470 lines** were added to `Paschke.lean`, in `section Correspondence`
between `exists_corrComp` and `paschke_correspondence_mem` (the helpers) and
in the two theorems themselves.  The costing (≈250 + ≈300 + ≈150) held in
total but was wrong about the shape:

| # | piece | costed | actual | note |
|---|---|---|---|---|
| .2 | order embedding, on the **concrete** module via `hilbmod_ordersep` + `E.dense` | 250 | **~60** | it is **not** run on the concrete module and uses **no density**: given `φ_t ≤_ncp φ_s`, part 3 produces a *positive* `u` with `φ_u = φ_{s−t}`, and injectivity gives `u = s − t` |
| .3 | surjectivity | 300 | **~200** | the thesis's 157VIII verbatim, except `T ≤ 1`, which comes from `φ_{T+T'} = φ_1` and injectivity rather than from `hilmod-fixed-on-V` |
| — | injectivity + the matrix identity (**not costed**) | — | ~150 | `paschkeModule_inner_tprod_commutant`, `paschkeModule_phiT_injective` |
| — | transport to an arbitrary triple (157IX) | 150 | **~60** | `exists_paschke_iso_paschkeModule` + `starAlgHom_nonneg` (`A/VN`) + the new `starAlgHom_nonneg_reflect` |

**The survey's claim that .2 "must be run on the concrete module — it needs
`hilbmod_ordersep` and `E.dense`" is wrong.**  Both parts run on an abstract
`M : PaschkeModule φ`; `hilmod_fixed_on_V`, `E.dense` and `hilbmod_ordersep`
appear nowhere in either proof (`ba_nonneg_iff`, which is `hilbmod_ordersep`
transported to `Ba`, is used once, for `0 ≤ W*W` — a one-liner, not a density
argument).  The two facts that replace the thesis's density steps are the
**full matrix identity** `⟨a ⊗ b, t(a' ⊗ b')⟩ = b' φ_t(a' a*) b*` for `t` in
the commutant (the thesis computes only the diagonal) and, through it,
**injectivity of `t ↦ φ_t`**; positivity of `T` is then never proved by hand,
because part 3 hands it over as `T = W*W`.  Note the dependency order is
inverted relative to the thesis: **.3 proves .2**.

Also worth recording: **157IV.2's hypotheses `0 ≤ s` and `t ≤ 1` are not
used** (only `s ≤ 1`, `0 ≤ t` and the two commutant memberships), and 157VI —
now public as **`exists_phiT_ncp`** — is model-independent, so part 1 is three
lines of it.

### The next gate

**156II `paschke_injective` / `paschke_injective_carrier`** (2 of the 3
remaining `sorry`s; the third is **155II** `ksgns`, which is a KSGNS
construction, not a Paschke item).  It is unblocked in the same way — the
transfer corollary plus the matrix identity above give the computation on the
constructed module — but it is *also* an A/VN question (`cceil-fundamental`,
`ad-contraposed`, the `ceil` of a map), so check those roots before starting.
`paschkeModule_inner_tprod_commutant` is likely to be the workhorse there too:
`ϱ(p) = 0` iff every matrix element `b' φ(a' p a*) b*` vanishes.

Unchanged after this session: **162II `total_mv_order`** is still the only
self-contained item outside the Paschke chain; **165VI** is still blocked
outside the directory on `tensor_characterization`; the five known-false items
and **164II.2b** (QUESTIONS D6) stand.  With 157IV closed, `Pure.lean`'s
**172III** `ncp_extreme_paschke` now needs only 171II and 170II.2 (its
`paschke_correspondence_*` prerequisite is met).


---

## Session 66 (result): **156II is proved** — and it needed no new `A/VN` — plus **172III**, which the survey had wrongly blocked on 170II.2

`Paschke.lean` **3 → 1**, `Pure.lean` **11 → 10**, `B/Dils` **26 → 23**:
`HilbertModules` 0, `SelfDualCompletion` 0, `Stinespring` 1, `Kaplansky` 4,
`Paschke` **1**, `SelfDual` 7, `Pure` **10** — every file run through `lean`
individually against rebuilt oleans and **paired with an error count, 0
everywhere**.  All three new theorems verify
`[propext, Classical.choice, Quot.sound]` from an importing file.

### 156II: the A/VN question was already answered

The brief flagged 156II as "partly an A/VN question (`cceil-fundamental`,
`ad-contraposed`, the `ceil` of a map)".  **Neither `cceil_fundamental` nor
`ad_contraposed` is used.**  They belong to the thesis's route, which proves
`⌈ϱ⌉ = ⌈⌈φ⌉⌉` by showing `p ≤ ⌈ϱ⌉^⊥ ⟺ p ≤ ⌈⌈φ⌉⌉^⊥` for every projection `p`;
the `a ⌈φ⌉ a* ≤ p^⊥` step (`ad-contraposed`) and the union
`⌈⌈φ⌉⌉ = ⋃_a ⌈a⌈φ⌉a*⌉` (`cceil-fundamental`) are what carry `a` through.  Our
two statements are phrased *without* carriers, so the whole detour
disappears:

* `paschke_injective_carrier` (`ϱ(p) = 0 ⟺ ∀a, φ(a*pa) = 0`).  **⇒** is three
  lines from `φ = h ∘ ϱ` alone — no model, no minimality.  **⇐** transports to
  the constructed module by `exists_paschke_iso_paschkeModule` and computes
  `⟨(ap) ⊗ b, (ap) ⊗ b⟩ = b φ(a p a*) b*`, so the hypothesis (at `a*`) kills
  every elementary tensor and `paschkeModule_ba_ext` gives `ϱ(p) = 0`.  This
  is the thesis's own computation; what it replaces is the appeal to
  `hilmod-fixed-on-V`.
* `paschke_injective` uses **63II**.4 `carrier_basic_4` and **69IV**
  `carrier_miu` from `A/VN` — **both already proved**, so nothing was needed
  *from* A/VN beyond what is on the shelf.  `⌈ϱ⌉` is central and
  `ϱ(⌈ϱ⌉^⊥) = 0`, so the carrier form at `a = 1` gives `φ(⌈ϱ⌉^⊥) = 0`, the
  hypothesis gives `⌈ϱ⌉ = 1`, and `carrier_basic_4` converts that to
  injectivity.  The `⇒` half needs only `a*za = z(a*a)z ≤ ‖a*a‖z` for central
  `z`.

⚠️ **Both statements were missing `[VonNeumannAlgebra ℬ]`** and it has been
restored — a transcription slip of exactly the `221IV.1` kind, not a
weakening in the source: dils.tex 156II is about an ncp-map, ncp-maps go
between von Neumann algebras, and every sibling in the file
(`existence_paschke`, all of **157IV**) carries both binders.  Without it
there is no `PaschkeModule φ` to transport to, and the ⇐ half is not provable
by any route we could find: the only *abstract* substitute we could see is a
minimality lemma ("a projection `r` in `ϱ(𝒜)^□` with `h(r^⊥·) = 0` is `1`",
proved from the universal property by comparing `π : c ↦ rcr` with the
mediating map out of the corner triple), and that needs corner **algebras**,
which live in `A/Proc/Measurement.lean` and are off this import path.
Recorded in `PROVING-LOG.md`, not `QUESTIONS.md`: the thesis is right and we
were wrong, so no author decision is involved.

### 172III: the survey's blocker was the thesis's proof, not the statement

`ncp_extreme_paschke` was listed as needing 170II.2 `dils_examples_pure_2`
(purity of `h`), which is blocked on 169IV/169X and hence on proc.tex.  That
is true of the thesis's **proof** of 3 ⇒ 1 only, where purity is used to split
`h = c ∘ h_p`, deduce `ptp = λp` and thereby *discover* that `0 < λ < 1`.
`λ` is ours to choose: for self-adjoint `a` in the commutant with `h(a) = 0`,
take `t = μa + ½` with `μ = (4(‖a‖+1))⁻¹`, so `¼ ≤ t ≤ ¾` and
`φ_t(1) = μh(a) + ½h(1) = ½φ(1)` **directly**.  Then `2φ_t`, `2φ_{1-t}` are
ncp (157VI `exists_phiT_ncp`) with value `φ(1)` at `1`, ncp-extremity gives
`φ_t = φ_{½1}`, and injectivity of `t ↦ φ_t` (from **157IV**.2) gives
`t = ½1`, i.e. `a = 0`.  A general commutant element is handled by its real
and imaginary parts.  2 ⇒ 3 is the thesis's argument verbatim, on **157IV**.3.

**Reusable output**, all `private` in `Pure.lean`: `smulReal_mono_aux`
(`x ≤ y → r·x ≤ r·y` for real `r ≥ 0` — Mathlib has no `PosSMulMono ℝ`
instance for C\*-algebras), `isLUB_ofReal_smul`, and **`ncpSMul`** (a
nonnegative real multiple of an ncp-map is an ncp-map, with
`ncpSMul_apply`).  `ncpSMul` is the one worth promoting: `NCPLe` and
`ncpInterval` quantify over *bundled* ncp-maps, so scalar multiples are
needed by anything that feeds a convex combination to **157IV**.3, and the
zero ncp-map (`ncpSMul 0`) is what makes `NCPLe` reflexive and hence turns
`paschke_correspondence_embedding` into injectivity of `t ↦ φ_t`.

### The next gate

**155II `ksgns`** is now the whole of `Paschke.lean` (a KSGNS construction,
independent of the Paschke chain).  In `Pure.lean` the remaining ten are
still rooted in three places, unchanged: **169IV** `standard_corner_dils`
and **169X** `dils_stand_filter` (both cited to proc.tex, which is off this
import path), and **171II** `paschke_corner` (which additionally needs
`cceil_sum`, `surjective_nmiu`, and `𝒜p` as a self-dual Hilbert
`p𝒜p`-module).  `172XII` `ncp_extreme_comp` remains blocked on 172X, which
is blocked on 171II.

Unchanged: **162II `total_mv_order`** is still the only self-contained item
outside the Paschke chain; **165VI** is still blocked outside the directory
on `tensor_characterization`; the five known-false items and **164II.2b**
(QUESTIONS D6) stand.
