# `Theses/A/VN/` — full survey of the remaining `sorry`s (updated session 73)

**Headline count: A/VN has 8 code `sorry`s** after session 73 (was 11).
Per file, compiler-counted (`declaration uses 'sorry'` warnings, *not* grep),
each paired with an error count of **0**:

| file | sorries |
|---|---|
| `Basic.lean` | **4** |
| `Projections.lean` | **1** |
| `Division.lean` | 3 |
| `NormalFunctionals.lean` | **0** |
| `Completeness.lean` | **0** |
| **total** | **8** |

(Every file compiles with **0 errors**; counts are compiler-counted.)

Refresh with (bypasses another agent's `lake build` lock):

```sh
LP=".lake/build/lib/lean"; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
for f in Basic Projections Division NormalFunctionals Completeness; do
  echo -n "$f: "; env LEAN_PATH="$LP" lean Theses/A/VN/$f.lean 2>&1 |
    grep -c "declaration uses"
done
```

> **Session 73 headline — the ERRATA 69III repair survives formalization, and
> `Basic.lean`'s two remaining self-contained items fall.**  Closed, all
> `#print axioms`-clean: **69II** `weakly_closed_ideal` (`Projections.lean`,
> now down to one), **43II**.11 `vn_counterexamples_11` — the last of the nine
> 43II counterexamples — and **45I**.2 `normal_not_us_cont` (`Basic.lean`).
>
> * **The powers-not-roots repair filed at ERRATA 69III holds**, with two
>   simplifications: the binomial expansion is unnecessary
>   (`1 − (1−a)ⁿ = (∑_{i<n}(1−a)^i)·a`, so ideal membership is one step), and
>   `1 − (1−a)ⁿ ↗ ⌈a⌉` is **not** a variant of 56I but has its own short
>   proof, now public as **`ceil_isLUB_one_sub_pow`**: with `p = ⌈a⌉`,
>   `x = p − a` one has `(1−p)x = x(1−p) = 0`, hence
>   `(1−a)^{n+1} = (1−p) + x^{n+1}` and `1 − (1−a)ⁿ = p − xⁿ`, and `⌊x⌋ = 0`
>   by leastness of `⌈a⌉`, so `xⁿ ↘ 0` by **56VI** `vna_floor`.  A *third*
>   circularity of the same shape was found further down the printed proof
>   ("self-adjoint by scaling … then real and imaginary parts" needs
>   `a⁺ ∈ 𝒟`); the Lean proof routes through `⌈a*a⌉, ⌈aa*⌉ ≤ c` instead.  See
>   PROVING-LOG session 73 and the updated ERRATA row.
> * **43II.11 is much cheaper than "unbounded functional + Riesz" suggests.**
>   The index type is `Finset ℓ²` (so `atTop` is directed and `NeBot` for
>   free); `f` comes from `Module.Basis.span` + `Basis.constr` +
>   `LinearMap.exists_extend`, with no Hamel basis of `ℓ²`; and ultraweak
>   Cauchyness is *eventual constancy*, not an estimate — by **39IX**
>   `bh_np`, `ω(|e⟩⟨v|) = ⟨v, z_ω⟩` for the single vector
>   `z_ω = ∑ₙ⟨yₙ,e⟩yₙ`, so `ω(|e⟩⟨x_S|) = f(z_ω)` for every `S ∋ z_ω`.  The
>   non-convergence half needs **no polarisation**: testing at `w = eₙ + e₀`
>   gives `⟨w,Aw⟩ = n` against `|⟨w,Aw⟩| ≤ 4‖A‖`.
> * **45I.2 needs no new carrier after all.**  `lp` already carries `Star`
>   (`lp.star_apply`, `NormedStarGroup`, `StarModule`), so `J := star` is the
>   conjugation; `transL2 T := J T* J` is built with `LinearMap.mkContinuous`,
>   is `∗`-compatible and hence **involutive**, and *normality is then free* —
>   a monotone involution is an order isomorphism.  Non-continuity is
>   `vn_counterexamples_4_ket`/`_bra` re-used verbatim, since
>   `transL2 |0⟩⟨n| = |n⟩⟨0|`.  All private, in `Basic.lean`'s new
>   `section Transpose`.

> **Session 70 headline — `gns_normal` was never [L], and `Projections.lean`
> is down to two.**  Closed, all `#print axioms`-clean: **48III**
> `gns_normal`, **53III** `vn_spectrum_extremally_disconnected` (`Basic.lean`);
> **56XVII**.3 `ceil_supremum_3`, **58IV** `ceil_sequential_product`,
> **59VII**.1–2 `hilb_ceil_1`, **59VII**.3 `hilb_ceil_2`, **62I** `ncpsu_floor`
> (`Projections.lean`).
>
> * **48III re-costed at ~55 lines, not "large".**  Mathlib's
>   `PositiveLinearMap.gnsStarAlgHom` *is* the GNS representation of a single
>   `ω`, and everything else was already in `Basic.lean`: `gnsVec`,
>   `gnsRep_gnsVec`, `gnsVec_inner`, `gnsVec_denseRange` (which gives both the
>   cyclicity clause and the separating-vectors hypothesis of
>   `starAlgHom_preservesDirSups_of_vectors`), `conjNP` for the np-functional
>   `⟪η_ω(b), ϱ(·)η_ω(b)⟫ = b*ω`, and the `bas.repr.conjStarAlgEquiv` transport
>   to `ℓ²(w)` copied verbatim from `ngns`.  The family block `gnsRepFam` was
>   **not** needed — the singleton case is shorter without it.
> * **53III is the thesis's own proof**, one obstacle removed: `C(spec 𝒜, ℂ)`
>   is a von Neumann algebra by `ngelfand_vna` (session 68), so
>   `D = {f : 0 ≤ f ≤ 1, f = 0 off U}` — the cofinal positive part of the
>   thesis's `{f ≤ 𝟙_U}`, chosen so that directedness is a pointwise `max` —
>   has a supremum, and Urysohn (`exists_continuous_zero_one_of_isClosed`,
>   `characterSpace` being compact Hausdorff hence normal) pins it to
>   `𝟙_{closure U}`.  `closure U = (⋁D)⁻¹{Re > ½}` is then open.  **An erratum
>   fell out**: the second Urysohn paragraph says "let `y ∈ spec(𝒜)\U`" where
>   it must say `y ∉ closure U`, or the `f` it asks for does not exist (filed).
> * **59VII is 63III.2's vocabulary, reused twice**, as predicted: `⌊T⌉` is
>   `starProjection ((range T).topologicalClosure)` and `⌈T⌋` is
>   `starProjection ((ker T)ᗮ)`, each identified through `ceill_basic_2` /
>   `ceill_basic_1` (least projection with `pT = T` resp. `Tp = T`) and
>   `proj_le_iff`; part 3 is the same move at `V = ker (T − 1)`, whose
>   `HasOrthogonalProjection` instance needs `ContinuousLinearMap.isClosed_ker`
>   fed to `completeSpace_coe` by hand.
> * **58IV is four lines of thesis text and about forty of Lean**, given 58II
>   `floor_difference` and 57I `floor_sequential_product`: `√p = p` for a
>   projection (`CFC.sqrt_eq_iff`) turns 57I into `p ∩ ⌊b⌋ = ⌊pbp⌋`, whence
>   both `p ∩ r^⊥ = p − r` for `r ≤ p` and `⌊p q^⊥ p⌋ = p ∩ q^⊥`; De Morgan
>   `p^⊥ ∪ q = (p ∩ q^⊥)^⊥` is three applications of `projSup_eq`.
> * **62I needed one genuinely new reusable piece**, now `private` in
>   `Projections.lean`: **`preservesDirInfs`** — *a normal positive map
>   preserves filtered infima* — proved by running normality on `−D`.  There
>   was nothing of this shape anywhere in `Theses/`.  With it 62I is the
>   thesis's proof verbatim (`⌊f(a)⌋ = ⌊f(a²)⌋` by `ceil_floor_basic_3` plus
>   `cp-cs`, iterate, then `⋀ₙ a^{2ⁿ} = ⌊a⌋` from `vna_floor`).  Note
>   `‖f(1)‖ ≤ 1` cannot go through `CStarRing.norm_one`, which needs
>   `Nontrivial B`; `‖1‖ = ‖1‖²` gives `‖1‖ ≤ 1` unconditionally.
> * **56XVII.3** is the thesis's `1, ½, ⅓, …` at `aₙ = (n+1)⁻¹·1`: `⌈aₙ⌉ = 1`
>   by `ceil_smul`, `⌈0⌉ = 0`, so `⌈·⌉` is discontinuous at `0`; the floor half
>   is then free, since `⌈a⌉ = 1 − ⌊1 − a⌋` (`ceil_floor_basic_1`) and
>   `a ↦ 1 − a` is a continuous self-map of `[0,1]_𝒜`.  No hand-built
>   `Nontrivial` witness was needed — `1 ≠ 0` is the whole of it.

> **Session 68 headline — the two "reduces to itself" gates fall, and both
> to the same device.**  In `Basic.lean`: **45I**.1 `us_cont_normal`,
> **47IV**.3 `vn_products_ncpsu`, **49IV**.2 `mn_vna_2`, **49IV**.3
> `mn_vna_3`, **53II**.1 `ngelfand_vna` and **53II**.2 `ngelfand_normal`; in
> `Projections.lean`, **63III**.2 `carrier_ad_operator`.  All seven are
> `#print axioms`-clean.
>
> * **45I**.1 really was a few lines, but not by copying
>   `preservesDirSups_of_continuousOn_effects`: that proof is now stated once,
>   as the private `preservesDirSups_of_continuousOn_effects_core`, with the
>   **finest** source topology (ultrastrong) and the **coarsest** target
>   topology (ultraweak) of its two applications.  **44XV** (2) ⇒ (3) and
>   **45I**.1 are then one-line corollaries — coarsen the source with
>   `ultrastrong_le_ultraweak` resp. coarsen the target with the same lemma.
>   Only two `have`s inside the core changed (`hbase`/`hnet` now go through
>   **44XIV** `vna_supremum_uslimit` and `omegaNorm_smul` instead of
>   `vna_supremum_uwlimit`).
> * **`mn_vna_3`'s circularity is breakable, and the key is a binder.**
>   Unwinding `PreservesDirSups (M_N f)` directly does reduce to itself,
>   because `M ↦ Mᵢⱼ` is not monotone.  But **49IV**.2' `mn_vna_2'`
>   ("convergence in `M_N(𝒜)` is entrywise") is stated for an **arbitrary
>   filter**, so it applies to the *identity net on `𝓝 M₀`* and yields
>   ultraweak **continuity**, not normality; **44XV** `p_uwcont` (1) ⇒ (3)
>   converts that back to normality, `M_N f` being positive by complete
>   positivity of `f`.  The same three-step device (identity net → entrywise →
>   `p_uwcont`) proves **49IV**.2 as well, whose map is `matForm a b`.  One
>   new public helper, `uwTendsto_mul_left_right` (the ultraweak twin of the
>   existing `usTendsto_mul_left_right`, three lines from
>   `continuous_ultraweak_conj`).  **`mn_vna_3` is what B/Dils routed around
>   through double polarisation — that detour can now be removed.**
> * **53II** needed one new reusable piece:
>   **`vonNeumannAlgebra_of_starAlgEquiv`**, "Kadison's definition transports
>   along a ∗-isomorphism" (~45 lines; both clauses are order-theoretic and
>   `starAlgEquiv_preservesDirSups` + `compNP` do the work).  `ngelfand_vna`
>   is then one line at `gelfandStarTransform A`, and `ngelfand_normal` is
>   *literally* `starAlgEquiv_preservesDirSups (gelfandStarTransform A)` — it
>   was never harder than that.  Note the lemma confines both algebras to one
>   universe, as everything in `section StarAlgHomAux` does; that is enough
>   here because `C(characterSpace ℂ A, ℂ)` lands in `A`'s universe.
> * **47IV**.3 is `cstar_product_4` (**34VI**.4, `A/CStar/Matrices.lean`) plus
>   pointwise normality — the same assembly `A/Proc/Duplicators.lean`'s
>   `exists_freeMonoidUnitCpsu` had already written out inline, with a comment
>   saying 47IV.3 itself "is not needed".  **The von Neumann hypotheses on the
>   `𝒜ᵢ` are not used** (deliberate `unusedSectionVars` warning, as for
>   `vn_products_nmiu`).
> * **63III**.2 is the thesis's `carrier_ad` argument transported: `p` is the
>   orthogonal projection onto `closure (range T)` (Mathlib's
>   `Submodule.starProjection` of `(LinearMap.range T).topologicalClosure`,
>   which is a star projection and has `HasOrthogonalProjection` by
>   `inferInstance`), `T*p^⊥T = 0` because `p^⊥T = 0`, and minimality is
>   `‖q^⊥Tx‖² = ⟪x, T*q^⊥Tx⟫ = 0` plus closedness of `ker q^⊥`.  Pure Hilbert
>   plumbing, ~55 lines, no new von Neumann theory.
>
> **Session 57 headline — `Projections.lean`'s last chain is finished, and
> eight of the nine 43II counterexamples fell.**  **66IV**.4
> `ultracyclic_basic_4`, **70II** `central_projection_central_carrier` and
> **70III** `cvn` are all proved.  70II turned out **not** to need 66IV.4 (the
> thesis's own hint runs the same Zorn argument directly on the *central*
> carriers), and 70III does **not** need 54XI — the Lean statement is the
> reduction `1 = ∑ᵢ ⌈⌈ωᵢ⌉⌉` with each `ωᵢ` faithful on its corner, and in a
> commutative algebra `⌈⌈ω⌉⌉ = ⌈ω⌉`, so faithfulness is `ceil_functionals_lemma`
> plus carrier leastness.  All three follow **83V** `cceil_sum`'s Zorn template.
>
> In `Basic.lean`, **43II** parts 2a, 2b, 4a, 4b, 4c, 5, 6 and 6c are proved
> (only part 11 is left).  The enabling helpers, all public and in
> `Basic.lean`'s `section BH`, are `omegaNorm_vectorNP` (moved up from
> `Completeness.lean`), `hasSum_omegaNorm_sq` (`‖T‖²_ω = ∑ₙ‖Txₙ‖²` from
> **39IX**) and `ultrastrong_continuous_apply` (`a ↦ ax` is ultrastrongly
> continuous — the ultrastrong topology is finer than the strong one, which is
> what turns part 5 into sequential compactness in `ℓ²`).  Mathlib's Tannery
> theorem `tendsto_tsum_of_dominated_convergence` is the dominated-convergence
> step.  In `Division.lean`, **79VI**.5 `pseudoinverse_basic_2'_5` is proved.
>
> **Two cleanups landed.**  (i) `Basic.lean`'s `GNSSum` block is now stated for
> an arbitrary family `F : ι → NPFunctional A` (`gnsHilbFam`, `gnsRepFam`,
> `gnsElemVecsFam`, `gnsRepFam_normal`); `gnsHilb`/`gnsRep` are its instance at
> `F = id` and `NormalFunctionals.lean`'s `gnsHilbOn`/`gnsRepOn` its instance at
> `F = Subtype.val` — 161 lines of duplication deleted.  (ii)
> `preservesDirSups_of_continuousOn_effects` (44XV (2) ⇒ (3)) is no longer
> `private`, and `preservesDirSups_of_continuousOn_effects_functional` is now a
> four-line corollary of it (103 lines deleted).  The obstacle recorded in
> session 56 was misdiagnosed: `ℂ` *does* carry a `VonNeumannAlgebra` instance
> (`Basic.lean:646`) and the section variable is `Type*`, not `Type u`; the one
> real gap was `ultraweak ℂ = ` the usual topology, now proved as
> `ultraweak_complex`.
>
> **A statement repair (ours).**  `ultracyclic_basic_4`, 70II and 70III wrote
> the index type as `∃ (ι : Type _)`, which auto-bound a *fresh* universe
> parameter — so as stated they asserted the existence of an index type in
> **every** universe, which is false for large `A`.  `Projections.lean` now
> names its universes (`universe u v w`, `{A : Type u} {B : Type v}`) and the
> three statements read `∃ (ι : Type u)` (resp. `Type w` for `cvn`'s `C`), which
> is what `Division.lean`'s `cceil_sum` already did.
>
> **Session 56 headline — `NormalFunctionals.lean` is finished, and with it
> `A/Proc`'s entire external frontier on `A/VN`.**  **86IX**
> `polar_decomposition_of_functional`, **86XII** `uwcont_on_ball`, **87III**
> `predual_complete` and **87VI** `norm_predual` are all proved, by the
> thesis's own arguments.  The enabling piece is that `(A, ultraweak)` is now
> known to be a **locally convex TVS over `ℝ`** —
> `ultraweak_isTopologicalAddGroup`, `ultraweak_continuousSMul`,
> `ultraweak_locallyConvexSpace`, three lines each from Mathlib's `iInf` /
> `induced` lemmas — so Mathlib's Krein–Milman lemma
> (`IsCompact.extremePoints_nonempty`) applies to the ultraweakly compact unit
> ball (**77III**).  Four other reusable helpers landed with them:
> `exists_extremePoint_max`, `posFunctional_mul_eq_zero` (Cauchy–Schwarz:
> a positive functional killing a projection kills every product with it),
> `preservesDirSups_of_continuousOn_effects_functional` (**44XV** (2) ⇒ (3)
> for functionals — `Basic.lean`'s version is `private` *and* needs a target
> in `Type u` with a `VonNeumannAlgebra` instance, which `ℂ` has not), and
> `plm_real_smul`.  In `Projections.lean`, **67II**.3 `central_examples_3`
> and **67IV**.1 `central_projections_sums_1` also fell.
>
> **Session 54 headline — the 690–900 mis-transcription is repaired and
> both of its consequences are closed.**  `CentreSeparating` rendered
> *neither* item of **69IX** (QUESTIONS D4, now deleted).  The two faithful
> notions were added beside it: **`CentreSeparatingConj`** = cstar.tex
> **21II**.4 = 69IX item 1, *defined as* `Theses.A.CStar.CentreSeparating`
> applied to `Ω` (the 21II.4 rendering already in `A/CStar/Positive.lean` —
> not duplicated), and **`CentreSeparatingCentralProj`** = 69IX item 2.
> `vn_center_separating` is now a genuine three-way TFAE and is **proved**,
> as is **90II**.2 `vn_center_separating_fundamental_2`, which therefore
> **unblocks B/Dils 159IX and 164II.2b**.  90II.1/.2 now take the thesis's
> hypothesis (`CentreSeparatingConj`).  The old `CentreSeparating` is kept
> under its name, retitled as the auxiliary central-positive notion it
> actually is, because `A/Proc/Tensor.lean` states eight results with it —
> all eight mean `CentreSeparatingConj` and are to be migrated.
>
> **Session 53 headline — `Completeness.lean` is finished and the 690 chain
> is half open.**  **77V** `vn_extension` *and* `vn_extension_norm` are proved,
> so **A/Proc's 112XI `tensor_universal_property` is unblocked** (and with it
> 114I, 114II, 116VII).  In `Projections.lean`, **63IV** `cp_comprehension`,
> **69V** `proto_gns_ceil` and **69VII** `gns_ceil` are proved; the core of 69V
> was factored into four private lemmas (`conj_proj_nonneg`, `gns_zero_iff`,
> `omega_conj_cceil_compl`, `cceil_npCarrier_le`), which is what made 69VII
> cheap.  **69IX is now gated on a decision, not on 69VII** — *(that decision
> was taken and 69IX proved in session 54; see the session-54 headline)*.
> All five are
> `#print axioms`-clean.
>
> **Session 50 headline — the 890 chain is finished.** **89XI**.1/.2/.3
> (`functional_permanence_*`) and **89XII** (`functional_extension`) are
> proved and axiom-clean.  The "one 120–150 line lemma" the previous session
> expected (*a square-summable family of vectors defines an np-functional on
> `B(H)`*) **already existed, upstream**: it is **38IV**.2
> `bh_functional_lemma_2` in `A/CStar/TowardsVN.lean`, in the same file as
> its converse 39IX `bh_np`, and fully proved.  89XI.1 is 20 lines on top of
> it.  An arbitrary-index wrapper `exists_sumVectorNP` was added to
> `A/VN/NormalFunctionals.lean` for `A/Proc` (see below).

Classification used below: **[S]** self-contained (all ingredients in the
tree), **[B]** blocked on a named `sorry`, **[L]** cited to the literature or
needs a carrier/development Mathlib lacks, **[F]** known false / parked.

---

## `NormalFunctionals.lean` — 0

**Nothing left.**  86IX, 86XII, 87III and 87VI were proved in session 56 (see
the headline above).  Everything else in the file was already proved, including the whole 880–890 block
(88IV–88IX, 89I–89IX, 89XI, 89XII) **and all of parsec 900**: **90II**.2 was
proved in session 54 through `ϱ_Ω` over the set `Ω` (a copy of `Basic.lean`'s
`GNSSum` block cut down to `Ω`, inserted above 90II; see the note there), 89IX
`normal_functional`, and **72III**.1c `bstaromega_lipschitz` for the passage
from `A` to the ultrastrongly dense `S`.

## `Completeness.lean` — 0

**Nothing left.**  Both halves of **77V** were proved in session 53 (~250
lines, plus six reusable helpers — `uwTendsto_unique`, `UWTendsto.add`/`.smul`,
`continuous_ultraweak_of_npFunctional`, `continuous_ultraweak_smul`,
`isClosed_ultraweak_closedBall`, `uw_map_of_cont` — placed just above them and
usable anywhere in `A/VN` and downstream.)

## `Division.lean` — 3

| point | decl | class |
|---|---|---|
| **84II** | `fdcstar` | [L] Artin–Wedderburn for finite-dimensional C\*-algebras; large |
| **84bIII** | `hereditarilyAtomic_subalgebra` | [S] but real work |
| **84bV** | `ha_equalisers` | [B] on 84bIII only (47V `vn_equalisers` is proved) |

(`pseudoinverse_basic_2'_4` and `div_usc` — both false as printed — have since
been retired with their `sorry`s; see HANDOFF.)

**81VIII**.2 `sequential_quotient_2` is **proved** (it was still listed here
after session 57 and was not).

**Note for the next worker:** 84bV's chief ingredient, "the equaliser of two
nmiu-maps is a von Neumann subalgebra", is 47V and was proved this session,
so 84bV is now only blocked on 84bIII.

## `Projections.lean` — 1

| point | decl | class |
|---|---|---|
| **67IV**.2 | `central_projections_sums_2` | [S] 67IV.1 is proved (session 56); **not** cheap, see below |

**69II** `weakly_closed_ideal` was proved in session 73 (see the headline);
its by-product `ceil_isLUB_one_sub_pow` (`1 − (1−a)^{2ⁿ} ↗ ⌈a⌉` for an effect
`a`) is **public** and sits just above it.

56XVII.3, 58IV, 59VII.1–3 and 62I were proved in session 70 (see the
headline).  **`preservesDirInfs`** — normal positive maps preserve filtered
infima — is now available (private, just above 62I); promote it if anything
else needs it.

**The parsec 690–700 chain is finished.**  69V → 69VII → 69IX → **70II** →
**70III** are all proved (69V/69VII in session 53, 69IX in session 54, 70II and
70III in session 57), as is **66IV**.4.  Two corrections to the earlier notes:
70II is *not* downstream of 66IV.4 — the thesis's hint runs its own Zorn
argument over np-functionals with orthogonal *central* carriers — and 70III
does *not* need 54XI, because our statement of `cvn` is the FIXME reduction
(`1 = ∑ᵢ ⌈⌈ωᵢ⌉⌉`, each `ωᵢ` faithful on its corner) rather than the
`⊕ᵢ L^∞(Xᵢ)` classification itself.

**63III**.2 was proved in session 68 exactly along the route sketched here
(orthogonal projection onto `closure (range T)`, minimality from
`T*q^⊥T = 0 ⟹ q^⊥T = 0`).

**67IV**.2 `central_projections_sums_2` is *not* the cheap sequel to 67IV.1
that the previous note implied.  Uniqueness is easy — if `cᵢ x = 0` for all
`i` then `⌈xx*⌉cᵢ = 0` (`ceil_mul_eq_zero`, the `cᵢ` being central), so
`projSup (range c) ≤ 1 − ⌊x⌉` and `hsum` forces `x = 0`.  **Existence is the
work**: one must build `a = "∑ᵢ bᵢ"` as an ultraweak limit of the finite
partial sums, which are norm-bounded by `sup ‖bᵢ‖` because the corners are
orthogonal, and then use ultraweak compactness of the ball (**77III**,
`Completeness.lean` — *downstream* of `Projections.lean`, so either the
statement moves or the compactness argument is redone).  Cost that before
starting.

Locate by name; line numbers are not recorded.

## `Basic.lean` — 4

| point | decl | class |
|---|---|---|
| **51IX** | `Linfty_vn` | [L] no `L^∞` carrier in Mathlib (FIXME); a construction job, ~400–800 lines, of which the proved 51VII is the last twenty |
| **54XI**.1 | `cvn_faithful_1` | [L] measure on the almost-clopen σ-algebra; large — **and the only A/VN item anything downstream still wants** (it blocks `A/Proc` 127III `duplicable`) |
| **54XI**.2 | `cvn_faithful_2` | [B] on 54XI.1 |
| **54XI**.3 | `cvn_faithful_3` | [B] on 54XI.1 |

48III and 53III were proved in session 70; 51VII.1/.2, **43II.11** and
**45I.2** in sessions 71–73 (see the session-73 headline).

### The 43II counterexamples: eight down, one to go

All of them are estimates of `‖·‖_ω` and `ω(·)` for an **arbitrary**
np-functional `ω` on `B(ℓ²)`.  Since **39IX** `bh_np`
(`A/CStar/TowardsVN.lean`) is proved, every such `ω` is `∑ₙ ⟪xₙ, (·) xₙ⟫` with
`∑ₙ‖xₙ‖² = ω 1 < ∞`, so `‖T‖²_ω = ω(T*T) = ∑ₙ ‖T xₙ‖²`
(`hasSum_omegaNorm_sq`, session 57), and parts 2, 4 and 6 are one
dominated-convergence argument (Mathlib's Tannery theorem
`tendsto_tsum_of_dominated_convergence`) with dominating family `(‖xₙ‖²)ₙ`.
Parts 2a, 2b, 4a, 4b, 4c, 5, 6 and 6c were proved in session 57, and part
**11** in session 73 — **the block is finished**.

**45I**.1 `us_cont_normal` was closed this way in session 68 — see the
headline: the whole proof is now `preservesDirSups_of_continuousOn_effects_core`
(ultrastrong source, ultraweak target) and both 44XV (2) ⇒ (3) and 45I.1 are
one-line corollaries of it.

---

## What `A/Proc` needs from here

**One thing: 54XI.1 `cvn_faithful_1`**, the last A/VN blocker of `A/Proc`'s
**127III** `duplicable` (`Duplicators.lean`).  The note below, written in
session 56, refers to the *tensor* frontier, which is indeed closed.

**As of session 56 the tensor answer is: nothing.**  The three sorries that were
`A/Proc`'s external frontier — 90II.2 (session 55), 87III and 86IX (session
56) — are all closed, and 87VI, which 116III.2 wants for its `≥` half, with
them.  The note below is kept because it records *why* `tensor-2` is
satisfiable.

`111VII`'s condition `tensor-2` (proc.tex:2528) needs, besides 89IX:

> the family `(n,m) ↦ xₙ ⊗ yₘ` is square-summable and defines an
> np-functional on `B(ℋ ⊗ 𝒦)`, restricted to `𝒯` along the inclusion.

All four ingredients now exist:

1. **89IX** `normal_functional` (session 49) for the `xₙ` and `yₘ`;
2. **`exists_sumVectorNP`** (`NormalFunctionals.lean`, session 50) — the
   np-functional attached to a square-summable family indexed by *any* type,
   in particular `ℕ × ℕ`;
3. `sq_summable_tensor`-style square-summability of `(x,y) ↦ f(x)g(y)`,
   already in `A/Proc/Tensor.lean:192`;
4. `VNSub.restrictNP` (`A/Proc/Tensor.lean:1107`) to restrict from
   `B(ℋ ⊗ 𝒦)` to `𝒯`.

So `tensor-2` is **genuinely satisfied** as far as `A/VN` is concerned; what
remains for it is `A/Proc`-local assembly (the identity
`⟪x ⊗ y, (A ⊗ B)(x ⊗ y)⟫ = ⟪x,Ax⟫⟪y,By⟫` and a `tsum` over `ℕ × ℕ`), not a
missing theorem.  Note that `special_tensor` also carries conditions
`tensor-1` and `tensor-3`, which were never blocked on `A/VN`.
