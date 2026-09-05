# thesis-B — sampled re-audit of `ok` rows, 2026-09-05

Assignment: every row of `docs/audit/SAMPLE-2026-09-05.md` whose file starts
with `bdils-` or `beff-` — 77 rows across seven CSVs, re-derived from
`dils.tex`, `eff.tex`, `proc.tex`, `vn.tex`, `bsols.tex`, `asols.tex` and
`berr.tex` against the Lean.  The rows' own notes were used only as a hint
about where to look.  READ-ONLY pass: nothing in the tree was changed.

**confirmed 72 / defect 5 / unsure 0** (defect rate 6.5%).

No `stmt=ok` grade was found wrong except one, 224VI `su_pure_state_iso`.
The other four defects are all in the `proof` column and all one shape:
`faithful` recorded where the print gives no argument for the claim the
declaration carries.

## bdils-hilbertmodules-selfdualcompletion.csv (16 / 0 / 0)

- CONFIRMED — 142VII `IsBSesquilinear` (line 18)
- CONFIRMED — 143III `norm_adjoint_le` (line 23)
- CONFIRMED — 144I `hilbmod_ordersep` (line 32)
- CONFIRMED — 147II `dils_uniform_spaces_basics_2` (line 54)
- CONFIRMED — 147II `dils_uniform_spaces_basics_4` (line 56)
- CONFIRMED — 148III `ultranormcontstruct_add_unTendsto` (line 66)
- CONFIRMED — 149V `mod_bessel` (line 83)
- CONFIRMED — 149VII `bddUnComplete_of_selfDual` (line 86)
- CONFIRMED — 149VIII `exists_isONBasis_of_bddUnComplete` (line 92)
- CONFIRMED — 149IX `unComplete_of_isONBasis` (line 93)
- CONFIRMED — 149IX `unSeminorm_sum_smul_sq` (line 94)
- CONFIRMED — 150XI `IsCompatExt` (line 117)
- CONFIRMED — 150XII `isCompatExt_range` (line 124)
- CONFIRMED — 150II `BInner.ulift` (line 131)
- CONFIRMED — 152III `ba_isBoundedBSesq` (line 134)
- CONFIRMED — 152VIII `hilbmod_adjoint_exists` (line 136)

Closest calls, all judged defensible: 142VII adds two ℂ-scalar clauses the
Definition (dils.tex:1476) does not list, but they are the file-wide `BInner`
encoding convention and free over unital 𝒷; 143III carries an extra
`‖T‖ = 0` branch because 143II.1's bound is strictly positive, a gap the
thesis skips, with every printed step still present; 148III states only the
net form of the Corollary, the sibling `ultranormcontstruct_add` (line 63)
carrying the uniform-continuity form under the audit's sibling rule; 152VIII
delivers a *continuous* adjoint where the print asks only for a linear one,
which is equivalent under the print's hypotheses plus the `berr.tex`
"T bounded" erratum.  `mod_bessel`'s DISP attribution is loose — Bessel is
printed at dils.tex:2385 inside 149VIII, not 149V — but that is not a
stmt/proof column.

## bdils-paschke-stinespring.csv (2 / 0 / 0)

- CONFIRMED — 138VIII `kraus_decomposition` (line 68)
- CONFIRMED — 139I `StinespringDilation.Minimal` (line 71)

138VIII's one deviation is the justification of ultraweak convergence: bsols
cites ultraweak continuity of `ad_V`, the Lean uses monotone convergence to
the LUB then linearity, which is encoding-forced because `conjOperator V₀`
crosses algebras and `ad_normal` does not apply.

## bdils-pure-beff-states-effectalgebras.csv (8 / 2 / 0)

- **DEFECT proof** — 94II.8 `cornerSet.restrictNP` (line 8): proc.tex 94II
  (`corner-vna-basic`, proc.tex:194) is an **Exercise** with no Proof block
  and no solution in `asols.tex`/`bsols.tex`; clause 8 prints only the
  instruction "Deduce from this that the restriction of an np-map … is an
  np-map", so there is no printed argument to be faithful to.  proof: should
  be `none`.  Cf. `Theses/B/Dils/Pure.lean:424`.  (The weaker of the two
  calls: the exercise does name the derivation, and the Lean does compose ω's
  normality with the corner inclusion's, so a defence of `faithful` exists.)
- **DEFECT proof** — 81VI `sfilter_bipos` (line 30): vn.tex 81VI
  (`sequential-douglas`, vn.tex:5480) is an Exercise with no proof and no
  solution, and the Lean is a two-line corollary of the sibling
  `sequential_douglas_2` that does **not** follow the exercise's own printed
  hint (factor through `√a`).  proof: should be `none`.  Cf.
  `Theses/B/Dils/Pure.lean:1558`.
- CONFIRMED — 171II `cornerLeft` (line 51)
- CONFIRMED — 172II `NCPExtreme` (line 63)
- CONFIRMED — 190II.2 `scalEffectMonoid` (line 74)
- CONFIRMED — 192VII `stat_mconvex` (line 129)
- CONFIRMED — 193IV.2 `MConvex.deriv_mu_step` (line 143)
- CONFIRMED — 174II `PCM` (line 166)
- CONFIRMED — 175V.8 `eabasics_perp_iff_le_orth` (line 197)
- CONFIRMED — 179III.1 `ea_equiv_emod_two, eaToEModTwo, eModTwoToEA` (line 240)

Both defects are the **same systematic class, and the A CSVs already grade
the identical thesis points the other way**: `avn-division-normalfunctionals.csv:75-77`
grades all three 81VI renderings `none` ("Exercise, no thesis proof"), and
`aproc-measurement.csv:15` grades `corner_vna_basic_8` — the same clause 8 —
`none`, while this B CSV grades 94II.5, 94II.6, 94II.8 and 81VI `faithful`.
If the author wants one ruling rather than two rows, the question is whether
an exercise's hint or "deduce from this" counts as a printed argument; the A
CSVs say no, except at 94II.4 where an explicit `(Hint: …)` is actually
followed.

Also flagged, not filed: `cornerLeft` (line 51) is a plain `Submodule`
definition graded `faithful`; 171II does print a proof and the declaration
sits on its route, but the print never argues the closure obligations.  It is
the sloppiest surviving grade in this file.

## bdils-selfdual-kaplansky.csv (11 / 0 / 0)

- CONFIRMED — 159III `mketbra_rules` (line 5)
- CONFIRMED — 149VIII `exists_max_orthonormal_ext` (line 18)
- CONFIRMED — 161II `hilbmod_el2, hilbmod_el2_selfDual, hilbmod_el2_iso` (line 27)
- CONFIRMED — 161II `L2Sub` (line 30)
- CONFIRMED — 161II `exists_l2_iso_punit` (line 37)
- CONFIRMED — 165III `vnTensor_mul_uliftComplex` (line 54)
- CONFIRMED — 9X `le_ofReal_smul_one` (line 56)
- CONFIRMED — 33II `gram_nonneg` (line 58)
- CONFIRMED — 166II `ultranorm_continuity_ext_tensor` (line 94)
- CONFIRMED — 158V `inv1p` (line 117)
- CONFIRMED — 158II `kaplansky_weak_of_commutative` (line 123)

Two note-level imprecisions, not grade defects: `inv1p`'s doc comment
(`Kaplansky.lean:191-194`) cites dils.tex:4213, the `kaplansky-splitting`
display, where the bounds it means are at dils.tex:4221, and it claims
`0 ≤ b * inv1p b ≤ 1` is available when only `inv1p_nonneg`/`inv1p_le_one`
exist standalone; rows 5 and 26 give bsols ranges for ϑ that disagree with
`hilbmod_el2_iso`'s doc comment (the solution's ϑ runs bsols.tex:1099-1114).

## beff-dagger-diamondamp.csv (14 / 0 / 0)

- CONFIRMED — 215III `dagger_theorem` (line 9)
- CONFIRMED — 216V `asrt_iso` (line 12)
- CONFIRMED — 217III `dagger_prime_basics_iso` (line 27)
- CONFIRMED — 219II `dagger_iso_chi` (line 41)
- CONFIRMED — 219XI `pureDagger_asrt_comp` (line 52)
- CONFIRMED — 220II `pureDagger_diamond_adjoint` (line 57)
- CONFIRMED — 220II `dagger_thm_sufficiency, dagger_thm_sufficiency'` (line 59)
- CONFIRMED — 221IV.4 `dils_abstract_basics_4` (line 65)
- CONFIRMED — 221IV.5 `dils_abstract_basics_5` (line 66)
- CONFIRMED — 207III `diamond_adjunction` (line 83)
- CONFIRMED — 207VI.5-6 `diamond_functor_push` (line 93)
- CONFIRMED — 210II `sharp_ceil` (line 109)
- CONFIRMED — 211VII `prop_corr_zeta_pi` (line 114)
- CONFIRMED — 212I `zeta_asrt_quot` (line 123)

Closest calls: 215III's printed "proof" (eff.tex:5326-5329) is only a forward
reference to the two halves, but it is a real Proof block and the Lean proof
is exactly that split, so `faithful` rather than `none` — calibrated against
219V `dagger_of_fg`, a Corollary with no Proof block at all, graded `none` in
the same file.  217III cannot use the solution's `ζ₁ = π₁ = asrt₁ = id`
because `comprObj 1 ≠ X`, so it builds the standard-form iso as
`π_{⌈1∘α⌉} ≫ α ≫ ζ_{IM α}` — typing-forced, same computation, arguably
`mild` under a strict reading but well below the `mild` bar used elsewhere in
these CSVs.  221IV.5 proves purity of `ξ ≫ h`, a step the print omits
entirely and that the `221IV.5/.6/.7` ERRATA row already records as a hole in
the text.

## beff-effectus-quotients.csv (7 / 1 / 0)

- CONFIRMED — 180VI `Par.category` (line 3)
- CONFIRMED — 181XV `tot_isPullback_kappa` (line 25)
- CONFIRMED — 197III `quotObj, quotMap, isQuotient_quotMap` (line 53)
- CONFIRMED — 197V.4 `quotient_basics_4` (line 57)
- CONFIRMED — 199VII.1 `compr_basics_1` (line 68)
- CONFIRMED — 199VII.6 `compr_basics_6` (line 73)
- CONFIRMED — 202I.2 `FaithfulMap, faithfulMap_iff` (line 79)
- **DEFECT proof** — 204V `lattice_compr` (line 97): `lattice-compr`
  (eff.tex:4353) is a bare Corollary — parsec 2040 point 50 runs five lines
  and closes with no Proof point, there is no `bsols.tex` solution and no
  erratum — so there is no printed argument for the Lean to follow.  proof:
  should be `none`, not `faithful`; the derivation via 204III
  `im_cotuple_sup` plus 203XII `img_of_compr` is ours.  Cf.
  `Theses/B/Eff/Quotients.lean:1393`.  This is exactly the regrade the tree
  already made on 2026-09-04 for 216IX `dagger_of_iso_adjoint`.

## beff-vnexamples.csv (14 / 2 / 0)

- CONFIRMED — 98X `exists_faithful_unital_ncp_not_bijective` (line 7)
- CONFIRMED — 189aII.1 `effectus_ous, OrderUnitSpace, OUS, OUSMap, …` (line 15)
- CONFIRMED — 189aIII `effectus_eja, EuclideanJordanAlgebra, EJAObj, …` (line 17)
- CONFIRMED — 190IV.3(c) `ch_pred_clopens, …, ch_no_separating_predicates` (line 25)
- CONFIRMED — 190V `nonUnitalNonAssocCommRing, …, eja_exists_state_ne_zero` (line 27)
- CONFIRMED — 190V `ejaOpHasTerminal, …, eja_stat_state` (line 28)
- CONFIRMED — 224VI `su_corner_iso, su_ncp_scalar_real` (line 77)
- **DEFECT stmt** — 224VI `su_pure_state_iso, su_pure_state_classification`
  (line 81): both the Exercise (eff.tex:7201) and the solution
  (bsols.tex:3357) state the opening task for **"any non-zero pure map
  `f : 𝒜 → ℂ`"**; `su_pure_state_iso` (`Theses/B/Eff/VNExamples.lean:7021`)
  and its corollary `su_pure_state_classification` (:7101) carry only
  `IsPureMap f` and no `f ≠ 0`, and the omission is real rather than
  cosmetic — the printed route needs it (it goes through the minimal
  projection `p = ⌊a⌋`, which is why the *sibling* `su_pure_state_minimal`
  (line 78) does carry `f 1 ≠ 0`), while ours replaces that step with
  `carrier_miu` and so proves the `f = 0` case too (trivial `K`, `𝒞 = 𝒜`).
  stmt: should be `stronger`, not `ok`.  Adjacent, outside the sample: line
  80 `su_pure_state_rep` drops the same hypothesis.
- **DEFECT proof** — 224VI `suPq, suPq_apply, su_isFilter_suPq,
  su_isQuotient_suPq, su_isPure_suPq, su_dagger_suPq, su_isPure_suPinl`
  (line 84): the stage this bundle realises is a bare assertion in the
  solution — "write `p` … for the regular coprojection `(T,c) ↦ T`, which is
  corner with `p†(T) = (T,0)`" (bsols.tex:3407-3409), with no argument
  whatever — while the Lean argues it in full over ~90 lines (filter ⇒
  quotient by 197IV ⇒ pure, then the dagger by 216VII via
  `su_dagger_of_quotient`).  proof: should be `none`, not `faithful`.  Cf.
  `Theses/B/Eff/VNExamples.lean:7555-7676`.  (The `stmt=ok` half stands: the
  print's word "corner" is never literally stated in Lean, only purity plus
  `dag suPq = suPinl`, but corner = dagger of a filter and the filter side is
  proved.)
- CONFIRMED — 224VI `su_minimalProjection_prod, su_minimalProjection_rk1,
  su_op_apply_eq_zero, suOb` (line 85)
- CONFIRMED — 225VI `pred_sea_s1_s2_s3` (line 99)
- CONFIRMED — 226IV.2 `IsExactMap` (line 102)
- CONFIRMED — 227II.3 `IsKerPush, IsKerPull, Kern.ker, Kern.push, …` (line 109)
- CONFIRMED — 227III.1 `exactAt_iff` (line 113)
- CONFIRMED — 227III.3 `Kern.IM_of_isKerPush, …, nsb_IM_kerPull` (line 115)
- CONFIRMED — 228II `snake_lemma` (line 120)

Closest calls: 226IV.2's printed first sentence — the *existence and
uniqueness* of the `g` with `f = ker(cok f) ∘ g ∘ cok(ker f)` — is asserted
nowhere in `Comparisons.lean`, `IsExactMap` existentially quantifying the
kernels, cokernels and `g` instead; that is equivalent to the printed notion
(cokernels epi, kernels mono, so `g` is unique), so `ok` holds and the
unstated well-definedness sentence is a residue, not a wrong grade.  228II
`snake_lemma` is borderline `faithful` against `mild`: the tree omits the
cube's right face (`v`, `h'`, ERRATA.md:118 — printed work that is not
needed) and substitutes the opening step of eff.tex:8074 (ERRATA.md:120 — the
printed step is wrong), but the two printed chains (eff.tex:8012, 8052) are
followed ingredient for ingredient and the two "dual argument" cases are
unprinted, so `faithful` is defensible.  227III.1's statement is the
`berr.tex` `eff-dagger-conc-ex`-corrected form (`⌈1∘g⌉`, not `⌈1∘f⌉`), which
`eff.tex` itself now carries.

## What the number says

Five wrong grades in 77 `ok` rows — **6.5%**, against 11% on the smaller
2026-09-04 B sample.  The shape is stable across both samples and is almost
entirely one thing: **`proof=faithful` recorded where the print gives no
argument for the claim the declaration carries** (4 of 5 here; 4 of 5 there).
Three sub-shapes, in decreasing order of how mechanically they could be
swept:

1. *Exercises with no solution* (94II.8, 81VI).  Systematic, and the A CSVs
   already grade the identical thesis points `none` — this is an
   inconsistency between the A and B columns, not a hard judgment.
2. *Bare Corollaries and Examples with no Proof point* (204V).  The tree
   already made exactly this regrade for 216IX on 2026-09-04.
3. *A step asserted in passing inside an argued solution* (224VI stage 4).
   The only one needing real judgment, since the enclosing point does print
   an argument.

The single `stmt` defect (224VI `su_pure_state_iso`) is a dropped "non-zero"
hypothesis, the `stronger` class — the same shape as the 113II precedent
recorded in `docs/STATEMENT-AUDIT.md`.

No `stmt=ok` grade in this sample was found `weaker`, and no row was left
`unsure`.

