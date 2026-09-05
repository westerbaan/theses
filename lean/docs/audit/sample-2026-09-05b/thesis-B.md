# thesis-B — sampled re-audit of `ok` rows, 2026-09-05 (second draw)

Assignment: every row of `docs/audit/SAMPLE-2026-09-05b.md` whose file starts
with `bdils-` or `beff-` — 70 rows across seven CSVs, re-derived from
`dils.tex`, `eff.tex`, `proc.tex`, `bsols.tex`, `asols.tex` and `berr.tex`
against the Lean.  The rows' own notes were used only as a hint about where to
look.  Graded under `SAMPLE-BRIEF.md` and the 2026-09-05 hint convention at the
end of `docs/STATEMENT-AUDIT.md`.  READ-ONLY pass: nothing in the tree was
changed.

**confirmed 60 / defect 8 / unsure 2** (defect rate 11.4%).

Seven of the eight defects are in the `proof` column, and six of those are one
shape: a grade of `faithful` or `none` that misreads whether the print argues
the clause the declaration carries.  Only one `stmt=ok` was found wrong
(149IIb).

## bdils-hilbertmodules-selfdualcompletion.csv (8 / 2 / 0)

- CONFIRMED — 142III `module_CS` (line 13)
- DEFECT — 143IV `baSubalgebra` (line 25): 143IV is a Proposition whose proof **is** printed at 143V (dils.tex:1600-1608 — "It is easy to see T*+S* is an adjoint of T+S … closed under scalar multiplication, composition and involution … Also the identity 1 … So B^a(X) is a unital *-algebra"), and `baSubalgebra`'s field proofs (`Theses/B/Dils/HilbertModules.lean:729-748`: `add_mem'`, `algebraMap_mem'`, `mul_mem'`, `one_mem'`) run exactly that paragraph; proof: should be `faithful`, not `none` (the sibling row 26 `Ba.instCStarAlgebra` already credits these same field proofs as 143V's argument).
- CONFIRMED — 147I `UnDense` (line 50)
- CONFIRMED — 148III `ultranormcontstruct_smul` (line 65)
- CONFIRMED — 148III `ultranormcontstruct_smul_unTendsto` (line 68)
- CONFIRMED — 149I `IsONBasis` (line 76)
- DEFECT — 149IIb `onbasis_beware_ketbraNat, onbasis_beware_ketbraNat_isONBasis` (line 77): the printed Beware (dils.tex:2182-2222) has an "and vice versa" half of clause 1 (the standard module H_{B(ℓ²)} of landi2012orthogonal §3, a basis in their sense but not in ours) and a whole clause 2 (blecher2004operator's w*-basis, "equivalent to ours"), neither of which is stated anywhere in the tree — `Theses/B/Dils/HilbertModules.lean:2818-2820` says so itself ("What is still not formalised is the *converse* half of the Beware"); stmt: should be `weaker`, not `ok`.
- CONFIRMED — 149XI `selfDual_of_isONBasis` (line 96)
- CONFIRMED — 150IX `unSeminorm_op_smul_sub` (line 109)
- CONFIRMED — 149V `bddUnComplete` (line 127)

## bdils-paschke-stinespring.csv (6 / 0 / 0)

- CONFIRMED — 145I `pVecLin_cp` (line 4)
- CONFIRMED — 154III `PaschkeModule` (line 10)
- CONFIRMED — 154III `existence_paschke` (line 18)
- CONFIRMED — 154III `existence_paschke_2` (line 19)
- CONFIRMED — 157III `phiT` (line 41)
- CONFIRMED — 138II `nmiuNCPaux` (line 63)

## bdils-pure-beff-states-effectalgebras.csv (17 / 5 / 0)

- DEFECT — 94II.5 `cornerSet.instStarOrderedRing` (line 5): proc.tex 940 point 20 (`corner-vna-basic`, proc.tex:194) is an Exercise whose clause 5 ("Show that eAe … is a C*-algebra") prints no proof and no hint — the exercise's only hint is on clause 4 — and `asols.tex` has no solution for it (its `\begin{solution}{parsec-N.M}` labels stop at parsec 340, i.e. cstar.tex only; nothing for proc.tex at all), so proof: should be `none`, not `faithful`.  The same objection applies to sibling rows 3, 6, 7 and 9, while row 4 (`cornerSet.instPartialOrder`, same clause 5) is already filed `none` — the block is internally inconsistent.
- CONFIRMED — 169IV `ncp_eq_zero_ceil` (line 15)
- CONFIRMED — 170II.2 `isCorner_comp_nmiuBij` (line 40)
- DEFECT — 170IV.2 `surjective_nmiu_2_false` (line 44): the thesis prints an argument for 170IV's converse half (bsols.tex:1363, `\begin{solution}{surjective-nmiu}`, second paragraph) and this declaration is the machine-checked **refutation** of it (A=B=CU, z=1, φ=λ·id), so it follows no printed argument at all; proof: should be `none` (`faithful` is impossible, and `route` would misdescribe it — the Lean proves the negation rather than re-routing the claim).
- CONFIRMED — 191VIII `rng_je` (line 94)
- DEFECT — 192III.2 `MConvexComb.mu` (line 104): the declaration is the *definition* of μ (`Theses/B/Eff/StatesPredicates.lean:2768`, `(exists_mu Φ).choose`) and eff.tex:2397 prints μ as a definition with no argument — the solution `exc-dm-effectus` (bsols.tex:1989) proves the monad laws (the `mu_eta`/`mu_mu`/`mu_map`/`mu_map_eta` rows) but never argues that μ(Φ) is a formal M-convex combination, which is all `exists_mu` does; proof: should be `none`, as the audit itself files for the printed definitions at 192II, 192IV, 192V.1 and 192VII.  Line 100 `MConvexComb.map` has the same defect.
- CONFIRMED — 192VII `statSum_mu` (line 123)
- CONFIRMED — 193IV `MConvex.DerivStep, MConvex.Deriv` (line 137)
- CONFIRMED — 193IV.3 `MConvex.deriv_map_rep, MConvex.deriv_of_quot_eq` (line 140)
- CONFIRMED — 194I `aconvalmosteffectus_kappaPullback` (line 154) — grades right; the note's `.lean` line numbers are stale (declaration at StatesPredicates.lean:7318, not :6753; `coprod_inl_injective` :7054 not :6566; `coprodQuot_surjective` :6840 not :6477), which is note imprecision, not a grade defect.
- CONFIRMED — 195IV.2 `exc_divisoid_basics_2` (line 157)
- CONFIRMED — 175II.5 `booleanEffectAlgebra` (line 182)
- CONFIRMED — 175III `prodEffectAlgebra` (line 185)
- CONFIRMED — 175IV `EASansZero` (line 187)
- CONFIRMED — 175V.4 `eabasics_cancellation` (line 193)
- CONFIRMED — 176II `exc_dposet_D4` (line 204)
- CONFIRMED — 176IV `DPoset` (line 205)
- CONFIRMED — 176III `DPoset.dovee` (line 208)
- CONFIRMED — 176III `dposetEffectAlgebra` (line 211)
- DEFECT — 178III.2 `booleanEffectMonoid` (line 229): `eff-monoid-examples` (eff.tex:633) is an *Examples* point; clause 2 (eff.tex:641-647) only exhibits the datum "the Boolean algebra is turned into an effect monoid with x ⊙ y ≡ x ∧ y" and prints no argument for the unit/associativity/distributivity axioms — no hint, no `\begin{solution}{eff-monoid-examples}` in bsols.tex, no erratum — and the Lean's distributivity verification (`Theses/B/Eff/EffectAlgebras.lean:1877-1906`) is entirely its own; proof: should be `none`, not `faithful` (exactly the regrade already applied to the parallel `eaexamples` clauses 175II.1-.6).
- DEFECT — 178III.3 `(instance : EffectMonoid Bool)` (line 232): same point — clause 3 (eff.tex:646-650, "In particular: the two-element Boolean algebra 2 … is an effect monoid with x ⊙ y = x ∧ y") is a bare assertion in an Examples point with no argument, hint, solution or erratum; proof: should be `none`, not `faithful`.
- CONFIRMED — 178V `emond_lemma_for_conv` (line 235)

## bdils-selfdual-kaplansky.csv (10 / 0 / 1)

- CONFIRMED — 159II `mketbra` (line 2)
- CONFIRMED — 159IV `ketbra_ultraweakly_dense` (line 10)
- CONFIRMED — 160X `selfdual_gramschmidt` (line 23)
- CONFIRMED — 161II `delta_isONBasis` (line 35)
- CONFIRMED — 149VIII `exists_max_orthonormal_orthoCompl` (line 48)
- UNSURE — 163II `selfdual_compl_defining_unique` (line 51): the statement is universe-monomorphic in the carrier (`SelfDualCompletion.{u,v,v}`, `Theses/B/Dils/SelfDual.lean:5500`), so it does not compare the canonical `dils_completion` — which is `SelfDualCompletion.{u,v,max u v}` (`SelfDualCompletion.lean:2158`) — against another completion when `u > v`; whether that restriction makes `stmt=ok` wrong is a judgement the sibling `selfdual_compl_defining_dense` records in its doc but this row does not.  Secondarily, the printed proof's final step ("U preserves the inner product", dils.tex:4984-4987, from ultranorm density of U(ηV) plus 148V `innerprod_ultraweak`) is not the Lean's, which builds the adjoint S of U (152VIII) and kills S∘U − id with 152IX.2 (`SelfDual.lean:5590-5608`) — by the calibration this file uses for 162II that step reads `mild` rather than `faithful`.
- CONFIRMED — 165III `vnTensor_mul_complex` (line 53)
- CONFIRMED — 164XI `mem_uwClosure_of_npApprox` (line 86)
- CONFIRMED — 164XII.1 `selfDual_complex_hilbert, extTensorHilb, extTensorHilbTensor` (line 87)
- CONFIRMED — 44III `vanishing_effects_bounded` (line 101)
- CONFIRMED — 166IV `ptmEta2_denseRange` (line 112)

## beff-dagger-diamondamp.csv (8 / 0 / 0)

- CONFIRMED — 216VII `dagger_of_compr` (line 14)
- CONFIRMED — 218VI `standard_form_pristine` (line 30)
- CONFIRMED — 218VII `pristine_asrt` (line 31)
- CONFIRMED — 219XI `dagger_iso_mu` (line 51)
- CONFIRMED — 206II `boxPull` (line 76)
- CONFIRMED — 207V.3 `order_adj_basics_3, order_adj_basics_3'` (line 87)
- CONFIRMED — 211VII `prop_corr_zeta_pi_compr` (line 115)
- CONFIRMED — 212III.3 `standard_form_map_compr` (line 127)

## beff-effectus-quotients.csv (8 / 0 / 1)

- CONFIRMED — 180X.3 `cho_thm_3_tot_par, cho_thm_3_par_tot` (line 7)
- UNSURE — 181IV `cotupl_pcm_one, cotupl_pcm_ea_iso` (line 12): the print (eff.tex:1014-1016) says the cotupling map is an effect algebra **isomorphism** `Pred X × Pred Y ≅ Pred (X+Y)`, but `cotupl_pcm_ea_iso` (`Theses/B/Eff/Effectus.lean:553`) states only a *bijective* `EAHom`, and `PCMHom.perp_map` (`EffectAlgebras.lean:85`) is one-directional (`Perp a b → Perp (f a) (f b)`), so a bijective EA-morphism is not in general an EA isomorphism; the missing perp-reflection is the "only if" half of `cotupl_pcm_1`, i.e. the adjacent row 181IV.1 — the point is fully rendered by the tree but not by this row's declarations alone.
- CONFIRMED — 181XIII `one_m_is_id, comp_truth_effObj, isTotal_truth, totIsTerminal, truth_terminal_isIso` (line 23)
- CONFIRMED — 181XIV `tot_isPullback_plus` (line 24)
- CONFIRMED — 183III.1 `pullback_lemma_1` (line 28)
- CONFIRMED — 187IV `par_comp_ovee, par_ovee_comp` (line 42)
- CONFIRMED — 188III `parTotFunctor, parTotInv, par_tot_equiv, parTotFunctor_full, …` (line 47)
- CONFIRMED — 197V.3 `quotient_basics_3` (line 56)
- CONFIRMED — 204III `im_cotuple_sup` (line 96)

## beff-vnexamples.csv (3 / 1 / 0)

- CONFIRMED — 190IV `ScalarsAreTwo, scalarsAreTwo_of_forall, parGamma, parPredEqu…` (line 19)
- CONFIRMED — 190V `nonUnitalNonAssocCommRing, two_nsmul_lin_aux, eja_eq_zero_of…` (line 27)
- DEFECT — 201III `su_isPure_of_procPure` (line 41): eff.tex:4039 does print an argument for 201III's first sentence — "Due to \sref{pure-fundamental}" — and `Theses/B/Eff/VNExamples.lean:5110` proves it by exactly that citation (`Theses.A.Proc.pure_fundamental`, `A/Proc/Measurement.lean:4430` = proc.tex:945) plus the two dictionary lemmas; proof: should be `faithful`, not `none`.  Precedent: `aproc-duplicators-quantumlambda.csv` line 7 (127III `duplicable_unique`), repaired in the 2026-09-05 sample precisely because "proc.tex:6551-6556 prints the two-citation argument and the proof is those two citations".
- CONFIRMED — 201III `su_conjOperator_subunital_iff` (line 44)

## Cross-cutting observations (not row verdicts)

1. **`asols.tex` has no solutions for `proc.tex` or `vn.tex`.**  Its
   `parsec-N.M` labels stop at 340 — cstar.tex ends at parsec 400, vn.tex runs
   410-910, proc.tex 920-1320.  Under the binding convention every proc.tex /
   vn.tex exercise clause with no in-text hint and no "deduce from this" tail is
   therefore `none`, whatever the Lean does.  Worth a sweep beyond these rows;
   the `corner-vna-basic` block (94II) is one instance and is already
   self-inconsistent.

2. **The 2026-09-04 "Examples points print no argument" regrade stopped short
   of `eff-monoid-examples`.**  It swept 175II and 179III but not 178III, whose
   clauses .2 and .3 are the two defects above.  178III.1
   `unitInterval.effectMonoid` (line 226, not sampled) is graded `faithful` for
   the identical reason and is very likely a third instance.

3. **Printed definitions are graded inconsistently in the 192-193 block**:
   `none` at 192II, 192IV, 192V.1, 192VII, 193IV but `faithful` at 192III.1
   (`MConvexComb.map`, line 100) and 192III.2 (`MConvexComb.mu`, line 104).

4. **A bare `\sref` justification counts as a printed argument** — that is what
   the 2026-09-05 repair of 127III settled.  Applied consistently it also
   regrades `beff-vnexamples.csv` line 40 `su_procPure_of_isPure`, the
   mirror-image direction of the same printed sentence, which is not in this
   sample.  Lines 42-44 concern 201III's *second* sentence, which genuinely
   prints nothing, and stay `none`.

5. **A possible ERRATA row, for the author.**  The printed proof of 175V.4
   (eff.tex:388-394) is garbled: it writes `((a ⋎ b)ᵖ ⋎ a) ⋎ c = ((a ⋎ b)ᵖ ⋎ a)
   ⋎ b = 1` and concludes `c = ((a ⋎ b)ᵖ ⋎ a)ᵖ = b`, using an `a ⋎ b` that is
   never defined (`a ⊥ b` is not hypothesised) and the wrong letter on the left
   of the conclusion.  The method it intends is what the Lean does, so the row
   stands `faithful` — but a reader does stumble.  No ERRATA entry exists.

6. **Decayed notes on rows whose grade is right** (not defects, per the brief):
   194I's three `.lean` line numbers; `bdils-paschke-stinespring.csv` line 4,
   which puts `hilbmod_vectstates_cp` in `SelfDual.lean` (it is
   `HilbertModules.lean:1160`); line 10, which names a non-existent
   `paschke_module_phi_eq_zero` (the real ones are
   `paschke_inner_conj_forces_zero`, `paschke_rho_forces_cyclic`); and
   `bdils-pure-beff…` line 235, whose note says 178V has "no thesis proof to
   follow" when bsols.tex:1645 carries a full solution the Lean follows.
