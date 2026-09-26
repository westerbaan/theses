# Final-round adversarial re-audit, 2026-09-26

Scope: rows whose module is REC Resolvent, Rec119, Rec136Hyps, Rec136Hyps2,
JordanSymmetry/JordanFromChains/SpectralChains (the REC 121 rows), FDS Linking,
Envelope and Bidual, and SEA JordanSEA. This was a read-only pass: nothing was
compiled and nothing was edited. Each line reads `csv:line DISP name — verdict. reason (lean; print)`.
Grade vocabulary is from docs/STATEMENT-AUDIT.md:38-61 and Papers/README.md:63.

## REC (papers-rec.csv)

- rec:178 REC 121 rec121, jb_of_chainDense, ChainDense, … — **DEFECT (stale status + module).**
  - The statement matches the print: ∃ Mul, JBAlgebra V_A, and p*a = ½(a + D_p a) for sharp p.
  - ChainDense is a real condition (norm approximation by nested commuting chains). va_chainDense proves it with no hypotheses, from spectral_rep. `mild` is right: the print asks to copy A–S 9.43, and the Lean does that with repairs.
  - The status still says "ok (modulo A–S 1.82 and REC 119)". rec121 does take hRC and h119 (Reconstruction2.lean:61), but both are now discharged (Resolvent.lean:235, Rec119.lean:440). There is no rec121_hypfree, and the row does not point to the discharge, so REC 121 reads as conditional.
  - ChainDense, Uop and AlfsenShultzJordanFromDerivations live in Reconstruction.lean:2372/2486/2351, not in Reconstruction2.lean.
  - (Reconstruction2.lean:61; JordanFromChains.lean:847; SpectralChains.lean:270; short.tex:2225-2238)
- rec:179 REC 121 jordan_symmetry, IsOrderDerivation.lie, lemmaP, … — **CONFIRMED.**
  - jordan_symmetry is proved from the family axioms alone. IsOrderDerivation.lie, lemmaP, ExpIn.lie and tendsto_trotter are all proved.
  - Direction is right: Transplant ⇒ FromDerivations (_of_transplant:588), so Transplant is the weaker Prop. Both Props are unused.
  - The rec102'/103'/136' in Monoidal.lean claim holds.
  - (JordanSymmetry.lean:445,588; short.tex:2233-2235)
- rec:200 REC 120 rec120_unconditional, alfsenShultzResolventCriterion_holds, … — **CONFIRMED.**
  - Literally rec120 with hRC discharged; h119 kept.
  - The criterion is not vacuous: δ is bounded, 1∓λδ preserves positivity for small λ, and the conclusion is IsOrderDerivation. This is A–S (1.82) plus the exponential formula.
  - `mild` is right.
  - Status "ok modulo REC 119" is now superseded by Rec119.lean, but the row gives no pointer (see rec:178).
  - (Resolvent.lean:200,229; Reconstruction.lean:2323; short.tex:2174-2224)
- rec:201 REC 121 rec121_unconditional — **DEFECT (stale status).**
  - The statement is literally rec121 minus hRC.
  - The status says "ok modulo WeteringStateOrderLemma", but REC 119 is proved and nothing names a hypothesis-free REC 121. Either add rec121_hypfree or point to weteringStateOrderLemma_holds.
  - (Resolvent.lean; Rec119.lean:440)
- rec:202 REC 102 rec102_unconditional — **CONFIRMED.** Identical to rec102, with hRC discharged inside rec102_jbFunctor. (Resolvent.lean:242; Reconstruction2.lean:693; short.tex:1869)
- rec:203 REC 103 rec103_unconditional — **CONFIRMED.** Identical to rec103; hirr is kept. (Resolvent.lean:261; Reconstruction2.lean:1042; short.tex:1874)
- rec:204 REC 136 rec136_unconditional — **CONFIRMED.** Identical to rec136. The remaining hypotheses are exactly h119, hHOS, hSh and hAS4, plus the print's hirr and h01. (Resolvent.lean:277; Monoidal.lean:2759; short.tex:2409)
- rec:205 REC 119 weteringStateOrderLemma_holds, r119_* — **DEFECT (proof grade).**
  - The statement is right: total states (as printed), right direction, and it does not depend on hRC or h119.
  - The print's whole proof is "follows in exactly the same way as … Proposition 46 of [vdW]", a bare citation. README:63 says "a proof of ours for a point the paper only cites is `none`", and STATEMENT-AUDIT.md:56 agrees.
  - vdW 1803.11139 is not in papers/, so the Lean cannot be checked against Prop 46 step by step. The s ∈ {0,1} scalar split is effectus-specific.
  - Grade `none`, not `mild`.
  - (Rec119.lean:440; Reconstruction.lean:2558; short.tex:2164-2169)
- rec:206 REC 102 rec102_hypfree — **CONFIRMED.**
  - Identical to rec102_unconditional, with h119 := weteringStateOrderLemma_holds. It really has no named hypotheses: separatedByStates and normality are fields of the print's own SequentialEffectus class.
  - (Rec119.lean:449; short.tex:1869)
- rec:207 REC 103 rec103_hypfree — **CONFIRMED.** Only the print's hirr remains. (Rec119.lean:469; short.tex:1874)
- rec:208 REC 136 rec136_hypfree — **CONFIRMED (nit).**
  - The statement is identical, and the three remaining named hypotheses (hHOS, hSh, hAS4) are disclosed.
  - The name "_hypfree" oversells, and the note does not point to the stronger rows rec:213 (noAS4) and rec:214-215 (bounded).
  - (Rec119.lean:485; short.tex:2409)
- rec:209 REC 52 JBWExceptionalSummand, jbwExceptionalSummand_of_HOS — **CONFIRMED.**
  - The Prop reads: JW, or a nonzero central c whose summand cV is killed by every Jordan hom into a C*-algebra.
  - HOS ⇒ Prop is proved (in the c = 0 case, φ is injective and normal, so V is JW). The Prop is not vacuous. `weaker` is consistent with the parent row rec:180.
  - (Rec136Hyps.lean:62,84; short.tex:925)
- rec:210 REC 55 ExceptionalAlbertPoint, exceptionalAlbertPoint_of_shultz — **CONFIRMED.** The Prop gives an exchangeable family with n ≥ 2 (from rec133) and a point evaluation χ with χ1 = 1. Shultz ⇒ Prop is proved. (Rec136Hyps.lean:75,108; short.tex:940)
- rec:211 REC 132 fam_tens, tower, tower_absurd, alb_orth_idem_card_le — **DEFECT (misleading grade).**
  - These are replacement lemmas for REC 135. None of them states or proves A–S Lemma 4.4 (AlfsenShultzFourExchangeable stays unproved).
  - A row keyed "REC 132 | ok" reads as "REC 132 formalised". Re-key it as REC 135 supporting, or grade it as a helper that differs from REC 132.
  - The note text itself is accurate.
  - (Rec136Hyps.lean:140,183,229,315; short.tex:2377)
- rec:212 REC 135 rec135_weak — **CONFIRMED.**
  - The conclusion is identical to rec135. {hHOS, hSh, hAS4} are replaced by {hP, hS}.
  - `route` is right: the print goes through 9 tensor idempotents and REC 132, the Lean through the iterated tensor count.
  - (Rec136Hyps.lean:372; short.tex:2395-2405)
- rec:213 REC 136 rec136_weak, rec136_weak_hypfree, rec136_hypfree_noAS4 — **CONFIRMED.**
  - The statements are literally rec136_hypfree's; noAS4 takes only hHOS and hSh.
  - Nit: the note does not say that rec136_weak itself still carries hRC and h119.
  - (Rec136Hyps.lean:409,434,447)
- rec:214 REC 136 rec136_bounded_hypfree, JBWBoundedObstruction, jbwBoundedObstruction_of_HOS_shultz — **CONFIRMED.**
  - The statement is identical.
  - The equivalence JBWBoundedObstruction ⇔ JBWExceptionalSummand ∧ ExceptionalBoundedRank is proved both ways, so "one Prop in form only" is honest.
  - (Rec136Hyps2.lean:102,175-200,359)
- rec:215 REC 136 rec136_bounded_weak_hypfree — **CONFIRMED.** Identical statement; ExceptionalAlbertPoint ⇒ ExceptionalBoundedRank is proved. (Rec136Hyps2.lean:111,344)
- rec:216 REC 135 rec135_bounded, tower_absurd_bounded — **CONFIRMED.** Identical to rec135 up to hypotheses. D is uniform and fixed before the tower is built, so the argument is not circular. (Rec136Hyps2.lean:223,283)
- rec:217 REC 55 ExceptionalBoundedRank, HasBoundedRankIdeal, … — **CONFIRMED (wording nit).**
  - Albert ⇒ FiniteQuotient ⇒ BoundedRank is proved.
  - The Prop is not vacuous: 1 ∉ J and 0 ∈ J, so the idempotents outside J are nonzero.
  - "The weakest form" is an unproved minimality claim; write "a weaker form".
  - (Rec136Hyps2.lean:74-163)

## FDS (papers-fds.csv)

- fds:36 FDS 2.2 homsHavePreduals_of_wStarCategory — **CONFIRMED.**
  - WStarCategory ⇒ HomsHavePreduals. The predual is the span of ω(⟨g,·⟩), and the Hom and predual universes match (Category.{u}).
  - `none` is right: the print cites [GLR, Prop. 2.15].
  - (Linking.lean:403; direct_sums.tex:274)
- fds:37 FDS 2.2 wStarCategory_iff_homsHavePreduals_of_linking — **CONFIRMED.**
  - `weaker` is right: the general predual ⇒ self-dual direction is nowhere in the tree.
  - The common-isometric-embedding hypothesis is stated exactly.
  - (Linking.lean:411)
- fds:38 FDS 2.2 Linking.selfDualPredualEquiv — **CONFIRMED.** (Linking.lean:367)
- fds:39 FDS 2.2 Linking.wStarAlgebra_of_vonNeumannAlgebra, predualEquiv — **CONFIRMED.** M ≅ (M_*)* is isometric, with the star twist so the map is linear. (Linking.lean:205,225)
- fds:40 FDS 2.5 nrep_equiv_rep — **DEFECT (class + stale note).**
  - The declaration is right: under IsRepEnvelope ι, restriction is an equivalence, identity on intertwiners.
  - But fds:43 (Env.nrep_bidual_equiv_rep) now states the clause with no hypothesis. By STATEMENT-AUDIT.md:79-103 (rules 2/3 and "a `weaker` row whose own note says the point is fully covered must never survive"), the row should be `ok` and name fds:43.
  - The note sentence "The construction of A** … is in neither Mathlib nor the tree" is stale. So are the Lean docstrings Envelope.lean:4-24 and :59-61 (IsRepEnvelope "Named hypothesis: the construction of A** is in neither Mathlib nor the tree").
  - (Envelope.lean:235; direct_sums.tex:315-318)
- fds:41 FDS 2.5 IsRepEnvelope, restrictRep, … — **CONFIRMED.**
  - IsRepEnvelope reads: every unital π on HilbObj.{u} is ρ∘ι for exactly one normal unital ρ. That is the print's reason ("non-degenerate" becomes unital).
  - Minor: the Hilbert spaces live in N's universe u while 𝒜 is in u₁. This is not disclosed on this row; only fds:43 says "A's universe".
  - (Envelope.lean:62)
- fds:42 FDS 2.5 isRepEnvelope_complex — **CONFIRMED.** A sanity check that the Prop is satisfiable. (Envelope.lean:258)
- fds:43 FDS 2.5 Env.nrep_bidual_equiv_rep, Env.isRepEnvelope_bidual — **CONFIRMED.**
  - A** := W*(π_u(A)) = π_u(A)'' over all positive functionals is a genuine VNSub. Uniqueness goes through 47V/48VI, existence through the H_u ⊕ H compression.
  - Unital A and Hilbert spaces in A's universe are disclosed.
  - Remarks:
    - "A**" is the enveloping von Neumann algebra. Its isomorphism with the Banach bidual is not proved; that is standard, and the note says ":=".
    - isRepEnvelope_bidual proves a fact the print only asserts. `faithful` still fits, since the print's one-line argument from that fact is followed.
  - (Bidual.lean:545,564)
- fds:44 FDS 2.5 Env.Bidual, Env.bidualEmb, … — **CONFIRMED.** exists_isRepEnvelope gives an injective ι into a VonNeumannAlgebra for every unital C*-algebra (spectral order). (Bidual.lean:576)

## SEA (papers-sea.csv)

- sea:116 SEA 16 sea16_eja, ejaSEA, ejaNormalSEA, … — **CONFIRMED.**
  - [0,1]_V of a Euclidean Jordan algebra is a convex EA (SEA 8 interval action) and a normal SEA with a∘b = U_{√a}b. S1-S7 are discharged from seq_comm_iff; directed completeness, seq_sup and comm_sup come from dirSup_weak.
  - `weaker`/`none` is right: the print only cites vdW 2019, and the infinite-dimensional JB/JBW case is not covered and is disclosed.
  - (JordanSEA.lean:629-772; second.tex:484)
- (out of scope, adjacent) sea:114 SEA 16 (Basic.lean) — the note is stale.
  - It says "neither Mathlib nor the tree has JB- or JBW-algebras", but Papers.REC.Algebras defines JBAlgebra and JBWAlgebra.
  - It says "even their [0,1] is not shown a SEA", which is contradicted by JordanSEA.lean, a file the same note cites.

## Would mislead the author

1. REC 119/120/121 (rec:178, 200, 201): REC 121 reads as conditional on REC 119, but both of its hypotheses are discharged. Add `rec121_hypfree` (one line: `rec121_unconditional σs weteringStateOrderLemma_holds A`) or add a pointer.
2. rec:211 "REC 132 | ok" suggests A–S Lemma 4.4 is formalised. It is not; the row holds replacement lemmas.
3. rec:205 REC 119 proof `mild` should be `none` under README:63.
4. fds:40 `weaker` with a stale "A** is in neither Mathlib nor the tree"; the same stale text is in the Envelope.lean docstrings.
5. Nits: `rec136_hypfree` keeps three literature hypotheses despite the name (rec:208); "the weakest form" (rec:217).
