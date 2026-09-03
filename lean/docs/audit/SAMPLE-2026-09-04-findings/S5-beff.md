# S5-beff — sample re-verification, 2026-09-04

Files: `beff-dagger-diamondamp.csv`, `beff-effectus-quotients.csv`,
`beff-vnexamples.csv`.  33 rows, re-derived from `eff.tex`/`bsols.tex`/`dils.tex`
and the Lean; the rows' own notes were not relied on.

Counts: **32 CONFIRMED, 1 DEFECT, 0 UNSURE.**

## beff-dagger-diamondamp.csv (11 of 11 confirmed)

- CONFIRMED — line 5, 214I.3 `DaggerCat.Unitary`.  `α.inv = dag α.hom` is eff.tex:5268 verbatim; Definition, no proof.
- CONFIRMED — line 19, 216XIII `asrt_comp_standard_form`.  The displayed standard form of eff.tex:5590 including the direction of `α : {X|⌈p&q⌉} ≅ {X|⌈q&p⌉}`; proof is the point's two ingredients (`1∘asrt_q∘asrt_p = p&q`, `im = ⌈q&p⌉` by ⋄-adjointness) then `standard-form-map`.
- CONFIRMED — line 33, 218IX.2 `asrt_pristine_reverse_2`.  `h†† = h` for pristine `h`; proof is bsols.tex:3253 — `1∘h† = im h`, `im h† = 1∘h`, then clause 1 again at `α⁻¹`.
- CONFIRMED — line 56, 219XVI `dagger_is_functor`.  `(f∘g)† = g†∘f†` for pure `f,g`; the tree now carries the Setting 219II with χ/ω/β/α and runs the six-step chain of eff.tex:6580, closing with 219V (`dagger_of_fg`).  The row's long stale-note history ends at proof=faithful, which holds.
- CONFIRMED — line 62, 221IV.1 `dils_abstract_basics_1`.  Unique iso between two dilations; proof is dils.tex:1193 `paschke-unique-up-to-iso` step for step (σ₁, σ₂; each composite equals the unique mediating identity).  Uniqueness is stated against all mediating maps, which is at least the point.
- CONFIRMED — line 67, 221IV.6 `dils_abstract_basics_6`.  Existence of `h''` is part of the conclusion, as in the point; purity of `h''` is discharged (`isPure_of_isQuotient_comp`) where eff.tex:6907 passes over it; the σ/epi argument is the thesis's.
- CONFIRMED — line 99, 208IX `spred_infimum`.  Stated as `SPred.IsInf`, which is what eff.tex:4664 proves; both bounds and the `compr-is-full` greatest-lower-bound step are the printed ones.
- CONFIRMED — line 100, 208XII `spred_sup`.  bsols.tex:3050's argument (factor `ξ_r` through `ξ_s`, `r = ξ^□(ξ_⋄(...))`).  Using the chosen `quotMap s` renders the thesis's own `ξ_p` notation (197III), not an added hypothesis.
- CONFIRMED — line 103, 209III.1 `diamond_squares_1`.  bsols.tex:3087, via functoriality of `(–)_⋄`/`(–)^⋄`.
- CONFIRMED — line 120, 211XIV `andthen_square_rule`.  bsols.tex:3117: `1∘asrt_p∘asrt_p = p&p`, the square is ⋄-positive (209III.3 with 211XI for purity), uniqueness of ⋄-positive maps.
- CONFIRMED — line 126, 212III.2 `standard_form_map_quot`.  `FaithfulMap f` is `IsImage f 1`, i.e. 202I.2's `im f = 1`, so it is the point's hypothesis; proof is eff.tex:5158 (π_{im f} iso, then 212III.1).

## beff-effectus-quotients.csv (11 of 11 confirmed)

- CONFIRMED — line 4, 180VII `FinPAC, EffectusPartialForm, IsTotal, predEffectAlgebra`.  Checked clause by clause against eff.tex:866–935: 1a binder, 1b(i) binder, 1b(ii) `comp_ovee`/`ovee_comp` (perp preservation *and* both distributions), 1b(iii) `comp_zero`/`zero_comp`, 1c `compatible_sum` with `▷₁=[id,0]`, `▷₂=[0,id]`, 1d `untying`; 2a the six fields, which are exactly `EffectAlgebra`'s (175I), assembled as `predEffectAlgebra`; 2b `perp_of_one_perp`; 2c `eq_zero_of_one_zero`; total = `IsTotal`.
- CONFIRMED — line 6, 180X.2 `eff_partial_to_total`.  `Nonempty (EffectusTotalStructure (Tot D))` bundles coproducts, terminal and the axioms; `proof-cho-thm` (eff.tex:1941) says point 2 is `eff-partial-to-total`, and the Lean is literally that assembly.
- CONFIRMED — line 12, 181IV `cotupl_pcm_one, cotupl_pcm_ea_iso`.  `[1,1]=1` from `coproj-total` as eff.tex:1057 does; the EA-isomorphism is rendered as a bijective `EAHom`, with reflection of `⊥` carried by the sibling `cotupl_pcm_1` (its own row) — audit rule 2/3.
- CONFIRMED — line 21, 181XI `tot_effectusTotalForm, eff_partial_to_total`.  The two binder hypotheses are proved in the same file (`totHasFiniteCoproducts`, `totHasTerminal`) and bundled by `eff_partial_to_total`; the three axiom proofs follow eff.tex points 140/150/160 (coprod-prod decomposition, `⟨α,β⟩`, joint monicity).
- CONFIRMED — line 40, 187I `parEffectusPartialForm`.  Binder `HasFiniteCoproducts (Par C)` is discharged by `parHasFiniteCoproducts` and bundled by `cho_thm_1` together with `parHomPCM`/`parFinPAC`; fields are the 180VII axioms.
- CONFIRMED — line 54, 197V.2 `quotient_basics_2`.  bsols' clause 2 exactly (θ, θ′ from the two universal properties; both composites are the unique mediating identity); uniqueness against all maps is bsols' own last line.
- CONFIRMED — line 59, 197VII `quotient_total`.  eff.tex:3747 verbatim, including `ξ` epi by 197V.6.
- CONFIRMED — line 64, 199II `IsComprehension, HasComprehension`.  No totality clause, respecting the Beware 199III; totality is the separate `compr_total` (202VIII).
- CONFIRMED — line 76, 201II `IsPure`.  Definition verbatim; the existentials bind the intermediate object, both maps and both predicates.
- CONFIRMED — line 90, 203IV.6 `floor_basics_6`.  Ad 6 (eff.tex:4271) both ways, via `p ≤ ⌈p⌉` and `⌈0⌉ = 0`.
- CONFIRMED — line 91, 203XII `img_of_compr`.  Both halves plus the "conclude" tail as two conjuncts; proof is bsols.tex's `img-of-compr` (`im-ineq` sandwich `p = im f ≤ ⌊p⌋ ≤ p`).

## beff-vnexamples.csv (10 confirmed, 1 defect)

- CONFIRMED — line 15, 197II `su_hasQuotients`.  `HasQuotients (WStarCPSUᵒᵖ)` is 197II instantiated; `IsQuotient` matches eff.tex:3658 exactly.  Examples, no proof.  (The note's clause "not 197II as the doc comment says" is now stale — the doc comment reads **197IV at `vNᵒᵖ`**.  Note only, not the grade.)
- CONFIRMED — line 17, 197IV `su_isQuotient_of_isFilter`.  Filter ⇒ quotient; `ξ(1) = pᵖ` is what "quotient *for* `p`" means, not an added hypothesis.  The converse is the sibling `su_isFilter_of_isQuotient`.
- CONFIRMED — line 19, 199II `su_hasComprehension`.  199II at `vNᵒᵖ`; the concrete corner is in `su_exists_corner`/`standard_corner_dils`.  Examples, no proof.
- CONFIRMED — line 38, 206II `su_orth_sharp`.  The last clause of the Definition (`sᵖ` sharp for sharp `s`) at `vNᵒᵖ`; Definition, no proof.
- **DEFECT — line 39, 206III `diamond_effectus_vn`: `stmt` should be `weaker`.**  The point (eff.tex:4461) asserts that `vNᵒᵖ`, `CvNᵒᵖ`, `EJAᵒᵖ` **and** `Set` are all ⋄-effectuses; the tree carries only `vNᵒᵖ` — `WStarCPSUᵒᵖ` is the only `DiamondEffectus` in the whole tree, and the Lean doc comment itself says the other three are "not formalized here", so three of the point's four clauses are nowhere.  That is audit rule 4, and it is the ground on which the *identical* `CvNᵒᵖ` clause is graded `weaker` at 189aI in this same file.  (`proof=none` is right.)
- CONFIRMED — line 43, 211II.2 `su_quot_after_compr_pure`.  Axiom 2 of 211II at `vNᵒᵖ` (diagrammatic `π ≫ ξ` = the thesis's `ξ ∘ π`); eff.tex:4863 justifies it by citing `pure-fundamental` (100III) and the Lean route is corner-then-filter, 100I closure, then the 100III dictionary bridge.
- CONFIRMED — line 47, 215VI `vn_is_dagger_category`.  Quantifying over `hA : AndThenEffectus` is forced by the `sorry` in 211IV, and 211IV `vn_is_andthen_eff` is the sibling supplying it (rule 2/3); the route is the Corollary's — verify 215III's axioms 1–3, apply 220II sufficiency.  (This sits in tension with the 215II row, which is graded `weaker` on exactly this conditionality; 215II is the row I would re-open, not this one.)
- CONFIRMED — line 56, 225V `effectsSEA`.  The `def` carries `seq = effSeq = √a b √a`, so the point's product is in the statement; asserted without proof in eff.tex.
- CONFIRMED — line 57, 225V `effects_sea`.  The theorem now reads `∃ S, ∀ a b, S.seq a b = √a b √a`, so the reclassification `weaker → ok` in the status column is right.  (The `note` field still argues the old `weaker` case; note only, not the grade.)
- CONFIRMED — line 65, 225V `commEffectMonoidSEA`.  Second sentence, the structure, with `seq a b = a ⊙ b`; all six SEA fields discharged from commutativity and associativity of `⊙`.  eff.tex:7385 prints the sentence and no argument, here or in bsols, so `proof=none`.
- CONFIRMED — line 67, 226II `homology_lemma`.  Statement matches; the proof now *is* eff.tex:7426's — diamond-oml reduction, `perp_sharp_is_orth` (213III) giving `tᵖ & sᵖ = 0`, the pristine `l` (private `exists_pristine_asrt_comp`, the interior of 219XI), and the `asrt²_{s&tᵖ}` computation of 7445–7462 with asrt-absorp-rule and sharp-prop.  The status column's `route → faithful` holds.  (The `note` field still says the proof does *not* follow eff.tex:7426; note only.)
