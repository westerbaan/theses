# S4-bdils — sample re-audit of `ok` rows

Assignment: `bdils-hilbertmodules-selfdualcompletion.csv`,
`bdils-paschke-stinespring.csv`, `bdils-pure-beff-states-effectalgebras.csv`,
`bdils-selfdual-kaplansky.csv` — 44 rows, each re-derived from `dils.tex`,
`eff.tex`, `proc.tex`, `vn.tex`, `asols.tex`, `bsols.tex` and the Lean.  The
rows' own notes were used only as a hint about where to look.

**confirmed 39 / defect 5 / unsure 0** (defect rate 11%).

All five defects are in the `proof` column and four of them are one shape:
`faithful` recorded where the thesis prints no argument at all.  No `stmt=ok`
grade was found wrong except one, `142VIII`.

## bdils-hilbertmodules-selfdualcompletion.csv (9 / 2 / 0)

- CONFIRMED — 43I `uwTendsto_of_unTendsto_mulInner` (line 3)
- CONFIRMED — 147I `UnComplete` (line 51)
- CONFIRMED — 147II `dils_uniform_spaces_basics_3` (line 55)
- DEFECT — 148VII `unDense_inner_nonneg` (line 71): 148VII (dils.tex:2124) is a Corollary that prints no argument — only "Cf. `hilbmod-ordersep`" — and `hilbmod-denseordersep` has no solution in `bsols.tex`, so the Lean's 130-line ε/density estimate follows nothing printed; proof: should be `none` (at most `route`), not `faithful`.
- CONFIRMED — 149III `mod_projelabs` (line 78)
- CONFIRMED — 150IX `semC_op_smul` (line 107)
- CONFIRMED — 150IX `ipf_op_smul` (line 109)
- CONFIRMED — 149V `completeSpace` (line 121)
- CONFIRMED — 149V `selfDual` (line 122)
- DEFECT — 142VIII `ba_isBSesquilinear` (line 135): the Example (dils.tex:1495) asserts `⟨·,T·⟩` is 𝒷-sesquilinear for every 𝒷-linear `T : X → X` on a pre-Hilbert module; ours assumes `Z ∈ Ba 𝒷 X`, i.e. bounded and adjointable, and the only other `IsBSesquilinear` witness in the tree (SelfDualCompletion.lean:2487) is an unnamed `have` inside another proof, so no sibling makes up the difference; stmt: should be `weaker`.  (The row's own note already says the general case "is not stated" — the class, not the note, is wrong.)
- CONFIRMED — 153I `hilbmod_ad_cp` (line 140)

Adjacent, outside the sample: line 72 `hilbmod_denseordersep` is `faithful`
against the same unprinted argument as line 71.

## bdils-paschke-stinespring.csv (11 / 0 / 0)

- CONFIRMED — 154III `exists_prho` (line 13)
- CONFIRMED — 154III `prho` (line 14)
- CONFIRMED — 154III `prhoHom` (line 15)
- CONFIRMED — 154III `prhoHom_normal` (line 16)
- CONFIRMED — 154III `pTheta_normal` (line 23)
- CONFIRMED — 154VIII `paschke_sigma_matrix` (line 26)
- CONFIRMED — 155II `ksgns_aux` (line 31)
- CONFIRMED — 157IV `paschke_correspondence_embedding` (line 40)
- CONFIRMED — 157VI `phiT_ncpLe_self` (line 47)
- CONFIRMED — 135IV `stinespring_aux` (line 52)
- CONFIRMED — 135IV `stinespring` (line 54)

The mirroring convention was re-derived rather than taken on trust: `prho a₀`
is the thesis's `ϱ(a₀*)` read through `tprod a b = (a*⊗b*)` and `⟨x,y⟩ = [y,x]`,
which is what makes `prho_mul` anti-multiplicative (hence the `ᵐᵒᵖ` codomain),
`prho_smul` ℂ-linear and `h(ρ a) = φ a` star-free; `ptensBInner`, `pTheta_sum`
and `paschke_sigma_matrix` all fall out of the same substitution.

Not a grading defect, but a candidate erratum found on the way: the printed
KSGNS statement (dils.tex:3862) has `T : Y → X` with `φ = ad_T ∘ ϱ`, which is
ill-typed against `φ : 𝒜 → 𝒷ᵃ(X)` under the thesis's own `ad` convention
(154III.4).  `ksgns_aux`/`ksgns` render the coherent Kasparov reading
`T : X → Y`, `φ(a) = T*ϱ(a)T`.

## bdils-pure-beff-states-effectalgebras.csv (9 / 2 / 0)

- DEFECT — 94II.5 `cornerSet.instCStarAlgebra` (line 3): proc.tex 94II is an Exercise with no solution in `asols.tex` (solutions are keyed `parsec-N.M`; there is no `parsec-940.20`), so the thesis prints no argument for part 5 and the empty-`where` instance has nothing to be faithful to; proof: should be `none` — as the sibling row `cornerSet.instPartialOrder` for the same DISP already is.  stmt is fine.
- CONFIRMED — 68III `fact_isStarProjection_cceil` (line 12).  Caveat, not filed as a defect: the closer is the in-tree `cceil_isLeast` (A/VN/Projections.lean:6211), not a Mathlib lemma, so `mathlib` is a vocabulary slip; the note discloses the real source and no other grade in the vocabulary fits better.
- CONFIRMED — 190II.7 `SeparatingPredicates` (line 77)
- CONFIRMED — 191II `emod_po2` (line 80)
- CONFIRMED — 192III.2 `MConvexComb.mu_mu` (line 102)
- CONFIRMED — 192VII `statSum_statMap` (line 121)
- CONFIRMED — 192VII `stat_functor` (line 126).  The status field's repair claim is real — the `HEq (F.map f).1 (statMap f.1 f.2)` clause is there — but its line number is stale: the declaration is at StatesPredicates.lean:5761, not 5296.
- CONFIRMED — 175I `SubEffectAlgebra` (line 162)
- CONFIRMED — 176III `DPoset.dsub_zero` (line 195)
- DEFECT — 177Ia `WrightTriangle.not_ea_modularity_prop` (line 202): the note is stale — eff.tex:484 was corrected on 2026-08-14 and now hypothesises the *supremum*, so 177Ia as printed is true (`ea_modularity_prop`, line 205).  This declaration refutes the swapped, no-longer-printed form by `decide` on a 6-element algebra, an argument the thesis never prints; proof: should be `route` (or `none`), not `faithful`.  stmt survives only through the sibling convention.
- CONFIRMED — 178II `EffectMonoid.Commutative` (line 210)

## bdils-selfdual-kaplansky.csv (10 / 1 / 0)

- CONFIRMED — 159II `mketbra_apply` (line 3)
- CONFIRMED — 159VI `onbProj_isLUB, …` (line 7).  All four clauses of `ketbra-dense-pt1` are stated.  The Lean cites 44VI `vna-supremum-uwlimit` where the thesis cites `vna-supremum-uslimit`; ultrastrong ⇒ ultraweak, so the printed conclusion is matched.
- CONFIRMED — 161II `binner` (line 31).  Nuance, not a defect: the five axiom proofs the `def` bundles are the bsols line about ultraweak continuity of `a↦a*`, `a↦ab`, `(a,b)↦a+b`, and no other row covers them.
- DEFECT — 113II `sum_t_nonneg` (line 52): proc.tex 1130.20 is an unlabelled Exercise with no Proof point and no solution in `asols.tex` or `bsols.tex`, and the Lean is a two-line `simpa` off the imported `matBilin_nonneg_of_mi`; proof: should be `none`, not `faithful`.  The tree's two other renderings of this DISP are already graded `none` for exactly this reason (`aproc-tensor.csv:75`, `acstar-matrices-representation.csv:57`).  stmt=`ok` stands.
- CONFIRMED — 164II `tSpan` (line 57)
- CONFIRMED — 164II `tensor_gram_le` (line 60).  The one real substitution (dense subalgebra for the norm completion) is separately graded `mild` on `le_smul_of_conj_norm_le`'s own row, so `faithful` here is not hiding a deviation.
- CONFIRMED — 164II `extTensor_map_ext` (line 64)
- CONFIRMED — 164XII.3 `extPlainTensor, extTensor_ultranorm_completion` (line 77).  Minor: the *status* field's own "corrections" are the stale ones — `extPlainTensor` is at SelfDual.lean:8067 and the section doc at :7978, i.e. the note field's numbers, not the status field's :8069/:7980.
- CONFIRMED — 166IV `exttensor_dense_subsets` (line 82)
- CONFIRMED — 144V `ba_ext_of_unDense` (line 91)
- CONFIRMED — 167I `paschke_tensor` (line 99).  Verified independently: all six `[VonNeumannAlgebra]` binders present, quantification over arbitrary `PaschkeTriple`s with `IsPaschkeDilationOf`, 167VI's qed at dils.tex:5956 and the commented passage to arbitrary dilations at 5958–5969 (the status field's number, correct).
