# S3-avn — sampled re-audit of `ok` rows (2026-09-04)

Files: `avn-basic.csv`, `avn-bax.csv`, `avn-division-normalfunctionals.csv`,
`avn-projections.csv`.  44 rows re-derived from `vn.tex`/`cstar.tex` and the
Lean source; the rows' own notes were not relied on.  (`asols.tex` was checked
for every exercise row: its solutions stop at parsec 340, so no point sampled
here has a printed solution.)

**Counts: 42 CONFIRMED, 2 DEFECT, 0 UNSURE.**

## avn-basic.csv

- CONFIRMED — line 8, 42I `VonNeumannAlgebra,dirSup,isLUB_dirSup`.  vn.tex:166
  Definition, both clauses: `isLUB_of_bddAbove_directed` = clause 1 with
  `dirSup`/`isLUB_dirSup` for the `⋁D` notation, `np_faithful` = clause 2.  The
  two deviations check out: `D.Nonempty` is forced (∅ is bounded and vacuously
  directed), and `BddAbove` vs the printed *norm* bounded defines the same
  class — for `d₀ ∈ D`, `D ∩ [d₀,∞)` is directed, cofinal (so same upper bounds
  and suprema) and norm-bounded by `max(‖d₀‖,‖b‖)`.  Definition, proof=none.
- CONFIRMED — line 19, 42V `inner_diag_mono`.  Auxiliary (`⟪x,(·)x⟫` monotone
  on `B(H)`), used for the `np_faithful` clause of 42V.2; not a transcription.
- CONFIRMED — line 36, 43II `vn_counterexamples_1`.  vn.tex:392 part 1
  verbatim: `(|n⟩⟨m|)* = |m⟩⟨n|` and `|n⟩⟨m||l⟩⟨k| = δ_{m,l}|n⟩⟨k|`;
  `ketbraNat n m z = ⟪e_m,z⟫•e_n` is the printed action.  Exercise, proof=none.
- CONFIRMED — line 38, 43II `vn_counterexamples_2_tendsto`.  Part 2's second
  half (`(|n⟩⟨n|)_n → 0` ultrastrongly); the printed "(and ultraweakly)" is
  `uwweaker_2` in the tree, and the first half is the `vn_counterexamples_2_sup`
  row.  Exercise, proof=none.
- CONFIRMED — line 57, 44VI `vna_supremum_uwlimit`.  vn.tex:692 exactly, under
  44V's hypotheses (bounded directed set of self-adjoint elements).  Exercise,
  no printed proof.
- CONFIRMED — line 77, 44XV `preservesDirSups_of_continuousOn_effects_core`.
  Private common core of 44XV (2)⇒(3) and 45I.1, stated with the finest source
  and coarsest target topology; not a transcription.  Exercise, proof=none.
- CONFIRMED — line 105, 48V `exists_faithful_normal_rep_vectors`.  Auxiliary
  refinement (every np-functional is a vector functional of the direct-sum GNS
  representation); 48V itself, for an arbitrary family, is the
  `gnsRepFam_normal` row.  Exercise, proof=none.
- CONFIRMED — line 122, 51VII `vna_of_faithful_countably_normal_1`.  vn.tex:1580
  part 1: hypotheses (faithful positive `τ`, every bounded ascending sequence
  has a `τ`-preserved supremum) and conclusion match.  The proof
  (`countably_normal_key`) is vn.tex:1593–1622 step for step — the ascending
  `aₙ` with `⋁ₙτ(aₙ) = ⋁_{d∈D}τ(d)`, the `bₙ ≥ b` above the `aₙ`, and
  `τ(⋁aₙ) = τ(⋁bₙ)` closed by faithfulness.
- CONFIRMED — line 137, 53II `ngelfand_vna`.  Exercise first half; the printed
  instruction (γ_A is an miu-isomorphism, hence an order isomorphism) is what
  `vonNeumannAlgebra_of_starAlgEquiv` runs.
- CONFIRMED — line 138, 53II `ngelfand_normal`.  Second half: normality of γ_A,
  by `starAlgEquiv_preservesDirSups`, which is literally the printed reason.
- CONFIRMED — line 160, 72III `conjNP`.  72III.1a: `b*ω : a ↦ ω(b*ab)` bundled
  as an np-functional (positivity from `star_left_conjugate_le_conjugate`,
  normality from 44VIII).  Printed as "Note that …", proof=none.

## avn-bax.csv

- CONFIRMED — line 1, 42III `uwTendsto_star`.  Auxiliary; 42III is the
  definition of the ultraweak topology and this is the involution companion of
  `UWTendsto.add`/`.smul`.  Not a transcription, proof=none.
- CONFIRMED — line 4, 49II `isSelfAdjoint_vecForm`.  Auxiliary:
  `⟪x,Tx⟫* = ⟪Tx,x⟫ = ⟪x,Tx⟫` for adjointable self-adjoint `T`.
- CONFIRMED — line 6, 49II `bah_vn_sup`.  stmt=ok is right under
  STATEMENT-AUDIT rule 3: 49II on the type is the sibling `bah_vn`, which has
  its own row.  The proof is vn.tex:1232–1249, the last two paragraphs (S an
  upper bound, then least), read off `exists_isLUB_vecForm`.  (The row's *status*
  field still ends "so `differs` stands for it", which contradicts its own note
  and the `ok` in the column; that is stale prose, not a wrong grade.)
- CONFIRMED — line 7, 49II `eq_zero_of_vecForm_eq_zero`.  Auxiliary: the vector
  functionals separate operators, by polarisation.
- CONFIRMED — line 10, 49II `vecFunctionalSA_mono`.  Auxiliary: 32XV.2
  (`bax_le_iff`) restricted to self-adjoint parts.
- CONFIRMED — line 12, 49II `vecFunctional`.  `⟨x,(·)x⟩ : 𝓑^a(X) → 𝒜` as a
  positive linear map; the single obligation (`monotone'`) is discharged by
  `bax_le_iff`, which is the printed 32XV.2.
- CONFIRMED — line 13, 49II `vecFunctional_apply`.  `rfl` simp lemma.
- CONFIRMED — line 14, 49II `vecFunctional_normal`.  The Theorem's second clause
  verbatim ("⟨x,(·)x⟩ … is normal for every x∈X"), with normality =
  `PreservesDirSups` = 42II's condition.  The proof is the printed remark at
  vn.tex:1250–1254 (the constructed supremum already satisfies
  `⟨x,Sx⟩ = ⋁_T ⟨x,Tx⟩`).
- CONFIRMED — line 15, 49II `baxNP`.  vn.tex:1262–1265: `ξ(⟨x,(·)x⟩)` is an
  np-functional on `𝓑^a(X)`; positivity 32XV.2, normality `vecFunctional_normal`.
- CONFIRMED — line 16, 49II `baxNP_apply`.  `rfl`.
- CONFIRMED — line 17, 49II `bah_vn`.  The Theorem itself, over the type:
  `VonNeumannAlgebra (Bax 𝒜 X)` for self-dual `X`.  `[CompleteSpace X]` is the
  thesis's own convention (cstar.tex:5108 — a Hilbert 𝒜-module *is* complete).
  Both 42I clauses come from `exists_isLUB_bax` and `bah_vn_np_faithful` applied
  to `baxNP`, which is vn.tex:1256–1268.

## avn-division-normalfunctionals.csv

- CONFIRMED — line 22, 79II `pinv_nonneg`.  Auxiliary read off 79II clause 4
  (`t a t = t`, so `a^{∼1} = (a^{∼1})* a a^{∼1} ≥ 0`); not a transcription.
- CONFIRMED — line 48, 80IV `posPart_sub_le`.  Auxiliary `(a−λ)₊ ≤ a` for the
  80IV construction; not a transcription.
- CONFIRMED — line 83, 81VIII `sequential_quotient_1`.  vn.tex:5518–5522, the
  equivalence of clauses 1 and 2, both directions, with `λ ≥ 0` real.
  Exercise, no printed proof or solution.
- CONFIRMED — line 114, 84aI `puEqualiserG_isUnitalMap`.  `g(1,1,1,1) = 1`; the
  Example asserts pu-ness without proof.
- CONFIRMED — line 121, 84bII `HereditarilyAtomic`.  vn.tex:6171 Definition;
  `⊕ᵢ M_{Nᵢ}` as the ℓ^∞-sum, nmiu-isomorphism as `≃⋆ₐ[ℂ]` (normality
  automatic), `M_{Nᵢ+1}` to keep summands nonzero — no generality lost.
- CONFIRMED — line 161, 87III `predual_complete`.  vn.tex:6537 Proposition;
  `predual` is the ultraweakly continuous functionals and `IsComplete` is the
  printed claim.  The proof is vn.tex:6539–6572: norm limit first, then
  ultraweak continuity on the unit ball via `uwcont_on_ball` (the printed
  `uwcont-on-ball`), with the printed two-term estimate packaged as
  `TendstoUniformlyOn`.
- CONFIRMED — line 194, 89I `gns_mapping_property`.  vn.tex:6866 Lemma, all
  three conclusions; the Lean statement has `U*U` on `closure(π(𝒜)y)` — the
  right way round, the printed proof's second `UU*` at vn.tex:6902 being the
  known erratum.  The proof is vn.tex:6883–6925: the isometry `V` between the
  cyclic subspaces, `U = EVF*`, `UU* = EE*`, `U*U = FF*`, and the intertwining
  checked on the dense subset.
- CONFIRMED — line 202, 89IX `normal_functional_assembly`.  Not a transcription
  but the displayed computation at the end of the 89IX proof (vn.tex:7148–7176):
  `hterm` is its four steps (`vᵢvᵢ* ≤ U*U`, `vᵢ ∈ ϱ(𝒜)^□`, `Uϱ_Ω(a) = ϱ(a)U`)
  and `∑ᵢ vᵢ*vᵢ = 1` supplies the sum.
- CONFIRMED — line 217, 48III `gnsVec_approx_functional`.  Not a transcription
  but the reduction step of vn.tex:7310–7331: `v` is a norm limit of `η_ω(b)`
  (48III) and `b ↦ b*ω` is `‖·‖_ω`-to-norm Lipschitz (72III.1c) — the two steps
  the thesis takes, in that order.
- CONFIRMED — line 218, 90II `inner_conj_diff_le`.  Auxiliary norm estimate
  `‖⟪u,Tu⟫ − ⟪w,Tw⟫‖ ≤ M(‖u‖+‖w‖)‖u−w‖`; not a transcription.
- CONFIRMED — line 225, 89XI `ncpOfNonneg`.  Infrastructure: `z ↦ z·a` as an
  ncp-map `ℂᵤ → 𝒜` for positive `a`; not a transcription.

## avn-projections.csv

- CONFIRMED — line 5, 55II `isStarProjection_iff_star_mul_self`.  vn.tex:2203
  Definition (`p*p = p`) proved equivalent to the tree's `IsStarProjection`;
  Definition, proof=none.
- CONFIRMED — line 15, 55V `le_of_paq_eq_zero`.  The second half of the printed
  proof at vn.tex:2264–2269, step for step: `qa*p = 0` by starring,
  `(1−p)(aq) = aq` and `qa*(1−p) = qa*`, then `aqa* ≤ aa* ≤ ‖a‖² ≤ 1`
  conjugated by `p^⊥`.
- CONFIRMED — line 22, 55XII `OrthogonalSet`.  vn.tex:2322 Definition: members
  pairwise equal or with product 0, membership in the projections folded in.
- CONFIRMED — line 33, 56I `ceil_mem`.  Not a thesis statement: 56I.20's formula
  `⌈b⌉ = ⋁ₙ b^{1/2ⁿ}` read inside a von Neumann subalgebra; 56I itself is the
  `vna_ceil`/`vna_ceil_sup` rows.
- CONFIRMED — line 47, 56XIII.1 `ceil_floor_basic_1`.  Both printed clauses
  (`⌈a⌉^⊥ = ⌊a^⊥⌋`, `⌊a⌋^⊥ = ⌈a^⊥⌉`).  Exercise, no printed proof.
- CONFIRMED — line 52, 56XVI `projSup`.  The definition of `⋃P` with junk value
  `0`; existence is `exists_projSup` and the infimum half has its own two rows.
- CONFIRMED — line 63, 59I `suppProj`.  vn.tex:2698 Notation: `⌈b⌋ = ⌈b*b⌉`.
- CONFIRMED — line 65, 59I `ceil_mem_ideal`.  Auxiliary: the effect-level
  `ceil_mem_ideal_of_effect` rescaled by 59I; not a transcription.
- **DEFECT** — line 112, 63VI `carrier_fundamental`: **proof=faithful is wrong;
  it should be `none`.**  vn.tex:3144–3149 is a bare Corollary with no proof
  point at all (the point closes at 3149 and the parsec at 3150) and asols has
  no solution, so there is no printed argument to be faithful to — the row's own
  note says so ("The thesis gives no proof text").  The tree has ruled this
  shape `none` repeatedly (104VI `centrally_similar_corollary`, 138VI
  `typei_inner_auto`, 172XII `ncp_extreme_comp`, and 216IX `dagger_of_iso`
  explicitly in session 96: "a bare Corollary with NO proof point at all").
  stmt=ok is right: the four printed equalities are stated verbatim.
- **DEFECT** — line 157, 69IV `carrier_miu`: **proof=faithful is wrong; it
  should be `none`.**  vn.tex:3610–3617 is likewise a bare Corollary with no
  proof point (69IVa `nmiu-factors` follows at 3618), and the row's own note
  again says "The thesis gives no proof text"; that the Lean proof routes
  through 69II is our choice of route, not a printed argument matched.  stmt=ok
  is right: centrality is stated, `ker f = ⌈⌈f⌉⌉^⊥𝒜` is rendered as
  `f a = 0 ↔ ⌈f⌉·a = 0` (the same set for a central projection), and the
  point's other half `⌈f⌉ = ⌈⌈f⌉⌉` is the sibling `carrier_eq_cceilMap`.
- CONFIRMED — line 162, 69V `omega_conj_cceil_compl`.  Half of the printed proof
  69VI (vn.tex:3648–3666): `⌈⌈ω⌉⌉^⊥` is central and killed by `ω`, and
  `⌈a*qa⌉ ≤ q`, giving `ω(a*⌈⌈ω⌉⌉^⊥a) = 0`.  Auxiliary to 69V, whose own rows
  sit beside it.
