# `Theses/A/Proc/` — full survey of the remaining `sorry`s (worker 71, 2026-08-16; revised workers 72–81, sessions 47–58)

**Headline count: A/Proc has 64 code `sorry`s** after session 59.
Per file: `Tensor` **25** (was 31), `Measurement` **11**, `QuantumLambda` 17,
`Duplicators` **11**.  (`grep -c sorry` over-counts, because the file
docstrings mention `sorry` in prose; the code counts are the ones above.
Note `\bsorry\b` also matches "sorry-ed" in prose — count the compiler's
`declaration uses \`sorry\`` warnings instead.)


> **Session 59 — the normal-limit lemma is written, and **115II `exists_tmap`
> is CLOSED**, together with 115IV, 116I's existence half and 116III.5.**
>
> **The public lemma, in two shapes** (both in `Tensor.lean`, both
> axiom-clean).  "An operator-norm limit of normal functionals is normal" is
> **87III** `predual_complete` used as a closure property:
> * `continuous_ultraweak_of_normLimit` — on a single von Neumann algebra:
>   `predual_complete.isClosed`, four lines.  This is the shape **116III.5**
>   wants.
> * `exists_uwExtension_of_normLimit` — on `𝒜 ⊙ ℬ`: if `ν` is, uniformly in
>   the tensor product norm, a limit of restrictions `E ∘ γ_⊙` of normal
>   functionals on a tensor product `𝒯`, then `ν` is itself such a
>   restriction.  This is 112X.5's own Cauchy argument with "sum of members of
>   `Ω`" abstracted away, and `uwTensor_continuous_of_uwExtension` then reads
>   off `uwTensorTopology`-continuity (112X.3.1) and the bound (112X.2).
>
> **The brief's plan needed one repair: 112XI cannot be used to build the
> approximants.**  `BilinNormal`/`BilinBounded` are stated for the section
> variables `{A B C : Type u}` — *one* universe — so they cannot be
> instantiated at `C := ℂ`, and neither 112XI nor 114I applies to a
> `ℂ`-valued bilinear map.  Two replacements were written:
> `exists_uwExtension_odotF` (112IX's *factorisation*: for uw-continuous
> `f ∈ 𝒜_*`, `g ∈ ℬ_*`, `f ⊙ g = E ∘ γ_⊙` for a normal `E` on `𝒯` — `luws`
> splits `f`, `g` into four np-functionals each and `prodNP_lift` factors the
> sixteen products) and `nonneg_of_nonneg_on_tensorSpan` (114I.4 for
> functionals: a uw-continuous functional nonnegative on `γ_⊙(v* v)` is
> positive, by 74VI + `uwTendsto_starMul`).  As a bonus `exists_uwExtension_odotF`
> *is* the existence half of **116I** (`exists_predualTensor`), which fell out
> in three lines.
>
> **115II.**  `BilinBounded β` and `BilinNormal β` for `β(a,b) = f(a) ⊗ g(b)`
> both run through one object: for an np-functional `χ` on `𝒞 ⊗ 𝒟`, an
> np-functional `E_χ` on `𝒜 ⊗ ℬ` with `E_χ ∘ ⊗_⊙ = χ ∘ β_⊙`.
> * For `χ ∈ Ω` (`exists_extension_conjProdNP`) this is the thesis's
>   computation `χ ∘ β_⊙ = ∑ₖₗ σ(cₖ* f(·)c_l) ⊙ τ(dₖ* g(·)d_l)` fed to
>   `exists_uwExtension_odotF`; `E_χ` is positive by `BilinCP β` (with `c ≡ 1`)
>   plus `nonneg_of_nonneg_on_tensorSpan`, hence an np-functional, and
>   `npFunctional_norm_le` is the Russo–Dye step the thesis takes with
>   `cp-russo-dye`: `‖χ(β_⊙ t)‖ ≤ ‖f(1)‖‖g(1)‖ χ(1) ‖t‖`.
> * `BilinBounded` is then the thesis's argument verbatim: `tmap_cs` (banked in
>   session 58) gives `χ(β_⊙(t)*β_⊙(t)) ≤ ‖f1‖‖g1‖ χ(β_⊙(t* t))`, the bound
>   above gives `≤ ‖f1‖²‖g1‖²‖t‖²χ(1)`, and the *order-separating* half of
>   112X.1 turns that into `β_⊙(t)*β_⊙(t) ≤ (‖f1‖‖g1‖‖t‖)²·1`, i.e.
>   `‖β_⊙ t‖ ≤ ‖f1‖‖g1‖‖t‖` — the sharp constant, and no `tensorNorm C D`
>   bookkeeping (the route through `TensorProduct.map` was not needed).
> * `BilinNormal` is where the normal-limit lemma earns its keep: a general
>   `χ` is only an operator-norm limit of members of `Ω` (112X.1.2), and
>   boundedness transports that limit to `𝒜 ⊙ ℬ` with the factor `M`.
>   **The thesis's "incidentally, since each `ω∘β_⊙` is ultraweakly continuous,
>   so is `β_⊙`" is a gap, not a slip** — it is proved only for *basic* `ω`.
>   ERRATA's 115II row gained item (e).
> * `exists_tmap` is then 112XI + 114I(5) + 44XV, and `tensor_functorial`'s
>   four parts are 114I(1)(2)(3) plus one monotonicity step; **115IV** (both
>   functor laws) is `exists_tmap`'s own uniqueness clause, twice.
>
> **116III.5** `tensor_simple_facts_5` falls with the *single-algebra* shape of
> the lemma: `b ↦ χ(a ⊗ b)` is, uniformly on the unit ball of `ℬ` (because
> `‖a ⊗ b‖ ≤ ‖a‖‖b‖`, the new `norm_vtmul_le`), a limit of the ultraweakly
> continuous `∑ₖₗ σ(cₖ* a c_l) τ(dₖ*(·)d_l)`, hence ultraweakly continuous.
> Complete positivity of `a ⊗ (·)` is `a = x* x` and
> `star(x ⊗ bᵢ)(x ⊗ bⱼ) = a ⊗ (bᵢ* bⱼ)`; the nmiu-map `1 ⊗ (·)` is the same
> map with the miu clauses read off 108I.
>
> **116III.4 does *not* fall with it — the brief was wrong about that.**  Joint
> ultraweak continuity of `(a,b) ↦ a ⊗ b` is tested along nets in the
> *product*, and the error term `ε‖a‖‖b‖` is uniform only on bounded sets,
> while ultraweak neighbourhoods are norm-unbounded; `predual_complete` has
> nothing to close on.  Worth noting for the authors: ultraweakly convergent
> *sequences* are automatically norm-bounded (uniform boundedness in
> `(ℬ_*)^*`), so the exercise is only about nets, and we could neither prove
> it nor refute it.  Its hint's reduction ("`⊙ : 𝒜 × ℬ → 𝒜 ⊙ ℬ` ultraweakly
> continuous, which boils down to `(a,b) ↦ ∑ᵢⱼ σ(aᵢ*a aⱼ)τ(bᵢ*b bⱼ)`") proves
> exactly the *separate* statement, which is 116III.5's half.
>
> **Next gate, precisely.**  In `Tensor.lean` the cheap remainder is now
> gated on two independent facts, neither of which is the normal-limit lemma:
> (i) the **`≥` half of 116III.2**, `‖a‖‖b‖ ≤ ‖a ⊗ b‖` (the `≤` half is proved
> as `norm_vtmul_le`), which wants "`‖x‖ = sup over np-functionals with
> `ω(1) ≤ 1`" — `order_separating_norm` (21VII) is stated for *unital* maps,
> so the rescaling is the work; and (ii) **116IV.1** `tensor_generation_1`,
> for which separate ultraweak continuity (now available on the right, and by
> symmetry on the left) plus closedness of the ultraweak closure of a
> submodule is the thesis's own two-step argument — the missing ingredient is
> that `ultraweak` makes the algebra a topological vector space, which the
> tree does not record.  **118IV.4** (129X's blocker) was *not* attempted: the
> thesis proves it through 118IV.2/.3, a spatial argument needing
> `carrier-vector-state` and the double commutant, and it is a genuine
> development rather than a corollary.  One more trap found: **`exists_tmapM`
> is *not* a corollary of `exists_tmap`** — it is stated in four *different*
> universes `u₁…u₄`, while `exists_tmap` (like `BilinNormal`, `BilinBounded`,
> 112XI and 114I) lives in a single `Type u`; making the `tmap` construction
> universe-polymorphic is a prerequisite for it and hence for 119V.


> **Session 58 — 114I and 114II are CLOSED; 115II is *not*, and its two
> remaining hypotheses are each a real piece of work, not a corollary.**
>
> * **114I** `tensor_universal_property_extra` (all five parts, ~180 lines).
>   Its hypotheses `hn`, `hb` are **not used**: the extension `g` is given, so
>   every clause is an identity on the ultraweakly dense ∗-subalgebra
>   `γ_⊙(𝒜⊙ℬ)` pushed to `𝒯`.  The linear clauses (1)–(3) go by separate
>   ultraweak continuity (**45IV** `mult_uws_cont` and the new
>   `continuous_ultraweak_star`).  The *quadratic* clauses (4)–(5) do not:
>   the new **`uwTendsto_starMul`** (`s_α* t_α → s* t` **ultraweakly** along a
>   norm-bounded ultrastrong net — Cauchy–Schwarz for `‖·‖_ω`, **72III**.1b)
>   plus ultraweak closedness of the positive cone (**44XI**.2) is what
>   carries them.  For (5) the `n` arguments have to converge *simultaneously*:
>   the trick that works is the **product filter** `Filter.pi` over the `n`
>   nets of **74VI**, which needs no `NeBot` side condition (`Fin 0` included).
>   The base case of (5) — families from `γ_⊙(𝒜⊙ℬ)` — is `BilinCP β`
>   re-indexed along `finSigmaFinEquiv`, because `BilinCP` only quantifies over
>   *pure* tensors while `γ_⊙(𝒜⊙ℬ)` consists of sums of them.
> * **114II** `tensor_uniqueness` (~55 lines) is then exactly as advertised:
>   `BilinNormal γ' = (tensor_basic_3 γ' hγ').1`, `BilinBounded γ'` is
>   `tensor_basic_2` with `M = 1`, 112XI both ways, the two composites are the
>   identity by 112XI's own uniqueness clause, miu-ness is 114I.1/.2/.3 read off
>   `hγ'.miu`, normality is `starAlgEquiv_preservesDirSups'`, and uniqueness
>   among nmiu-maps uses **44XV** `p_uwcont` (3)⇒(1) to make an arbitrary
>   nmiu-map ultraweakly continuous.
>
> **115II `exists_tmap`: what is actually left.**  With `β(a,b) = f(a) ⊗ g(b)`:
> `BilinCP β` is `cp_bilinear_comp` (one line); the extension, its complete
> positivity and its normality are then 112XI + 114I(5) + `p_uwcont`.  The two
> real gaps are `BilinBounded β` and `BilinNormal β`.
> * **`BilinBounded β` — the hard half is now banked.**  proc.tex:3210 needs
>   `β_⊙(s)*β_⊙(s) ≤ ‖f‖‖g‖ β_⊙(s* s)`, which it gets from `cp-cs` applied to
>   the amplification `M_n f` and an `M_n ⊗` computation.  **That inequality is
>   proved and axiom-clean in the file as `tmap_cs`**, by a route that never
>   amplifies: the new **`cp_cs_sum`** is `cp-cs` for a *vector* of arguments
>   (apply `cstar_positive_2x2matrix` to the 2×2 compression of the positive
>   matrix `(f(vᵢ* vⱼ))` along `v = (a₁,…,a_n,1)`; the compression is positive
>   by `cstar_matrix_positive_iff` at `w = (c₁x,…,c_nx,y)`), and `tmap_cs`
>   splits `‖f1‖‖g1‖ Q⊗Q' − P⊗P'` as `P⊗R' + R⊗P' + R⊗R'` with
>   `R = ‖f1‖Q − P ≥ 0`, each summand positive by
>   `Theses.A.CStar.matBilin_nonneg_of_mi`.
>   What remains for `BilinBounded` is the *other* promise of proc.tex:3175,
>   `‖ω∘β_⊙‖ ≤ ‖f‖‖g‖` for a basic `ω` on `𝒞⊙𝒟` with `ω(1) ≤ 1`.  The route is
>   the thesis's, and every input is proved: write `ω = χ ∘ ⊗_⊙` with
>   `χ = conjProdNP σ τ v ∈ Ω` (`exists_conjProdNP_of_isBasicFunctional`) and
>   `v = ∑ₖ cₖ ⊗ dₖ`; then
>   `χ(β(a,b)) = ∑ₖₗ σ(cₖ* f(a) c_l) · τ(dₖ* g(b) d_l)`, so `χ ∘ β_⊙` is a
>   finite sum of `odotF`s of bounded ultraweakly continuous functionals, hence
>   bounded *and* `uwTensorTopology`-continuous by **112IX**
>   `product_functional`; **112XI** then extends it to `ω'` on `𝒜⊗ℬ` **with the
>   same bounds** (112XI's second clause), `ω'` is positive by **114I**(4)
>   (`BilinCP β` with `c ≡ 1`), so `‖ω'‖ = ‖ω'(1)‖ = ‖χ(f1 ⊗ g1)‖ ≤ ‖f1‖‖g1‖`
>   by `russo_dye_cor` and `npFunctional_norm_le`.  Feeding that back through
>   112XI's bound clause gives `‖ω(β_⊙ t)‖ ≤ ‖f1‖‖g1‖ ‖t‖`, and combining with
>   `tmap_cs` inside `tensor_basic_2`'s supremum finishes.  Estimate: ~150 lines.
> * **`BilinNormal β` is the genuine gate, and it is NOT a corollary of 112IX +
>   112X.1.2.**  Continuity into `ultraweak (𝒞⊗𝒟)` has to be tested against
>   *every* np-functional `χ` on `𝒞⊗𝒟`, and only the members of `Ω` come with
>   the `∑ₖₗ odotF` decomposition above.  112X.1.2 makes a general `χ` an
>   *operator-norm* limit of finite sums from `Ω`, and passing that through
>   `β_⊙` gives a limit that is uniform only relative to `tensorNorm` — this is
>   the **same dead end already recorded for 116III.4** (a `tensorNorm`-uniform
>   limit of `uwTensorTopology`-continuous functionals need not be continuous).
>   Two escapes that do *not* work, both checked: (i) `simple ∘ (f⊙g)` is not
>   simple (basic functionals are `(σ⊙τ)(t₀*(·)t₀)` and `f⊙g` does not commute
>   with the conjugation), so `NormLimitOfSimple` is not preserved; (ii) using
>   112X.5 to replace `uwTensorTopology (𝒞,𝒟)` by the topology induced from
>   `𝒞⊗𝒟` turns the goal back into itself.  **The route that should work** is
>   the one 112X.5 itself takes: each `∑ᵢχᵢ ∘ β_⊙` is `Eₙ ∘ γ_⊙^{𝒜ℬ}` for an
>   ultraweakly continuous `Eₙ` on `𝒜⊗ℬ` (112XI again); `‖Eₙ − Eₘ‖` is
>   controlled on the *whole* algebra because **74VI** makes the unit ball of
>   `γ_⊙(𝒜⊙ℬ)` ultrastrongly dense in the unit ball of `𝒜⊗ℬ`; **87III**
>   `predual_complete` (proved) gives the limit `E`, and `χ ∘ β_⊙ = E ∘ γ_⊙`
>   is then `uwTensorTopology`-continuous by **112X**.3.1.  Estimate: ~150 lines.
>   *The same lemma — "an operator-norm limit of normal functionals is normal",
>   i.e. `predual_complete` used as a closure property — is what 116III.4 and
>   116III.5 need too*, so it is worth writing once, publicly, in `Tensor.lean`.
>
> **New in `Tensor.lean`, all axiom-clean:** `continuous_ultraweak_star`,
> `uwTendsto_starMul` (both in a new `DensityAux` section, universe-polymorphic
> and hypothesis-minimal), `cp_cs_sum`, `tmap_cs`.
> **ERRATA gained a 115II row** (four slips in parsec 1150, including
> `(f⊗g)(a⊗b) = f(a)⊗f(b)` in the statement itself).
> **Correction to the session-57 note:** its one-line summary of 115II
> ("needs `BilinNormal` + `BilinBounded`, then 112XI plus 114I(5)") is correct
> but hides that each of those two is a ~150-line development in its own right.

> **Session 57 — 112X IS CLOSED WHOLE (all five parts) AND SO IS 112XI
> `tensor_universal_property`.  A/Proc has no external frontier at all.**
> The session-55/56 notes below are correct but their blocker lists are now
> stale in the decisive place: **A/VN session 56 finished
> `NormalFunctionals.lean`**, so **86IX** `polar_decomposition_of_functional`
> and **87III** `predual_complete` — the last two external gates, which the
> notes below still list as `sorry` — were already proved when this session
> started.  112X.4 and 112X.5 were therefore local, not blocked, and with
> them 112XI.  `Tensor.lean` 38 → 33; A/Proc **77 → 72**.
>
> * **112X.2** `‖γ_⊙ s‖ = ‖s‖`.  The route in the session-55 note (rescale
>   `Ω` to the unital `Ω₁`, apply **21VII** `order_separating_norm`) was not
>   used and is *not* needed: the `≤` half is 112X.1's order-separating
>   conjunct applied directly at `γ_⊙(s)*γ_⊙(s) ≤ ‖s‖²·1`, which is 21VII's
>   own argument with the `Ω → Ω₁` renormalisation left out.  The predicted
>   "sSup bookkeeping" reduced to one private lemma, `basic_star_self_le`
>   (`ω(s* s) ≤ ‖s‖²ω(1)` for every basic `ω`, by rescaling `ω` by `ω(1)⁻¹`
>   — the `ω(1) = 0` branch is `basic_norm_le_tensorNorm`).  The `≥` half is
>   `χ(γ_⊙(s)*γ_⊙(s)) ≤ ‖γ_⊙ s‖²χ(1)` through
>   `exists_conjProdNP_of_isBasicFunctional`.
> * **112X.3** is 112X.1's second conjunct restricted along `γ_⊙`
>   (`isBasicFunctional_comp_lift` makes each summand basic, 112X.2 converts
>   `ε‖γ_⊙ t‖` to `ε‖t‖`), plus `iInf_le` for the continuity half.
> * **112X.4** `‖f ∘ γ_⊙‖ = ‖f‖` is the thesis's argument verbatim: **86IX**
>   gives the partial isometry `u` with `f(u) = ‖f‖` (**86XI**
>   `functional_norm`), **74VI** approximates it with `‖s_α‖ ≤ ‖u‖(1+ε)`,
>   and 112X.2 converts the bound.
> * **112X.5**: the extension is the thesis's route through **87III**, with
>   112X.4 supplying the isometry that makes the approximating sequence
>   Cauchy in `𝒯_*`; the limit is positive by a re/im argument and normal by
>   `preservesDirSups_of_continuousOn_effects_functional` (banked by A/VN in
>   session 56 — it is exactly what turns an ultraweakly continuous positive
>   functional into an `NPFunctional`).  The topology equality is
>   `le_antisymm` of 112X.3's first conjunct and `induced_mono` applied to
>   the factorisation just obtained.
> * **112XI** is **77V** `vn_extension` on `S = tensorSpan γ`, exactly as
>   proc.tex:2998 says.  The "trivial details" the thesis waves at are two:
>   the inverse `γ_⊙⁻¹ : S → 𝒜⊙ℬ` (`γ_⊙` is injective because it is an
>   isometry, 112X.2) built by `choose`, and the `‖β_γ‖ ≤ ‖β_⊙‖` half, which
>   needs the same 74VI approximation as 112X.4 plus a new
>   `norm_le_of_uwTendsto` (the ultraweak twin of `norm_le_of_usTendsto`,
>   from `isClosed_ultraweak_closedBall`).
>
> **The next gate is 115II `exists_tmap`**, which now has no external
> blocker: it needs `(a,b) ↦ f a ⊗ g b` to be a *normal bounded* bilinear
> map, i.e. `BilinNormal` + `BilinBounded` for it, and then 112XI plus
> 114I(5).  114I and 114II are also local now.

> **Session 55 — 112X.1 IS PROVED; the external frontier is down to two
> `sorry`s, and `Tensor.lean`'s next gate is 112X.2, which is in *this*
> chapter.**
> The session-54 note below is correct about the *chain* but its blocker list
> is now stale in one place: **90II.2 `vn_center_separating_fundamental_2` was
> closed by the A/VN worker in session 55**, and with it **112X**.1
> `tensor_basic_1` is now **proved and axiom-clean** — both conjuncts:
> * *order separating*: `nonneg_of_conjNP_of_centreSeparating` (30X) fed with
>   the product functionals, which are `CentreSeparatingConj` for the trivial
>   reason that faithfulness (condition (3) of 108II) is the `b = 1` case; the
>   hypothesis only conjugates by `γ_⊙(s)`, and the gap to arbitrary `c ∈ 𝒯`
>   is closed by **74VI** `dense_subalgebra` (a norm-bounded net from
>   `γ_⊙(𝒜⊙ℬ)` converging ultrastrongly) plus **72III**.1c
>   `bstaromega_lipschitz`;
> * *norm-limit-of-sums*: a direct application of **90II**.2 to the collection
>   of product functionals and to the ultrastrongly dense ∗-subalgebra
>   `γ_⊙(𝒜⊙ℬ)`.
>
> Banked infrastructure (all in `Tensor.lean`, all axiom-clean): `tensorSpan`
> (the ∗-subalgebra `γ_⊙(𝒜⊙ℬ)`), `range_lift_eq_span`, `prodFunctionals`,
> `eq_prodNP`, `centreSeparatingConj_prodFunctionals`,
> `dense_ultrastrong_tensorSpan`, `lift_one/lift_mul/lift_star` (`γ_⊙` is a
> ∗-homomorphism), `prodNP_lift` (`γ(σ,τ) ∘ γ_⊙ = σ ⊙ τ`), `conjProdNP` (the
> collection `Ω` of 112X.1), `isBasicFunctional_comp_lift` and
> `exists_conjProdNP_of_isBasicFunctional` — the last two are the *second*
> half of 112X.1's exercise text (`Ω ↔ basic functionals`), which our Lean
> statement of part 1 does not carry.
>
> **The next gate is 112X.2 `tensor_basic_2` (`‖γ_⊙ s‖ = ‖s‖`), and it is
> A/Proc-local.**  With 112X.1 in hand the thesis's route is: the unital
> members `Ω₁` of `Ω` are order separating (rescale `σ`), so **21VII**
> `order_separating_norm` (proved, `A/CStar/Positive.lean`) gives
> `‖a‖ = ⨆_{ω∈Ω₁} ‖ω a‖` for positive `a`; apply it at
> `a = γ_⊙(s)*γ_⊙(s) = γ_⊙(s*s)` and match the resulting supremum with
> `tensorNorm`'s, using the bijection `Ω ↔ basic functionals` above (which
> also matches the subunitality conditions, since
> `conjProdNP hγ σ τ s 1 = odotF σ τ (star s * 1 * s)`).  The remaining work
> is the sSup/iSup bookkeeping (squares vs. square roots; subunital vs.
> unital sups).  112X.3 follows from 112X.1's second conjunct once 112X.2
> supplies the norm bound, and 112X.3 then unblocks **116III**.4/.5,
> **116IV**.1 and **118II**.
>
> **A/Proc's external frontier is now two `sorry`s in
> `A/VN/NormalFunctionals.lean`: 87III `predual_complete` (gates 112X.5,
> hence 112XI, 114I, 114II, 115II) and 86IX
> `polar_decomposition_of_functional` (gates 112X.4 and, via 116I, 116III.3;
> 87VI `norm_predual` is the other half of 116III.2).**
>
> **Also this session:** all eight `CentreSeparating` uses in `Tensor.lean`
> were migrated to `CentreSeparatingConj` (= cstar.tex **21II**.4, the
> thesis's notion) — 116IV.2 `tensor_generation_2` (3), 116VII
> `tensor_characterization` (3), 117II.2 `sum_generation_2` (2).
> `sum_generation_2` was reproved and is *shorter* under the correct notion:
> the centrality argument disappears entirely (test `a` against `ω ∘ πᵢ`
> conjugated by `κᵢ(b)`).  A/VN's auxiliary `CentreSeparating` now has **no
> A/Proc consumer**; its only remaining use in the tree is inside a proof at
> `A/VN/Basic.lean:1837`, so A/VN may retire it.
>
> **Two corrections to the tables below.**
> 1. **129X is not behind 115II.**  The row "129X needs the product functional
>    `ω ⊗ ω` and `carrier-tensor` faithfulness (118IV), both behind 115II" is
>    wrong on both counts: `prodNP` produces `ω ⊗ ω` straight out of
>    `IsTensorProduct.prod_exists` (no `tmap`), and **118IV.4**
>    `carrier_tensor_4`'s *statement* mentions no `tmap` either — it is about a
>    product np-functional `χ` on `𝒜 ⊗ ℬ`.  129X's blocker is therefore
>    **118IV.4, inside this chapter**, together with the dyadic-partition
>    construction of proc.tex:6395 (`continuous_measure_space` is already
>    proved in `Duplicators.lean`).
> 2. **The D1 `smul` fix does not unblock 129X/130IV/130V.**  It is necessary
>    (without ℂ-linearity `ψ : z ↦ q(const z)` need not be the algebra map) but
>    it is not what is missing.  130IV needs a genuine build: the ∗-algebra
>    isomorphism `𝒜 ≅ ⊕ₙ ℬₙ`, `q f ↦ (qB n f)ₙ`, whose *surjectivity* needs a
>    uniform bound on the representatives — given `y ∈ ℓ^∞(ℬ)` one must show
>    each representative `fₙ` is a.e. bounded by `‖y n‖`, which `IsLinftyOf`
>    does not record and which has to be derived from positivity of `q`
>    (`q(1_S)` is a nonzero projection when `μ S > 0`, and
>    `(y n·p)*(y n·p) ≥ (M+ε)²p` contradicts `‖y n‖ ≤ M`).  *Normality of the
>    resulting map is free*: a bijective ∗-homomorphism is an order
>    isomorphism, so `starAlgEquiv_preservesDirSups'` (already in
>    `Tensor.lean`) applies.  130V is blocked on 130IV alone, as recorded.

> **Session 54 correction — 112XI IS NOT UNBLOCKED BY 77V, and the whole
> `Tensor.lean` upper half is still shut.**
> The row "112XI | blocked on **77V** `vn_extension`" below was wrong, and so
> was the session-53 A/VN note that inherited it.  77V is now proved, and
> 112XI is still out of reach: proc.tex:2998 reads "since `β_⊙` is ultraweakly
> continuous and bounded, and `𝒜⊙ℬ` can **by `tensor-basic`** be considered an
> ultraweakly dense ∗-subalgebra of `𝒯` via `γ_⊙`, the theorem follows from
> `vn-extension`" — it cites **112X as well as 77V**, and all five parts of
> 112X are `sorry`.  Concretely, `vn_extension` wants a map `f : S → 𝒞` on a
> ∗-subalgebra `S ⊆ 𝒯` that is continuous for the topology **induced from
> `𝒯`** plus a bound `‖f s‖ ≤ C‖s‖_𝒯`, and building `f` from `β_⊙` needs
> (i) injectivity of `γ_⊙` (well-definedness; available from 112X.2, or by a
> separate product-functional separation argument);
> (ii) `uwTensorTopology ≤ induced(γ_⊙, ultraweak 𝒯)` — equivalently, every
> norm-limit-of-simple functional on `𝒜⊙ℬ` is the restriction of a normal
> functional on `𝒯`, which is exactly **112X.5**'s first half, whose own hint
> is **87III** `predual_complete` (`A/VN/NormalFunctionals.lean:889`,
> `sorry`).  This is not a Lean artefact: continuity for an *induced* topology
> is equivalent to extendability of the testing functionals, so no amount of
> `BilinNormal β` (continuity for the *finer* `uwTensorTopology`) substitutes
> for it;
> (iii) the norm bound, which converts `hb`'s tensorNorm bound through
> **112X.2** `‖γ_⊙ s‖ = ‖s‖`, resting on **90II.2**
> (`NormalFunctionals.lean:3336`, `sorry`).
> **So A/Proc's external frontier is now three `sorry`s in one A/VN file,
> `NormalFunctionals.lean`: 87III `predual_complete`, 90II.2
> `vn_center_separating_fundamental_2`, and 86IX
> `polar_decomposition_of_functional` (needed by 112X.4).**  Everything above
> them — 112X, 112XI, 114I, 114II, 115II, 116VII and the whole
> functoriality/monoidal block — stays shut.
> **Closed instead this session, all in `Duplicators.lean` and all following
> the thesis's own proofs:** **127VI** `unit_duplicator`, **128VIII**
> `uniqueness_duplicator` (a duplicable von Neumann algebra is commutative and
> its duplicator is multiplication), **128XI** `duplicability_multiplication`,
> **127III**-uniqueness `duplicable_unique`, **132III**.1
> `dup_vna_is_monoid_1` and **132III**.3 `dup_vna_is_monoid_3`.  128VIII cost
> ~90 lines: **128VI** `sef_instrument` and **128II** `tomiyama` were already
> proved in the file, and the only new machinery is that the effects span `𝒜`
> linearly (`mem_span_effects`, `effects_induction`), which is what the
> thesis's "by the usual reasoning" appeals to.
> **128XIII** `duplicable_product` is *not* reachable: the thesis builds
> `π₁ ∘ δ ∘ (κ₁ ⊗ κ₁)`, and `κ₁ ⊗ κ₁` needs `tmap`/`tmapM`, i.e. **115II**.

> **Session 52 update — THE VACUOUS BAND IS OPEN: 111VII and 111XII are
> proved and axiom-clean.**
> `special_tensor` (**111VII**), `vnTensorProduct_exists` and
> `vnTensorProduct_nonempty` (**111XII**, unbundled and bundled) are proved,
> so `vnTensor`, `VNT` and `⊗ᵥ` are now axiom-clean *definitions*.
> **What that buys, measured rather than estimated: exactly 12 previously
> `sorryAx`-tainted declarations became clean — the 3 theorems above plus
> the 9 definitions built from them** (`vnTensor`, `VNT`, `vtmul` in
> `Tensor`; `tensorSub`, `TensorBSurjective` in `QuantumLambda`;
> `Duplicator`, `Duplicable`, `MonoidInWcpsu`, `MonoidInWmiu` in
> `Duplicators`).  **None of the 54 band members flips to clean by itself**
> — every one of them is still a `sorry`; what changed is that their
> statements are no longer vacuous, so proving one now *yields* an
> axiom-clean theorem.  First one done: **116III.1**
> `tensor_simple_facts_1` (+ the reusable `vtmul_nonneg`), which is three
> lines of `a ⊗ b = (√a ⊗ √b)*(√a ⊗ √b)` off miu-bilinearity.
> Session-51's analysis of 111VII was right in every detail; the one thing
> it did not foresee is that the *bundled* 111XII has its two algebras in
> **different universes** while the spatial construction needs both Hilbert
> spaces in one, which cost a `ULift` Hilbert-space instance and
> universe-polymorphic re-proofs of four `A/VN` lemmas (see PROVING-LOG
> session 52 §3).
> **The next gate for `Tensor.lean` is now 112XI `tensor_universal_property`
> (blocked on A/VN 77V `vn_extension`)**, which gates 114I, 114II and — with
> 112X — 116VII; and **115II `exists_tmap`**, which gates all of the
> functoriality/monoidal block (115IV, 115V, 118IV, 119II–119V).

> **Session 51 update — parsec 1020 is closed, and the next gate is 111VII,
> which is in *this* chapter.**
> **102VII** `canonical_quotient_rigid` and **102IX** `pure_is_rigid` are
> **proved and axiom-clean**, together with the index-free `ad_rigid` (any
> `d*(·)d : ⌈d⌉ᵣ𝒜⌈d⌉ᵣ → 𝒜` is rigid) and `stdFilter_rigid`.  102VII cost
> ~210 lines and needed nothing the tree lacked; the only real step is the
> compression `x ↦ eₙ h(x) eₙ` being the identity by **102V** `nmiu-rigid`
> (private `compress_eq_of_ceil`).  Three corrections to what follows:
> (i) **81V `douglas` is proved** — `A/VN/Division.lean`'s seven `sorry`s do
> not include `douglas_1/2` or `sequential_quotient_1`; only **81VIII.2**
> `sequential_quotient_2` and **81IX.2** `div_usc` remain of that block, so
> the "104III.3/.4/.5 → 81V/81VIII" row below is half stale (those three are
> unsolved *exercises* about `div`/`pinv`/infima, not blocked items).
> (ii) **111VII `special_tensor` is NOT in the vacuous band** — its statement
> mentions no `VNT`; it is what *gates* the band, and the table under "(c)"
> should not list it.
> (iii) **111VII is now A/Proc-local.**  Session 50 supplied the last A/VN
> input to `tensor-2` (89IX + `exists_sumVectorNP`); `tensor-1` is **88VI**
> `double_commutant` (proved: `W*(S)` = the ultraweak closure of a unital
> ∗-subalgebra, and the span of the range of `⊗` is one, since
> `(A⊗B)(C⊗D) = AC⊗BD`); `tensor-3` is the thesis's `√T·x⊗y = 0` argument
> plus `(hilbTensor H K).isTensor.dense`.  Only miu-bilinearity of `opTensor`
> ("left to the reader") is genuinely unwritten.  **111VII → 111XII
> un-vacuums 54 of the 88 remaining statements and is the highest-leverage
> target in the chapter.**

> **Session 49 update — 100III is proved, and the parsec-1000 gate is open.**
> **100III** `pure_fundamental`, **100VII**.1/.2/.3 `special_pure_maps_*`,
> **105III**.4 `chevron_f_basic_4` and **105IV**.1/.3
> `chevron_f_purely_positive_1/3` are **proved and axiom-clean**.
> Two corrections to what follows:
> (i) **98XI `ad-pure` was not needed** — (1)⟹(2) reduces to "`π_s ∘ c_p` is
> properly pure", and that factors directly as (filter)∘(corner) with
> `a := √p·s`: `x ↦ ⌊a⌉x⌊a⌉` is a corner `⌈p⌉𝒜⌈p⌉ → ⌊a⌉𝒜⌊a⌉` and `a*(·)a` a
> filter `⌊a⌉𝒜⌊a⌉ → s𝒜s`, so no polar decomposition and no iterated corners.
> 98XI is still **not transcribed**, and reading it produced ERRATA **98XI**
> (its `[f] = [a](·)[a]*` has the brackets swapped).
> (ii) **our `IsPure` (100I) was mis-transcribed** — no von Neumann hypothesis
> on the algebra in the middle of a composition, which makes (1)⟹(2)
> unprovable; `[VonNeumannAlgebra B]` was added to the `comp` constructor
> (PROVING-LOG session 49 §1).
> **The chain above 100III is now blocked only by A/VN**: 104III.3/.4/.5 wait
> on 81V `douglas` / 81VIII `sequential-quotient`, and 104VII → 104IX →
> 105V-uniqueness → 105VII / 106I-uniqueness behind them.  The one big
> *reachable* item left in `Measurement.lean` is **102VII**
> `canonical_quotient_rigid` (and 102IX behind it).

> **Session 48 update — both parsec-980 blockers are gone.**
> **98III** `filters_composition` and **98VI** `corners_composition` are
> **proved and axiom-clean**, and neither needed the machinery the previous
> two surveys expected: 98III needs no `⌊√p'√q⌉ = ⌈p'⌉` (see below), and 98VI
> needs neither the printed hint nor its converse.  Also closed: **103II**.1/.2
> (`purely_positive_examples_1/2`), **105III**.1-2 (`chevron_f_basic_12`),
> **105V** existence (`positive_map_uniqueness_exists`) and **106I** existence
> (`uniqueness_sequential_product_exists`).  **The single blocker of the whole
> parsec 1000–1060 chain is now 100III `pure_fundamental`**, and inside it the
> one hard implication (1)⟹(2), which needs **98XI `ad-pure`** — the statement
> that `[a*(·)a] = [a](·)[a]*` is an ncpu-isomorphism.  `ad-pure` is an
> *Example* in proc.tex and **is not transcribed in the Lean file at all**; it
> needs 82I `polar-decomposition` (proved, A/VN) plus corner bookkeeping.
> Everything else in 100III is short: (2)⟹(3) is the uniqueness clause of
> 98IX, and (3)⟹(1) is `f = c_{f(1)} ∘ [f] ∘ π_{⌈f⌉}` with an iso in the
> middle (an ncp-isomorphism is a filter — see `isPure_of_iso`).

> **Session 47 update — 96V is proved, and the Measurement chain is open.**
> `canonical_filter` (**96V**) is closed and axiom-clean, and does **not**
> need the false conjunct of 81IX: only 81VI.1/.2 and 81VII (all proved) are
> used, and the thesis's `div-usc` step for *normality* is replaced by an
> elementary bipositivity argument (ERRATA row **96VI**).  Two corrections to
> the map below follow: (i) our Lean statement of 96V used `suppProj d` where
> the thesis has `\ceilr{d} = rangeProj d`, which made it **false** — fixed;
> (ii) with `isFilter_stdFilter` in place, the parsec-980 block is no longer
> one undifferentiated block behind 96V.  **Closed in session 47:** 96V,
> 98II.1, 98II.2, 98II.3, 98VII, 98VII-formula, 98IX `exists_sqBracket`,
> 98IX `square_f`, 100II.3.  **Still blocking the rest of parsec 980–1000:**
> **98III** `filters_composition` and **98VI** `corners_composition`, which
> together gate 100III `pure_fundamental` and everything above it.

## Classification summary

| class | count | share |
|---|---|---|
| (c) **vacuous band** — statement mentions `VNT`/`⊗ᵥ`/`Duplicator`, hence depends on `sorryAx` through **111XII**; can never be closed axiom-cleanly until 111XII is | **56** | 64% |
| (b) blocked on a *named* `sorry` outside A/Proc, or on another A/Proc `sorry` | **~24** | 27% |
| (a) self-contained / reachable now | **4** (124I, 125II, 125cIII, 130IV) | 5% |
| (c′) cited to literature, no thesis argument at all | **1** (121II) | 1% |
| (d) suspicious | **0 new** (3 already-known false statements are recorded and realigned) | |

*(Recomputed in session 51 against the current 88.  `QuantumLambda` and
`Duplicators` were surveyed per-declaration for the first time; the earlier
band figures for those two files were both wrong, in opposite directions.
`Measurement`'s and `Tensor`'s rows have not been re-derived — the per-item
tables below are the current record.)*

The two blockers that gate almost everything:

* **89IX `normal_functional`** (`A/VN/NormalFunctionals.lean:1727`, `sorry`) —
  gates **111VII** `special_tensor`, hence **111XII**, hence the whole
  54-statement vacuous band.  48VIII `ngns` (the other input to 111XII) **is
  proved**, so 89IX is the *only* thing between A/Proc and un-vacuuming 47% of
  the chapter.  **This is by a wide margin the highest-leverage item for
  A/Proc, and it is in A/VN, not here.**
* ~~**81VI / 81VII / 81IX** gate **96V**~~ — **resolved.** 81VI.1/.2, 81VII,
  81V.1/.2 and 81VIII.1 are proved (session 46), and 96V is proved from them
  (session 47).  81IX's false second half is **not** needed.

## (a) Reachable now

| DISP | decl | file:line | note |
|---|---|---|---|
| **99XI** | `filter_of_projection_multiplicative` | Measurement 2601 | **CLOSED this session** |
| **106III**.1 | `sequential_product_counterexample_1` | Measurement ~4281 | **CLOSED this session** — was unblocked by the new `isFilter_cornerIncl`: axiom (B) needs `⌈p⌉(·)⌈p⌉` to be *pure*, which is `corner ; filter` with the filter being the corner inclusion of a projection.  (C) collapses to `⌈p⌉q⌈p⌉ = ⌈p⌉q⌈p⌉`, (D) is `q := p`, (E) reduces to `e₁⌈p⌉e₂ = 0` being star-symmetric (no contraposition theory needed), and ¬(A) needs `⌈½·1⌉ = 1 ≠ ½·1`. |
| **98II**.2 | `filter_basic_2` | Measurement 2018 | **two of the three conjuncts are directly provable** — see "the near miss" below |
| **124I** | `vn_generation_bound` | QuantumLambda 678 | pure cardinal arithmetic on `wstar S`; no thesis proof, no dependency on anything sorried |
| **125II** | `vn_gns_bound` | QuantumLambda 729 | `ngns` + a cardinality count of the GNS direct sum; `ngns` is proved |
| ~~**129X**~~ | `continuous_finite_measure_space_not_duplicable` | Duplicators 725 | **REMOVED (session 51)** — `hd : Duplicable 𝒜` is in the *type*, so it is tainted after all; and proc.tex:6367 really does use the product functional `ω⊗ω` and `carrier-tensor` faithfulness |
| **130IV** | `measure_space_partition` | Duplicators 1019 | (a) — its recorded obstruction has been discharged; see the `Duplicators` table |
| **125cIII** | `Fha_concrete` | QuantumLambda 894 | (a) but long — nothing it needs is `sorry` |

### The near miss: 98II.2 `filter_basic_2` — **superseded (session 47)**

*Kept for the record; 98II.2 was closed the thesis's own way, through 98II.1,
once 96V made `c_p` a filter.  The ℂ-gadget below is still the cheapest new
infrastructure in the chapter, but nothing in parsec 980 needs it any more.*


Worth writing down because it is a genuinely short route the thesis does not
take, and because it stops one gadget short.

* **mono in `W*_cp`** is immediate from `IsFilter.universal`'s *uniqueness*
  clause once `g`, `h` are rescaled into the unit ball by `s⁻¹` with
  `s = ‖g 1‖ + ‖h 1‖ + 1` (the universal property demands `f 1 ≤ c 1`, which
  an arbitrary ncp-map does not satisfy).  `exists_ncpSmul` +
  `Theses.A.CStar.ofReal_smul_nonneg` + `algebraMap_ofReal_mono` do it in
  ~20 lines.  Written and type-checked during the session.
* **`c z = 0 ⟹ z = 0` for positive `z`** then follows from mono applied to
  `√z(·)√z` and the zero map: for positive `x`, `√z x √z ≤ ‖x‖·z`, so
  `c(√z x √z) = 0`; extend to all `x` by `x = ℜx + i·ℑx`, `y = y⁺ − y⁻`.
  Hence **faithfulness `⌈c⌉ = 1` is reachable**.
* **Injectivity is not**, and the obstruction is precise: it needs mono at
  `B = ℂ`, i.e. the ncp-map `ℂ → C`, `ζ ↦ ζ·a` for positive `a`.  **The tree
  has no ncp-map out of `ℂ`** — no `algebraMap` as an `NCPMap`/`NMIUMap`, and
  `cp_commutative_dom` (34IX.2) is itself `sorry`.  Building it needs
  (i) `M ≥ 0` in `M_k(ℂ)` implies `M.map (algebraMap ℂ C) ≥ 0` (route:
  `M = star X * X`, and `CStarMatrix.map` of a ∗-hom is multiplicative), and
  (ii) `algebraMap ℂ C` preserves directed suprema (route: a LUB of reals is
  in the closure of the set, and the positive cone of `C` is norm-closed).
  **That gadget is reusable and would close 98II.2 outright**; it is the
  single cheapest piece of new infrastructure in this chapter.

Since the statement is one conjunction, the two provable clauses cannot be
banked separately, so the `sorry` stands.

## (c) The vacuous band — 56 statements behind 111XII

*(Recounted per-declaration in session 51: `QuantumLambda` is 10, not 13, and
`Duplicators` is 14, not 9.  **111VII `special_tensor` is not in the band** —
its statement mentions no `VNT`; it is what gates the band, and it has been
removed from the `Tensor.lean` list below, which is therefore 31.)*

**Session 52: this band is no longer vacuous.**  `vnTensorProduct_nonempty`
is proved, so `vnTensor`/`VNT`/`⊗ᵥ` are axiom-clean and every statement below
is now a real (provable, and once proved axiom-clean) obligation rather than a
vacuous one.  The list is kept because it is still the list of open `sorry`s;
strike 111XII ×2 (proved) and 116III.1 (proved, session 52).  Historical note:
their *types* mention `VNT 𝒜 ℬ = (vnTensor 𝒜 ℬ).carrier`, and `vnTensor` used
to be `Nonempty.some` of the sorried `vnTensorProduct_nonempty`.

* `Tensor.lean` (25, of which 111XII ×2, 116III.1, **115II ×2, 115IV ×2,
  116I's existence half and 116III.5** are now closed): ~~115II ×2~~,
  ~~115IV ×2~~, 115V, 116I (`product_functional_norm`; `exists_predualTensor`
  is closed), 116III.2/.4, 116IV.1/.2, 117III, 118II ×2, 118IV.1/.4/.5/.6,
  119II, 119IV, 119IVb, 119IVc, `exists_tmapM`, 119V ×5.  (`tensor_simple_facts_3` and `product_functional_norm`
  are tainted too — via `predualTensor`, itself chosen from a sorried existence.)
* `QuantumLambda.lean` (10): 123II.1/.2, 125IV, 125VI, 125VIIb, 125VIII,
  125dII, 125eIIa, 125eIII, 125eVII.  **Not** tainted (corrections, session 51):
  **121II** (it is about the *concrete* Hilbert-space tensor product, whose
  `hilbTensor` comes from the **proved** `hilbertTensor_nonempty`), **125bII**
  and **125cIII** (`HaFreeMIU` / `MatAlg` / `lp` contain no `VNT`, and the
  `VonNeumannAlgebra (MatAlg n)` instance `Theses.A.VN.mn_vna_1` is proved).
* `Duplicators.lean` (14, of which six are now closed — session 54: 127III
  uniqueness, 127VI, 128VIII, 128XI, 132III.1, 132III.3): 127III (main
  equivalence ~~and uniqueness~~), ~~127VI~~,
  ~~128VIII~~, ~~128XI~~, **128XIII**, **129X**, ~~**132III.1**~~, 132III.2/~~.3~~/.4,
  **132III.5**, 132IV, **132VI** `free_monoid_in_Wcpsu`.  The five in bold were
  previously classified (b) or (a); each carries `Duplicable`/`Duplicator`/`⊗ᵥ`
  in its *type*, hypothesis side included, so none can be axiom-clean before
  111XII.  Only **130IV**, **130V** and the unit `exists_freeMonoidUnitCpsu`
  are untainted.

## (b) Blocked, with the named blocker

### `Measurement.lean` (parsecs 960–1060) — 11 left, 2 closed in session 51 (7 in session 49, 7 in session 48, 9 in session 47)

| DISP | decl | blocked on |
|---|---|---|
| 96V | `canonical_filter` | **CLOSED (session 47)** — also `isFilter_ad`, `isFilter_stdFilter`, `ldiv_div_ad`, `ad_injective`, `ad_bipositive` |
| 98II.1 | `filter_basic_1` | **CLOSED** |
| 98II.2 | `filter_basic_2` | **CLOSED** — via 98II.1, so the ℂ-gadget of the "near miss" below was **not** needed |
| 98II.3 | `filter_basic_3` (bipositivity) | **CLOSED** |
| 98III | `filters_composition` | **CLOSED (session 48)** — and the "route that should work" recorded in session 47 (reduce to `c_q ∘ c_{p'}` and prove `⌊√p'√q⌉ = ⌈p'⌉`) is **not needed**.  The obstruction (`f(1) ≤ d(c(1))` does not give `f(1) ≤ d(1)`) is removed by *rescaling*: `c(1) ≤ l·1` with `l = ‖c(1)‖+1`, so `f(1) ≤ l·d(1)`, and `l⁻¹f` factors through `d`; rescaling the factor back by `l` gives `h'` with `d(h'(1)) = f(1) ≤ d(c(1))`, hence `h'(1) ≤ c(1)` by bipositivity of `d` (98II.3), hence a factorisation through `c`.  Uniqueness is injectivity of both (98II.2).  Total: ~45 lines, using `exists_ncpSmul` |
| 98VI | `corners_composition` | **CLOSED (session 48)** — using neither the printed hint nor its converse.  Take the composite's effect to be `s := β'(r)`, the transport of `τ`'s effect along the 98IV.1 isomorphism `β : ⌊p⌋𝒜⌊p⌋ ≅ ℬ`; then `s ≤ ⌊p⌋ ≤ p` and `π(1−s) = 1−r`, and the universal property falls out of `π`'s and `τ`'s.  Uniqueness is surjectivity of `τ∘π` (98IV.2).  ERRATA row 98VI and QUESTIONS A1 updated |
| 98VII, 98VII-formula | `filter_corner`, `filter_corner_formula` | **CLOSED** (the thesis's proof verbatim) |
| 98IX | `exists_sqBracket`, `square_f` | **CLOSED** |
| 100II.3 | `isPure_adSelf` | **CLOSED** (`a*(·)a = canonicalFilter a ∘ π_{⌊a⌉}`) |
| 100III | `pure_fundamental` | **CLOSED (session 49)** — and **without 98XI**: `π_s ∘ c_p` factors directly as (corner into `⌊a⌉𝒜⌊a⌉`) then (filter `a*(·)a`), `a = √p·s`.  Needed one repair to our own `IsPure` (see the session-49 note above) |
| 100VII.1/.2/.3 | `special_pure_maps_*` | **CLOSED (session 49)** — a unital filter and a corner of `1` are isomorphisms |
| 102VII | `canonical_quotient_rigid` | **CLOSED (session 51)** — the thesis's proof, ~210 lines; `approximate_pseudoinverse` (80IV), `IsApproxPseudoinverse.mul_eq_suppProj`, `partialSums_of_isLUB`, `ceil_fundamental_1` (60VII.1) and `nmiu_rigid` were all already in the tree.  The final limit is taken **ultraweakly** on the truncations `eₘ x eₘ`, not ultrastrongly on `eₙ h(eₙ a eₙ) eₙ`, so `cp-uscont` and the corner-topology transfer are not needed (ERRATA **102VIII**) |
| 102IX | `pure_is_rigid` | **CLOSED (session 51)** — 60 lines from `ad_rigid` at `d = √f(1)` (`stdFilter_rigid`), the 98IX square, and 100III's inverse for `[f]`; the thesis's `⋄`-computation is replaced by the pointwise identity `π_{⌈f⌉}(q.val) = q` |
| 103II.1/.2 | `purely_positive_examples_*` | **CLOSED (session 48)** — .1 is `isPure_adSelf` (100II.3) plus 101VII.1 at `a* = a`; .2 is `a(·)a = g∘g` for `g = √a(·)√a` |
| 104III.2a | `centrally_similar_basic_2a` | **parked: false as printed**, ERRATA row exists |
| 104III.3/.4/.5 | `centrally_similar_basic_*` | **not blocked** — 81V `douglas` and 81VIII.1 are proved (correction, session 51).  These are unsolved exercises about `div`, `pinv` and infima of positive elements, with no published solution (asols stops at parsec 340) |
| 104VII | `positive_quotients_centrally_similar` | 104III.4/.5 (80IV is now proved — correction to w46 §7) |
| 104IX | `faithful_positive_map_uniqueness` | 100VII + 104VII |
| 105III.1-2 | `chevron_f_basic_12` | **CLOSED (session 48)** — part 1 is the defining formula, part 2 is the 98IX square at `a ∈ ⌈f⌉𝒜⌈f⌉` plus `ceilOne_conj` |
| 105III.4 | `chevron_f_basic_4` | **CLOSED (session 49)** |
| 105IV.1/.3 | `chevron_f_purely_positive_*` | **CLOSED (session 49)** — and neither needed 105III.4: the map `u f(·) u` is pure directly (corner ∘ `f` ∘ `cornerIncl`), and its ⋄-self-adjointness transports from `f`'s via the new `corner_ceil_val` (ceilings in a corner are ambient ceilings) and `le_sub_iff_le_one_sub` |
| 105V uniqueness, 105VII | `positive_map_uniqueness`, `sqrt_axiom` | 104IX (105IV is now proved; the thesis's proof cites `faithful-positive-map-uniqueness` = 104IX explicitly).  **105V existence is CLOSED (session 48)**: it is `adSelf √p`, ⋄-positive by 103II.2 — it never needed 104IX |
| 106I uniqueness | `uniqueness_sequential_product` | 105V uniqueness.  **106I existence is CLOSED (session 48)**: (A)/(C)/(D) are `√p√p = p` computations, (B) is `adSelf √p` with 100II.3, and (E) is 101VII.1 transported from ceilings to the order by the new private helper `effect_le_isStarProjection_iff` (`b ≤ q ↔ ⌈b⌉ ≤ q` for an *effect* `b` and a projection `q`) |
| 106III.1 | `sequential_product_counterexample_1` | **CLOSED this session** |
| 106III.2/.3 | `sequential_product_counterexample_2/3` | purity-free? .2's axioms (A)(C)(D)(E) are computations; (E) needs contraposition.  Worth a look after 106III.1 |

### `Tensor.lean` — the 11 untainted ones

| DISP | decl | blocked on |
|---|---|---|
| 112X.1 | `tensor_basic_1` | **CLOSED (session 55)** — 90II.1 *and* .2 are proved, and this is 90II.2 applied to the product functionals plus 74VI/72III.1c for the order-separating half.  See the session-55 note at the top |
| 112X.2 | `tensor_basic_2` | **CLOSED (session 57)** — no `Ω₁` rescaling was needed; see the session-57 note at the top |
| 112X.3 | `tensor_basic_3` | **CLOSED (session 57)** |
| 112X.4 | `tensor_basic_4` | **CLOSED (session 57)** — 86IX closed in A/VN session 56 |
| 112X.5 | `tensor_basic_5` | **CLOSED (session 57)** — 87III closed in A/VN session 56 |
| 112XI | `tensor_universal_property` | **CLOSED (session 57)** — 77V applied to `S = γ_⊙(𝒜⊙ℬ)`, with 112X.2 for injectivity/the bound and 112X.5 for the topology |
| 114I | `tensor_universal_property_extra` | **CLOSED (session 58)** — see the note at the top |
| 114II | `tensor_uniqueness` | **CLOSED (session 58)** — as predicted: apply 112XI in both directions (`γ'` is normal and bounded *as a bilinear map* by 112X.3.1 and 112X.2); miu-ness of the extension is the usual separate-continuity-plus-density argument (`mult_uws_cont`), normality is then free via `starAlgEquiv_preservesDirSups'` |
| 116VII | `tensor_characterization` | 112X + 116IV |

### `QuantumLambda.lean` — the 7 untainted ones (recounted, session 51)

| DISP | decl | file:line | class | note |
|---|---|---|---|---|
| 121II | `intersection_tensor` | :326 | (c′) | proc.tex:4473 gives no argument, only "See Corollary IV.5.10 of Takesaki I".  **Not** in the vacuous band |
| 123I.3 | `linf_tensor` | :650 | (b) | **116VII** `tensor_characterization` (`Tensor.lean:2407`, `sorry`), which proc.tex:4645 cites explicitly; parts 1/2 of the exercise are proved just above it |
| 124I | `vn_generation_bound` | :678 | (a) | proc.tex:4696 needs `#(∗-algebra generated by S) ≤ #ℂ + #S` **and** that every element of `wstar S` is an ultraweak limit of a filter on it — the tree has **no** characterisation of `wstar` as a closure (only `isVNSubalgebra_wstar`), so a transfinite-closure construction has to be written |
| 124III | `second_adjunction` | :707 | (b) | Freyd's AFT: needs products and equalisers in `W*_miu` preserved into `W*_cpsu`.  47V `vn_equalisers` is **proved**; **47IV.3 `vn_products_ncpsu` (`A/VN/Basic.lean:2905`, `sorry`) is the real external blocker** — the earlier note ("124I + 125II + Zorn") missed it |
| 125II | `vn_gns_bound` | :729 | (a) | `ngns` is proved and `gnsHilb`/`exists_faithful_normal_rep` give the representation concretely; only the cardinal count `#H ≤ 2^#A` is left (the thesis's `#H = Σ_ω #H_ω` is correct only via countable support of `ℓ²`-families) |
| 125bII | `ha_second_adjunction` | :852 | (b) | AFT again: `ha_equalisers` (84bV, `A/VN/Division.lean:3084`), `hereditarilyAtomic_subalgebra` (84bIII, `Division.lean:3074`) and `vn_products_ncpsu`, all `sorry` |
| 125cIII | `Fha_concrete` | :894 | (a), long | nothing it needs is `sorry`: `HereditarilyAtomic` *is* the direct-sum decomposition by definition, and `mn_vna_1` is proved.  The work is the representatives/re-indexing bijection |

### `Duplicators.lean` — the 3 untainted ones (recounted, session 51)

| DISP | decl | file:line | class | note |
|---|---|---|---|---|
| 130IV | `measure_space_partition` | :1019 | (a) | **the recorded obstruction is gone**: `lp_infty_nonneg_iff` / `lp_infty_le_iff` (`A/VN/Basic.lean:765 ff.`) and 47IV.1/.2 supply the componentwise order on `lp ℬ ∞`.  proc.tex:6518 is a bare Exercise — build `𝒜 ≅ ⊕ₙ ℬₙ` from `IsLinftyOf` by restriction maps; ordinary measure theory |
| 130V | `discrete_ell_x` | :1034 | (b) | 130IV alone; `atomic_measure_space` (same file, :892, **proved**) already turns each atom into `ℂ` |
| 132VI unit | `exists_freeMonoidUnitCpsu` | :1206 | (b) | **47IV.3 `vn_products_ncpsu` (`A/VN/Basic.lean:2905`, `sorry`)** — it is exactly the `W*_cpsu` product of the family `(ω)_{ω ∈ W*_cpsu(𝒜,ℂ)}`.  The earlier note ("missing componentwise positivity of `CStarMatrix n (lp …)`") named the symptom, not the blocker |

Everything else in the file is in the vacuous band (see above).  Note that
128VIII's main input, **Tomiyama 128II**, is proved in this file (`tomiyama`).

## (c′) Cited to literature

* **121II** `intersection_tensor` — proc.tex:4473 cites Takesaki IV.5.10 and gives
  no argument.  (**Not** in the vacuous band — correction, session 51: it is about
  the concrete Hilbert-space tensor product.)

## (d) Suspicious

Nothing new found this session.  The three already-known false statements of
this chapter are all recorded and the Lean statements realigned:
104III.2a (parked), 104IV (repaired, ERRATA), 101VII.2 (repaired, ERRATA),
117II.1 (repaired and since **proved**).

## Corrections to earlier reports

1. **A/Proc is 115 (now 114), not ~120.**
2. **48VIII `ngns` is proved.**  111XII therefore hangs on 111VII alone, and
   111VII on 89IX alone.  Earlier notes named "89IX" as *a* blocker; it is
   *the* blocker, and it now gates 54 statements — nearly half the chapter.
3. **21VII `order_separating_norm` and 90II.1 are now proved**; only 90II.2
   blocks 112X.1/.2.  w42's table listed 90II wholesale.
4. **80IV `approximate_pseudoinverse` is proved** (session 36), so w46 §7's
   "104VII is blocked on 80IV" is stale; 104III.4/.5 are what is left there.
5. **74IV/74VI are proved** (sessions 23/25), so w42's entry for 112X.4 is
   down to 86IX alone.
6. The standard filter `c_p` of a *projection* does **not** need 96V: the
   corner inclusion is a filter by an elementary argument (now in the tree as
   `isFilter_cornerIncl`).  Earlier maps treated all of parsec 980 as one
   block behind 96V.
