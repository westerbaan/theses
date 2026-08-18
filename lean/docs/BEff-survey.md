# `Theses/B/Eff/` — full survey of the remaining `sorry`s (worker, session 82, 2026-08-17; **updated session 83, 2026-08-18**)

> **Session 83 update.**  The root, **180V**, is CLOSED — *both*
> `effectus_vn` and `effectus_vn_partial` are proved in `VNExamples.lean` and
> are `#print axioms`-clean.  B/Eff is now at **13** `sorry`s (`VNExamples`
> **9**, `StatesPredicates` 2, `EffectAlgebras` 2), 0 errors.  Three further
> corrections to what is below: `WStar.trivial` was stated one universe too
> high (`WStar.{u+1}`) and so could never be an object of `WStarNCPU.{u}` —
> fixed; the costing overlooked that **`ℂ` also has to be lifted** to
> `ULift.{u} ℂ` and given a `Theses.VonNeumannAlgebra` instance; and the real
> cost of the file is not the mathematics but that `WStarCat.lean`'s `id` and
> `comp` come from `Classical.choice`, so every categorical step needs a
> propositional apply-lemma where `emod_effectus` uses `rfl`.  The eight
> hypothetical examples are *still* gated on a transport of the new concrete
> structure to the arbitrary `s` of their statements.  See PROVING-LOG,
> session 83.
>
> **Session 83, second worker.**  `exc_dm_effectus_kleisli` (192III.3) is also
> CLOSED, from the author's solution at `bsols.tex:1991–2170`, which is
> complete and usable as written.  With both closures B/Eff is at **12**
> `sorry`s (`VNExamples` 9, `StatesPredicates` **1**, `EffectAlgebras` 2), 0
> errors.  See the `StatesPredicates.lean` section below.

> **Session 84.**  **`effects_sea` (225V) is CLOSED**, axiom-clean, in
> `VNExamples.lean`; B/Eff is at **11** `sorry`s (`VNExamples` **8**,
> `StatesPredicates` 1, `EffectAlgebras` 2), 0 errors.  The costing below was
> ~3× too high: **~230 added lines**, because the Gudder–Greechie
> characterisation `√a b √a = √b a √b ⟺ ab = ba` is short in Mathlib
> (`quasispectrum.mul_comm` + `nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts`)
> and the three commutation axioms are then one line each.
>
> **The eight hypothetical examples: how many are reachable?  Still zero, and
> the reason is sharper than "a transport".**  Each takes an *arbitrary*
> `s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ` and none of them mentions
> `effectus_vn_partial`, so **closing 180V unblocked none of them** and
> strengthening `effectus_vn_partial` (QUESTIONS **B13**) would unblock none
> of them either.  What every one of the eight needs is a lemma that does not
> exist: *the effect object of an `EffectusPartialStructure` on `vN_cpsuᵒᵖ` is
> isomorphic to `ℂᵤ`*.  The other three fields of `s` are already pinned —
> `hasFiniteCoproducts` is a `Prop` (`Subsingleton.elim`), `homPCM` is
> `effectusPartialStructure_homPCM_unique`, `finPAC` is a `Prop` over that
> data — and inside `EffectusPartialForm` the field `orth` is pinned by
> `orth_unique` and `one X` is pinned as the `≼`-greatest predicate
> (`le_truth` + `pred_le_antisymm`).  **`I` is the only free datum.**
>
> A route exists and is not long (~150–250 lines): `one_m_is_id`
> (**181XIII**, `Effectus.lean:672`) says `1_I = 𝟙 I`, so `I` is *terminal in
> `Tot`*; `Tot` is defined from `one`, hence from `I`, so the circle has to be
> cut by an `I`-free characterisation of totality, and in `vN` there is one:
> `f` is total iff `f` is **≼-maximal**.  (⇒ is the finPAC axioms; ⇐ is
> concrete — if `f(1) ≠ 1` then `g = ω(·)(1 − f(1))` for a normal state `ω`
> is a nonzero `g ⊥ f`, and `ω` exists because `np_faithful` gives a
> separating family and `f(1) ≠ 1` forces the algebra nontrivial.)  Then
> `1_s : ℂᵤ ⟶ I_s` and our `suOne : I_s ⟶ ℂᵤ` are mutually inverse by
> `one_m_is_id` on both sides.  **Nobody should take one of the eight without
> writing this first**; after it, each still costs its own 200–600 lines.
>
> **Two further corrections to the record** (both were wrong here and in
> `why-open.csv`): `vn_is_dagger_category` (215VI) is **not** blocked on
> `vn_is_andthen_eff`/A-Proc 105V — our rendering quantifies over an arbitrary
> `hA : AndThenEffectus`, which is a `Prop` class, so it never needs 211IV;
> and the "†-effectus development of parsecs 215–220" that `exc_purec_*` were
> said to wait on is **not parked** — `Dagger.lean` has 0 `sorry`s and
> `dagger_thm_sufficiency` (220II) is proved.  Only `vn_is_andthen_eff`
> itself is blocked outside `B/Eff`.

> **Session 85.**  **The uniqueness-of-`I` lemma exists**, axiom-clean, in
> `VNExamples.lean` (new section after `effectus_vn_partial`, ~330 lines):
>
> * `vn_effObj_iso (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ)` —
>   `∃ θ : s.effectus.I ≅ ℂᵤ, ∀ X, s.effectus.one X ≫ θ.hom = suOne X`;
> * `vn_isTotal_iff` — the corollary every dependant will actually use:
>   `f ≫ s.effectus.one Y = s.effectus.one X ↔ f.unop 1 = 1`, i.e. **the
>   total maps of *any* partial-form effectus structure on `vN_cpsuᵒᵖ` are
>   exactly the ncpu-maps**;
> * by-products: `vnPartialStructure` (the bundled concrete structure, now
>   also the proof of `effectus_vn_partial`), and `exists_ncpsu_state` — *a
>   nontrivial von Neumann algebra carries a normal state, presented as a
>   unital ncpsu-map `A → ℂᵤ`* — which fills a real API gap (the tree had no
>   `NPFunctional → NCPSUMap`; `A/Proc/QuantumLambda.lean` had to build the
>   `NPFunctional → NCPMap` half for itself in session 84).
>
> **The recorded route was wrong, and the replacement is shorter.**  Session
> 84 proposed to cut the circle "`I` is terminal in `Tot`, but `Tot` is
> defined from `I`" with the `I`-free characterisation *total ⟺ `≼`-maximal*.
> **That characterisation is false in `vN_cpsuᵒᵖ`**: the unique morphism
> `X ⟶ 0` into the initial object (the trivial algebra, which *is* an object
> here) is `≼`-maximal, being the only element of its hom-set, but it is
> total only if `X` is a zero object.  `Tot` is not needed at all.  What
> works instead, and is the whole of the proof:
>
> 1. `p ⋁ pᗮ = 1` is the *pointwise* sum in the concrete PCM (which is
>    `s`'s, by `effectusPartialStructure_homPCM_unique`), so every predicate
>    is dominated **pointwise** by the truth predicate.  This replaces all
>    reasoning with `≼`.
> 2. The algebra `A` under `s.effectus.I` is nontrivial, else `𝟙 ℂᵤ = 0` by
>    `eq_zero_of_one_zero`.
> 3. So `A` has a normal state `ψ` (`exists_ncpsu_state`); `ψ ≤ φ` pointwise
>    for `φ := 1_{ℂᵤ}` and `φ(1) ≤ 1 = ψ(1)` force `φ = ψ` and `φ(1) = 1`.
> 4. **`one_m_is_id` (181XIII) at the effect object itself**: `1_I = 𝟙 I`
>    says `𝟙` is the greatest element of `vN_cpsu(A, A)`, i.e.
>    `φ(a)·1 ≤ a` for `a ≥ 0`.  Running that at `a` *and* at `‖a‖·1 − a`
>    gives `φ(a)·1 ≤ a ≤ φ(a)·1`; `linear_eq_zero_of_nonneg` extends it to
>    all `a`.  So `A ≅ ℂ` — and this is the one genuinely operator-algebraic
>    step, three lines once the state is in hand.
> 5. `1_X(1) = 1` for every `X` (the compatibility clause) because
>    `a ↦ φ(a)·1_X` is a *unital* predicate dominated by `1_X`.
>
> **Costing.**  The ~150–250 lines costed below was ~1.3–2× low: **~330
> lines**, of which ~90 are `exists_ncpsu_state` and its `ℂᵤ` plumbing.  The
> dominant cost was again not the mathematics but *types*: `WStar.of` is
> semireducible, so `(Opposite.unop suI).base.carrier` and `ULift ℂ` are
> defeq but never syntactically equal, and every `rw`/`+`/`1` that crosses
> the two has to be given an explicit ascription (`exact` and `show` are
> fine).  Budget for that in any of the eight.
>
> **What the eight now cost.**  Each still needs its own mathematics; none
> is closed.  Re-costed with the transport in hand:
> `vn_has_dilations` (221III) and `vn_dilation_order_correspondence` (223VI)
> ~200 lines each and still the cheapest; `effectus_vn_real_separating`
> (190III) ~250–350 — its `SeparatingPredicates` half is now nearly free
> (predicates on `X` are the effects of `X.unop`, and separation is
> linearity), its `SeparatingStates` half needs "np-functionals separate
> *self-adjoint* elements", which wants the ceiling calculus of
> `A/VN/Projections.lean`, and `IsRealEffectus` needs an effect-monoid
> isomorphism `Scal C ≅ [0,1]`; `diamond_effectus_vn` (206III) ~250;
> `vn_is_dagger_category` (215VI) via `dagger_thm_sufficiency`; the two
> `exc_purec_*` ~600/~400.  `vn_is_andthen_eff` (211IV) is unchanged:
> blocked on A/Proc's 105V.

> **Session 86.**  **`effectus_vn_real_separating` (190III) is CLOSED**,
> axiom-clean (checked *in situ*), in `VNExamples.lean`; B/Eff is at **8**
> `sorry`s (`VNExamples` **7**, `EffectAlgebras` 1, `StatesPredicates` 0 —
> all three counted with the compiler), 0 errors.  ~400 added lines
> against the ~250–350 costed, so ~1.2–1.6× low.  Three corrections to the
> costing just above, in **both** directions:
>
> * `SeparatingStates` did **not** need the ceiling calculus.  "np-functionals
>   separate self-adjoint elements" is four lines of conjugation:
>   `ν = ω(y⁺ · y⁺)` is again an np-functional (`conjNP`, `A/VN/Basic.lean`)
>   and `y⁺ y y⁺ = (y⁺)³` because `y⁺y⁻ = 0`, so `np_faithful` at `(y⁺)³`
>   kills `y⁺`, and the same at `y⁻`.  No spectral projections, no ceilings.
>   (New reusable lemma: `eq_zero_of_ncpsu_states`.)
> * `IsRealEffectus` was the *largest* of the three parts, not a footnote: the
>   effect-monoid isomorphism `Scal C ≅ [0,1]` has to be built by hand out of
>   `θ`, with `⋁ ↦ +`, `∘ ↦ ×`, and bijectivity both ways.
> * `SeparatingPredicates` was indeed nearly free, but needed the scaling
>   `b ↦ (‖b‖+1)⁻¹·b` to get from effects to all positive elements (helpers
>   `smul_le_smul_cstar`, `smul_one_le_one`).
>
> **The remaining six reachable items are re-costed sharply upwards, and the
> ~200-line figures above are wrong.**  190III turns out to be the *only* one
> of the eight that never mentions sharpness, purity, quotients or
> comprehensions — which is why it went through on `vn_effObj_iso` alone.
> Every other one does: `IsDilation` asks for `SharpMap ϱ`, `IsTotal ϱ` and
> `IsPure h`; `DiamondEffectus` asks for `HasQuotients`, `HasComprehension`,
> `HasImages` and `orth_sharp`; `DaggerPrimeEffectus` asks for `quot_sharp`;
> `PureCat` is built from `IsPure`.  The concrete identifications that supply
> these — **sharp predicates = projections** (eff.tex:4195), **quotients =
> corners** (3684), **comprehensions = filters** (3934), **pure maps** (4040),
> **sharp maps = nmiu-maps** (4777) — are *bare Examples in eff.tex with no
> proof* and are formalized **nowhere in the tree** (grep: no Lean statement
> cites any of those five lines).  `vn_has_dilations`'s "as shown in
> `existence-paschke`" presupposes all of them: `existence_paschke` quantifies
> over *nmiu* `ϱ'`, the abstract universal property over *sharp total* `ϱ'`,
> so the two are the same statement only after "sharp + total ⟹ nmiu", which
> needs the **multiplicative domain** of a ucp-map — and neither that nor
> Kadison–Schwarz for maps is in the tree (grep: no `multDomain`, no
> `kadison_schwarz`).  Realistic shared cost of that bridge layer:
> **~800–1500 lines**; after it, each of the six is comparatively cheap and
> `vn_has_dilations`/`vn_dilation_order_correspondence` are again the first
> two to take.  **This layer, not any one of the six, is the next target.**

> **Session 87.**  **The bridge layer is half built and `diamond_effectus_vn`
> (206III) is CLOSED**, axiom-clean (checked *in situ*).  `VNExamples.lean` is
> at **6** `sorry`s, 0 errors, 3692 lines (**+530**) — against the ~800–1500
> costed for the whole layer, so the half that landed came in at about a third
> of the estimate.  B/Eff is at **7** (`VNExamples` 6, `EffectAlgebras` 1,
> `StatesPredicates` 0).
>
> What landed, all in the `IUnique` section (so it holds for an *arbitrary*
> `EffectusPartialForm` on `vN_cpsuᵒᵖ`, and the `Wrapper` idiom transports it):
>
> * **the predicate–effect dictionary** — `suPredVal p = p(1)`, with
>   `su_pred_ext` (a predicate is determined by the effect it names),
>   `su_pred_exists` (every effect is named), `suPredVal_comp`,
>   `suPredVal_truth`, `suPredVal_orth` (`pᗮ ↦ 1 − a`) and **`su_pred_le_iff`**
>   (the algebraic order `≼` of the effect algebra *is* the C\*-order).  This
>   is what every one of the five identifications is stated against, and it is
>   ~120 lines;
> * **`su_hasQuotients`** — quotients are **filters** (`dils_stand_filter`);
> * **`su_hasComprehension`** — comprehensions are **corners**
>   (`standard_corner_dils`);
> * **`su_hasImages`** — the image of `f` is its **carrier** `⌈f⌉`
>   (`Theses.A.VN.carrier`, vn.tex 63I);
> * **`su_isSharp_iff`** — *the sharp predicates of `vNᵒᵖ` are exactly the
>   projections* (eff.tex:4195);
> * **`su_orth_sharp`**, **`su_diamondEffectus`**, and hence **206III**;
> * **`su_sharpMap_iff`** — a map is sharp iff its ncpsu-map sends projections
>   to projections.
>
> **Three corrections to the session-86 block below, one of them structural.**
>
> 1. **Quotients and comprehensions were swapped** in that block, in
>    `why-open.csv`, and in the brief derived from them.  eff.tex:3686 says
>    quotients in `op(vN)` are *contractive filters*; eff.tex:3935 says
>    comprehensions are *corners*.  (dils.tex:6072 and :6140 agree, each
>    calling the effectus-side notion "the direction-reversed counterpart".)
>    The Lean proofs confirm it: `IsQuotient p ξ` unfolds to `IsFilterFor
>    ξ.unop (1 − a)` and `IsComprehension p π` to `IsCornerFor π.unop a`.
> 2. **The multiplicative domain is *not* the root, and nothing about it is
>    missing.**  "Sharp maps = nmiu-maps" is **99XII** `sharp_multiplicative`
>    (proc.tex:905) — *for an ncp-map: multiplicative ⟺ sends projections to
>    projections ⟺ `⌈f(a)⌉ = f(⌈a⌉)`* — and it is **PROVED** at
>    `Theses/A/Proc/Measurement.lean:3568`, together with **99II** `gardner`
>    (:3352) and **100III** `pure_fundamental` (:4058, the pure-maps
>    identification of eff.tex:4040).  eff.tex:4779 cites `sharp-multiplicative`
>    explicitly, so this is not even a bare Examples point.  The claim that the
>    five identifications are "formalized nowhere in the tree" is right only for
>    the three that live in `B/Eff` and is **wrong for the two that gate
>    `vn_has_dilations`**.
> 3. Hence the remaining gate for 221III/223VI is an **import**, not
>    mathematics: `VNExamples.lean` does not import `Theses.A.Proc.Measurement`.
>    Adding it is a real change (that file carries 11 `sorry`s of its own,
>    including 105V) but a mechanical one; with it, `su_sharpMap_iff` +
>    `gardner` gives *sharp + total ⟹ nmiu* in a few lines.
>
> Two traps cost time and are worth recording.  `Quiver.Hom.op (wEffect …)`
> **diverges** (`whnf` timeout, not slowness) unless its type is ascribed:
> without it Lean has to solve `?P.base.carrier =?= ULift ℂ`, and `WStar.of` is
> semireducible.  The `obtain ⟨q, hq⟩ : ∃ q : X ⟶ suI, … := ⟨…, fun _ => rfl⟩`
> idiom fixes it.  And every equation whose *codomain* is a corner algebra has
> to be written as an `Eq.trans` chain: `rw` will not cross
> `cornerSet A p` versus `(Opposite.unop (Opposite.op (WStarCPSU.of (WStar.of
> (cornerSet A p))))).base.carrier`.
>
> Not done, and the natural next increments: **pure maps = filter-after-corner**
> (needs "every quotient is a filter", i.e. uniqueness-up-to-iso of the
> universal objects, plus `pure_fundamental`), then `vn_has_dilations` (221III)
> and `vn_dilation_order_correspondence` (223VI).  Nothing for ERRATA (no defect
> in a *statement* — the swap was a defect in **our** record); no new QUESTIONS.

> **Session 88.**  **`vn_has_dilations` (221III) is CLOSED**, axiom-clean
> (checked *in situ*), and the bridge layer is finished *as far as dilations
> need it*.  `VNExamples.lean` is at **5** `sorry`s, 0 errors, 4022 lines
> (**+330**).  B/Eff is at **6** (`VNExamples` 5, `EffectAlgebras` 1,
> `StatesPredicates` 0).
>
> **The import went in and cost almost nothing.**  `VNExamples.lean` now
> imports `Theses.A.Proc.Measurement` as well as `Theses.B.Eff.Comparisons`
> and `Theses.B.Dils.Pure`.  `Measurement.lean` imports only
> `Theses.A.VN.NormalFunctionals`, which `B/Dils` already pulled in, so the
> import adds one file and **7 seconds** (24s → 31s) and no name clash — in
> particular `Theses.A.Proc.IsPure`/`IsFilter`/`IsCornerMap` do not collide
> with `Theses.B.Eff.IsPure` or `Theses.B.Dils.IsFilter`, because nothing
> `open`s `Theses.A.Proc`.  **The B/Eff chain arrangement is preserved**:
> checked by grep — no `.lean` file imports `VNExamples` except `Theses.lean`,
> and the other eight B/Eff files still import `Theses.Common` alone.
>
> What landed, all in the `IUnique` section:
>
> * **`su_exists_nmiu_of_sharp_total`** — *sharp + total ⟹ nmiu*, with
>   `su_sharp_total_of_nmiu` the converse and `su_exists_ncpsu_of_nmiu` the
>   plumbing.  **`gardner` (99II) is not what is needed**: it demands
>   unitality, and the fact used is **99XII** `sharp_multiplicative`, which
>   demands none.  Involution-preservation is `cstar_p_implies_i` for any
>   positive map, and the `StarAlgHom` is `AlgHom.ofLinearMap` plus that.
>   ~40 lines.
> * **`su_isQuotient_of_isFilterFor`** — *every* filter is a quotient (the
>   converse reading of `su_hasQuotients`), and
>   **`su_isComprehension_of_isCornerFor`** — every **unital** corner is a
>   comprehension.  **Unitality is a genuine hypothesis, not a convenience**:
>   by QUESTIONS **D7**, `λ·h_a` is a corner for the same effect under 169II
>   as printed, and for `λ < 1` the mediating map of a subunital `f` is
>   `λ⁻¹·f'`, which is not subunital — so *not* every corner is a
>   comprehension.  ~70 lines.
> * **`su_isDilation_of_paschke`** and **`su_hasDilations`**, hence 221III.
>
> **The construction is not `existence_paschke` applied to `φ`.**  `IsPure h`
> needs the *unital* corner just described, so the dilation is assembled the
> way **170II**.2 assembles one: filter off `φ(1)` (`dils_stand_filter`),
> take the unique unital `φ'` with `φ = c'∘φ'` (`dils_filter_basics_2a`),
> dilate `φ'`, and put the filter back (`dils_filter_basics_2b`).  The right
> leg is then a corner by **169V** `h_is_corner_for_unital_map` *and* unital,
> `h(1) = h(ϱ(1)) = φ'(1) = 1`.  This also sidesteps
> `paschke_unique_up_to_iso`, which `dils_examples_pure_2` needs only because
> it is handed the dilation.
>
> Two mismatches between **140II** `def-paschke` and **221II**
> `dfn-eff-dilations` turned out harmless and are worth recording: the
> mediating ncp-map of 140II is automatically **unital**, hence a morphism of
> `vN_cpsuᵒᵖ` (`σ(1) = σ(ϱ'(1)) = ϱ(1) = 1`, both legs being nmiu); and
> 140II's uniqueness is among *all* ncp-maps, which is stronger than the
> effectus asks for.
>
> **Costing.**  ~330 added lines against the ~800–1500 costed in session 86
> for the whole layer, of which ~530 landed in session 87 — so the layer came
> in at ~860 lines total, at the low end of that estimate, and the session-86
> claim that the layer was the *root* was right even though its diagnosis
> (the multiplicative domain) was wrong.
>
> **223VI `vn_dilation_order_correspondence` is re-costed sharply upwards and
> is *not* now cheap.**  `DilationOrderCorrespondence` is stated with `asrt`
> and `sef`, so it needs `asrt_p` identified concretely in `vN` as
> `b ↦ √a b √a` — and by **206II**.4 that means proving `ad_{√a}` **pure**
> and equal to `g ≫ g` for a **⋄-self-adjoint** `g`, i.e. computing
> `diaPull`/`diaPush` concretely in `vN`: a second bridge layer of roughly the
> size of the first.  After it, `sef_p ≫ ϱ = ϱ ⟺ t ∈ ϱ(𝒜)'` and `Θ` is
> `paschke_correspondence_mem`/`_embedding`/`_surjective`.  **~400–600 lines,
> not the ~200 recorded until now.**  Nothing for ERRATA (no defect in a
> statement); no new QUESTIONS — the corner-unitality point is **D7**, already
> filed.

> **Session 90.**  **Both 224 exercises are CLOSED**, axiom-clean, in
> `VNExamples.lean`: `exc_purec_equal` (224VII, `Pure (vNᵒᵖ)` has no
> coequalizers) and `exc_purec_no_biproduct` (224VI, no binary coproducts).
> With session 89's 223VI and 215VI that puts B/Eff at **2** `sorry`s
> (`VNExamples` **1**, `EffectAlgebras` 1), 0 errors — and the one left in
> `VNExamples.lean` is 211IV, blocked outside B/Eff.  ~725 added lines
> against the ~1000 costed for the two.
>
> **Both costings were built on the author's solutions, and both solutions
> are longer than they need to be.**  The single lemma that carried the two
> exercises is `su_pure_range`: *the range of a pure map contains `√a x √a`
> for every effect `x`, `a = f(1)`*.  It needs only (i) that a comprehension
> of `vNᵒᵖ` has **surjective** `unop` (`su_compr_surjective`, from
> `compr_basics_2` against the standard corner — `su_exists_corner` was
> extended to report surjectivity) and (ii) the **effectus** universal
> property of the quotient half, applied to `ad_{√(√a x √a)}`.  No filter is
> ever identified concretely and `dils_filters_injective` is never used.
>
> * **224VI needs no GNS, no `paschke-pure`, no minimal projections and no
>   `M₂`.**  Both coprojections `π₁, π₂` of a hypothetical coproduct of `ℂ`
>   and `ℂ` are *states* (they are left inverses of the mediating map `ĝ₀` of
>   `(id, id)`, so `π_i(a₀) = 1` for `a₀ = ĝ₀(1)`); a state fixing `a₀` is
>   invariant under `x ↦ √a₀ x √a₀` (`su_state_sqrtConj`, from Cauchy–Schwarz
>   **31IV** `omega_norm_basic_1` plus `a ≤ √a`); and `√a₀ a₁ √a₀` lies in
>   the range of `ĝ₀`, where `π₁` and `π₂` agree.  So
>   `1 = π₁(a₁) = π₂(a₁) = 0`.  ~200 lines against the ~600 costed.
> * **224VII needs no pseudoinverse and no `M₃`.**  The author's
>   `⌈ξ(1)⌉p_𝒮⌈ξ(1)⌉`-central-in-a-factor step is replaced by
>   `proj_mul_selfAdjoint`: testing `p·(s x s) = (s x s)·p` against the
>   *rank-one* effects `|ξ⟩⟨ξ|` gives `p(sξ) ∈ {0, sξ}` for every `ξ`, and a
>   vector space is not the union of two proper subspaces, so `ps = 0` or
>   `ps = s`.  The final contradiction runs with `ad_p` and `ad_{1−p}`
>   (pure, fixed by `ad_σ`) instead of `ad_{e†_𝒮} : M₃ → M₄`, and the whole
>   thing is stated for an arbitrary projection `p ∉ {0,1}` of a `B(ℋ)`,
>   instantiated at `ℋ = ℂ²`.  ~380 lines against the ~400 costed.
>
> New in `VNExamples.lean`: `rk1`, `rk1_isStarProjection`,
> `proj_mul_selfAdjoint`; `su_le_sqrt`, `su_sq_le_self`,
> `su_posFun_mul_eq_zero`, `su_state_sqrtConj`; `su_exists_ad'` (`ad_w` for
> `w` **not** positive — needed because `ad_σ` is pure only as an
> *isomorphism*), `suop_id_apply`, `su_proj_eq_zero`, `su_compr_surjective`,
> `su_pure_range`, `su_no_coequalizer_of_proj`, `su_exc_purec_equal`,
> `suFun`, `su_exc_purec_no_biproduct`.  Nothing for ERRATA or QUESTIONS.

> **Session 84, second worker.**  **`finite_effectMonoid_boolean` (178III.2) is
> CLOSED**, axiom-clean, in `EffectAlgebras.lean` (new section
> `FiniteBoolean`).  With `effects_sea` that puts B/Eff at **10** `sorry`s
> (`VNExamples` 8, `StatesPredicates` 1, `EffectAlgebras` **1**), 0 errors.
> The costing below was **~2× too high**: **~185 added lines** net, not
> 250–400.  Two reasons.  (i) The survey's route had the dependencies backwards
> — it said the structure equality "needs `Perp a b ↔ a ⊙ b = 0` (itself a
> consequence of distributivity)".  It is the other way round: `a ⊥ b ⟺
> a ⊙ b = 0` follows in three lines from `a = a ⊙ 1 = (a⊙b) ⋁ (a⊙bᵖ)`, and
> *distributivity* is what needs it (via de Morgan and `b ⊔ c = b ⋁ (c ⊙ bᵖ)`).
> (ii) The MSc props 13–16 sup/inf calculus (`msc_*`, `:1224`–`:1400`) was
> **not used at all** — it is stated for *ortholattices*, a structure a finite
> effect monoid is not known to carry until after this theorem.  The three real
> ingredients were `emon_finite_idem`, the meet (extracted from
> `finite_effectMonoid_commutative` as the new `emon_finite_isInf`), and
> `emon_finite_perp_iff`; everything else is de Morgan duality.
> Also: `Mathlib`'s `DistribLattice.ofInfSupLe` means only **one** distributive
> inequality has to be proved, and every field of the resulting Boolean algebra
> except `Perp` and `⋁` matches `em` by `rfl`.
> `effectModule_unitInterval_representation` was **not** attacked, deliberately;
> its rendering gap is now **QUESTIONS B14**, split out of A3.

> **Session 85.**  **`cancellative_iso_convex` (192V.4) is CLOSED**,
> axiom-clean (checked *in situ*), and **`StatesPredicates.lean` is
> FINISHED** — 0 `sorry`s, 0 errors, both counted with `lean` on the file
> itself.  `EffectAlgebras.lean` is unchanged at 1, and that one is the
> ruling-blocked B14.  That puts B/Eff at **9** if `VNExamples.lean` is still
> at the 8 of session 84 — it was not re-counted here, because another worker
> was mid-flight in it and rebuilding the chain would have raced with them.
> **Nothing in `B/Eff` outside `VNExamples.lean` is open any more except the
> one ruling-blocked statement**, 179III.2.
>
> Costing was again **~2× too high**: **~289 net added lines** (7724 → 8013),
> ~27 of them the section header, against ~500–600.  The reason is the same as
> for `finite_effectMonoid_boolean`: the survey costed the *textbook* route —
> the cone `ℝ_{>0} × X ∪ {0}`, its Grothendieck group, and an `ℝ`-module
> structure built on that quotient by hand — instead of a route that lets
> Mathlib supply the algebra.  What works is to stay inside the **free vector
> space `X →₀ ℝ`** and quotient by an explicit `Submodule`, so that
> `AddCommGroup` and `Module ℝ` are `Submodule.Quotient`'s and nothing has to
> be checked; the relators are `t·(P − Q)` for formal convex combinations with
> `h P = h Q` and `t > 0`, written in that *existential* shape so that both
> closure under `+`/`•` and injectivity are easy.  Cancellativity is used
> **exactly once**, for injectivity.  (Mathlib does have
> `Algebra.GrothendieckAddGroup` with `mk_left_injective`, in
> `GroupTheory/MonoidLocalization/GrothendieckGroup.lean` — but it carries no
> scalar action, so it would not have saved the module structure.)
>
> **The survey's claim that "nothing in the tree helps beyond
> `MConvex.ofConvex` and the `rsum` API" was wrong.**  `mu_bin`, `map_bin`,
> `mu_map_eta` and `unitInterval_isSumOf_iff` are the whole `𝒟_[0,1]` calculus
> this needs and were all already present — `mu_bin`/`map_bin` merely had to be
> **moved up the file** (with `map_spec_of_list`, `mu_spec_of_subset`) from the
> parsec-196 block to next to `bin_eq_zero`, no statement changed.  This is the
> third time a `B/Eff` item has needed helpers moved up; check the *whole* file
> for existing API before costing, not just the neighbourhood.
>
> `eff.tex:2589` carries **no `\label`** and is not an Exercise, so `bsols.tex`
> has no solution for it — verified, not assumed.  Like `effects_sea` and
> `finite_effectMonoid_boolean`, this is mathematics we supplied, and an
> independent check of \[statesofconvexsets, thm. 8\]; see PROVING-LOG
> session 85.  QUESTIONS **A3**'s 192V.4 bullet is struck through.

**Headline count (session 82): B/Eff had 15 code `sorry`s.**  Per file, each source run
through `lean` individually with `LEAN_PATH` set (never `lake env lean`), and
each checked for **errors** as well as `sorry`s.  (`VNExamples.lean` was
re-verified against freshly built `B/Dils` oleans; while the `B/Dils` worker
is mid-rebuild it reports a transient `object file … does not exist` at its
import line, which is not a defect in this directory — retry, do not debug.)

| file | lines | `sorry` | errors |
|---|---|---|---|
| `VNExamples.lean` | 408 (now 2786) | **11** (now **8**) | 0 |
| `StatesPredicates.lean` | 7216 (now 8013) | **2** (now **0**) | 0 |
| `EffectAlgebras.lean` | 3088 (now 3348) | **2** (now **1**) | 0 |
| `Comparisons.lean` | 1903 | 0 | 0 |
| `Dagger.lean` | 2572 | 0 | 0 |
| `DiamondAmp.lean` | 1855 | 0 | 0 |
| `Quotients.lean` | 1427 | 0 | 0 |
| `Effectus.lean` | 2783 | 0 | 0 |
| `WStarCat.lean` | 292 | 0 | 0 |
| **total** | | **9** | **0** |

The import chain is linear:
`EffectAlgebras + WStarCat → Effectus → StatesPredicates → Quotients →
DiamondAmp → Dagger → Comparisons → VNExamples`.  Only `VNExamples.lean`
imports thesis A (via `Theses.B.Dils.Pure`); the other eight import
`Theses.Common` alone.  **Preserve that**: it is an author ruling of
2026-08-17, and it is why `B/Eff` builds in seconds and cannot be broken by
work upstream.

---

## Headline findings of this session

1. **Neither recorded blocker is real.**
   * *"Mathlib lacks a `CStarAlgebra` instance for the trivial algebra."*
     **Refuted, and fixed.**  Mathlib's `CStarAlgebra` extends `NormedRing`,
     **not** `NormOneClass`, so `‖1‖ = 0` is no obstacle; only four instances
     (`StarRing`, `CStarRing`, `StarModule ℂ`, and then `CStarAlgebra` itself
     as `{}`) were missing for `PUnit`, plus `StarOrderedRing` and
     `Theses.VonNeumannAlgebra`.  All six are now in `VNExamples.lean`, with
     `WStar.trivial` as the object.  ~25 lines.  (Mathlib in fact *already*
     has a trivial C\*-algebra by accident: `CStarAlgebra (Π _ : Empty, ℂ)`
     synthesises from the finite-`Pi` instance.)
   * *"An `EffectusPartialStructure` uniqueness lemma is missing."*  **Half
     real, and the hard half is now proved.**  The PCM-enrichment of a finPAC
     is **not extra data**: it is uniquely determined by the category and its
     finite coproducts (`finPAC_pcm_unique`, `Comparisons.lean`, axiom-clean),
     hence so is the enrichment carried by any `EffectusPartialStructure`
     (`effectusPartialStructure_homPCM_unique`).  What is *not* determined is
     the effect object `I` of `EffectusPartialForm` together with its truth
     map: those are unique only up to isomorphism, and the nine hypothetical
     statements will additionally need an invariance-under-`I`-iso lemma
     (small, but not written).

   The argument, for the record, uses only the finPAC axioms:
   `𝟙` on the initial object is `0` (both are maps `0 ⟶ 0`), so `f = f ≫ 𝟙 =
   f ≫ 0 = 0` for every `f : X ⟶ 0` and `C(X, 0)` is a **singleton**; hence
   `0 = 0_{X,0} ≫ !` is the same morphism for any two enrichments.  With `0`
   fixed the partial projections `▷₁, ▷₂` are fixed, and `f ⊥ g` iff `f, g`
   are the two components of one `b : X ⟶ Y + Y` (`⇐` is *compatible sum*,
   `⇒` takes `b = κ₁f ⋁ κ₂g`, which exists by *untying*).  Finally
   `f ⋁ g = ∇ ∘ b` for any such `b`, because `▷₁ ⋁ ▷₂ = ∇` and `⋁` commutes
   with precomposition.

2. **`effectus_vn` / `effectus_vn_partial` (180V) is the root**, as previously
   recorded, and it is now genuinely open work rather than gated: the trivial
   algebra exists, and the uniqueness lemma removes the second gate for its
   eight dependants.  See the entry below for what remains.

3. **`vn_is_andthen_eff` (211IV) needs `A/Proc`, which is not on the import
   path** — a correction to `VNExamples.lean`'s own header, which says "`A/Proc`
   … nothing here has been shown to need it".  eff.tex:4859 proves the two
   &-effectus axioms by citing **105V** `positive-map-uniqueness` and **100III**
   `pure-fundamental`, and both live in `Theses/A/Proc/Measurement.lean`.
   Worse: **105V is itself `sorry` there** (`Measurement.lean:6610`).  So 211IV
   is blocked on an A/Proc item *and* on an import that must first be added.

4. **Three of the four non-`VNExamples` items are literature parks, not
   targets** (QUESTIONS **A3**); only `exc_dm_effectus_kleisli` is a live
   target, and it has a complete author solution.

5. **QUESTIONS A3 is stale in two places**: it lists
   `finite_effectMonoid_commutative` and `exists_noncommutative_effectMonoid`
   as parked, but both are **proved** (`EffectAlgebras.lean:2780`, `:2300`;
   line numbers as of session 84).
   Only `finite_effectMonoid_boolean` of that trio was still open, and it is
   **proved as of session 84** — the whole of A3's 178III trio is closed.

---

## Classification at a glance

| classification | statements |
|---|---|
| **proved (session 83)** | `exc_dm_effectus_kleisli`; `effectus_vn` + `effectus_vn_partial` |
| **proved (session 84)** | `effects_sea` (225V); `finite_effectMonoid_boolean` (178III.2) |
| **proved (session 85)** | `cancellative_iso_convex` (192V.4) — `StatesPredicates.lean` is finished |
| **reachable, live target** | *(none left outside the gated eight)* |
| **transport now available** | the eight hypothetical vN examples below: the uniqueness-of-`I` lemma they were gated on is **proved** (session 85, `vn_effObj_iso`); each is now open on its own mathematics alone |
| **blocked outside B/Eff** | `vn_is_andthen_eff` (A/Proc 105V + missing import) — and **only** that one |
| **awaiting a ruling / literature park** | `effectModule_unitInterval_representation` (QUESTIONS **A3** *and* **B14** — do not attack before the B14 ruling) — the only one left |
| **known false** | none in this directory |

Nothing in `B/Eff` is known false, and nothing is waiting on a thesis-B
ruling: the open thesis-B rulings (B10, B12, D6, D7) all bite in `B/Dils`.

---

## `VNExamples.lean` — the eleven von Neumann examples

All eleven are **Examples/Corollaries** of eff.tex, and this matters for
costing: nine of them are asserted with **no proof in the text**, or with a
one-line pointer.  There is very little to transcribe here; almost all of the
mathematics has to be supplied.

### The root: `effectus_vn` (180V) and `effectus_vn_partial` (180V)

*Route.* eff.tex:832 says only "**To see `vNᵒᵖ` is an effectus in total form,
adapt the proof of `emod-effectus`**" — QUESTIONS **A3** already records that
there is no proof to transcribe.  `emod_effectus` (191II) *is* proved, in
`StatesPredicates.lean:1480`, and the bridge it goes through,
**`effectusTotalForm_of_pres`** (`StatesPredicates.lean:819`), is exactly what
`effectus_vn` should use: it reduces `EffectusTotalForm D` to the three axioms
of 180I verified against *any* concrete presentation of the final object and
the binary coproducts.  Two further worked instances of that bridge are in the
same file (`emod_effectus_aux:1492`, `exc_rng_eff:1881`).

*What has to be built.*

1. `HasTerminal (WStarNCPU.{u}ᵒᵖ)`, i.e. `ℂ` is **initial** in `vN`: existence
   is `algebraMap`, uniqueness is unitality + `ℂ`-linearity.  Normality of
   `z ↦ z • 1` needs closedness of the positive cone (Mathlib
   `isClosed_nonneg`).  ~60 lines.
2. `HasFiniteCoproducts (WStarNCPU.{u}ᵒᵖ)`, i.e. finite **products** in `vN`.
   Terminal object: **`WStar.trivial`** — now available; what is left is
   `IsTerminal (WStarNCPU.of WStar.trivial)`, whose every obligation is a
   `Subsingleton.elim`, ~30 lines.  Binary products: `A × B`, and Mathlib
   already has `CStarAlgebra (A × B)`; `PartialOrder`, `StarOrderedRing` and
   `Theses.VonNeumannAlgebra` on the product are componentwise.  ~120 lines.
   **Do not route this through thesis A's `⊕ᵢ𝒜ᵢ = lp 𝒜 ∞`** — that carries
   `[∀ i, Nontrivial (𝒜 i)]`, which is precisely what the coproduct with the
   initial object violates.  Mathlib's `Prod`/finite-`Pi` C\*-instances have no
   such hypothesis, and that is the fix for the second half of the recorded
   blocker.
3. The three axioms of 180I at that presentation.  In `vN` they are statements
   about `A × ℂ`, `A × B` and `ℂ × ℂ × ℂ`; the *proofs* are the ones
   `emod_effectus` gives for effect modules, run in a different concrete
   category.

*Costing.* **~500–800 lines, one to two sessions**, with step 3 the bulk.
`effectus_vn_partial` is then the partial-form counterpart; the thesis notes
(eff.tex:835) that the partial maps are the ncpsu-maps, i.e. exactly
`WStarCPSU`, so most of the work is shared, but the PCM structure
(`f ⊥ g` iff `f + g` is again subunital, `f ⋁ g = f + g`) and the effects data
(`I = ℂ`, `truth = ` the unit map) have to be built explicitly.  Add ~300
lines.  **This is the highest-value target in the directory**: eight of the
remaining ten sit behind it.

*Classification:* **reachable, long.**

### The eight hypothetical examples

`effectus_vn_real_separating` (190III), `diamond_effectus_vn` (206III),
`vn_is_andthen_eff` (211IV), `vn_is_dagger_category` (215VI),
`vn_has_dilations` (221III), `vn_dilation_order_correspondence` (223VI),
`exc_purec_no_biproduct` (224VI), `exc_purec_equal` (224VII).

Each takes an **arbitrary** `s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ` and
must produce its conclusion for *that* `s`.  Since this session, the
enrichment part of `s` is known to be canonical
(`effectusPartialStructure_homPCM_unique`), so a proof may compute with the
concrete `⋁`; what still has to be supplied is the transport along
`s.effectus.I ≅ ℂ`.  Nobody should attack any of these before 180V exists —
without a concrete `s` in hand there is nothing to compute with.

Individually:

* **`effectus_vn_real_separating` (190III)** — **PROVED, session 86** (~400
  lines).  eff.tex:2136 asserts it and cites `[effintro]`; no proof, so the
  mathematics was supplied.  One correction to what stood here: separation of
  states is *not* `np_faithful` — that axiom is about *positive* elements, and
  what is needed is separation of *self-adjoint* ones, which takes the
  conjugation `ω(y⁺ · y⁺)` (`eq_zero_of_ncpsu_states`).
* **`diamond_effectus_vn` (206III)** — eff.tex:4460 is a bare Examples list
  ("`vNᵒᵖ`, `CvNᵒᵖ`, `EJAᵒᵖ` and `Set` are all ⋄-effectuses"), no proof.
  `f_⋄` is `p ↦ ⌈f(p)⌉`; the ceiling calculus is fully developed in
  `A/VN/Projections.lean` and on the import path.  **~250 lines after 180V.**
  *Reachable, blocked on the root.*
* **`vn_is_andthen_eff` (211IV)** — the one example whose text gives a real
  route, and the only one **blocked outside `B/Eff`**: eff.tex:4861 proves
  axiom 1 by **105V** `positive-map-uniqueness` and axiom 2 by **100III**
  `pure-fundamental`, both in `Theses/A/Proc/Measurement.lean`.  100III is
  proved; **105V is `sorry`** (`Measurement.lean:6610`).  And `A/Proc` is not
  imported by `VNExamples.lean` — adding `import Theses.A.Proc.Measurement`
  is a small change but a real one, and the file header's claim that nothing
  here needs `A/Proc` is wrong.  *Blocked: A/Proc 105V, plus the root.*
* **`vn_is_dagger_category` (215VI)** — eff.tex:5338 is a **Corollary** of
  211IV together with the †'-effectus theorem of 215V, so it inherits 211IV's
  blocker.  Whether 215V's sufficiency direction is available in the tree
  should be checked before costing.  *Blocked, via 211IV.*
* **`vn_has_dilations` (221III)** — eff.tex:6806 says "as shown in
  `existence-paschke`", and **`existence_paschke` is proved**
  (`B/Dils/Paschke.lean:1376`), on the import path.  This is therefore the
  cheapest of the eight once 180V exists: the work is fitting the Paschke
  dilation into the abstract `IsDilation` shape.  **~200 lines after 180V.**
  *Reachable, blocked on the root.*  **Session 86: the ~200 is wrong.**
  "Fitting into the abstract shape" *is* the whole job — `IsDilation` asks for
  `SharpMap ϱ`, `IsTotal ϱ` and `IsPure h`, and `existence_paschke`'s
  universal property quantifies over *nmiu* maps where the abstract one
  quantifies over *sharp total* maps.  See the session-86 block at the top.
* **`vn_dilation_order_correspondence` (223VI)** — eff.tex:7095, "By
  `paschke-correspondence`".  `paschke_correspondence_mem`, `_embedding` and
  `_surjective` are all **proved** (`Paschke.lean:2861, 2893, 2973`).  Same
  shape as 221III.  **~200 lines after 180V.**  *Reachable, blocked on the
  root.*  **Session 86: also re-costed upwards** — it consumes 221III (it is
  handed an abstract `IsDilation`, which has to be recognised as the Paschke
  one) and additionally needs `asrt` and `sef` concretely.
* **`exc_purec_no_biproduct` (224VI)** and **`exc_purec_equal` (224VII)** —
  **both PROVED, session 90** (~200 and ~380 lines; see the session-90 block
  at the top — neither needed the GNS/`paschke-pure`/factoriality of the one
  solution nor the pseudoinverse and `M₃` of the other).  What follows is the
  session-82 costing, kept for the record. —
  Exercises\* with **full author solutions** (`bsols.tex:3358–3479` and
  `3480–3540`).  These are the only two vN examples with a transcribable
  proof, but they are also the heaviest: 224VI classifies the non-zero pure
  maps `𝒜 → ℂ` through a GNS representation, `paschke-pure`, minimality of a
  projection and factoriality of `⌈⌈p⌉⌉𝒜`; 224VII works inside `M₄` with
  filters, `⌈ξ(1)⌉` and pseudoinverses.  **~600 and ~400 lines**, each after
  180V *and* after the †-effectus development of parsecs 215–220 that
  `PureCat` and `AndThenEffectus` presuppose.  *Blocked on the root and on
  215–220.*

### `effects_sea` (225V) — **PROVED, session 84** (the one that never needed 180V)

> Closed in ~230 lines, not the ~400–600 costed below.  `bsols.tex` has
> nothing on it (225V is an *Examples*, not an Exercise).  The whole statement
> reduces to `√a b √a = √b a √b ⟺ ab = ba`; see PROVING-LOG, session 84, for
> the spectral argument and for the reusable by-products
> `nonneg_of_normal_of_swap` and `nonneg_mul_of_normal` (*a product of
> positives is positive as soon as it is normal*).

*Route.* eff.tex:7381 asserts that `[0,1]_𝒜` is a sequential effect algebra
with `a & b = √a b √a`, without proof.  Note the neighbouring **225VI**
proves only (S1), (S2), (S3) for a †-effectus, so it is not a route to the
whole statement; ours is `SequentialEffectAlgebra` with six fields, and
`seq_comm_orth`, `seq_comm_assoc`, `seq_comm_compat` are the Gudder–Greechie
content.  Everything needed is Mathlib's continuous functional calculus —
**always available, so the old "needs the import" note in `why-open.csv` was
wrong**; the statement is an isolated one with no dependence on the effectus
structure at all.

*Costing.* **~400–600 lines**, dominated by the commutation axioms
(`√a b √a = √b a √b` forces `ab = ba`, and then the identities are C\*-algebra
computations).  *Reachable and independent — the best target in this file
for anyone who does not want to build 180V.*

---

## `StatesPredicates.lean` — none left (FINISHED, session 85)

* **`exc_dm_effectus_kleisli` (192III.3, `exc-dm-effectus`, eff.tex:2410,
  Exercise\*)** — **PROVED, session 83**, by transcribing the author's
  solution (`bsols.tex:1991–2170`), which is complete and usable exactly as
  the survey described it, and the costing of ~500–700 lines was right at its
  low end: **~480 added lines**, of which ~190 are the `MConvexComb` glue and
  ~290 the Kleisli plumbing and the three axioms.  Notes for anyone building on it:
  * The new section `DMKleisli` gives `Kl(𝒟_M)` a concrete `CoprodPres`
    (`one M = PUnit`, `P X Y = X ⊕ Y`, `pinl/pinr = kpure κᵢ`) together with
    `HasTerminal`/`HasFiniteCoproducts`, and the three axioms go through
    `effectusTotalForm_of_pres`, its third worked instance.
  * The only real content is `MConvexComb.exists_glue`: given `α ∈ 𝒟_M(X+1)`
    and `β ∈ 𝒟_M(1+Y)` agreeing in `𝒟_M(1+1)`, the glued `δ` sums to `1`
    because `α(κ₂*) = ⋁_y β(κ₂y)`.  That is the author's own computation.
  * Six `MConvexComb`/`PCM` helpers (`eq_eta_punit`,
    `map_apply_of_unique_fiber`, `PCM.le_of_mem_isSumOf`,
    `eq_zero_of_map_eq_zero`, `exists_map_inl`, `jointly_injective_of_three`)
    were **moved up** in the file, from the `AConv_M` block (parsecs 193–194)
    to just before the `𝒟_M` monad, because 192III.3 needs them earlier.  No
    statement changed; the `AConv_M` uses are unaffected.
  * `Kleisli.Adjunction.adj` is in Mathlib but was **not** used: the coproduct
    is quicker to give by hand than to extract from the adjunction, because
    Mathlib's `BinaryCofan.mk` does not reduce reducibly to the given
    coprojections.  Related trap: `DMKleisli.pres` must be `@[reducible]`, or
    `(pres M).T.of` does not unfold and every `rw` against a `kpure` lemma
    fails with a type mismatch that the error message reports as "did not find
    an occurrence of the pattern".
* ~~**`cancellative_iso_convex` (192V.4, eff.tex:2588)**~~ — **PROVED,
  session 85**, in the new section before the theorem, **~289 net added
  lines** (not the ~500–600 costed here), axiom-clean.  The thesis cites
  \[statesofconvexsets, thm. 8\] and proves nothing; `eff.tex:2589` has no
  `\label` and is not an Exercise, so `bsols.tex` has no solution either — the
  mathematics is ours, and this is an independent check of the cited claim.
  The route, for anyone comparing it with thm. 8: `V` is `X →₀ ℝ` modulo
  `MConvex.embSubmodule`, the relators `t·(P − Q)` with `h P = h Q`, `t > 0`;
  the `AddCommGroup`/`Module ℝ` structure is `Submodule.Quotient`'s, closure
  of the relators under `+` is the Eilenberg–Moore law via
  `MConvexComb.cmix`, and **cancellativity is used exactly once**, to show
  `embMap` injective.  New reusable API: `MConvexComb.coeFinsupp`,
  `MConvexComb.cmix` (+ `coeFinsupp_cmix`, `cmix_eta_eta`),
  `MConvexComb.bin_comm` (general effect monoid), `MConvex.h_cmix`.
  `map_spec_of_list`, `map_bin`, `mu_spec_of_subset`, `mu_bin` were **moved
  up** from the parsec-196 block to next to `bin_eq_zero`; no statement
  changed, and their old site carries a comment.

## `EffectAlgebras.lean` — one

* ~~**`finite_effectMonoid_boolean` (178III.2, eff.tex:645)**~~ — **PROVED,
  session 84**, in the new section `FiniteBoolean`, ~185 added lines,
  axiom-clean.  No proof exists in eff.tex (it cites \[basmsc, prop. 40\]) and
  we did not consult `basmsc`, so this is an **independent check** that the
  cited claim holds.  The route, for anyone comparing it with prop. 40:
  * `emon_finite_mul_orth` (`a ⊙ aᵖ = 0`) and `emon_finite_isInf` (`a ⊙ b` is
    the `≼`-meet) are lifted out of the existing proofs of `emon_finite_idem`
    and `finite_effectMonoid_commutative`, which now both call them;
  * `emon_finite_perp_iff`: `a ⊥ b ⟺ a ⊙ b = 0`.  This is the pivot, and it
    is **not** downstream of distributivity as this survey previously said:
    `a = a ⊙ 1 = (a ⊙ b) ⋁ (a ⊙ bᵖ) = a ⊙ bᵖ ≼ bᵖ`;
  * de Morgan `(a ⋁ b)ᵖ = aᵖ ⊙ bᵖ` (`emon_finite_orth_ovee`), so the partial
    sum *is* the join `(aᵖ ⊙ bᵖ)ᵖ` (`emon_finite_ovee_eq`) and that join is
    the `≼`-supremum (`emon_finite_isSup`), being the dual of the meet;
  * distributivity from `b ⊔ c = b ⋁ (c ⊙ bᵖ)` (`emon_finite_sup_eq`), and
    only the `⊓`-over-`⊔` inequality is needed
    (`DistribLattice.ofInfSupLe`);
  * the structure equality then needs three `cases`-and-`subst` helpers
    (`emonB_pcm_eq`, `emonB_ea_eq`, `emonB_em_eq`; the first duplicates
    `Comparisons.lean`'s `pcm_eq_of_data`, which cannot be imported here) —
    and `⊓ = ⊙`, `⊥ = 0`, `⊤ = 1`, `·ᶜ = ·ᵖ` all match by `rfl`.
  * The **MSc props 13–16 calculus was not used**: it is stated for
    `Ortholattice`, which a finite effect monoid is not known to be until this
    theorem is proved.  Anyone re-costing similar items should discount it.
* **`effectModule_unitInterval_representation` (179III.2, eff.tex:739)** —
  Gudder–Pulmannová, cited only.  QUESTIONS **A3** for the parking, and
  **QUESTIONS B14** (new, session 84) for the separate defect that
  **our statement is weaker than the cited result**: it produces
  `[PartialOrder V] [IsOrderedAddMonoid V]` and `0 ≤ u` where the source needs
  an *ordered real vector space* (positive cone closed under nonnegative
  scalars — exactly the `PosSMulMono`/`SMulPosMono` pair that the *converse*
  half `orderIntervalEffectModule` had to be given) with `u` an **order
  unit**.  As written it would be provable without being the theorem, so a
  closed `sorry` here would be worth nothing.  **Do not attack before the
  ruling.**

---

## Suggested order for the next worker

1. ~~`effects_sea` (225V)~~ — **proved, session 84** (~230 lines, not the
   ~400–600 costed here); see the block at the top of this file.
2. ~~`finite_effectMonoid_boolean` (178III.2)~~ — **proved, session 84**
   (~185 lines, not the ~250–400 costed here); see above.
3. ~~`effectus_vn` + `effectus_vn_partial`~~ — **proved, session 83.**
4. **The uniqueness of the effect object** — "the `I` of any
   `EffectusPartialStructure` on `vN_cpsuᵒᵖ` is isomorphic to `ℂᵤ`", ~150–250
   lines, described in the session-84 block at the top.  It is now the root of
   the whole file: all eight remaining `VNExamples` items need it, and — since
   `cancellative_iso_convex` was proved in session 85 — **nothing else in
   `B/Eff` is open** except the ruling-blocked 179III.2.  Every open item in
   this directory is now in `VNExamples.lean`.

Do **not** start on 211IV/215VI until A/Proc's 105V is closed, and do not add
`import Theses.A.Proc.*` to any file other than `VNExamples.lean`.

---

## New infrastructure added this session

In `Comparisons.lean`, section `FinPACUnique` (general effectus theory; it
**belongs in `Effectus.lean`** and is parked here only because moving it there
would invalidate the whole `B/Eff` olean chain — move it at the next full
rebuild):

* `pcm_eq_of_data` — two `PCM`s agree if their zero, `Perp` and `ovee` do;
* `finPAC_eq_zero_of_hom_to_initial` — every map into the initial object is
  `0`, from the **finPAC axioms alone** (`Quotients.lean` has the same
  statement for an effectus in *partial form*, via `eq_zero_of_one_zero`);
* `perp_pproj`, `ovee_pproj` — `▷₁ ⊥ ▷₂` and `▷₁ ⋁ ▷₂ = ∇`;
* `perp_iff_exists_bound`, `ovee_eq_bound` — the bound characterisation;
* `finPAC_pcm_unique`, `effectusPartialStructure_homPCM_unique`.

In `VNExamples.lean`, section `TrivialAlgebra`: the six missing instances for
`PUnit` and the object `WStar.trivial`.

All are `#print axioms`-clean (`propext, Classical.choice, Quot.sound`), and
both files compile with 0 errors.
