# Decisions

Everything in the formalization that is waiting on an author, in one place, in
the order that clears the most work.  It is meant to be answerable in a sitting:
each item says what is being asked, what it holds up, what the choices are, what
we recommend and why, and what we do on each answer.

**How to answer.**  Name the item and pick a letter — "1.2 (a)", "2.4 (b)".
Nothing else is needed; we will make the source edits and the Lean edits and
record the ruling.  Where an item is really an erratum acceptance we say so, and
"accept" is a complete answer.

**Where things stand.**  **9 declarations are unproved**, and **nothing else
in the tree depends on a `sorry`**.  All nine are waiting on §1 below.  (It
was ten until 2026-08-29, when `kaplansky_hilbmod_A₂` turned out to be
**true** — the witness reports `ω₀(A₂) = 0`, which had been read as the
functional not seeing it.)  (The
declaration total was 8931 at the last full build; it has grown since and is
not re-counted here, but the `sorry` count is checked on every commit.)

The eleventh, `centrally_similar_basic_5` (104III.5), is **gone from this
list: it was proved on 2026-08-29** — see §4.2, which used to explain why it
was waiting on mathematics rather than on you.

Beyond the `sorry`s there are 100 open rows in `ERRATA.md` (those are
corrections, not decisions, and are not repeated here) and **ten** audit
rows in `docs/audit/` marked `left-ruling`, re-counted 2026-09-03 (twelve on
2026-08-29; 51IX §2.6 was closed on 2026-09-02, and 69IX's rows left §2.4 on
2026-09-03 when the printed 69X route was taken without restating 30X): three
are §2 (191II §2.3, 30X §2.4, 28II §2.5), two are §3 (132III §3.2, 34V §3.3),
and four are §1 (199V §1.1, 215II §1.2, and 139XI §1.4 and 179III.2 §1.5,
which are the two that hold up a `sorry`).

The tenth, **180V** `effectus_vn_partial`, names no item of this file at
all — it points only at `QUESTIONS.md` B13.  So a reader working through
§1–§3 will not meet it, which is why it is named here.

Point numbers are the primary key; the Lean name is given so we can find the
declaration.  Sources were re-read for this document — several entries that
`QUESTIONS.md` still carries have been overtaken by later edits, and those are
in §4 rather than in front of you.

## At a glance

| # | point | question | holds up | we recommend |
|---|---|---|---|---|
| 1.1 | 169II / 170IV | corner: ncp or ncpsu universal property? | `surjective_nmiu_2` | (a) read it in `W*_cpsu` |
| 1.2 | 206II.2/.4 / 211IV | must the ⋄-self-adjoint square root be pure? | `vn_is_andthen_eff` | (a) yes, it is meant to be |
| 1.3 | 158III–158V | printed proof is false — replace it how? | 3 × `kaplansky_hilbmod_A*` | (a) delete, use the linking algebra |
| 1.4 | 139XI | case (ii) takes the complement in the wrong space | `ess_uniq_pur` | (a) complements in `𝒦'` |
| 1.5 | 179III.2 | strengthen our statement, or drop the point? — ruled (a) 2026-09-04 | `effectModule_unitInterval_representation` | (a) strengthen, else (b) drop |
| 1.6 | 106III.3, 116III.4 | two errata to accept | 2 red rows | accept |
| 2.1 | — | may we match the printed statement without asking? — ruled (a) 2026-09-04, only in a dedicated statement-alignment pass | 54 audit rows | (a) standing authorisation |
| 2.2 | — | does "no forward references" apply outside `A/CStar`? — ruled (a) 2026-09-04: global and retroactive, out-of-order proofs allowed insofar as the thesis does that itself | 520 audit rows | (b) forward only; label the rest |
| 2.3 | 191II | what does "equivalent to a subcategory" mean? | 1 audit row | (c) weaken to faithful |
| 2.4 | 30X | may clause (1) name `ϱ_Ω`? | 1 audit row | (a) yes |
| 2.5 | 28II.4 | may the unique element be identified with `f(a)`? | 1 audit row | (a) yes |
| 2.6 | 51IX | may `q` be asked to be ℂ-linear? — done 2026-09-02 under D1 | 0 audit rows | (a) yes |
| 2.7 | 180V | should the effect object be pinned? | 1 audit row | (a) yes |
| 3.1 | 101VII.1 | does the middle clause gain `aqa* ≤ p`? | nothing | (a) yes — erratum |
| 3.2 | 132III.4/.5, 123II.2 | may "=" be an equivalence of categories? | nothing | (b) reword |
| 3.3 | 34V.3, 32II, 33I, 141III | mirrored cp condition for modules? | nothing | (a) add the mirrored condition |
| 3.4 | 98VI | replace the hint or turn it round? | nothing | (a) replace |
| 3.5 | 34VI.1 | the solution slot is an empty `\TODO{}` | nothing | your call |
| 3.6 | `onb1` | the solution over-assumes | nothing | leave it |
| 3.7 | — | bridge Kadison to Mathlib's Sakai `WStarAlgebra`? | nothing | scope question |
| 3.8 | 169II / 169VIII | may a corner's / filter's test object be a bare C\*-algebra? | 4 audit rows | (a) narrow to von Neumann |

§4 lists seven things `QUESTIONS.md` still asks that the current sources have
already answered.  **Do not spend time on those.**

---

## 1. Decisions that unblock a `sorry`

Hardest to reverse first.  Answering all of §1 removes six of the eleven
unproved declarations outright, closes a seventh immediately under one of the
two readings on offer, and turns the remaining three from "must not be touched"
into ordinary work.

### 1.1 — 169II `dils-corner`: is the universal property of a corner read in ncp or in ncpsu?

*(`QUESTIONS.md` D7.  Blocks `surjective_nmiu_2` in `Theses/B/Dils/Pure.lean` —
the converse half of exercise **170IV** `surjective-nmiu`.)*

**What is being asked.**  169II (`dils.tex`, parsec 1690, point 20) defines: an
ncp-map `h : 𝒜 → ℬ` is a corner for `a ∈ [0,1]_𝒜` if `h(a) = h(1)` and every
**ncp**-map `f : 𝒜 → 𝒞` with `f(1) = f(a)` factors uniquely through `h` by an
**ncp**-map `f'`.  Should `h`, `f` and `f'` all be read as **ncpsu** (subunital)
maps — i.e. should the universal property be read in `W*_cpsu`?

**Why it is being asked: the printed converse of 170IV is false.**  Machine-
checked in the tree as `surjective_nmiu_2_false` (axiom-clean, verified
2026-08-26):

> `𝒜 = ℬ = ℂ`, `z = 1`, `φ = λ·id` for any `λ > 0`, `λ ≠ 1`.  A positive
> multiple of a corner is again a corner under 169II **as printed**, because the
> mediating map `f' = λ⁻¹f` is ncp and `λ ≠ 0` makes `x ↦ λx` a bijection, so
> uniqueness is untouched.  But `φ(1) = λ ≠ 1`, and every nmiu-map is unital.
> Taking `φ = λ·h_z` breaks the claim at **every** central projection, so
> nothing is special about `z = 1`.

The author's own solution (`bsols.tex`, `surjective-nmiu`) goes wrong at one
step: it builds `ϑ₁ : z𝒜 → 𝒞` and `ϑ₂ : 𝒞 → z𝒜` from the two universal
properties, gets `ϑ₁ϑ₂ = id` and `ϑ₂ϑ₁ = id`, and then says "`ϑ₁` is an
ncp-isomorphism and consequently an nmiu-isomorphism by `iso`".  But `iso`
(**99IX**, proc.tex:878) is about **ncpsu**-isomorphisms, and its proof opens
with `f⁻¹(1) ≤ 1`, hence `1 = f(f⁻¹(1)) ≤ f(1) ≤ 1` — exactly the step `λ·id`
defeats.  As printed, 169II delivers only an *ncp*-isomorphism.

**This is B11 one point earlier.**  For filters (**169VIII**) the mediating map
had to be made subunital, and that was ruled on 2026-08-16.  The identical edit
does *not* suffice here: for filters the hypothesis `f(1) ≤ b ≤ 1` already
forces the quantified `f` to be subunital, whereas `f(a) = f(1)` constrains
nothing — restricting only `f'` would make even the standard corner `h_z` fail
its own universal property (`f = 2·h_z` gives `f'(1) = 2 ≰ 1`).

**Options.**

* **(a)** Read 169II in `W*_cpsu` throughout: `h`, the quantified `f` and the
  mediating `f'` are all ncpsu.
* **(b)** Leave 169II alone and state the converse of 170IV only for corners
  that are additionally **unital**.

**Recommendation: (a).**  It is the same repair as B11, it puts the universal
property in the category where `iso` lives and where corners are quotients, and
it kills the witness completely: for `λ < 1` the mediating map `λ⁻¹·id` is not
subunital, and for `λ > 1` the map `λ·id` is not itself subunital.  The standard
corner survives — `h_a(1) = ⌊a⌋` is the unit of `⌊a⌋𝒜⌊a⌋`, and
`f'(1) = f'(h_a(1)) = f(1) ≤ 1` — so nothing that should be a corner stops being
one.  Under (b) the exercise is repaired but 169II keeps a universal property
that does not characterise what it is used to characterise.

**What we do.**  Under (a): change `IsCornerFor` to quantify over ncpsu, prove
`surjective_nmiu_2`, and re-check the *existence* clause at the four places that
build corners (`standard_corner_dils` 169IV, `h_is_corner_for_unital_map` 169V,
`paschke_corner` 171II, `corners_composition` 98VI) — the *uniqueness* clause
only gets easier everywhere.  `surjective_nmiu_1` is true and proved and is
unaffected.  Under (b): add "unital" to 170IV's second half and prove it there.

### 1.2 — 206II.2/.4: must the ⋄-self-adjoint square root of a ⋄-positive map be **pure**?

*(`QUESTIONS.md` B15.  Blocks `vn_is_andthen_eff` in
`Theses/B/Eff/VNExamples.lean` — **211IV** `vn-is-andthen-eff`.)*

**What is being asked.**  The two theses define ⋄-positivity differently.

* **proc.tex 103I**: `f` is ⋄-**self-adjoint** if it is *pure* and contraposed
  to itself; ⋄-**positive** if `f = gg` for a ⋄-self-adjoint `g`.  The square
  root is pure, and `f` is pure with it.
* **eff.tex 206II** (verified against the current source, eff.tex:4413): an
  endomap is ⋄-self-adjoint if `f^⋄ = f_⋄` — **no purity** — and 206II.4 reads
  "a **pure** endomap `f` is ⋄-positive if `f = g ∘ g` for some ⋄-self-adjoint
  `g`".  The word "pure" sits on `f`, precisely because `g` is not asked to be
  pure.

So the effectus notion is formally weaker.  211II.1 asks for a *unique*
⋄-positive `asrt_p` with `1 ∘ asrt_p = p` — uniqueness in the **larger** class —
and 211IV discharges it by citing **105V** `positive-map-uniqueness`, which is
uniqueness in the **smaller** one.  The citation leaves a step.

**The step is not cosmetic.**  A ⋄-self-adjoint square root allowed to be impure
would break uniqueness outright: for self-adjoint but not positive `b`, the map
`ad_b : x ↦ bxb` is pure and contraposed to itself with `ad_b(1) = b²`, while
`ad_b ≠ ad_{|b|}`.  What has to be shown is that no ⋄-self-adjoint `g` with
`gg = ad_b` exists.  For `𝒜 = M₂` and `b` invertible this is checkable by hand
(Kadison forces `g = ad_c` or `ad_c ∘ transpose`, and self-contraposition forces
`b` positive up to sign); we have found no general argument, and neither thesis
gives one.

**Options.**

* **(a)** 206II.4 *does* intend `g` to be pure — eff.tex's ⋄-self-adjointness
  silently means proc.tex's, and "pure endomap `f`" in 206II.4 is redundant.
  The fix is to the wording of 206II.
* **(b)** 206II.4 is as printed, and 211IV needs an extra step: *in `vNᵒᵖ`, a
  ⋄-self-adjoint `g` whose square `gg` is pure has a **pure** ⋄-self-adjoint
  square root with the same square.*

**Evidence.**  The statement/proof audit compared `Theses/B/Eff/DiamondAmp.lean`
clause by clause with eff.tex: our definitions take the **printed form
verbatim** (`DiamondSelfAdjoint f := diaPull f = diaPush f`, no purity;
`DiamondPositive f := IsPure f ∧ ∃ g, DiamondSelfAdjoint g ∧ f = g ≫ g`, purity
on `f`, none on `g`).  Everything else in 211IV is proved and axiom-clean —
axiom 2 of 211II is `su_quot_after_compr_pure` (100III `pure-fundamental`,
exactly as eff.tex:4862 says); axiom 1's existence half is `su_exists_asrt`; its
uniqueness half is `su_asrt_unique_of_pure_sqrt`, which is 105V reached through
two dictionary lemmas.  `vn_is_andthen_eff` is
`su_andThenEffectus_of_pure_sqrt` (axiom-clean) applied to exactly one
hypothesis, and that hypothesis is the file's only `sorry`:

    ∀ {X} (g : X ⟶ X), DiamondSelfAdjoint g → IsPure (g ≫ g) →
      ∃ h, IsPure h ∧ DiamondSelfAdjoint h ∧ g ≫ g = h ≫ h

**Recommendation: (a)**, unless you know the missing step is true.  Under (a)
the two theses agree, 211IV's citation of 105V becomes verbatim correct, and the
`sorry` closes with no further mathematics.  Under (b) 211IV keeps a genuine
gap that neither thesis addresses, and the tree keeps a `sorry` that is open
research.  Nothing else in the tree turns on this: `Effectus.lean`'s partial-form
machinery was checked field by field against 180VII and is faithful either way.

**What we do.**  Under (a): add an `IsPure` conjunct to `DiamondSelfAdjoint`,
delete the now-redundant one from `DiamondPositive`, discharge the hypothesis,
and the red row goes green the same day.  Under (b): the `sorry` stays, and we
record it as open mathematics rather than as a pending decision.

### 1.3 — 158III–158V `kaplansky-hilbmod`: the printed proof is false; how should it be replaced?

*(Arithmetic re-checked 2026-08-28.  The falsity rests on a computation carried
out on paper, and every other falsity verdict in the tree that the author is
asked to accept — 106III.3, 116III.4 — is machine-checked.  This one is now
reproducible at least: `scripts/kaplansky_witness.py` redoes it exactly over ℚ,
the witness living in the span of `e₁, e₂, eₙ`, and **all nine recorded values
come out**, the factor-4 identity `1/9 = 4(−1/12 − 1/18 + 0 + 1/6)` included.
It is still not a Lean proof.  It also found two slips in our own prose, both
now fixed in `Kaplansky.lean`: the module action's side and the mirrored inner
product's argument order were written the way the thesis writes them, and read
literally in that file's own convention two of the six values are `0`.)*

*(`QUESTIONS.md` B10.  Blocks three: `kaplansky_hilbmod_A₁`, `A₁'` and `A₂'`
in `Theses/B/Dils/Kaplansky.lean`.  **Corrected 2026-08-29**: it used to say
four, counting `A₂` — but `A₂` is *true*, and is now proved.  The witness gives
it the value `0` at `ω₀`, which this document and the file both read as one
functional failing to see it; it is not that.  What separates `A₂` from `A₂'` is
which resolvent moves with `α`: in `A₂` the varying one multiplies the bounded
vector `y_α` and the constant one the small vector `y_α − y`, so Cauchy–Schwarz
for the `ω`-seminorms plus `inv1p_conj_le_one` plus ultraweak continuity of
multiplication by a **constant** closes it — the thesis's own argument.  In `A₂'`
the two change places, and that is where `ω₀(A₂') = 1/6` bites.  Nothing else in
this section changes: 158V itself is still false, and the printed proof of 158II
still has to be replaced.)*

**What is being asked.**  **158II** itself is **true and proved** — `kaplansky_hilbmod`
and the self-dual case `kaplansky_hilbmod_of_selfDual` are unconditional and
axiom-clean (verified 2026-08-26), with no strengthening of the hypotheses.  But
the thesis proves 158II through **158V**, and 158V is **false**: `h` is not
ultranorm continuous, not even on norm-bounded sets, so `kaplansky-splitting`
does not converge.  The decision is how to repair the printed text.

**The counterexample** (paper computation, in `ERRATA.md` and in the file's own
docstring; not machine-checked — the four estimates are transcribed and left
`sorry` because they are false):

> `ℬ = B(ℓ²)`, `X = ℬ` over itself; `y = |e₂⟩⟨e₁|`, `yₙ = |e₂⟩⟨e₁+eₙ|` (`n ≥ 2`).
> Then `⟨yₙ−y, yₙ−y⟩ = pₙ` and `ω(pₙ) → 0` for every np-functional, so
> `yₙ → y` ultranorm, inside a ball of radius `√2`.  Yet at `ω₀ = ⟨e₁, ·e₁⟩`,
> **independently of `n`**: `ω₀(A₁) = −1/12`, `ω₀(A₁') = −1/18`, `ω₀(A₂) = 0`,
> `ω₀(A₂') = 1/6`, and `ω₀(⟨hy − hyₙ, hy − hyₙ⟩) = 1/9`.  Nothing tends to `0`.

The failing step is the right-hand half of `kaplanskytodo2` (dils.tex:4251) — the
one whose "different, but simpler" proof the thesis omits.  The left-hand half is
fine.  (The same computation shows `kaplansky-splitting` is off by a factor `4`:
`⟨hy − hyₙ, hy − hyₙ⟩ = 4(A₁+A₁'+A₂+A₂')`, and `1/9 = 4·(−1/12 − 1/18 + 0 + 1/6)`.
That is a separate `ERRATA.md` row.)

**The approach is dead for every renormalizer, not just this one.**  Let
`φ : [0,∞) → ℝ` and `h(y) := y·φ(⟨y,y⟩)` (the shape of every renormalizer of this
kind, the thesis's `φ(t) = 2/(1+t)` included).  If `‖h(y)‖ ≤ 1` for all `y` and
`h∘g = id` on the unit ball for some `g`, then `h` is **not** ultranorm
continuous: the counterexample above forces `φ(a+c) = φ(a)` for all `a,c > 0`,
so `φ ≡ κ`, so `h(y) = κy` is unbounded unless `κ = 0`, and `κ = 0` contradicts
`h(g(x)) = x`.  The scheme asks one continuous function to be sensitive to the
escaping mass (to contract into the ball) and insensitive to it (to be ultranorm
continuous) at once.  Iterated trimming also fails: `1 − q_{k−1}⋯q₀` is an
ordered product of noncommuting positive contractions and can leave the ball
(`‖·‖ ≈ 1.155` for two ideal trimmers).

**The replacement proof, which the thesis has all the material for.**  Let
`Lk = X ⊕ ℬ` and work in `ℬᵃ(Lk)` (**152X**, parsec 1520).  Embed `X` in the
corner by `cor z = |z ⊕ 0⟩⟨0 ⊕ 1|`, i.e. `[[0,z],[0,0]]`.  Then
`(cor z)*(cor z) = ι⟨z,z⟩`, so the ultrastrong seminorms of `cor z` are exactly
the ultranorm seminorms of `z` — the mirrored quantity `ω(bb*)` that kills every
route through 158V never appears.  `D` sits inside the closed ∗-subalgebra
`S = {T : T(N) ⊆ N, T*(N) ⊆ N}` with `N = cl(D) ⊕ 𝒜`, and 158II's two hypotheses
are exactly what puts it there.  Thesis A's **74IV** `kaplansky` then returns a
net in `S` bounded by `‖cor x‖ = ‖x‖`, and compressing at `0 ⊕ 1` lands in
`cl(D)`.  Three things worth recording: `𝒜` need **not** be ultrastrongly dense
in `ℬ` (74IV is applied to a single element); the classical self-adjointization
`[[0,x],[x*,0]]` is **not** usable (its square has the `|e⟩⟨e|` corner, which
reintroduces the mirror) and not needed, since our `cor` is not self-adjoint and
74IV already handles that; and the only dependency is **150II** `dils-completion`
at parsec 1500, before 1580, so the thesis's own order is respected.

**Options.**

* **(a)** Delete 158III–158V and replace the proof of `kaplansky-hilbmod` by the
  linking-algebra argument.
* **(b)** Demote 158III–158V to a remark recording the failed approach, and add
  the linking-algebra proof.
* **(c)** Keep 158III–158V and add the hypotheses under which the renormalizer
  route would work.

**Recommendation: (a).**  (c) is not available: the obstruction is not a missing
hypothesis but the shape of the map, and the argument above rules out every
renormalizer of that form.  (b) costs pages for a route that is now known to be
dead; if you want the record kept, the erratum entry and this document already
hold it.

**What we do.**  Under (a) or (b) the three remaining `kaplansky_hilbmod_A*`
`sorry`s are **deleted** — they exist only to record that the printed estimates
are false — and the tree goes from 10 unproved declarations to 7.  (`A₂`, the
fourth, is proved and stays either way.)  `kaplansky_hilbmod_of_weak`
(158II from *weak* bounded approximation) and `kaplansky_hilbmod_of_commutative`
stay as independent partial results.  Under (c) we would need the hypotheses
before anything changes.

*(For reference: H. Lin, "Double duals and Hilbert modules", arXiv:2311.15462 §4
proves an analogue under two hypotheses 158II lacks — `𝒜` SOT-dense in `M`, and
the target in the norm-closed `M`-module generated by `D`.  The linking-algebra
proof needs neither.)*

### 1.4 — 139XI `ess-uniq-pur`: case (ii) of the repaired exercise is still false

*(`QUESTIONS.md` B12, **which is stale as written** — see §4.1.  Blocks
`ess_uniq_pur` in `Theses/B/Dils/Stinespring.lean`.)*

**What has already happened.**  The exercise was repaired on 2026-08-18.  The
current `dils.tex:998` asks for a unitary `U` on `𝒦'` with `V = (1 ⊗ U)W`
whenever **(i)** both dilations are minimal (`𝒱 = ℋ ⊗ 𝒦' = 𝒲`), **(ii)**
`dim 𝒱^⊥ = dim 𝒲^⊥`, or **(iii)** `ℋ` and `𝒦` are finite dimensional.  So the
question `QUESTIONS.md` still prints — "which of three repairs?" — is answered.

**What is being asked now.**  Case **(ii)** is false as printed, because the
complements are taken in `ℋ ⊗ 𝒦'` where they must be taken in `𝒦'`.

**Counterexample** (paper, derived for this document; not machine-checked).
*Reviewed 2026-08-28, and unlike §1.3's witness there is nothing here to
recompute:* its content is a dimension count, not an arithmetic one, so a
script would add nothing and only a Lean proof would raise its standing.  What
the review does confirm is the sentence the witness turns on — that it attacks
**(ii) alone**: (i) asks both dilations to be minimal and `𝒱 = ℋ ⊗ ran S₂` is
not `ℋ ⊗ 𝒦'`, (iii) asks `ℋ` and `𝒦` to be finite-dimensional and both are
infinite.  And `(ran S₁)^⊥`, `(ran S₂)^⊥` really are the spans of `e₀` and of
`e₀, e₁`, dimensions `1` and `2`.

> `ℋ = 𝒦' = ℓ²`, `𝒦 = ℋ ⊗ 𝒦'`.  Let `S₁` be the unilateral shift and `S₂` the
> shift by two.  Put `W = 1 ⊗ S₁` and `V = 1 ⊗ S₂`.  Both dilate
> `φ(a) = a ⊗ 1`, since `V*(a⊗1)V = a ⊗ S₂*S₂ = a⊗1 = a ⊗ S₁*S₁ = W*(a⊗1)W`.
> `𝒲` is invariant under the self-adjoint algebra `B(ℋ)⊗1`, so its projection
> lies in the commutant `1 ⊗ B(𝒦')`; concretely `𝒲 = ℋ ⊗ ran S₁` and
> `𝒱 = ℋ ⊗ ran S₂`.  Hence `dim 𝒱^⊥ = dim(ℋ ⊗ ℂ²) = ℵ₀ = dim(ℋ ⊗ ℂ) = dim 𝒲^⊥`
> and **(ii) holds**.  But `V = (1⊗U)W` forces `US₁ = S₂`, so `U` carries
> `ran S₁` onto `ran S₂` and therefore `(ran S₁)^⊥` onto `(ran S₂)^⊥` —
> dimensions `1` and `2`.  No such unitary exists.  (i) and (iii) both fail
> here, so this attacks (ii) alone.

**What (ii) should say.**  Since `𝒱` and `𝒲` are `B(ℋ)⊗1`-invariant, write
`𝒱 = ℋ ⊗ ℒ_V` and `𝒲 = ℋ ⊗ ℒ_W` for closed `ℒ_V, ℒ_W ⊆ 𝒦'` (valid for
`ℋ ≠ 0`).  Case (i) already supplies a unitary `ℒ_W → ℒ_V`; extending it to a
unitary of `𝒦'` needs exactly `dim ℒ_V^⊥ = dim ℒ_W^⊥`, the complements taken
**in `𝒦'`**.  That is also what `berr.tex`'s own prose means when it lists "the
ancillar spaces of the same dimension".  Multiplying by `dim ℋ` destroys the
information whenever `ℋ` is infinite-dimensional, which is what the witness
exploits.

**Options.**

* **(a)** Replace (ii) by `dim ℒ_V^⊥ = dim ℒ_W^⊥` in `𝒦'`, with one sentence
  saying `𝒱 = ℋ ⊗ ℒ_V` because `P_𝒱` lies in the commutant.
* **(b)** Keep (ii) and add `dim ℋ < ∞` to it.
* **(c)** Delete (ii), leaving (i) and (iii).

**Recommendation: (a).**  It is the hypothesis the argument actually consumes,
it matches the erratum's prose, and it keeps the general case that (i) and (iii)
do not cover.  (b) makes (ii) nearly redundant against (iii).

**What we do.**  Realigning our `ess_uniq_pur` to the current `dils.tex` needs no
ruling — the source moved under us and our statement is a transcription of the
first printing, which is why the audit records it as **false as ours** (it drops
all three hypotheses; the proof is `sorry`, so nothing false is derived).  We
will restate it with whichever form of (ii) you choose and then attempt the
proof — which is real work, not a free close.

### 1.5 — 179III.2 `gudder1998representation`: strengthen our statement, or drop the point? — **ruled (a), 2026-09-04**

*(`QUESTIONS.md` B14, now closed, deleted 2026-09-04.  Blocks `effectModule_unitInterval_representation` in
`Theses/B/Eff/EffectAlgebras.lean`.  Audit row
`bdils-pure-beff-states-effectalgebras.csv:228`, `left-ruling`.)*

**What is being asked.**  eff.tex:737 (Examples 179III.2) says: "If `V` is an
**ordered real vector space with order unit** `u`, then `[0,u]` is an effect
module over `[0,1]`.  In fact, every effect module over `[0,1]` is of this form
[gudder1998representation]."  Our rendering of the second sentence is weaker
than the cited theorem in two ways, and the decision is whether to fix it or to
drop the point.

**The gap.**

1. *No scalar compatibility.*  We produce `V` with `[PartialOrder V]` and
   `[IsOrderedAddMonoid V]` only — the additive half.  An ordered real vector
   space also has its positive cone closed under nonnegative scalars.  This is
   not pedantry: the **converse half of the very same Examples point**,
   `orderIntervalEffectModule`, could not be proved until `[PosSMulMono ℝ V]`
   and `[SMulPosMono ℝ V]` were added to it, and they are there now
   (`EffectAlgebras.lean:3474`).  So the two halves of one Examples point
   currently use two different meanings of "ordered real vector space", and only
   one of them is yours.
2. *`0 ≤ u` is not "order unit".*  We ask only that `u` be positive.  The source
   requires every `v : V` to satisfy `v ≤ n • u` for some `n : ℕ` — which is
   what makes `[0,u]` generate `V`, and is the whole content of a
   *representation* theorem.

**Consequence.**  As written, 179III.2 could be discharged **without proving
Gudder–Pulmannová**, because the `V` it may produce need not be an ordered
vector space in your sense and `u` need not be an order unit.  A closed `sorry`
here would be worth nothing, which is why the declaration is deliberately not
attacked.

**Options.**

* **(a)** Strengthen: add the two `SMul` monotonicity hypotheses to the produced
  `V`, and replace `0 ≤ u` by an order-unit condition.
* **(b)** Drop 179III.2 as out of scope — it is cited to the literature with no
  proof in `eff.tex`, and we do not transcribe what is not there.

**Recommendation: (a) if the point is to stay in the tree at all, otherwise (b)
without hesitation.**  What must not happen is the status quo, where a weakened
statement stands under the name of a theorem it does not assert.  Note that
three of the four other "cited only, never proved" statements have since been
proved independently (178III.2/.4, 192V.4, `extensive_effectus`), so (b) is not
a pattern we are otherwise following.

**What we do.**  Ruled (a) on 2026-09-04: the statement is restated with the
two `SMul` monotonicity hypotheses and an order-unit condition, and the proof
of Gudder–Pulmannová is attempted in the same pass (see the row and
`PROVING-LOG.md`).  Under (a) as originally written: add an `OrderUnit`
predicate, restate, and attack the proof.  Under (b): delete the declaration;
the tree loses a red row and the `docs/why-open.csv` and audit rows are closed.

### 1.6 — Two errata acceptances, each of which frees a `sorry`

These are not decisions with options; they are `ERRATA.md` rows where "accept"
is the whole answer, listed here because each is holding a red row open.

* **106III.3** clause (E) (`sequential_product_counterexample_3`,
  `A/Proc/Measurement.lean`).  "If `u_p* = u_p` for all `p` then axiom (E)
  holds" is **false**, machine-checked as
  `sequential_product_counterexample_3_ax5_is_false` (axiom-clean, verified
  2026-08-26): in `B(ℂ²)` with `p = diag(1, 9/25)` and `u_p` the flip
  `!![0,1;1,0]` (self-adjoint and unitary on `⌈p⌉𝒜⌈p⌉ = 𝒜`, and `u_x = ⌈x⌉`
  elsewhere), `a := u_p√p = !![0,3/5;1,0]` has `e₁ a e₂ = 0 ≠ e₂ a e₁`.  The
  clause is kept unchanged as documentation and will be deleted or restated on
  acceptance.
* **116III.4** (`tensor_simple_facts_4`, `A/Proc/Tensor.lean`).
  `⊗ : 𝒜 × ℬ → 𝒜 ⊗ ℬ` is **not** jointly ultraweakly continuous, so part 4 of
  the exercise cannot be done.  Machine-checked as
  `tensor_simple_facts_4_counterexample` (axiom-clean, verified 2026-08-26):
  `𝒜 = ℬ = ℓ^∞(ℕ)` with the diagonal functional
  `χ = ∑ₘ 2^{−m−1}(evₘ ⊗ evₘ)`.  The hint's own reduction target *is* true and
  is proved as `tensor_simple_facts_4_hint_form`, so the repair is to state the
  **separate** continuity.  Note the knock-on: **116V**'s proof of 116IV part 1
  cites the joint form, and needs the same repair.

---

## 2. Decisions that unblock audit rows

No `sorry` turns on any of these.  What turns on them is whether ~250 statement
divergences recorded by the audit get repaired or get recorded as deliberate.
Hardest to reverse first.

### 2.1 — The standing question: may our statement be brought up to the printed one without asking? — **ruled (a), 2026-09-04, only in a dedicated pass**

This is not in `QUESTIONS.md`; it is the reason four of the six items below
exist.  The house rule is that **we never change a Lean statement without a
ruling**.  That rule has done its job — it is why `ess_uniq_pur` never acquired
a false proof — but it now generates a queue of individually trivial questions
of exactly one shape: *our statement says less than the printed one; may we make
it match?*

The audit found **174 such rows** (`weaker`) out of 2248 when it ran on
2026-08-20.  **Re-counted 2026-08-29 it is 54 of 2504** (twelve of those closed
on 2026-09-02: §2.6, and the ten `lp 𝒜 ∞` binder rows of 20aI, 34VI, 42V and
47IV, which a 70-line reindexing equivalence settled) — the intervening
sessions repaired most of them as ordinary work, which is what option (a)
below anticipates.  So the scope of this ruling is now a third of what the
paragraph was written for.  (The other two columns moved the other way:
`stronger` 49 → 55, `differs` 30 → 37, for 146 rows not `ok` against the
recorded 253.)  A8, A10 and B13 below are three of them that happen to
have been noticed by hand before the audit ran (A9 was a fourth, closed on
2026-09-02 under the D1 ruling, §2.6).

**Options.**

* **(a)** A standing authorisation: **a change that brings a Lean statement
  closer to the printed statement of its own point needs no ruling** — it is a
  transcription fix.  Changes that go *beyond* the printed statement, or that
  weaken it, still need one.
* **(b)** Keep the current rule and answer each case.
* **(c)** A standing authorisation limited to the cases where the audit records
  the strengthening as *free* (i.e. the existing proof already establishes it).

**Recommendation: (a).**  Bram's ruling of 2026-08-22 — *"before filing a row,
ask whether a reader would stumble, not whether a checker would"* — applies with
full force here.  A reader does not stumble over 51IX; only our own
bookkeeping does.  Under (a) the four items below are answered at a stroke,
along with most of the remaining 54, and the queue in front of you stays what it should
be: places where the *thesis* is unclear or wrong.

**What we do.**  Ruled (a) on 2026-09-04 with one condition, in the author's words: "only when explicitly performing this task. We don't want an agent to 'cheat' in an unrelated task."  So a statement is brought up to the print only inside a pass whose assignment is exactly that (`docs/audit/STATEMENT-BRIEF.md`); in every other job statements stay byte-identical.  The first such pass runs the same day over the `weaker`/`differs` rows whose verdict is ours.

### 2.2 — Does the "no forward references" rule apply outside `A/CStar`? — **ruled (a), 2026-09-04, with the thesis's own forward references allowed**

*(`HANDOFF.md`, "Still open", item 0.  Not in `QUESTIONS.md`.  Governs the
audit's 520 proof-divergence rows.)*

**What is being asked.**  You decided that the formalization should validate the
thesis's own bootstrapping — *a proof of a statement at parsec `P` may use only
what the thesis has at or before `P`* — and that has been implemented for
`A/CStar`, which now bootstraps from parsec 110 upward with exactly two imported
facts at the base (`IsSelfAdjoint.spectralRadius_eq_nnnorm` for 16III and
`IsSelfAdjoint.mem_spectrum_eq_re` for 11XV.1, both below the CFC in Mathlib's
import graph).  The question is whether the same rule now applies
**retroactively** to `A/VN`, `A/Proc`, `B/Dils` and `B/Eff`.

**What it costs.**  Of 2248 audited proofs, 753 follow the thesis step for step,
975 have no thesis proof to match, and **520 diverge** — 247 by a different
route, 141 mild, 114 closed by a Mathlib lemma without transcribing the author,
18 `sorry`.  In the elementary chapters `mathlib` is the norm, not the exception
(43 of 109 rows in `A/CStar/Basic`), and in a few places it inverts the thesis's
own dependency order (11XIII from 11XV.1, which the thesis proves from 11XIII).

**Options.**

* **(a)** The rule is global and retroactive: we rewrite the `mathlib` and
  order-inverting proofs along the author's routes, chapter by chapter.
* **(b)** The rule is global going forward, but existing proofs are left alone
  and simply *labelled* — the audit CSVs already carry the class.
* **(c)** The rule applies to `A/CStar` only, because that is where the
  bootstrapping claim is being made.

**Ruled (a) on 2026-09-04**, in the author's words: "we go with (a), but with the caveat that we can use out-of-order proofs insofar the thesis does that itself."  So the rule is global and retroactive: `mathlib` rows are rewritten along the author's routes chapter by chapter, and a proof at parsec `P` may cite a later point only where the printed proof of that point does so.  `scripts/forward_check.py` finds the order-inverting proofs against the printed `\sref`s; the `mathlib` rows are worked file by file under `docs/audit/BRIEF.md`.

**Recommendation: (b).**  Under (a) the largest single item is not even in the
list above: closing parsecs **120–150** (Banach-space-valued contour integration
— Goursat, Cauchy, Taylor, winding numbers, bridged to Mathlib) would remove the
last two imports and make `A/CStar` self-supporting from the ground up.  That is
the highest-value target in the chapter and worth doing on its own merits; but
sweeping the other four chapters for provenance is weeks of rework for no new
mathematics, and the audit already records exactly which proofs are affected, so
(b) loses nothing that (a) would find.

### 2.3 — 191II: what does "equivalent to a subcategory of `EMod_M^op`" mean?

*(`QUESTIONS.md` B16.  Audit row
`bdils-pure-beff-states-effectalgebras.csv:86`, `left-ruling`.  Lean:
`emod_effectus_representation`, `Theses/B/Eff/StatesPredicates.lean`.)*

**What is being asked.**  The Theorem's second sentence (eff.tex:2206) reads:
"every effectus `C` in total form with scalars `M` and separating predicates is
equivalent to a subcategory of `EMod_M^op`".  191VII establishes exactly one
thing — `Pred f = Pred g` iff `p ∘ f = p ∘ g` for every `p ∈ Pred Y`, so that
`Pred` is faithful iff `C` has separating predicates — and closes in a sentence:
"So if `C` has separating predicates, `C` is equivalent to the subcategory
`Pred C` of `EMod_M^op`."

**That inference is invalid.**  A faithful functor does not exhibit its domain
as equivalent to a subcategory of its codomain.  Take `C` the discrete
two-object category and `D = 1` the terminal category: the unique functor
`C → D` is faithful (every hom-set of `C` is a singleton or empty, so no two
arrows are identified), the only subcategories of `1` are `∅` and `1`, and `C`
— two isomorphism classes — is equivalent to neither.  Nor does "full onto its
image" help: in that same example the functor onto its image is full **and**
surjective on objects, and the equivalence still fails.  What faithfulness does
not control is object identification.

**Options**, in decreasing strength.

* **(a)** `Pred` is **full** as well as faithful.  Then `C` is equivalent to the
  *full* subcategory on the objects `Pred X`.  Fullness is a substantial claim —
  for `C = vN_cpsuᵒᵖ` it says every `M`-effect-module map `Pred 𝒜 → Pred ℬ` is
  `p ↦ p ∘ f` for an ncpsu-map `f` — and neither `eff.tex` nor `bsols.tex`
  proves or asserts it.
* **(b)** `Pred` is faithful **and injective on objects**.  Then `C` is
  *isomorphic* to the (non-full) subcategory `Pred C`, the older sense in which
  a faithful functor "is" a subcategory inclusion.  Also not claimed.
* **(c)** Conclude only that `Pred` is faithful, i.e. that `C` is concrete over
  `EMod_M^op`, and weaken the Theorem's second sentence to say so.

**Recommendation: (c)**, unless you have fullness in mind.  (c) is exactly what
the printed proof delivers, and it is what we have: `emod_effectus_representation`
produces `F : Tot C ⥤ (EMod_{Scal C})^op` with object part `Pred X`, morphism
part pinned to `p ↦ p ∘ f`, and `F.Faithful` — proved and axiom-clean (verified
2026-08-26).  Under (a) or (b) the printed proof needs a genuinely new step, and
the Lean cost is the cost of that step, not of the packaging.

**What we do.**  Under (c): one sentence of `eff.tex`, nothing in Lean.  Under
(a) or (b): the new step first, then the subcategory clause is added to
`emod_effectus_representation`.

*(Not a question for you: the Theorem's headline — "with scalars `M` and
separating predicates" — is also unasserted by our `emod_effectus`, but that is
a missing tool for computing `Pred` and `Scal` of `Par C`, recorded on the
declaration itself.)*

### 2.4 — 30X `proto-gelfand-naimark`: may clause (1) name `ϱ_Ω`?

*(`QUESTIONS.md` A8.  Audit row `acstar-matrices-representation.csv:138`,
`left-ruling`.  Lean: `proto_gelfand_naimark_2`.)*

**What is being asked.**  30X states a three-way equivalence for a collection
`Ω` of p-maps: (1) `ϱ_Ω : 𝒜 → B(ℋ_Ω)` is injective; (2) `Ω` is centre
separating; (3) `Ω'` is order separating — plus the closing claim that
`ϱ_Ω(𝒜)` is a C\*-subalgebra and `ϱ_Ω` an miu-isomorphism onto it.  We have
(2) ⇔ (3) in full (`proto_gelfand_naimark_1`, proved), but we render (2) ⇒ (1)
as `∃ H (ρ : 𝒜 →⋆ₐ[ℂ] B H), Function.Injective ρ`, which mentions neither `Ω`
nor `ϱ_Ω`.

**Two consequences, both real.**  (i) The converse (1) ⇒ (2) becomes
*unstatable*: in the existential form, clause (1) no longer depends on `Ω`, so
it cannot imply anything about `Ω`.  Only half the equivalence is captured.
(ii) It collapses 30X.2 into **30XIV**: as stated, our (2) ⇒ (1) says "every
C\*-algebra admitting a centre separating family of p-maps has an injective
representation", which *is* Gelfand–Naimark, four points later.  So in our tree
30X.2 is not a step towards 30XIV; it is 30XIV.

**Options.**  **(a)** Restate 30X as the genuine three-way equivalence with
clause (1) reading `Function.Injective (dsumRep …)`, and add the closing
miu-isomorphism claim.  **(b)** Leave it and mark the equivalence deliberately
unstated.

**Recommendation: (a).**  The obstacle this question was filed for is **gone**:
`dsumRep` in `Theses/A/CStar/Representation.lean` *is* the thesis's `ϱ_Ω`, the
diagonal operator on `lp (fun ω => ω.GNS) 2`, built because Mathlib has the
single-`ω` GNS representation and the Hilbert direct sum but not the diagonal
operator.  The closing claim is on the shelf as `injective_miu_iso_on_image`.
Downstream: `proto_gelfand_naimark_2` has one user, `gelfand_naimark` (30XIV,
`Theses/A/CStar/Representation.lean`), which the strengthened form still gives
at once; the `A/VN` uses are all of `proto_gelfand_naimark_`**`1`**.

### 2.5 — 28II.4 `functional-calculus`: may the unique element be identified with `f(a)`?

*(`QUESTIONS.md` A10.  Audit row `acstar-matrices-representation.csv:114`,
`left-ruling`.  Lean: `functional_calculus_4`.)*

**What is being asked.**  The exercise asks: given `f ∈ C(spec(a))`, show that
`f(a)` is the unique element of `C*(a)` with `φ(f(a)) = f(φ(a))` for every
character `φ`.  Two clauses at once: the character condition pins down at most
one element, **and** that element **is** `f(a)`.  We state only the first (plus
bare existence); the name `f(a)` never occurs, so our statement never says which
element it is — and that identification is the usable content: it is what lets
one compute with `f(a)` through characters, and what the four later parts
(spectral mapping, naturality, composition) are built on.

**Options.**  **(a)** Strengthen to
`∀ b, (∀ φ, φ b = f (φ a)) ↔ (b : 𝒜) = cfc f a`, or minimally add the conjunct
`∀ φ, φ (cfc f a) = f (φ a)`.  **(b)** Leave it.

**Recommendation: (a); the cost is the ruling and nothing else.**
`functional_calculus_4` is proved by the thesis's own route — the unique element
is `(gelfandStarTransform (C*(a))).symm (f ∘ j)` with `j : φ ↦ φ(a)` from part 3
— and Mathlib's `cfc f a` is *defined* by that same formula.  The missing
conjunct has been compiled in the scratchpad (14 lines, no `sorry`, not
committed because it changes a statement); with it, the iff form follows from
the uniqueness half already proved.  Nothing downstream uses
`functional_calculus_4`.

### 2.6 — 51IX `Linfty-vn`: may `q` be asked to be ℂ-linear? — **done 2026-09-02**

*(Was `QUESTIONS.md` A9, now deleted.  Audit row `avn-basic.csv` `Linfty_vn`,
`repaired`.)*  The clause `q (z • f) = z • q f` was added to `Linfty_vn` and
proved by the existing `qmap_smul`, on the ground that the D1 ruling of
2026-08-16 (add `smul` to `IsLinftyOf`) is a ruling on this exact defect — the
word "miu" includes ℂ-linearity, so the omission was ours — and needs no
second asking.  Nothing was reproved; the one consumer in `A/Proc/Duplicators`
ignores the new conjunct.  If this reading of D1 is too broad, revert
`Linfty_vn`'s clause and reopen the item.

### 2.7 — 180V: should `effectus_vn_partial` pin the effect object?

*(`QUESTIONS.md` B13, partly stale — see §4.3.  Audit row
`beff-vnexamples.csv:11`, `left-ruling`.  Lean: `effectus_vn_partial`.)*

**What is being asked.**  180V (eff.tex:827) says the partial maps of `vNᵒᵖ`
"correspond to the ncp-maps `f` with `f(1) ≤ 1`".  We state
`Nonempty (EffectusPartialStructure WStarCPSU.{u}ᵒᵖ)`, which asserts only that
*some* effectus structure exists.  Two clauses of the sentence are not in it:
the effect object is `ℂ`, and the comparison with `Par(vNᵒᵖ)` itself.  The
neighbouring `cho_thm_1` does pin its effect object
(`∃ s, s.effectus.I = Par.of (⊤_ C)`), so the asymmetry is ours.

**Options.**  **(a)** Strengthen to
`∃ s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ, s.effectus.I = suI` — one line,
since the proof already builds `I = ℂᵤ` (`suEffectusPartialForm`).  **(b)**
Leave it and record both clauses as deliberately unstated.

**Recommendation: (a)**, but this is the least consequential item in §2 and it
is purely about faithfulness to the text.  It unblocks nothing: the eight
examples of `VNExamples.lean` each take their own arbitrary
`s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ` as a hypothesis, and what they
need — "the effect object of *any* such structure is isomorphic to `ℂᵤ`" — is a
different lemma, `vn_effObj_iso`, which is now **proved and axiom-clean**
(verified 2026-08-26).

The second clause, the comparison with `Par(vNᵒᵖ)`, is a larger piece of work
and we are **not** asking for it here: `Par C` needs `HasFiniteCoproducts` and
`HasTerminal` as instances, and for `WStarNCPU.{u}ᵒᵖ` those live inside the
proof of `effectus_vn` as a record, so they must be hoisted and transported
before the hom-bijection can even be stated.

---

## 3. Questions with no current consequence

Nothing in the tree waits on any of these.  They are here so that "no" is
available as an answer and the items can then be closed.

### 3.1 — 101VII.1: does the middle clause gain the hypothesis `aqa* ≤ p`?

*(`QUESTIONS.md` A12.  Lean: `equivalent_examples_1_corners`.)*  The point says:
"if `p` and `q` are projections with `a*pa ≤ q` (as in `ad-ncp`), then the maps
`a*(·)a : p𝒜p → q𝒜q` and `a(·)a* : q𝒜q → p𝒜p` are contraposed."  The
hypothesis governs only the **first** map — it is exactly 94III `ad-ncp`'s
hypothesis, and it is what puts `a*(·)a` inside `q𝒜q`.  It says nothing about
`a(·)a*`, and without a hypothesis that map need not exist: take `p = 0`,
`q = 1`, `a = 1`; then `a*pa = 0 ≤ 1 = q` holds, while `a(·)a*` is the identity
of `𝒜` and `p𝒜p = {0}`.  The mirrored hypothesis is `aqa* ≤ p`.

Nothing in the tree is wrong: our statement takes both maps as *given* ncp-maps
and proves them contraposed, and both places where the thesis uses the clause
supply the mirror anyway (94III's `adNCP` is the first map; the "in particular"
`π_s`/`c_s` pair is `p = 1`, `q = s`, `a = s`, where `aqa* = s ≤ 1 = p`).

**Options.**  **(a)** 101VII.1 gains `aqa* ≤ p` — an erratum, since as printed
the sentence names a map that need not exist.  **(b)** The middle clause is
about two maps whose existence is presupposed, which is what we implement.

**Recommendation: (a).**  A reader *does* stumble here — the sentence asserts a
map into `p𝒜p` with nothing making it land there.  94III itself is correct and
is used one-sidedly elsewhere, so it needs no change; only the mirrored instance
is missing.  Under (a) we restate `equivalent_examples_1_corners` with the two
maps **constructed** from 94III and its mirror rather than assumed — plumbing
only; the proof is untouched, since both sides of the contraposition reduce to
`x a t = 0`.

### 3.2 — 132III.4: may "=" be read as an equivalence of categories?

*(`QUESTIONS.md` A11.  Lean: `dup_vna_is_monoid_4`.)*  The point says "Conclude
that `CMon(W*_miu) = Mon(W*_miu) = CMon(W*_cpsu) = Mon(W*_cpsu)`."  The
four-fold equality is not stated in the tree and cannot be: Mathlib renders the
two constructions as *distinct structure types* (`Mon C` is `⟨X, [MonObj X]⟩`,
`CommMon C` adds `[IsCommMonObj X]` and a `BraidedCategory` instance), so
`CMon(W*_miu) = Mon(W*_miu)` is not expressible as an equality.  The two
cross-category equalities have the same problem from the other side: the
categories have different ambient hom-sets (nmiu vs ncpsu).

What the *content* of item 4 is, we do prove: every monoid in `W*_cpsu` is
commutative and its multiplication is an nmiu-map (`dup_vna_is_monoid_4`),
together with item 1 (a monoid in `W*_cpsu` is a duplicator) and item 3 (the
monoid morphisms in either category are exactly the nmiu-maps).

**Options.**  **(a)** "=" is to be read as an **equivalence** of categories, and
in the cross-category cases as a fully faithful essentially surjective
comparison functor.  **(b)** Reword the point to "a monoid in either category is
automatically commutative, its multiplication is the algebra's own, and its
morphisms are the nmiu-maps" — which is what we already prove.

**Recommendation: (b)**, on grounds of what it buys.  No `sorry` closes either
way; the ruling decides whether two clauses ever acquire statements.  Under (a)
the remaining work is **packaging, not mathematics**: a tensor bifunctor on the
category `WMIU`, associators and unitors as natural isomorphisms, and the
coherences restated in Mathlib's bundled form — all over equations that are now
proved (`vn_smc_pentagon`, `vn_smc_triangle`, `vn_smc_unitors_agree`,
`vn_smc_hexagon`, `vn_smc_symmetry`, the four naturality lemmas, `exists_tmapM`,
`exists_associator`, `exists_unitors`, `exists_braiding` — all green).  For
`W*_cpsu` there is a further, purely organisational obstacle: `A/Proc` has no
category of von Neumann algebras and ncpsu-maps, and the one that exists
(`WStarCPSU`) belongs to thesis B, so `A/Proc` cannot import it.
**132III.5's first half** `Mon(W*_miu) ≅ dW*_miu` is blocked on exactly the same
packaging; its second half `dW*_miu ≃ Set^op` is proved (`dupEquivSetOp`).

A **third** clause hangs on this same ruling, added by the A/Proc statement pass
of 2026-08-26: **123II.2's parenthetical** "(This makes `nsp` strong monoidal.)"
(proc.tex:4688).  The part's own claim — that `(σ,τ) ↦ σ ⊗ τ` is a bijection
`nsp(𝒜) × nsp(ℬ) → nsp(𝒜 ⊗ ℬ)` — is proved (`nsp_tensor_2_bijection`), and
`nsp` is a functor in the tree (`nspFunctor : WMIUᵒᵖ ⥤ Type u`); `Type u` is
already a `MonoidalCategory` in Mathlib.  The only thing missing is again
`MonoidalCategory WMIUᵒᵖ`.  Stating strong monoidality *concretely* instead —
naturality of the bijection in `𝒜` and `ℬ`, plus compatibility with the
associators and unitors — would add statements the thesis never displays, which
is the same choice (a)/(b) as above.

If the answer is (b), all three clauses should be recorded as deliberately
unstated rather than as open work.

### 3.3 — 34V.3 in the module setting: is the mirrored cp condition wanted?

*(`QUESTIONS.md` A13, partly stale — see §4.5.  Audit row
`acstar-matrices-representation.csv:58`, `left-ruling`.  Lean: `ad_cp_3`.)*
34V.3 says: for every element `x` of a Hilbert `𝒜`-module `X`, the vector
functional `T ↦ ⟨x, Tx⟩ : ℬᵃ(X) → 𝒜` is completely positive.  We state the case
`𝒜 = ℂ`, `X = ℋ` only.  The **convention** half of this question was already
settled in session 2 — Mathlib's `CStarModule` convention was approved, and it
is the mirror of the thesis's.  *(Careful: the shorthand this document and §4.5
used to give for that mirror, `⟪x,y⟫_Mathlib = ⟨y,x⟩_thesis`, is not the
relation; the relation is the **opposite algebra**, re-derived at the foot of
this item, and the argument swap is what you get after composing the mirror with
a `star`.  Files that transcribe a printed formula do exactly that — see the
`star ∘ mirror` recipe in `B/Dils/Kaplansky.lean:158` — which is why both
descriptions circulate.  For a `⟨y,y⟩` or a commutative `𝒜` they agree.)*
What is left is narrower.

Under Mathlib's convention the ℂ-linear map `T ↦ inner 𝒜 x (T x)` **fails** our
`IsCompletelyPositiveMap`, which asks `0 ≤ ∑ᵢⱼ bᵢ* f(aᵢ*aⱼ) bⱼ`: what the module
makes positive is `∑ᵢⱼ bⱼ·⟪yᵢ,yⱼ⟫·bᵢ*`, with the `b`'s on the other sides.  The
form that *does* satisfy it is `T ↦ ⟪Tx, x⟫`, and that map is
conjugate-linear in `T`, hence not eligible at all.

**Options.**  **(a)** Add a mirrored companion to `IsCompletelyPositiveMap`
(`∑ᵢⱼ bᵢ·f(aᵢaⱼ*)·bⱼ*`) and state the module version in it — a new definition,
which is why it needs a ruling.  **(b)** Leave 34V.2/.3 in the Hilbert-space
case, with the doc comments recording the divergence, and mark the module
versions deliberately unstated.

**Recommendation: (a).**  *(Changed 2026-08-26.  The recommendation used to be
(b), on the strength of "a second obstruction blocks (a) anyway and needs no
ruling: `ℬᵃ(X)` exists in the tree only as the private `Bax 𝒜 X`, with no
cross-module hom-sets, so `S*TS` for `S : Y → X` has nowhere to live."  That
obstruction was not real and is gone.  `S*TS` is a map `Y → Y` and it is
adjointable, so it lives in `Bax 𝒜 Y`; no hom-set type is needed, only `S`
together with an adjoint.  **34V.2 is now stated and proved for Hilbert
𝒜-modules** — `conjModule` and `ad_cp_2_module` in `A/CStar/Matrices.lean` —
and so is the neighbouring 32IV, whose `J` now carries a `CStarModule C[0,1]`
instance and whose inclusion is proved non-adjointable as a module map.  So
34V.3 is the **only** part of 34V still in the Hilbert-space case, and this
question is the only thing holding it.)*

The exact shape of the clash, re-derived: Mathlib's `CStarModule 𝒜 X` is a
**left** module with `⟪x, a•y⟫ = a⟪x,y⟫`, while the thesis has a right module
with `⟨x, y·b⟩ = ⟨x,y⟩b`.  Both are ℂ-linear in the second argument, so the two
conventions differ by the **opposite algebra**, not by a swap of arguments.  The
ℂ-linear functional `φ T = ⟪x, Tx⟫` gives `φ(Tᵢ*Tⱼ) = ⟪Tᵢx, Tⱼx⟫`, and what the
module structure makes positive is `∑ᵢⱼ bᵢ* ⟪Tⱼx, Tᵢx⟫ bⱼ` — the **transposed**
matrix — whereas `IsCompletelyPositiveMap` asks for `∑ᵢⱼ bᵢ* ⟪Tᵢx, Tⱼx⟫ bⱼ`.
For commutative `𝒜` the two coincide, which is why the Hilbert-space `ad_cp_3`
is unaffected.  What the answer settles is the shape of every future `𝒜`-valued
cp statement, 161II in `B/Dils` included.

**Three statements in the tree already carry the mirror, and a reader who takes
the printed formula literally will read them backwards.**  Found by the
statement-class sweeps of 2026-08-27 and recorded here rather than in
`ERRATA.md`, because none of the three printed points is *wrong* — it is our
carrier that mirrors them, and which convention `ℬᵃ(X)` and `𝒜^N` are read in is
the ruling this item asks for.

* **32II** (`acstar-matrices-representation.csv`, `differs`).  `𝒜^N` is
  Mathlib's `C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜)`, whose inner product is built coordinatewise
  out of `inner x y := y * star x`
  (`Mathlib/Analysis/CStarAlgebra/Module/Constructions.lean:79`), so ours is
  `∑ₙ (yₙ)·(xₙ)*` where cstar.tex 32II displays `∑ₙ (xₙ)*·(yₙ)`.  The two agree
  exactly when `𝒜` is commutative.  Nothing downstream is wrong; every `𝒜^N`
  computation in `A/CStar/Matrices.lean` and `A/CStar/TowardsVN.lean` is
  consistent with *ours*.
* **33I** `matrixBaxEquiv` (`A/CStar/Matrices.lean:1634`, `differs`).  Because
  Mathlib's module is a **left** module, the adjointables on `𝒜^N` are the right
  multiplications and compose backwards, so what is true is
  `M_N(𝒜)ᵐᵒᵖ ≅ ℬᵃ(𝒜^N)`; `M_N(𝒜) ≅ ℬᵃ(𝒜^N)` as 33I.4 prints it is **false**
  under these conventions, and `a ↦ a̲` is a ∗-anti-isomorphism.  Nothing is lost
  by the `ᵐᵒᵖ` — it preserves star, positivity, the order and its suprema.
* **141III** `rightMulEquiv` (`B/Dils/Paschke.lean:2049`, `differs`).  The `N = 1`
  case of the same thing: `ℬ ≅ ℬᵃ(ℬ)ᵐᵒᵖ`, with `rightMul_mul` proving
  `R_s R_t = R_{ts}`.

Answering (a) would let 34V.3, 161II and these three be restated in the thesis's
convention; answering (b) leaves them as they are, with the `ᵐᵒᵖ`s standing and
this item as the place a reader is sent.

### 3.4 — 98VI: replace the hint, or turn its inequality round?

*(`QUESTIONS.md` A1.  Lean: `corners_composition`, **proved**.)*  The hint at
proc.tex:640 gives `⌈τ⌉ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉^⊥`.  That is a restatement of
`τ(π(r^⊥)) = 0` and is the direction one does **not** need; a proof along the
hint needs the **converse**, `⌈τ⌉^⊥ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉`.  In the concrete model
both hold (the two sides are equal), so nothing downstream is wrong.

**Options.**  **(a)** Drop the hint and point at the shorter route: if `π` is a
corner of `p` and `τ` a corner of `r`, then `τ∘π` is a corner of the effect
`s := β'(r)` — four lines, in the 98VI row of `ERRATA.md`.  **(b)** Keep the
carrier route with the inequality turned round.

**Recommendation: (a).**  98VI is proved and needs neither the hint nor its
converse, so the hint currently sends the reader down the longer of two roads
and points the wrong way along it.

### 3.5 — `parsec-340.60` (34VI.1) is an empty `\TODO{}`

*(`QUESTIONS.md` A2.)*  The solution slot exists and is empty, and it is the
**last** entry in `asols.tex` — which is why solution coverage appears to stop
at parsec 340.  Our `cstar_product_4` is proved, but from Mathlib rather than
from your argument, so it is **not cross-checked**.  Nothing is blocked; the
only question is whether you want the solution written, in which case we will
check ours against it.

### 3.6 — `onb1`: the solution over-assumes

*(`QUESTIONS.md` B8.)*  The `bsols.tex` solution to `onb1` assumes self-duality,
which neither the exercise nor our statement requires.  Harmless; noted for
tidiness.  Answering "leave it" closes the item.

### 3.7 — Should Kadison's `VonNeumannAlgebra` be bridged to Mathlib's Sakai `WStarAlgebra`?

*(`HANDOFF.md`, closing note.  Not in `QUESTIONS.md`.)*  Mathlib's
`VonNeumannAlgebra` is the *concrete* (double-commutant) definition and its
`WStarAlgebra` is Sakai-style; neither matches the thesis's Kadison-style
abstract definition, which is what `Theses.VonNeumannAlgebra` implements.
Proving them equivalent would unlock a lot of Mathlib reuse in `A/VN`.  This is
a scope question, not a defect: nothing is blocked, and we would not start it
without a "yes".

### 3.8 — 169II / 169VIII: may a corner's and a filter's test object be a bare C*-algebra?

*(Found by the `stronger`/`differs` sweep of 2026-08-27.  Audit rows
`bdils-pure-beff-states-effectalgebras.csv` 169XII, 169XI.1, 169XI.2a, 169XI.2b.
Lean: `IsCornerFor` `B/Dils/Pure.lean:679`, `IsFilterFor` `:1353`.  Distinct
from §1.1 and from `QUESTIONS.md` D7, which are about ncp vs ncpsu.)*

Both definitions quantify their test object over C\*-algebras —
`∀ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C) (_ : StarOrderedRing C)` —
where dils.tex:6068 and :6124 quantify over the chapter's von Neumann algebras.
More test maps means a harder universal property, so **both predicates are
strictly stronger than the printed ones**.

That is harmless where the predicate is *concluded* — 169IV, 169V, 169VI, 169X
and 170IV.1 all prove the stronger form, and their rows are correctly `stronger`.
It is a **gap** where the predicate is *assumed*: 169XII `dils_filters_injective`,
169XI.1 `dils_filter_basics_1`, 169XI.2 `dils_filter_basics_2a` and `_2b` each
take `IsFilter`/`IsFilterFor` as a hypothesis, so a filter in the printed sense
need not satisfy it and **none of those four statements implies the printed
point**.  No sibling states them for printed filters.  The four rows were graded
`stronger` on the strength of dropped `[VonNeumannAlgebra]` binders; two of those
binder-drops were repaired in session 70 without the grade being moved, which is
how it went unnoticed.  They are now `differs`, `differs`, `weaker`, `weaker`.

**Nothing false is proved and nothing is blocked** — the four are true as stated.

**Options.**  **(a)** Add `[VonNeumannAlgebra C]` to the test-object quantifier
in both definitions, matching the print.  **(b)** Rule that the widened test
class is wanted (it is the stronger and more useful predicate), and record the
four rows as deliberate.

**Recommendation: (a).**  The widening buys nothing at any site: every one of the
eight instantiations already lands on a von Neumann algebra —
`Pure.lean:1922` at `CU = ULift ℂ`, `:2181` at `D'.P` (a `PaschkeTriple`'s `P`,
which carries `vn`), `:2241` at `A`, `:2377` passes its own `C` through, and
`VNExamples.lean:3445`, `:3552`, `:3845`, `:3878` at objects of `WStarCPSU`.

**Cost, if (a).**  ~150–250 lines touched, no new mathematics, in two files.
The two definitions gain a binder; the ten declarations that *prove* the
predicate (`isFilterFor_ncpId` `:701`, `standard_corner_dils` `:944`,
`pdil_isCornerFor` `:1255`, `h_is_corner_for_unital_map` `:1299`,
`dils_stand_filter` `:1821`, `isCorner_comp_nmiuBij` `:2356`,
`isCornerFor_comp` `:4022`, and in `B/Eff/VNExamples.lean`
`su_isQuotient_of_isFilterFor` `:3829`, `su_isComprehension_of_isCornerFor`
`:3862`, `su_stand_corner_ceil`) accept one more binder each; the eight
instantiation sites above supply one more instance each.  **One real
prerequisite:** the `VonNeumannAlgebra (ULift ℂ)` instance lives at
`B/Eff/VNExamples.lean:758`, *downstream* of `B/Dils/Pure.lean`, and would have
to move upstream (~20 lines) for `dils_filters_injective` to instantiate at `CU`.

---

## 4. Overtaken items, for the record

Each of these was once printed as open in `QUESTIONS.md` or `docs/why-open.csv`
and has been overtaken; the text that printed them has since been rewritten,
so nothing here needs an answer.  One line each so a reader who meets the old
wording in a log knows where it went.

| item | what was printed | what is true |
|---|---|---|
| 4.1 | B12's three-option repair list | answered 2026-08-18; `dils.tex:998` carries the disjunction; the live residue is §1.4 |
| 4.2 | "104III.5 waits on a ruling" | ruled 2026-08-19 (`parsec-1040.30`); `centrally_similar_basic_5` proved 2026-08-29 by right-multiplying the central similarity by `(eₙp)^∼¹`, six private auxiliaries in `Measurement.lean`; part 4 is never invoked |
| 4.3 | B13's "uniqueness lemma is unbuilt" | it is `vn_effObj_iso`, proved and axiom-clean |
| 4.4 | A8's obstruction "`ϱ_Ω` does not exist" | `dsumRep` exists; A8 is a pure statement question, §2.4 |
| 4.5 | A13's convention half | ruled in session 2 (Mathlib's, with the swap `⟪x,y⟫ = ⟨y,x⟩`); only the mirrored-cp half is live, §3.3 |
| 4.6 | A11's "the coherences are none of which the tree has" | all nine coherences, four naturality lemmas and `exists_braiding` are proved; §3.2 is only about the word "=" |
| 4.7 | A3, "statements the theses only cite" | four of six bullets proved; the fifth is B14 (§1.5); deleted 2026-08-26 |
| 4.8 | `docs/why-open.csv` listing 65 unproved | rewritten 2026-08-26 to the rows `docs/status.txt` marks red, nine since 2026-08-29; `audit_check.py` enforces the equality both ways |

---

## 5. Suggested follow-ups (ours, not the authors')

Items 1, 2, 3, 4, 6 and 7 were applied on 2026-08-26 and are struck; item 5 is
a proving job and is still open.

1. ~~**Rewrite `docs/why-open.csv`.**  54 of its 65 rows describe finished
   work, and five of its eight `awaiting-ruling` rows point at rulings that
   have landed (§4.8).  As it stands it is the most misleading file in
   `docs/`.~~  **Done 2026-08-26**: 65 rows down to the 11 that
   `docs/status.txt` marks red, each pointing at the §1 item that clears it.
2. ~~**Delete `QUESTIONS.md` A3** and move its two informational remarks into
   `ERRATA.md` as `OPEN (informational)` rows, which is the class that file
   already uses (§4.7).  In particular the dangling "see B4 above" must
   go.~~  **Done 2026-08-26**; the two remarks are now `ERRATA.md` rows under
   **180V** and **189aII.3**.
3. ~~**Reframe B12** to the live question (§1.4) and delete the three-option
   list the author has already answered.~~  **Done 2026-08-26.**
4. ~~**Trim B13's session-84 correction paragraph** (§4.3) and A11's cost
   estimate (§4.6); both describe a tree that no longer exists.~~
   **Done 2026-08-26.**  Note that A11's ⚠ about `dup_vna_is_monoid_4`'s doc
   comment was itself stale: that doc comment had already been brought into
   line with wave 3 and is accurate.
5. **Realign `ess_uniq_pur` to the current `dils.tex`.**  This needs no ruling —
   the source changed under us, so restating is a transcription fix, not a
   strengthening.  It is the one statement in the tree the audit calls *false as
   ours*.  **Still open** (it is a proving job, not a bookkeeping one).
6. ~~**Fix a DISP label in D7.**  `QUESTIONS.md` D7 cites "proc.tex **100IX**
   `iso`"; `iso` is at proc.tex:878, inside parsec 990 point 90, i.e. **99IX** —
   which is what `Pure.lean`'s own doc comment says.  The audit's standing note
   applies: a wrong label sends the next reader to the wrong point.~~
   **Done 2026-08-26**, in `QUESTIONS.md` and also in `docs/BDils-survey.md`
   row 170IV.2, which carried the same wrong label and which neither audit had
   caught.
7. ~~**Record in `QUESTIONS.md` A13** that the convention half was ruled in
   session 2 (§4.5), so the entry reads as the narrower question it now
   is.~~  **Done 2026-08-26.**
