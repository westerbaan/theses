# Questions for the authors

Everything in this file needs a decision from an author.  Nothing here is a
Lean problem: each item is either a defect in a thesis statement, or a choice
about how faithfully our statement should track the thesis.

Findings that need **no** decision live elsewhere: thesis defects to be
corrected are in [ERRATA.md](ERRATA.md), and our own mis-transcriptions in
[PROVING-LOG.md](PROVING-LOG.md).

**Everything in this file is open.**  Once a question is answered *and* the
answer is implemented, its section is **deleted** rather than marked resolved —
on 2026-08-16 that removed B2, B4, B5, B6, B7, D2, D3, B9 and the whole
"Resolved" section (821 → 345 lines).  The rulings themselves are preserved in
the commit messages that implemented them and in PROVING-LOG.md, so nothing is
lost; git history has the full text.  Do not re-add a resolved item.

Conventions: **DISP** is the display number (e.g. `192V.3`); erratum keys are
the `parsec-N.M` keys of the errata block at the top of `../asols.tex`.
Line references drift whenever the sources are edited — **locate by point
number, not by line**.

---

## Thesis B (`eff.tex`, `dils.tex`, `bsols.tex`) — all open

Thesis A was ruled on 2026-08-13; none of thesis B has been.

### B10. 158II `kaplansky-hilbmod` — **now proved, by a different route**; the printed proof (158III–158V) must be replaced
`dils.tex` parsec 1580.  The thesis proves 158II via **158V**, and 158V is
**false** (counterexample in `PROVING-LOG`/`ERRATA`; `B(ℓ²)`, `y = |e₂⟩⟨e₁|`,
`yₙ = |e₂⟩⟨e₁+eₙ|`).  **158II itself is true**: it is now proved in Lean
(`Theses/B/Dils/Kaplansky.lean`, 2026-08-16) through the **linking algebra**,
with no strengthening of its hypotheses.

**The proof.**  Let `Lk = X ⊕ ℬ` (a Hilbert ℬ-module) and work in the von
Neumann algebra `ℬᵃ(Lk)` (**152X** `ba_vonNeumannAlgebra`, which needs `Lk`
self dual).  Embed `X` in the corner by `cor z = |z ⊕ 0⟩⟨0 ⊕ 1|`, i.e.
`[[0,z],[0,0]]`.  Then

    (cor z)* (cor z) = ι⟨z,z⟩,    ι b = [[0,0],[0,b]],

so the ultrastrong seminorms of `cor z` are **exactly** the ultranorm
seminorms of `z` — the mirrored quantity `ω(bb*)` that kills every route
through 158V never appears.  `D` sits inside the closed ∗-subalgebra
`S = {T : T(N) ⊆ N and T*(N) ⊆ N}`, `N = cl(D) ⊕ 𝒜`, and the two hypotheses
of 158II are exactly what puts it there: `⟨D,D⟩ ⊆ 𝒜` (by polarization from
`⟨d,d⟩ ∈ 𝒜`) and `𝒜·D ⊆ D`.  Ultranorm density of `D` gives
`cor x ∈ ultrastrong-closure(S)`, thesis A's **74IV** `kaplansky` returns a
net in `S` bounded by `‖cor x‖ = ‖x‖`, and compressing at the vector `0 ⊕ 1`
lands in `cl(D)`; a norm approximation plus a rescaling `d ↦ t·d` puts it back
in `D` inside the ball (`kaplansky_hilbmod_of_closure`).

Three points worth recording, because they answer questions the earlier
analysis left open.

1. **`𝒜` need not be ultrastrongly dense in `ℬ`** (the hypothesis Lin's
   Theorem 4.4 needs and 158II lacks).  74IV is applied to a *single element*
   `cor x` and a subalgebra whose ultrastrong closure need not be everything.
2. **The self-adjointization `[[0,x],[x*,0]]` of the classical proof is not
   usable and not needed.**  Its square has the `|e⟩⟨e|` corner, which
   reintroduces the mirror (`θ_{e,e} = |e₂⟩⟨e₂|` is constant along the
   standard counterexample), so `ξ(dₙ) → ξ(x)` fails ultrastrongly.  Our
   `cor` is not self-adjoint, and 74IV — repaired in `A/VN` for exactly this
   reason — already handles non-self-adjoint elements.
3. **The only dependency is the self-dual completion 150II** `dils_completion`
   (parsec 1500, before 1580, so the thesis's own order is respected), used to
   pass from `X` to a self-dual `X̄`; ultranorm density is transitive, and both
   the norm bound and the seminorms are computed from the inner product, which
   the embedding preserves.  `150II` is still `sorry` in Lean, so
   `#print axioms kaplansky_hilbmod` shows `sorryAx`.  The **self-dual case**
   `kaplansky_hilbmod_of_selfDual` is unconditional and axiom-clean.

*Decision needed*: how to repair the thesis.  Concretely, 158III–158V should
be deleted or demoted, and the proof of `kaplansky-hilbmod` replaced by the
linking-algebra argument above (which the thesis has all the material for:
152X at parsec 1520, 150II at 1500, `kaplansky` at 74IV).  The erratum row for
158V in `ERRATA.md` carries the same request.

*Superseded material, kept because it rules routes out.*  The renormalizer
approach is dead for **every** renormalizer, not just the thesis's:

**Claim.** Let `φ : [0,∞) → ℝ` and `h(y) := y·φ(⟨y,y⟩)` (functional calculus —
the shape of every renormalizer of this kind, the thesis's `φ(t) = 2/(1+t)`
included).  If `‖h(y)‖ ≤ 1` for all `y ∈ X` and `h∘g = id` on the unit ball for
*some* `g`, then `h` is **not** ultranorm continuous.

*Proof.*  In `ℬ = B(ℓ²)`, `X = ℬ`, take `v ⊥ uₙ` with `‖v‖² = a > 0`,
`‖uₙ‖² = c > 0` and `uₙ → 0` weakly; put `y := |e₂⟩⟨v|`, `yₙ := |e₂⟩⟨v+uₙ|`
(all rank one, hence in `D = 𝒜 = K(ℓ²)`).  Since `⟨y,y⟩ = a·P_v` is rank one,
`φ(⟨y,y⟩) = φ(0)(1−P_v) + φ(a)P_v` and therefore `h(y) = φ(a)·y`; likewise
`h(yₙ) = φ(a+c)·yₙ`.  Now `⟨yₙ−y, yₙ−y⟩ = |uₙ⟩⟨uₙ| → 0` ultraweakly, so
`yₙ → y` ultranorm, while

    h(yₙ) − h(y) = (φ(a+c) − φ(a))·y + φ(a+c)·|e₂⟩⟨uₙ|,

whose second term is ultranorm null.  Continuity at `y` thus forces
`φ(a+c) = φ(a)` for **all** `a, c > 0`, i.e. `φ ≡ κ` on `(0,∞)`.  Then
`h(y) = κy` for every `y ≠ 0`, so `‖h‖` is unbounded on `X` unless `κ = 0`,
and `κ = 0` contradicts `h(g(x)) = x` for `x ≠ 0`. ∎

The scheme asks one continuous function to be *sensitive* to the escaping mass
(to contract into the unit ball) and *insensitive* to it (to be ultranorm
continuous) at once; restricting `h`'s continuity to points `g(x)` or to nets
from `D` does not help, since the counterexample already lies inside that
restriction.  Also recorded: iterated trimming fails because the accumulated
coefficient `1 − q_{k-1}⋯q₀` is an ordered product of noncommuting positive
contractions and can exceed the unit ball (`‖·‖ ≈ 1.155` for two ideal
trimmers) — there is no two-sided trimming on a one-sided module.  H. Lin,
*Double duals and Hilbert modules*, arXiv:2311.15462 §4 proves an analogue
under two hypotheses 158II lacks (`𝒜` SOT-dense in `M`; the target in the
norm-closed `M`-module generated by `D`); the linking-algebra proof needs
neither.  `kaplansky_hilbmod_of_weak` (158II from *weak* bounded
approximation) and `kaplansky_hilbmod_of_commutative` remain in the file as
independent partial results.

### B12. 139XI `ess-uniq-pur` — essential uniqueness of purification is false without a dimension hypothesis; which repair?
`dils.tex:998`, solution `bsols.tex:209`.  The exercise asks to show: if
`V, W : 𝒦 → ℋ ⊗ 𝒦'` satisfy `V*(a⊗1)V = φ(a) = W*(a⊗1)W` for all `a ∈ B(ℋ)`,
then `V = (1 ⊗ U)W` for a **unitary** `U` on `𝒦'`.

**Counterexample** (see ERRATA for the full row): `𝒦' = ℓ²`, `𝒦 = ℋ ⊗ ℓ²`,
`W = 1`, `V = 1 ⊗ S` with `S` the unilateral shift.  Both dilate
`φ(a) = a ⊗ 1`; the only `U` with `V = (1⊗U)W` is `S`, which is an isometry
but not unitary.  Weakening "unitary" to "isometry" does not save it either:
exchanging `V` and `W` in the same example requires a `U` mapping `𝒦'` onto
`𝒦'` isometrically *from* a proper subspace, which is impossible.

The solution is correct up to its last paragraph, which reads "As `𝒱` and `𝒲`
are isomorphic, they have the same dimension and so do `𝒱^⊥` and `𝒲`" (the
last `𝒲` is a typo for `𝒲^⊥`).  Equal dimension does not imply equal
codimension in infinite dimensions, and that is exactly what the extension of
`U₁ : 𝒲' → 𝒱'` to a unitary of `𝒦'` needs.

*Decision needed*: point 139X introduces the property as one "concerning
dilations *of the same dimension*", so a hypothesis is clearly intended.
Which one — (a) both dilations minimal, (b) `dim 𝒦' < ∞`, or (c) conclude only
with a unitary `𝒲' → 𝒱'` between the ancilla subspaces?  Under (a) or (b) the
printed statement is recovered verbatim; under (c) the exercise's own first
half is already the whole content.  We have left `ess_uniq_pur` `sorry`ed and
unchanged.

### D7. 170IV `surjective-nmiu`, converse half — false as printed; corners need subunital mediating maps, exactly as filters did (B11)
`dils.tex:6223` (Exercise), solution `bsols.tex:1365`, `Pure.lean`
(`surjective_nmiu_2`).  The exercise's second half — "any corner of a central
projection is a surjective nmiu-map" — is **false** under **169II**
`dils-corner` as printed, and the counterexample is machine-checked in the
tree as `surjective_nmiu_2_false` (axiom-clean).

**Witness**: `𝒜 = ℬ = ℂ`, `z = 1`, `φ = λ·id` for any `λ > 0`, `λ ≠ 1`.  A
positive scalar multiple of a corner is again a corner under 169II, because
the mediating map is `f' = λ⁻¹f`, which is ncp; uniqueness is unaffected,
since `λ ≠ 0` makes `x ↦ λx` a bijection.  But `φ(1) = λ ≠ 1` and every
nmiu-map is unital.  The same scaling breaks the claim at **every** central
projection (take `φ = λ·h_z`), so nothing is special about `z = 1`.

**Where the solution goes wrong**: it obtains `ϑ₁ : z𝒜 → 𝒞` and
`ϑ₂ : 𝒞 → z𝒜` from the two universal properties, shows `ϑ₁ϑ₂ = id` and
`ϑ₂ϑ₁ = id`, and then says "`ϑ₁` is an ncp-isomorphism and consequently an
nmiu-isomorphism by `iso`".  But proc.tex **100IX** `iso` is stated for
**ncpsu**-isomorphisms, and its proof opens with `f⁻¹(1) ≤ 1`, hence
`1 = f(f⁻¹(1)) ≤ f(1) ≤ 1` — precisely the step that fails for `λ·id`.  The
universal properties as printed deliver only an *ncp*-isomorphism.

**This is the same defect as B11**, one point earlier in the same
development: there the mediating map of `IsFilterFor` (**169VIII**) had to be
made subunital, and the author ruled on 2026-08-16 that it should be.  The
identical edit does **not** suffice here, though.  For filters the hypothesis
`f(1) ≤ b ≤ 1` already forces the quantified `f` to be subunital, so only
`f'` needed changing; for corners the hypothesis is `f(a) = f(1)`, which
constrains nothing.  Requiring only `f'` subunital while `f` ranges over all
ncp-maps would make even the standard corner `h_z` fail its own universal
property (`f = 2·h_z` gives `f'(1) = 2·1 ≰ 1`).

*Decision needed*: restrict **both** the quantified `f` and the mediating
`f'` in 169II to ncpsu-maps — i.e. read the universal property in `W*_cpsu`,
which is where `iso` lives and where corners are quotients — or state the
converse of 170IV only for corners that are additionally unital.  We have
left `surjective_nmiu_2` `sorry`ed and the definition unchanged.  Note that
the first half, `surjective_nmiu_1`, is **true and proved** as it stands, and
that changing `IsCornerFor` will require its existence clause to be
re-checked (its uniqueness clause only gets easier).

### B13. Minor: our `effectus_vn_partial` does not record that `I = ℂ`

**180V** (`eff.tex:832`) says the partial maps of `vNᵒᵖ` "correspond to the
ncp-maps `f` with `f(1) ≤ 1`", and our doc comment says "its effect object
being `ℂ`" — but the statement we render,
`Nonempty (EffectusPartialStructure WStarCPSU.{u}ᵒᵖ)`, asserts only that
*some* effectus structure exists and says nothing about `I`.  As it stands it
is weaker than the text and than its own doc comment, and it is weaker than the
neighbouring `cho_thm_1`, which does pin its effect object
(`∃ s, s.effectus.I = Par.of (⊤_ C)`).

The proof given (2026-08-17) *does* build `I = ℂᵤ` (`suEffectusPartialForm`),
so strengthening the statement to
`∃ s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ, s.effectus.I = suI`
would cost a line.  **Ruling wanted**: strengthen it (statements are not
changed without one).

**Correction (session 84), because it changes what the ruling buys.**  An
earlier version of this entry said the strengthening "also matters
downstream", since the eight examples of `VNExamples.lean` need
`s.effectus.I ≅ ℂᵤ`.  They do need that — but **not one of the eight
mentions `effectus_vn_partial`**: each takes its own arbitrary
`s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ` as a hypothesis.  So
strengthening `effectus_vn_partial` would unblock **none** of them; what they
need is the *uniqueness* statement "the effect object of any
`EffectusPartialStructure` on `vN_cpsuᵒᵖ` is isomorphic to `ℂᵤ`", which is a
new lemma, not a stronger 180V.  (`I` is the only free datum in an
`EffectusPartialStructure`: the coproducts and the finPAC axioms are `Prop`s,
`homPCM` is unique by `effectusPartialStructure_homPCM_unique`, `orth` is
pinned by `orth_unique`, and `one X` is the `≼`-greatest predicate.)  The
ruling asked for above is therefore purely about **faithfulness of our 180V
to the text**, with no downstream consequence — which is the right ground on
which to decide it.  A route to the uniqueness lemma is recorded in
`docs/BEff-survey.md`.

### B14. 179III.2 `effectModule_unitInterval_representation` — **our** statement is weaker than the cited Gudder–Pulmannová theorem, and weaker than its own sibling

*(Split out of A3, session 84, where it had been a one-line footnote.  The
parking question — "is it right to leave a cited-only result unproved?" —
stays in A3; this entry is about the separate defect that the statement we
parked is not the statement that was cited.)*

**What the source claims** (`eff.tex:737`, Examples 179III.2): "If `V` is an
**ordered real vector space with order unit** `u`, then `[0,u]` is an effect
module over `[0,1]`.  In fact, every effect module over `[0,1]` is of this
form \[gudder1998representation\]."

**What we state** (`EffectAlgebras.lean:3338`): for every effect module `E`
over `[0,1]` there are `V` with `[AddCommGroup V] [Module ℝ V]
[PartialOrder V] [IsOrderedAddMonoid V]`, a `u : V` with `0 ≤ u`, and a
bijection `f : E → Set.Icc 0 u` preserving `⋁` and `•`.

**The gap, in two parts.**

1. *No scalar compatibility.*  `IsOrderedAddMonoid V` says only that `+` is
   monotone; an **ordered real vector space** also has its positive cone
   closed under nonnegative scalars.  This is not pedantry: the *converse*
   half of the very same Examples point, `orderIntervalEffectModule`, could
   not be proved until `[PosSMulMono ℝ V] [SMulPosMono ℝ V]` were added to it
   (HANDOFF, "Open decisions", item 1, resolved).  So the two halves of one
   Examples point currently use two different meanings of "ordered real
   vector space", and only one of them is the source's.
2. *`0 ≤ u` is not "order unit".*  The source requires `u` to be an order
   unit — every `v : V` satisfies `v ≤ n • u` for some `n : ℕ` — which is what
   makes `[0,u]` generate `V` and is the whole content of a *representation*
   theorem.  We ask only that `u` be positive.

**Consequence**: as written, 179III.2 could be discharged without proving
Gudder–Pulmannová, because the `V` it is allowed to produce need not be an
ordered vector space in the source's sense and `u` need not be an order unit.
A closed `sorry` here would therefore be worth nothing, which is why it must
not be attacked before the ruling.

**Ruling wanted**: strengthen the statement (add the two `SMul` monotonicity
hypotheses to the produced `V`, and replace `0 ≤ u` by an order-unit
condition — no `OrderUnit` predicate exists in the file yet, so this is a real
addition), or drop 179III.2 as out of scope.  Statements are not changed
without a ruling.

### B15. 206II.4 / 211IV — is the ⋄-self-adjoint square root of a ⋄-positive map required to be **pure**?  (eff.tex vs proc.tex 103I)
`eff.tex` parsec 2060 point 40 (`diamond-basics`), and parsec 2110 point 40
(`vn-is-andthen-eff`).

The two theses define ⋄-positivity differently, and 211IV's proof depends on
the difference.

* **proc.tex 103I** (parsec 1030): `f` is **⋄-self-adjoint** if it is *pure*
  and contraposed to itself; `f` is **⋄-positive** if `f = gg` for a
  ⋄-self-adjoint `g`.  So the square root is pure, and `f` is pure with it.
* **eff.tex 206II**: an endomap is ⋄-self-adjoint if `f^⋄ = f_⋄` — *no*
  purity; and 206II.4 reads "a **pure** endomap `f` is ⋄-positive if
  `f = g ∘ g` for some ⋄-self-adjoint `g`".  The word "pure" on `f` is there
  precisely because `g` is not asked to be pure (under proc.tex's definition
  it would be redundant).

So the effectus notion is **formally weaker**: the class of ⋄-positive maps it
describes is a priori larger.  211II.1 asks for a *unique* ⋄-positive
`asrt_p` with `1 ∘ asrt_p = p`, i.e. uniqueness in the **larger** class, and
211IV proves it by citing **105V** `positive-map-uniqueness`, which is
uniqueness in the **smaller** one.  The citation therefore leaves a step.

The step is not cosmetic.  A ⋄-self-adjoint square root that is allowed to be
impure would break uniqueness outright: for self-adjoint but **not** positive
`b` in a von Neumann algebra, `ad_b : x ↦ bxb` is pure and contraposed to
itself (103II.1) with `ad_b(1) = b²`, yet `ad_b ≠ ad_{|b|} = √(b²)(·)√(b²)`.
What has to be shown is that no ⋄-self-adjoint `g` with `gg = ad_b` exists.
For `𝒜 = M₂` and `b` invertible this can be checked by hand (`gg` is then an
order automorphism, so `g` is `ad_c` or `ad_c ∘ transpose` by Kadison;
contraposition to itself forces `c* = μc` resp. `cᵀ = μc`, and either way
`b` comes out positive up to sign), but we have found no general argument and
neither thesis gives one.

**Ruling wanted**, one of:

1. *206II.4 does intend `g` to be pure* (so that eff.tex's ⋄-self-adjoint
   silently means proc.tex's, and "pure endomap `f`" in 206II.4 is
   redundant) — then 211IV.1 follows from 105V verbatim, and the fix is to
   the wording of 206II;
2. *206II.4 is as printed*, and 211IV needs an extra step, namely: in
   `vNᵒᵖ`, a ⋄-self-adjoint `g` whose square `gg` is pure has a **pure**
   ⋄-self-adjoint square root with the same square.  Is there a proof?

**Formalization status** (session 92): everything else in 211IV is proved and
axiom-clean in `Theses/B/Eff/VNExamples.lean`.  Axiom 2 of 211II is
`su_quot_after_compr_pure` (via 100III `pure-fundamental`, exactly as
eff.tex:4862 says); axiom 1's existence half is `su_exists_asrt`; its
uniqueness half is `su_asrt_unique_of_pure_sqrt`, which is 105V reached
through the two dictionary lemmas `su_procPure_of_isPure` (effectus purity ⟹
100I purity) and `su_contraposed_of_diamondSelfAdjoint` (effectus
⋄-self-adjointness ⟹ 101VI contraposition).  `vn_is_andthen_eff` is
`su_andThenEffectus_of_pure_sqrt` applied to the one hypothesis above, and
that hypothesis is the file's only `sorry`.  Under ruling (1) the `sorry`
disappears immediately.

⚠️ **Audit update (2026-08-20): what the tree actually implements is now
established, and it is reading (2).**  The statement/proof audit compared both
definitions in `Theses/B/Eff/DiamondAmp.lean` clause by clause with eff.tex,
and they take its **printed form verbatim**:

* `DiamondSelfAdjoint f := diaPull f = diaPush f` — **no purity on `f`**;
* `DiamondPositive f := IsPure f ∧ ∃ g, DiamondSelfAdjoint g ∧ f = g ≫ g` —
  purity sits on **`f`**, and **none is required of the square root `g`**.

So under reading (2) the missing step is exactly the single `sorry` in
`VNExamples.lean`: *a ⋄-self-adjoint `g` whose square is pure has a **pure**
⋄-self-adjoint square root with the same square.*  Under reading (1) — that
206II.2 silently means "pure" — both definitions gain an `IsPure` conjunct and
**that `sorry` closes with no further mathematics**.  Nothing else in the tree
depends on which way this goes; `Effectus.lean`'s partial-form machinery was
checked field by field against 180VII and is faithful either way.

### B16. 191II's "equivalent to a subcategory of `EMod_M^op`" does not follow from faithfulness of `Pred` — a gap in the printed argument
`eff.tex` parsec 1910, point 20 (`emod-effectus`, the Theorem) and point 70
(its *Representation* step, which is where the claim is discharged);
rendered as `emod_effectus_representation` in
`Theses/B/Eff/StatesPredicates.lean`.

**What the source claims.**  The Theorem's second sentence: "In fact: every
effectus `C` in total form with scalars `M` and separating predicates is
equivalent to a subcategory of `EMod_M^op`."  191VII establishes exactly one
thing — `Pred f = Pred g` iff `p ∘ f = p ∘ g` for every `p ∈ Pred Y`, so that
"the functor `Pred : C → EMod_M^op` is faithful if and only if `C` has
separating predicates" — and then closes in a single sentence: "So if `C` has
separating predicates, `C` is equivalent to the subcategory `Pred C` of
`EMod_M^op`."

**That inference is invalid.**  A faithful functor does not exhibit its domain
as equivalent to a subcategory of its codomain.  Take `C` the discrete
two-object category and `D = 1` the terminal category: the unique functor
`C → D` is faithful (each hom-set of `C` is a singleton or empty, so no two
arrows are identified), the only subcategories of `1` are `∅` and `1` itself,
and `C` — which has two isomorphism classes — is equivalent to neither.  Nor
is it enough to add that `Pred` is *full onto its image*: in that same example
the functor onto the image subcategory is full **and** surjective on objects,
and the equivalence still fails.  What faithfulness does not control is
object identification, and that is exactly what breaks.

**What would repair it**, in decreasing strength:

1. `Pred` **full** as well as faithful.  Then `C` is equivalent to the *full*
   subcategory of `EMod_M^op` on the objects `Pred X`, which is the standard
   "fully faithful functors are embeddings" statement, and "subcategory" can
   be read as "full subcategory".  Fullness is a substantial claim — for
   `C = vN_cpsuᵒᵖ` it says that every `M`-effect-module map
   `Pred 𝒜 → Pred ℬ` is `p ↦ p ∘ f` for some ncpsu-map `f` — and neither
   `eff.tex` nor `bsols.tex` proves or even asserts it.
2. `Pred` faithful **and injective on objects**.  Then `C` is *isomorphic* to
   the (non-full) subcategory `Pred C`, which is the older sense in which a
   faithful functor "is" a subcategory inclusion.  Also not claimed.
3. Conclude only that `Pred` is faithful, i.e. that `C` is concrete over
   `EMod_M^op`.  That is precisely what the printed proof delivers, and the
   Theorem's second sentence would have to be weakened to say so.

**What we have.**  `emod_effectus_representation` is reading 3, and is
**proved**: it produces `F : Tot C ⥤ (EMod_{Scal C})^op` with object part
`Pred X`, morphism part pinned to `p ↦ p ∘ f` (the pinning was the B6 defect,
repaired in session 94), and `F.Faithful`.  The subcategory clause is stated
nowhere in the tree.

*Decision needed*: how "equivalent to a subcategory" is to be read.  Under 3
there is nothing to do in Lean and the repair is one sentence of `eff.tex`.
Under 1 or 2 the printed proof needs a genuinely new step (fullness, resp.
injectivity on objects), and only then could the clause be added to
`emod_effectus_representation` — the Lean cost is then the cost of that new
step, not of the packaging.  No `sorry` turns on this; what turns on it is
whether the Theorem's second sentence is provable as printed.

(Unrelated, and *not* a question for the authors: the Theorem's **headline**
— "with scalars `M` and separating predicates" — is also unasserted by our
`emod_effectus`, but that is a missing tool for computing `Pred` and `Scal`
of `Par C`, recorded on the declaration itself, not a defect in the source.)

### B8. Minor: `bsols.tex`'s `onb1` solution over-assumes
Its solution assumes self-duality, which neither the exercise nor our statement
requires.  Harmless; noted for tidiness.

---

## Thesis A (`cstar.tex`, `vn.tex`, `proc.tex`) — remaining after the 2026-08-13 rulings

### A1. 98VI's hint points the wrong way
`proc.tex:631`.  The hint says to show `⌈τ⌉ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉^⊥`.  That is a
restatement of `τ(π(r^⊥)) = 0` and is the direction one does **not** need; the
proof requires the **converse**, `⌈τ⌉^⊥ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉`.  In the concrete model
both hold (the two sides are equal), so nothing downstream is wrong — but only
the converse is usable.

⚠️ **Update (session 48): 98VI is now proved, and it needs neither the hint nor
its converse**, so this is a question about the *hint* only.  The exercise is
short if one takes the corner's effect to be `s := β'(r)` rather than the
carrier `⌈τ∘π⌉` — see the 98VI row of ERRATA.md for the four-line argument.
The decision left is whether to replace the hint by that route or to keep the
carrier route with the inequality turned round.

### A8. 30X `proto-gelfand-naimark` — **our** statement of clause (1) drops `ϱ_Ω`, and with it half of the equivalence
`cstar.tex` parsec 300, point 100.  The thesis states a three-way equivalence
for a collection `Ω` of p-maps: (1) `ϱ_Ω : 𝒜 → B(ℋ_Ω)` is **injective**;
(2) `Ω` is centre separating; (3) `Ω'` is order separating — plus the closing
claim that `ϱ_Ω(𝒜)` is a C\*-subalgebra and `ϱ_Ω` an miu-isomorphism onto it.

We have (2) ⇔ (3) in full (`proto_gelfand_naimark_1`, **proved**).  But our
`proto_gelfand_naimark_2` renders (2) ⇒ (1) as

    ∃ H (Hilbert) (ρ : 𝒜 →⋆ₐ[ℂ] B H), Function.Injective ρ

which mentions neither `Ω` nor `ϱ_Ω`.  Two consequences, both real:

1. **The converse (1) ⇒ (2) becomes unstatable.**  In the existential form
   clause (1) no longer depends on `Ω` at all, so it cannot imply anything
   about `Ω`.  Only half of the equivalence is captured.
2. **It collapses 30X.2 into 30XIV.**  As stated, our (2) ⇒ (1) says exactly
   "every C\*-algebra admitting a centre separating family of p-maps has an
   injective representation" — i.e. the Gelfand–Naimark theorem itself, which
   is 30XIV four points later.  So 30X.2 is not a *step towards* 30XIV in our
   formalization; it *is* 30XIV.

**Both are now proved** (2026-08-17), and `ϱ_Ω` *does* now exist in Lean:
`dsumRep` in `Theses/A/CStar/Representation.lean` is the thesis's
`ϱ_Ω : 𝒜 → B(⊕_{ω∈Ω} ℋ_ω)`, the diagonal operator on `lp (fun ω => ω.GNS) 2`,
built there because Mathlib has the single-`ω` GNS representation and the
Hilbert direct sum but not the diagonal operator.  So the obstacle to stating
30X faithfully is gone.

*Decision needed*: whether to **restate 30X** as the thesis's genuine three-way
equivalence, with clause (1) reading `Function.Injective (dsumRep …)`, and to
add the closing claim that `ϱ_Ω` restricts to an miu-isomorphism onto its image
(the proved `injective_miu_iso_on_image` supplies it immediately).  We have not
done this because it changes a statement.  Nothing downstream is affected: no
declaration in `Theses/` uses `proto_gelfand_naimark_2` (the three existing
uses in `A/VN` are all of `proto_gelfand_naimark_`**`1`**).

### A9. 51IX `Linfty-vn` — our rendering of "`q` is a miu-map" omits `ℂ`-homogeneity, exactly as `IsLinftyOf` did before D1

**DISP** 51IX (`Linfty-vn`, vn.tex:1620), rendered as `Linfty_vn` in
`Theses/A/VN/Basic.lean`.

Our statement asks for `q : 𝓛^∞(X) → 𝒜` with

* `q (f + g) = q f + q g`, `q (f · g) = q f · q g`, `q (star f) = star (q f)`,
* `q 1 = 1`, `q f = 0 ↔ f =ᵐ[μ] 0`, and `q` surjective,

and the surrounding comment calls this "`q` is a surjective miu-map on
`𝓛^∞(X)`".  It is not: a miu-map is `ℂ`-**linear**, and the listed clauses
make `q` only a ∗-*ring* homomorphism.  Complex conjugation `ℂ → ℂ` satisfies
every one of them and is not `ℂ`-linear.

This is the same defect that was found in `A/Proc/Duplicators.lean`'s
`IsLinftyOf` and repaired on 2026-08-16 under **QUESTIONS D1** (ruled by Bas)
by adding the field `smul : q (z • f) = z • q f`.  `IsLinftyOf` is otherwise
field-for-field our 51IX, so the two renderings should agree.

**Question.** May the clause `∀ (z : ℂ) f, IsBoundedMeasurable X f →
q (z • f) = z • q f` be added to `Linfty_vn`?  It strengthens a statement,
which needs a ruling.

**Update (2026-08-17, session 80).**  51IX is now **proved**, with the
statement exactly as it stands, and the omission **did not obstruct the
proof**: the `q` that is constructed is `f ↦ (MemLp.toLp f)`, which is
`ℂ`-linear, so the clause above is true of it and would cost one further
`rep_injective` + `filter_upwards` line.  Adding it therefore requires no
reproving at all — only the ruling.


**Update (2026-08-21, repair wave 3): confirmed free a second time, and the
omission has since started to cost something.**  The `A/VN` repair pass
re-checked the point independently and reports exactly the session-80 finding
— the constructed `q = (f ↦ MemLp.toLp f)` *is* `ℂ`-linear, so the clause is
one line and no reproving — and left the row unrepaired only for want of this
ruling.  (It also observed, incidentally, that the completeness hypothesis
`hμ` is never used by the proof.)

What is new is a **downstream** consequence, which A9 previously had none of.
When 129X `continuous_finite_measure_space_not_duplicable` was put back on the
thesis's own integral state, the state had to be transported from
`Linfty_vn`'s presentation `p : 𝓛^∞(X) → 𝒞` onto an arbitrary `IsLinftyOf`
presentation `q : 𝓛^∞(X) → 𝒜` along the comparison map `Ψ : q f ↦ p f`
(`exists_integralNP`, `Theses/A/Proc/Duplicators.lean`).  Because `Linfty_vn`
carries no `smul` clause while `IsLinftyOf` does, `Ψ` could only be built as a
bijective ∗-**ring** map, and its **normality had to come from its being an
order isomorphism** (`0 ≤ x` iff `x = c*c`, which needs no linearity), with
`ℂ`-linearity of the resulting `ω` recovered afterwards from the integral
formula.  Granting the clause would make `Ψ` a ∗-algebra isomorphism outright
and let that detour go.

For the record: the sibling defect **D1** is absent from this file because it
was ruled and implemented — `IsLinftyOf` has carried
`smul : q (z • f) = z • q f` since 2026-08-16 — so A9 is the **only**
surviving instance of the gap, and it is in `Linfty_vn`, not in the
presentation `Prop`.

### A10. 28II.4 `functional-calculus` — **our** statement drops the identification of the unique element with `f(a)`

**28II**.4 (`functional-calculus`, cstar.tex:4299 — the exercise's part 4),
rendered as `functional_calculus_4` in `Theses/A/CStar/Representation.lean`.

The exercise asks: *given `f ∈ C(spec(a))`, show that `f(a)` is the unique
element of `C*(a)` with `φ(f(a)) = f(φ(a))` for all `φ ∈ spec(C*(a))`.*  Two
clauses are being asserted at once: (i) the character condition **pins down**
at most one element of `C*(a)`, and (ii) the element it pins down **is** `f(a)`
— the `Φ(f)` defined in part 3, i.e. Mathlib's `cfc f a`.

Our statement is

    ∃! b : StarAlgebra.elemental ℂ a,
      ∀ φ : characterSpace ℂ (StarAlgebra.elemental ℂ a), φ b = f (φ a)

which is clause (i) alone, plus the (weaker) assertion that *some* element has
the property.  The name `f(a)` never occurs, so the statement never says which
element it is — and that identification is the entire usable content of the
exercise: it is what lets one compute with `f(a)` through characters, and it is
what the four later parts (spectral mapping, naturality, composition) are
implicitly built on.  As it stands our part 4 is a fact about the character
space of `C*(a)`, not a characterisation of the functional calculus.

**Question.** May the statement be strengthened to the thesis's, i.e. to

    ∀ b : StarAlgebra.elemental ℂ a,
      (∀ φ, φ b = f (φ a)) ↔ (b : 𝒜) = cfc f a

(or, minimally, may the conjunct `(∀ φ, φ (cfc f a) = f (φ a))` be added)?
Strengthening a statement needs a ruling.

**Cost of the repair: near zero, and the missing half is already checked.**
`functional_calculus_4` is now **proved** as it stands (2026-08-18, session 92),
by the thesis's own route: the unique element is exhibited as
`(gelfandStarTransform (C*(a))).symm (f ∘ j)`, where `j : φ ↦ φ(a)` is part 3's
map `spec(C*(a)) → spec(a)` (Mathlib's `elemental.characterSpaceToSpectrum`).
Mathlib's `cfc f a` is *defined* by that same formula: `continuousFunctionalCalculus a`
is `((characterSpaceHomeo a).compStarAlgEquiv' ℂ ℂ).trans (gelfandStarTransform _).symm`,
with `f ∘ j` written as the restriction of `f` transported along the
homeomorphism `characterSpaceHomeo a : spec(C*(a)) ≃ₜ spec(a)`.  So the missing
clause needs no new mathematics.  It has been **compiled in the scratchpad** (14
lines, no `sorry`, not committed because it changes a statement):

    example (a : 𝒜) [ha : IsStarNormal a] (f : ℂ → ℂ)
        (hf : ContinuousOn f (spectrum ℂ a))
        (φ : characterSpace ℂ (StarAlgebra.elemental ℂ a)) :
        φ ⟨cfc f a, cfc_mem_elemental f a⟩ = f (φ ⟨a, StarAlgebra.elemental.self_mem ℂ a⟩) := by
      have heq : (⟨cfc f a, cfc_mem_elemental f a⟩ : StarAlgebra.elemental ℂ a)
          = continuousFunctionalCalculus a ⟨_, hf.domRestrict⟩ := by
        refine Subtype.ext ?_
        show cfc f a = ((continuousFunctionalCalculus a ⟨_, hf.domRestrict⟩ :
          StarAlgebra.elemental ℂ a) : 𝒜)
        rw [cfc_apply f a ha hf, cfcHom_eq_of_isStarNormal]; rfl
      rw [heq]
      show gelfandStarTransform (StarAlgebra.elemental ℂ a)
          (continuousFunctionalCalculus a ⟨_, hf.domRestrict⟩) φ = _
      rw [continuousFunctionalCalculus, StarAlgEquiv.trans_apply,
        StarAlgEquiv.apply_symm_apply]
      rfl

With this in hand the iff form is immediate from the uniqueness half already
proved.  So the ruling is the whole cost.

Nothing downstream is affected: no declaration in `Theses/` uses
`functional_calculus_4`.

### A11. 132III.4 cannot be stated as an **equality** of categories at all — and `W*_miu` is still not a `MonoidalCategory` in the tree
`proc.tex` parsec 1320, point 30 (`prop:dup-vna-is-monoid`, Exercise), item 4;
rendered as `dup_vna_is_monoid_4` in `Theses/A/Proc/Duplicators.lean`.

**What the point says.**  "Conclude that
`CMon(W*_miu) = Mon(W*_miu) = CMon(W*_cpsu) = Mon(W*_cpsu)`."

**What we state.**  `dup_vna_is_monoid_4` (proved): every monoid `M` in
`W*_cpsu` is commutative (`m ∘ γ = m`) and its multiplication is an nmiu-map.
Together with item 1 (`dup_vna_is_monoid_1`: a monoid in `W*_cpsu` is a
duplicator) and item 3 (`dup_vna_is_monoid_3`: the monoid morphisms in either
category are exactly the nmiu-maps) that is the whole *content* of item 4.
The four-fold equality itself is not stated, and cannot be, for two
independent reasons.

**1. The shape — this is the part that needs a ruling.**  Mathlib renders the
two constructions as *distinct structure types*:
`CategoryTheory.Mon C` is `⟨X : C, [mon : MonObj X]⟩` and
`CategoryTheory.CommMon C` is `⟨X : C, [mon : MonObj X], [comm : IsCommMonObj X]⟩`
(with `CommMon` additionally requiring a `BraidedCategory` instance).  They
are not the same type, so `CMon(W*_miu) = Mon(W*_miu)` is not expressible as
an equality there at all.  The strongest available reading is an
**equivalence** (or an isomorphism) of categories — `CommMon.toMon` is fully
faithful and would be essentially surjective here — which is a change of
statement, hence the ruling.  The same applies to the two cross-category
equalities `Mon(W*_miu) = Mon(W*_cpsu)`: the two categories have different
ambient hom-sets (nmiu-maps vs ncpsu-maps), so what item 3 gives is again an
isomorphism-onto-the-image, not an equality.

**2. The infrastructure — much smaller than it was, but not gone.**  Forming
`Mon(-)` and `CMon(-)` needs `MonoidalCategory` (and `BraidedCategory`)
instances on `W*_miu` and `W*_cpsu`.  **The mathematics for the `W*_miu` one
now exists**: repair wave 3 stated 119V `vn-smc` concretely and in full in
`Theses/A/Proc/Tensor.lean` — `vn_smc_pentagon`, `vn_smc_triangle`,
`vn_smc_unitors_agree`, `vn_smc_hexagon`, `vn_smc_symmetry` and the four
naturality lemmas, all proved, with `exists_braiding` (119IVc) no longer
`sorry`.  What is missing is the *packaging*: a tensor bifunctor on the
category `WMIU` (`Theses/A/Proc/QuantumLambda.lean`), associators and unitors
as natural isomorphisms of that category, and the coherences restated in
Mathlib's bundled form.  That is plumbing over proved equations, not new
mathematics.  (⚠ The doc comment on `dup_vna_is_monoid_4` still says the
coherences are "none of which the tree has"; wave 3 overtook it.)

For `W*_cpsu` there is a further, purely organisational obstacle: `A/Proc`
has no category of von Neumann algebras and ncpsu-maps.  The one that exists,
`WStarCPSU`, is in `Theses/B/Eff/WStarCat.lean` and belongs to thesis B, so
`A/Proc` cannot import it (the same reason `WMIU` was built separately from
`WStar`, recorded at `QuantumLambda.lean`'s `Categorical` section).

*Decision needed*: whether "=" in 132III.4 may be rendered as an equivalence
of categories (and, in the cross-category cases, as a fully faithful
essentially surjective comparison functor), or whether the point should be
reworded — the natural rewording being "a monoid in either category is
automatically commutative, its multiplication is the algebra's own, and its
morphisms are the nmiu-maps", which is what we already prove.

*What the ruling buys*: no `sorry` closes either way — it decides whether two
clauses ever acquire statements.  Besides 132III.4 itself, **132III.5's first
half** `Mon(W*_miu) ≅ dW*_miu` is blocked on exactly the same
`MonoidalCategory` instance; its second half `dW*_miu ≃ Set^op` is proved
(`dupEquivSetOp`).  If the ruling is "leave it", both should be recorded as
deliberately unstated rather than as open work.

### A12. 101VII.1's middle clause is under-hypothesised as printed — the second map need not exist
`proc.tex` parsec 1010, point 70 (`equivalent-examples`, Examples), part 1,
middle paragraph; rendered as `equivalent_examples_1_corners` in
`Theses/A/Proc/Measurement.lean`.

**What the point says.**  "If `p` and `q` are projections of `𝒜` with
`a*pa ≤ q` (as in `ad-ncp`), then the maps `a*(·)a : p𝒜p → q𝒜q` and
`a(·)a* : q𝒜q → p𝒜p` are contraposed."

**The hypothesis governs only the first map.**  `a*pa ≤ q` is exactly the
hypothesis of **94III** `ad-ncp` (parsec 940, point 30), and it is what puts
`a*(·)a` inside `q𝒜q`: for `b ∈ p𝒜p` positive, `b ≤ ‖b‖p` gives
`a*ba ≤ ‖b‖·a*pa ≤ ‖b‖q`.  It says nothing about `a(·)a*`, and without a
hypothesis that map need not exist.  Take `p = 0`, `q = 1`, `a = 1`: then
`a*pa = 0 ≤ 1 = q`, so the printed hypothesis holds, while `a(·)a*` is the
identity of `𝒜` and `p𝒜p = {0}`.  The hypothesis that does the mirrored job
is `aqa* ≤ p`, i.e. 94III read with `(p, a)` and `(q, a*)` exchanged.

**Nothing in the tree is wrong.**  `equivalent_examples_1_corners` takes both
maps as *given* ncp-maps `f : p𝒜p → q𝒜q` and `g : q𝒜q → p𝒜p` with
`(f b).val = a* b a` and `(g b).val = a b a*`, and proves them contraposed;
assuming the maps assumes neither `a*pa ≤ q` nor its mirror, so the statement
is true and proved, and its doc comment records why it is phrased that way.
Both places where the thesis uses the clause supply the mirror anyway:
94III's `adNCP` is the first map, and the "in particular" `π_s`/`c_s` pair is
`p = 1`, `q = s`, `a = s`, where `aqa* = s ≤ 1 = p`.

*Decision needed*: whether 101VII.1 gains the hypothesis `aqa* ≤ p` — an
erratum, since as printed the sentence names a map that need not exist — or
whether the middle clause is to be read as being about two maps whose
existence is presupposed, which is what we implement.  94III itself is
correct as it stands and is used one-sidedly elsewhere, so it needs no
change; only the mirrored *instance* of it is what the middle clause is
missing.

*What the ruling buys*: no `sorry`, but under the first reading we would
restate `equivalent_examples_1_corners` with the two maps **constructed**
from 94III and its mirror rather than assumed, which is strictly closer to
the text and costs only plumbing — the proof is untouched, since both sides
of the contraposition already reduce to `x a t = 0`.

### A13. 34V.3 in the module setting — which `𝒜`-valued inner-product convention is the cp condition stated in?
`cstar.tex` parsec 340, point 50 (`ad-cp`, Exercise), part 3; rendered — in
the Hilbert-*space* case only — as `ad_cp_3` in
`Theses/A/CStar/Matrices.lean`.

**What the point says.**  For every element `x` of a Hilbert `𝒜`-module `X`,
the vector functional `T ↦ ⟨x, Tx⟩ : ℬᵃ(X) → 𝒜` is completely positive.
(Part 2 is the companion `T ↦ S*TS : ℬᵃ(X) → ℬᵃ(Y)` for adjointable
`S : Y → X`.)

**What we state.**  `ad_cp_3` is the case `𝒜 = ℂ`, `X = ℋ`: the vector
functional `B(ℋ) → ℂ`.  Likewise `ad_cp_2`/`conjOperator` state only the
Hilbert-space case of part 2.  All three doc comments say so, and the audit
flagged all three rows as weaker.

**Two obstructions; only the second needs a ruling.**

1. *Infrastructure* (no ruling needed).  `ℬᵃ(X)` exists in the tree only as
   the private `Bax 𝒜 X`, a subalgebra of `X →L[ℂ] X`, with **no cross-module
   hom-sets**: `S*TS` for `S : Y → X` needs adjoints of maps between
   *different* modules and a `star` that swaps hom-sets, neither of which is
   there.
2. *Convention* — the author's call.  **32I** `chilb-basic` (parsec 320,
   point 10) defines an `𝒜`-valued inner product so that `⟨x, ·⟩` is a
   **module map**: `X` is a right `𝒜`-module and the scalar acts on the right
   of the second argument, `⟨x, y·a⟩ = ⟨x,y⟩·a`.  Mathlib's `CStarModule`
   axiom is the mirror image, `⟪x, a • y⟫ = a * ⟪x, y⟫` — concretely, on `𝒜`
   viewed over itself Mathlib takes `⟪x,y⟫ = y·x*` where 32I gives `x*·y`.
   Under Mathlib's convention the `ℂ`-linear vector functional
   `T ↦ inner 𝒜 x (T x)` **fails** our `IsCompletelyPositiveMap`
   (`Theses/A/CStar/Basic.lean`), which asks
   `0 ≤ ∑ᵢⱼ bᵢ* f(aᵢ*aⱼ) bⱼ`: writing `yᵢ := Tᵢ x`, the expression the module
   makes positive is
   `⟪∑ᵢ bᵢ•yᵢ, ∑ⱼ bⱼ•yⱼ⟫ = ∑ᵢⱼ bⱼ·⟪yᵢ,yⱼ⟫·bᵢ*` — the `b`'s on the *other*
   sides from the ones the cp condition wants.  The form that does satisfy
   the cp condition is `T ↦ ⟪Tx, x⟫` (then
   `∑ᵢⱼ bᵢ*·⟪yⱼ,yᵢ⟫·bⱼ = ⟪∑ⱼ bⱼ*•yⱼ, ∑ᵢ bᵢ*•yᵢ⟫ ≥ 0`), and *that* map is
   **conjugate-linear in `T`**, hence not a `𝒜 →ₗ[ℂ] ℬ` and not eligible for
   `IsCompletelyPositiveMap` at all.

*Decision needed*: which `𝒜`-valued convention the module-valued statements
of the tree are phrased in.

* **(a) Keep Mathlib's.**  Every Hilbert-module file already rests on
  `CStarModule` — `B/Dils/{HilbertModules, SelfDual, SelfDualCompletion,
  Paschke, Kaplansky}` and `A/CStar/{Matrices, TowardsVN}`, some 800 lines
  mentioning it — so this is the cheap option.  The cost is that 34V.3 will
  not read like the printed formula (the thesis's `⟨x, Tx⟩` becomes
  Mathlib's `⟪Tx, x⟫`), and that the `𝒜`-valued cp condition wants a mirrored
  companion to `IsCompletelyPositiveMap` (`∑ᵢⱼ bᵢ·f(aᵢaⱼ*)·bⱼ*`), which is a
  new definition and so needs the ruling on its own account.
* **(b) Introduce the thesis's convention** alongside Mathlib's, so that
  34V.3 is transcribed verbatim.  This forfeits Mathlib's Hilbert-module API
  (Cauchy–Schwarz, the induced norm, the constructions) for anything stated
  in it, and would put two inner products on the same objects.
* **(c) Status quo**: leave 34V.2/.3 in the Hilbert-space case, with the doc
  comments recording the divergence, and mark the module versions as
  deliberately unstated.

*What the ruling buys*: no `sorry` closes either way, and nothing in the tree
is currently wrong — the Hilbert-space cases we state are correct and proved.
What it settles is the shape of 34V.2/.3 in the module setting and of every
future `𝒜`-valued statement; the neighbouring module rows (32IV.2
`paschke_inclusion_no_adjoint`, and 161II in `B/Dils`) are waiting on the
sub-Hilbert-module infrastructure and would be written in whichever
convention is chosen.

### A2. `parsec-340.60` (34VI.1) is an empty `\TODO{}`
The solution slot exists but is empty, and it is the *last* entry in
`asols.tex` — which is why solution coverage appears to stop at parsec 340.
Our `cstar_product_4` is proved, but from Mathlib rather than the author's
argument, so it is **not cross-checked**.

### A3. Statements the theses only *cite*, never prove
These have no proof to transcribe, so we have parked rather than proved them.
Confirm that is the right treatment:

* **179III.2** Gudder–Pulmannová representation (`eff.tex:739`, cited to
  `gudder1998representation`).  Still parked — but note our statement is *also*
  weaker than the cited result, which is a separate defect and now has its own
  entry, **B14** above.  Confirming the parking here does **not** settle B14.
* ~~**178III.2**~~ "every finite effect monoid comes from a Boolean algebra,
  hence is commutative" and **178III.4** "there is a non-commutative effect
  monoid on lexicographic `ℝ⁵`" (`eff.tex:640`/`651`, cited to `basmsc`
  prop. 40 / cor. 51) — **no longer parked: all three are proved.**
  `finite_effectMonoid_commutative` and `exists_noncommutative_effectMonoid`
  were proved on 2026-08-17 by routes not needing the cited results, and
  **`finite_effectMonoid_boolean` was proved on 2026-08-18** (session 84,
  `EffectAlgebras.lean`, section `FiniteBoolean`) — again independently of
  \[basmsc, prop. 40\], which we never consulted, so this is a genuine
  independent check that the cited claim holds.  Nothing is asked of the
  authors here any more; the route is in PROVING-LOG and in the section note
  in the file.
* ~~**192V.4**~~ "every cancellative abstract `[0,1]`-convex set embeds
  affinely in a real vector space" (`eff.tex:2591`, cited to
  `statesofconvexsets` thm. 8) — **no longer parked: `cancellative_iso_convex`
  was proved on 2026-08-18** (session 85, `StatesPredicates.lean`), again
  without consulting the cited paper, so this too is an independent check that
  the cited claim holds.  Nothing is asked of the authors here any more; the
  route (the Stone–Gudder embedding, carried out inside the free vector space
  `X →₀ ℝ` rather than through a Grothendieck group) is in PROVING-LOG
  session 85 and in the section note in the file.
* ~~**`extensive_effectus`**~~ (189aII.3, `eff.tex:2043`, cites `effintro`) —
  **no longer parked: proved 2026-08-14** (worker 44) from Mathlib's
  `FinitaryExtensive`, i.e. from the van Kampen property of binary coproducts.
  Two remarks for the authors, since this is the one place where we had to
  supply mathematics the thesis does not contain:
  * The two pullback axioms are essentially immediate from extensivity, as one
    would expect.  The **third** axiom — joint monicity of
    `[κ₁,κ₂,κ₂], [κ₂,κ₁,κ₂] : 1+1+1 → 1+1` — is *not* proved anywhere in
    `eff.tex` or `bsols.tex`, and Mathlib has nothing about it either.  It is
    **true** in any finitary extensive category with a final object; the short
    argument is in PROVING-LOG session 17 and is now formalized.  It may be
    worth a sentence in the text, since the reader is otherwise left with the
    hardest of the three axioms unaddressed.
  * `effintro` is still the only citation; we did not consult it.  If it does
    contain the argument, our proof is an independent one and the entry above
    can simply be dropped.
* ~~**`effectus_vn`**~~ (`eff.tex:832`, says only "adapt the proof of
  `emod-effectus`") — **no longer parked: `effectus_vn` and
  `effectus_vn_partial` are both proved, 2026-08-17** (`VNExamples.lean`).  The
  thesis gives no proof, so the mathematics had to be supplied; it is recorded
  in PROVING-LOG.  It does follow the shape of 191II — it goes through the same
  bridge `effectusTotalForm_of_pres` — but nothing beyond the shape is shared,
  and the authors may want to know what the "adapt the proof" of 180V actually
  comes to: the two 180I pullbacks are the statements that a ncpu-map out of
  `𝒜 ⊕ ℬ` is exactly a compatible pair out of `𝒜 ⊕ ℂ` and `ℂ ⊕ ℬ`
  (glued by `γ(a,b) = β(a,0) + α(0,b)`), and that a ncpu-map out of `𝒜` is
  exactly one out of `𝒜 ⊕ ℬ` killing `0 ⊕ ℬ`; the only non-formal ingredient
  is that a positive map killing `(0,1)` kills `0 ⊕ ℬ` (because
  `b ≤ ‖b‖·1`).
* **177Ia** — see B4 above.

---

## Not for the authors — upstream Mathlib

Recorded here only so they are not re-diagnosed.

* `ContinuousFunctionalCalculus ℝ (CStarMatrix n n 𝒜) IsSelfAdjoint` and
  `NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix …)` / `NonnegSpectrumClass ℝ`
  **are not found by instance search** although they apply verbatim: the
  instance carries `Algebra.complexToReal` while `Algebra ℝ (CStarMatrix …)`
  resolves to `CStarMatrix.instAlgebra` — defeq but not syntactically equal.
  Worked around with `letI` throughout; worth filing upstream.
* **`MeasureTheory.AEEqFun` (`α →ₘ[μ] γ`) has no ring structure.**  It
  carries `AddCommGroup`, `CommMonoid`, `Module 𝕜`, `Star` and a partial
  order, but distributivity is never proved, so even
  `Semiring (X →ₘ[μ] ℂ)` fails to synthesise — and consequently there is no
  `Algebra`, no `StarRing`, and nothing downstream on `Lp E ∞ μ`.  Supplied
  locally in `A/VN/Basic.lean`'s `LinftyConstruction` block (four instances,
  ~70 lines, each axiom three lines via `AEEqFun.induction_on`); worth
  filing upstream, since it is the only thing standing between Mathlib and a
  C*-algebra `L^∞(X)`.
* Mathlib has **no double commutant theorem** (an explicit TODO in its own
  header), **no von Neumann tensor product**, no spatial tensor product, and no
  normal GNS.  Its `VonNeumannAlgebra` is the *concrete* (double-commutant)
  definition; `WStarAlgebra` is Sakai-style — neither matches the thesis's
  Kadison-style abstract definition.

---
