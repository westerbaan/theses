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

### D6. 164II.2b `ext_tensor_ketbra_dense` — **our** statement is false; the thesis's is true and is now proved
`dils.tex:5327` (**164XI**), `SelfDual.lean`.  The thesis claims only that the
linear span of

>  `D = {|(e'ᵢa) ⊗ (d'ⱼb)⟩⟨e_k ⊗ d_l|; a ∈ 𝒜, b ∈ ℬ, i,k ∈ I', j,l ∈ J'}`

is **ultraweakly dense** in `ℬᵃ(X ⊗ Y)`.  Our transcription instead demands an
approximating **net indexed by `Finset (ι × κ)` along `atTop`** (copying the
shape of **159IV** `ketbra_ultraweakly_dense`, where the thesis's own proof
*does* produce such a net, `p_S T p_S`).  That strengthening is **false**:

* take `ι = κ = PUnit`, `𝒜 = ℬ = B(ℓ²)`, `𝒞 = 𝒜 ⊗ ℬ`, `X = 𝒜`, `Y = ℬ`,
  `E = extTensorSelf` (session 52), `e = d = 1` — a legitimate orthonormal
  basis of a von Neumann algebra over itself;
* then `E.Z = 𝒞`, `f() = t 1 1 = 1`, `ℬᵃ(X ⊗ Y) ≅ 𝒞` (as right multiplications)
  and `span D ≅ 𝒜 ⊙ ℬ`, the *algebraic* tensor product;
* `Finset (PUnit × PUnit)` has a greatest element, so `atTop` is the principal
  filter there and — the ultraweak topology being Hausdorff — the net's value at
  that element must **equal** `T`.  So the statement would force
  `𝒜 ⊗ ℬ = 𝒜 ⊙ ℬ`, which fails for `B(ℓ²)`.

The counterexample cannot be written down *inside* the tree, because
`IsVNTensor` is axiomatized (proc.tex 108II is not formalized) and the only
concrete instance we have is `ℂ ⊗ ℂ = ℂ`, where the statement is true.  So the
`sorry` is left in place per the never-change-a-statement rule.

**The thesis's actual claim is now proved**, as `ext_tensor_ketbra_uwDense`
(same file, immediately below), in the entourage form "for finitely many
np-functionals and `ε > 0` there is an element of `span D` within `ε` of `T` on
all of them" — via **159IV**, **164II**.2a, Kaplansky (**74IV**) and **159IX**
(also proved this session).  That form is what **165VI**'s `generates` clause
needs, so nothing downstream is lost.

*Decision needed*: replace the net in `ext_tensor_ketbra_dense` by the
entourage form (i.e. delete the statement and keep `ext_tensor_ketbra_uwDense`
under the 164II.2b name), or keep both with the net form restricted to a
hypothesis that rules the degenerate case out.  We recommend the first.

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

### A7. 104III.3/.4/.5 — the proposed repair `⌈⌈p⌉⌉ = ⌈⌈q⌉⌉` fails for .4 and .5; and what does `p ∧ q` mean?
`proc.tex:1465`.  Bram proposed (2026-08-16) repairing the three false parts of
`centrally-similar-basic` by assuming that `p` and `q` have the same **central
carrier** `⌈⌈p⌉⌉ = ⌈⌈q⌉⌉` rather than the same carrier.  It is indeed necessary
(part 2 gives `⌈p⌉ = ⌈q⌉`) and it does exclude the printed counterexample
(`ℓ^∞({0,1})` is commutative, where `⌈⌈·⌉⌉ = ⌈·⌉`).  **It is not sufficient.**
Tested on 2026-08-16 in `A/Proc/Measurement.lean`, in the *factor* `B(ℂ²)`
where equal central carriers hold automatically:

* **.4 fails**: at `p = q = m = diag(1,0)` the pair is centrally similar
  (`c = d = 1`) while `p q^∼¹ = p` is not central
  (`centrally_similar_basic_4_cceil_counterexample`).  Since `p = q`, *any*
  reflexive hypothesis — `⌈p⌉ = ⌈q⌉` included — is satisfied, so part 4 needs a
  hypothesis excluding non-faithful `p`: the `⌈p⌉ = ⌈q⌉ = 1` that its only
  consumer **104VII** already assumes, under which the first two `iff`s are
  proved (`centrally_similar_basic_4_faithful`).
* **.5 fails**: `p = diag(1,0)`, `q = 1`, `eₙ = p`
  (`centrally_similar_basic_5_cceil_counterexample`).  Part 5 assumes no
  centrality of anything, so — unlike parts 2a and 3 — being inside a factor
  does not force faithfulness.  It needs `⌈p⌉ = ⌈q⌉`, i.e. `⋃ₙ eₙ = ⌈q⌉` as
  well as `= ⌈p⌉`; 104VII supplies this.
* **.3 survives** the test and is, we believe, true under `⌈⌈p⌉⌉ = ⌈⌈q⌉⌉` —
  but only through Kadison's **anti-lattice** theorem.  With `c = m/p` and
  `d = m/q` central one has `cp = m = dq` already; what is missing is
  `⌈p⌉ ≤ ⌈c⌉` and `⌈q⌉ ≤ ⌈d⌉`, which amount exactly to
  `⌈⌈m⌉⌉ = ⌈⌈p⌉⌉ = ⌈⌈q⌉⌉`.  That can only fail on a central block where
  `⌈p⌉ ⊥ ⌈q⌉` (note `pq/(‖p‖+‖q‖)` is a lower bound of both, so `m = 0` there
  forces `pq = 0`), and on such a block the *conclusion* fails too — so no
  argument avoids ruling the block out, and the only thing that rules it out is
  the existence of `p ∧ q`, i.e. the anti-lattice theorem.  Neither it nor the
  comparison theory it rests on is in the theses or in our tree, so `⌈p⌉ = ⌈q⌉`
  remains the repair we can actually prove from.

**Second question, and it decides .3.**  What is `p ∧ q` for positive `p, q`?
Read as the thesis's `⋀` (vn.tex:371, the infimum in the order of `𝒜`), it is
a very strong hypothesis: by the anti-lattice theorem two positive elements
have an infimum only when they are comparable relative to the centre, so
outside the commutative case the hypotheses of .3 are rarely met at all — and
`p ∧ q` in .4's third `iff` and in 104VII's construction of the `eₙ` may then
not exist.  Read instead as the meet in the commutative von Neumann algebra
generated by the commuting pair (the pointwise minimum, which for the
orthogonal projections `p = diag(1,0)`, `q = 1−p` of `B(ℂ²)` is `pq = 0`),
part 3 is **false even with `⌈⌈p⌉⌉ = ⌈⌈q⌉⌉`**
(`centrally_similar_basic_3_meet_cceil_counterexample`).  Which reading is
intended?

⚠️ **Update (session 90): the ruling is needed for less than the record said,
and for something slightly different.**  Two things were established on
2026-08-18.

1. **Nothing below 104VII needs A7 at all.**  `104VII → 104IX → 105V →
   {105VII, 106I}` is now *proved* in `A/Proc/Measurement.lean`, by
   transcribing the authors' own proofs, and `#print axioms` (against a copy
   in which 104VII's `sorry` is replaced by a named axiom) shows the four
   results depend on **104VII and on nothing else** — no `sorryAx`, so in
   particular none of the four broken parts of 104III is used.  The four
   `sorry`s at 104IX, 105V, 105VII and 106I are gone; `B/Eff`'s **211IV**
   `vn_is_andthen_eff` is thereby blocked on 104VII rather than on 105V.
   What the earlier record got wrong is the shape of the dependency: 104VII
   consumes 104III.**4** only in the *invertible* case (where
   `centrally_similar_basic_4_faithful`, already proved, applies — and in
   fact `z p = q` with `z = p⁻¹q` central is even more direct), and 104III.**5**
   only through a *corner reduction* that is not in the tree.  So the
   repaired-parts-already-proved reading is right for .4 and wrong for .5.

2. **The second question — what is `p ∧ q`? — sits *inside* 104VII's proof,
   not upstream of it.**  104VII's proof invokes 104III.5, whose only printed
   route (its hint) runs through 104III.3 and through the *third* `iff` of
   104III.4, both of which mention `p ∧ q`; and 104VII builds its `eₙ` from an
   approximate pseudoinverse of `p ∧ q`.  The latter is harmless (any
   increasing `eₙ` commuting with `p` and `q` with `⋃ₙeₙ = ⌈p⌉` and `eₙp`,
   `eₙq` pseudoinvertible will do — e.g. the spectral projections of `pq`,
   which exist because `⌈pq⌉ = ⌈p⌉ ∧ ⌈q⌉ = 1` under 104VII's faithfulness).
   The former is not: a repaired 104III.5 usable by 104VII has to be proved
   by some route that does not go through `p ∧ q`.  Separately, the proof of
   104VII has a genuine gap at the reduction step — central similarity
   obtained inside `eₙ𝒜eₙ` is not central similarity in `𝒜` without
   `Z(e𝒜e) = Z(𝒜)e`, which is in neither thesis nor tree.  See the new
   **104VIII** row of `ERRATA.md`.

3. **A partial answer on .3**, offered for the ruling but *not formalized*:
   under the faithfulness `⌈p⌉ = ⌈q⌉ = 1` that 104VII supplies, the
   anti-lattice obstruction described above disappears.  `pq/(‖p‖+‖q‖)` is a
   lower bound of both `p` and `q`, and `⌈pq⌉ = 1` (if `pqr = 0` for a
   projection `r` then `p(qr) = 0`, so `qr = 0` because `⌈p⌉ = 1`, so `r = 0`
   because `⌈q⌉ = 1`), hence `⌈m⌉ = 1` for any lower bound `m` above it — in
   particular for the infimum.  Then `m = cp` with `c` central gives
   `⌈c⌉ ≥ ⌈cp⌉ = ⌈m⌉ = 1`, which is exactly the missing carrier condition,
   and likewise for `d`.  (Caveat: this reads `m/p` as the genuine quotient,
   i.e. it assumes `m ∈ 𝒜p` and `m ∈ 𝒜q`, which our `div` does not force —
   off its domain `div` has the junk value `0`, which is central.)  So the
   ruling that would unblock the chain is the *faithful* form of .3/.5, not
   the general one.

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

### A4. 217I's independence-of-choice claim is not formalised
Our `IsDaggerOf` is stated relative to the *chosen* `π_{IM f}`, so the theorem
as transcribed does not assert that the dagger is independent of that choice —
which is what 217I is about.  Not wrong, but weaker than the source.  Low
priority; flagged so it is not mistaken for a full formalisation.

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
