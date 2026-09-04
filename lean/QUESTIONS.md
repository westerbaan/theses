# Questions for the authors

Everything in this file needs a decision from an author.  Nothing here is a
Lean problem: each item is either a defect in a thesis statement, or a choice
about how faithfully our statement should track the thesis.

Findings that need **no** decision live elsewhere: thesis defects to be
corrected are in [ERRATA.md](ERRATA.md), and our own mis-transcriptions in
[PROVING-LOG.md](PROVING-LOG.md).  Every question below is also restated, with
our recommendation and what it blocks, in the `docs/DECISIONS.md` section named
at the end of its entry.

**Everything in this file is open.**  Once a question is answered *and* the
answer is implemented, its section is **deleted** rather than marked resolved;
the ruling survives in the commit message that implemented it and in
PROVING-LOG.md.  Do not re-add a resolved item.

**Keys a reader may still meet in a commit message or a dated log**, each
removed by a commit whose message carries the ruling — that is where to read
it (`scripts/questions_check.py` carries the same list and reports any live
pointer to a key that is in neither):

| key | removed | commit |
|---|---|---|
| **B1** | 2026-08-16 | `227ce6e` — "B1 removed (was fixed); B3 was OUR misreading of 221II" |
| **A6**, **B11** | 2026-08-16 | `ffd073b` — "A5: division IS ultraweakly continuous — Bram's repair works, one word" |
| **D1** | 2026-08-16 | `43e270f` — "D1 fixed (ruled by Bas); six in Duplicators" |
| **D4**, **D5** | 2026-08-16 | `3aa13e7` — "D4 and D5 implemented: 69IX, 90II.2, 170IV.1, 157IV.1" |
| **A5** | 2026-08-17 | `3b4ba57` — "81IX div-usc ruled: c\a/b is only ultraweakly continuous" |
| **D6** | 2026-08-18 | `abc3af3` — "D6 ruled: delete the false net form of 164II.2b" |
| **A7** | 2026-08-19 | `5f19f62` — "26II.5 and 104III: p ∧ q is defined, and 2a and 3 are proved" |
| **A9** | 2026-09-02 | `3ae948d` — 51IX's ℂ-homogeneity clause restored under the D1 ruling |
| **B13** | 2026-09-04 | ruled (a) by Bas: 180V's `effectus_vn_partial` pins its effect object to `ℂ` |
| **B14** | 2026-09-04 | ruled (a) by Bas: 179III.2 restated to the cited theorem (scalar monotonicity, order unit) and its proof attempted |

Note that `ffd073b`'s subject names A5 while its diff removes A6 and B11; read
the diff, not the subject.  Keep this table in step when a question is deleted.

Deleted earlier and not in the table: **B2**, **B4**, **B5**, **B6**, **B7**,
**B9**, **D2**, **D3** (2026-08-16), **A4** (2026-08-21) and **A3**
(2026-08-26).  A3 asked whether it is right to leave a cited-only result
unproved; four of its six bullets are now proved independently of the citation,
the fifth was **B14** (ruled (a) on 2026-09-04, now deleted), the sixth pointed at an errata row that was
withdrawn when `eff.tex` changed, and its two *informational* remarks (the
third axiom of `extensive_effectus`, and what "adapt the proof of
`emod-effectus`" comes to for 180V) are `OPEN (informational)` rows in
[ERRATA.md](ERRATA.md).

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
`yₙ = |e₂⟩⟨e₁+eₙ|`).  **158II itself is true**: it is proved in Lean
(`Theses/B/Dils/Kaplansky.lean`) through the **linking algebra**, with no
strengthening of its hypotheses.

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

Three points, because they rule out the obvious alternatives.

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
   the embedding preserves.  `dils_completion` is proved, so `kaplansky_hilbmod`
   and the self-dual case `kaplansky_hilbmod_of_selfDual` are unconditional and
   axiom-clean.  The only `sorry`s in `Kaplansky.lean` are `kaplansky_hilbmod_A₁`,
   `A₁'` and `A₂'`, which record that 158V is false and which `kaplansky_hilbmod`
   does not use.  (The fourth estimate, `A₂`, is *true* and is proved; what
   separates it from `A₂'` is which resolvent moves with `α` — see the file's
   own ⚠ block.  158V itself is false and the request below is unchanged.)

*Decision needed*: how to repair the thesis.  Concretely, 158III–158V should
be deleted or demoted, and the proof of `kaplansky-hilbmod` replaced by the
linking-algebra argument above (which the thesis has all the material for:
152X at parsec 1520, 150II at 1500, `kaplansky` at 74IV).  The erratum row for
158V in `ERRATA.md` carries the same request.  See `docs/DECISIONS.md` §1.3.

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
restriction.  Iterated trimming fails too: the accumulated coefficient
`1 − q_{k-1}⋯q₀` is an ordered product of noncommuting positive contractions
and can exceed the unit ball (`‖·‖ ≈ 1.155` for two ideal trimmers) — there is
no two-sided trimming on a one-sided module.  H. Lin, *Double duals and Hilbert
modules*, arXiv:2311.15462 §4 proves an analogue under two hypotheses 158II
lacks (`𝒜` SOT-dense in `M`; the target in the norm-closed `M`-module generated
by `D`); the linking-algebra proof needs neither.  `kaplansky_hilbmod_of_weak`
(158II from *weak* bounded approximation) and `kaplansky_hilbmod_of_commutative`
remain in the file as independent partial results.

### B12. 139XI `ess-uniq-pur` — case (ii) of the **repaired** exercise is still false: the complements are taken in the wrong space
`dils.tex:998`, solution `bsols.tex:209`.  The exercise asks to show: if
`V, W : 𝒦 → ℋ ⊗ 𝒦'` satisfy `V*(a⊗1)V = φ(a) = W*(a⊗1)W` for all `a ∈ B(ℋ)`,
then `V = (1 ⊗ U)W` for a **unitary** `U` on `𝒦'` — under one of three
hypotheses, **(i)** both dilations minimal (`𝒱 = ℋ ⊗ 𝒦' = 𝒲`), **(ii)**
`dim 𝒱^⊥ = dim 𝒲^⊥`, **(iii)** `ℋ` and `𝒦` finite dimensional.  Only (ii) is
in question here.

**Why a hypothesis is needed at all** (settled; full row in `ERRATA.md`).
Without one the claim is false: `𝒦' = ℓ²`, `𝒦 = ℋ ⊗ ℓ²`, `W = 1`, `V = 1 ⊗ S`
with `S` the unilateral shift.  Both dilate `φ(a) = a ⊗ 1`; the only `U` with
`V = (1⊗U)W` is `S`, an isometry but not unitary.  Weakening "unitary" to
"isometry" does not save it: exchanging `V` and `W` in the same example
requires a `U` mapping `𝒦'` onto `𝒦'` isometrically *from* a proper subspace.

The solution is correct up to its last paragraph, which reads "As `𝒱` and `𝒲`
are isomorphic, they have the same dimension and so do `𝒱^⊥` and `𝒲`" (the
last `𝒲` is a typo for `𝒲^⊥`).  Equal dimension does not imply equal
codimension in infinite dimensions, and that is exactly what the extension of
`U₁ : 𝒲' → 𝒱'` to a unitary of `𝒦'` needs.

**The defect: case (ii) is false as printed.**  The complements are taken in
`ℋ ⊗ 𝒦'`, where the argument needs them in `𝒦'`.  Counterexample (paper, not
machine-checked): `ℋ = 𝒦' = ℓ²`, `𝒦 = ℋ ⊗ 𝒦'`, `S₁` the unilateral shift and
`S₂` the shift by two, `W = 1 ⊗ S₁`, `V = 1 ⊗ S₂`.  Both dilate
`φ(a) = a ⊗ 1`.  `𝒲` and `𝒱` are invariant under `B(ℋ)⊗1`, so
`𝒲 = ℋ ⊗ ran S₁` and `𝒱 = ℋ ⊗ ran S₂`, whence
`dim 𝒱^⊥ = ℵ₀ = dim 𝒲^⊥` and **(ii) holds**; but `V = (1⊗U)W` forces
`U S₁ = S₂`, so `U` would carry `(ran S₁)^⊥` (dimension 1) onto `(ran S₂)^⊥`
(dimension 2).  (i) and (iii) both fail here, so this attacks (ii) alone.

*Decision needed*: **(a)** replace (ii) by `dim ℒ_V^⊥ = dim ℒ_W^⊥` taken **in
`𝒦'`**, writing `𝒱 = ℋ ⊗ ℒ_V` and `𝒲 = ℋ ⊗ ℒ_W` (valid because `P_𝒱`
lies in the commutant `1 ⊗ B(𝒦')`) — which is what `berr.tex`'s own prose
"the ancillar spaces of the same dimension" means; **(b)** keep (ii) and add
`dim ℋ < ∞`; or **(c)** delete (ii).  We recommend (a).

*What waits on it*: `ess_uniq_pur` (`Theses/B/Dils/Stinespring.lean`) is
`sorry`ed and unchanged.  *Realigning* it to the current `dils.tex:998` needs
no ruling — our statement transcribes the first printing and drops all three
hypotheses, which is why the audit records it as "false as ours"; it is the
choice of (ii) that we are waiting on.  See `docs/DECISIONS.md` §1.4.

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
nmiu-isomorphism by `iso`".  But proc.tex **99IX** `iso` (proc.tex:878, parsec
990 point 90) is stated for **ncpsu**-isomorphisms, and its proof opens with
`f⁻¹(1) ≤ 1`, hence `1 = f(f⁻¹(1)) ≤ f(1) ≤ 1` — precisely the step that fails
for `λ·id`.  The universal properties as printed deliver only an *ncp*-isomorphism.

**This is the same defect as B11**, one point earlier in the same
development: there the mediating map of `IsFilterFor` (**169VIII**) had to be
made subunital, and the author ruled on 2026-08-16 that it should be.  The
identical edit does **not** suffice here.  For filters the hypothesis
`f(1) ≤ b ≤ 1` already forces the quantified `f` to be subunital, so only
`f'` needed changing; for corners the hypothesis is `f(a) = f(1)`, which
constrains nothing.  Requiring only `f'` subunital while `f` ranges over all
ncp-maps would make even the standard corner `h_z` fail its own universal
property (`f = 2·h_z` gives `f'(1) = 2·1 ≰ 1`).

*Decision needed*: restrict **both** the quantified `f` and the mediating
`f'` in 169II to ncpsu-maps — i.e. read the universal property in `W*_cpsu`,
which is where `iso` lives and where corners are quotients — or state the
converse of 170IV only for corners that are additionally unital.

*What waits on it*: `surjective_nmiu_2` is `sorry`ed and `IsCornerFor`
unchanged.  The first half, `surjective_nmiu_1`, is **true and proved** as it
stands; changing `IsCornerFor` will require its existence clause to be
re-checked (its uniqueness clause only gets easier).  See
`docs/DECISIONS.md` §1.1.

### B15. 206II.4 / 211IV — is the ⋄-self-adjoint square root of a ⋄-positive map required to be **pure**?  (eff.tex vs proc.tex 103I)
`eff.tex` parsec 2060 point 40 (`diamond-basics`), and parsec 2110 point 40
(`vn-is-andthen-eff`).  The two theses define ⋄-positivity differently, and
211IV's proof depends on the difference.

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
   ⋄-self-adjoint square root with the same square.  **This is a theorem**
   (`docs/B15-pure-sqrt.md`, 2026-09-04): such a `g` is *itself* pure, so
   `h = g`, by Kadison's order-isomorphism theorem on the corner `g`
   preserves — valid in all types, where the Kraus argument stalls.  So both
   readings are mathematically sound.  A *formal* Lean proof of (2) needs
   Kadison's theorem, which Mathlib lacks; reading (1) closes the `sorry` with
   no new mathematics.  The choice is now purely which the author intends.

**What the tree implements is reading (2)**, verbatim: in
`Theses/B/Eff/DiamondAmp.lean`, `DiamondSelfAdjoint f := diaPull f = diaPush f`
(**no** purity on `f`) and
`DiamondPositive f := IsPure f ∧ ∃ g, DiamondSelfAdjoint g ∧ f = g ≫ g`
(purity on **`f`**, none on the square root `g`).

*What waits on it*: everything else in 211IV is proved and axiom-clean in
`Theses/B/Eff/VNExamples.lean`.  Axiom 2 of 211II is
`su_quot_after_compr_pure` (via 100III `pure-fundamental`, exactly as
eff.tex:4862 says); axiom 1's existence half is `su_exists_asrt`; its
uniqueness half is `su_asrt_unique_of_pure_sqrt`, which is 105V reached
through the two dictionary lemmas `su_procPure_of_isPure` (effectus purity ⟹
100I purity) and `su_contraposed_of_diamondSelfAdjoint` (effectus
⋄-self-adjointness ⟹ 101VI contraposition).  `vn_is_andthen_eff` is
`su_andThenEffectus_of_pure_sqrt` applied to the one hypothesis above, and
that hypothesis is the file's only `sorry`.  Under ruling (1) both definitions
gain an `IsPure` conjunct and the `sorry` closes with no further mathematics;
under (2) it is exactly the missing step.  Nothing else in the tree depends on
which way this goes — `Effectus.lean`'s partial-form machinery was checked
field by field against 180VII and is faithful either way.  See
`docs/DECISIONS.md` §1.2.

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
`C → D` is faithful (each hom-set of `C` is a singleton or empty), the only
subcategories of `1` are `∅` and `1`, and `C` — with two isomorphism classes —
is equivalent to neither.  Adding that `Pred` is *full onto its image* does not
help: in that same example the functor onto the image subcategory is full **and**
surjective on objects, and the equivalence still fails.  What faithfulness does
not control is object identification, and that is what breaks.

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
`Pred X`, morphism part pinned to `p ↦ p ∘ f`, and `F.Faithful`.  The
subcategory clause is stated nowhere in the tree.

*Decision needed*: how "equivalent to a subcategory" is to be read.  Under 3
there is nothing to do in Lean and the repair is one sentence of `eff.tex`.
Under 1 or 2 the printed proof needs a genuinely new step (fullness, resp.
injectivity on objects), and only then could the clause be added to
`emod_effectus_representation` — the Lean cost is then the cost of that new
step, not of the packaging.  No `sorry` turns on this; what turns on it is
whether the Theorem's second sentence is provable as printed.  See
`docs/DECISIONS.md` §2.3.

(Unrelated, and *not* a question for the authors: the Theorem's **headline**
— "with scalars `M` and separating predicates" — is also unasserted by our
`emod_effectus`, but that is a missing tool for computing `Pred` and `Scal`
of `Par C`, recorded on the declaration itself, not a defect in the source.)

### B8. Minor: `bsols.tex`'s `onb1` solution over-assumes
**161IV** (`onb1`, `dils.tex:4681`, Exercise).  The solution assumes
self-duality, which neither the exercise nor our `onb1`
(`Theses/B/Dils/SelfDual.lean`) requires.  Harmless; noted for tidiness.
Answering "leave it" closes the item.  See `docs/DECISIONS.md` §3.6.

---

## Thesis A (`cstar.tex`, `vn.tex`, `proc.tex`) — remaining after the 2026-08-13 rulings

### A1. 98VI's hint points the wrong way
`proc.tex:631`.  The hint says to show `⌈τ⌉ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉^⊥`.  That is a
restatement of `τ(π(r^⊥)) = 0` and is the direction one does **not** need; a
proof along the hint requires the **converse**, `⌈τ⌉^⊥ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉`.  In
the concrete model both hold (the two sides are equal), so nothing downstream
is wrong — but only the converse is usable.

This is a question about the *hint* only: 98VI is proved
(`corners_composition`, `Theses/A/Proc/Measurement.lean`, axiom-clean), and it
needs neither the hint nor its converse.  The exercise is short if one takes
the corner's effect to be `s := β'(r)` rather than the carrier `⌈τ∘π⌉` — the
four-line argument is in the 98VI row of `ERRATA.md`.

*Decision needed*: replace the hint by that route, or keep the carrier route
with the inequality turned round.  See `docs/DECISIONS.md` §3.4.

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

Both halves are proved, and `ϱ_Ω` exists in Lean: `dsumRep` in
`Theses/A/CStar/Representation.lean` is the thesis's
`ϱ_Ω : 𝒜 → B(⊕_{ω∈Ω} ℋ_ω)`, the diagonal operator on `lp (fun ω => ω.GNS) 2`,
built there because Mathlib has the single-`ω` GNS representation and the
Hilbert direct sum but not the diagonal operator.  So the obstacle to stating
30X faithfully is gone.

*Decision needed*: whether to **restate 30X** as the thesis's genuine three-way
equivalence, with clause (1) reading `Function.Injective (dsumRep …)`, and to
add the closing claim that `ϱ_Ω` restricts to an miu-isomorphism onto its image
(the proved `injective_miu_iso_on_image` supplies it immediately).  We have not
done this because it changes a statement.

*What waits on it*: `proto_gelfand_naimark_2` has one user in the tree,
`gelfand_naimark` (30XIV) in the same file, and the strengthened form still
gives it immediately; the three uses in `A/VN` are all of
`proto_gelfand_naimark_`**`1`**.  See `docs/DECISIONS.md` §2.4.

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

**The repair costs nothing but the ruling.**  `functional_calculus_4` is
proved as it stands, by the thesis's own route: the unique element is exhibited
as `(gelfandStarTransform (C*(a))).symm (f ∘ j)`, where `j : φ ↦ φ(a)` is part
3's map `spec(C*(a)) → spec(a)` (Mathlib's
`elemental.characterSpaceToSpectrum`).  Mathlib's `cfc f a` is *defined* by
that same formula — `continuousFunctionalCalculus a` is
`((characterSpaceHomeo a).compStarAlgEquiv' ℂ ℂ).trans (gelfandStarTransform _).symm`
— so the missing clause needs no new mathematics; the 14-line proof of
`φ (cfc f a) = f (φ a)` has been compiled with no `sorry` and not committed,
because it changes a statement.  With it the iff form is immediate from the
uniqueness half already proved.

*What waits on it*: nothing else — no declaration in `Theses/` uses
`functional_calculus_4`.  See `docs/DECISIONS.md` §2.5.

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

**2. The infrastructure — packaging only.**  Forming `Mon(-)` and `CMon(-)`
needs `MonoidalCategory` (and `BraidedCategory`) instances on `W*_miu` and
`W*_cpsu`.  The mathematics for the `W*_miu` one exists: 119V `vn-smc` is
stated concretely and in full in `Theses/A/Proc/Tensor.lean` —
`vn_smc_pentagon`, `vn_smc_triangle`, `vn_smc_unitors_agree`, `vn_smc_hexagon`,
`vn_smc_symmetry` and the four naturality lemmas, all proved, with
`exists_braiding` (119IVc) no longer `sorry`.  What is missing is a tensor
bifunctor on the category `WMIU` (`Theses/A/Proc/QuantumLambda.lean`),
associators and unitors as natural isomorphisms of that category, and the
coherences restated in Mathlib's bundled form: plumbing over proved equations,
not new mathematics.

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
deliberately unstated rather than as open work.  See `docs/DECISIONS.md` §3.2.

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
of the contraposition already reduce to `x a t = 0`.  See
`docs/DECISIONS.md` §3.1.

### A13. 34V.3 in the module setting — is the **mirrored** cp condition wanted?
`cstar.tex` parsec 340, point 50 (`ad-cp`, Exercise), part 3; rendered — in
the Hilbert-*space* case only — as `ad_cp_3` in
`Theses/A/CStar/Matrices.lean`.

**What the point says.**  For every element `x` of a Hilbert `𝒜`-module `X`,
the vector functional `T ↦ ⟨x, Tx⟩ : ℬᵃ(X) → 𝒜` is completely positive.
(Part 2 is the companion `T ↦ S*TS : ℬᵃ(X) → ℬᵃ(Y)` for adjointable
`S : Y → X`.)

**What we state.**  `ad_cp_3` is the case `𝒜 = ℂ`, `X = ℋ`: the vector
functional `B(ℋ) → ℂ`, and the doc comment says so.  Part 2 is *not* in this
position: `conjModule` and `ad_cp_2_module` state and prove 34V.2 for Hilbert
`𝒜`-modules, and 32IV is likewise proved at module level
(`paschke_inclusion_no_adjoint`).  So 34V.3 is the only part of 34V still
confined to Hilbert spaces, and this question is the only thing holding it.

**Which convention is already ruled — do not answer that again.**  Session 2
approved **Mathlib's** `CStarModule`, and two statements were corrected against
it (`chilb_cs` 32VI and `cstar_matrix_gram_nonneg` 33II.2 — both *false* as
first transcribed; see PROVING-LOG session 2).  Note the relation precisely:
**32I** `chilb-basic` (parsec 320, point 10) makes `X` a **right** `𝒜`-module
with `⟨x, y·a⟩ = ⟨x,y⟩·a` (on `𝒜` over itself, `⟨x,y⟩ = x*·y`), while Mathlib's
`CStarModule` is a **left** module with `⟪x, a • y⟫ = a * ⟪x, y⟫` (on `𝒜` over
itself, `⟪x,y⟫ = y·x*`).  The two therefore differ by the **opposite algebra**,
not by a swap of arguments; the shorthand `⟪x,y⟫ = ⟨y,x⟩_thesis` is what one
gets after composing the mirror with a `star`, and agrees with the mirror only
on a `⟨y,y⟩` or a commutative `𝒜`.

**What is live.**  Under Mathlib's convention the ℂ-linear vector functional
`T ↦ inner 𝒜 x (T x)` **fails** our `IsCompletelyPositiveMap`
(`Theses/A/CStar/Basic.lean`), which asks `0 ≤ ∑ᵢⱼ bᵢ* f(aᵢ*aⱼ) bⱼ`: writing
`yᵢ := Tᵢ x`, the expression the module makes positive is
`⟪∑ᵢ bᵢ•yᵢ, ∑ⱼ bⱼ•yⱼ⟫ = ∑ᵢⱼ bⱼ·⟪yᵢ,yⱼ⟫·bᵢ*` — the `b`'s on the *other* sides
from the ones the cp condition wants.  The form that does satisfy the cp
condition is `T ↦ ⟪Tx, x⟫` (then
`∑ᵢⱼ bᵢ*·⟪yⱼ,yᵢ⟫·bⱼ = ⟪∑ⱼ bⱼ*•yⱼ, ∑ᵢ bᵢ*•yᵢ⟫ ≥ 0`), and *that* map is
**conjugate-linear in `T`**, hence not a `𝒜 →ₗ[ℂ] ℬ` and not eligible for
`IsCompletelyPositiveMap` at all.

*Decision needed*: whether the mirrored `𝒜`-valued cp condition is wanted.

* **(a) Keep Mathlib's, and add the mirrored companion**
  `∑ᵢⱼ bᵢ·f(aᵢaⱼ*)·bⱼ*` to `IsCompletelyPositiveMap`, and state the module
  version in it.  Every Hilbert-module file already rests on `CStarModule` —
  `B/Dils/{HilbertModules, SelfDual, SelfDualCompletion, Paschke, Kaplansky}`
  and `A/CStar/{Matrices, TowardsVN}`, some 900 lines mentioning it — so this
  is the cheap option.  The cost is that 34V.3 will not read like the printed
  formula (the thesis's `⟨x, Tx⟩` becomes Mathlib's `⟪Tx, x⟫`), and that the
  companion is a new definition, which needs the ruling on its own account.
* ~~**(b) Introduce the thesis's convention** alongside Mathlib's, so that
  34V.3 is transcribed verbatim.~~  **Ruled out in session 2**, and kept only
  so the trade-off it names is on the record.  It forfeits Mathlib's
  Hilbert-module API (Cauchy–Schwarz, the induced norm, the constructions) for
  anything stated in it, and would put two inner products on the same objects.
* **(c) Status quo**: leave 34V.3 in the Hilbert-space case, with the doc
  comment recording the divergence, and mark the module version as
  deliberately unstated.

*What the ruling buys*: no `sorry` closes either way, and nothing in the tree
is currently wrong — the Hilbert-space case we state is correct and proved.
What it settles is the shape of 34V.3 in the module setting and of every
future `𝒜`-valued statement, 161II in `B/Dils` included, together with the
three statements that already carry the mirror (32II's `𝒜^N`, 33I's
`matrixBaxEquiv`, 141III's `rightMulEquiv`, all with an `ᵐᵒᵖ`).  See
`docs/DECISIONS.md` §3.3.

### A2. `parsec-340.60` (34VI.1) is an empty `\TODO{}`
The solution slot exists but is empty, and it is the *last* entry in
`asols.tex` — which is why solution coverage appears to stop at parsec 340.
Our `cstar_product_4` is proved, but from Mathlib rather than the author's
argument, so it is **not cross-checked**.  Nothing is blocked; the question is
whether you want the solution written, in which case we will check ours
against it.  See `docs/DECISIONS.md` §3.5.

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
  order, but distributivity is never proved, so even `Semiring (X →ₘ[μ] ℂ)`
  fails to synthesise — and consequently there is no `Algebra`, no `StarRing`,
  and nothing downstream on `Lp E ∞ μ`.  Supplied locally in
  `A/VN/Basic.lean`'s `LinftyConstruction` block (four instances, ~70 lines,
  each axiom three lines via `AEEqFun.induction_on`); worth filing upstream,
  since it is the only thing standing between Mathlib and a C*-algebra
  `L^∞(X)`.
* Mathlib has **no double commutant theorem** (an explicit TODO in its own
  header), **no von Neumann tensor product**, no spatial tensor product, and no
  normal GNS.  Its `VonNeumannAlgebra` is the *concrete* (double-commutant)
  definition; `WStarAlgebra` is Sakai-style — neither matches the thesis's
  Kadison-style abstract definition.

---
