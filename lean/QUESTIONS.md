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

### B1. 192V.3.3 — "semilattices are exactly abstract 2-convex sets" is false
`eff.tex:2577`.  By the thesis's **own** Definition 192II the support condition
uses the *partial* effect-algebra sum, and `1 ⋁ 1` is undefined in `2`.  Hence
`𝒟_2 ≅ Id` and the abstract 2-convex sets are just **sets**, not semilattices.

Verified formally: our Lean proof of `semilattice_two_convex` goes through
**without ever using `SemilatticeSup`**.  The intended claim holds for the
non-empty-finite-powerset monad.

*Decision needed*: correct the thesis, and tell us whether to restate our
version (as written it is silently weaker and useless as a validation).

Bas: fixed. (A followup question is whether semilattices can be defined as abstract M-convex sets for some M. Probably not.)

**REALIGNED 2026-08-15** (`bb9615f`, "Fix 192V3"): the false claim is deleted
upstream and the surviving direction carries the new label
`eff-semilattice-aconv`.  Our side (session 39): `semilattice_two_convex` is
gone; in its place `two_convexComb_eq_eta`, `two_convex_nonempty` and
`two_convex_unique` say what is actually true (`𝒟₂ ≅ Id`, so `AConv₂ ≅ Set`),
and `semilattice_unitInterval_convex` — the thesis's surviving claim — now
*pins* the structure map to the join of the support instead of merely asserting
`Nonempty (MConvex I L)`.  The second sentence of the corrected item
("cancellative iff `x = y` for all `x,y`") is proved as
`semilattice_cancellative_iff`.  The followup question is discussed in
PROVING-LOG session 39.

### B3. 221IV.6 — purity of the mediating map is never checked
`eff.tex:6923`.  221II requires the mediating map to be pure, and the proof of
221IV.6 never establishes it.  The gap is real but harmless: we have now proved
it (`isPure_of_isQuotient_comp` / `isPure_of_comp_isComprehension`, in plain
effectus generality).  Recorded so the thesis can add the step.

### B10. 158II `kaplansky-hilbmod` — the thesis's proof is dead and no replacement is known
`dils.tex` parsec 1580.  158II is proved in the thesis via **158V**, and 158V is
**false** (counterexample in `PROVING-LOG`; `B(ℓ²)`, `y = |e₂⟩⟨e₁|`,
`yₙ = |e₂⟩⟨e₁+eₙ|`).  A dedicated run then failed both to prove and to refute
158II itself:

* every replacement route tried — truncation/`h`-style renormalizers, adaptive
  two-stage `conjNP` requests, a least-squares sandwich — funnels into the same
  mirrored quantity, the `ω`-mass of `spec ⟪d₀,d₀⟫` above `‖x‖²`, which an
  adversarial approximant makes `O(1)` for any *one-shot* renormalizer;
* every adversarial `D` collapses, because `⟪D,D⟫ ⊆ 𝒜` lets `𝒜`-functional
  calculus trim the escaping components — so the `∃ d ∈ D` form genuinely
  resists the 158V counterexample.

Recorded, and worth keeping: the `∃ d ∈ D` freedom is real but **not sufficient
on its own** — pointwise ultranorm continuity of `h` fails even at norm-interior
points, so any proof must exploit the `𝒜`-module trimming, not just the
entourage form.

**Banked**: `kaplansky_hilbmod_of_weak` (proved, axiom-clean) reduces 158II to
*weak* bounded approximation — `‖ω⟪w, x−d⟫‖ ≤ η` with `d` in the `‖x‖`-ball of
`D` — via a Mazur-style variational lemma.  So the open part is now the weak
form alone.

*Decision needed*: prove the weak form, refute 158II, or strengthen its
hypotheses.  The pointer H. Lin, *Double duals and Hilbert modules*,
arXiv:2311.15462 §4 has now been **checked in full** (worker 60, session 30
of `PROVING-LOG`): Lemma 4.3/Theorem 4.4 do prove the analogue — for an
*arbitrary* Hilbert `𝒜`-module, not just the standard one, via matrix
Kaplansky + Kasparov stabilization + an approximate identity of `K(H)` —
but under two hypotheses 158II lacks: `𝒜` SOT-dense in the enveloping
`M`, and the target in the *norm*-closed `M`-module generated by `D`
rather than the ultranorm closure.  His §5 Example 5.1 also shows the
analogous density *fails* one topology further out (for `H^♯`).  Session 30
additionally rules out finite/decidable counterexamples for (W)/158II/158V
(all true in finite dimension, and 158V is true for commutative `ℬ`), shows
commutative 158II is provable outright, and blocks the natural
iterated-trimming route on a precise structural fact: the accumulated
coefficient is an ordered product of noncommuting positive contractions,
whose defect `1 − q_{k-1}⋯q₀` can exceed the unit ball (`‖·‖ ≈ 1.155`
already for two ideal trimmers) — no two-sided trimming exists on a
one-sided module.

### B11. 169VIII `dils-def-filter` — "filter **for** `b`" is defined weaker than in proc.tex, and 169XI.2 is false as printed
`dils.tex:6118`.  The Definition says "`c` is a filter for `b ≥ 0` if
**`c(1) ≤ b`** and every ncp-map `f` with `f(1) ≤ b` factors uniquely through
`c`", while proc.tex **96I** (`filter`), which the surrounding text says it is
recalling, asks the universal property for `f(1) ≤ c(1)` and calls `c` a filter
*for `c(1)`* — so there `c(1) = b` by construction.

The two are genuinely different: `c = ½·id : ℬ → ℬ` satisfies the dils.tex
condition for `b = 1` (each `f` with `f(1) ≤ 1` factors uniquely, as `2f`)
while `c(1) = ½`.  Consequently **169XI**.2 — "there is a unique **unital**
ncp-map `φ'` with `φ = c' ∘ φ'`", for `c'` a filter of `φ(1)` — is false as
printed: take `φ = id : ℂ → ℂ` and `c' = ½·id`.  Its `bsols.tex` solution uses
`c'(1) = φ(1)`, i.e. the proc.tex reading.  See ERRATA for the one-character
fix (`c(1) ≤ b` → `c(1) = b`), which repairs everything; the *derived* notion
"`c` is a filter" (= a filter for some `b`) is insensitive to the change, so
purity (**170I**), **169XI**.1 and **169XII** are untouched.

*Decision needed*: our `IsFilterFor` (`B/Dils/Pure.lean`) transcribes
dils.tex literally and so carries the weak form, which leaves
`dils_filter_basics_2a` unprovable.  Say whether to change it to `c 1 = b`
(the proc.tex form) — we have not, under the standing rule that statements are
not altered without an author's ruling.

*Status 2026-08-16 (worker 73): the blast radius is now **machine-confirmed**
to be exactly `dils_filter_basics_2a`.*  **169XI**.1 `dils_filter_basics_1`
and **169XI**.2's second half `dils_filter_basics_2b` are both **proved**
against the weak (dils.tex) reading and are axiom-clean.  Part 1 survives
because the only place it needs the filter's universal property is at
`h'(1) = c(φ(1))`, and `c(φ(1)) ≤ c(1) ≤ b` holds under either reading; part
2b never uses unitality of `φ'` at all — it is part 1 applied to `c'` and the
dilation of `φ'`.  So a ruling on B11 changes exactly one Lean statement.

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

### B8. Minor: `bsols.tex`'s `onb1` solution over-assumes
Its solution assumes self-duality, which neither the exercise nor our statement
requires.  Harmless; noted for tidiness.

---

## Ours to decide, not the authors' — but it changes four statements

### D1. `IsLinftyOf` omits `ℂ`-linearity of `q`
`Theses/A/Proc/QuantumLambda.lean`.  Our predicate requires `q` to be a
`∗`-ring map but never `q (z • f) = z • q f`.  Without that, the thesis's
argument "every `f` is a.e. constant, hence `L^∞ ≅ ℂ`" does **not** produce an
nmiu-map: a `∗`-ring isomorphism `ℂ → 𝒜` can be *conjugate*-linear, so the
conclusion genuinely does not follow from the hypotheses as we stated them.

130II was proved anyway, by routing through Gelfand–Mazur instead — so nothing
is currently blocked on this.  But the rendering is weaker than intended.

*Decision needed (Bas, not the authors — this is our transcription, not a
thesis defect)*: add `q (z • f) = z • q f` to `IsLinftyOf`?  It is the right
fix, but it touches **four statements at once**, which is why it was not done
unilaterally.

### D5. 170IV `surjective_nmiu_1`/`_2` drop the thesis's "between von Neumann algebras"
`Theses/B/Dils/Pure.lean:1126` and `:1134`.  The exercise (dils.tex:6223)
reads "any surjective nmiu-map **between von Neumann algebras** is a corner
of a central projection … and conversely".  Both our statements sit in
`section Pure`, whose only binders are `[CStarAlgebra A] [PartialOrder A]
[StarOrderedRing A]` (likewise `B`), so as transcribed they claim the result
for **arbitrary C\*-algebras** — strictly more than the source.  Every
neighbouring statement that needs the hypothesis has it
(`standard_corner_dils` at `:643`, `paschke_corner` at `:1164`), so this
looks like an omission rather than a deliberate generalisation.

It is not academic.  The whole reachable route to 170IV.1 — **69IV**
`carrier_miu`, which is proved and supplies the central projection
`z = ⌈ϱ⌉` together with `ϱ a = 0 ↔ z·a = 0` — requires
`[VonNeumannAlgebra A]`, and so does the author's own route through 69II.
Without it there is no central projection to produce and the item is not
provable by any argument in the thesis.  No counterexample was found (the
natural commutative candidates, `ev₀ : C([0,1]) → ℂ` and `lim : c → ℂ`, are
not normal and hence not `NMIUMap`s), so the over-general statement is
*open*, not known false.

*Decision needed (Bas — our transcription, not a thesis defect)*: add
`[VonNeumannAlgebra A] [VonNeumannAlgebra B]` to both halves of 170IV?
Nothing downstream consumes them yet, so the change is local to two
signatures.

### D4. `CentreSeparating` renders the wrong item of 69IX
`Theses/A/VN/Projections.lean`.  `Theses.A.VN.CentreSeparating` is our
rendering of **69IX.2**, not **69IX.1** (which is cstar.tex 21II.4, the
C\*-notion).  But 69IX.1 is what 90II's proof and `proto_gelfand_naimark_1`
actually consume.

The consequence is that `vn_center_separating`'s TFAE is a **class-4
mis-transcription**: its item 1 duplicates its item 2, and the C\*-notion is
lost from the statement altogether.

Not repaired: fixing the definition touches 90II.1, 90II.2, 69IX and reaches
into `B/Dils`.  Worker 43 proved **90II.1** anyway, by a different route —
central support plus 60I `ceil_functionals_lemma`, avoiding the thesis's
`gns_ceil` — so nothing is currently blocked on it.

*Decision needed (Bas)*: restate `CentreSeparating` as 69IX.1 and re-derive
69IX.2 from it, or keep the present rendering and add the C\*-notion as a
separate definition?  Related: 69IX item 3 needs one missing lemma — *a
`projSup` of central projections is central* — which is cheap either way.

*Update (session 53)*: that lemma **already exists**, `projSup_isCentral`
(`Projections.lean:4176`), and **69VII** `gns_ceil` is now proved, so the
implication (2) ⇒ (3) of 69IX — the only one the thesis proves at length — is
a few lines away (`z := (⋃_ω ⌈⌈ω⌉⌉)^⊥` is central, and `ω(z) ≤ ω(⌈⌈⌈ω⌉⌉⌉^⊥) = 0`
by the private `omega_conj_cceil_compl` of the same file).  What (3) ⇒ (1)
still needs is *`⌈a⌉` is central for central positive `a`*, which the tree does
not have; the natural proof is that `⌈a⌉` is the ultrastrong limit of the
`a^{1/2ⁿ}` and `vna_supremum_mult` passes centrality to the limit.  69IX is
therefore left `sorry` pending this decision **and** that lemma, not pending
69VII.

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

### A5. 81IX `div-usc` — the second half is false; which repair do you want?
`vn.tex:5533`.  The Lemma claims both `a ↦ a/b : (𝒜)₁b → 𝒜` **and**
`a ↦ c∖a/b : c(𝒜)₁b → 𝒜` are ultrastrongly continuous.  The first is true and
is now proved from the thesis's own argument (`div_usc_ball`).  The second is
**false** — see the 81IX row in ERRATA.md for the counterexample
(`b = 1`, `c = diag(1,½,⅓,…)` in `B(ℓ²)`, `dₙ = |n⟩⟨0|`).

Three repairs are available and they are not equivalent, so this needs a
decision:

1. **Drop the second map.**  Nothing in **vn.tex** appears to use it: the
   sequel (**82I** polar decomposition, **83II**, **83V**) uses only
   **81III** and the definition of division.  ⚠️ **Update (session 47):** it
   *is* used, in **proc.tex** — the proof of **96V** `canonical-filter`
   derives normality of `g = d*∖f(·)/d` from precisely this false half.  96V
   itself is true, and its proof has been repaired (and machine-checked)
   without any form of `div-usc`: see the **96VI** row of ERRATA.md.  So
   option 1 remains available, but it needs the 96VI repair alongside it.
2. **Restrict `c`.**  For `c` with closed range — equivalently `c`
   pseudoinvertible in the sense of **79I** — one has `c∖x = tx` for the
   bounded pseudoinverse `t`, and `‖t(x−x₀)‖_ω ≤ ‖t‖‖x−x₀‖_ω` makes the map
   continuous at once.
3. **Weaken the topology for that factor** to the ultrastrong-\* topology,
   in which `c∖(·)` *is* continuous on `c(𝒜)₁` (the mirror of the thesis's
   own argument, run on the seminorms `ω(xx*)^½`).

Note that **81VII** `div-approx` — which reads like the same statement about
`c∖·/b` — is **true** and is proved (`div_approx`): for one fixed `a` the
convergence holds by normality; it is only the *uniformity* over the unit ball
that fails, and the Lean statement of 81VII does not claim it.  The thesis's
parenthetical "(and uniformly so)" in 81VII should therefore be checked too:
by the same counterexample it is false for the `c∖·` half.

### A2. `parsec-340.60` (34VI.1) is an empty `\TODO{}`
The solution slot exists but is empty, and it is the *last* entry in
`asols.tex` — which is why solution coverage appears to stop at parsec 340.
Our `cstar_product_4` is proved, but from Mathlib rather than the author's
argument, so it is **not cross-checked**.

### A3. Statements the theses only *cite*, never prove
These have no proof to transcribe, so we have parked rather than proved them.
Confirm that is the right treatment:

* **179III.2** Gudder–Pulmannová representation (`eff.tex:739`, cited to
  `gudder1998representation`).  Note our statement is also *weaker* than the
  cited result — it omits both the order-unit condition and the scalar
  compatibility — so if it is ever revived it must be strengthened first.
* **178III.2** "every finite effect monoid comes from a Boolean algebra, hence
  is commutative" and **178III.4** "there is a non-commutative effect monoid on
  lexicographic `ℝ⁵`" (`eff.tex:640`/`651`, cited to `basmsc` prop. 40 /
  cor. 51).  Three parked statements: `finite_effectMonoid_boolean`,
  `finite_effectMonoid_commutative`, `exists_noncommutative_effectMonoid`.
* **192V.4** "every cancellative abstract `[0,1]`-convex set embeds affinely in
  a real vector space" (`eff.tex:2591`, cited to `statesofconvexsets` thm. 8);
  `cancellative_iso_convex`.
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
* **`effectus_vn`** (`eff.tex:832`, says only "adapt the proof of
  `emod-effectus`").  Note (2026-08-14, worker 45): `emod-effectus` (191II) is
  now fully formalized, so the analogy now has something concrete to be an
  analogy *to* — but the two proofs share nothing beyond their shape: 191II's
  is elementwise in `EMod_M`, and the `vNᵒᵖ` version needs the von Neumann
  theory of thesis A, none of which is on `B/Eff`'s import path (`B/Eff`
  imports only `Theses.Common`).
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
* Mathlib has **no double commutant theorem** (an explicit TODO in its own
  header), **no von Neumann tensor product**, no spatial tensor product, and no
  normal GNS.  Its `VonNeumannAlgebra` is the *concrete* (double-commutant)
  definition; `WStarAlgebra` is Sakai-style — neither matches the thesis's
  Kadison-style abstract definition.

---
