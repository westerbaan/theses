# Questions for the authors

Everything in this file needs a decision from an author.  Nothing here is a
Lean problem: each item is either a defect in a thesis statement, or a choice
about how faithfully our statement should track the thesis.

Findings that need **no** decision live elsewhere: thesis defects to be
corrected are in [ERRATA.md](ERRATA.md), and our own mis-transcriptions in
[PROVING-LOG.md](PROVING-LOG.md).  Resolved questions are at the bottom.

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

### B2. 227III.1 — exactness condition names the wrong map
`eff.tex:7629`.  For `A —f→ B —g→ C`, exactness at `B` is stated as
`IM^⊥ f = ⌈1 ∘ f⌉`; it must be `⌈1 ∘ g⌉` — as printed the condition does not
mention `g` at all.  Our `exactAt_iff` carries the corrected form and is
**proved**; the printed form is false.

### B3. 221IV.6 — purity of the mediating map is never checked
`eff.tex:6923`.  221II requires the mediating map to be pure, and the proof of
221IV.6 never establishes it.  The gap is real but harmless: we have now proved
it (`isPure_of_isQuotient_comp` / `isPure_of_comp_isComprehension`, in plain
effectus generality).  Recorded so the thesis can add the step.

### B4. 177Ia — RESOLVED: the Proposition is false, and we have a machine-checked counterexample
`eff.tex:~510`.  *Status 2026-08-14 (worker 55): settled — no author decision is
needed on how to prove it, only on how to amend it.  See the two 177Ia rows in
ERRATA.md.*

The printed proof has a real gap: it argues about `x⊥ ⋁ s` for an *arbitrary*
upper bound `s` of `c,d`, but that sum is only defined when `s ≤ x`, so it
establishes leastness only among elements below `x`.  We then twice tried to
repair or replace it, and the outcome is that **no repair exists — the
Proposition itself is false.**

**Counterexample** (`WrightTriangle` in `B/Eff/EffectAlgebras.lean`, every
effect algebra axiom checked by `decide`): the Greechie loop of order 3 — three
copies of `2³` pasted in a triangle, `B₁ = {a₁,a₄,a₂}`, `B₂ = {a₂,a₅,a₃}`,
`B₃ = {a₃,a₆,a₁}`, 14 elements.  Here `a₁ ⊥ a₂`, and `a₁ ∧ a₂ = 0` exists, but
`a₁ ∨ a₂` does **not**: `a₄ᵖ = a₁ ⋁ a₂` and `a₃ᵖ = a₆ ⋁ a₁ = a₂ ⋁ a₅` are
incomparable minimal upper bounds.  Formalised as
`WrightTriangle.not_ea_modularity_prop`, and
`WrightTriangle.not_modularity_lemma` refutes the intermediate lemma of points
20/30 as well — *even with `c ⊥ d` added*, so that patch does not save it
either.

The one-line reason to believe it without reading the table: in **any**
orthoalgebra `a ⊥ b` forces `a ∧ b = 0` (a common lower bound `c` has `c ⊥ c`),
so 177Ia would say every orthoalgebra is an orthomodular poset — and the Wright
triangle is the standard orthoalgebra that is not one.

*Decision needed (now a drafting decision, not a mathematical one)*: amend the
statement.  The natural amendment, and the only one the thesis's own uses need,
is to **hypothesise that `a ∨ b` exists**; the identity
`a ⋁ b = (a ∧ b) ⋁ (a ∨ b)` then holds, and is proved
(`ea_modularity_prop`, realigned; it is master's thesis Corollary 16.2).  A
lattice-effect-algebra hypothesis would do as well.  The citation to
Dvurečenskij–Pulmannová 1.8.2 should be checked: as stated in the thesis the
result is false, so 1.8.2 must carry a hypothesis that was dropped in transit.

**§2.1.1 of the master's thesis is also affected, and is now in the tree.**
Its Corollary 14 asserts that `a ⋁ (·)` and `a ⊖ (·)` transport suprema and
infima *in both directions*, justified by "suprema and infima in the order
restricted to `↓a⊥` are the same as in the whole of `E`".  That is sound only
where the relevant bounds are forced into the interval, which is the case for
exactly two of the four halves.  We transcribed the sound halves —
`msc_prop13_1`, `msc_prop13_3`, `msc_cor14_1_sup`, `msc_cor14_1_inf`,
`msc_cor14_2_inf`, `msc_prop15`, `msc_cor16_1`, `msc_cor16_2` — and the unsound
one in honest form as `msc_cor14_2_sup_below` (least upper bound *among
elements below `a`*).  Corollary 16.1 as printed ("`a ∧ b = 0` and `a ⊥ b`
⟹ `a ⋁ b = a ∨ b`") is false in the same way if read as asserting existence;
read as an identity given existence, it is true and proved.

**What we got wrong twice, and it is worth recording.**  First we said "we
could not repair it, therefore it is unreachable" — treating a broken proof as
evidence of a hard theorem.  Then we swung the other way and accepted a
three-line derivation from Corollary 14.2 without checking Corollary 14's own
proof; that derivation produces the join *inside `↓(a ⋁ b)`* and silently
promotes it to a join in `E`, which is the very step the printed proof gets
wrong.  The lesson: when a proof's gap is "leastness only within an interval",
any replacement built on interval-relative suprema inherits the gap — and the
cheapest way to find out is to look for a counterexample with the same energy
one spends looking for a proof.

**Nothing waits on this.**  177Ia was the last source of `sorryAx` leakage in
B/Eff and was bypassed earlier: `isSharp_ovee` and `diamond_oml_subEA` are
proved without modularity, and **177VI** `orth-ea-is-orthomodular` is proved
too (in an ortholattice both bounds exist, so it only ever needs the surviving
identity).  B/Eff: 1756 declarations walked, 19 `sorry`, **0** depending on
one.

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

### B5. `IsVNTensor` is too weak for 165III (and, it turns out, 166II)
*Status 2026-08-14 (worker 52): the **positivity** half is answered (worker 40,
confirmed by worker 41), and 165III `dfn_tensor_of_hilbmod_maps` is
**proved**.  The **normality-of-the-legs** half is answered too — it is
derivable, so `IsVNTensor` needs no new clause — and **166II**
`ultranorm_continuity_ext_tensor`, the statement that raised it, is now
**proved** as well.  A **third**, genuinely different gap has replaced them:
`IsVNTensor` omits proc.tex `tensor`-**2** (the *existence* of product
functionals), which **165VI** needs.  That one is open — and it is the only
open half of B5.*

`dils.tex:5433`.  Our axiomatization of the von Neumann tensor product
(proc.tex 108II) gives miu-bilinearity, `generates`, and separation by product
np-functionals — **nothing about order**.  165III's proof needs positivity of
`Mₙ(⊗) : Mₙ𝒜 × Mₙℬ → Mₙ(𝒜⊗ℬ)` (`cp-bilinear`) plus matrix positivity, and that
clause is not derivable from the existing four.

*Decision needed*: add a positivity clause to the definition.  Until then
`dfn_tensor_of_hilbmod_maps` and `ba_ext_tensor_pres` are unreachable.

*Re-verified 2026-08-13* against `SelfDual.lean:841`: the structure has
`add_left`, `add_right`, `smul_complex`, `mul`, `one`, `star`, `generates`,
`separating` — no order clause, as recorded.  One refinement: the
**uniqueness** half of 165III does *not* need the clause — `extTensor_map_ext`
(proved, in file) already gives it — so adding the clause leaves only the
existence half to prove.

**Answered 2026-08-14 (worker 40): the clause is derivable, so no decision is
needed.**  proc.tex **113II** and **113IV** are now proved
(`A/Proc/Tensor.lean`), and reading their proofs back shows what they actually
consume: 113II uses **only** multiplicativity and involution preservation, and
113IV (1) ⇒ (3) uses **only** additivity in each slot.  No `ℂ`-homogeneity
enters either.  Those four properties are exactly `mul`, `star`, `add_left`,
`add_right` of `IsVNTensor`.  Proved in that shape, so that an `IsVNTensor`
discharges it field by field:

```
Theses.A.Proc.matBilin_nonneg_of_mi (t : 𝒜 → ℬ → 𝒞) (hl hr hmul hstar)
  (M : M_N 𝒜) (M' : M_N ℬ) (hM : 0 ≤ M) (hM' : 0 ≤ M') (c) :
  0 ≤ ∑ᵢⱼ cᵢ* · t (Mᵢⱼ) (M'ᵢⱼ) · cⱼ
```

which is the cstar.tex 33II criterion for `0 ≤ Mₙ(t)(M,M')`.  `#print axioms`
clean.

**Checked and confirmed by the `B/Dils` worker, 2026-08-14 (worker 41).**
Reading **165IV** (the proof of 165III, `dils.tex:5433`) line by line, the
existence half consumes exactly three things beyond `ExtTensor.univ` (a
*field*, so free) and `η_inner`: (i) **33II**.1 `cstar_matrix_positive_iff`,
proved and on `B/Dils`'s import path; (ii) *positivity* of `Mₙ(⊗)`, which is
worker 40's lemma; (iii) *bi-monotonicity* of `Mₙ(⊗)` in the step
`Mₙ(⊗)((⟨Sxᵢ,Sxⱼ⟩), (⟨Tyᵢ,Tyⱼ⟩)) ≤ Mₙ(⊗)((‖S‖²⟨xᵢ,xⱼ⟩), (‖T‖²⟨yᵢ,yⱼ⟩))` —
and that is a two-line consequence of (ii) with `add_left`/`add_right`
(`Mₙ(⊗)(A',B') − Mₙ(⊗)(A,B) = Mₙ(⊗)(A'−A, B') + Mₙ(⊗)(A, B'−B)`).  Nothing
else in 165IV needs an order clause.  **So B5's positivity half is settled:
no change to `IsVNTensor` is required.**

~~One practical obstacle remains … `matBilin_nonneg_of_mi` lives in
`Theses/A/Proc/Tensor.lean`, which is not on `B/Dils`'s import path.~~
**Resolved** (QUESTIONS D3, worker 43): the lemma was moved to
`Theses/A/CStar/Matrices.lean`, which `B/Dils` already imports.  **165III
`dfn_tensor_of_hilbmod_maps` is proved as of 2026-08-14 (worker 50)**, exactly
along the route (i)–(iii) above; the only ingredient the analysis had missed is
ℂ-homogeneity of `t` in its *second* slot, needed to pull `‖T‖²` out of
`Mₙ(⊗)(G, ‖T‖²H)`, which is `vnTensor_smul_complex_right` (see below).

*Second gap, found 2026-08-14 (worker 41): `IsVNTensor` also omits
**normality of the legs**.*  The eight fields make `a ↦ t a 1` and `b ↦ t 1 b`
miu-maps (hence completely positive, by `cp_of_mi`), but say nothing about
their preserving directed suprema.  **166II**
`ultranorm_continuity_ext_tensor` needs exactly that: its proof rewrites
`⟨xα ⊗ yα, xα ⊗ yα⟩` as `(⟨xα,xα⟩ ⊗ 1)·(1 ⊗ ⟨yα,yα⟩)` and applies **44III**
`vanishing_effects`, which requires the first factor to converge *ultraweakly*
to `0` — i.e. that `Ω ∘ (· ⊗ 1)` be an np-functional of `𝒜` for every np `Ω`
of `𝒜 ⊗ ℬ`.  `generates` and `separating` give pointwise separation, not
this.  The thesis asserts the legs are "ncp" with a commented-out `\TODO`
where the justification should be (see the 166II row in ERRATA.md).

*Answered 2026-08-14 (worker 50): no clause is needed — leg normality is
derivable, and is now in the tree.*  `vnTensor_legLeft_normal` and
`vnTensor_legRight_normal` (`B/Dils/SelfDual.lean`, `#print axioms` clean)
prove `PreservesDirSups (fun a => t a 1)` and `PreservesDirSups (fun b => t 1 b)`
from the eight existing fields.  The argument uses only `separating`:

* the leg is positive (`t (c*c) 1 = star (t c 1) · t c 1`), hence monotone and
  self-adjointness-preserving;
* for a bounded directed `D ⊆ selfAdjoint 𝒜` with `⋁D = s`, the image has a
  supremum `s' ≤ s ⊗ 1` in `𝒞` (`𝒞` is a von Neumann algebra);
* every *product* np-functional `Ω = ω ⊗ ξ` gives `Ω(d ⊗ 1) = ω(d)·ξ(1)`, so
  `Ω(s')` and `Ω(s ⊗ 1)` are the same supremum of reals (normality of `Ω`,
  normality of `ω`, and `ξ(1) ≥ 0`);
* so `Ω((s ⊗ 1) − s') = 0` for all product `Ω`, and `(s ⊗ 1) − s' ≥ 0`, whence
  `s ⊗ 1 = s'` by `separating`.

The mirror statements for the right leg come from `vnTensor_flip`
(`IsVNTensor t → IsVNTensor (fun b a => t a b)`), whose `smul_complex` field is
`vnTensor_smul_complex_right` — itself derived from `separating` in the same
way (proc.tex 108I asks a tensor product to be ℂ-**bi**linear; `IsVNTensor`
records ℂ-homogeneity in the first slot only, and the second slot follows).

**166II is therefore no longer blocked on a decision.**  *Closed
2026-08-14 (worker 52): `ultranorm_continuity_ext_tensor` is **proved**.*  The
only piece of the predicted plumbing that was actually needed is the bundling
of `Ω ∘ leg` as an `NPFunctional` — `vnTensorLegLeftNP` / `vnTensorLegRightNP`,
which are `compNP` applied to the leg together with `vnTensor_leg*_normal`.
The scaling into `effects 𝒞` is *not* needed: once `Ω(· ⊗ 1)` is known to be an
np-functional, the estimate can stay in the order of `𝒞`,
`Ω(⟨d,d⟩ ⊗ ⟨yα,yα⟩) ≤ M²·Ω(⟨d,d⟩ ⊗ 1)` (monotonicity of `⊗` in each slot over
a positive other slot, plus `⟨yα,yα⟩ ≤ M²·1`), and **44III**
`vanishing_effects` is never invoked.  A by-product: the norm bound on the
`x`-net is unnecessary (ERRATA, 166II statement row).

*Third gap, found 2026-08-14 (worker 50): `IsVNTensor` omits the **existence**
of product functionals — proc.tex `tensor` clause 2 — and **165VI** needs it.*
proc.tex 108II asks three things of a tensor product: (1) the range generates,
(2) for **all** np `σ` on `𝒜` and `τ` on `ℬ` the product functional
`γ(σ,τ)` *exists* and is positive, (3) those product functionals are faithful.
`IsVNTensor` has (1) as `generates` and (3) as `separating`, but **not (2)**.
That asymmetry is convenient where an `IsVNTensor` has to be *produced*, and
fatal where one has to be *consumed with its functionals*: **165VI**
`ba_ext_tensor_pres` must produce `separating` for `Θ(S,T) = S ⊗ T`, and the
thesis's proof (165IX) does so by exhibiting the functionals
`σ ⊗ τ = (f ⊗ g)(x ⊗ y, (·) x ⊗ y)` — which presupposes that `f ⊗ g` exists on
`𝒞 = 𝒜 ⊗ ℬ` for the *given* `t`.  With only `separating` available for `t`,
there is nothing to build them from.

*Decision needed*: add to `IsVNTensor` a field
`productFunctional : ∀ (ω : NPFunctional 𝒜) (ξ : NPFunctional ℬ), ∃ Ω : NPFunctional 𝒞, ∀ a b, Ω (t a b) = ω a * ξ b`
(proc.tex `tensor`-2), which is a faithful transcription of the definition and
strictly weakens nothing that is currently proved — but it does add a proof
obligation to **165VI** and to any future construction of a tensor product.
Note 165VI is *additionally* blocked on **164II**.1 `ext_tensor_dense` and
**164II**.2a `ext_tensor_basis`, both still `sorry`, so the decision is not
urgent.

### B6. `exc_dm_effectus_functor` / `_monad` / `_kleisli` are too weak to be meaningful
Our statements constrain only `.obj` — they say *some* functor/monad agrees
with `𝒟_M` on objects, and nothing about `map`, `η` or `μ`.  `_kleisli` is
**confirmed unprovable as stated**: transporting *any* monad along a bijection
`T.obj X ≃ 𝒟_M X` satisfies the hypothesis.

This is our transcription, not a thesis defect.  *Decision needed*: restate to
pin `map`/`η`/`μ` (we would then prove them — the intended witness already
exists).

### B7. 194I — is the trivial effect monoid (`1 = 0`) admitted?
`eff.tex:2974`.  The proof says "As `𝒟_M ∅ = ∅`, the empty set is … the initial
object of `AConv_M`".  When `1 = 0` the empty formal combination sums to `1`, so
`𝒟_M ∅` is a *singleton* and `∅` is not an abstract `M`-convex set at all.  The
proposition still holds (for `1 = 0` every object is a singleton, so `1` is
initial) and our Lean proof splits on it.

*Decision needed*: keep effect monoids possibly trivial and add the case split,
or exclude `1 = 0` from the definition (178II) once and for all?  The same
question governs `MConvexComb`, whose `sum_one` degenerates identically — the
`1 = 0` branch already appears in five proofs in `StatesPredicates.lean`.

*Update (193X/194I.3/194I.4)*: the cost is smaller than it looked.  Isolating
the split in one lemma — `MConvexComb.eq_eta_punit`, "`𝒟_M 1` is a singleton",
which holds in both branches — makes the whole of 193X and 194I.3/.4 uniform in
`1 = 0`.  So the question is now purely one of what the thesis should *say*,
not of how much rework it costs us.

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

### D3. `matBilin_nonneg_of_mi` is in the wrong chapter for its consumer — **RESOLVED (worker 43)**
**Option 2 was taken, authorised by Bas.**  The lemma now lives in
`Theses/A/CStar/Matrices.lean` as `Theses.A.CStar.matBilin_nonneg_of_mi`
(axiom-clean), generalised to three independent universes; `A/Proc/Tensor.lean`
keeps a pointer comment where it used to be.  `B/Dils` already imports
`A/CStar/Matrices`, so 165III is now unblocked with no new inter-chapter
coupling.  The original question is kept below for the record.

It lived in `Theses/A/Proc/Tensor.lean` (worker 40) and is exactly what 165III
in `Theses/B/Dils/SelfDual.lean` needs — but `B/Dils` imports `A/CStar/Matrices`,
`A/VN/Projections` and `Theses.Common`, **not** `A/Proc`. So the lemma is off
the consumer's import path and 165III is blocked structurally rather than
mathematically.

Three options, and a **recommendation**:

1. **Add `import Theses.A.Proc.Tensor` to `B/Dils`.** Legitimate on the face of
   it — CONVENTIONS records that thesis B freely imports thesis A, matching the
   text's cross-references. But it **couples two chapters that are currently
   independent**, and `A/Proc` is the largest active work-front (145 `sorry`s).
   After this, no worker could edit `A/Proc` while another worked `B/Dils`.
2. **Relocate the lemma to `A/CStar/Matrices.lean`**, which `B/Dils` already
   imports. Its content — positivity of `∑ᵢⱼ cᵢ* t(Mᵢⱼ, M'ᵢⱼ) cⱼ` for a
   multiplicative, involution-preserving, biadditive `t` — is about matrices
   over C\*-algebras and has no `proc.tex` content, so it belongs there on
   merit, not merely for convenience. **Recommended.**
3. Duplicate it. Cheapest, and wrong.

Not done unilaterally because option 2 edits `A/CStar`, which is upstream of
every other chapter and was frozen while workers were live.

### D2. `PaschkeModule` is internally inconsistent with `IsPaschkeDilationOf`
`Theses/B/Dils/Paschke.lean` (warning block at the head of the file).  Our
mirroring of parsec 1540 is off by a `star`.  The fields `inner_tprod`,
`ρ_tprod` and `h_def` together *prove* `h (ρ a) = φ (star a)`, while
`IsPaschkeDilationOf` in `Stinespring.lean` asks for `h (ρ a) = φ a`.  So
**`existence_paschke_5` is false as stated** once `PaschkeModule φ` is
inhabited, and `existence_paschke_4`'s `hφ` is off by the same `star`.

Machine-checked, and **no single field can be repaired**: `inner_tprod` is
forced by positivity of `⟨v,v⟩`, `h_def` by ℂ-linearity of `h`, `ρ_tprod` by
multiplicativity of `ρ`.  The fix is a coordinated re-mirroring of the bundle,
touching **~10 statements across two files** — which is why it was diagnosed
and flagged rather than done unilaterally.

A *separate* and unambiguous defect in the same area **has been fixed**:
`PhiCompatible.bound` was mirrored on the wrong side, which made
`PaschkeModule φ` outright **uninhabited** and so made nine theorems vacuous.
Counterexample (re-derived independently): `φ = id` on `M₂`, `a = e₀₀`,
`b = e₁₀` gives `‖b* φ(a*a) b‖ = ‖ab‖² = 0` while `inner_tprod` forces
`‖b φ(a*a) b*‖ = ‖e₁₁‖ = 1`, i.e. `1 ≤ r·0`.

*Decision needed (Bas)*: which of the two candidate re-mirrorings to adopt —
see PROVING-LOG session 14 §5.  **Until then, nothing should be built on
`PaschkeModule`, `PaschkeTriple` or `IsPaschkeDilationOf`.**

## Thesis A (`cstar.tex`, `vn.tex`, `proc.tex`) — remaining after the 2026-08-13 rulings

### A1. 98VI's hint points the wrong way
`proc.tex:631`.  The hint says to show `⌈τ⌉ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉^⊥`.  That is a
restatement of `τ(π(r^⊥)) = 0` and is the direction one does **not** need; the
proof requires the **converse**, `⌈τ⌉^⊥ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉`.  In the concrete model
both hold (the two sides are equal), so nothing downstream is wrong — but only
the converse is usable.

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

## Resolved

**2026-08-13, by Bram** — all thesis-A items below are fixed in the sources,
with deltas in the `asols.tex` errata block.  See HANDOFF.md § "Resolved by the
author" for the full list and erratum keys.

16V, 16VI (reworded, not merely hypothesised), 17III, 17VI.3, 19Ia, 22III.5,
22VIII, 23VII.3, 30IV.2, 34aVII, 37IX, 38VI.2, 4VIII, 61II, 62I, 68IV.2,
72III.1b/1c, 11XX.1, 12III.3, 23II, plus solution-text fixes to 11XV.2, 11XX.2,
16VII, 17VI.6, 20aII, 26II.1, 26II.4, 30IV.1.

**Key ruling**: the trivial C\*-algebra `{0}` **stays admitted globally** — 8II
and the categorical chapters need it — so only five statements gained
`𝒜 ≠ {0}` rather than adding `[Nontrivial]` throughout.

**Earlier, by Bas**: the C\*-module inner-product convention (Mathlib mirrors
the thesis, `⟪x,y⟫_Mathlib = ⟨y,x⟩_thesis`) — five of our statements were
transcribed without the swap and are now corrected; and the `Corner` /
`cornerSet` / `VNSub` / `mketbra` / `145I` / `148VII` / `88IV` fixes, all of
which were **our** transcription errors rather than thesis defects.

### B9. 188IV — is "total" independent of the effectus-in-partial-form structure?

`Tot D` is defined by `1 ∘ f = 1`, i.e. relative to the effect object `I` and
the truth predicate `1` of the chosen `EffectusPartialForm` structure on `D`.
Everything *else* in such a structure is determined by the category together
with its coproducts:

* the initial object `0` is also terminal (for `f : X → 0`, `1 ∘ f = f ∘ 1_0`
  and `1_0 = 0_0` by initiality, so `1 ∘ f = 0` and `f = 0`), so the zero maps
  are the maps through `0` and `▷₁ = [id,0]`, `▷₂ = [0,id]` are determined;
* `f ⊥ g` iff there is `b` with `▷₁ ∘ b = f`, `▷₂ ∘ b = g` (⇐ is the compatible
  sum axiom, ⇒ is untying with `b = κ₁f ⋁ κ₂g`), and then `f ⋁ g = ∇ ∘ b` — so
  the PCM-enrichment is determined too.

We could not settle whether `(I, 1)` is likewise determined (up to a canonical
iso of `I`), i.e. whether the wide subcategory `Tot D` depends on the choice.
The obvious candidates fail: "`f` is total iff `f ⊥ g` implies `g = 0`" is
false — in `Par(Set)` the unique map `X ⇸ ∅` is maximal but not total.

**Why it matters.**  Our statement of 188IV (`cho_thm_3_tot_par`) originally
quantified over *every* structure of an effectus in partial form on `Par C`,
which is strictly stronger than what the thesis proves (188IV is about the
structure built in 187I).  It has been weakened to the canonical structure.
If totality is in fact structure-independent, the stronger form follows and
the statement could be restored; a counterexample would be interesting in its
own right.
