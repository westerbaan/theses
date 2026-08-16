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

### B2. 227III.1 — exactness condition names the wrong map — **RESOLVED 2026-08-16**
`eff.tex:7629`.  For `A —f→ B —g→ C`, exactness at `B` is stated as
`IM^⊥ f = ⌈1 ∘ f⌉`; it must be `⌈1 ∘ g⌉` — as printed the condition does not
mention `g` at all.  Our `exactAt_iff` carries the corrected form and is
**proved**; the printed form is false.

**Fixed by Bas** (`0d85d0e`): `eff.tex` now reads `IM^⊥ f = ⌈1 ∘ g⌉`, which is
exactly our `exactAt_iff` (`Comparisons.lean:787`) — `ExactAt f g ↔ orth (imPred f)
= ceilPred (g ≫ truth Z)`.  No Lean change needed; the statement was already
carrying the corrected form.  The same commit also labels the containing point
`eff-dagger-conc-ex`, so it is citable now.

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

### B5. `IsVNTensor` is too weak for 165III (and, it turns out, 166II) — CLOSED
*Status 2026-08-15 (worker 66): **all three halves are settled and nothing is
asked of the authors.*** The **positivity** half is answered (worker 40,
confirmed by worker 41) and 165III `dfn_tensor_of_hilbmod_maps` is **proved**;
the **normality-of-the-legs** half is derivable, so no clause was needed, and
**166II** `ultranorm_continuity_ext_tensor` is **proved**.  The third half —
the missing proc.tex `tensor`-**2** (*existence* of product functionals) — was
**our mis-transcription of 108II, not a weakness of the thesis**, and the field
has now been added (divergence class 4; see the closing note below).

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

**Closed 2026-08-15 (worker 66): this was not a question but a transcription
error of ours (divergence class 4), and it is fixed.**  108II's `tensor-2` had
simply been dropped when `IsVNTensor` was written; the thesis's definition is
fine.  `IsVNTensor` (`B/Dils/SelfDual.lean`) now carries, between `generates`
(`tensor-1`) and `separating` (`tensor-3`),

```lean
exists_productFunctional : ∀ (ω : NPFunctional 𝒜) (ξ : NPFunctional ℬ),
  ∃ Ω : NPFunctional 𝒞, ∀ (a : 𝒜) (b : ℬ), Ω (t a b) = ω a * ξ b
```

("exists **and is positive**" of the thesis: positivity and normality are
carried by the type `NPFunctional 𝒞`).  Verbatim `tensor-2` was chosen over
the weaker `tensor-characterization` (proc.tex:3578) variant, which restricts
existence to centre-separating collections `Σ, Γ`: that is an equivalent
*characterisation* rather than a weaker interface — it still demands existence,
only for fewer functionals — and it would additionally force
`CentreSeparating` into the definition, which nothing in parsecs 1640–1670
consumes.

Only two things construct an `IsVNTensor`, and both were discharged:
`vnTensor_mul_complex` (the ℂ ⊗ ℂ witness; the product functional is
`smulNP (σ(1)·τ(1)) complexIdNP`) and `vnTensor_flip` (transports the field
with `mul_comm`).  Everything already proved from `IsVNTensor` is unaffected —
adding a field only strengthens the hypothesis — and `#print axioms` stays
clean for `vnTensor_mul_complex`, `vnTensor_flip`,
`vnTensor_smul_complex_right` and `vnTensor_legLeft_normal`.

**165VI is still not reachable**, and the new field is not what blocks it:
`ba_ext_tensor_pres` *concludes* `IsVNTensor Θ`, so the field is an extra
obligation there (to be met, as the thesis's 165IX does, by
`σ ⊗ τ = (f ⊗ g)(x ⊗ y, (·) x ⊗ y)` — which is exactly what the field now makes
available on the *given* `t`).  Its blockers are the three `sorry`ed
properties of **164II** it consumes — `ext_tensor_dense`, `ext_tensor_basis`
and `ext_tensor_ketbra_dense` — plus 165VII–165X, which are not converted.
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

**ANSWERED 2026-08-15 by Bas**: "yes, please fix the statements."  Done in
session 39, by dropping the existential shape entirely — it is exactly what
admitted the transported impostor, and with `F.obj X = 𝒟_M X` only
*propositional* one cannot even phrase the condition on `F.map` without a cast.
`exc_dm_effectus_functor : Type u ⥤ Type u` and
`exc_dm_effectus_monad : Monad (Type u)` are now **definitions** whose object
part is literally `MConvexComb M`, whose action on maps is literally
`MConvexComb.map`, and whose `η`, `μ` are literally `MConvexComb.eta`,
`MConvexComb.mu` — pinned by the `rfl` lemmas `exc_dm_effectus_functor_obj`,
`_functor_map`, `_monad_toFunctor`, `_monad_eta`, `_monad_mu`.  The functor and
monad laws are `map_id`/`map_comp` and `mu_map_eta`/`mu_eta`/`mu_mu`, all
already proved, so .1 and .2 are **closed**.  `exc_dm_effectus_kleisli` is now
stated about `Kleisli (exc_dm_effectus_monad M)` — no longer vacuous-by-transport
— and remains `sorry`: it is the starred exercise itself (a full
`EffectusTotalStructure` on `Kl 𝒟_M`), not something .2 hands us.

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

**ANSWERED 2026-08-15 by Bas** (`d61feea`, "Fix 194I"): effect monoids stay possibly
trivial, and 194I now performs the case split explicitly — it treats `M = 1` first
(every abstract `1`-convex set is a singleton, so any of them is initial), then
assumes `M ≠ 1` for the `𝒟_M ∅ = ∅` argument.  That is exactly the shape our proof
already had, so **no Lean change is needed**; the split stays isolated in
`MConvexComb.eq_eta_punit`.

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

### D2. `PaschkeModule` cannot carry `ρ : NMIUMap 𝒜 (Ba ℬ X)` — RULED, and FIXED (session 43)
**Ruling (Bas, 2026-08-15):** *"the definition of Paschke dilation should not
include the star"* — so `IsPaschkeDilationOf` (`Stinespring.lean:1179`,
`∀ a, D.h (D.ρ a) = φ a`) **is correct as it stands** and the defect is on the
`PaschkeModule` side.  Investigated 2026-08-15 (session 15); the defect turned
out to be *structural*, not a misplaced `star`, and is still open.

What was previously recorded here — that the fields prove
`h (ρ a) = φ (star a)`, repairable by a coordinated re-mirroring — was
**wrong in a stronger direction**.  Machine-checked in `Paschke.lean`:

* `paschke_module_phi_eq_zero`: the fields force **`φ = 0`**.  `inner_tprod`'s
  right-hand side `b' φ(a'* a) b*` is ℂ-*linear* in `a`, while
  `⟨·,·⟩` is conjugate-linear in its first argument and
  `PhiCompatible.smul_complex` makes `tprod` ℂ-linear in `a`; at `c = i` this
  gives `2i·φ(a) = 0`.  So `PaschkeModule φ` is uninhabited for every non-zero
  `φ`, `existence_paschke` is false, and all nine statements with a
  `PaschkeModule` hypothesis are vacuous.
* No edit of `inner_tprod`/`h_def` repairs it.  `tprod a b = b • tprod a 1`
  forces `⟨a ⊗ b, a' ⊗ b'⟩ = b' M(a,a') b*`; positivity of `⟨v,v⟩` in
  Mathlib's left-action convention leaves exactly two candidates,
  `M(a,a') = φ(a'* a)` (needs `tprod` *conjugate*-linear in `a`, and then `ρ`
  is conjugate-linear) and `M(a,a') = φ(a' a*)` (compatible with the ℂ-linear
  `tprod`).  For the second, `paschke_rho_forces_cyclic` shows `ρ_tprod` plus
  adjointability of `ρ(a₀)` forces `φ(a' a* a₀*) = φ(a₀* a' a*)` for all
  `a, a', a₀` — false already for `φ = id` on `M₂`.
* **Root cause.**  Mirroring a right Hilbert ℬ-module to a left one is passage
  to the *conjugate* module, which turns the thesis's *left* `𝒜`-action into a
  *right* one.  For a left Hilbert ℬ-module `X`, `𝒷ᵃ(X)` is anti-isomorphic to
  the thesis's `𝒷ᵃ(X)` (for `X = ℬ` the adjointables are the *right*
  multiplications, so `𝒷ᵃ(ℬ) ≅ ℬᵒᵖ`).  So the Paschke module carries an
  nmiu-map `𝒜 → 𝒷ᵃ(𝒜 ⊗_φ ℬ)ᵐᵒᵖ`, not `𝒜 → 𝒷ᵃ(𝒜 ⊗_φ ℬ)`, and `𝒜 ≅ 𝒜ᵒᵖ` fails
  for general von Neumann algebras (Connes).

**Ruling implemented (Bas, 2026-08-16: "Ok, fix the transcription please";
session 43).**  Of the two mechanisms on the table, `Paschke.lean` now uses
**`ᵐᵒᵖ` on the operators**:

    ρ : NMIUMap 𝒜 (Ba ℬ X)ᵐᵒᵖ
    ρ_tprod    : (ρ a₀).unop (a ⊗ b) = (a a₀) ⊗ b
    inner_tprod: ⟨a ⊗ b, a' ⊗ b'⟩ = b' φ(a' a*) b*
    bound      : ‖∑ᵢ T(aᵢ,bᵢ)‖² ≤ r ‖∑ᵢⱼ bᵢ φ(aᵢ aⱼ*) bⱼ*‖
    h : NCPMap (Ba ℬ X)ᵐᵒᵖ ℬ,  h T = ⟨1 ⊗ 1, T.unop (1 ⊗ 1)⟩

`h_def` is unchanged in substance and `paschkeModule_h_ρ` proves
`h (ρ a) = φ a` with no `star`, so `IsPaschkeDilationOf` stands untouched, as
ruled.  The mirroring dictionary that makes all of this a *faithful* image of
the thesis is now stated in the file header: the mirror of a right module is
the **conjugate** module, so the ℂ-action is conjugated too, and the mirror of
the thesis's `⊗` carries a `star` in **both** arguments,
`tprod a b = (a* ⊗ b*)_thesis`.  That single correction produces `inner_tprod`,
`bound` and the anti-homomorphism `ρ` simultaneously.

*Why this mechanism and not `CStarModule ℬᵐᵒᵖ X` (`ᵐᵒᵖ` on the scalars).*
The expected tiebreaker — that Mathlib's `MulOpposite` support for a
C*-algebra `ℬ` is richer than anything available for `Ba ℬ X` — does not
exist: `CStarAlgebra Aᵐᵒᵖ` (`Mathlib/Analysis/CStarAlgebra/Classes.lean:139`),
`MulOpposite.instPartialOrder` and `StarOrderedRing Aᵐᵒᵖ`
(`Mathlib/Algebra/Order/Star/Basic.lean:395`) are all generic in `A`, so they
apply verbatim to `Ba ℬ X`.  And the one piece Mathlib does *not* supply — the
abstract Kadison `VonNeumannAlgebra Aᵐᵒᵖ` of `Theses/Common.lean` — is needed
identically by both routes (the scalars route needs it for `ℬᵐᵒᵖ`, to invoke
`ba_vonNeumannAlgebra`).  It is now proved once, as
`vonNeumannAlgebra_mulOpposite` in `Paschke.lean`.

With the tiebreaker gone the decision is churn, and the operators route wins:
`𝒜 ⊗_φ ℬ` stays a `CStarModule ℬ`-module, i.e. in the same mirrored
convention as the rest of the chapter, so `SelfDual`, `cstarBInner`,
`IsBoundedModuleMap`, `UnDense` and `ExtTensor` all apply unchanged — in
particular **167I** (`paschke_tensor`, `paschke_tensor_module`) and **166VI**
(`dilationspace_dense_subset`) in `SelfDual.lean` needed *no* edit.  The
scalars route would have needed `ExtTensor` over `ℬᵢᵐᵒᵖ` plus an `IsVNTensor`
transfer to the opposite algebras, i.e. new infrastructure for statements that
are still `sorry`.  `ᵐᵒᵖ` now occurs in exactly three places, all inside
`Paschke.lean`: `ρ`, `h`, and the `PaschkeTriple` of `existence_paschke_5`.

*A third fact the `ᵐᵒᵖ` explains.*  In the mirrored convention the vector
state is completely positive on the **opposite** of `𝒷ᵃ(X)`, not on `𝒷ᵃ(X)`:
for `X = ℬ` the adjointables are the right multiplications, `𝒷ᵃ(ℬ) ≅ ℬᵐᵒᵖ`
via `t ↦ R_t` with `⟨1, R_t 1⟩ = t`, so `h : 𝒷ᵃ(ℬ) → ℬ` is `unop`, which is
the transpose on `M₂` — positive but not completely positive.  With the `ᵐᵒᵖ`
on the domain it is a ∗-isomorphism.  (Worth checking whether **145I**
`hilbmod_vectstates_cp` in `HilbertModules.lean` has the same defect; it was
out of scope for session 43 and is still `sorry`.)

*Non-vacuity.*  `paschkeModuleId` exhibits `ℬ` itself, with `tprod a b = b·a`
and `ρ = rightMulEquiv`, as a `PaschkeModule` of `φ = id`, so the repaired
bundle is inhabited for a non-zero `φ` and the nine theorems that quantify
over it say something.  This is the check that would have caught both this
defect and the `PhiCompatible.bound` defect below.

A *separate* and unambiguous defect in the same area **has been fixed**:
`PhiCompatible.bound` was mirrored on the wrong side, which made
`PaschkeModule φ` outright **uninhabited** and so made nine theorems vacuous.
Counterexample (re-derived independently): `φ = id` on `M₂`, `a = e₀₀`,
`b = e₁₀` gives `‖b* φ(a*a) b‖ = ‖ab‖² = 0` while `inner_tprod` forces
`‖b φ(a*a) b*‖ = ‖e₁₁‖ = 1`, i.e. `1 ≤ r·0`.

The freeze on `PaschkeModule` is **lifted**: the bundle is repaired and
inhabited, `existence_paschke_2` and `existence_paschke_4` are proved against
it, and `existence_paschke_5`'s `h ∘ ϱ = φ` half — the half that was false —
is proved.  `PaschkeTriple` and `IsPaschkeDilationOf` were always fine.

## Thesis A (`cstar.tex`, `vn.tex`, `proc.tex`) — remaining after the 2026-08-13 rulings

### A1. 98VI's hint points the wrong way
`proc.tex:631`.  The hint says to show `⌈τ⌉ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉^⊥`.  That is a
restatement of `τ(π(r^⊥)) = 0` and is the direction one does **not** need; the
proof requires the **converse**, `⌈τ⌉^⊥ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉`.  In the concrete model
both hold (the two sides are equal), so nothing downstream is wrong — but only
the converse is usable.

### A5. 81IX `div-usc` — the second half is false; which repair do you want?
`vn.tex:5533`.  The Lemma claims both `a ↦ a/b : (𝒜)₁b → 𝒜` **and**
`a ↦ c∖a/b : c(𝒜)₁b → 𝒜` are ultrastrongly continuous.  The first is true and
is now proved from the thesis's own argument (`div_usc_ball`).  The second is
**false** — see the 81IX row in ERRATA.md for the counterexample
(`b = 1`, `c = diag(1,½,⅓,…)` in `B(ℓ²)`, `dₙ = |n⟩⟨0|`).

Three repairs are available and they are not equivalent, so this needs a
decision:

1. **Drop the second map.**  Nothing in the thesis appears to use it: the
   sequel (**82I** polar decomposition, **83II**, **83V**) uses only
   **81III** and the definition of division.
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
